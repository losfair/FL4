//! Regressions for fl4-core audit findings: the per-core debug TCB lists
//! across migration (finding 2), IRQ backend release on handler deletion
//! (finding 3b), the hardware debug exception path (finding 8.1), and
//! DomainSetSet on a thread running on another core (audit F4), the
//! paging-structure flush after a PDPT unmap, and IOAPIC routes the
//! backend refuses.
#![cfg(not(feature = "aarch64"))]

use fl4_abi::consts::object as ot;
use fl4_core::capability::{Cap, FrameSize};
use fl4_core::interrupt;
use fl4_core::layout::{cte, node, reg};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_get, node_set, Sc, Slot, Tcb};
use fl4_core::{cdt, debug, objects, schedcontext, syscall, vspace};
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory {
    words: BTreeMap<u64, u64>,
    cpu: u64,
    freed_range: Option<(u64, u64)>,
}
impl Store for Memory {
    fn read(&self, a: u64) -> u64 {
        if let Some((base, len)) = self.freed_range { assert!(a < base || a >= base + len, "read freed SC at {a:#x}"); }
        *self.words.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        if let Some((base, len)) = self.freed_range { assert!(a < base || a >= base + len, "write freed SC at {a:#x}"); }
        self.words.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len);
    }
    fn ks_base(&self) -> u64 {
        0x100000
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}

#[derive(Default)]
struct Machine {
    time: u64,
    events: Vec<(&'static str, u64)>,
    acked: Vec<u64>,
    freed: Vec<u64>,
    masked: Vec<(u64, bool)>,
    /// When set, a remote stall runs the stalled core's side on this memory.
    smp: Option<Shared>,
    /// Reschedule IPIs sent, by core mask.
    rescheduled: Vec<u64>,
    /// IOAPICs (24 pins each), what routing a pin returns, and the routes.
    ioapics: u64,
    ioapic_ok: bool,
    routed: Vec<(u64, u64, u64)>,
    /// How often `irq_pending` was read, and what it answers.
    irq_reads: u64,
    irq_line: bool,
}
impl Arch for Machine {
    fn now(&mut self) -> u64 {
        self.time
    }
    fn set_deadline(&mut self, _: u64) {}
    fn us_to_ticks(&self, x: u64) -> u64 {
        x
    }
    fn ticks_to_us(&self, x: u64) -> u64 {
        x
    }
    fn max_us(&self) -> u64 {
        u64::MAX
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        1
    }
    fn irq_pending(&mut self) -> bool {
        self.irq_reads += 1;
        self.irq_line
    }
    fn take_pending_irq(&mut self) -> u64 {
        u64::MAX
    }
    fn mask_irq(&mut self, irq: u64, mask: bool) {
        self.masked.push((irq, mask));
    }
    fn ack_irq(&mut self, irq: u64) { self.acked.push(irq); }
    fn irq_free(&mut self, irq: u64) {
        self.freed.push(irq);
    }
    fn set_vspace(&mut self, _: u64, _: u64) {}
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, asid: u64) { self.events.push(("invalidate_asid", asid)); }
    fn invalidate_page_structures(&mut self, asid: u64) { self.events.push(("invalidate_ps", asid)); }
    fn ioapic_map(&mut self, ioapic: u64, pin: u64, _: u64, _: u64, vector: u64) -> bool {
        self.routed.push((ioapic, pin, vector));
        self.ioapic_ok
    }
    fn ioapic_map_remapped(&mut self, ioapic: u64, pin: u64, _: u64, _: u64, vector: u64, _: u64) -> bool {
        self.routed.push((ioapic, pin, vector));
        self.ioapic_ok
    }
    fn num_ioapics(&self) -> u64 {
        self.ioapics
    }
    fn ioapic_pins(&self, i: u64) -> u64 {
        if i < self.ioapics { 24 } else { 0 }
    }
    fn port_in(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, t: u64) { self.events.push(("flush", t)); }
    fn fpu_sanitise(&mut self, t: u64) { self.events.push(("sanitise", t)); }
    fn fpu_reload(&mut self, t: u64) { self.events.push(("reload", t)); }
    fn fpu_release(&mut self, t: u64) { self.events.push(("release", t)); }
    fn remote_stall(&mut self, cpu: u64) {
        self.events.push(("stall", cpu));
        if let Some(m) = &self.smp {
            let mut there = Shared { cpu, ..m.clone() };
            fl4_core::smp::stall(&mut there, &mut Machine::default());
        }
    }
    fn send_reschedule(&mut self, mask: u64) { self.rescheduled.push(mask); }
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 {
        0
    }
    fn halt(&mut self) {}
}

/// One memory seen from several cores.
#[derive(Clone, Default)]
struct Shared {
    words: std::rc::Rc<std::cell::RefCell<BTreeMap<u64, u64>>>,
    cpu: u64,
}
impl Store for Shared {
    fn read(&self, a: u64) -> u64 { *self.words.borrow().get(&a).unwrap_or(&0) }
    fn write(&mut self, a: u64, v: u64) { self.words.borrow_mut().insert(a, v); }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) { self.write(a + i, 0); }
    }
    fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len); }
    fn ks_base(&self) -> u64 { 0x100000 }
    fn cur_cpu(&self) -> u64 { self.cpu }
}

const DEBUG_TCBS: u64 = node::DEBUG_TCBS;

/// The TCBs on `cpu`'s debug list, checking its back links.
fn debug_list(s: &Memory, cpu: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut prev = 0;
    let mut t = node_get(s, cpu, DEBUG_TCBS);
    while t != 0 {
        assert_eq!(Tcb(t).debug_prev(s), prev, "debug list of core {cpu} badly linked at {t:#x}");
        assert!(out.len() < 64, "debug list of core {cpu} does not end");
        out.push(t);
        prev = t;
        t = Tcb(t).debug_next(s);
    }
    out
}

fn thread(s: &mut Memory, a: &mut Machine, base: u64) -> Tcb {
    match objects::create_object(s, a, ot::Tcb, base, 0, false) {
        Cap::Thread { ptr } => Tcb(ptr),
        _ => unreachable!(),
    }
}

/// Finding 2: a thread created on core 0 (head of core 0's debug list) is
/// bound to an SC of core 1, then deleted; its memory is retyped. Creating
/// another thread on core 0 must not write through a stale list head into
/// the retyped object (slot 112 of a CNode, or offset 0xe00 of a user
/// frame, is where the stale head's `debug_prev` lies).
#[test]
fn migrated_thread_leaves_no_stale_head_over_a_retyped_cnode() {
    stale_head_case(false);
}

#[test]
fn migrated_thread_leaves_no_stale_head_over_a_retyped_frame() {
    stale_head_case(true);
}

fn stale_head_case(retype_as_frame: bool) {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let victim_base = 0x40_0000;
    let victim = thread(&mut s, &mut a, victim_base);
    assert_eq!(debug_list(&s, 0), vec![victim_base]);

    let sc = Sc(0x50_0000);
    sc.set_cpu(&mut s, 1);
    schedcontext::bind_tcb(&mut s, &mut a, sc, victim);
    assert_eq!(victim.affinity(&s), 1);

    // Delete the thread: finalise its cap, then the untyped reset clears
    // the memory and retypes it.
    let _ = objects::finalise_cap(&mut s, &mut a, Cap::Thread { ptr: victim_base }, true, true);
    s.clear_free(victim_base, 1 << 12);
    let guarded = Cap::Endpoint { ptr: 0x60_0000, badge: 7, send: true, recv: true, grant: false, grant_reply: false };
    let slot112 = Slot(victim_base + 112 * cte::SIZE);
    assert_eq!(slot112.0, victim_base + 0xe00);
    if retype_as_frame {
        let c = objects::create_object(&mut s, &mut a, ot::X86Page4K, victim_base, 0, false);
        assert!(c == Cap::Frame { ptr: victim_base, size: FrameSize::Small, rights: 3, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 });
    } else {
        let _ = objects::create_object(&mut s, &mut a, ot::CapTable, victim_base, 7, false);
        slot112.set_cap(&mut s, guarded);
    }

    let fresh_base = 0x70_0000;
    let fresh = thread(&mut s, &mut a, fresh_base);
    if retype_as_frame {
        for off in (0..(1u64 << 12)).step_by(8) {
            assert_eq!(s.read(victim_base + off), 0, "kernel wrote {:#x} into the user frame at {off:#x}", s.read(victim_base + off));
        }
    } else {
        assert!(slot112.cap(&s) == guarded, "slot 112 of the retyped CNode was overwritten");
    }
    assert_eq!(debug_list(&s, 0), vec![fresh_base]);
    assert_eq!(fresh.debug_next(&s), 0);
    assert_eq!(node_get(&s, 1, DEBUG_TCBS), 0);
}

/// Migrating to the core a thread is already on changes nothing.
#[test]
fn migrating_to_the_same_core_keeps_the_debug_list() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let t1 = thread(&mut s, &mut a, 0x40_0000);
    let t2 = thread(&mut s, &mut a, 0x41_0000);
    let sc = Sc(0x50_0000);
    schedcontext::bind_tcb(&mut s, &mut a, sc, t1);
    assert_eq!(debug_list(&s, 0), vec![t2.0, t1.0]);
    // Moving the tail, then the head, to core 1 keeps both lists linked.
    fl4_core::smp::migrate_tcb(&mut s, &mut a, t1, 1);
    assert_eq!(debug_list(&s, 0), vec![t2.0]);
    assert_eq!(debug_list(&s, 1), vec![t1.0]);
    fl4_core::smp::migrate_tcb(&mut s, &mut a, t2, 1);
    assert_eq!(debug_list(&s, 0), Vec::<u64>::new());
    assert_eq!(debug_list(&s, 1), vec![t2.0, t1.0]);
}

/// Finding 3b: deleting an IRQHandler cap releases the backend's routing
/// for that IRQ exactly once.
#[test]
fn deleting_an_irq_handler_frees_the_irq() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let irq = 5;
    interrupt::set_irq_state(&mut s, &mut a, interrupt::IRQ_SIGNAL, irq);
    let slot = Slot(0x40_0000);
    slot.set_cap(&mut s, Cap::IrqHandler { irq });
    cdt::delete(&mut s, &mut a, slot, true).ok().expect("delete");
    assert!(slot.cap(&s).is_null());
    assert_eq!(interrupt::irq_state(&s, irq), interrupt::IRQ_INACTIVE);
    assert_eq!(a.masked.last(), Some(&(irq, true)));
    assert_eq!(a.freed, vec![irq]);
}

const DR6_SINGLE_STEP: u64 = 1 << 14;
const EFLAGS_TF: u64 = 1 << 8;
const EFLAGS_RF: u64 = 1 << 16;
const SS_ENABLED: u64 = 6;
const SS_COUNT: u64 = 7;

/// Finding 8.1: a single step the user asked for with RFLAGS.TF itself
/// (the debug API's single step off) is reported once: TF is cleared.
#[test]
fn user_trap_flag_single_step_clears_tf() {
    let mut s = Memory::default();
    let t = Tcb(0x40_0000);
    t.set_reg(&mut s, reg::FLAGS, EFLAGS_TF | 0x202);
    t.set_reg(&mut s, reg::FAULT_IP, 0x1234);
    let f = debug::debug_exception(&mut s, t, 1, DR6_SINGLE_STEP);
    assert!(f.is_some());
    assert_eq!(t.reg(&s, reg::FLAGS), 0x202 | EFLAGS_RF);

    // With the debug API's single step on, TF stays for the next step.
    t.set_debug_reg(&mut s, SS_ENABLED, 1);
    t.set_reg(&mut s, reg::FLAGS, EFLAGS_TF | 0x202);
    let _ = debug::debug_exception(&mut s, t, 1, DR6_SINGLE_STEP);
    assert_eq!(t.reg(&s, reg::FLAGS), EFLAGS_TF | 0x202 | EFLAGS_RF);
}

/// Finding 8.1: a #DB that delivers no fault (a multi-step not run out)
/// still charges the time the thread ran.
#[test]
fn pending_single_step_still_charges_time() {
    let mut s = Memory::default();
    let mut a = Machine::default();
    let t = Tcb(0x40_0000);
    let sc = Sc(0x50_0000);
    node_set(&mut s, 0, node::CUR_THREAD, t.0);
    node_set(&mut s, 0, node::CUR_SC, sc.0);
    node_set(&mut s, 0, node::CUR_TIME, 100);
    t.set_sc(&mut s, sc.0);
    sc.set_tcb(&mut s, t.0);
    t.set_debug_reg(&mut s, SS_ENABLED, 1);
    t.set_debug_reg(&mut s, SS_COUNT, 3);
    a.time = 150;
    syscall::handle_debug_exception(&mut s, &mut a, 1, DR6_SINGLE_STEP);
    assert_eq!(t.debug_reg(&s, SS_COUNT), 2, "the step was counted");
    assert_eq!(node_get(&s, 0, node::CUR_TIME), 150, "the timestamp was not updated");
    // The SC has no budget left, so the 50 ticks are charged to it.
    assert_eq!(sc.consumed(&s), 50, "the time was not charged");
}


/// All four invocations enter the common decoder before touching remote state.
#[test]
fn remote_tcb_invocations_stall_before_fpu_and_space_changes() {
    use fl4_abi::{consts::tcb_flag, label};
    use fl4_core::{msg, sched, tcb};
    for lbl in [label::TCBReadFPU, label::TCBWriteFPU, label::TCBSetFlags, label::TCBSetSpace] {
        let mut s = Memory::default();
        let mut a = Machine::default();
        let caller = Tcb(0x20000);
        let target = Tcb(0x30000);
        target.set_affinity(&mut s, 1);
        node_set(&mut s, 0, node::CUR_THREAD, caller.0);
        node_set(&mut s, 1, node::CUR_THREAD, target.0);
        let extra = [Slot(0x50000), Slot(0x50020), Slot(0x50040)];
        extra[0].set_cap(&mut s, Cap::Frame {
            ptr: 0x60000, size: FrameSize::Small, rights: 3, is_device: false,
            mapped: false, is_ept: false, asid: 0, vaddr: 0,
        });
        caller.set_reg(&mut s, msg::msg_register(0), 0);
        caller.set_reg(&mut s, msg::msg_register(1), tcb_flag::FPU_DISABLED);
        let invoked = Slot(0x50060);
        invoked.set_cap(&mut s, Cap::Thread { ptr: target.0 });
        if lbl == label::TCBSetSpace {
            caller.set_reg(&mut s, msg::msg_register(1), 0);
            extra[0].set_cap(&mut s, Cap::Null);
            extra[1].set_cap(&mut s, Cap::CNode { ptr: 0x70000, radix: 4, guard: 0, guard_size: 0 });
            extra[2].set_cap(&mut s, Cap::Pml4 { ptr: 0x80000, mapped: true, asid: 1 });
            target.slot(fl4_core::layout::tcb::SLOT_VTABLE).set_cap(&mut s,
                Cap::Pml4 { ptr: 0x90000, mapped: true, asid: 2 });
            let table = s.ks_base() + fl4_core::layout::ks::ASID_TABLE;
            s.write(table, 0xa0000);
            s.write(0xa0000 + 2 * 8, 0x90000);
        }
        s.write(target.fpu_addr(), 123);
        s.write(0x60000, 456);
        let ctx = tcb::Ctx { length: 2, buf: 0, call: false, slot: invoked, extra: &extra };
        assert!(tcb::decode(&mut s, &mut a, lbl, target, &ctx).is_ok(), "label {lbl}");
        assert_eq!(a.events[0], ("stall", 1));
        assert_eq!(node_get(&s, 0, node::IPI_PENDING), 2);
        if lbl == label::TCBReadFPU {
            assert_eq!(s.read(0x60000), 123);
            assert_eq!(a.events[1], ("flush", target.0));
        } else if lbl == label::TCBWriteFPU {
            assert_eq!(s.read(target.fpu_addr()), 456);
            assert_eq!(&a.events[1..], &[("flush", target.0), ("sanitise", target.0), ("reload", target.0)]);
        } else if lbl == label::TCBSetFlags {
            assert_eq!(target.flags(&s), tcb_flag::FPU_DISABLED);
            assert_eq!(a.events[1], ("release", target.0));
        } else {
            assert!(target.slot(fl4_core::layout::tcb::SLOT_VTABLE).cap(&s) == extra[2].cap(&s));
            assert_eq!(a.events[1], ("invalidate_asid", 2));
            assert_eq!(s.read(0xa0000 + 2 * 8), 0);
        }
        assert!(caller.state(&s) == sched::TS_RUNNING || caller.state(&s) == sched::TS_RESTART);
    }
}

/// Once the stall is acknowledged, the other core can retype the old SC.
/// Neither VM completion nor the next ordinary interrupt may touch it.
#[test]
fn stalled_vm_exit_and_following_irq_do_not_access_retyped_sc() {
    use fl4_core::{sched, smp, sporadic};
    for (irq, time) in [(syscall::NO_IRQ, 20), (7, 20), (7, 1020)] {
        let mut s = Memory::default();
        let mut a = Machine { time, ..Default::default() };
        let guest = Tcb(0x20000);
        let idle = Tcb(0x30000);
        let old_sc = Sc(0x40000);
        let idle_sc = Sc(0x50000);
        guest.set_state(&mut s, sched::TS_RUNNING_VM);
        guest.set_sc(&mut s, old_sc.0);
        idle.set_state(&mut s, sched::TS_IDLE);
        idle.set_sc(&mut s, idle_sc.0);
        old_sc.set_tcb(&mut s, guest.0);
        node_set(&mut s, 0, node::CUR_THREAD, guest.0);
        node_set(&mut s, 0, node::IDLE_THREAD, idle.0);
        node_set(&mut s, 0, node::CUR_SC, old_sc.0);
        node_set(&mut s, 0, node::IDLE_SC, idle_sc.0);
        node_set(&mut s, 0, node::CUR_TIME, 10);
        node_set(&mut s, 0, node::CONSUMED, 3);
        sporadic::refill_new(&mut s, old_sc, 2, 1000, 0);
        sporadic::refill_new(&mut s, idle_sc, 2, 100000, 0);
        smp::stall(&mut s, &mut a);
        assert_eq!(sched::cur_thread(&s).0, idle.0);
        assert_eq!(sched::cur_sc(&s).0, idle_sc.0);
        assert_eq!(sched::consumed(&s), 0);
        assert_eq!(old_sc.consumed(&s), time - 7);
        assert_eq!(sporadic::head(&s, old_sc).amount, if time == 20 { 987 } else { 1000 });
        schedcontext::unbind_all_tcbs(&mut s, &mut a, old_sc);
        s.zero(old_sc.0, 256);
        s.freed_range = Some((old_sc.0, 256));
        smp::stall(&mut s, &mut a); // repeated stalls while idle are harmless
        a.time += 5;
        syscall::handle_vcpu_exit(&mut s, &mut a, irq, true);
        assert_eq!(sched::cur_time(&s), time, "cancelled completion must not re-charge time");
        assert_eq!(a.acked, if irq == syscall::NO_IRQ { vec![] } else { vec![irq] });
        assert_eq!(sched::cur_sc(&s).0, idle_sc.0);
        a.time += 10;
        syscall::handle_interrupt_entry(&mut s, &mut a, 8);
        assert_eq!(*a.acked.last().unwrap(), 8);
        assert_eq!(sched::cur_sc(&s).0, idle_sc.0);
    }
}

/// Audit F4: DomainSetSet on a thread running on another core. Without a
/// stall, set_domain queues the thread on its core while it runs there;
/// once it blocks, that core's scheduler would pick it from the queue and
/// run a blocked thread. With the stall, its core has switched to idle
/// first, so the thread is queued and current nowhere.
#[test]
fn domain_set_set_stalls_a_thread_running_on_another_core() {
    use fl4_abi::label;
    use fl4_core::{domain, sched, sporadic};
    for remote in [true, false] {
        let mut s = Shared::default();
        let mut a = Machine { smp: Some(s.clone()), ..Default::default() };
        let caller = Tcb(0x20000);
        let target = Tcb(0x30000);
        let sc = Sc(0x40000);
        caller.set_state(&mut s, sched::TS_RUNNING);
        target.set_state(&mut s, sched::TS_RUNNING);
        target.set_affinity(&mut s, 1);
        target.set_sc(&mut s, sc.0);
        sc.set_tcb(&mut s, target.0);
        sporadic::refill_new(&mut s, sc, 2, 1000, 0);
        for cpu in 0..2 {
            let idle = Tcb(0x60000 + cpu * 0x1000);
            let idle_sc = Sc(0x70000 + cpu * 0x1000);
            idle.set_state(&mut s, sched::TS_IDLE);
            idle.set_sc(&mut s, idle_sc.0);
            sporadic::refill_new(&mut s, idle_sc, 2, 100000, 0);
            node_set(&mut s, cpu, node::IDLE_THREAD, idle.0);
            node_set(&mut s, cpu, node::IDLE_SC, idle_sc.0);
        }
        node_set(&mut s, 0, node::CUR_THREAD, caller.0);
        if remote {
            node_set(&mut s, 1, node::CUR_THREAD, target.0);
            node_set(&mut s, 1, node::CUR_SC, sc.0);
        } else {
            let idle = node_get(&s, 1, node::IDLE_THREAD);
            node_set(&mut s, 1, node::CUR_THREAD, idle);
        }
        let extra = [Slot(0x50000), Slot(0x50020), Slot(0x50040)];
        extra[0].set_cap(&mut s, Cap::Thread { ptr: target.0 });
        assert!(domain::decode(&mut s, &mut a, label::DomainSetSet, 1, 0, &extra).is_ok());
        assert!(sched::queued(&s, target), "a runnable thread in the current domain is queued");
        assert_ne!(node_get(&s, 1, node::CUR_THREAD), target.0, "the thread is queued while it runs on core 1");
        assert_eq!(a.events, if remote { vec![("stall", 1)] } else { vec![] });
        assert_eq!(node_get(&s, 0, node::IPI_PENDING) & 2, 2, "core 1 must reschedule");
    }
}

/// Unmapping a PDPT flushes the paging-structure caches after the PML4
/// entry is cleared, as unmapping a page directory or table does: a core
/// running the address space may have walked the entry again since the
/// flush before it.
#[test]
fn pdpt_unmap_flushes_paging_structures_after_clearing_the_entry() {
    use fl4_core::layout::{ks, pptr};
    use fl4_core::obj::ks_set;
    let mut s = Memory::default();
    let mut a = Machine::default();
    let (pool, root, pdpt) = (pptr(0x2000), pptr(0x3000), pptr(0x4000));
    ks_set(&mut s, ks::ASID_TABLE, pool);
    s.write(pool + 8, root);
    let vaddr = 5u64 << 39;
    let slot = root + 5 * 8;
    s.write(slot, 0x4000 | 7);
    vspace::unmap_pdpt(&mut s, &mut a, 1, vaddr, pdpt);
    assert_eq!(s.read(slot), 0);
    assert_eq!(a.events, [("invalidate_asid", 1), ("invalidate_ps", 1)]);
}

/// Audit F5(a): the entry saves FaultIP at the `int $N` itself, so that a
/// remote stall cancelling the entry restarts it rather than skipping it.
/// The handler takes the address from NextIP, whatever FaultIP holds, and
/// reports the instruction once, not two bytes before it.
#[cfg(not(feature = "aarch64"))]
#[test]
fn a_trap_gate_syscall_reports_the_int_instruction() {
    for saved in [0x1000, 0x1002, 0xdead] {
        let mut s = Memory::default();
        let mut a = Machine::default();
        let t = Tcb(0x40_0000);
        node_set(&mut s, 0, node::CUR_THREAD, t.0);
        t.set_flags(&mut s, fl4_abi::consts::tcb_flag::TRAP_SYSCALLS);
        t.set_reg(&mut s, reg::NEXT_IP, 0x1002);
        t.set_reg(&mut s, reg::FAULT_IP, saved);
        syscall::handle_trap_syscall(&mut s, &mut a, 0xa0);
        assert_eq!(t.reg(&s, reg::FAULT_IP), 0x1000, "FaultIP {saved:#x} before the handler");
    }
}

/// X86PML4Flush checks that the cap's ASID still names its PML4, as every
/// other use of a PML4 cap does (and AArch64's VSpace flush): once its
/// ASID pool is deleted the cap keeps `mapped` and the ASID, and a new
/// pool can give that ASID to another address space, whose TLB entries
/// (and the cores running it) the stale cap must not reach.
#[test]
fn pml4_flush_through_a_stale_cap_reaches_no_other_address_space() {
    use fl4_abi::label;
    use fl4_core::error::{Exc, LookupFault, SysError};
    use fl4_core::layout::{ks, pptr};
    use fl4_core::obj::ks_set;
    let (pool, root, other) = (pptr(0x2000), pptr(0x3000), pptr(0x5000));
    let cap = Cap::Pml4 { ptr: root, mapped: true, asid: 1 };
    let flush = |pool_entry: Option<u64>, cap: Cap| {
        let mut s = Memory::default();
        let mut a = Machine::default();
        node_set(&mut s, 0, node::CUR_THREAD, 0x40_0000);
        if let Some(r) = pool_entry {
            ks_set(&mut s, ks::ASID_TABLE, pool);
            s.write(pool + 8, r);
        }
        let ex = [Slot(0); 3];
        let r = vspace::decode(&mut s, &mut a, label::X86PML4Flush, 0, Slot(0x50060), cap, false, 0, &ex);
        (r, a.events)
    };
    // The ASID names the cap's PML4: flushed.
    let (r, events) = flush(Some(root), cap);
    assert!(r.is_ok());
    assert_eq!(events, [("invalidate_asid", 1)]);
    // Unmapped: invalid, as before.
    let (r, events) = flush(Some(root), Cap::Pml4 { ptr: root, mapped: false, asid: 1 });
    assert!(r == Err(Exc::Sys(SysError::InvalidCapability { arg: 0 })));
    assert!(events.is_empty());
    // The pool was deleted: the ASID names nothing.
    let (r, events) = flush(None, cap);
    assert!(r == Err(Exc::Sys(SysError::FailedLookup { source: false, lf: LookupFault::InvalidRoot })));
    assert!(events.is_empty(), "flushed an unassigned ASID: {events:?}");
    // A new pool gave the ASID to another PML4, or to an EPT root.
    for reused in [other, other | 1] {
        let (r, events) = flush(Some(reused), cap);
        assert!(r.is_err());
        assert!(events.is_empty(), "flushed the ASID's new owner {reused:#x}: {events:?}");
    }
    let (r, _) = flush(Some(other), cap);
    assert!(r == Err(Exc::Sys(SysError::InvalidCapability { arg: 0 })));
}

/// A native X86PageMap of a 1 GiB frame needs 1 GiB pages, which the boot
/// code records (`ks::FEATURE_HUGE_PAGES`) when every core takes them:
/// without, the PDPTE's PS bit is reserved and the mapping would fault on
/// every access. It is refused with IllegalOperation, nothing written,
/// the cap included; 2 MiB frames map as before. With the feature the
/// 1 GiB frame maps.
#[test]
fn a_1gib_frame_maps_natively_only_on_cores_with_1gib_pages() {
    use fl4_abi::label;
    use fl4_core::error::{Exc, SysError};
    use fl4_core::layout::{ks, pptr};
    use fl4_core::msg::msg_register;
    use fl4_core::obj::{ks_get, ks_set};
    let (pool, root, pdpt, pd) = (pptr(0x2000), pptr(0x3000), pptr(0x4000), pptr(0x5000));
    let t = Tcb(0x40_0000);
    let vroot = Slot(0x50000);
    let huge = Cap::Frame { ptr: pptr(0x4000_0000), size: FrameSize::Huge, rights: 3, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 };
    let large = Cap::Frame { ptr: pptr(0x20_0000), size: FrameSize::Large, rights: 3, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 };
    let map = |features: u64, cap: Cap, vaddr: u64| {
        let mut s = Memory::default();
        let mut a = Machine::default();
        node_set(&mut s, 0, node::CUR_THREAD, t.0);
        ks_set(&mut s, ks::ASID_TABLE, pool);
        ks_set(&mut s, ks::FEATURES, features);
        s.write(pool + 8, root);
        s.write(root, 0x4000 | 7);
        s.write(pdpt + 2 * 8, 0x5000 | 7);
        vroot.set_cap(&mut s, Cap::Pml4 { ptr: root, mapped: true, asid: 1 });
        let frame = Slot(0x50040);
        frame.set_cap(&mut s, cap);
        t.set_reg(&mut s, msg_register(0), vaddr);
        t.set_reg(&mut s, msg_register(1), 3);
        t.set_reg(&mut s, msg_register(2), 0);
        let r = vspace::decode(&mut s, &mut a, label::X86PageMap, 3, frame, cap, false, 0, &[vroot, Slot(0), Slot(0)]);
        assert_eq!(ks_get(&s, ks::FEATURES), features);
        (r, s, frame)
    };
    let g = 1u64 << 30;
    for features in [0, ks::FEATURE_NX] {
        let (r, s, frame) = map(features, huge, g);
        assert!(r == Err(Exc::Sys(SysError::IllegalOperation)));
        assert_eq!(s.read(pdpt + 8), 0, "no entry");
        assert!(frame.cap(&s) == huge, "the cap is unchanged");
        let (r, s, frame) = map(features, large, 2 * g);
        assert!(r.is_ok());
        assert_eq!(s.read(pd) & !0xfff & 0x000f_ffff_ffff_ffff, 0x20_0000);
        assert!(matches!(frame.cap(&s), Cap::Frame { mapped: true, asid: 1, .. }));
    }
    let (r, s, frame) = map(ks::FEATURE_HUGE_PAGES, huge, g);
    assert!(r.is_ok());
    let e = s.read(pdpt + 8);
    assert_eq!((e & 0x000f_ffff_c000_0000, e & (1 << 7), e & 1), (0x4000_0000, 1 << 7, 1));
    assert!(matches!(frame.cap(&s), Cap::Frame { mapped: true, asid: 1, vaddr, .. } if vaddr == g));
}

/// An IOAPIC route the backend cannot program (a compatibility-format
/// entry cannot name a boot core whose x2APIC ID is above 255,
/// fl4-arch-x86_64 ioapic.rs `map`) issues no IRQHandler: the IRQ stays
/// inactive, the slot empty, and the caller is not restarted.
#[test]
fn an_ioapic_route_the_backend_refuses_issues_no_handler() {
    use fl4_abi::label;
    use fl4_core::error::{Exc, SysError};
    use fl4_core::{msg, sched};
    for remapped in [false, true] {
        for ok in [false, true] {
            let mut s = Memory::default();
            let mut a = Machine { ioapics: 1, ioapic_ok: ok, ..Default::default() };
            let caller = Tcb(0x20000);
            node_set(&mut s, 0, node::CUR_THREAD, caller.0);
            sched::set_thread_state(&mut s, caller, sched::TS_RUNNING);
            let control = Slot(0x30000);
            control.set_cap(&mut s, Cap::IrqControl);
            let root = Slot(0x30100);
            root.set_cap(&mut s, Cap::CNode { ptr: 0x50000, radix: 4, guard_size: 60, guard: 0 });
            let buf = 0x40000;
            // Slot 3 of the CNode, IOAPIC 0 pin 9, level, active low,
            // IRQ 4 (vector 0x34), interrupt-remapping handle 7.
            let args = [3, 64, 0, 9, 1, 1, 4, 7];
            for (i, v) in args.into_iter().enumerate() {
                let i = i as u64;
                if i < msg::N_MSG_REGISTERS {
                    caller.set_reg(&mut s, msg::msg_register(i), v);
                }
                s.write(buf + (i + 1) * 8, v);
            }
            let lbl = if remapped { label::X86IRQIssueIRQHandlerIOAPICRemapped } else { label::X86IRQIssueIRQHandlerIOAPIC };
            let r = interrupt::decode_irq_control(&mut s, &mut a, lbl, 8, control, buf, &[root, Slot(0), Slot(0)]);
            let dest = Slot::index(0x50000, 3);
            assert_eq!(a.routed.len(), 1, "remapped {remapped} ok {ok}");
            let irq = a.routed[0].2 - 0x20;
            if ok {
                assert!(r.is_ok(), "remapped {remapped}");
                assert!(dest.cap(&s) == Cap::IrqHandler { irq }, "remapped {remapped}");
                assert_eq!(interrupt::irq_state(&s, irq), interrupt::IRQ_SIGNAL);
                assert_eq!(caller.state(&s), sched::TS_RESTART);
            } else {
                assert!(r == Err(Exc::Sys(SysError::IllegalOperation)), "remapped {remapped}");
                assert!(dest.cap(&s).is_null(), "remapped {remapped}: a handler was issued");
                assert_eq!(interrupt::irq_state(&s, irq), interrupt::IRQ_INACTIVE, "remapped {remapped}");
                assert_eq!(caller.state(&s), sched::TS_RUNNING, "remapped {remapped}");
            }
        }
    }
}

/// The preemption point reads the pending IRQ line whenever the work count
/// expires, before the budget test (C seL4 preemption.c tests
/// `isIRQPending()` first; the abstract spec's preemptionPoint always calls
/// getActiveIRQ). Here the current SC (null) is inactive, so the budget
/// test alone already preempts.
#[test]
fn preemption_point_reads_the_irq_line_even_without_budget() {
    use fl4_core::layout::ks;
    use fl4_core::obj::{ks_get, ks_set};
    use fl4_core::sched::{self, MAX_WORK_UNITS_PER_PREEMPTION};
    for line in [false, true] {
        let mut s = Memory::default();
        let mut a = Machine { irq_line: line, ..Machine::default() };
        ks_set(&mut s, ks::WORK_UNITS, MAX_WORK_UNITS_PER_PREEMPTION - 1);
        let r = sched::preemption_point(&mut s, &mut a);
        assert!(r == Err(fl4_core::error::Exc::Preempted), "line {line}");
        assert_eq!(a.irq_reads, 1, "line {line}: the IRQ line was not read");
        assert_eq!(ks_get(&s, ks::WORK_UNITS), 0);
        // Below the work limit nothing is read.
        assert!(sched::preemption_point(&mut s, &mut a).is_ok());
        assert_eq!(a.irq_reads, 1);
    }
}

/// Audit r13 T5-02: the IPC buffer limits user space is told (fl4-abi) are
/// the ones the kernel enforces (fl4-core `msg`).
#[test]
fn abi_message_limits_match_the_kernel() {
    assert_eq!(fl4_abi::consts::MSG_MAX_LENGTH, fl4_core::msg::MSG_MAX_LENGTH);
    assert_eq!(fl4_abi::consts::MSG_MAX_EXTRA_CAPS, fl4_core::msg::MSG_MAX_EXTRA_CAPS);
}

/// A signal to a notification bound to a thread running its guest on
/// another core interrupts that core (a reschedule IPI) and stalls nothing:
/// the badge waits in the notification for the owner's entry check.
#[cfg(not(feature = "aarch64"))]
#[test]
fn signal_to_a_remote_guest_kicks_without_stalling() {
    use fl4_core::obj::{Ntfn, NTFN_ACTIVE};
    use fl4_core::{notification, sched};
    for (cpu, running, kicked) in [(1, true, true), (1, false, false), (0, true, false)] {
        let mut s = Memory::default();
        let mut a = Machine::default();
        let guest = Tcb(0x20000);
        let n = Ntfn(0x30000);
        guest.set_state(&mut s, sched::TS_RUNNING_VM);
        guest.set_affinity(&mut s, cpu);
        n.set_bound_tcb(&mut s, guest.0);
        if running {
            node_set(&mut s, cpu, node::CUR_THREAD, guest.0);
        }
        notification::send_signal(&mut s, &mut a, n.0, 0x40);
        assert_eq!(n.state(&s), NTFN_ACTIVE, "cpu {cpu}, running {running}");
        assert_eq!(n.badge(&s), 0x40);
        assert_eq!(guest.state(&s), sched::TS_RUNNING_VM);
        assert!(!a.events.iter().any(|e| e.0 == "stall"), "no stall");
        assert_eq!(a.rescheduled, if kicked { vec![1u64 << cpu] } else { vec![] }, "cpu {cpu}, running {running}");
    }
}
