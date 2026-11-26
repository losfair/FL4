//! The AArch64 local paths of hardware virtualization (`fl4_core::localvm`,
//! `ARMVCPURun`), composed as `fl4-sync`'s wrappers compose them, without
//! the locks: refinement against the general path (word for word, with the
//! same `Arch` effects), decline (only `FAULT_IP` and the clock), and the
//! objects each path has `fl4-sync` lock. The wrappers' locking itself is
//! `fl4-sync`'s unit tests.
#![cfg(feature = "aarch64")]

use fl4_abi::consts::{vcpu_run_stop, vcpu_state_mask as sm};
use fl4_abi::label;
use fl4_abi::syscall as sc;
use fl4_core::capability::{Cap, FrameSize, VM_READ_WRITE};
use fl4_core::layout::{ks, node, reg, tcb as tl};
use fl4_core::localvm::{self, VmLocks, NTFN_BYTES, VCPU_BYTES};
use fl4_core::machine::{Arch, Store};
use fl4_core::msginfo::MessageInfo;
use fl4_core::obj::{ks_set, node_get, node_set, Ntfn, Sc, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE};
use fl4_core::{cspace, interrupt, localtimer, msg, sched, sporadic, syscall, vcpu};
use std::collections::HashMap;

#[derive(Clone, Default)]
struct Memory {
    m: HashMap<u64, u64>,
    cpu: u64,
}
impl Store for Memory {
    fn read(&self, a: u64) -> u64 {
        *self.m.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        self.m.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len)
    }
    fn ks_base(&self) -> u64 {
        KS_BASE
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}
impl Memory {
    fn diff(&self, other: &Memory) -> Vec<u64> {
        let nz = |m: &HashMap<u64, u64>| -> HashMap<u64, u64> { m.iter().filter(|(_, v)| **v != 0).map(|(k, v)| (*k, *v)).collect() };
        let (a, b) = (nz(&self.m), nz(&other.m));
        let mut d: Vec<u64> = a.keys().chain(b.keys()).filter(|k| a.get(k) != b.get(k)).copied().collect();
        d.sort();
        d.dedup();
        d
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Ev {
    Deadline(u64),
    Ack(u64),
    Mask(u64, bool),
    Vspace(u64, u64),
    High(u64, u64),
    Stage2(u64, u64),
    Flush(u64, u64),
    Reschedule(u128),
    Stall(u64),
}

#[derive(Clone)]
struct Machine {
    time: u64,
    ev: Vec<Ev>,
}
impl Arch for Machine {
    fn now(&mut self) -> u64 {
        self.time
    }
    fn set_deadline(&mut self, t: u64) {
        self.ev.push(Ev::Deadline(t));
    }
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
        false
    }
    fn take_pending_irq(&mut self) -> u64 {
        u64::MAX
    }
    fn mask_irq(&mut self, irq: u64, m: bool) {
        self.ev.push(Ev::Mask(irq, m));
    }
    fn ack_irq(&mut self, irq: u64) {
        self.ev.push(Ev::Ack(irq));
    }
    fn set_vspace(&mut self, r: u64, asid: u64) {
        self.ev.push(Ev::Vspace(r, asid));
    }
    fn set_high_vspace(&mut self, r: u64, asid: u64) {
        self.ev.push(Ev::High(r, asid));
    }
    fn set_stage2_vspace(&mut self, r: u64, asid: u64) {
        self.ev.push(Ev::Stage2(r, asid));
    }
    fn vcpu_flush_state(&mut self, vc: u64, mask: u64) {
        self.ev.push(Ev::Flush(vc, mask));
    }
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, _: u64) {}
    fn invalidate_page_structures(&mut self, _: u64) {}
    fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn num_ioapics(&self) -> u64 {
        0
    }
    fn ioapic_pins(&self, _: u64) -> u64 {
        0
    }
    fn port_in(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, _: u64) {}
    fn fpu_sanitise(&mut self, _: u64) {}
    fn fpu_reload(&mut self, _: u64) {}
    fn fpu_release(&mut self, _: u64) {}
    fn remote_stall(&mut self, c: u64) {
        self.ev.push(Ev::Stall(c));
    }
    fn send_reschedule(&mut self, m: u128) {
        self.ev.push(Ev::Reschedule(m));
    }
    fn cache_op(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) {}
    fn hw_access_flag(&self) -> bool {
        true
    }
    fn max_spi(&self) -> u64 {
        0
    }
    fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 {
        0
    }
    fn halt(&mut self) {}
}

const KS_BASE: u64 = 0x1000_0000;
const CPU: u64 = 1;
const IDLE: Tcb = Tcb(0x40_0000);
const IDLE_SC: Sc = Sc(0x41_0000);
const CT: Tcb = Tcb(0x20_0000);
const CSC: Sc = Sc(0x21_0000);
const W: Tcb = Tcb(0x22_0000);
const WSC: Sc = Sc(0x23_0000);
const GUEST: Tcb = Tcb(0x24_0000);
const VC: u64 = 0x80_0000;
const N: u64 = 0x90_0000;
const N2: u64 = 0x91_0000;
const IPC: u64 = 0x60_0000;
const ROOT_CNODE: u64 = 0xa0_0000;
const VCPU_CPTR: u64 = 3;
const STATE_OFF: u64 = 1024;
const TIMER_IRQ: u64 = 0x40;
const NOW: u64 = 1_000_000;
const BUDGET: u64 = 5_000;

fn sc_setup(s: &mut Memory, t: Tcb, sc: Sc, budget: u64, period: u64) {
    t.set_sc(s, sc.0);
    sc.set_tcb(s, t.0);
    sc.set_cpu(s, CPU);
    sporadic::refill_new(s, sc, 4, budget, period);
}

/// Core `CPU` at `NOW`, running the monitor `CT` (native, its own SC,
/// budget left), with bound notification `N`; VCPU `VC` bound to the
/// inactive guest thread `GUEST`, last run on this core; `CT`'s IPC buffer
/// a RAM frame; slot 3 of its CSpace `VC`'s cap.
fn fixture() -> (Memory, Machine) {
    let mut s = Memory { m: HashMap::new(), cpu: CPU };
    let mut a = Machine { time: NOW, ev: Vec::new() };
    node_set(&mut s, CPU, node::CUR_TIME, NOW - 100);
    ks_set(&mut s, ks::DOMAIN_TIME, 1);
    sc_setup(&mut s, IDLE, IDLE_SC, 1 << 40, 0);
    node_set(&mut s, CPU, node::IDLE_THREAD, IDLE.0);
    node_set(&mut s, CPU, node::IDLE_SC, IDLE_SC.0);
    IDLE.set_affinity(&mut s, CPU);
    for (t, sc) in [(CT, CSC), (W, WSC)] {
        t.set_affinity(&mut s, CPU);
        t.set_prio(&mut s, 100);
        sc_setup(&mut s, t, sc, BUDGET, 10 * BUDGET);
    }
    CT.set_state(&mut s, sched::TS_RUNNING);
    node_set(&mut s, CPU, node::CUR_THREAD, CT.0);
    node_set(&mut s, CPU, node::CUR_SC, CSC.0);
    node_set(&mut s, CPU, node::ARMED, NOW + BUDGET);
    GUEST.set_affinity(&mut s, CPU);
    vcpu::init(&mut s, &a, VC);
    s.write(VC + vcpu::TCB, GUEST.0);
    s.write(GUEST.0 + tl::VCPU, VC);
    s.write(VC + vcpu::OWNER_CPU, CPU + 1);
    CT.set_bound_ntfn(&mut s, N);
    Ntfn(N).set_bound_tcb(&mut s, CT.0);
    Ntfn(N).set_state(&mut s, NTFN_IDLE);
    CT.slot(tl::SLOT_BUFFER).set_cap(
        &mut s,
        Cap::Frame { ptr: IPC, size: FrameSize::Small, rights: VM_READ_WRITE, is_device: false, mapped: true, is_ept: false, asid: 1, vaddr: 0x1000 },
    );
    CT.slot(tl::SLOT_CTABLE).set_cap(&mut s, Cap::CNode { ptr: ROOT_CNODE, radix: 4, guard_size: 60, guard: 0 });
    Slot::index(ROOT_CNODE, VCPU_CPTR).set_cap(&mut s, Cap::Vcpu { ptr: VC });
    CT.set_reg(&mut s, reg::NEXT_IP, 0x4004);
    a.ev.clear();
    (s, a)
}

fn run_regs(s: &mut Memory, offset: u64, in_mask: u64, out_mask: u64) {
    CT.set_reg(s, reg::MSG_INFO, MessageInfo::new(label::ARMVCPURun, 0, 0, 3).to_word());
    CT.set_reg(s, reg::CAP, VCPU_CPTR);
    CT.set_reg(s, msg::msg_register(0), offset);
    CT.set_reg(s, msg::msg_register(1), in_mask);
    CT.set_reg(s, msg::msg_register(2), out_mask);
}

/// `CT` in an `ARMVCPURun` of `VC`, through the general path.
fn running(s: &mut Memory, a: &mut Machine) {
    run_regs(s, STATE_OFF, sm::GPRS, sm::GPRS);
    syscall::handle_syscall(s, a, sc::SysCall);
    assert_eq!(CT.state(s), sched::TS_RUNNING_VM);
    a.ev.clear();
}

fn refines(
    s: &Memory,
    a: &Machine,
    local: impl FnOnce(&mut Memory, &mut Machine) -> bool,
    general: impl FnOnce(&mut Memory, &mut Machine),
) -> (Memory, Machine) {
    let (mut ls, mut la) = (s.clone(), a.clone());
    let (mut gs, mut ga) = (s.clone(), a.clone());
    assert!(local(&mut ls, &mut la), "the local path declined");
    general(&mut gs, &mut ga);
    assert_eq!(ls.diff(&gs), Vec::<u64>::new(), "words the local and general paths left differently");
    assert_eq!(la.ev, ga.ev, "Arch effects");
    (ls, la)
}

fn declines(
    s: &Memory,
    a: &Machine,
    local: impl FnOnce(&mut Memory, &mut Machine) -> bool,
    general: impl Fn(&mut Memory, &mut Machine),
) {
    let (mut ls, mut la) = (s.clone(), a.clone());
    assert!(!local(&mut ls, &mut la), "the local path ran");
    let allowed = [
        CT.0 + tl::REGS + reg::FAULT_IP * 8,
        fl4_core::obj::node_base(s, CPU) + node::CUR_TIME,
        fl4_core::obj::node_base(s, CPU) + node::CONSUMED,
    ];
    for w in ls.diff(s) {
        assert!(allowed.contains(&w), "a declined local path wrote {w:#x}");
    }
    assert!(la.ev.is_empty(), "a declined local path made Arch calls: {:?}", la.ev);
    let (mut gs, mut ga) = (s.clone(), a.clone());
    general(&mut gs, &mut ga);
    general(&mut ls, &mut la);
    assert_eq!(ls.diff(&gs), Vec::<u64>::new());
    assert_eq!(la.ev, ga.ev);
}

/// The objects `l` has `fl4-sync` lock, as (address, bytes): each nonzero
/// address once, sorted.
fn locked(l: &VmLocks) -> Vec<(u64, u64)> {
    let mut v: Vec<(u64, u64)> = l.objects.iter().copied().filter(|&(o, _)| o != 0).collect();
    v.sort();
    v.dedup();
    v
}

/// The slot and VCPU the current thread's capability register names, as
/// `fl4-sync`'s locked lookup finds them; VCPU 0 for none.
fn vcpu_cap(s: &Memory) -> (Slot, u64) {
    let t = sched::cur_thread(s);
    match cspace::lookup_slot(s, t, t.reg(s, reg::CAP)).ok().map(|r| (r.slot, r.slot.cap(s))) {
        Some((slot, Cap::Vcpu { ptr })) => (slot, ptr),
        _ => (Slot(0), 0),
    }
}

/// `fl4-sync`'s `local_arm_vcpu_run`, its locks aside, with `hw` the
/// kernel's word on the VCPU's hardware state.
fn run_local(hw: bool) -> impl Fn(&mut Memory, &mut Machine) -> bool {
    move |s, a| {
        let (slot, vc) = vcpu_cap(s);
        let l = localvm::vm_locks(s, vc);
        if l.vcpu == 0 {
            return false;
        }
        let hw = !localvm::vcpu_guest(s, vc).is_null() && hw;
        localvm::handle_arm_vcpu_run_local(s, a, sc::SysCall, slot, vc, l.ntfn, hw)
    }
}

/// `fl4-sync`'s `local_arm_vm_entry`, its lock of the notification aside.
fn local_arm_vm_entry(s: &Memory) -> bool {
    localvm::arm_vm_entry_ready(s, localvm::vm_locks(s, localvm::cur_vcpu(s)).ntfn)
}
fn run_general(s: &mut Memory, a: &mut Machine) {
    syscall::handle_syscall(s, a, sc::SysCall)
}

#[test]
fn arm_vcpu_run_beside_the_gate_refines_handle_syscall() {
    let (mut s, a) = fixture();
    s.write(IPC + STATE_OFF + 64 * 8 + reg::X0 * 8, 0x1234);
    for (in_mask, out_mask) in [(sm::GPRS, sm::GPRS), (0, 0), (sm::ALL & !sm::VGIC_LR & !sm::VGIC, sm::GPRS)] {
        let mut s2 = s.clone();
        run_regs(&mut s2, STATE_OFF, in_mask, out_mask);
        let (ls, _) = refines(&s2, &a, run_local(true), run_general);
        assert_eq!(CT.state(&ls), sched::TS_RUNNING_VM);
        assert_eq!(ls.read(VC + vcpu::RUN_CALLER), CT.0);
    }
    // Refused: an unaligned state offset, a mask out of range.
    for (off, in_mask) in [(32, 0), (STATE_OFF, 1 << 6)] {
        let mut s2 = s.clone();
        run_regs(&mut s2, off, in_mask, 0);
        let (ls, _) = refines(&s2, &a, run_local(true), run_general);
        assert_eq!(CT.state(&ls), sched::TS_RUNNING);
        assert_ne!(MessageInfo::from_word_clamped(CT.reg(&ls, reg::MSG_INFO)).label, 0, "an error reply");
    }
}

#[test]
fn arm_vcpu_run_declines_what_is_another_cores_or_the_gates() {
    let (mut s, a) = fixture();
    run_regs(&mut s, STATE_OFF, sm::GPRS, sm::GPRS);
    let untouched = |s2: &Memory, hw: bool| {
        let mut ls = s2.clone();
        assert!(!run_local(hw)(&mut ls, &mut a.clone()));
        assert!(ls.diff(s2).is_empty());
    };
    // The hardware state is live elsewhere, or the VMID unallocated.
    untouched(&s, false);
    let cases: Vec<Box<dyn Fn(&mut Memory)>> = vec![
        Box::new(|s| s.write(VC + vcpu::OWNER_CPU, CPU + 2)), // Last run on another core.
        Box::new(|s| GUEST.set_state(s, sched::TS_RUNNING)),  // The guest thread runs.
        Box::new(|s| s.write(VC + vcpu::RUN_CALLER, W.0)),    // Another run in flight.
        Box::new(|s| s.write(GUEST.0 + tl::VCPU, 0)),
        Box::new(|s| Ntfn(N).set_state(s, NTFN_ACTIVE)),     // Ends the run at once.
        Box::new(|s| sched::set_action(s, sched::ACTION_CHOOSE_NEW)),
    ];
    for change in cases {
        let mut s2 = s.clone();
        change(&mut s2);
        untouched(&s2, true);
    }
    // Budget spent, a timer due: after the clock, the gate.
    let mut spent = s.clone();
    node_set(&mut spent, CPU, node::CONSUMED, BUDGET);
    declines(&spent, &a, run_local(true), run_general);
    let mut due = s.clone();
    fl4_core::timer::insert(&mut due, W, NOW - 1, 7);
    declines(&due, &a, run_local(true), run_general);
    // No VCPU cap: declined before anything runs.
    let mut s2 = s.clone();
    CT.set_reg(&mut s2, reg::CAP, 0xe);
    assert_eq!(vcpu_cap(&s2).1, 0);
    untouched(&s2, true);
    // It locks the VCPU and the caller's bound notification (another core
    // holding either: the gate).
    assert!(localvm::is_vm_syscall(&s, CT, sc::SysCall));
    let l = localvm::vm_locks(&s, vcpu_cap(&s).1);
    assert_eq!((l.vcpu, l.ntfn), (VC, N));
    assert_eq!(locked(&l), vec![(VC, VCPU_BYTES), (N, NTFN_BYTES)]);
}

#[test]
fn the_check_before_the_guest_beside_the_gate_writes_nothing() {
    let (mut s, mut a) = fixture();
    assert!(!local_arm_vm_entry(&s), "not running a VCPU");
    running(&mut s, &mut a);
    let before = s.clone();
    assert!(local_arm_vm_entry(&s));
    let mut serial = s.clone();
    vcpu::check(&mut serial, &mut a, CT);
    assert!(serial.diff(&before).is_empty() && s.diff(&before).is_empty());
    Ntfn(N).set_state(&mut s, NTFN_ACTIVE);
    assert!(!local_arm_vm_entry(&s));
    // The notification it locks (another core holding it: the gate).
    assert_eq!(localvm::cur_vcpu(&s), VC);
    assert_eq!(localvm::vm_locks(&s, VC).ntfn, N);
}

fn exit_local(stop: u64, w: (u64, u64, u64), hvc: Option<(Tcb, u64)>) -> impl Fn(&mut Memory, &mut Machine) -> bool {
    // `fl4-sync`'s `local_arm_vcpu_run_exit`, its lock of the VCPU aside.
    move |s, a| {
        let vc = localvm::vcpu_locks(localvm::cur_vcpu(s)).vcpu;
        vc != 0 && localvm::handle_arm_vcpu_run_exit_local(s, a, vc, stop, w.0, w.1, w.2, hvc)
    }
}
fn exit_general(stop: u64, w: (u64, u64, u64), hvc: Option<(Tcb, u64)>) -> impl Fn(&mut Memory, &mut Machine) {
    move |s, a| {
        if let Some((g, elr)) = hvc {
            if g.reg(s, reg::ELR_EL1) == elr.wrapping_sub(4) {
                g.set_reg(s, reg::ELR_EL1, elr);
            }
        }
        syscall::handle_vcpu_run_exit(s, a, stop, w.0, w.1, w.2)
    }
}

#[test]
fn run_exits_beside_the_gate_refine_handle_vcpu_run_exit() {
    let (mut s, mut a) = fixture();
    running(&mut s, &mut a);
    GUEST.set_reg(&mut s, reg::X0, 0xdead);
    for (stop, w) in [(vcpu_run_stop::VMFAULT, (0x9200_0007, 0x5000_0000, 0x5000_0010)), (vcpu_run_stop::VCPUFAULT, (0x5a00_0001, 1, 2))] {
        let (ls, _) = refines(&s, &a, exit_local(stop, w, None), exit_general(stop, w, None));
        assert_eq!(CT.state(&ls), sched::TS_RUNNING);
        assert_eq!(ls.read(IPC + STATE_OFF + 64 * 8 + reg::X0 * 8), 0xdead);
    }
    // An HVC, its PC rewound by the entry.
    let mut h = s.clone();
    GUEST.set_reg(&mut h, reg::ELR_EL1, 0x8000 - 4);
    let hvc = Some((GUEST, 0x8000));
    let (ls, _) = refines(&h, &a, exit_local(vcpu_run_stop::VCPUFAULT, (0x5800_0000, 0, 0), hvc), exit_general(vcpu_run_stop::VCPUFAULT, (0x5800_0000, 0, 0), hvc));
    assert_eq!(GUEST.reg(&ls, reg::ELR_EL1), 0x8000);
    // Budget spent (a timeout fault may follow), a timer due: the gate.
    let w = (1, 2, 3);
    let mut spent = s.clone();
    node_set(&mut spent, CPU, node::CONSUMED, BUDGET);
    declines(&spent, &a, exit_local(vcpu_run_stop::VMFAULT, w, None), exit_general(vcpu_run_stop::VMFAULT, w, None));
    let mut due = h.clone();
    fl4_core::timer::insert(&mut due, W, NOW - 1, 7);
    declines(&due, &a, exit_local(vcpu_run_stop::VCPUFAULT, w, hvc), exit_general(vcpu_run_stop::VCPUFAULT, w, hvc));
    // It locks the VCPU alone (another core holding it: the gate).
    assert_eq!(localvm::cur_vcpu(&s), VC);
    assert_eq!(locked(&localvm::vcpu_locks(VC)), vec![(VC, VCPU_BYTES)]);
}

/// `fl4-sync`'s `local_vm_timer_irq`, its locks aside.
fn timer_local(s: &mut Memory, a: &mut Machine) -> bool {
    let Some(p) = localtimer::plan_timer_irq(s, TIMER_IRQ) else { return false };
    let l = localvm::vm_timer_locks(s, localvm::cur_vcpu(s), &p);
    l.vcpu != 0 && localvm::handle_vm_timer_irq_local(s, a, TIMER_IRQ, &p, l.ntfn)
}
fn timer_general(s: &mut Memory, a: &mut Machine) {
    syscall::handle_interrupt_entry(s, a, TIMER_IRQ)
}

/// The kernel timer while the guest runs: nothing due, or a due timer
/// whose signal wakes no thread, beside the gate; a refill (which would
/// switch back to the guest's thread, setting its Stage-2 root) or a wake,
/// at the gate.
#[test]
fn the_timer_while_a_guest_runs_beside_the_gate_refines_handle_interrupt_entry() {
    let (mut s, mut a) = fixture();
    running(&mut s, &mut a);
    ks_set(&mut s, ks::IRQ_STATE + TIMER_IRQ * 8, interrupt::IRQ_TIMER);
    let (_, la) = refines(&s, &a, timer_local, timer_general);
    assert!(la.ev.contains(&Ev::Ack(TIMER_IRQ)));
    let mut due = s.clone();
    W.set_bound_ntfn(&mut due, N2);
    Ntfn(N2).set_bound_tcb(&mut due, W.0);
    Ntfn(N2).set_state(&mut due, NTFN_IDLE);
    fl4_core::timer::insert(&mut due, W, NOW - 1, 7);
    let (ls, _) = refines(&due, &a, timer_local, timer_general);
    assert_eq!(Ntfn(N2).state(&ls), NTFN_ACTIVE);
    // The due timer's notification N2 is locked beside VC and N.
    let l = localvm::vm_timer_locks(&due, VC, &localtimer::plan_timer_irq(&due, TIMER_IRQ).unwrap());
    let objs: Vec<u64> = locked(&l).iter().map(|&(o, _)| o).collect();
    assert!([VC, N, N2].iter().all(|o| objs.contains(o)), "{objs:x?}");
    let mut rr = s.clone();
    sporadic::refill_new(&mut rr, CSC, 4, BUDGET, 0);
    node_set(&mut rr, CPU, node::CONSUMED, BUDGET);
    declines(&rr, &a, timer_local, timer_general);
    let mut sig = s.clone();
    Ntfn(N).set_state(&mut sig, NTFN_ACTIVE);
    declines(&sig, &a, timer_local, timer_general);
}

/// The guest thread's own timer is the earliest (its bound notification in
/// the timer plan): the kernel timer while its guest runs still goes beside
/// the gate, the notification named twice (the plan's and the caller's),
/// which `fl4-sync` locks once.
#[test]
fn the_timer_with_the_callers_own_timer_armed_goes_beside_the_gate() {
    let (mut s, mut a) = fixture();
    running(&mut s, &mut a);
    ks_set(&mut s, ks::IRQ_STATE + TIMER_IRQ * 8, interrupt::IRQ_TIMER);
    fl4_core::timer::insert(&mut s, CT, NOW + 10_000, 9);
    let p = localtimer::plan_timer_irq(&s, TIMER_IRQ).unwrap();
    assert!(p.objects[..p.n].iter().any(|&(o, _)| o == N));
    let l = localvm::vm_timer_locks(&s, VC, &p);
    assert_eq!(l.objects.iter().filter(|&&(o, _)| o == N).count(), 2);
    assert_eq!(locked(&l).iter().filter(|&&(o, _)| o == N).count(), 1);
    refines(&s, &a, timer_local, timer_general);
}

/// Reschedule IPIs owed to cores past 63 go in `IPI_PENDING_HI` and reach
/// the backend in the high word of the mask.
#[test]
fn reschedule_ipis_reach_cores_past_63() {
    let (mut s, mut a) = fixture();
    assert!(fl4_core::layout::MAX_NODES == 128);
    let cores = [0u64, 63, 64, 70, 127];
    assert!(!cores.contains(&CPU));
    assert!(fl4_core::smp::none_pending(&s, CPU));
    for c in cores {
        fl4_core::smp::remote_reschedule(&mut s, &mut a, c);
    }
    // Its own core owes nothing.
    fl4_core::smp::remote_reschedule(&mut s, &mut a, CPU);
    assert!(!fl4_core::smp::none_pending(&s, CPU));
    assert_eq!(node_get(&s, CPU, node::IPI_PENDING), 1 | 1 << 63);
    assert_eq!(node_get(&s, CPU, node::IPI_PENDING_HI), 1 | 1 << 6 | 1 << 63);
    fl4_core::smp::send_pending(&mut s, &mut a);
    let want = cores.iter().fold(0u128, |m, &c| m | fl4_core::machine::core_bit(c));
    assert_eq!(a.ev, vec![Ev::Reschedule(want)]);
    assert!(fl4_core::smp::none_pending(&s, CPU));
}

const EP: u64 = 0x92_0000;
const R: u64 = 0x93_0000;

/// A data abort of `CT` beside the gate (`handle_vm_fault_local`), with `W`
/// waiting for faults on `CT`'s fault endpoint; `bind` binds `W` a VCPU.
fn vm_fault_beside_the_gate(bind: bool) -> (bool, Memory) {
    use fl4_core::obj::{Ep, Reply, EP_RECV};
    let (mut s, mut a) = fixture();
    CT.slot(tl::SLOT_FAULT_HANDLER)
        .set_cap(&mut s, Cap::Endpoint { ptr: EP, badge: 7, send: true, recv: false, grant: true, grant_reply: false });
    Ep(EP).set_queue(&mut s, W.0, W.0, EP_RECV);
    W.set_state(&mut s, sched::TS_BLOCKED_ON_RECV);
    W.set_reply_obj(&mut s, R);
    Reply(R).set_tcb(&mut s, W.0);
    if bind {
        s.write(W.0 + tl::VCPU, VC);
    }
    // ESR_EL1: a data abort from EL0 (EC 0x24), a level-3 translation
    // fault on a write.
    let esr = (0x24 << 26) | (1 << 25) | (1 << 6) | 0x07;
    let ran = syscall::handle_vm_fault_local(&mut s, &mut a, 0x7000_1000, esr);
    (ran, s)
}

/// The VM fault's fast path hands the fault to a waiting handler on this
/// core; not to one with a bound VCPU, whose Stage-2 root `switch_to`
/// would install, which may allocate a VMID (the gate's).
#[test]
fn a_vm_fault_beside_the_gate_switches_to_its_handler_but_not_to_a_vcpu_thread() {
    let (ran, s) = vm_fault_beside_the_gate(false);
    assert!(ran);
    assert_eq!(sched::cur_thread(&s).0, W.0);
    assert_eq!(CT.state(&s), sched::TS_BLOCKED_ON_REPLY);
    let (ran, s) = vm_fault_beside_the_gate(true);
    assert!(!ran);
    assert_eq!(sched::cur_thread(&s).0, CT.0);
    assert_eq!(CT.state(&s), sched::TS_RUNNING);
}
