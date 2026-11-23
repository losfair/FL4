//! Kernel entry and exit: entry.S has saved the user registers into the
//! current TCB; dispatch to fl4-core, then run whichever thread is current.
use crate::kprintln;
use fl4_arch_aarch64::arch::PhysArch;
use fl4_arch_aarch64::{cpu, fpu, gic, mmu, percpu, smp, timer, vcpu};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{sched, syscall};
use fl4_store::{Phys, PhysStore};
use fl4_sync::SerialGate;

core::arch::global_asm!(include_str!("entry.S"));

extern "C" {
    fn fl4_restore_user(regs: u64) -> !;
    fn fl4_idle(stack_top: u64) -> !;
    fn fl4_nvhe_enter_guest(regs_pa: u64, vcpu_pa: u64, vttbr: u64, hcr_nvhe: u64, trap_fp: u64, stack_top: u64) -> !;
}

const KIND_SYNC: u64 = 0;
const KIND_IRQ: u64 = 1;
const KIND_RETRY: u64 = 3;

/// ESR_EL1 exception classes from EL0.
const EC_UNKNOWN: u64 = 0x00;
const EC_FP: u64 = 0x07;
const EC_SVC64: u64 = 0x15;
const EC_HVC64: u64 = 0x16;
const EC_IABT_LOW: u64 = 0x20;
const EC_DABT_LOW: u64 = 0x24;

static mut KS_BASE: u64 = 0;

/// The serial gate (DESIGN.md §7).
pub static GATE: SerialGate = SerialGate::new();

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

pub fn store() -> PhysStore {
    PhysStore { frame_masks: (0, 0), ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64 }
}

fn service_remote() -> bool {
    smp::service(|| {
        let mut s = store();
        let mut a = PhysArch;
        fl4_core::smp::stall(&mut s, &mut a);
        // The stall puts the stalled thread back in its queue, which may
        // be another core's if the caller moved it: that core is owed a
        // reschedule IPI, and this core is not in an entry that sends it.
        fl4_core::smp::send_pending(&mut s, &mut a);
    })
}

/// Take the serial gate (on a multi-core system), servicing remote calls
/// while waiting. Returns false when a stall cancelled the entry.
pub fn lock() -> bool {
    let stalled = core::cell::Cell::new(false);
    if smp::multi() {
        GATE.acquire(&Phys, percpu::cpu_index() as u64, || {
            if service_remote() {
                stalled.set(true);
            }
        });
        percpu::get().gate_held.set(true);
    }
    !stalled.get()
}

/// Before `exit` takes the serial gate after an entry that ran without it
/// (a local path): the current thread's entry is over, so a remote stall
/// serviced while waiting must resume it where it now continues. The stall
/// (`fl4_core::smp::stall`) makes a running thread restart at `FAULT_IP`,
/// which is right for an entry it cancels before it ran; here `FAULT_IP`
/// is still that of the thread's last kernel entry. For a thread a local
/// path has just woken from `ReplyRecv` or `Recv`, that is the syscall
/// instruction, which would run again with the received badge in the
/// capability register (l4h issue 227: a cap fault in its receive phase
/// on the badge). Only this core changes the thread's context until the
/// stall is acknowledged.
#[inline(always)]
fn settle_resume_point(s: &mut PhysStore, ct: Tcb) {
    if ct.state(s) == sched::TS_RUNNING && ct.0 != node_get(s, s.cur_cpu(), node::IDLE_THREAD) {
        let ip = ct.reg(s, reg::NEXT_IP);
        ct.set_reg(s, reg::FAULT_IP, ip);
    }
}

fn unlock() {
    let pc = percpu::get();
    if pc.gate_held.get() {
        pc.gate_held.set(false);
        GATE.release(&Phys);
    }
}

struct KernelEnv;

impl fl4_sync::EntryEnv for KernelEnv {
    type S = PhysStore;
    type A = PhysArch;
    type M = Phys;
    fn cpu(&self) -> u64 {
        percpu::cpu_index() as u64
    }
    fn multi(&self) -> bool {
        smp::multi()
    }
    fn store(&self) -> PhysStore {
        PhysStore { frame_masks: (0, 0), ks_base: unsafe { KS_BASE }, cpu: self.cpu() }
    }
    fn arch(&self) -> PhysArch {
        PhysArch
    }
    fn mem(&self) -> &Phys {
        &Phys
    }
    fn service_remote(&self) -> bool {
        service_remote()
    }
    fn holding_gate(&self) {
        let pc = percpu::get();
        pc.gate_held.set(true);
    }
}

fn run_entry(irq: bool, body: impl FnMut(&mut PhysStore, &mut PhysArch)) -> bool {
    fl4_sync::run_entry(&KernelEnv, &GATE, irq, body)
}

/// Back to the interrupted thread without a kernel entry.
fn resume() -> ! {
    let s = store();
    let ct = sched::cur_thread(&s);
    let run_v = if ct.state(&s) == sched::TS_RUNNING_VM {
        s.read(ct.0 + tl::RUN_VCPU)
    } else {
        0
    };
    let (v, target) = if run_v != 0 {
        (run_v, Tcb(s.read(run_v + fl4_core::vcpu::TCB)))
    } else {
        (fl4_core::vcpu::bound(&s, ct), ct)
    };
    if v != 0 && cpu::is_el2_nvhe() {
        vcpu::nvhe_prepare_guest(v);
        mmu::publish_tables();
        let pc = percpu::get();
        let me = percpu::cpu_index();
        unsafe {
            fl4_nvhe_enter_guest(
                fl4_core::layout::paddr(target.0 + tl::REGS),
                fl4_core::layout::paddr(v),
                percpu::vttbr(me),
                vcpu::nvhe_guest_hcr(v),
                pc.guest_fp_trap.get() as u64,
                pc.stack_top.load(core::sync::atomic::Ordering::Relaxed),
            )
        }
    }
    if v != 0 {
        vcpu::enter_guest_hcr(v);
    }
    mmu::publish_tables();
    unsafe { fl4_restore_user(target.0 + tl::REGS) }
}

enum TakenIrq {
    Normal(u64),
    VgicMaint(u64),
    Vppi(u64),
}

/// Acknowledge an interrupt; returns what kind of kernel entry it needs.
fn take_irq() -> Option<TakenIrq> {
    let raw = gic::ack();
    let id = raw & 0x3ff;
    if raw == gic::SPURIOUS || id >= 1020 {
        return None;
    }
    percpu::get().iar.set(raw);
    if cpu::has_el2() && id == irq::VGIC_MAINT_ID {
        let eisr = vcpu::read_vgic_eisr();
        if !cpu::is_el2_nvhe() {
            vcpu::mask_ppi_vgic();
        }
        gic::eoi(raw);
        return Some(TakenIrq::VgicMaint(eisr));
    }
    if cpu::has_el2() && id == irq::TIMER_ID {
        vcpu::mask_ppi_vtimer();
        gic::eoi(raw);
        return Some(TakenIrq::Vppi(irq::TIMER_ID));
    }
    if id == timer::timer_irq_id() {
        // A stale timer interrupt (l4h 0012): the deadline it was for has
        // been replaced by a later one.
        if timer::early() {
            gic::eoi(raw);
            return None;
        }
        timer::quiesce();
    }
    if id == irq::REMOTE_CALL_ID {
        service_remote();
    }
    Some(TakenIrq::Normal(irq::of(id, percpu::cpu_index() as u64)))
}

/// Handle an exception/IRQ from a guest entered via `ARMVCPURun` (caller `t`
/// stays in `TS_RUNNING_VM` with its own `FAULT_IP` untouched).
#[allow(clippy::too_many_arguments)]
fn fl4_entry_vcpu_run(
    s: &mut PhysStore,
    run_v: u64,
    guest_tcb: Tcb,
    kind: u64,
    esr: u64,
    far: u64,
    s2_ipa: u64,
    eff_hpfar: u64,
) -> ! {
    use fl4_abi::consts::vcpu_run_stop;
    let ec = esr >> 26;
    if kind == KIND_IRQ {
        let (quiesce_cntv, quiesce_vgic) = if cpu::is_el2_nvhe() {
            vcpu::nvhe_irq_quiesce_flags(run_v)
        } else {
            (false, false)
        };
        let taken = take_irq();
        if cpu::is_el2_nvhe() {
            let q_vgic = quiesce_vgic && !matches!(taken, Some(TakenIrq::VgicMaint(_)));
            vcpu::nvhe_quiesce_after_irq(quiesce_cntv, q_vgic);
        }
        match taken {
            None => resume(),
            Some(TakenIrq::VgicMaint(eisr)) => {
                run_entry(true, |s, a| syscall::handle_vcpu_run_exit(s, a, vcpu_run_stop::VGIC_MAINT, eisr, 0, 0));
            }
            Some(TakenIrq::Vppi(irq_id)) => {
                run_entry(true, |s, a| syscall::handle_vcpu_run_vppi(s, a, irq_id));
            }
            Some(TakenIrq::Normal(irq)) => {
                run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, irq));
            }
        }
        exit()
    }
    if kind != KIND_SYNC {
        vcpu::record_exit_regs(run_v, far, eff_hpfar, esr);
        run_entry(false, |s, a| syscall::handle_vcpu_run_exit(s, a, vcpu_run_stop::VCPUFAULT, esr, far, eff_hpfar));
        exit()
    }
    if ec == EC_FP && guest_tcb.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED == 0 {
        fpu::lazy_load(guest_tcb.0);
        resume()
    }
    vcpu::record_exit_regs(run_v, far, eff_hpfar, esr);
    if ec == EC_IABT_LOW || ec == EC_DABT_LOW {
        run_entry(false, |s, a| syscall::handle_vcpu_run_exit(s, a, vcpu_run_stop::VMFAULT, esr, s2_ipa, far));
    } else if ec == EC_HVC64 {
        // HVC is the one exit here that is not raised again when the guest
        // resumes: its ELR is already past the instruction. (A software
        // step's ELR is past the stepped instruction too, but the step
        // stays pending and should be taken again before the next one.)
        // The caller stays `TS_RUNNING_VM` when a remote stall cancels this
        // entry, and its next `ARMVCPURun` round enters the guest at the
        // saved ELR: the guest would go on after an HVC its VMM never saw.
        // So the guest's PC is the HVC until the entry runs (as `FAULT_IP`
        // is for a bound VCPU's HVC, in `fl4_entry`), and goes past it
        // again only in the body, before `complete_run` reads the guest
        // state for the VMM. TCB invocations on a guest's TCB stall the
        // thread running it, cancelling this entry before the body runs;
        // the check below is defensive against moving a PC that is no
        // longer the rewound one.
        let elr = guest_tcb.reg(s, reg::ELR_EL1);
        guest_tcb.set_reg(s, reg::ELR_EL1, elr.wrapping_sub(4));
        run_entry(false, |s, a| {
            if guest_tcb.reg(s, reg::ELR_EL1) == elr.wrapping_sub(4) {
                guest_tcb.set_reg(s, reg::ELR_EL1, elr);
            }
            syscall::handle_vcpu_run_exit(s, a, vcpu_run_stop::VCPUFAULT, esr, far, eff_hpfar)
        });
    } else {
        run_entry(false, |s, a| syscall::handle_vcpu_run_exit(s, a, vcpu_run_stop::VCPUFAULT, esr, far, eff_hpfar));
    }
    exit()
}

/// Called by entry.S for every exception from EL0 or a guest EL1/EL0.
#[no_mangle]
extern "C" fn fl4_entry(kind: u64, esr: u64, far: u64, hpfar: u64) -> ! {
    let s = &mut store();
    let t = sched::cur_thread(s);
    let run_v = if t.state(s) == sched::TS_RUNNING_VM {
        s.read(t.0 + tl::RUN_VCPU)
    } else {
        0
    };
    let bound_v = if run_v == 0 { fl4_core::vcpu::bound(s, t) } else { 0 };
    let eff_v = if run_v != 0 { run_v } else { bound_v };
    let guest_tcb = if run_v != 0 {
        Tcb(s.read(run_v + fl4_core::vcpu::TCB))
    } else {
        t
    };
    let elr = guest_tcb.reg(s, reg::ELR_EL1);
    let ec = esr >> 26;
    let mut s2_ipa = 0u64;
    let mut eff_hpfar = hpfar;
    if eff_v != 0 {
        if cpu::is_el2_nvhe() {
            vcpu::nvhe_post_exit(eff_v, kind);
            if kind == KIND_RETRY {
                resume();
            }
            // Stage-2 permission faults were already resolved in EL2 via AT S1E1R.
            s2_ipa = ((hpfar & 0x0000_0fff_ffff_fff0) << 8) | (far & 0xfff);
        } else {
            // Sync hardware auto-clear of HCR_EL2.VSE before any early `resume()`
            // (e.g. AT S1E1R retry) or `set_host_hcr()` overwrites HCR_EL2.
            vcpu::sync_exit_hcr(eff_v);
            // Stage-2 permission fault (not S1PTW): resolve VA->IPA via AT S1E1R
            // while HCR_EL2.TGE is still 0.
            if kind == KIND_SYNC
                && (ec == EC_IABT_LOW || ec == EC_DABT_LOW)
                && (esr & 0x3c) == 0x0c
                && (esr & (1 << 7)) == 0
            {
                match vcpu::resolve_s2_perm_ipa(far) {
                    Some(ipa) => {
                        s2_ipa = ipa;
                        eff_hpfar = (ipa >> 8) & 0x0000_0fff_ffff_fff0;
                    }
                    None => resume(),
                }
            } else {
                s2_ipa = ((hpfar & 0x0000_0fff_ffff_fff0) << 8) | (far & 0xfff);
            }
            vcpu::set_host_hcr();
        }
    }
    if run_v != 0 {
        fl4_entry_vcpu_run(s, run_v, guest_tcb, kind, esr, far, s2_ipa, eff_hpfar);
    }
    let v = bound_v;
    if kind == KIND_IRQ {
        // The restart PC first: taking a remote-call SGI services a stall,
        // and once that is acknowledged the calling core may restart,
        // rewrite or delete `t` (and retype its memory). Not a word of `t`
        // after `take_irq`. Harmless when the interrupt needs no entry.
        t.set_reg(s, reg::FAULT_IP, elr);
        let (quiesce_cntv, quiesce_vgic) = if cpu::is_el2_nvhe() && v != 0 {
            vcpu::nvhe_irq_quiesce_flags(v)
        } else {
            (false, false)
        };
        let taken = take_irq();
        if cpu::is_el2_nvhe() && v != 0 {
            let q_vgic = quiesce_vgic && !matches!(taken, Some(TakenIrq::VgicMaint(_)));
            vcpu::nvhe_quiesce_after_irq(quiesce_cntv, q_vgic);
        }
        match taken {
            None => resume(),
            Some(TakenIrq::VgicMaint(eisr)) => {
                run_entry(true, |s, a| syscall::handle_vgic_maintenance_entry(s, a, eisr));
            }
            Some(TakenIrq::Vppi(irq_id)) => {
                run_entry(true, |s, a| syscall::handle_vppi_event_entry(s, a, irq_id));
            }
            Some(TakenIrq::Normal(irq)) => {
                run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, irq));
            }
        }
        exit()
    }
    if v != 0 {
        if kind != KIND_SYNC {
            t.set_reg(s, reg::FAULT_IP, elr);
            vcpu::record_exit_regs(v, far, hpfar, esr);
            run_entry(false, |s, a| syscall::handle_vcpu_fault(s, a, esr));
            exit()
        }
        if ec == EC_FP {
            if t.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED == 0 {
                fpu::lazy_load(t.0);
                resume()
            }
        }
        // HVC (EC=0x16) advances ELR_EL2 past the instruction like SVC: record
        // FAULT_IP as elr - 4 so MCS budget exhaustion or a remote stall
        // restarts the HVC instead of silently skipping it.
        t.set_reg(s, reg::FAULT_IP, if ec == EC_HVC64 { elr.wrapping_sub(4) } else { elr });
        vcpu::record_exit_regs(v, far, eff_hpfar, esr);
        if ec == EC_IABT_LOW || ec == EC_DABT_LOW {
            run_entry(false, |s, a| syscall::handle_vm_fault(s, a, s2_ipa, esr));
        } else {
            run_entry(false, |s, a| syscall::handle_vcpu_fault(s, a, esr));
        }
        exit()
    }
    if kind != KIND_SYNC {
        // An SError from user code: asynchronous, so there is no faulting
        // instruction to blame. Report it as a user exception.
        t.set_reg(s, reg::FAULT_IP, elr);
        run_entry(false, |s, a| syscall::handle_user_exception(s, a, esr, 0));
        exit()
    }
    // FP/SIMD trap: lazy switching (fpu.rs). A thread with FP/SIMD
    // disabled gets the fault instead.
    if ec == EC_FP {
        if t.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED == 0 {
            fpu::lazy_load(t.0);
            resume()
        }
    }
    // A syscall restarts at the SVC, for when a remote stall cancels the
    // entry before handle_syscall runs.
    t.set_reg(s, reg::FAULT_IP, if ec == EC_SVC64 { elr.wrapping_sub(4) } else { elr });
    trace(kind, esr, elr, t.0, s);
    let number = t.reg(s, reg::SYSCALL) as i64;
    if ec == EC_SVC64 {
        // The local paths beside the serial gate (fl4_sync::run_syscall),
        // as on x86_64.
        let local = |s: &mut PhysStore, a: &mut PhysArch| fl4_sync::local_syscall(s, a, &Phys, number, |_, _| {});
        let body = |s: &mut PhysStore, a: &mut PhysArch| dispatch_syscall(s, a, number);
        fl4_sync::run_syscall(&KernelEnv, &GATE, number, local, body);
    } else {
        run_entry(false, |s, a| dispatch(s, a, ec, esr, far, elr));
    }
    exit()
}

/// `dispatch` for a syscall, through `handle_syscall_fast`: whether a fast
/// path ran (`fl4_sync::run_syscall`).
#[inline(always)]
fn dispatch_syscall<S: Store>(s: &mut S, a: &mut PhysArch, number: i64) -> bool {
    let ct = sched::cur_thread(s);
    let vroot = ct.slot(tl::SLOT_VTABLE).cap(s);
    let fast = syscall::handle_syscall_fast(s, a, number);
    if sched::cur_thread(s) == ct && ct.slot(tl::SLOT_VTABLE).cap(s) != vroot {
        fl4_core::vspace::set_vm_root(s, a, ct);
    }
    fast
}

#[inline(always)]
fn dispatch<S: Store>(s: &mut S, a: &mut PhysArch, ec: u64, esr: u64, far: u64, elr: u64) {
    // As on x86_64 (fl4-kernel entry.rs `dispatch_entry`): l4v's
    // ThreadControlCaps (TCB_SetSpace, _Configure) installs a running
    // thread's new VSpace root without switching to it. When the current
    // thread's root cap changed in an entry that did not switch threads,
    // switch to its new root here, in the entry, rather than letting it go
    // on in the address space it gave up.
    let ct = sched::cur_thread(s);
    let vroot = ct.slot(tl::SLOT_VTABLE).cap(s);
    dispatch_handler(s, a, ec, esr, far, elr);
    if sched::cur_thread(s) == ct && ct.slot(tl::SLOT_VTABLE).cap(s) != vroot {
        fl4_core::vspace::set_vm_root(s, a, ct);
    }
}

#[inline(always)]
fn dispatch_handler<S: Store>(s: &mut S, a: &mut PhysArch, ec: u64, esr: u64, far: u64, elr: u64) {
    // Syscalls go through `dispatch_syscall` (fl4_sync::run_syscall).
    match ec {
        EC_DABT_LOW => syscall::handle_vm_fault(s, a, far, esr),
        EC_IABT_LOW => syscall::handle_vm_fault(s, a, elr, esr),
        _ => {
            let _ = EC_UNKNOWN;
            syscall::handle_user_exception(s, a, esr, 0)
        }
    }
}

/// An interrupt while this core idled.
#[no_mangle]
extern "C" fn fl4_kernel_irq() -> ! {
    percpu::get().idle.set(false);
    if let Some(TakenIrq::Normal(irq)) = take_irq() {
        run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, irq));
    }
    exit()
}

/// A synchronous exception or SError in the kernel: a bug.
#[no_mangle]
extern "C" fn fl4_kernel_fault(esr: u64, far: u64, elr: u64, sp: u64) -> ! {
    panic!("kernel exception: esr {:#x} far {:#x} elr {:#x} sp {:#x}", esr, far, elr, sp)
}

/// Leave the kernel to the current thread (or the idle loop), giving up
/// the serial gate.
pub fn exit() -> ! {
    loop {
        let s = &mut store();
        let pc = percpu::get();
        // The ASID this core ran was invalidated by another core: if it was
        // deleted, run the current thread on what its VSpace cap now names
        // (the empty table, where it faults), not on the deleted tables.
        // That reads the thread's cap, the ASID table and a pool, which a
        // serial entry on another core may be deleting (and the memory
        // reused) unless this core holds the gate: after a local path, or
        // from the idle loop, it does not. A stall while taking it moves
        // the thread off this core (its entry has already run, so it
        // resumes where it continues: `settle_resume_point`): start over
        // with whatever thread is current then.
        //
        // So does a thread running a VM (`ARMVCPURun`): before its guest
        // runs, `vcpu::check` reads its bound notification, which other
        // cores' serial entries signal, unbind and delete under the gate.
        // The thread itself is this core's until a remote stall is
        // acknowledged, which it is not before this core leaves the kernel.
        let ct = sched::cur_thread(s);
        if smp::multi()
            && !pc.gate_held.get()
            && (pc.vspace_stale.get() || ct.state(s) == sched::TS_RUNNING_VM)
        {
            settle_resume_point(s, ct);
            lock();
            continue;
        }
        let core = s.cur_cpu();
        let idle = ct.0 == node_get(s, core, node::IDLE_THREAD);
        let mut a = PhysArch;
        if pc.vspace_stale.replace(false) {
            if idle {
                fl4_core::vspace::set_kernel_vm_root(s, &mut a);
            } else {
                fl4_core::vspace::set_vm_root(s, &mut a, ct);
            }
        }
        // A signal pending on the bound notification ends the run
        // (`vcpu_run_stop::INTERRUPT`) before the guest is entered: the
        // thread then returns to its caller below, as a native one.
        if ct.state(s) == sched::TS_RUNNING_VM {
            fl4_core::vcpu::check(s, &mut a, ct);
        }
        // Page-table writes this entry made reach the table walkers of
        // every core before the gate opens to the next entry, and before
        // this core sleeps (a WFI need not drain its stores).
        mmu::publish_tables();
        unlock();
        if idle {
            vcpu::switch_to(0);
            vcpu::set_host_hcr();
            pc.idle.set(true);
            unsafe { fl4_idle(pc.stack_top.load(core::sync::atomic::Ordering::Relaxed)) }
        }
        if ct.state(s) == sched::TS_RUNNING_VM {
            let run_v = s.read(ct.0 + tl::RUN_VCPU);
            if run_v != 0 {
                let guest_ptr = s.read(run_v + fl4_core::vcpu::TCB);
                if guest_ptr != 0 {
                    let guest = Tcb(guest_ptr);
                    fpu::switch_to(guest.0, guest.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED != 0, true);
                    vcpu::switch_to(run_v);
                    if cpu::is_el2_nvhe() {
                        vcpu::nvhe_prepare_guest(run_v);
                        mmu::publish_tables();
                        let me = percpu::cpu_index();
                        unsafe {
                            fl4_nvhe_enter_guest(
                                fl4_core::layout::paddr(guest.0 + tl::REGS),
                                fl4_core::layout::paddr(run_v),
                                percpu::vttbr(me),
                                vcpu::nvhe_guest_hcr(run_v),
                                pc.guest_fp_trap.get() as u64,
                                pc.stack_top.load(core::sync::atomic::Ordering::Relaxed),
                            )
                        }
                    }
                    vcpu::enter_guest_hcr(run_v);
                    mmu::publish_tables();
                    unsafe { fl4_restore_user(guest.0 + tl::REGS) }
                }
            }
        }
        let v = fl4_core::vcpu::bound(s, ct);
        fpu::switch_to(ct.0, ct.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED != 0, v != 0);
        vcpu::switch_to(v);
        if v != 0 && cpu::is_el2_nvhe() {
            vcpu::nvhe_prepare_guest(v);
            mmu::publish_tables();
            let me = percpu::cpu_index();
            unsafe {
                fl4_nvhe_enter_guest(
                    fl4_core::layout::paddr(ct.0 + tl::REGS),
                    fl4_core::layout::paddr(v),
                    percpu::vttbr(me),
                    vcpu::nvhe_guest_hcr(v),
                    pc.guest_fp_trap.get() as u64,
                    pc.stack_top.load(core::sync::atomic::Ordering::Relaxed),
                )
            }
        }
        if v != 0 {
            vcpu::enter_guest_hcr(v);
        } else {
            vcpu::set_host_hcr();
        }
        mmu::publish_tables();
        unsafe { fl4_restore_user(ct.0 + tl::REGS) }
    }
}

// Every core records here, outside the gate: the x86_64 kernel's ring,
// which never waits (a busy ring drops the entry, a busy dump is skipped).
#[path = "../../fl4-kernel/src/trace.rs"]
mod ring;

const TRACE_N: usize = 4096;
static TRACE: ring::Trace<TRACE_N> = ring::Trace::new();

fn trace(kind: u64, esr: u64, elr: u64, tcb: u64, s: &PhysStore) {
    if !fl4_abi::config::DEBUG_BUILD {
        return;
    }
    let t = Tcb(tcb);
    TRACE.record([kind, esr, elr, t.reg(s, reg::X7), t.reg(s, reg::X0), tcb, 0, 0]);
}

pub fn dump_trace() {
    TRACE.visit_recent(32, |i, t| {
        kprintln!("  #{} kind {} esr {:#x} pc {:#x} x7 {} x0 {:#x} tcb {:#x}", i, t[0], t[1], t[2], t[3] as i64, t[4], t[5]);
    });
}
