//! Kernel entry and exit: save the user registers into the current TCB,
//! dispatch to fl4-core, and restore whichever thread is current after.
use crate::kprintln;
use fl4_arch_x86_64::arch::{PhysArch, TIMER_VECTOR};
use fl4_arch_x86_64::{apic, cpu, fpu, percpu, timer, tlb};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{debug, sched, syscall};
use fl4_arch_x86_64::arch;
use fl4_store::{Phys, PhysStore};
use fl4_sync::SerialGate;
use fl4_arch_x86_64::smp;
use core::sync::atomic::{AtomicU64, Ordering};

core::arch::global_asm!(
    include_str!("../../fl4-arch-x86_64/src/spec.S"), include_str!("sysret.S"), include_str!("bad_iret.S"),
    include_str!("safe_ret.S"), include_str!("entry.S"),
    spec_ibpb = const fl4_arch_x86_64::spec::policy::IBPB,
    spec_rsb = const fl4_arch_x86_64::spec::policy::RSB,
    spec_pbrsb = const fl4_arch_x86_64::spec::policy::PBRSB,
    spec_legacy = const fl4_arch_x86_64::spec::policy::LEGACY_IBRS,
    spec_bhb = const fl4_arch_x86_64::spec::policy::BHB,
    spec_ibhf = const fl4_arch_x86_64::spec::policy::IBHF,
    skim_cpu_size = const crate::gdt::SKIM_CPU_SIZE,
    options(att_syntax)
);

extern "C" {
    fn __x86_return_thunk();
    fn fl4_restore_user(regs: u64, stack_top: u64, cr3: u64) -> !;
    fn fl4_idle(stack_top: u64) -> !;
    static fl4_idle_loop: u8;
    static fl4_idle_end: u8;
    static fl4_vectors: u8;
    static fl4_common_entry: u8;
}

/// On the boot core, while the APs are parked and native entries still
/// use IBPB, switch Rust returns to the Safe RET sequence.
pub fn patch_return_thunk() {
    let paddr = crate::paging::image_paddr(__x86_return_thunk as *const () as u64);
    let opcode = fl4_core::layout::pptr(paddr) as *mut u8;
    unsafe {
        assert_eq!(opcode.read_volatile(), 0xc3);
        assert_eq!(opcode.add(1).read_volatile(), 0xcc);
        // Write through the physical window. The instruction mapping
        // stays read-only.
        opcode.write_volatile(0xeb);
    }
    crate::smp::sync_patched_text();
}

/// The CR3 value entry.S switches to on every entry with the skim window
/// (the kernel's tables, PCID 0), or 0 without it. Read on the user's
/// tables, so in the skim window.
#[no_mangle]
#[link_section = ".bss.skim"]
static FL4_KERNEL_CR3: AtomicU64 = AtomicU64::new(0);

/// Set once on the boot core, before any core runs user code.
pub fn set_kernel_cr3(v: u64) {
    FL4_KERNEL_CR3.store(v, Ordering::Relaxed);
}

/// The frame entry.S builds (see there).
#[repr(C)]
pub struct Frame {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rbp: u64,
    pub rdi: u64,
    pub rsi: u64,
    pub rdx: u64,
    pub rcx: u64,
    pub rbx: u64,
    pub rax: u64,
    pub vector: u64,
    pub error: u64,
    pub rip: u64,
    pub cs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
}

const VEC_SYSCALL: u64 = 0x100;
const VEC_SPURIOUS: u64 = apic::SPURIOUS_VECTOR;
const VEC_TRAP_MIN: u64 = 0xa0;
const VEC_IRQ_MIN: u64 = irq::INT_OFFSET;
const VEC_IRQ_MAX: u64 = irq::MAX + irq::INT_OFFSET;
const RFLAGS_IF: u64 = 1 << 9;
const RFLAGS_TF: u64 = 1 << 8;

static mut KS_BASE: u64 = 0;

/// The serial gate (DESIGN.md §7): kernel entries that cannot run as
/// transactions run holding it, with no transaction running.
pub static GATE: SerialGate = SerialGate::new();

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

/// Direct access to kernel memory (one core, the serial gate, or this
/// core's own thread context).
pub fn store() -> PhysStore {
    PhysStore { frame_masks: (fl4_arch_x86_64::sev::mask(), 0), ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64, tx: false }
}

fn save_user(s: &mut PhysStore, f: &Frame) {
    let t = sched::cur_thread(s);
    let r = t.0 + tl::REGS;
    let w = |s: &mut PhysStore, i: u64, v: u64| s.write(r + i * 8, v);
    w(s, reg::RDI, f.rdi);
    w(s, reg::RSI, f.rsi);
    w(s, reg::RAX, f.rax);
    w(s, reg::RBX, f.rbx);
    w(s, reg::RBP, f.rbp);
    w(s, reg::R12, f.r12);
    w(s, reg::R13, f.r13);
    w(s, reg::R14, f.r14);
    w(s, reg::RDX, f.rdx);
    w(s, reg::R10, f.r10);
    w(s, reg::R8, f.r8);
    w(s, reg::R9, f.r9);
    w(s, reg::R15, f.r15);
    w(s, reg::FLAGS, f.rflags);
    w(s, reg::NEXT_IP, f.rip);
    // -1 marks a context SYSCALL saved: it leaves by SYSRET (entry.S).
    w(s, reg::ERROR, if f.vector == VEC_SYSCALL { u64::MAX } else { f.error });
    w(s, reg::RSP, f.rsp);
    // A syscall or `int $N` on a trap gate restarts at that instruction
    // (two bytes long), for when a remote stall cancels the entry before
    // handle_syscall or handle_trap_syscall runs: from FAULT_IP, the
    // restart would skip it. Stray interrupts on trap vectors never get
    // here (apic::ack_stray in fl4_entry).
    let two_byte = f.vector == VEC_SYSCALL || (VEC_TRAP_MIN..VEC_SPURIOUS).contains(&f.vector);
    w(s, reg::FAULT_IP, if two_byte { f.rip.wrapping_sub(2) } else { f.rip });
    w(s, reg::R11, f.r11);
    w(s, reg::RCX, f.rcx);
    // With FSGSBASE the thread may have moved its FS or GS base itself.
    if cpu::fsgsbase() {
        let pc = percpu::get();
        pc.fs_base.set(cpu::fs_base());
        pc.gs_base.set(cpu::gs_base());
        w(s, reg::FS_BASE, pc.fs_base.get());
        w(s, reg::GS_BASE, pc.gs_base.get());
    }
}

/// An IST always lands at a fixed stack top. If it overwrote a live
/// frame, the fresh frame is usable for termination only. An IRQ taken
/// with IF clear is also invalid, including after a switch to another IST.
#[no_mangle]
extern "C" fn fl4_snp_kernel_entry_stack(f: &Frame) -> u64 {
    let Some(stack) = crate::gdt::snp_ist(f as *const Frame as u64, f.vector as usize) else {
        return 0;
    };
    if stack.contains(&f.rsp) || (f.vector >= 32 && f.rflags & RFLAGS_IF == 0) {
        fl4_arch_x86_64::sev::snp::terminate(0);
    }
    // The idle loop has reset RSP to the kernel stack top and keeps
    // nothing on that stack. Dispatch a waking IRQ there, leaving the
    // small IST available for landing and for the IRET frame.
    let idle_start = core::ptr::addr_of!(fl4_idle_loop) as u64;
    let idle_end = core::ptr::addr_of!(fl4_idle_end) as u64;
    let top = percpu::stack_top(percpu::cpu_index());
    if f.vector >= 32 && f.rsp == top && (idle_start..idle_end).contains(&f.rip) {
        top
    } else {
        0
    }
}

#[no_mangle]
extern "C" fn fl4_bad_entry_frame() -> ! {
    if fl4_arch_x86_64::sev::snp::active() {
        fl4_arch_x86_64::sev::snp::terminate(0);
    }
    cpu::halt_forever()
}

fn kernel_fault(f: &Frame) -> ! {
    if fl4_arch_x86_64::sev::snp::active() {
        // Injected exceptions must not send private registers or RAM to
        // a hypervisor-controlled console.
        kprintln!("FL4: SNP kernel exception {:#x} error {:#x}", f.vector, f.error);
        fl4_arch_x86_64::sev::snp::terminate(0);
    }
    kprintln!(
        "rax {:#x} rbx {:#x} rcx {:#x} rdx {:#x} rsi {:#x} rdi {:#x} rbp {:#x}\nr8 {:#x} r9 {:#x} r10 {:#x} r11 {:#x} r12 {:#x} r13 {:#x} r14 {:#x} r15 {:#x}",
        f.rax, f.rbx, f.rcx, f.rdx, f.rsi, f.rdi, f.rbp, f.r8, f.r9, f.r10, f.r11, f.r12, f.r13, f.r14, f.r15
    );
    for p in [f.rdi, f.rsi, f.r9] {
        if p >> 40 == 0xffffff && p & 7 == 0 {
            let w = |i: u64| unsafe { core::ptr::read_volatile((p + 8 * i) as *const u64) };
            kprintln!("[{:#x}] {:#x} {:#x} {:#x} {:#x} {:#x} {:#x} {:#x} {:#x}", p, w(0), w(1), w(2), w(3), w(4), w(5), w(6), w(7));
        }
    }
    panic!(
        "kernel exception {:#x} error {:#x} at {:#x} (cr2 {:#x}, rsp {:#x})",
        f.vector,
        f.error,
        f.rip,
        cpu::read_cr2(),
        f.rsp
    )
}

/// Service a remote call addressed to this core (a stall runs the kernel's
/// stall logic on behalf of the core that holds the gate). Returns whether
/// this core's current thread was stalled.
fn service_remote() -> bool {
    smp::service(|| {
        let mut s = store();
        let mut a = PhysArch;
        fl4_core::smp::stall(&mut s, &mut a);
    })
}

/// Take the serial gate (on a multi-core system), servicing remote calls
/// while waiting. Returns false when a stall cancelled the entry: this core
/// then runs its idle thread, and the entry must not proceed for the thread
/// that made it (which restarts it later).
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

fn unlock() {
    let pc = percpu::get();
    if pc.gate_held.get() {
        pc.gate_held.set(false);
        GATE.release(&Phys);
    }
}

/// The kernel's side of `fl4_sync::run_entry`.
struct KernelEnv {
    serial: bool,
}

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
    fn prefer_serial(&self) -> bool {
        self.serial
    }
    fn store(&self, tx: bool) -> PhysStore {
        PhysStore { frame_masks: (fl4_arch_x86_64::sev::mask(), 0), ks_base: unsafe { KS_BASE }, cpu: self.cpu(), tx }
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
    fn set_tx(&self, on: bool) {
        let pc = percpu::get();
        pc.tx.set(on);
        if on {
            pc.held_used.set(false);
        }
    }
    fn finish_effects(&self, committed: bool) {
        if committed {
            arch::apply_effects();
        } else {
            arch::discard_effects();
        }
    }
    fn entry_done(&self) {
        // An interrupt only an aborted attempt took stays for unhandled_irq.
        let pc = percpu::get();
        if pc.held_used.get() {
            pc.held_irq.set(percpu::NO_IRQ);
        }
        pc.held_used.set(false);
    }
    fn unhandled_irq(&self) -> Option<u64> {
        let pc = percpu::get();
        let v = pc.held_irq.replace(percpu::NO_IRQ);
        pc.held_used.set(false);
        (v != percpu::NO_IRQ).then_some(v)
    }
    fn holding_gate(&self) {
        let pc = percpu::get();
        pc.gate_held.set(true);
        pc.held_used.set(false);
    }
    fn count(&self, what: fl4_sync::Count) {
        // These counters are exposed only by debug diagnostics. In a
        // release build their shared cache line would contend on every entry.
        if !fl4_abi::config::DEBUG_BUILD { return; }
        use core::sync::atomic::Ordering::Relaxed;
        match what {
            fl4_sync::Count::Commit => {
                let c = smp::TX_COMMITS.fetch_add(1, Relaxed);
                if fl4_abi::config::DEBUG_BUILD && c & 0x3ffff == 0x3ffff {
                    arch::print_stats();
                }
            }
            fl4_sync::Count::Abort => {
                smp::TX_ABORTS.fetch_add(1, Relaxed);
            }
            fl4_sync::Count::Serial => {
                smp::SERIAL_ENTRIES.fetch_add(1, Relaxed);
            }
        }
    }
}

/// Run the kernel's part of an entry (DESIGN.md §7, `fl4_sync::run_entry`).
fn run_entry(irq: bool, serial: bool, body: impl FnMut(&mut PhysStore, &mut PhysArch)) -> bool {
    fl4_sync::run_entry(&KernelEnv { serial }, &GATE, irq, body)
}

/// Back to the interrupted user code without a kernel entry: the CR3 value
/// entry.S loads before it returns (with the skim window, the user's tables
/// again; 0 for none).
fn resume_user() -> u64 {
    // A deferred #DB at this entry's first instruction turned the thread's
    // loaded breakpoints off, expecting the exit to load them again.
    let pc = percpu::get();
    if fl4_abi::config::HARDWARE_DEBUG_API && pc.dr_disarmed.replace(false) && pc.dr_loaded.get() {
        let s = store();
        cpu::write_dr7(sched::cur_thread(&s).debug_reg(&s, 5));
    }
    if tlb::skim() {
        tlb::take_exit_cr3()
    } else {
        0
    }
}

/// A #DB in kernel mode at the first instruction of an entry stub or the
/// SYSCALL entry: a single-stepped SYSCALL, or a MOV SS / POP SS with a
/// data breakpoint whose #DB the CPU held until after the SYSCALL or INT n
/// that followed (CVE-2018-8897). It belongs to user mode; the entry it
/// interrupted goes on.
fn deferred_user_debug(f: &Frame) -> bool {
    let start = unsafe { &fl4_vectors as *const u8 as u64 };
    let end = unsafe { &fl4_common_entry as *const u8 as u64 };
    f.vector == 1 && (start..end).contains(&f.rip)
}

/// Called by entry.S for every kernel entry, on the kernel's tables; from
/// user mode, on the core's kernel stack. Returns only to resume the
/// interrupted code at once, with the CR3 value to load first (0: what the
/// entry interrupted).
#[no_mangle]
extern "C" fn fl4_entry(f: &mut Frame) -> u64 {
    let v = f.vector;
    if v == 29 && fl4_arch_x86_64::sev::snp::active() {
        if f.cs & 3 == 0 {
            crate::snp::vc(f);
            return 0;
        }
        // A second core can otherwise remove a table while #VC walks
        // the active user's mappings. Save the interrupted state first:
        // a remote stall can cancel this entry and restart it later.
        save_user(&mut store(), f);
        if !lock() || percpu::get().vspace_stale.get() {
            exit();
        }
        if crate::snp::user_vc(f) {
            save_user(&mut store(), f);
            exit();
        }
        unlock();
    }
    let irq = (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&v);
    if f.cs & 3 == 0 {
        let pc = percpu::get();
        if (VEC_IRQ_MIN..=VEC_SPURIOUS).contains(&v) {
            if pc.polling.get() {
                // take_pending_irq or the VCPU exit path polled an interrupt:
                // record it and go back with interrupts off so only one is
                // taken. A remote call cannot be left unserviced here: it
                // is made only under the serial gate, which this core
                // holds, or which no core holds while this core runs a
                // transaction (SerialGate drains them first; a transaction
                // that needs a remote call goes serial), and the VCPU exit
                // path services remote calls right after its poll. Taken
                // here, REMOTE_CALL_VECTOR needs only its EOI (handle_ipi).
                if v <= VEC_IRQ_MAX {
                    pc.polled_irq.set(v - VEC_IRQ_MIN);
                } else {
                    apic::ack_stray(v);
                }
                f.rflags &= !RFLAGS_IF;
                return 0;
            }
            if pc.idle.get() && v == TIMER_VECTOR as u64 && timer::early() {
                // Back to idle (l4h 0012); fl4_idle's loop halts again.
                apic::eoi();
                return 0;
            }
            if pc.idle.get() {
                pc.idle.set(false);
                if v == smp::REMOTE_CALL_VECTOR as u64 {
                    service_remote();
                }
                apic::ack_stray(v);
                if irq {
                    run_entry(true, false, |s, a| syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN));
                }
                exit();
            }
        }
        if v == 2 {
            return 0;
        }
        if deferred_user_debug(f) {
            // Breakpoints come back on the way out to the thread
            // (load_debug_state, or resume_user for an entry that goes
            // straight back).
            cpu::write_dr7(0x400);
            cpu::write_dr6(0xffff_0ff0);
            percpu::get().dr_disarmed.set(true);
            return 0;
        }
        kernel_fault(f);
    }
    // A timer interrupt before the armed deadline needs no kernel entry
    // (l4h 0012): acknowledge it and go back to the thread.
    if v == TIMER_VECTOR as u64 && timer::early() {
        apic::eoi();
        return resume_user();
    }
    // An interrupt on a trap-range vector (a device's MSI can name one)
    // is no `int n` from the thread: acknowledge it and go back.
    if apic::ack_stray(v) {
        return resume_user();
    }
    // #NM on the lazy FPU path (fpu.rs): load the thread's FPU state and
    // let it retry the instruction. A thread with the FPU disabled gets
    // the fault instead.
    if v == 7 && fpu::lazy() {
        let s = store();
        let ct = sched::cur_thread(&s);
        if ct.flags(&s) & fl4_abi::consts::tcb_flag::FPU_DISABLED == 0 {
            fpu::lazy_load(ct.0);
            return resume_user();
        }
    }
    // The bench profile's MSR syscalls (DESIGN.md §3) touch only the
    // caller's registers and the MSR: answered here, outside the core.
    // Not for a thread with trapSyscalls (l4h 0001): its syscall goes to
    // its fault handler like every other (`dangerous_msr::call`).
    if fl4_abi::config::KERNEL_X86_DANGEROUS_MSR && v == VEC_SYSCALL && !fl4_arch_x86_64::sev::snp::active() {
        let n = f.rdx as i64;
        // The TCB flags are read only for the MSR calls themselves.
        if n == fl4_abi::syscall::SysX86DangerousRDMSR || n == fl4_abi::syscall::SysX86DangerousWRMSR {
            let flags = {
                let s = store();
                sched::cur_thread(&s).flags(&s)
            };
            match crate::dangerous_msr::of(n, flags) {
                Some(crate::dangerous_msr::Call::Read) => {
                    f.r10 = cpu::rdmsr(f.rdi as u32);
                    // seL4_MessageInfo_new(0, 0, 0, 1).
                    f.rsi = 1;
                    return resume_user();
                }
                Some(crate::dangerous_msr::Call::Write) => {
                    cpu::wrmsr(f.rdi as u32, f.r10);
                    return resume_user();
                }
                None => {}
            }
        }
    }
    save_user(&mut store(), f);
    trace(f);
    if v == smp::REMOTE_CALL_VECTOR as u64 {
        service_remote();
    }
    // Machine state the entry reads once, outside the repeatable part.
    let cr2 = if v == 14 { cpu::read_cr2() } else { 0 };
    let dr6 = if v == 1 && fl4_abi::config::HARDWARE_DEBUG_API {
        let d = cpu::read_dr6();
        cpu::write_dr6(0xffff_0ff0);
        d
    } else {
        0
    };
    // Only a VMEnter that can reach vcpu::enter needs the serial gate.
    // Invalid or trapped calls retain ordinary probe/transaction admission.
    // These caller-owned reads are only a hint: dispatch rechecks them,
    // and a remote stall still cancels the entry before its body runs.
    let serial = v == VEC_SYSCALL
        && f.rdx as i64 == fl4_abi::syscall::SysVMEnter
        && fl4_arch_x86_64::vm::backend() != 0
        && {
            let s = store();
            let t = sched::cur_thread(&s);
            t.flags(&s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS == 0
                && fl4_core::vcpu::bound(&s, t) != 0
        };
    // An interrupt is handled even if a stall cancelled the entry: it has
    // been accepted and needs its EOI.
    run_entry(irq, serial, |s, a| {
        if s.tx {
            dispatch_entry(&mut s.specialize::<true>(), a, v, irq, f.rdx as i64, f.error, cr2, dr6);
        } else {
            dispatch_entry(&mut s.specialize::<false>(), a, v, irq, f.rdx as i64, f.error, cr2, dr6);
        }
    });
    exit()
}

#[inline(always)]
fn dispatch_entry<S: fl4_core::machine::Store>(
    s: &mut S,
    a: &mut PhysArch,
    v: u64,
    irq: bool,
    number: i64,
    error: u64,
    cr2: u64,
    dr6: u64,
) {
    // l4v's ThreadControlCaps (seL4_TCB_SetSpace, _Configure) installs a
    // thread's new VSpace root without switching to it, even when the
    // thread runs: it would go back to user mode on the old root, and keep
    // running there after another core deletes that root's last cap (a
    // remote thread is stalled first, so switches when it runs again).
    // So when the current thread's root cap changed in an entry that did
    // not switch threads, switch to its new root here, in the entry.
    let ct = sched::cur_thread(s);
    let vroot = ct.slot(tl::SLOT_VTABLE).cap(s);
    dispatch_handler(s, a, v, irq, number, error, cr2, dr6);
    if sched::cur_thread(s) == ct && ct.slot(tl::SLOT_VTABLE).cap(s) != vroot {
        fl4_core::vspace::set_vm_root(s, a, ct);
    }
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn dispatch_handler<S: fl4_core::machine::Store>(
    s: &mut S,
    a: &mut PhysArch,
    v: u64,
    irq: bool,
    number: i64,
    error: u64,
    cr2: u64,
    dr6: u64,
) {
    if v == VEC_SYSCALL {
        syscall::handle_syscall(s, a, number);
    } else if irq {
        syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN);
    } else if v == 14 {
        syscall::handle_vm_fault(s, a, cr2, error);
    } else if (v == 1 || v == 3) && fl4_abi::config::HARDWARE_DEBUG_API {
        syscall::handle_debug_exception(s, a, v, dr6);
    } else if v == 2 || v == VEC_SPURIOUS {
        // NMI or spurious interrupt: nothing to do.
    } else if v < 32 {
        syscall::handle_user_exception(s, a, v, error);
    } else if v >= VEC_TRAP_MIN {
        syscall::handle_trap_syscall(s, a, v);
    }
}

/// Leave the kernel to the current thread (or the idle loop), giving up
/// the serial gate. What follows touches only this core's thread, whose
/// context no other core changes without stalling this one first.
pub fn exit() -> ! {
    loop {
        fl4_arch_x86_64::sev::snp::halt_if_poisoned();
        // Exit never runs in a transaction. Use the direct specialization
        // for guest entry/exit and scheduling, as syscall dispatch does.
        let s = &mut store().specialize::<false>();
        let mut ct = sched::cur_thread(s);
        if ct.state(s) == sched::TS_RUNNING_VM {
            // Register the nested root before releasing the gate. An
            // unmap must then interrupt this core even if it has not yet
            // executed its entry instruction.
            if !percpu::get().gate_held.get() {
                lock();
                ct = sched::cur_thread(s);
            }
            let mut a = PhysArch;
            fl4_core::vcpu::check(s, &mut a, ct);
            if ct.state(s) == sched::TS_RUNNING_VM {
                let v = fl4_core::vcpu::bound(s, ct);
                let cap = ct.slot(tl::SLOT_EPT).cap(s);
                let root = match fl4_core::ept::root(s, cap) {
                    Ok((root, _)) => { fl4_core::ept::mark_core(s, root); root }
                    Err(_) => fl4_arch_x86_64::vm::empty_root(),
                };
                unlock();
                let vector = fl4_arch_x86_64::vm::run(s, v, ct.0, root);
                let irq = if vector == 0x100 {
                    // This poll is outside the transaction runner; it
                    // must not leave a held IRQ for the next kernel entry.
                    percpu::get().polled_irq.set(percpu::NO_IRQ);
                    percpu::get().polling.set(true);
                    cpu::enable_interrupts_briefly();
                    percpu::get().polling.set(false);
                    percpu::get().polled_irq.get()
                } else if (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&vector) {
                    vector - VEC_IRQ_MIN
                } else {
                    // Acknowledged on exit, so in service until its EOI.
                    apic::ack_stray(vector);
                    syscall::NO_IRQ
                };
                // Results are already durable if this call stalls us.
                let stalled = service_remote();
                // Always acquire, even if the first call stalled us: an
                // accepted host IRQ still needs handling under the gate.
                let resumed = lock();
                syscall::handle_vcpu_exit(s, &mut a, irq, stalled || !resumed);
                unlock();
                continue;
            }
        }
        // Another core invalidated the ASID this core ran: if it was
        // deleted, run the current thread on what its VSpace cap now names
        // (the kernel's tables, where it faults), not on the deleted ones.
        // That reads the thread's cap, the ASID table and a pool, which a
        // serial entry on another core may be deleting (and the memory
        // reused) unless this core holds the gate: after a transaction, or
        // from the idle loop, it does not.
        if percpu::get().vspace_stale.get() && smp::multi() && !percpu::get().gate_held.get() {
            lock();
            continue;
        }
        let core = s.cur_cpu();
        let idle = ct.0 == node_get(s, core, node::IDLE_THREAD);
        if percpu::get().vspace_stale.replace(false) {
            let mut a = PhysArch;
            if idle {
                fl4_core::vspace::set_kernel_vm_root(s, &mut a);
            } else {
                fl4_core::vspace::set_vm_root(s, &mut a, ct);
            }
        }
        unlock();
        let stack_top = percpu::stack_top(percpu::cpu_index());
        if idle {
            percpu::get().idle.set(true);
            unsafe { fl4_idle(stack_top) }
        }
        fpu::switch_to(ct.0, ct.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED != 0);
        let pc = percpu::get();
        let fs = ct.reg(s, reg::FS_BASE);
        let gs = ct.reg(s, reg::GS_BASE);
        if cpu::fsgsbase() {
            // The thread's own changes reached the TCB (save_user).
            if fs != pc.fs_base.get() { cpu::set_fs_base(fs); pc.fs_base.set(fs); }
            if gs != pc.gs_base.get() { cpu::set_gs_base(gs); pc.gs_base.set(gs); }
        } else {
            // Loading FS or GS in user mode changes the base behind the
            // kernel's back: compare with what the CPU holds.
            if cpu::rdmsr(cpu::msr::FS_BASE) != fs { cpu::wrmsr(cpu::msr::FS_BASE, fs); }
            if cpu::rdmsr(cpu::msr::GS_BASE) != gs { cpu::wrmsr(cpu::msr::GS_BASE, gs); }
            pc.fs_base.set(fs);
            pc.gs_base.set(gs);
        }
        if fl4_abi::config::HARDWARE_DEBUG_API { load_debug_state(s, ct); }
        let cr3 = if tlb::skim() { tlb::take_exit_cr3() } else { 0 };
        let entry_top = crate::gdt::entry_top(core as usize);
        unsafe { fl4_restore_user(ct.0 + tl::REGS, entry_top, cr3) }
    }
}

/// Load a thread's breakpoints and single-step flag (seL4
/// `restore_user_debug_context`).
fn load_debug_state<S: Store>(s: &mut S, t: Tcb) {
    let dr7 = t.debug_reg(s, 5);
    let pc = percpu::get();
    pc.dr_disarmed.set(false);
    if dr7 & 0xff != 0 || pc.dr_loaded.get() {
        for i in 0..4 {
            cpu::write_dr(i, t.debug_reg(s, i));
        }
        cpu::write_dr7(dr7);
        pc.dr_loaded.set(dr7 & 0xff != 0);
    }
    if debug::single_step_enabled(s, t) {
        let f = t.reg(s, reg::FLAGS) | RFLAGS_TF;
        t.set_reg(s, reg::FLAGS, f);
    }
}

const TRACE_N: usize = 8192;
static TRACE: crate::trace::Trace<TRACE_N> = crate::trace::Trace::new();

fn trace(f: &Frame) {
    if !fl4_abi::config::DEBUG_BUILD || fl4_arch_x86_64::sev::snp::active() {
        return;
    }
    let s = store();
    let ct = sched::cur_thread(&s).0;
    TRACE.record([f.vector, f.rip, f.rdi, f.rsi, f.rdx, ct, f.rbx, f.rbp]);
}

/// Print the most recent kernel entries (for panics).
pub fn dump_trace() {
    TRACE.visit_recent(64, |i, t| {
        kprintln!("  #{} vec {:#x} rip {:#x} rdi {:#x} rsi {:#x} rdx {:#x} tcb {:#x}", i, t[0], t[1], t[2], t[3], t[4] as i64, t[5]);
    });
}
