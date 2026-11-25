//! Kernel entry and exit: save the user registers into the current TCB,
//! dispatch to fl4-core, and restore whichever thread is current after.
use crate::kprintln;
use crate::user_trap;
use fl4_arch_x86_64::arch::{PhysArch, TIMER_VECTOR};
use fl4_arch_x86_64::{apic, cpu, cvm, fpu, kconfig, percpu, tdx, timer, tlb};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{debug, sched, syscall};
use fl4_store::{Phys, PhysStore};
use fl4_sync::SerialGate;
use fl4_arch_x86_64::smp;
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

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
    fn __x86_indirect_thunk_r11();
    fn fl4_retpoline_r11();
    fn fl4_restore_user(regs: u64, stack_top: u64, cr3: u64) -> !;
    fn fl4_idle(stack_top: u64, poll_end: u64) -> !;
    static fl4_idle_loop: u8;
    static fl4_idle_end: u8;
    static fl4_vectors: u8;
    static fl4_common_entry: u8;
    // The kernel runs on the user's RSP in [fl4_syscall_entry,
    // fl4_syscall_on_stack) and [fl4_sysret_user_rsp, fl4_sysret_end)
    // (entry.S, cvm_entry.rs).
    fn fl4_syscall_entry();
    static fl4_syscall_on_stack: u8;
    static fl4_sysret_user_rsp: u8;
    static fl4_sysret_end: u8;
}

/// On the boot core, while the APs are parked and native entries still
/// use IBPB, switch Rust returns to the Safe RET sequence and, with
/// `retpoline`, indirect calls and jumps to the retpoline (safe_ret.S).
pub fn patch_return_thunk(retpoline: bool) {
    let paddr = crate::paging::image_paddr(__x86_return_thunk as *const () as u64);
    let opcode = fl4_core::layout::pptr(paddr) as *mut u8;
    unsafe {
        assert_eq!(opcode.read_volatile(), 0xc3);
        assert_eq!(opcode.add(1).read_volatile(), 0xcc);
        // Write through the physical window. The instruction mapping
        // stays read-only.
        opcode.write_volatile(0xeb);
    }
    if retpoline {
        let thunk = __x86_indirect_thunk_r11 as *const () as u64;
        let disp = fl4_retpoline_r11 as *const () as u64 - (thunk + 2);
        assert!(thunk % 16 == 0 && disp < 128);
        let at = fl4_core::layout::pptr(crate::paging::image_paddr(thunk)) as *mut u16;
        unsafe {
            // JMP *%r11 (41 ff e3) becomes JMP rel8 (eb disp) in one
            // aligned store; the E3 byte after it is never reached.
            assert_eq!(at.read_volatile(), 0xff41);
            at.write_volatile(0xeb | (disp as u16) << 8);
        }
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

/// The serial gate (DESIGN.md §7): kernel entries run holding it, except
/// syscalls' local paths, which run beside it.
pub static GATE: SerialGate = SerialGate::new();

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

/// Direct access to kernel memory (one core, the serial gate, or this
/// core's own thread context).
pub fn store() -> PhysStore {
    PhysStore { frame_masks: (cvm::private_mask(), cvm::shared_mask()), ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64 }
}

#[inline(always)]
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
/// RSP is no kernel frame where the kernel runs on the user's RSP: a #DB
/// at the SYSCALL entry's first instruction, or an NMI or #MC there or on
/// the SYSRET path, may find it in an IST (cvm_entry.rs).
#[no_mangle]
extern "C" fn fl4_cvm_kernel_entry_stack(f: &Frame) -> u64 {
    let Some(stack) = crate::gdt::cvm_ist(f as *const Frame as u64, f.vector as usize) else {
        return 0;
    };
    let syscall = fl4_syscall_entry as *const () as u64..core::ptr::addr_of!(fl4_syscall_on_stack) as u64;
    let sysret = core::ptr::addr_of!(fl4_sysret_user_rsp) as u64..core::ptr::addr_of!(fl4_sysret_end) as u64;
    let (ist_overlap, if_clear) = crate::cvm_entry::invalid_entry(f.vector, f.rip, f.rsp, f.rflags, stack, syscall, sysret);
    if ist_overlap || if_clear {
        cvm::terminate_with(0, format_args!("invalid kernel entry vec={:#x} ist_overlap={} if_clear={}", f.vector, ist_overlap, if_clear));
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
    if cvm::hardened() {
        cvm::terminate_with(0, format_args!("bad entry frame"));
    }
    cpu::halt_forever()
}

fn kernel_fault(f: &Frame) -> ! {
    if cvm::hardened() {
        // Injected exceptions must not send private registers or RAM to
        // a hypervisor-controlled console.
        kprintln!("FL4: confidential guest kernel exception {:#x} error {:#x}", f.vector, f.error);
        cvm::terminate(0);
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
        // The stall puts the stalled thread back in its queue, which may
        // be another core's if the caller moved it: that core is owed a
        // reschedule IPI, and this core is not in an entry that sends it.
        fl4_core::smp::send_pending(&mut s, &mut a);
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

#[inline(always)]
fn unlock() {
    let pc = percpu::get();
    if pc.gate_held.get() {
        pc.gate_held.set(false);
        GATE.release(&Phys);
    }
}

/// The kernel's side of `fl4_sync::run_entry`.
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
        PhysStore { frame_masks: (cvm::private_mask(), cvm::shared_mask()), ks_base: unsafe { KS_BASE }, cpu: self.cpu() }
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
    #[inline(always)]
    fn holding_gate(&self) {
        let pc = percpu::get();
        pc.gate_held.set(true);
    }
    fn now(&self) -> u64 {
        fl4_arch_x86_64::timer::now()
    }
    fn local_wait_over(&self, _spins: u32, start: u64) -> bool {
        fl4_arch_x86_64::timer::now().wrapping_sub(start) >= fl4_arch_x86_64::timer::us_to_ticks(fl4_sync::LOCAL_WAIT_US)
    }
    fn count(&self, what: fl4_sync::Count) {
        // These counters are exposed only by debug diagnostics. In a
        // release build their shared cache line would contend on every entry.
        if !fl4_abi::config::DEBUG_BUILD { return; }
        use core::sync::atomic::Ordering::Relaxed;
        match what {
            fl4_sync::Count::Serial => {
                smp::SERIAL_ENTRIES.fetch_add(1, Relaxed);
            }
            fl4_sync::Count::Local => {}
        }
    }
}

/// Run the kernel's part of an entry (DESIGN.md §7, `fl4_sync::run_entry`).
#[inline(always)]
fn run_entry(irq: bool, body: impl FnMut(&mut PhysStore, &mut PhysArch)) -> bool {
    fl4_sync::run_entry(&KernelEnv, &GATE, irq, body)
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

/// Whether `rip` is in the idle loop, the one place the kernel halts with
/// interrupts on.
pub fn in_idle_loop(rip: u64) -> bool {
    let start = core::ptr::addr_of!(fl4_idle_loop) as u64;
    let end = core::ptr::addr_of!(fl4_idle_end) as u64;
    (start..end).contains(&rip)
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

/// How many unhandled user #VEs are logged.
const USER_VE_LOG_MAX: u32 = 8;
static USER_VE_LOGS: AtomicU32 = AtomicU32::new(0);

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
    if v == 20 && tdx::active() {
        // First: until the TDX module has handed over this #VE's
        // information, another #VE would be a double fault.
        let info = tdx::ve_info();
        if f.cs & 3 == 0 {
            crate::tdx::ve(f, &info);
            return 0;
        }
        // As for SNP's #VC: a second core could otherwise remove a table
        // this walks, and a remote stall can cancel this entry.
        save_user(&mut store(), f);
        if !lock() || percpu::get().vspace_stale.get() {
            exit();
        }
        if crate::tdx::user_ve(f, &info) {
            save_user(&mut store(), f);
            exit();
        }
        unlock();
        // The thread's own fault from here. User code can repeat it, so
        // only the first few reach the console, which the VMM reads: the
        // exit reason and nothing of the thread's.
        if USER_VE_LOGS.load(Ordering::Relaxed) < USER_VE_LOG_MAX
            && USER_VE_LOGS.fetch_add(1, Ordering::Relaxed) < USER_VE_LOG_MAX
        {
            kprintln!("FL4: unhandled user TDX #VE (exit_reason {})", info.exit_reason);
        }
    }
    let irq = (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&v);
    if f.cs & 3 == 0 {
        let pc = percpu::get();
        if (VEC_IRQ_MIN..=VEC_SPURIOUS).contains(&v) {
            if pc.polling.get() {
                // take_pending_irq or the VCPU exit path polled an interrupt:
                // record it and go back with interrupts off so only one is
                // taken. A remote call cannot be left unserviced here: it
                // is made under the serial gate, which this core holds, or
                // by a local path, which runs only while no core holds it
                // (SerialGate drains them first) and so while no core
                // polls in an entry body; and the VCPU exit path services
                // remote calls right after its poll. Taken
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
                if v == TIMER_VECTOR as u64 {
                    timer_irq(v - VEC_IRQ_MIN, |s, a| syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN));
                } else if irq {
                    run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, v - VEC_IRQ_MIN));
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
    // A remote call that is no stall (a TLB or FPU request, as local paths
    // on other cores make) needs no kernel entry unless it left the
    // address space this core runs stale: service it, acknowledge it and
    // go back. A kernel entry would take the serial gate, which drains
    // every core's local paths, only to acknowledge it.
    if v == smp::REMOTE_CALL_VECTOR as u64 && smp::service_unless_stall() && !percpu::get().vspace_stale.get() {
        apic::eoi();
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
    if fl4_abi::config::KERNEL_X86_DANGEROUS_MSR && v == VEC_SYSCALL && !cvm::hardened() {
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
    // SysKernelConfig: one boot-frozen word (kconfig.rs), answered from the
    // caller's registers alone, in a confidential VM too. A thread with
    // trapSyscalls takes the ordinary path to its fault handler.
    if v == VEC_SYSCALL && f.rdx as i64 == fl4_abi::syscall::SysKernelConfig {
        let s = store();
        if sched::cur_thread(&s).flags(&s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS == 0 {
            (f.rdi, f.r10) = kconfig::reply(f.rdi);
            // seL4_MessageInfo_new(0, 0, 0, 1).
            f.rsi = 1;
            return resume_user();
        }
    }
    save_user(&mut store(), f);
    trace(f);
    if v == smp::REMOTE_CALL_VECTOR as u64 {
        service_remote();
    }
    // Machine state the entry reads once.
    let cr2 = if v == 14 { cpu::read_cr2() } else { 0 };
    let dr6 = if v == 1 && fl4_abi::config::HARDWARE_DEBUG_API {
        let d = cpu::read_dr6();
        cpu::write_dr6(0xffff_0ff0);
        d
    } else {
        0
    };
    // #BP (`int3`, a trap: RIP is past it) and #DB (single-step and data
    // breakpoints are traps too) cannot be taken again by restarting the
    // thread, and DR6 has just been cleared. A remote stall that cancelled
    // the entry would lose them. So the thread keeps the trap until it is
    // delivered, by `exit`, which takes the gate for it.
    if v == 1 || v == 3 {
        let s = &mut store();
        sched::cur_thread(s).set_debug_reg(s, user_trap::SLOT, user_trap::encode(v, dr6, f.rip));
        percpu::get().check_user_trap.set(true);
        exit();
    }
    // An interrupt is handled even if a stall cancelled the entry: it has
    // been accepted and needs its EOI.
    let body = |s: &mut PhysStore, a: &mut PhysArch| {
        dispatch_entry(s, a, v, irq, f.error, cr2, dr6);
    };
    if v == VEC_SYSCALL {
        let number = f.rdx as i64;
        let local = |s: &mut PhysStore, a: &mut PhysArch| fl4_sync::local_syscall(s, a, &Phys, number, |_, _| {});
        let syscall_body = |s: &mut PhysStore, a: &mut PhysArch| dispatch_syscall_entry(s, a, number);
        fl4_sync::run_syscall(&KernelEnv, &GATE, number, local, syscall_body);
    } else if v == 14 {
        // A user page fault (kernel-mode ones went to kernel_fault above):
        // its fast path may run beside the gate.
        let error = f.error;
        let local = |s: &mut PhysStore, a: &mut PhysArch| fl4_sync::local_vm_fault(s, a, &Phys, cr2, error, |_, _| {});
        fl4_sync::run_vm_fault(&KernelEnv, &GATE, local, body);
    } else if v == TIMER_VECTOR as u64 {
        timer_irq(v - VEC_IRQ_MIN, body);
    } else {
        run_entry(irq, body);
    }
    exit()
}

/// The kernel timer interrupt `irq`, accepted from user code or the idle
/// loop: its local path beside the serial gate, else `body` under it
/// (`fl4_sync::run_timer_irq`). With the hardware debug API, a thread the
/// local path switched to may hold a user trap that `exit` must deliver
/// (`check_user_trap`): a stalled thread, back in a ready queue.
#[inline(always)]
fn timer_irq(irq: u64, body: impl FnMut(&mut PhysStore, &mut PhysArch)) {
    let local = |s: &mut PhysStore, a: &mut PhysArch| {
        let before = sched::cur_thread(s);
        let ran = fl4_sync::local_timer_irq(s, a, &Phys, irq, |_, _| {});
        if ran && fl4_abi::config::HARDWARE_DEBUG_API && sched::cur_thread(s) != before {
            percpu::get().check_user_trap.set(true);
        }
        ran
    };
    fl4_sync::run_timer_irq(&KernelEnv, &GATE, local, body);
}

#[inline(always)]
fn dispatch_entry<S: fl4_core::machine::Store>(
    s: &mut S,
    a: &mut PhysArch,
    v: u64,
    irq: bool,
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
    dispatch_handler(s, a, v, irq, error, cr2, dr6);
    if sched::cur_thread(s) == ct && ct.slot(tl::SLOT_VTABLE).cap(s) != vroot {
        fl4_core::vspace::set_vm_root(s, a, ct);
    }
}

/// `dispatch_entry` for a syscall: true if a fast path ran.
#[inline(always)]
fn dispatch_syscall_entry<S: fl4_core::machine::Store>(s: &mut S, a: &mut PhysArch, number: i64) -> bool {
    let ct = sched::cur_thread(s);
    let vroot = ct.slot(tl::SLOT_VTABLE).cap(s);
    let fast = syscall::handle_syscall_fast(s, a, number);
    if sched::cur_thread(s) == ct && ct.slot(tl::SLOT_VTABLE).cap(s) != vroot {
        fl4_core::vspace::set_vm_root(s, a, ct);
    }
    fast
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn dispatch_handler<S: fl4_core::machine::Store>(
    s: &mut S,
    a: &mut PhysArch,
    v: u64,
    irq: bool,
    error: u64,
    cr2: u64,
    dr6: u64,
) {
    // Syscalls go through `dispatch_syscall_entry` (fl4_sync::run_syscall).
    if irq {
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
/// How long an idle core polls before it halts (fl4_idle).
const IDLE_POLL_US: u64 = 100;

pub fn exit() -> ! {
    loop {
        cvm::halt_if_poisoned();
        let s = &mut store();
        let mut ct = sched::cur_thread(s);
        if ct.state(s) == sched::TS_RUNNING_VM {
            // Register the nested root before releasing the gate. An
            // unmap must then interrupt this core even if it has not yet
            // executed its entry instruction. Beside the gate when that
            // changes nothing (`fl4_core::localvm::vm_entry_ready`): this
            // core is registered already, and the checks write nothing.
            let mut ready = None;
            if !percpu::get().gate_held.get() {
                if smp::multi() {
                    let found = core::cell::Cell::new(None);
                    match fl4_sync::try_local(&KernelEnv, &GATE, |s, _| {
                        found.set(fl4_sync::local_vm_entry(s, &Phys));
                        found.get().is_some()
                    }) {
                        fl4_sync::Local::Done => ready = found.get(),
                        // The thread is no longer this core's to enter.
                        fl4_sync::Local::Stalled => continue,
                        fl4_sync::Local::Closed | fl4_sync::Local::Declined => {}
                    }
                }
                // A VCPU whose VMCS another core last loaded is entered
                // under the gate, which clears it there first (below).
                if ready.is_some() && !fl4_arch_x86_64::vm::loadable_here(fl4_core::vcpu::bound(s, ct)) {
                    ready = None;
                }
                if ready.is_none() {
                    lock();
                    ct = sched::cur_thread(s);
                }
            }
            let mut a = PhysArch;
            if ready.is_none() {
                fl4_core::vcpu::check(s, &mut a, ct);
                if ct.state(s) == sched::TS_RUNNING_VM {
                    let cap = ct.slot(tl::SLOT_EPT).cap(s);
                    ready = Some(match fl4_core::ept::root(s, cap) {
                        Ok((root, _)) => { fl4_core::ept::mark_core(s, root); root }
                        Err(_) => 0,
                    });
                }
            }
            if let Some(root) = ready {
                let root = if root == 0 { fl4_arch_x86_64::vm::empty_root() } else { root };
                let v = fl4_core::vcpu::bound(s, ct);
                // Still under the gate where it is held: `run` makes no
                // remote call (fl4-arch-x86_64's smp module comment).
                if percpu::get().gate_held.get() {
                    fl4_arch_x86_64::vm::evict(v);
                }
                unlock();
                let vector = fl4_arch_x86_64::vm::run(s, v, ct.0, root);
                let irq = if vector == 0x100 {
                    // This poll is outside run_entry; it must not leave
                    // a held IRQ for the next kernel entry.
                    percpu::get().polled_irq.set(percpu::NO_IRQ);
                    percpu::get().polling.set(true);
                    cpu::enable_interrupts_briefly();
                    percpu::get().polling.set(false);
                    percpu::get().polled_irq.get()
                } else if (VEC_IRQ_MIN..=VEC_IRQ_MAX).contains(&vector) {
                    vector - VEC_IRQ_MIN
                } else if vector == fl4_arch_x86_64::vm::NO_INTERRUPT {
                    syscall::NO_IRQ
                } else {
                    // Acknowledged on exit, so in service until its EOI.
                    apic::ack_stray(vector);
                    syscall::NO_IRQ
                };
                // Results are already durable if this call stalls us.
                let stalled = service_remote();
                // An exit without a host interrupt, or the kernel timer's,
                // first beside the gate (`fl4_sync::local_vm_exit`). The
                // timer's interrupt has been accepted: if the local path
                // declines or a stall comes while it waits for the gate,
                // it is handled under the gate, as any other.
                let local = !stalled
                    && smp::multi()
                    && (irq == syscall::NO_IRQ || irq == TIMER_VECTOR as u64 - VEC_IRQ_MIN);
                let res = if local {
                    fl4_sync::try_local(&KernelEnv, &GATE, |s, a| fl4_sync::local_vm_exit(s, a, &Phys, irq, |_, _| {}))
                } else {
                    fl4_sync::Local::Declined
                };
                if !matches!(res, fl4_sync::Local::Done) {
                    // Always acquire, even if the first call stalled us: an
                    // accepted host IRQ still needs handling under the gate.
                    let resumed = lock();
                    let local_stalled = matches!(res, fl4_sync::Local::Stalled);
                    syscall::handle_vcpu_exit(s, &mut a, irq, stalled || !resumed || local_stalled);
                }
                // That ran the scheduler. A thread it made current may hold
                // a user trap (`check_user_trap`). The gate, if held, is
                // kept for the next round: a guest re-entered at once is
                // prepared under it, and anything else leaves through the
                // release below, one release per exit.
                percpu::get().check_user_trap.set(true);
                continue;
            }
        }
        // A user #BP or #DB that `fl4_entry` left with the thread
        // (`user_trap`): delivered under the gate. A stall while taking it
        // moves the thread off this core with the trap still pending, and
        // the thread resumes after the `int3` or trapping instruction
        // (`settle_resume_point`); the trap is delivered when it next runs,
        // on whichever core. Reading the current thread without the gate is
        // safe: only this core changes its context until a stall is
        // acknowledged. On one core `lock` does nothing.
        //
        // The slot is read only when a trap can be there: this entry left
        // one (`check_user_trap`); a serial entry's scheduler made the
        // thread current, and the gate is still held (a stalled thread is
        // TS_RESTART, which no local path switches to); or the VM block
        // above did so and gave the gate up (`check_user_trap` again). The
        // flag is consumed first, whatever follows: after a stall the trap
        // is the stalled thread's, found under the gate where it next runs.
        //
        // The invocation that stalled the thread may have changed it
        // (written its registers, removed the breakpoint, redirected it
        // from a timeout fault). A trap is delivered only if the thread is
        // still where it trapped, and dropped otherwise, as a fault already
        // sent is when such an invocation cancels the thread's IPC.
        let pc = percpu::get();
        if (pc.check_user_trap.replace(false) || pc.gate_held.get())
            && ct.state(s) == sched::TS_RUNNING
            && ct.0 != node_get(s, s.cur_cpu(), node::IDLE_THREAD)
        {
            if let Some(trap) = user_trap::decode(ct.debug_reg(s, user_trap::SLOT)) {
                if !pc.gate_held.get() {
                    settle_resume_point(s, ct);
                    if !lock() {
                        continue;
                    }
                }
                ct.set_debug_reg(s, user_trap::SLOT, user_trap::NONE);
                if trap.current(ct.reg(s, reg::FAULT_IP), ct.debug_reg(s, user_trap::DR7_SLOT)) {
                    dispatch_entry(s, &mut PhysArch, trap.vector, false, 0, 0, trap.dr6);
                }
                continue;
            }
        }
        // Another core invalidated the ASID this core ran: if it was
        // deleted, run the current thread on what its VSpace cap now names
        // (the kernel's tables, where it faults), not on the deleted ones.
        // That reads the thread's cap, the ASID table and a pool, which a
        // serial entry on another core may be deleting (and the memory
        // reused) unless this core holds the gate: after a local path, or
        // from the idle loop, it does not.
        if percpu::get().vspace_stale.get() && smp::multi() && !percpu::get().gate_held.get() {
            settle_resume_point(s, ct);
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
            // Poll for a while before halting (fl4_idle): under a
            // hypervisor, with other cores to wake this one (idle_polls).
            let end = if smp::idle_polls() { timer::now().wrapping_add(timer::us_to_ticks(IDLE_POLL_US)).max(1) } else { 0 };
            percpu::get().idle.set(true);
            unsafe { fl4_idle(stack_top, end) }
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
    if !fl4_abi::config::DEBUG_BUILD || cvm::hardened() {
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
