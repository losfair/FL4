//! Per-core backend state. The first two words are read by the SYSCALL
//! entry stub through KERNEL_GS_BASE (kernel stack top, scratch).
use core::cell::UnsafeCell;

/// Cores the backend has room for.
pub const MAX_CPUS: usize = 16;
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

#[repr(C)]
pub struct PerCpu {
    /// Read by entry.S at offset 0.
    pub stack_top: u64,
    /// Scratch for entry.S at offset 8.
    pub scratch: u64,
    /// The core is in the idle loop.
    pub idle: bool,
    /// The kernel is polling for an interrupt (`take_pending_irq`).
    pub polling: bool,
    /// The IRQ a poll accepted.
    pub polled_irq: u64,
    /// TCB whose FPU state is live in this core's registers (0 = none).
    pub fpu_owner: u64,
    /// CR0.TS is set (the current thread may not use the FPU).
    pub ts_set: bool,
    /// User FS/GS bases currently loaded.
    pub fs_base: u64,
    pub gs_base: u64,
    /// Debug registers hold a thread's breakpoints.
    pub dr_loaded: bool,
    /// The user address space this core runs (CR3 value and ASID). With
    /// the skim window the kernel runs on `kernel_cr3` and `exit_cr3` is
    /// what the exit to user code loads.
    pub cr3: u64,
    pub asid: u64,
    pub kernel_cr3: u64,
    pub exit_cr3: u64,
    /// The ASIDs this core's PCIDs hold (tlb.rs).
    pub pcids: [crate::tlb::Slot; crate::tlb::SLOTS],
    pub apic_id: u32,
    /// This core holds the serial gate.
    pub gate_held: bool,
    /// The deadline the timer is armed for (TSC ticks; 0 = none).
    pub armed: u64,
    /// A transaction runs on this core (Arch effects are queued).
    pub tx: bool,
    pub effects: [crate::arch::Effect; crate::arch::MAX_EFFECTS],
    pub neffects: usize,
    /// An interrupt accepted during the current entry, offered again if
    /// the entry's transaction reruns.
    pub held_irq: u64,
    /// The current run of the entry (transaction attempt or serial run)
    /// was given `held_irq`.
    pub held_used: bool,
    /// Initialized locally before enabling virtualization.
    pub spec_plan: Option<crate::spec::policy::Plan>,
    pub spec_rejected: Option<crate::spec::policy::Rejected>,
}

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: 0,
            scratch: 0,
            idle: false,
            polling: false,
            polled_irq: NO_IRQ,
            fpu_owner: 0,
            ts_set: false,
            fs_base: 0,
            gs_base: 0,
            dr_loaded: false,
            cr3: 0,
            asid: 0,
            kernel_cr3: 0,
            exit_cr3: 0,
            pcids: [crate::tlb::Slot::EMPTY; crate::tlb::SLOTS],
            apic_id: 0,
            gate_held: false,
            armed: 0,
            tx: false,
            effects: [crate::arch::Effect::Ack; crate::arch::MAX_EFFECTS],
            neffects: 0,
            held_irq: NO_IRQ,
            held_used: false,
            spec_plan: None,
            spec_rejected: None,
        }
    }
}

struct Cells(UnsafeCell<[PerCpu; MAX_CPUS]>);
// SAFETY: each core touches only its own entry, with interrupts disabled.
unsafe impl Sync for Cells {}

static PERCPU: Cells = Cells(UnsafeCell::new([const { PerCpu::new() }; MAX_CPUS]));

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

/// The calling core's index. Every core runs the kernel on its own stack
/// in KSTACKS, so the stack pointer identifies it; the boot core's early
/// boot stack lies elsewhere and is core 0.
#[inline]
pub fn cpu_index() -> usize {
    let rsp: u64;
    unsafe { core::arch::asm!("mov {}, rsp", out(reg) rsp, options(nomem, nostack, preserves_flags)) };
    let base = KSTACKS.0.get() as u64;
    let off = rsp.wrapping_sub(base);
    if off < (MAX_CPUS * KSTACK_SIZE) as u64 {
        (off / KSTACK_SIZE as u64) as usize
    } else {
        0
    }
}

/// This core's state. Callers run with interrupts disabled and must not
/// hold two of these references at once.
#[allow(clippy::mut_from_ref)]
pub fn get() -> &'static mut PerCpu {
    get_for(cpu_index())
}

#[allow(clippy::mut_from_ref)]
pub fn get_for(i: usize) -> &'static mut PerCpu {
    unsafe { &mut (*PERCPU.0.get())[i] }
}

/// Set up `i`'s stack top; returns it.
pub fn init(i: usize) -> u64 {
    let base = unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 };
    let top = base + KSTACK_SIZE as u64;
    let p = get_for(i);
    p.stack_top = top;
    top
}
