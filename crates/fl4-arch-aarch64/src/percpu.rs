//! Per-core backend state, reached through TPIDR_EL1. The first word is
//! read by the exception vectors (entry.S): the core's kernel stack top.
//!
//! As on x86_64, a core's `PerCpu` is its own: its `Cell`s are used only by
//! that core, with interrupts disabled, through shared references (`get`
//! may be called again while a reference from an outer call is live, so a
//! `&mut` would alias). What other cores read lives apart, in atomics
//! (`SHARED`), with the ordering each protocol needs.
use core::cell::{Cell, UnsafeCell};
use core::sync::atomic::{AtomicU64, Ordering};

/// Cores the backend has room for (and that have banked interrupt state,
/// `fl4_core::layout::irq::BANKED_CORES`).
pub const MAX_CPUS: usize = 16;
const _: () = assert!(MAX_CPUS as u64 == fl4_core::layout::irq::BANKED_CORES);
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

#[repr(C)]
pub struct PerCpu {
    /// Read by entry.S at offset 0. Written before the core starts.
    pub stack_top: AtomicU64,
    /// This core's index, at offset 8. Written before the core starts.
    pub index: AtomicU64,
    /// The core is in the idle loop.
    pub idle: Cell<bool>,
    /// EL0 may use FP/SIMD (CPACR_EL1.FPEN), as last written.
    pub fp_enabled: Cell<bool>,
    /// `mmu::ASID_GEN` when this core last flushed its TLB for it.
    pub asid_gen: Cell<u64>,
    /// Another core invalidated the ASID this core runs: the exit checks
    /// that it still names the current thread's VSpace (`mmu::retired`).
    pub vspace_stale: Cell<bool>,
    /// This core holds the serial gate.
    pub gate_held: Cell<bool>,
    /// The deadline the timer is armed for (counter ticks; 0 = none).
    pub armed: Cell<u64>,
    /// A transaction runs on this core (Arch effects are queued).
    pub tx: Cell<bool>,
    pub effects: [Cell<crate::arch::Effect>; crate::arch::MAX_EFFECTS],
    pub neffects: Cell<usize>,
    /// An interrupt accepted during the current entry, offered again if
    /// the entry's transaction reruns (a GIC interrupt ID).
    pub held_irq: Cell<u64>,
    /// The current run of the entry was given `held_irq`.
    pub held_used: Cell<bool>,
    /// The raw acknowledge value of the interrupt last taken (GICv2 SGIs
    /// carry their source in it, which the EOI needs).
    pub iar: Cell<u64>,
}

const _: () = assert!(core::mem::offset_of!(PerCpu, stack_top) == 0 && core::mem::offset_of!(PerCpu, index) == 8);

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: AtomicU64::new(0),
            index: AtomicU64::new(0),
            idle: Cell::new(false),
            fp_enabled: Cell::new(true),
            asid_gen: Cell::new(0),
            vspace_stale: Cell::new(false),
            gate_held: Cell::new(false),
            armed: Cell::new(0),
            tx: Cell::new(false),
            effects: [const { Cell::new(crate::arch::Effect::Ack(0)) }; crate::arch::MAX_EFFECTS],
            neffects: Cell::new(0),
            held_irq: Cell::new(NO_IRQ),
            held_used: Cell::new(false),
            iar: Cell::new(0),
        }
    }
}

struct Locals([PerCpu; MAX_CPUS]);
// SAFETY: a core uses the `Cell`s of its own entry only (`get`); other
// cores touch only its atomics (`init_stack`, before it starts).
unsafe impl Sync for Locals {}
static PERCPU: Locals = Locals([const { PerCpu::new() }; MAX_CPUS]);

/// Fields other cores read.
struct Shared {
    /// TCB whose FP/SIMD state is live in this core's registers (0 = none).
    fpu_owner: AtomicU64,
    /// The user address space this core runs (TTBR0_EL1 value).
    ttbr0: AtomicU64,
    /// MPIDR_EL1 affinity of this core.
    mpidr: AtomicU64,
    /// GICv3: this core's redistributor (kernel virtual address). GICv2:
    /// the CPU interface number SGIs target.
    gicr: AtomicU64,
    gic_cpu: AtomicU64,
}

static SHARED: [Shared; MAX_CPUS] = [const {
    Shared {
        fpu_owner: AtomicU64::new(0),
        ttbr0: AtomicU64::new(0),
        mpidr: AtomicU64::new(0),
        gicr: AtomicU64::new(0),
        gic_cpu: AtomicU64::new(0),
    }
}; MAX_CPUS];

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

/// The calling core's index (TPIDR_EL1 points at its `PerCpu`).
#[inline]
pub fn cpu_index() -> usize {
    let p = crate::mrs!("tpidr_el1");
    if p == 0 {
        0
    } else {
        unsafe { (*(p as *const PerCpu)).index.load(Ordering::Relaxed) as usize }
    }
}

/// This core's state. Callers run with interrupts disabled.
#[inline]
pub fn get() -> &'static PerCpu {
    let p = crate::mrs!("tpidr_el1");
    if p == 0 {
        &PERCPU.0[0]
    } else {
        unsafe { &*(p as *const PerCpu) }
    }
}

/// Give core `i` its index and kernel stack (before it starts, or on the
/// boot core); returns the stack top.
pub fn init_stack(i: usize) -> u64 {
    let base = unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 };
    let top = base + KSTACK_SIZE as u64;
    let p = &PERCPU.0[i];
    p.stack_top.store(top, Ordering::Relaxed);
    p.index.store(i as u64, Ordering::Relaxed);
    top
}

/// On core `i`: set up its state and point TPIDR_EL1 at it; returns its
/// kernel stack top.
pub fn init(i: usize) -> u64 {
    let top = init_stack(i);
    set_mpidr(i, crate::cpu::mpidr());
    crate::msr!("tpidr_el1", &PERCPU.0[i] as *const PerCpu as u64);
    top
}

/// The stack top of core `i`.
pub fn stack_top(i: usize) -> u64 {
    unsafe { (*KSTACKS.0.get())[i].as_ptr() as u64 + KSTACK_SIZE as u64 }
}

/// The TCB whose FP/SIMD state core `c` holds. Acquire: a core that saw
/// an owner change also sees the previous owner's state saved (fpu.rs).
pub fn fpu_owner(c: usize) -> u64 {
    SHARED[c].fpu_owner.load(Ordering::Acquire)
}

/// This core's FP/SIMD registers now hold `t`'s state (after saving the
/// previous owner's: Release).
pub fn set_fpu_owner(t: u64) {
    SHARED[cpu_index()].fpu_owner.store(t, Ordering::Release);
}

/// The TTBR0_EL1 value core `c` runs (mmu.rs: sequentially consistent,
/// half of the switch/invalidation handshake).
pub fn ttbr0(c: usize) -> u64 {
    SHARED[c].ttbr0.load(Ordering::SeqCst)
}

pub fn set_ttbr0(v: u64) {
    SHARED[cpu_index()].ttbr0.store(v, Ordering::SeqCst);
}

/// Set before core `c` is started or on core `c` itself; read by other
/// cores only once it is online (`smp::set_online` orders it).
pub fn mpidr(c: usize) -> u64 {
    SHARED[c].mpidr.load(Ordering::Relaxed)
}

pub fn set_mpidr(c: usize, v: u64) {
    SHARED[c].mpidr.store(v, Ordering::Relaxed);
}

/// As `mpidr`: set by the core while it starts (gic.rs `init_cpu`).
pub fn gicr(c: usize) -> u64 {
    SHARED[c].gicr.load(Ordering::Relaxed)
}

pub fn set_gicr(v: u64) {
    SHARED[cpu_index()].gicr.store(v, Ordering::Relaxed);
}

pub fn gic_cpu(c: usize) -> u64 {
    SHARED[c].gic_cpu.load(Ordering::Relaxed)
}

pub fn set_gic_cpu(v: u64) {
    SHARED[cpu_index()].gic_cpu.store(v, Ordering::Relaxed);
}
