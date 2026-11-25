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
pub const MAX_CPUS: usize = 128;
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
    /// FP/SIMD trap mode: 0 = trap EL0 (FPEN=01), 1 = trap EL1+EL0 (FPEN=00),
    /// 2 = enabled (FPEN=11).
    pub fp_mode: Cell<u8>,
    /// In EL2 nVHE mode, whether to trap guest FP/SIMD via `CPTR_EL2.TFP`.
    pub guest_fp_trap: Cell<bool>,
    /// `mmu::ASID_GEN` when this core last flushed its TLB for it.
    pub asid_gen: Cell<u64>,
    /// `mmu::VMID_GEN` when this core last flushed its Stage-2 TLB for it.
    pub vmid_gen: Cell<u64>,
    /// Whether the lazily owned `vcpu_owner` is currently active in hardware
    /// (false when suspended for a native/idle thread).
    pub vcpu_active: Cell<bool>,
    /// Cached GIC mask state of PPI 25 (VGIC maintenance) on this core (true = masked).
    pub ppi_vgic_masked: Cell<bool>,
    /// Cached GIC mask state of PPI 27 (guest vTimer) on this core (true = masked).
    pub ppi_vtimer_masked: Cell<bool>,
    /// Another core invalidated the ASID this core runs: the exit checks
    /// that it still names the current thread's VSpace (`mmu::retired`).
    pub vspace_stale: Cell<bool>,
    /// This core holds the serial gate.
    pub gate_held: Cell<bool>,
    /// The deadline the timer is armed for (counter ticks; 0 = none).
    pub armed: Cell<u64>,
    /// The raw acknowledge value of the interrupt last taken (GICv2 SGIs
    /// carry their source in it, which the EOI needs).
    pub iar: Cell<u64>,
    /// Pointer authentication (pac.rs): the TCB and key generation whose
    /// keys this core's key registers hold (0: none, the APGA key all
    /// zero), the SCTLR_EL1 enables it runs with, and the cached 10 key
    /// words currently loaded in hardware so threads sharing keys skip MSRs.
    pub pac_owner: Cell<u64>,
    pub pac_epoch: Cell<u64>,
    pub pac_flags: Cell<u64>,
    pub pac_keys: Cell<[u64; 10]>,
    pub pac_keys_valid: Cell<bool>,
    /// The high window (mmu.rs `switch_high`): the one `ArmHighVSpace`
    /// (TTBR1 value, any physical address, 0 included) whose translations
    /// this core's TLB may hold, and the TTBR0 ASID they are tagged with.
    /// `high_asid` 0: no pair (ASID 0 never has a window), whatever
    /// `high_ttbr1` says.
    pub high_ttbr1: Cell<u64>,
    pub high_asid: Cell<u64>,
    /// `mmu::HIGH_GEN` as this core's `switch_high` last saw it.
    pub high_gen: Cell<u64>,
}

const _: () = assert!(core::mem::offset_of!(PerCpu, stack_top) == 0 && core::mem::offset_of!(PerCpu, index) == 8);

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            stack_top: AtomicU64::new(0),
            index: AtomicU64::new(0),
            idle: Cell::new(false),
            fp_mode: Cell::new(2),
            guest_fp_trap: Cell::new(true),
            asid_gen: Cell::new(0),
            vmid_gen: Cell::new(0),
            vcpu_active: Cell::new(false),
            ppi_vgic_masked: Cell::new(true),
            ppi_vtimer_masked: Cell::new(true),
            vspace_stale: Cell::new(false),
            gate_held: Cell::new(false),
            armed: Cell::new(0),
            iar: Cell::new(0),
            pac_owner: Cell::new(0),
            pac_epoch: Cell::new(0),
            pac_flags: Cell::new(0),
            pac_keys: Cell::new([0; 10]),
            pac_keys_valid: Cell::new(false),
            high_ttbr1: Cell::new(0),
            high_asid: Cell::new(0),
            high_gen: Cell::new(0),
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
    /// VCPU whose EL1/VGIC state is live in this core's registers (0 = none).
    vcpu_owner: AtomicU64,
    /// The user address space this core runs (TTBR0_EL1 value).
    ttbr0: AtomicU64,
    /// The TTBR1_EL1 value this core runs (`TTBR1_UNSET` before its first
    /// switch: the kernel's, from boot; a TTBR1 value, a window's physical
    /// address, may be 0).
    ttbr1: AtomicU64,
    /// The Stage-2 root+VMID this core runs (VTTBR_EL2 value).
    vttbr: AtomicU64,
    /// The logical Stage-2 ASID currently loaded on this core (0 = empty).
    s2_asid: AtomicU64,
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
        vcpu_owner: AtomicU64::new(0),
        ttbr0: AtomicU64::new(0),
        ttbr1: AtomicU64::new(TTBR1_UNSET),
        vttbr: AtomicU64::new(0),
        s2_asid: AtomicU64::new(0),
        mpidr: AtomicU64::new(0),
        gicr: AtomicU64::new(0),
        gic_cpu: AtomicU64::new(0),
    }
}; MAX_CPUS];

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

#[inline]
fn read_tpidr() -> u64 {
    if crate::cpu::is_el2_vhe() {
        crate::mrs!("tpidr_el2")
    } else {
        crate::mrs!("tpidr_el1")
    }
}

/// The calling core's index (TPIDR_EL2 in EL2, TPIDR_EL1 in EL1).
#[inline]
pub fn cpu_index() -> usize {
    let p = read_tpidr();
    if p == 0 {
        0
    } else {
        unsafe { (*(p as *const PerCpu)).index.load(Ordering::Relaxed) as usize }
    }
}

/// This core's state. Callers run with interrupts disabled.
#[inline]
pub fn get() -> &'static PerCpu {
    let p = read_tpidr();
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

/// On core `i`: set up its state and point TPIDR_EL2 (EL2) or TPIDR_EL1
/// (EL1) at it; returns its kernel stack top.
pub fn init(i: usize) -> u64 {
    let top = init_stack(i);
    set_mpidr(i, crate::cpu::mpidr());
    let ptr = &PERCPU.0[i] as *const PerCpu as u64;
    if crate::cpu::is_el2_vhe() {
        crate::msr!("tpidr_el2", ptr);
    } else {
        crate::msr!("tpidr_el1", ptr);
    }
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

/// The VCPU whose EL1/VGIC state core `c` currently holds (0 = none).
pub fn vcpu_owner(c: usize) -> u64 {
    SHARED[c].vcpu_owner.load(Ordering::Acquire)
}

pub fn set_vcpu_owner(v: u64) {
    SHARED[cpu_index()].vcpu_owner.store(v, Ordering::Release);
}

/// The TTBR0_EL1 value core `c` runs (mmu.rs: sequentially consistent,
/// half of the switch/invalidation handshake).
pub fn ttbr0(c: usize) -> u64 {
    SHARED[c].ttbr0.load(Ordering::SeqCst)
}

pub fn set_ttbr0(v: u64) {
    SHARED[cpu_index()].ttbr0.store(v, Ordering::SeqCst);
}

/// The TTBR1_EL1 value core `c` runs (mmu.rs `invalidate_high_vspace`:
/// sequentially consistent, as `ttbr0`).
pub fn ttbr1(c: usize) -> Option<u64> {
    match SHARED[c].ttbr1.load(Ordering::SeqCst) {
        TTBR1_UNSET => None,
        v => Some(v),
    }
}

/// No TTBR1 published yet: not a TTBR1 value (those are page aligned).
const TTBR1_UNSET: u64 = u64::MAX;

pub fn set_ttbr1(v: u64) {
    SHARED[cpu_index()].ttbr1.store(v, Ordering::SeqCst);
}

/// The VTTBR_EL2 value core `c` runs (mmu.rs: sequentially consistent).
pub fn vttbr(c: usize) -> u64 {
    SHARED[c].vttbr.load(Ordering::SeqCst)
}

pub fn set_vttbr(v: u64) {
    SHARED[cpu_index()].vttbr.store(v, Ordering::SeqCst);
}

/// Logical Stage-2 ASID core `c` runs (0 = empty Stage-2 root).
pub fn s2_asid(c: usize) -> u64 {
    SHARED[c].s2_asid.load(Ordering::SeqCst)
}

pub fn set_s2_asid(v: u64) {
    SHARED[cpu_index()].s2_asid.store(v, Ordering::SeqCst);
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
