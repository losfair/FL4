//! Per-core backend state, and which core the caller runs on.
use core::cell::{Cell, UnsafeCell};
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

/// Cores the backend has room for.
pub const MAX_CPUS: usize = 64;
pub const KSTACK_SIZE: usize = 64 * 1024;
pub const NO_IRQ: u64 = u64::MAX;

// Each core's state is alone on its 128-byte pair of cache lines (Intel's
// spatial prefetcher fetches lines in pairs): written on every address-space
// switch and FPU change, it would otherwise bounce between neighbouring cores.
#[repr(C, align(128))]
pub struct PerCpu {
    /// The core is in the idle loop.
    pub idle: Cell<bool>,
    /// The kernel is polling for an interrupt (`take_pending_irq`).
    pub polling: Cell<bool>,
    /// Another core invalidated the ASID this core runs: the exit checks
    /// that it still names the current thread's VSpace (tlb.rs
    /// `remote_invalidate_asid`).
    pub vspace_stale: Cell<bool>,
    /// The IRQ a poll accepted.
    pub polled_irq: Cell<u64>,
    /// CR0.TS is set (the current thread may not use the FPU).
    pub ts_set: Cell<bool>,
    /// The FPU registers hold the initial state and no thread's (fpu.rs
    /// `scrub_local`).
    pub fpu_clean: Cell<bool>,
    /// User FS/GS bases currently loaded.
    pub fs_base: Cell<u64>,
    pub gs_base: Cell<u64>,
    /// Debug registers hold a thread's breakpoints.
    pub dr_loaded: Cell<bool>,
    /// A deferred user #DB turned breakpoints off (DR7) during this entry.
    pub dr_disarmed: Cell<bool>,
    /// The user address space this core runs (CR3 value). With
    /// the skim window the kernel runs on its own tables (entry.S loads
    /// them on every entry) and `exit_cr3` is what the exit to user code
    /// loads.
    pub cr3: Cell<u64>,
    pub exit_cr3: Cell<u64>,
    /// The ASIDs this core's PCIDs hold (tlb.rs).
    pub pcids: [Cell<crate::tlb::Slot>; crate::tlb::SLOTS],
    /// This core holds the serial gate.
    pub gate_held: Cell<bool>,
    /// The deadline the timer is armed for (TSC ticks; 0 = none).
    pub armed: Cell<u64>,
    /// Initialized locally before enabling virtualization.
    pub spec_plan: Cell<Option<crate::spec::policy::Plan>>,
    pub spec_rejected: Cell<Option<crate::spec::policy::Rejected>>,
}

impl PerCpu {
    const fn new() -> PerCpu {
        PerCpu {
            idle: Cell::new(false),
            polling: Cell::new(false),
            vspace_stale: Cell::new(false),
            polled_irq: Cell::new(NO_IRQ),
            ts_set: Cell::new(false),
            fpu_clean: Cell::new(false),
            fs_base: Cell::new(0),
            gs_base: Cell::new(0),
            dr_loaded: Cell::new(false),
            dr_disarmed: Cell::new(false),
            cr3: Cell::new(0),
            exit_cr3: Cell::new(0),
            pcids: [const { Cell::new(crate::tlb::Slot::EMPTY) }; crate::tlb::SLOTS],
            gate_held: Cell::new(false),
            armed: Cell::new(0),
            spec_plan: Cell::new(None),
            spec_rejected: Cell::new(None),
        }
    }
}

struct Locals([PerCpu; MAX_CPUS]);
// SAFETY: get() indexes by the running CPU. PerCpu contains Cell and
// cannot be shared across threads through a reference.
unsafe impl Sync for Locals {}
static PERCPU: Locals = Locals([const { PerCpu::new() }; MAX_CPUS]);

/// Fields accessed from another CPU. The AP publishes its APIC ID before
/// joining the online mask; the FPU and TLB protocols synchronize separately.
/// Each core's on its own cache-line pair, as `PerCpu`: every address-space
/// switch stores `asid`.
#[repr(align(128))]
struct Shared {
    pub apic_id: AtomicU32,
    pub fpu_owner: AtomicU64,
    pub asid: AtomicU64,
}

static SHARED: [Shared; MAX_CPUS] = [const {
    Shared { apic_id: AtomicU32::new(0), fpu_owner: AtomicU64::new(0), asid: AtomicU64::new(0) }
}; MAX_CPUS];

fn shared(cpu: usize) -> &'static Shared {
    &SHARED[cpu]
}

pub fn apic_id(cpu: usize) -> u32 {
    shared(cpu).apic_id.load(Ordering::Relaxed)
}

pub fn set_apic_id(id: u32) {
    shared(cpu_index()).apic_id.store(id, Ordering::Relaxed);
}

pub(crate) fn fpu_owner(cpu: usize) -> u64 {
    shared(cpu).fpu_owner.load(Ordering::Acquire)
}

pub(crate) fn set_fpu_owner(owner: u64) {
    shared(cpu_index()).fpu_owner.store(owner, Ordering::Release);
}

pub(crate) fn current_asid(cpu: usize) -> u64 {
    shared(cpu).asid.load(Ordering::SeqCst)
}

#[inline(always)]
pub(crate) fn publish_asid(asid: u64) {
    shared(cpu_index()).asid.store(asid, Ordering::SeqCst);
}

#[repr(C, align(4096))]
pub struct Stacks(pub UnsafeCell<[[u8; KSTACK_SIZE]; MAX_CPUS]>);
unsafe impl Sync for Stacks {}
pub static KSTACKS: Stacks = Stacks(UnsafeCell::new([[0; KSTACK_SIZE]; MAX_CPUS]));

/// The per-core entry areas (the kernel's `SkimCpu`s: entry stack and IST
/// stacks, one area per core, `SKIM_STRIDE` bytes apart from `SKIM_BASE`).
/// Registered once the kernel sets up its descriptor tables; 0 before.
static SKIM_BASE: AtomicU64 = AtomicU64::new(0);
static SKIM_STRIDE: AtomicU64 = AtomicU64::new(0);

/// Tell `cpu_index` where the per-core entry areas are.
pub fn register_entry_areas(base: u64, stride: u64) {
    SKIM_BASE.store(base, Ordering::Relaxed);
    SKIM_STRIDE.store(stride, Ordering::Relaxed);
}

/// The core whose stack `rsp` is on: core `c` runs the kernel on
/// KSTACKS[c], and takes NMI, #DB, #MC and #DF (and, briefly, every entry
/// from user mode) on the stacks of its entry area `c`. Anything else is
/// the boot core's early boot stack: core 0.
#[inline(always)]
fn index_of(rsp: u64, kstacks: u64, skim_base: u64, skim_stride: u64) -> usize {
    let off = rsp.wrapping_sub(kstacks);
    if off < (MAX_CPUS * KSTACK_SIZE) as u64 {
        return (off / KSTACK_SIZE as u64) as usize;
    }
    let off = rsp.wrapping_sub(skim_base);
    if skim_stride != 0 && off < MAX_CPUS as u64 * skim_stride {
        return (off / skim_stride) as usize;
    }
    0
}

/// The calling core's index, from the stack pointer (`index_of`).
#[inline(always)]
pub fn cpu_index() -> usize {
    let rsp: u64;
    unsafe { core::arch::asm!("mov {}, rsp", out(reg) rsp, options(nomem, nostack, preserves_flags)) };
    index_of(rsp, KSTACKS.0.get() as u64, SKIM_BASE.load(Ordering::Relaxed), SKIM_STRIDE.load(Ordering::Relaxed))
}

/// The current CPU's private state. Field accesses borrow only shared
/// references, including when a nested entry uses the same CPU.
#[inline(always)]
pub fn get() -> &'static PerCpu {
    &PERCPU.0[cpu_index()]
}

pub fn stack_top(cpu: usize) -> u64 {
    assert!(cpu < MAX_CPUS);
    KSTACKS.0.get() as u64 + ((cpu + 1) * KSTACK_SIZE) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    const KS: u64 = 0xffff_ffff_8060_0000;
    const SKIM: u64 = 0xffff_ffff_8020_0000;
    const STRIDE: u64 = 0x8000;

    #[test]
    fn every_kernel_stack_names_its_core() {
        for c in 0..MAX_CPUS {
            let base = KS + (c * KSTACK_SIZE) as u64;
            for rsp in [base, base + 8, base + KSTACK_SIZE as u64 - 8] {
                assert_eq!(index_of(rsp, KS, SKIM, STRIDE), c);
            }
        }
    }

    /// An NMI or #DB from user mode on core c runs on c's IST stacks, not
    /// KSTACKS: it must not be taken for core 0 (whose TCB, PerCpu and
    /// gate slot it would then use).
    #[test]
    fn entry_and_ist_stacks_name_their_core() {
        for c in 0..MAX_CPUS {
            let area = SKIM + c as u64 * STRIDE;
            // Header page, entry stack, then IST1..IST4.
            for page in 1..6 {
                let top = area + (page + 1) * 4096;
                assert_eq!(index_of(top - 176, KS, SKIM, STRIDE), c, "core {c} page {page}");
                assert_eq!(index_of(area + page * 4096, KS, SKIM, STRIDE), c);
            }
            assert_eq!(index_of(area + STRIDE - 8, KS, SKIM, STRIDE), c);
        }
    }

    #[test]
    fn other_stacks_are_the_boot_core() {
        // The early boot stack, and anything outside both ranges.
        assert_eq!(index_of(0xffff_ffff_8019_0000, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(SKIM + MAX_CPUS as u64 * STRIDE, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(KS + (MAX_CPUS * KSTACK_SIZE) as u64, KS, SKIM, STRIDE), 0);
        assert_eq!(index_of(SKIM - 8, KS, SKIM, STRIDE), 0);
        // Before the entry areas are registered.
        assert_eq!(index_of(SKIM + 3 * STRIDE + 4096, KS, 0, 0), 0);
    }

    #[test]
    fn the_real_kernel_stacks_name_their_core() {
        let base = KSTACKS.0.get() as u64;
        assert_eq!(index_of(base + 5 * KSTACK_SIZE as u64 + 100, base, 0, 0), 5);
    }
}
