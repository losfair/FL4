//! Cross-core requests: remote calls (stall, TLB invalidation, FPU state)
//! and reschedule IPIs. A remote call is made with the serial gate held;
//! targets service it in their interrupt handler or while spinning on the
//! gate (fl4-kernel), and the caller waits for every acknowledgement.
use crate::{apic, percpu};
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout::irq;

pub const REMOTE_CALL_VECTOR: u32 = (irq::REMOTE_CALL_IPI + irq::INT_OFFSET) as u32;
pub const RESCHEDULE_VECTOR: u32 = (irq::RESCHEDULE_IPI + irq::INT_OFFSET) as u32;

pub const CALL_STALL: u64 = 1;
pub const CALL_INVLPG: u64 = 2;
pub const CALL_FLUSH_TLB: u64 = 3;
pub const CALL_FPU_SAVE: u64 = 4;
pub const CALL_FPU_DROP: u64 = 5;
pub const CALL_EPT: u64 = 6;

/// Kernel entries by how they ran, on all cores (DESIGN.md §7).
pub static TX_COMMITS: AtomicU64 = AtomicU64::new(0);
pub static TX_ABORTS: AtomicU64 = AtomicU64::new(0);
pub static SERIAL_ENTRIES: AtomicU64 = AtomicU64::new(0);

/// Cores that have finished starting.
static ONLINE: AtomicU64 = AtomicU64::new(1);
static NUM_ONLINE: AtomicU64 = AtomicU64::new(1);

struct Call {
    kind: AtomicU64,
    arg0: AtomicU64,
    arg1: AtomicU64,
    /// Cores that still have to service the call.
    pending: AtomicU64,
}

static CALL: Call = Call { kind: AtomicU64::new(0), arg0: AtomicU64::new(0), arg1: AtomicU64::new(0), pending: AtomicU64::new(0) };

pub fn set_online(c: usize) {
    ONLINE.fetch_or(1 << c, Ordering::AcqRel);
    NUM_ONLINE.fetch_add(1, Ordering::AcqRel);
}

pub fn online_mask() -> u64 {
    ONLINE.load(Ordering::Acquire)
}

pub fn num_online() -> u64 {
    NUM_ONLINE.load(Ordering::Acquire)
}

/// More than one core runs the kernel: the serial gate and IPIs are needed.
pub fn multi() -> bool {
    num_online() > 1
}

fn ipi(c: usize, vector: u32) {
    // Fixed delivery, physical destination, assert.
    apic::send_ipi(percpu::get_for(c).apic_id, vector | (1 << 14));
}

/// Make the cores in `mask` (other than this one) run a remote call, and
/// wait until all have. The caller holds the serial gate.
pub fn remote_call(kind: u64, arg0: u64, arg1: u64, mask: u64) {
    let me = 1u64 << percpu::cpu_index();
    let targets = mask & !me & online_mask();
    if targets == 0 {
        return;
    }
    CALL.kind.store(kind, Ordering::Relaxed);
    CALL.arg0.store(arg0, Ordering::Relaxed);
    CALL.arg1.store(arg1, Ordering::Relaxed);
    CALL.pending.store(targets, Ordering::Release);
    for c in 0..percpu::MAX_CPUS {
        if targets & (1 << c) != 0 {
            ipi(c, REMOTE_CALL_VECTOR);
        }
    }
    while CALL.pending.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
}

/// Service a remote call addressed to this core, if there is one. A stall
/// runs `stall` (kernel logic, on behalf of the gate holder) before it is
/// acknowledged. Returns whether a stall was serviced.
pub fn service(stall: impl FnOnce()) -> bool {
    let me = 1u64 << percpu::cpu_index();
    if CALL.pending.load(Ordering::Acquire) & me == 0 {
        return false;
    }
    let kind = CALL.kind.load(Ordering::Relaxed);
    let a0 = CALL.arg0.load(Ordering::Relaxed);
    let a1 = CALL.arg1.load(Ordering::Relaxed);
    let stalled = kind == CALL_STALL;
    match kind {
        CALL_STALL => stall(),
        CALL_INVLPG => crate::tlb::remote_invalidate_page(a0, a1),
        CALL_FLUSH_TLB => crate::tlb::remote_invalidate_asid(a0),
        CALL_FPU_SAVE => crate::fpu::flush_local(a0),
        CALL_EPT => crate::vm::invalidate_local(a0),
        CALL_FPU_DROP => crate::fpu::forget_local(a0),
        _ => {}
    }
    CALL.pending.fetch_and(!me, Ordering::AcqRel);
    stalled
}

/// Send reschedule IPIs to the cores in `mask` other than this one.
pub fn reschedule(mask: u64) {
    let me = 1u64 << percpu::cpu_index();
    let targets = mask & !me & online_mask();
    for c in 0..percpu::MAX_CPUS {
        if targets & (1 << c) != 0 {
            ipi(c, RESCHEDULE_VECTOR);
        }
    }
}

