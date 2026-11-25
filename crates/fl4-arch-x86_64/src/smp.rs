//! Cross-core requests: remote calls (stall, TLB invalidation, FPU state,
//! VMCLEAR) and reschedule IPIs. A remote call is made with the serial
//! gate held, or, for a TLB invalidation or a VMCLEAR, by a local path
//! beside it (fl4-sync's frame invocations; a VCPU state invocation's
//! `vm::sync`); `CALL_LOCK` gives one of them the mailbox at a time.
//! Targets service it in their interrupt handler or while spinning (on the
//! gate, on `CALL_LOCK`; fl4-kernel), and the caller waits for every
//! acknowledgement.
//!
//! The gate holder never waits for `CALL_LOCK`: it makes calls only in its
//! body, after the local paths drained, and none starts until it leaves.
//! So only local paths contend for it, and they make only TLB
//! invalidations and VMCLEARs; a stall, which only the gate holder makes,
//! cannot reach a core spinning for it. Code outside both (`vm::run`,
//! after the gate is released) makes no remote call. Every core a caller waits for is in user code,
//! idle, or in the kernel heading for a loop that services calls (local
//! paths wait only here), so the wait ends.
use crate::{apic, percpu};
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout::irq;

pub const REMOTE_CALL_VECTOR: u32 = (irq::REMOTE_CALL_IPI + irq::INT_OFFSET) as u32;
pub const RESCHEDULE_VECTOR: u32 = (irq::RESCHEDULE_IPI + irq::INT_OFFSET) as u32;

pub const CALL_STALL: u64 = 1;
pub const CALL_INVLPG: u64 = 2;
pub const CALL_FLUSH_TLB: u64 = 3;
pub const CALL_FPU_DROP: u64 = 5;
pub const CALL_EPT: u64 = 6;
pub const CALL_FPU_RELEASE: u64 = 7;
pub const CALL_CVM_INVLPG: u64 = 8;
/// VMCLEAR a VCPU's VMCS here: it is to be loaded on another core or
/// deleted (`vm::load`, `vm::release`).
pub const CALL_VMCLEAR: u64 = 9;

/// Kernel entries by how they ran, on all cores (DESIGN.md §7).
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
/// 1 while a core uses `CALL` (module comment).
static CALL_LOCK: AtomicU64 = AtomicU64::new(0);

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

/// Run `f` on each core in `mask`, lowest first.
fn each(mut mask: u64, mut f: impl FnMut(usize)) {
    while mask != 0 {
        f(mask.trailing_zeros() as usize);
        mask &= mask - 1;
    }
}

fn ipi(c: usize, vector: u32) {
    // Fixed delivery, physical destination, assert.
    apic::send_ipi(percpu::apic_id(c), vector | (1 << 14));
}

/// Make the cores in `mask` (other than this one) run a remote call, and
/// wait until all have. The caller holds the serial gate, or is a local
/// path making a TLB invalidation (module comment).
pub fn remote_call(kind: u64, arg0: u64, arg1: u64, mask: u64) {
    let me = 1u64 << percpu::cpu_index();
    let targets = mask & !me & online_mask();
    if targets == 0 {
        return;
    }
    while CALL_LOCK.load(Ordering::Relaxed) != 0
        || CALL_LOCK.compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed).is_err()
    {
        // Another local path's invalidation, which may be waiting for
        // this core. No stall can come here (module comment).
        service(|| debug_assert!(false, "stall while waiting for CALL_LOCK"));
        core::hint::spin_loop();
    }
    CALL.kind.store(kind, Ordering::Relaxed);
    CALL.arg0.store(arg0, Ordering::Relaxed);
    CALL.arg1.store(arg1, Ordering::Relaxed);
    CALL.pending.store(targets, Ordering::Release);
    each(targets, |c| ipi(c, REMOTE_CALL_VECTOR));
    while CALL.pending.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
    CALL_LOCK.store(0, Ordering::Release);
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
        CALL_EPT => crate::vm::invalidate_local(a0),
        CALL_FPU_DROP => crate::fpu::forget_local(a0),
        CALL_FPU_RELEASE => crate::fpu::release_local(a0),
        CALL_CVM_INVLPG => crate::cvm::invalidate_aliases(a0, a1),
        CALL_VMCLEAR => crate::vm::vmclear_local(a0),
        _ => {}
    }
    CALL.pending.fetch_and(!me, Ordering::AcqRel);
    stalled
}

/// `service` for a remote call that is no stall, from user mode before the
/// thread's registers are saved: false, with the call left pending, if it
/// is a stall (which needs the kernel entry). A call addressed to this
/// core cannot change while it is pending: the caller waits for it.
pub fn service_unless_stall() -> bool {
    let me = 1u64 << percpu::cpu_index();
    if CALL.pending.load(Ordering::Acquire) & me == 0 {
        return true;
    }
    if CALL.kind.load(Ordering::Relaxed) == CALL_STALL {
        return false;
    }
    let _ = service(|| debug_assert!(false, "stall in service_unless_stall"));
    true
}

/// Send reschedule IPIs to the cores in `mask` other than this one.
pub fn reschedule(mask: u64) {
    let me = 1u64 << percpu::cpu_index();
    let targets = mask & !me & online_mask();
    each(targets, |c| ipi(c, RESCHEDULE_VECTOR));
}


/// Whether an idle core polls before it halts (fl4-kernel's fl4_idle):
/// with other cores to wake it, under a hypervisor (CPUID.1:ECX[31]),
/// where a halt and the wakeup from it are exits, and not in a CVM, where
/// the poll's RDTSC may itself exit. On bare metal HLT is cheap and the
/// spin would only burn power and an SMT sibling's share. Decided once.
pub fn idle_polls() -> bool {
    static POLLS: core::sync::atomic::AtomicU8 = core::sync::atomic::AtomicU8::new(0);
    // Cores come online after boot: only the platform is decided once.
    multi()
        && match POLLS.load(Ordering::Relaxed) {
            1 => false,
            2 => true,
            _ => {
                let on = crate::cpu::cpuid(1, 0).ecx & (1 << 31) != 0 && !crate::cvm::active();
                POLLS.store(if on { 2 } else { 1 }, Ordering::Relaxed);
                on
            }
        }
}
