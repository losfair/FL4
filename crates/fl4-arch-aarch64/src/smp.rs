//! Cross-core requests: remote calls (stall, FP/SIMD state) and
//! reschedule IPIs, as SGIs; starting cores with PSCI. A remote call is
//! made with the serial gate held; targets service it in their interrupt
//! handler or while spinning on the gate, and the caller waits for every
//! acknowledgement. TLB maintenance is broadcast (l4h 0015); only cores
//! running an invalidated ASID are called, to check it on their way out.
use crate::{gic, percpu};
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout::irq;

pub const CALL_STALL: u64 = 1;
pub const CALL_FPU_DROP: u64 = 5;
pub const CALL_FPU_RELEASE: u64 = 6;
pub const CALL_ASID: u64 = 7;
/// GICv2 banked interrupt (arg0) of the called core: mask (arg1 1) or
/// unmask it, or set edge (arg1 1) or level triggering (`gic::remote`).
pub const CALL_GIC_MASK: u64 = 8;
pub const CALL_GIC_CONFIG: u64 = 9;

static ONLINE: AtomicU64 = AtomicU64::new(1);
static NUM_ONLINE: AtomicU64 = AtomicU64::new(1);

struct Call {
    kind: AtomicU64,
    arg0: AtomicU64,
    arg1: AtomicU64,
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

pub fn multi() -> bool {
    num_online() > 1
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
            gic::send_sgi(irq::REMOTE_CALL_ID, c as u64);
        }
    }
    while CALL.pending.load(Ordering::Acquire) != 0 {
        core::hint::spin_loop();
    }
}

/// Service a remote call addressed to this core, if there is one.
/// Returns whether a stall was serviced.
pub fn service(stall: impl FnOnce()) -> bool {
    let me = 1u64 << percpu::cpu_index();
    if CALL.pending.load(Ordering::Acquire) & me == 0 {
        return false;
    }
    let kind = CALL.kind.load(Ordering::Relaxed);
    let a0 = CALL.arg0.load(Ordering::Relaxed);
    let a1 = CALL.arg1.load(Ordering::Relaxed);
    let stalled = kind == CALL_STALL;
    let here = percpu::cpu_index() as u64;
    match kind {
        CALL_STALL => stall(),
        CALL_FPU_DROP => crate::fpu::forget_local(a0),
        CALL_FPU_RELEASE => crate::fpu::release_local(a0),
        CALL_ASID => crate::mmu::retired(a0),
        CALL_GIC_MASK => gic::mask(a0, here, a1 != 0),
        CALL_GIC_CONFIG => gic::configure(a0, here, a1 != 0),
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
            gic::send_sgi(irq::RESCHEDULE_ID, c as u64);
        }
    }
}

/// PSCI conduit: 0 none, 1 SMC, 2 HVC.
static PSCI: AtomicU64 = AtomicU64::new(0);
pub const PSCI_NONE: u64 = 0;
pub const PSCI_SMC: u64 = 1;
pub const PSCI_HVC: u64 = 2;

pub fn set_psci(conduit: u64) {
    PSCI.store(conduit, Ordering::Relaxed);
}

pub fn psci() -> u64 {
    PSCI.load(Ordering::Relaxed)
}

fn psci_call(fid: u64, a1: u64, a2: u64, a3: u64) -> i64 {
    let mut r = fid;
    unsafe {
        match PSCI.load(Ordering::Relaxed) {
            PSCI_SMC => core::arch::asm!("smc #0", inout("x0") r, inout("x1") a1 => _, inout("x2") a2 => _, inout("x3") a3 => _,
                out("x4") _, out("x5") _, out("x6") _, out("x7") _, out("x8") _, out("x9") _, out("x10") _, out("x11") _,
                out("x12") _, out("x13") _, out("x14") _, out("x15") _, out("x16") _, out("x17") _),
            PSCI_HVC => core::arch::asm!("hvc #0", inout("x0") r, inout("x1") a1 => _, inout("x2") a2 => _, inout("x3") a3 => _,
                out("x4") _, out("x5") _, out("x6") _, out("x7") _, out("x8") _, out("x9") _, out("x10") _, out("x11") _,
                out("x12") _, out("x13") _, out("x14") _, out("x15") _, out("x16") _, out("x17") _),
            _ => r = (-1i64) as u64,
        }
    }
    r as i64
}

/// PSCI CPU_ON: start the core with affinity `mpidr` at physical address
/// `entry` with `ctx` in x0. Returns the PSCI status (0 on success).
pub fn cpu_on(mpidr: u64, entry: u64, ctx: u64) -> i64 {
    psci_call(0xc400_0003, mpidr, entry, ctx)
}

/// PSCI SYSTEM_OFF, if there is PSCI.
pub fn system_off() {
    psci_call(0x8400_0008, 0, 0, 0);
}
