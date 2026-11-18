//! The EL1 virtual timer (CNTV), the kernel's MCS timer. Ticks are the
//! virtual counter's, at the CNTFRQ_EL0 rate read at boot (l4h 0016).
use crate::percpu;
use core::sync::atomic::{AtomicU64, Ordering};

static FREQ: AtomicU64 = AtomicU64::new(1);

pub const KERNEL_WCET_US: u64 = 10;
const CTL_ENABLE: u64 = 1;
const CTL_IMASK: u64 = 2;

pub fn init() -> bool {
    let f = crate::mrs!("cntfrq_el0") & 0xffff_ffff;
    FREQ.store(f.max(1), Ordering::Relaxed);
    init_core();
    f != 0
}

/// Per core: the timer off until armed. EL0 may read the virtual counter
/// (libsel4's clock) and, as the user configuration exports them, the
/// physical counter and timer (`KernelArmExportPCNTUser`,
/// `KernelArmExportPTMRUser`).
pub fn init_core() {
    crate::msr!("cntv_ctl_el0", 0);
    let mut k = 1 << 1; // EL0VCTEN
    if fl4_abi::config::ARM_EXPORT_PCNT_USER {
        k |= 1 << 0; // EL0PCTEN
    }
    if fl4_abi::config::ARM_EXPORT_PTMR_USER {
        k |= 1 << 9; // EL0PTEN
    }
    crate::msr!("cntkctl_el1", k);
    crate::cpu::isb();
}

pub fn freq() -> u64 {
    FREQ.load(Ordering::Relaxed)
}

#[inline]
pub fn now() -> u64 {
    crate::cpu::isb();
    crate::mrs!("cntvct_el0")
}

/// Interrupt at counter value `ticks` (or at once if it passed).
pub fn set_deadline(ticks: u64) {
    percpu::get().armed.set(ticks);
    crate::msr!("cntv_cval_el0", if ticks == 0 { 1 } else { ticks });
    crate::msr!("cntv_ctl_el0", CTL_ENABLE);
    crate::cpu::isb();
}

/// The timer interrupt was taken: stop it asserting (it is level
/// triggered) until the kernel arms it again.
pub fn quiesce() {
    crate::msr!("cntv_ctl_el0", CTL_ENABLE | CTL_IMASK);
    crate::cpu::isb();
}

/// A timer interrupt arrived: is it stale (l4h 0012)? It is when the
/// timer is armed for a deadline still ahead, which replaced the one
/// that fired. The kernel need not run then.
pub fn early() -> bool {
    let armed = percpu::get().armed.get();
    armed != 0 && now() < armed
}

pub fn us_to_ticks(us: u64) -> u64 {
    let t = us as u128 * freq() as u128 / 1_000_000;
    if t > u64::MAX as u128 {
        u64::MAX
    } else {
        t as u64
    }
}

pub fn ticks_to_us(ticks: u64) -> u64 {
    (ticks as u128 * 1_000_000 / freq() as u128) as u64
}

/// Largest number of microseconds whose tick count fits in 64 bits.
pub fn max_us() -> u64 {
    let m = u64::MAX as u128 * 1_000_000 / freq() as u128;
    if m > u64::MAX as u128 {
        u64::MAX
    } else {
        m as u64
    }
}
