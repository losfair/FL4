//! Speculative-execution mitigations, each on exactly when the CPU needs
//! it (DESIGN.md §3).
//!
//! - Meltdown (rogue data cache load): the skim window, on Intel CPUs that
//!   do not report RDCL_NO in IA32_ARCH_CAPABILITIES (or have no such MSR).
//!   User address spaces then map only the kernel image, not the window
//!   onto physical memory, and every entry switches to the kernel's tables.
//! - Spectre v2 against the kernel: enhanced IBRS (Intel, IBRS_ALL) or
//!   automatic IBRS (AMD), set once per core when the CPU has it.
//! - Guest returns require eIBRS or Automatic IBRS. VMX additionally uses
//!   the PBRSB exit sequence unless the CPU reports PBRSB_NO.
//!
//! IBPB on context switch is not used: it guards user programs against
//! each other through the branch predictor at thousands of cycles per
//! switch between address spaces, and, as in seL4's default
//! configuration, that threat is outside FL4's model for now.
use crate::cpu::{cpuid, msr, rdmsr, wrmsr};
use core::sync::atomic::{AtomicBool, Ordering};

const MSR_ARCH_CAPABILITIES: u32 = 0x10a;
const MSR_SPEC_CTRL: u32 = 0x48;
const ARCH_CAP_RDCL_NO: u64 = 1 << 0;
const ARCH_CAP_IBRS_ALL: u64 = 1 << 1;
const ARCH_CAP_PBRSB_NO: u64 = 1 << 24;
const SPEC_CTRL_IBRS: u64 = 1 << 0;
const EFER_AIBRSE: u64 = 1 << 21;

static SKIM: AtomicBool = AtomicBool::new(false);
static EIBRS: AtomicBool = AtomicBool::new(false);
static AUTO_IBRS: AtomicBool = AtomicBool::new(false);

fn is_intel() -> bool {
    let v = cpuid(0, 0);
    v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e
}

fn arch_capabilities() -> Option<u64> {
    if cpuid(0, 0).eax >= 7 && cpuid(7, 0).edx & (1 << 29) != 0 {
        Some(rdmsr(MSR_ARCH_CAPABILITIES))
    } else {
        None
    }
}

fn vmx_pbrsb_for(caps: Option<u64>) -> Option<bool> {
    let caps = caps?;
    // PBRSB_NO alone does not protect returns from guest RSB poisoning.
    (caps & ARCH_CAP_IBRS_ALL != 0).then_some(caps & ARCH_CAP_PBRSB_NO == 0)
}

/// None disables VMX without eIBRS; Some(true) selects Intel's PBRSB
/// sequence (CVE-2022-26373). Probe every core before enabling VMX there.
pub(crate) fn vmx_pbrsb() -> Option<bool> {
    vmx_pbrsb_for(arch_capabilities())
}

/// Automatic IBRS provides guest-return protection: RAP clearing on
/// VMEXIT, or host/guest isolation on ERAPS CPUs (AMD APM vol. 2 §3.2.9).
/// Older CPUs need software mitigations that FL4 does not provide.
pub(crate) fn auto_ibrs_supported() -> bool {
    cpuid(0x8000_0000, 0).eax >= 0x8000_0021 && cpuid(0x8000_0021, 0).eax & (1 << 8) != 0
}

/// Decide the mitigations on the boot core.
pub fn detect() {
    let caps = arch_capabilities();
    let intel = is_intel();
    let rdcl_no = caps.is_some_and(|c| c & ARCH_CAP_RDCL_NO != 0);
    SKIM.store(intel && !rdcl_no, Ordering::Relaxed);
    EIBRS.store(caps.is_some_and(|c| c & ARCH_CAP_IBRS_ALL != 0), Ordering::Relaxed);
    AUTO_IBRS.store(auto_ibrs_supported(), Ordering::Relaxed);
}

/// Turn on this core's per-core mitigations.
pub fn init_core() {
    if EIBRS.load(Ordering::Relaxed) {
        wrmsr(MSR_SPEC_CTRL, rdmsr(MSR_SPEC_CTRL) | SPEC_CTRL_IBRS);
    }
    if AUTO_IBRS.load(Ordering::Relaxed) {
        wrmsr(msr::EFER, rdmsr(msr::EFER) | EFER_AIBRSE);
    }
}

/// The skim window is in use.
pub fn skim() -> bool {
    SKIM.load(Ordering::Relaxed)
}

/// For the boot banner.
pub fn describe() -> &'static str {
    match (skim(), EIBRS.load(Ordering::Relaxed), AUTO_IBRS.load(Ordering::Relaxed)) {
        (true, true, _) => "skim window, enhanced IBRS",
        (true, false, _) => "skim window",
        (false, true, _) => "enhanced IBRS",
        (false, false, true) => "automatic IBRS",
        (false, false, false) => "none needed",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vmx_requires_eibrs_even_with_rdcl_no_or_pbrsb_no() {
        for caps in [
            None,
            Some(0),
            Some(ARCH_CAP_RDCL_NO),
            Some(ARCH_CAP_PBRSB_NO),
            Some(ARCH_CAP_RDCL_NO | ARCH_CAP_PBRSB_NO),
        ] {
            assert_eq!(vmx_pbrsb_for(caps), None);
        }
    }

    #[test]
    fn eibrs_requires_the_exit_sequence_unless_pbrsb_no_is_present() {
        assert_eq!(vmx_pbrsb_for(Some(ARCH_CAP_IBRS_ALL)), Some(true));
        assert_eq!(
            vmx_pbrsb_for(Some(ARCH_CAP_IBRS_ALL | ARCH_CAP_PBRSB_NO)),
            Some(false)
        );
    }
}
