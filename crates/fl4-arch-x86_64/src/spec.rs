//! Speculation policy and boot-time activation. See
//! docs/virtualization-security.md for the supported CPU/firmware contract.
use crate::{
    cpu::{self, cpuid, msr, rdmsr, wrmsr},
    percpu,
};
use core::fmt;
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

pub mod policy;
use policy::*;

// Written during serialized BSP/AP startup, frozen before users run.
// Native entries use the union, so NMI/IST entries need neither GS nor a
// CPU-index lookup before the barrier. Every enabled action is legal on
// all admitted cores; VM exits use each core's own plan. Entries read them
// on the user's tables, so they live in the skim window (paging.rs).
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_SPEC_ENTRY: AtomicU32 = AtomicU32::new(0);
/// Published once before running the root task or releasing APs.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_SAFE_RET: AtomicBool = AtomicBool::new(false);
static ALL_SAFE_RET: AtomicBool = AtomicBool::new(true);
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_SPEC_BUFFERS: AtomicU32 = AtomicU32::new(0);
static NO_SMT: AtomicBool = AtomicBool::new(false);
static SKIM: AtomicBool = AtomicBool::new(false);
static BOOT_VENDOR: AtomicU32 = AtomicU32::new(0);
static BOOT_IBPB: AtomicBool = AtomicBool::new(false);
/// The boot core's `select` succeeded.
static BOOT_PLAN: AtomicBool = AtomicBool::new(false);

fn caps() -> Caps {
    let root = cpuid(0, 0);
    let ext = cpuid(0x8000_0000, 0).eax;
    let one = cpuid(1, 0);
    let vendor = match (root.ebx, root.edx, root.ecx) {
        (0x756e_6547, 0x4965_6e69, 0x6c65_746e) => Vendor::Intel,
        (0x6874_7541, 0x6974_6e65, 0x444d_4163) => Vendor::Amd,
        _ => Vendor::Other,
    };
    let seven = if root.eax >= 7 {
        cpuid(7, 0)
    } else {
        cpu::Cpuid {
            eax: 0,
            ebx: 0,
            ecx: 0,
            edx: 0,
        }
    };
    let arch = if vendor == Vendor::Intel && seven.edx & (1 << 29) != 0 {
        rdmsr(0x10a)
    } else {
        0
    };
    let family = (one.eax >> 8) & 15;
    let model = (one.eax >> 4) & 15;
    let microcode = match vendor {
        Vendor::Intel if one.ecx & (1 << 31) == 0 && arch & RDCL_NO != 0 => {
            // IA32_BIOS_SIGN_ID is refreshed by CPUID.1 after clearing it.
            wrmsr(0x8b, 0);
            cpuid(1, 0);
            (rdmsr(0x8b) >> 32) as u32
        }
        Vendor::Amd if family == 15 && one.ecx & (1 << 31) == 0 => rdmsr(0x8b) as u32,
        _ => 0,
    };
    let a21 = if ext >= 0x8000_0021 {
        cpuid(0x8000_0021, 0)
    } else {
        cpu::Cpuid {
            eax: 0,
            ebx: 0,
            ecx: 0,
            edx: 0,
        }
    };
    Caps {
        vendor,
        family: family
            + if family == 15 {
                (one.eax >> 20) & 255
            } else {
                0
            },
        model: model
            | if family == 6 || family == 15 {
                (one.eax >> 12) & 0xf0
            } else {
                0
            },
        stepping: one.eax & 15,
        hypervisor: one.ecx & (1 << 31) != 0,
        microcode,
        arch,
        leaf7_edx: seven.edx,
        leaf7_2_edx: if seven.eax >= 2 { cpuid(7, 2).edx } else { 0 },
        smep: seven.ebx & (1 << 7) != 0,
        rtm: seven.ebx & (1 << 11) != 0,
        amd8: if ext >= 0x8000_0008 {
            cpuid(0x8000_0008, 0).ebx
        } else {
            0
        },
        amd21: a21.eax,
        amd21_ecx: a21.ecx,
    }
}

/// Enable the native policy after all admitted cores have contributed.
pub fn finish_native_entry_policy(patch_return_thunk: impl FnOnce()) -> bool {
    if !ALL_SAFE_RET.load(Ordering::Relaxed) {
        return false;
    }
    patch_return_thunk();
    FL4_SAFE_RET.store(true, Ordering::Release);
    true
}

/// Whether the kernel needs the skim window (Meltdown, rogue data cache
/// load): on Intel CPUs that do not report RDCL_NO, and on CPUs of vendors
/// whose immunity FL4 cannot tell. AMD and Hygon (AMD's Zen design) are
/// not affected.
fn needs_skim(vendor: Vendor, hygon: bool, arch: u64) -> bool {
    match vendor {
        Vendor::Amd => false,
        Vendor::Intel => arch & RDCL_NO == 0,
        Vendor::Other => !hygon,
    }
}

fn hygon() -> bool {
    let v = cpuid(0, 0);
    // "HygonGenuine".
    (v.ebx, v.edx, v.ecx) == (0x6f67_7948, 0x6e65_476e, 0x656e_6975)
}

pub fn detect() {
    let c = caps();
    SKIM.store(needs_skim(c.vendor, hygon(), c.arch), Ordering::Relaxed);
}

/// Whether an AP may join the boot core: the boot core chose the skim
/// window from its own capabilities only, so an AP that needs it when the
/// boot core did not would run user code with the kernel mapped; and an
/// AP whose `select` fails beside a boot core whose `select` succeeded
/// would leave that core with an incomplete policy the boot core reports
/// as complete (and skip the stricter-SMT check below).
fn ap_admissible(boot_skim: bool, ap_needs_skim: bool, boot_plan: bool, ap_plan: bool) -> bool {
    (boot_skim || !ap_needs_skim) && (ap_plan || !boot_plan)
}

/// Probe and initialize each logical CPU after its GDT/IDT is installed,
/// before VMX/SVM is enabled. BSP rejection leaves virtualization unavailable;
/// available native mitigations are still applied. Incompatible AP capabilities
/// return false here or fail the subsequent VM initialization, halting boot.
pub fn init_core(bsp: bool) -> bool {
    let c = caps();
    let ibpb = match c.vendor {
        Vendor::Intel => c.leaf7_edx & (1 << 26) != 0,
        Vendor::Amd => c.amd8 & AMD_IBPB != 0,
        Vendor::Other => false,
    };
    let vendor = c.vendor as u32;
    if bsp {
        BOOT_VENDOR.store(vendor, Ordering::Relaxed);
        BOOT_IBPB.store(ibpb, Ordering::Relaxed);
    } else if BOOT_VENDOR.load(Ordering::Relaxed) != vendor
        || BOOT_IBPB.load(Ordering::Relaxed) != ibpb
    {
        return false;
    }
    // On bare metal explicitly make LFENCE dispatch-serializing. A nested
    // VMM requires the architected CPUID promise from L0 instead.
    if c.vendor == Vendor::Amd && !c.hypervisor && (zen2(&c) || c.family >= 0x19) {
        let mut de_cfg = rdmsr(0xc001_1029) | 2;
        if zen2(&c) {
            // Zenbleed software workaround, unless known fixed by this
            // patch stream. Never undo a workaround set by firmware.
            let fixed = match (c.model, c.stepping) {
                (0x31, 0) => Some(0x0830107b),
                (0x60, 1) => Some(0x0860010c),
                (0x68, 1) => Some(0x08608107),
                (0x71, 0) => Some(0x08701033),
                (0xa0, 0) => Some(0x08a00009),
                _ => None,
            }
            .is_some_and(|r| c.microcode >= r);
            if !fixed {
                de_cfg |= 1 << 9;
            }
        }
        wrmsr(0xc001_1029, de_cfg);
    }
    let plan = select(&c);
    if bsp {
        BOOT_PLAN.store(plan.is_ok(), Ordering::Relaxed);
    } else if !ap_admissible(SKIM.load(Ordering::Relaxed), needs_skim(c.vendor, hygon(), c.arch),
        BOOT_PLAN.load(Ordering::Relaxed), plan.is_ok()) {
        return false;
    }
    let pc = percpu::get();
    pc.spec_plan.set(plan.ok());
    pc.spec_rejected.set(plan.err());
    let mut entry = 0;
    let mut spec_ctrl = 0;
    let mut auto = false;
    if let Ok(p) = plan {
        // A stricter AP policy must not leave an already-started sibling
        // running. Mixed requirements need topology-aware admission before
        // AP startup; reject such a configuration until that exists.
        if !bsp && p.no_smt && !NO_SMT.load(Ordering::Relaxed) {
            return false;
        }
        entry = p.entry;
        spec_ctrl = p.spec_ctrl;
        auto = p.auto_ibrs;
        FL4_SPEC_BUFFERS.fetch_or(u32::from(p.buffers), Ordering::Relaxed);
        NO_SMT.fetch_or(p.no_smt, Ordering::Relaxed);
        if p.disable_tsx {
            wrmsr(0x122, rdmsr(0x122) | 3);
        }
    } else {
        // Native-only boots get available mitigations, reported as
        // incomplete. This path never authorizes guest execution.
        if ibpb {
            entry = IBPB;
            if c.vendor == Vendor::Amd && c.amd8 & (1 << 30) == 0 {
                entry |= RSB;
            }
        }
        if c.vendor == Vendor::Intel && c.leaf7_edx & (1 << 26) != 0 {
            spec_ctrl = 1;
            entry |= if c.arch & IBRS_ALL != 0 {
                PBRSB
            } else {
                LEGACY_IBRS | RSB
            };
        }
        if c.vendor == Vendor::Amd {
            auto = c.amd21 & AUTO_IBRS != 0;
        }
        FL4_SPEC_BUFFERS.store(1, Ordering::Relaxed);
    }
    let safe_ret = native_safe_ret(&c) && !crate::sev::snp::active()
        && matches!(plan, Ok(_) | Err(Rejected::BufferMicrocode));
    ALL_SAFE_RET.fetch_and(safe_ret, Ordering::Relaxed);
    if safe_ret && plan.is_err() {
        // A native-only boot still needs cross-thread predictor isolation.
        spec_ctrl |= 2;
        NO_SMT.store(true, Ordering::Relaxed);
    }
    if spec_ctrl != 0 {
        wrmsr(0x48, rdmsr(0x48) | spec_ctrl);
    }
    if auto {
        wrmsr(msr::EFER, rdmsr(msr::EFER) | (1 << 21));
    }
    // VERW must not be disabled via FB_CLEAR_DIS. Also retain the
    // enumerated microcode mitigation for Gather Data Sampling.
    if c.vendor == Vendor::Intel && c.arch & ((1 << 18) | GDS_CTRL) != 0 {
        let mut mcu = rdmsr(0x123);
        if c.arch & (1 << 18) != 0 {
            mcu &= !(1 << 3);
        }
        if c.arch & GDS_CTRL != 0 {
            mcu &= !(1 << 4);
        }
        wrmsr(0x123, mcu);
    }
    FL4_SPEC_ENTRY.fetch_or(entry, Ordering::Relaxed);
    true
}

pub(crate) fn vmexit() -> Option<u32> {
    percpu::get().spec_plan.get().map(|p| p.vmexit)
}
pub fn skim() -> bool {
    SKIM.load(Ordering::Relaxed)
}
pub fn no_smt() -> bool {
    NO_SMT.load(Ordering::Relaxed)
}

/// Low APIC-ID bits representing SMT siblings. Unknown topology under a
/// no-SMT policy is handled by using only the BSP.
pub fn smt_shift() -> Option<u32> {
    let max = cpuid(0, 0).eax;
    for leaf in [0x1f, 0xb] {
        if max >= leaf {
            let c = cpuid(leaf, 0);
            if c.ebx != 0 && (c.ecx >> 8) & 255 == 1 {
                return Some(c.eax & 31);
            }
        }
    }
    if cpuid(0x8000_0000, 0).eax >= 0x8000_001e && cpuid(0x8000_0001, 0).ecx & (1 << 22) != 0 {
        let threads = ((cpuid(0x8000_001e, 0).ebx >> 8) & 255) + 1;
        return Some(32 - (threads - 1).leading_zeros());
    }
    None
}

pub fn allow_ap(apic: u32, bsp: u32, shift: Option<u32>, no_smt: bool) -> bool {
    if apic == bsp {
        return false;
    }
    if !no_smt {
        return true;
    }
    let Some(shift) = shift else {
        return false;
    };
    let mask = (1u32 << shift) - 1;
    apic & mask == 0 && apic >> shift != bsp >> shift
}

pub struct Status(Option<Plan>, Option<Rejected>);
impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(e) = self.1 {
            return write!(f, "incomplete: {}", e.describe());
        }
        let Some(p) = self.0 else {
            return f.write_str("not initialized");
        };
        write!(f, "IBPB on kernel entry and VM exit")?;
        if p.auto_ibrs {
            f.write_str(", AutoIBRS")?;
        }
        if p.spec_ctrl & 1 != 0 {
            f.write_str(if p.entry & LEGACY_IBRS != 0 {
                ", legacy IBRS"
            } else {
                ", eIBRS"
            })?;
        }
        if p.vmexit & RSB != 0 {
            f.write_str(", RSB fill")?;
        }
        if p.vmexit & PBRSB != 0 {
            f.write_str(", PBRSB")?;
        }
        if p.vmexit & BHB != 0 {
            f.write_str(", BHB clear")?;
        }
        if p.spec_ctrl & (1 << 10) != 0 {
            f.write_str(", BHI_DIS_S")?;
        }
        if p.buffers {
            f.write_str(", VERW")?;
        }
        if p.spec_ctrl & 2 != 0 {
            f.write_str(", STIBP")?;
        }
        if p.no_smt {
            f.write_str(", SMT siblings parked")?;
        }
        Ok(())
    }
}
pub fn describe() -> Status {
    let pc = percpu::get();
    Status(pc.spec_plan.get(), pc.spec_rejected.get())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skim_window_fails_closed_for_unknown_vendors() {
        assert!(!needs_skim(Vendor::Amd, false, 0));
        assert!(needs_skim(Vendor::Intel, false, 0));
        assert!(!needs_skim(Vendor::Intel, false, RDCL_NO));
        assert!(!needs_skim(Vendor::Other, true, 0));
        // Other vendors' architectural capabilities are not read.
        assert!(needs_skim(Vendor::Other, false, 0));
        assert!(needs_skim(Vendor::Other, false, RDCL_NO));
    }

    /// Audit round 5 F4: with no VM backend nothing else compares an AP's
    /// speculation state with the boot core's.
    #[test]
    fn aps_never_weaken_the_boot_cores_skim_window_or_policy() {
        // AP needs the skim window the boot core did not turn on.
        assert!(!ap_admissible(false, true, true, true));
        assert!(!ap_admissible(false, true, false, false));
        assert!(ap_admissible(true, true, true, true));
        assert!(ap_admissible(true, false, true, true));
        assert!(ap_admissible(false, false, true, true));
        // AP without a policy beside a boot core with one.
        assert!(!ap_admissible(false, false, true, false));
        assert!(!ap_admissible(true, true, true, false));
        // A boot core without one already reports the policy incomplete.
        assert!(ap_admissible(false, false, false, false));
        assert!(ap_admissible(false, false, false, true));
    }

    #[test]
    fn smt_admission_retains_bsp_and_one_thread_per_other_core() {
        assert!(!allow_ap(0, 0, Some(1), true));
        assert!(!allow_ap(1, 0, Some(1), true));
        assert!(allow_ap(2, 0, Some(1), true));
        assert!(!allow_ap(3, 0, Some(1), true));
        assert!(allow_ap(4, 0, Some(1), true));
        // A BSP booted on the secondary thread must retain its whole core.
        assert!(!allow_ap(0, 1, Some(1), true));
        assert!(allow_ap(2, 1, Some(1), true));
        assert!(allow_ap(1, 0, Some(0), true));
        assert!(!allow_ap(2, 0, None, true));
        assert!(allow_ap(2, 0, None, false));
    }
}
