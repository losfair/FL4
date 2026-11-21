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
/// Some core's Safe RET has no AutoIBRS: indirect branches need retpolines.
static RETPOLINE: AtomicBool = AtomicBool::new(false);
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
/// `patch` switches Rust returns to Safe RET and, if its argument is true,
/// indirect calls and jumps to the retpoline. Returns whether Safe RET is
/// on, and whether with retpolines.
pub fn finish_native_entry_policy(patch: impl FnOnce(bool)) -> Option<bool> {
    if !ALL_SAFE_RET.load(Ordering::Relaxed) {
        return None;
    }
    let retpoline = RETPOLINE.load(Ordering::Relaxed);
    patch(retpoline);
    FL4_SAFE_RET.store(true, Ordering::Release);
    Some(retpoline)
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

/// Whether a core whose policy needs one thread per physical core
/// (`needs_no_smt`) may join: an AP may not, once SMT siblings may have
/// been started (`no_smt` still false); a stricter AP policy must not
/// leave an already-started sibling running. Mixed requirements need
/// topology-aware admission before AP startup; reject such a configuration
/// until that exists. `Some(needs_no_smt)`: admitted, and whether it
/// requires `NO_SMT`.
fn smt_admission(bsp: bool, needs_no_smt: bool, no_smt: bool) -> Option<bool> {
    if needs_no_smt && !bsp && !no_smt {
        return None;
    }
    Some(needs_no_smt)
}

/// Whether a rejected `select` still lets this core's native entries use
/// Safe RET: rejections for VM support (buffer-clearing microcode, nested
/// LFENCE, SRSO's IBPB microcode) say nothing about native returns.
fn native_safe_ret_allowed(plan: &Result<Plan, Rejected>) -> bool {
    matches!(
        plan,
        Ok(_) | Err(Rejected::BufferMicrocode | Rejected::Lfence | Rejected::SrsoMicrocode)
    )
}

/// Whether this core's native entries skip IBPB (`allowed`: its
/// capabilities permit it, `native_entry_without_ibpb`): only with a plan
/// or a native-only rejection for buffer clearing alone (Safe RET also
/// allows the nested-LFENCE and SRSO-microcode rejections,
/// `native_safe_ret_allowed`).
fn entry_without_ibpb(allowed: bool, plan: &Result<Plan, Rejected>) -> bool {
    allowed && matches!(plan, Ok(_) | Err(Rejected::BufferMicrocode))
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
    let no_entry_ibpb = entry_without_ibpb(native_entry_without_ibpb(&c), &plan);
    if bsp {
        BOOT_PLAN.store(plan.is_ok(), Ordering::Relaxed);
    } else if !ap_admissible(SKIM.load(Ordering::Relaxed), needs_skim(c.vendor, hygon(), c.arch),
        BOOT_PLAN.load(Ordering::Relaxed), plan.is_ok()) {
        return false;
    }
    let pc = percpu::get();
    pc.spec_plan.set(plan.ok());
    pc.spec_rejected.set(plan.err());
    let safe_ret = native_safe_ret(&c) && native_safe_ret_allowed(&plan);
    // A native-only boot keeps SMT siblings, with Safe RET too: STIBP
    // (which `native_safe_ret` requires, and `native_only` sets) isolates
    // them, as in Linux on Zen 3/4. Only VM-capable plans park them on
    // SRSO-affected parts.
    let needs_no_smt = match plan {
        Ok(p) => p.no_smt,
        Err(_) => false,
    };
    let Some(needs_no_smt) = smt_admission(bsp, needs_no_smt, NO_SMT.load(Ordering::Relaxed)) else {
        return false;
    };
    let (entry, spec_ctrl, auto, disable_tsx) = if let Ok(p) = plan {
        FL4_SPEC_BUFFERS.fetch_or(u32::from(p.buffers), Ordering::Relaxed);
        (p.entry, p.spec_ctrl, p.auto_ibrs, p.disable_tsx)
    } else {
        // Native-only boots get available mitigations, reported as
        // incomplete. This path never authorizes guest execution.
        FL4_SPEC_BUFFERS.store(1, Ordering::Relaxed);
        let n = native_only(&c, no_entry_ibpb);
        (n.entry, n.spec_ctrl, n.auto_ibrs, n.disable_tsx)
    };
    if disable_tsx {
        wrmsr(0x122, rdmsr(0x122) | 3);
    }
    // `native_only` enables STIBP on every core that can use Safe RET
    // (native_safe_ret requires it).
    ALL_SAFE_RET.fetch_and(safe_ret, Ordering::Relaxed);
    RETPOLINE.fetch_or(safe_ret && native_retpoline(&c), Ordering::Relaxed);
    NO_SMT.fetch_or(needs_no_smt, Ordering::Relaxed);
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
        f.write_str(if p.entry & IBPB != 0 {
            "IBPB on kernel entry and VM exit"
        } else {
            "IBPB on VM exit"
        })?;
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

    /// Native-only boots (Safe RET or not) keep SMT siblings, so an AP
    /// never turns `NO_SMT` on halfway through AP startup (audit r11 F4).
    #[test]
    fn native_only_safe_ret_rejections_cover_vm_support_only() {
        for e in [Rejected::BufferMicrocode, Rejected::Lfence, Rejected::SrsoMicrocode] {
            assert!(native_safe_ret_allowed(&Err(e)));
        }
        for e in [Rejected::Vendor, Rejected::Meltdown, Rejected::Smep, Rejected::BeforeZen2,
                  Rejected::Ibpb, Rejected::ItsMicrocode] {
            assert!(!native_safe_ret_allowed(&Err(e)));
        }
    }

    /// Both policy paths share the stricter-AP rule: no core turns SMT
    /// off after siblings may have started.
    #[test]
    fn stricter_smt_need_is_refused_after_siblings_may_have_started() {
        // Boot core: decides before any AP starts.
        assert_eq!(smt_admission(true, true, false), Some(true));
        assert_eq!(smt_admission(true, false, false), Some(false));
        // AP needing no SMT, siblings possibly running: refused.
        assert_eq!(smt_admission(false, true, false), None);
        // AP needing no SMT under a no-SMT boot, or needing nothing.
        assert_eq!(smt_admission(false, true, true), Some(true));
        assert_eq!(smt_admission(false, false, false), Some(false));
        assert_eq!(smt_admission(false, false, true), Some(false));
    }

    #[test]
    fn entry_ibpb_is_kept_for_other_rejections() {
        let p = Plan {
            entry: 0,
            vmexit: IBPB,
            buffers: true,
            spec_ctrl: 2,
            auto_ibrs: true,
            no_smt: false,
            disable_tsx: false,
        };
        assert!(entry_without_ibpb(true, &Ok(p)));
        assert!(entry_without_ibpb(true, &Err(Rejected::BufferMicrocode)));
        assert!(!entry_without_ibpb(false, &Ok(p)));
        assert!(!entry_without_ibpb(false, &Err(Rejected::BufferMicrocode)));
        for e in [Rejected::SrsoMicrocode, Rejected::Lfence, Rejected::Ibpb] {
            assert!(!entry_without_ibpb(true, &Err(e)));
        }
    }

    #[test]
    fn status_names_the_entry_ibpb_only_when_used() {
        extern crate std;
        use std::format;
        let p = Plan {
            entry: 0,
            vmexit: IBPB,
            buffers: false,
            spec_ctrl: 0,
            auto_ibrs: true,
            no_smt: false,
            disable_tsx: false,
        };
        assert_eq!(format!("{}", Status(Some(p), None)), "IBPB on VM exit, AutoIBRS");
        let p = Plan { entry: IBPB, ..p };
        assert_eq!(
            format!("{}", Status(Some(p), None)),
            "IBPB on kernel entry and VM exit, AutoIBRS"
        );
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
