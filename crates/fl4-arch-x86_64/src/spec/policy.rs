//! Pure mitigation selection. Bit definitions come from the Intel SDM and
//! AMD APM; sources and the firmware contract are in docs/virtualization-security.md.

pub const IBPB: u32 = 1;
pub const RSB: u32 = 2;
pub const PBRSB: u32 = 4;
pub const LEGACY_IBRS: u32 = 8;
pub const BHB: u32 = 16;
pub const IBHF: u32 = 32;

pub const RDCL_NO: u64 = 1;
pub const IBRS_ALL: u64 = 1 << 1;
const MDS_NO: u64 = 1 << 5;
pub const TSX_CTRL: u64 = 1 << 7;
const TAA_NO: u64 = 1 << 8;
const MMIO_NO: u64 = 7 << 13;
const FB_CLEAR: u64 = 1 << 17;
const BHI_NO: u64 = 1 << 20;
const PBRSB_NO: u64 = 1 << 24;
pub const GDS_CTRL: u64 = 1 << 25;
const RFDS_NO: u64 = 1 << 27;
const RFDS_CLEAR: u64 = 1 << 28;
const ITS_NO: u64 = 1 << 62;

pub const AMD_IBPB: u32 = 1 << 12;
pub const AMD_STIBP: u32 = 1 << 15;
const AMD_IBPB_RET: u32 = 1 << 30;
pub const LFENCE_SERIAL: u32 = 1 << 2;
const VERW_CLEAR: u32 = 1 << 5;
pub const AUTO_IBRS: u32 = 1 << 8;
const IBPB_BRTYPE: u32 = 1 << 28;
const SRSO_NO: u32 = 1 << 29;
// AMD TSA guidance rev. 3.0 (November 2026), section 6, Fn8000_0021 ECX.
const TSA_SQ_NO: u32 = 1 << 1;
const TSA_L1_NO: u32 = 1 << 2;
const TSA_FILL_NO: u32 = 1 << 7;
const TSA_NO: u32 = TSA_SQ_NO | TSA_L1_NO | TSA_FILL_NO;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vendor {
    Intel,
    Amd,
    Other,
}

#[derive(Clone, Copy, Debug)]
pub struct Caps {
    pub vendor: Vendor,
    pub family: u32,
    pub model: u32,
    pub stepping: u32,
    pub hypervisor: bool,
    pub microcode: u32,
    pub arch: u64,
    pub leaf7_edx: u32,
    pub leaf7_2_edx: u32,
    pub smep: bool,
    pub rtm: bool,
    pub amd8: u32,
    pub amd21: u32,
    pub amd21_ecx: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Plan {
    /// Used at every native kernel entry, including NMI/exception entries.
    pub entry: u32,
    /// Used after saving guest GPRs, before any host RET or interrupt enable.
    pub vmexit: u32,
    pub buffers: bool,
    pub spec_ctrl: u64,
    pub auto_ibrs: bool,
    pub no_smt: bool,
    pub disable_tsx: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rejected {
    Vendor,
    Meltdown,
    Smep,
    BeforeZen2,
    Ibpb,
    SrsoMicrocode,
    BufferMicrocode,
    ItsMicrocode,
    Lfence,
}
impl Rejected {
    pub fn describe(self) -> &'static str {
        match self {
            Self::Vendor => "unsupported CPU vendor",
            Self::Meltdown => "Intel RDCL_NO is required (Meltdown immunity)",
            Self::Smep => "Intel return protection requires SMEP",
            Self::BeforeZen2 => "AMD Zen 2 or newer is required",
            Self::Ibpb => "IBPB support is required",
            Self::SrsoMicrocode => "SRSO mitigation needs updated microcode / IBPB_BRTYPE exposure",
            Self::BufferMicrocode => {
                "CPU buffer clearing needs updated microcode / capability exposure"
            }
            Self::ItsMicrocode => "ITS mitigation needs Intel IPU 2025.1 or newer microcode",
            Self::Lfence => "nested AMD requires LFENCE_ALWAYS_SERIALIZING",
        }
    }
}

pub fn zen2(c: &Caps) -> bool {
    c.vendor == Vendor::Amd
        && c.family == 0x17
        && matches!(c.model, 0x30..=0x4f | 0x60..=0x7f | 0x90..=0x91 | 0xa0..=0xaf)
}

// AMD TSA guidance, rev. 3.0 (November 2026), appendix. These revisions
// also postdate the family 19h SRSO/IBPB branch-type fixes. Never compare
// revisions belonging to different model/stepping patch streams.
pub fn amd_buffer_revision(model: u32, stepping: u32) -> Option<u32> {
    Some(match (model, stepping) {
        (0x01, 1) => 0x0a0011d7,
        (0x01, 2) => 0x0a00123b,
        (0x08, 2) => 0x0a00820d,
        (0x11, 1) => 0x0a10114c,
        (0x11, 2) => 0x0a10124c,
        (0x18, 1) => 0x0a108109,
        (0x21, 0) => 0x0a20102e,
        (0x21, 2) => 0x0a201211,
        (0x44, 1) => 0x0a404108,
        (0x50, 0) => 0x0a500012,
        (0x61, 2) => 0x0a60120a,
        (0x74, 1) => 0x0a704108,
        (0x75, 2) => 0x0a705208,
        (0x78, 0) => 0x0a708008,
        (0x7c, 0) => 0x0a70c008,
        (0xa0, 2) => 0x0aa00216,
        _ => return None,
    })
}

// Intel's microcode-20250512 release (INTEL-SA-01153). This matters even
// for ITS variants whose eIBRS guest/host isolation is unaffected: the
// VMSCAPE barrier must provide the documented IBPB semantics as well.
fn intel_its_revision(model: u32, stepping: u32) -> Option<u32> {
    Some(match (model, stepping) {
        (0x55, 7) => 0x05003901,
        (0x55, 0xb) => 0x07002b01,
        (0x8e, 0xc) => 0x100,
        (0x9e, 0xd) => 0x104,
        (0xa5, 2 | 3 | 5) => 0x100,
        (0xa6, 0) => 0x102,
        (0xa6, 1) => 0x100,
        (0x6a, 6) => 0x0d000404,
        (0x6c, 1) => 0x010002d0,
        (0x7e, 5) => 0xca,
        (0x8c, 1) => 0xbc,
        (0x8c, 2) => 0x3c,
        (0x8d, 1) => 0x56,
        (0xa7, 1) => 0x64,
        _ => return None,
    })
}

pub fn select(c: &Caps) -> Result<Plan, Rejected> {
    let mut p = Plan {
        entry: IBPB,
        vmexit: IBPB,
        buffers: false,
        spec_ctrl: 0,
        auto_ibrs: false,
        no_smt: false,
        disable_tsx: false,
    };
    match c.vendor {
        Vendor::Other => return Err(Rejected::Vendor),
        Vendor::Intel => {
            if c.arch & RDCL_NO == 0 {
                return Err(Rejected::Meltdown);
            }
            // Intel IBRS relies on SMEP for native user-to-supervisor
            // returns. This also rejects a nested host masking SMEP.
            if !c.smep {
                return Err(Rejected::Smep);
            }
            if c.leaf7_edx & (1 << 26) == 0 {
                return Err(Rejected::Ibpb);
            }
            p.spec_ctrl = 1; // eIBRS always on; legacy IBRS reasserted on entry.
            if c.arch & IBRS_ALL == 0 {
                p.entry |= LEGACY_IBRS;
                p.vmexit |= LEGACY_IBRS | RSB;
            } else if c.arch & PBRSB_NO == 0 {
                p.entry |= PBRSB;
                p.vmexit |= PBRSB;
            }
            if c.leaf7_edx & (1 << 27) != 0 {
                p.spec_ctrl |= 2;
            }
            p.no_smt = c.arch & IBRS_ALL == 0 && c.leaf7_edx & (1 << 27) == 0;
            if c.arch & BHI_NO == 0 {
                if c.leaf7_2_edx & (1 << 4) != 0 {
                    p.spec_ctrl |= 1 << 10;
                } else {
                    p.entry |= BHB;
                    p.vmexit |= BHB;
                }
                // IBHF is a NOP on older processors. Include it after the
                // software sequence as well, for virtualized environments.
                p.entry |= IBHF;
                p.vmexit |= IBHF;
            }
            let its = c.family == 6
                && (matches!(
                    c.model,
                    0x6a | 0x6c | 0x7e | 0x8c | 0x8d | 0xa5 | 0xa6 | 0xa7
                ) || c.model == 0x55 && c.stepping >= 6
                    || c.model == 0x8e && c.stepping >= 0xc
                    || c.model == 0x9e && c.stepping >= 0xd);
            // A nested VMM must trust L0 to implement the advertised IBPB
            // contract; guest IA32_BIOS_SIGN_ID is not a host patch level.
            if its
                && !c.hypervisor
                && c.arch & ITS_NO == 0
                && !intel_its_revision(c.model, c.stepping).is_some_and(|r| c.microcode >= r)
            {
                return Err(Rejected::ItsMicrocode);
            }
            let mds = c.arch & MDS_NO == 0;
            let mmio = c.arch & MMIO_NO != MMIO_NO
                && (c.hypervisor
                    || c.family == 6
                        && matches!(
                            c.model,
                            0x55 | 0x8e
                                | 0x9e
                                | 0x6a
                                | 0x6c
                                | 0x7e
                                | 0xa5
                                | 0xa6
                                | 0xa7
                                | 0x8a
                                | 0x86
                                | 0x96
                                | 0x9c
                        ));
            let rfds = c.arch & RFDS_NO == 0
                && (c.hypervisor
                    || c.family == 6
                        && matches!(
                            c.model,
                            0x5c | 0x5f
                                | 0x7a
                                | 0x86
                                | 0x96
                                | 0x9c
                                | 0x97
                                | 0x9a
                                | 0xb7
                                | 0xba
                                | 0xbf
                                | 0xbe
                        ));
            let taa = c.rtm && c.arch & TAA_NO == 0;
            p.disable_tsx = taa && c.arch & TSX_CTRL != 0;
            // Intel MMIO guidance, "Example Mitigation Selection": implicit
            // FB_CLEAR needs MDS_NO=0 as well as MD_CLEAR and FLUSH_L1D.
            if mds && c.leaf7_edx & (1 << 10) == 0
                || mmio
                    && c.arch & FB_CLEAR == 0
                    && !(mds && c.leaf7_edx & ((1 << 10) | (1 << 28)) == (1 << 10) | (1 << 28))
                || rfds && c.arch & RFDS_CLEAR == 0
                || taa && !p.disable_tsx
            {
                return Err(Rejected::BufferMicrocode);
            }
            p.buffers = mds || mmio || rfds;
            // Buffer clearing cannot isolate concurrently executing SMT
            // siblings on MDS/MMIO-affected CPUs.
            p.no_smt |= mds || mmio;
        }
        Vendor::Amd => {
            if !zen2(c) && c.family < 0x19 {
                return Err(Rejected::BeforeZen2);
            }
            if c.amd8 & AMD_IBPB == 0 {
                return Err(Rejected::Ibpb);
            }
            if c.hypervisor && c.amd21 & LFENCE_SERIAL == 0 {
                return Err(Rejected::Lfence);
            }
            let patched19 = !c.hypervisor
                && c.family == 0x19
                && amd_buffer_revision(c.model, c.stepping).is_some_and(|r| c.microcode >= r);
            if c.amd21 & (IBPB_BRTYPE | SRSO_NO) == 0 && !(zen2(c) && !c.hypervisor) && !patched19 {
                return Err(Rejected::SrsoMicrocode);
            }
            if c.amd8 & AMD_IBPB_RET == 0 {
                p.entry |= RSB;
                // AutoIBRS clears or isolates returns at VM exit even when
                // L0 did not expose the separate IBPB_RET capability.
                if c.amd21 & AUTO_IBRS == 0 {
                    p.vmexit |= RSB;
                }
            }
            p.auto_ibrs = c.amd21 & AUTO_IBRS != 0;
            if c.amd8 & AMD_STIBP != 0 {
                p.spec_ctrl |= 2;
            } else {
                p.no_smt = true;
            }
            // Use one thread per physical core on SRSO-affected parts.
            // Do not rely on model-specific shared-BTB controls initially.
            p.no_smt |= c.amd21 & SRSO_NO == 0;
            // Only pre-19h bare metal has implicit TSA immunity. Affected
            // Zen 5 advertises VERW_CLEAR after updating microcode (AMD TSA
            // rev. 3.0, sections 1/6); do not exempt family 1Ah wholesale.
            p.buffers = c.amd21_ecx & TSA_NO != TSA_NO && !(zen2(c) && !c.hypervisor);
            if p.buffers && c.amd21 & VERW_CLEAR == 0 && !patched19 {
                return Err(Rejected::BufferMicrocode);
            }
        }
    }
    Ok(p)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn intel() -> Caps {
        Caps {
            vendor: Vendor::Intel,
            family: 6,
            model: 0x97,
            stepping: 2,
            hypervisor: false,
            microcode: 0,
            arch: RDCL_NO | IBRS_ALL | MDS_NO | TAA_NO | MMIO_NO | RFDS_NO,
            leaf7_edx: (1 << 26) | (1 << 27),
            leaf7_2_edx: 1 << 4,
            smep: true,
            rtm: false,
            amd8: 0,
            amd21: 0,
            amd21_ecx: 0,
        }
    }
    fn amd() -> Caps {
        Caps {
            vendor: Vendor::Amd,
            family: 0x17,
            model: 0x31,
            stepping: 0,
            hypervisor: false,
            microcode: 0x0830107b,
            arch: 0,
            leaf7_edx: 0,
            leaf7_2_edx: 0,
            smep: true,
            rtm: false,
            amd8: AMD_IBPB | AMD_STIBP,
            amd21: LFENCE_SERIAL,
            amd21_ecx: 0,
        }
    }

    #[test]
    fn meltdown_immunity_is_independent_of_ibrs_and_brand_generation() {
        let mut c = intel();
        c.arch &= !RDCL_NO;
        assert_eq!(select(&c), Err(Rejected::Meltdown));
        c.arch |= RDCL_NO;
        c.arch &= !IBRS_ALL;
        let p = select(&c).unwrap();
        assert_eq!(
            p.vmexit & (LEGACY_IBRS | IBPB | RSB),
            LEGACY_IBRS | IBPB | RSB
        );
        assert_ne!(p.entry & LEGACY_IBRS, 0);
        c.smep = false;
        assert_eq!(select(&c), Err(Rejected::Smep));
    }

    #[test]
    fn eibrs_keeps_ibpb_for_host_userspace_and_selects_pbrsb() {
        let mut c = intel();
        let p = select(&c).unwrap();
        assert_eq!(p.vmexit, IBPB | PBRSB | IBHF);
        assert_ne!(p.spec_ctrl & (1 << 10), 0);
        c.arch |= PBRSB_NO;
        assert_eq!(select(&c).unwrap().vmexit, IBPB | IBHF);
        c.arch |= BHI_NO;
        assert_eq!(select(&c).unwrap().spec_ctrl & (1 << 10), 0);
        c.leaf7_2_edx = 0;
        c.arch &= !BHI_NO;
        assert_ne!(select(&c).unwrap().entry & IBPB, 0);
        assert_ne!(select(&c).unwrap().entry & BHB, 0);
    }

    #[test]
    fn intel_its_checks_the_model_specific_microcode_stream() {
        let mut c = intel();
        for (model, stepping, minimum) in [
            (0x55, 7, 0x05003901),
            (0x55, 0xb, 0x07002b01),
            (0x8e, 0xc, 0x100),
            (0x9e, 0xd, 0x104),
            (0xa5, 2, 0x100),
            (0xa6, 0, 0x102),
            (0xa6, 1, 0x100),
            (0x8c, 1, 0xbc),
            (0x8c, 2, 0x3c),
        ] {
            c.model = model;
            c.stepping = stepping;
            c.microcode = minimum - 1;
            assert_eq!(select(&c), Err(Rejected::ItsMicrocode));
            c.microcode += 1;
            assert!(select(&c).is_ok());
        }
        c.hypervisor = true;
        c.microcode = 0;
        assert!(select(&c).is_ok()); // L0 implements advertised IBPB semantics.
    }

    #[test]
    fn intel_buffer_clear_and_smt_requirements_are_not_implied_by_rdcl_no() {
        let mut c = intel();
        c.arch &= !MDS_NO;
        assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
        c.leaf7_edx |= 1 << 10;
        let p = select(&c).unwrap();
        assert!(p.buffers && p.no_smt);
        c = intel();
        c.arch &= !RFDS_NO;
        assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
        c.arch |= RFDS_CLEAR;
        assert!(select(&c).unwrap().buffers);
        c = intel();
        c.model = 0xa5;
        c.stepping = 2;
        c.microcode = 0x100;
        c.arch &= !MMIO_NO;
        assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
        c.arch |= FB_CLEAR;
        let p = select(&c).unwrap();
        assert!(p.buffers && p.no_smt);
    }

    #[test]
    fn taa_needs_a_working_tsx_disable_control() {
        let mut c = intel();
        c.rtm = true;
        c.arch &= !TAA_NO;
        assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
        c.arch |= TSX_CTRL;
        assert!(select(&c).unwrap().disable_tsx);
    }

    #[test]
    fn intel_model_vulnerabilities_do_not_alias_other_families() {
        for model in [0x55, 0x97] {
            // MMIO and RFDS model lists respectively.
            let mut c = intel();
            c.model = model;
            c.arch = (c.arch | ITS_NO) & !(MMIO_NO | RFDS_NO);
            assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
            for family in [0x12, 0x13] {
                c.family = family;
                assert!(!select(&c).unwrap().buffers);
                c.hypervisor = true;
                // Nested CPUs still require explicit immunity or clearing.
                assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
                c.hypervisor = false;
            }
        }
    }

    #[test]
    fn implicit_fill_buffer_clearing_requires_mds_vulnerability() {
        for hypervisor in [false, true] {
            let mut c = intel();
            c.model = 0x86;
            c.hypervisor = hypervisor;
            c.arch &= !MMIO_NO;
            c.leaf7_edx |= (1 << 10) | (1 << 28);
            // MD_CLEAR + FLUSH_L1D alone does not promise VERW clears FB.
            assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
            c.arch &= !MDS_NO;
            assert!(select(&c).unwrap().buffers);
            c.leaf7_edx &= !(1 << 28);
            assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
            c.arch |= MDS_NO | FB_CLEAR;
            assert!(select(&c).unwrap().buffers);
        }
    }

    #[test]
    fn zen2_needs_ibpb_and_rap_stuffing_but_not_auto_ibrs() {
        let mut c = amd();
        let p = select(&c).unwrap();
        assert_eq!(p.vmexit, IBPB | RSB);
        assert_eq!(p.entry, IBPB | RSB);
        assert!(!p.auto_ibrs && !p.buffers && p.no_smt);
        assert_eq!(p.spec_ctrl, 2);
        for model in [0x01, 0x08, 0x20, 0x50, 0x5f] {
            c.model = model;
            assert_eq!(select(&c), Err(Rejected::BeforeZen2));
        }
        for model in [0x31, 0x47, 0x60, 0x68, 0x71, 0x90, 0xa0] {
            c.model = model;
            assert!(select(&c).is_ok());
        }
    }

    #[test]
    fn zen3_and_zen4_need_fixed_ibpb_and_buffer_clearing() {
        let mut c = amd();
        c.family = 0x19;
        for (model, stepping) in [(1, 1), (1, 2), (0x21, 0), (0x21, 2), (0x61, 2), (0xa0, 2)] {
            c.model = model;
            c.stepping = stepping;
            c.microcode = amd_buffer_revision(model, stepping).unwrap() - 1;
            assert_eq!(select(&c), Err(Rejected::SrsoMicrocode));
            c.microcode += 1;
            let p = select(&c).unwrap();
            assert!(p.buffers);
            assert_eq!(p.vmexit, IBPB | RSB);
        }
        c.amd21 |= AUTO_IBRS;
        assert_eq!(select(&c).unwrap().vmexit, IBPB);
        c.amd8 |= AMD_IBPB_RET;
        let p = select(&c).unwrap();
        assert!(p.auto_ibrs);
        assert_eq!(p.vmexit, IBPB);
        c.microcode = 0;
        assert_eq!(select(&c), Err(Rejected::SrsoMicrocode)); // AutoIBRS is insufficient.
    }

    #[test]
    fn nested_amd_uses_capabilities_not_masked_family_or_patch_level() {
        let mut c = amd();
        c.hypervisor = true;
        assert_eq!(select(&c), Err(Rejected::SrsoMicrocode));
        c.amd21 |= IBPB_BRTYPE;
        assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
        c.amd21 |= VERW_CLEAR;
        assert!(select(&c).unwrap().buffers);
        c.amd21 &= !VERW_CLEAR;
        c.amd21_ecx = TSA_NO;
        assert!(!select(&c).unwrap().buffers);
        c.amd21 &= !LFENCE_SERIAL;
        assert_eq!(select(&c), Err(Rejected::Lfence));
    }

    #[test]
    fn modern_amd_capabilities_allow_hardware_return_protection_and_smt() {
        let mut c = amd();
        c.family = 0x1a;
        c.amd21 |= AUTO_IBRS | SRSO_NO | VERW_CLEAR;
        c.amd8 |= AMD_IBPB_RET;
        let p = select(&c).unwrap();
        assert_eq!(p.vmexit, IBPB);
        assert!(p.auto_ibrs && p.buffers && !p.no_smt);
        c.amd8 &= !AMD_STIBP;
        assert!(select(&c).unwrap().no_smt);
        c.amd8 |= AMD_STIBP;
        c.amd21 = (c.amd21 & !SRSO_NO) | IBPB_BRTYPE;
        assert!(select(&c).unwrap().no_smt); // Deliberate conservative SMT policy.
    }

    #[test]
    fn bare_metal_zen5_needs_the_tsa_microcode_capability() {
        let mut c = amd();
        c.family = 0x1a;
        c.amd21 |= AUTO_IBRS | IBPB_BRTYPE;
        c.microcode = u32::MAX; // A synthetic revision is not VERW_CLEAR.
        for model in [0x02, 0x24, 0x44, 0x60, 0x70] {
            c.model = model;
            c.amd21 &= !VERW_CLEAR;
            assert_eq!(c.amd21_ecx, 0);
            assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
            c.amd21 |= VERW_CLEAR; // Enumerated by updated Zen 5 hardware.
            assert!(select(&c).unwrap().buffers);
        }
    }

    #[test]
    fn tsa_sq_and_l1_immunity_does_not_imply_fill_immunity() {
        for hypervisor in [false, true] {
            let mut c = amd();
            c.family = 0x1a;
            c.hypervisor = hypervisor;
            c.amd21 |= SRSO_NO;
            c.amd21_ecx = TSA_SQ_NO | TSA_L1_NO;
            assert_eq!(select(&c), Err(Rejected::BufferMicrocode));
            c.amd21 |= VERW_CLEAR;
            assert!(select(&c).unwrap().buffers);
            c.amd21 &= !VERW_CLEAR;
            c.amd21_ecx |= TSA_FILL_NO;
            assert!(!select(&c).unwrap().buffers);
        }
    }

    #[test]
    fn missing_ibpb_never_falls_back_to_unprotected_execution() {
        let mut c = amd();
        c.amd8 &= !AMD_IBPB;
        assert_eq!(select(&c), Err(Rejected::Ibpb));
        c = intel();
        c.leaf7_edx &= !(1 << 26);
        assert_eq!(select(&c), Err(Rejected::Ibpb));
    }
}
