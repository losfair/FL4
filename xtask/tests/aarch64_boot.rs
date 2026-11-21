//! The AArch64 kernel's boot-time decisions on the host: its memory lists
//! (fl4-kernel-aarch64 bootmem.rs), its ACPI parsing (hw.rs, over
//! host-allocated tables), the GIC layout arithmetic and the cores'
//! capability check (fl4-arch-aarch64 gic_layout.rs, ap_caps.rs). Only the window, the console
//! and the boot core's MPIDR are replaced.
extern crate self as fl4_core;
extern crate self as fl4_arch_aarch64;

pub mod boot {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Region {
        pub start: u64,
        pub end: u64,
    }
    impl Region {
        pub const EMPTY: Region = Region { start: 0, end: 0 };
    }
}

/// Physical memory: a host buffer (`MEMORY`: its address and length), so
/// tables hold small physical addresses (an RSDT's are 32 bits).
pub mod layout {
    use std::cell::Cell;
    thread_local! {
        pub static MEMORY: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
    }
    pub fn pptr(p: u64) -> u64 {
        let (base, len) = MEMORY.get();
        assert!(p < len, "read outside physical memory: {p:#x}");
        base + p
    }
}

/// The window maps all of the buffer.
pub mod mmu {
    pub fn in_window(start: u64, len: u64) -> bool {
        start.checked_add(len).is_some_and(|end| end <= super::layout::MEMORY.get().1)
    }
}

pub mod serial {
    pub const KIND_NONE: u64 = 0;
    pub const KIND_PL011: u64 = 1;
    pub const KIND_16550: u64 = 2;
}

pub mod smp {
    pub const PSCI_NONE: u64 = 0;
    pub const PSCI_SMC: u64 = 1;
    pub const PSCI_HVC: u64 = 2;
}

pub mod cpu {
    pub fn mpidr() -> u64 {
        0
    }
}

#[path = "../../crates/fl4-arch-aarch64/src/gic_layout.rs"]
pub mod gic_layout;
#[path = "../../crates/fl4-arch-aarch64/src/el0_access.rs"]
mod el0_access;
#[path = "../../crates/fl4-arch-aarch64/src/ap_caps.rs"]
mod ap_caps;
#[allow(dead_code)]
#[path = "../../crates/fl4-kernel-aarch64/src/bootmem.rs"]
mod bootmem;
#[allow(dead_code)]
#[path = "../../crates/fl4-kernel-aarch64/src/hw.rs"]
mod hw;
#[path = "../../crates/fl4-efi/src/efi_mmap.rs"]
mod efi_mmap;
#[path = "../../crates/fl4-kernel-aarch64/src/extra_bi.rs"]
mod extra_bi;

// ---- GIC ---------------------------------------------------------------------

#[test]
fn the_distributor_never_touches_the_special_intids() {
    assert_eq!(gic_layout::dist_lines(0), 32);
    assert_eq!(gic_layout::dist_lines(2), 96);
    assert_eq!(gic_layout::dist_lines(30), 992);
    // ITLinesNumber 31: 1024 lines, of which 1020..1023 are special.
    assert_eq!(gic_layout::dist_lines(31), 1020);
    assert_eq!(gic_layout::dist_lines(0xffff_ffff), 1020);
    assert_eq!(gic_layout::bank_bits(960, 1020), u32::MAX);
    assert_eq!(gic_layout::bank_bits(992, 1020), 0x0fff_ffff);
    assert_eq!(gic_layout::bank_bits(32, 64), u32::MAX);
    assert_eq!(gic_layout::bank_bits(64, 64), 0);
    // The registers init_dist writes stay inside the defined ones:
    // IPRIORITYR/ITARGETSR up to n = 254, IROUTER up to n = 1019.
    let lines = gic_layout::dist_lines(31);
    assert!((32..lines).step_by(4).all(|i| i / 4 <= 254));
    assert!((32..lines).all(|i| i <= 1019));
}

#[test]
fn gicv2_spis_go_to_the_boot_cores_interface() {
    assert_eq!(gic_layout::v2_targets(0x0404_0404), 0x0404_0404);
    assert_eq!(gic_layout::v2_targets(0x0000_0080), 0x8080_8080);
    // A uniprocessor GIC reads zero.
    assert_eq!(gic_layout::v2_targets(0), 0x0101_0101);
}

/// Audit round 5 F5: SGIs only reach cores a target list can name. GICv2
/// has eight CPU interfaces; a core reading no interface (or several, or
/// another core's) would never answer a remote call. GICv3 names Aff0 16
/// and more only with the range selector, which both the distributor and
/// the sending CPU interface must support.
#[test]
fn sgis_only_go_to_cores_a_target_list_can_name() {
    assert_eq!(gic_layout::v2_interface(0x0404_0404), 4);
    assert_eq!(gic_layout::v2_interface(0), 0);
    assert!(gic_layout::v2_interface_ok(1, []));
    assert!(gic_layout::v2_interface_ok(0x80, [1, 2, 4]));
    assert!(!gic_layout::v2_interface_ok(0, []), "no interface");
    assert!(!gic_layout::v2_interface_ok(3, []), "two interfaces");
    assert!(!gic_layout::v2_interface_ok(0x100, []), "a ninth interface");
    assert!(!gic_layout::v2_interface_ok(2, [1, 2]), "another core's interface");
    assert_eq!(gic_layout::V2_INTERFACES, 8);
    let typer_rss = 1 << 26;
    let ctlr_rss = 1 << 18;
    assert!(gic_layout::v3_rss(typer_rss, ctlr_rss));
    assert!(!gic_layout::v3_rss(typer_rss, 0));
    assert!(!gic_layout::v3_rss(0, ctlr_rss));
    assert!(!gic_layout::v3_rss(!typer_rss, !ctlr_rss));
    assert!(gic_layout::v3_sgi_reaches(0, false));
    assert!(gic_layout::v3_sgi_reaches(15, false));
    assert!(!gic_layout::v3_sgi_reaches(16, false), "would reach Aff0 0");
    assert!(!gic_layout::v3_sgi_reaches(0xff, false));
    assert!(gic_layout::v3_sgi_reaches(16, true));
    assert!(gic_layout::v3_sgi_reaches(0xff, true));
}

/// GICR_TYPER values at frame addresses.
fn frames(list: &[(u64, u64)]) -> impl Fn(u64) -> u64 + '_ {
    move |a| list.iter().find(|f| f.0 == a).map(|f| f.1).unwrap_or_else(|| panic!("read of an unknown frame {a:#x}"))
}

const VLPIS: u64 = 1 << 1;
const LAST: u64 = 1 << 4;

#[test]
fn redistributors_are_found_only_inside_their_mapping() {
    let b = 0x800_0000;
    let t = [(b, 0 << 32), (b + 0x2_0000, 1 << 32), (b + 0x4_0000, 2 << 32 | LAST)];
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 1, frames(&t)), Some(b + 0x2_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 2, frames(&t)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 3, frames(&t)), None);
    // A mapping that ends inside the third frame: never that one, and its
    // GICR_TYPER is not read (`frames` would panic).
    assert_eq!(gic_layout::find_frame(b, 0x5_0000, 2, frames(&t)), None);
    assert_eq!(gic_layout::find_frame(b, 0x1_0000, 0, frames(&t)), None);
    assert_eq!(gic_layout::find_frame(b, 0, 0, frames(&t)), None);
    // GICv4: 256 KiB per redistributor.
    let v4 = [(b, 0 << 32 | VLPIS), (b + 0x4_0000, 1 << 32 | VLPIS | LAST)];
    assert_eq!(gic_layout::find_frame(b, 0x8_0000, 1, frames(&v4)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 1, frames(&v4)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(u64::MAX - 0xffff, 0x1_0000, 0, frames(&[])), None);
}

#[test]
fn a_gicv4_redistributor_reserves_its_vlpi_frames() {
    let b = 0x800_0000;
    // A MADT GICC entry's range: one core's RD and SGI frames.
    assert_eq!(gic_layout::span(b, 0x2_0000, frames(&[(b, VLPIS)])), 0x4_0000);
    assert_eq!(gic_layout::span(b, 0x2_0000, frames(&[(b, 0)])), 0x2_0000);
    // A GICR range: all of it, the last frame's VLPI frames included.
    let v4 = [(b, VLPIS), (b + 0x4_0000, VLPIS | LAST)];
    assert_eq!(gic_layout::span(b, 0x8_0000, frames(&v4)), 0x8_0000);
    assert_eq!(gic_layout::span(b, 0x1_0000, frames(&v4)), 0);
}

// ---- cache maintenance ------------------------------------------------------------

/// Audit F1: on GICv2 another core's SGIs and PPIs (IDs 0..31) are banked
/// in its own CPU interface's view of the distributor, so masking,
/// unmasking or configuring one from here takes a remote call (an IRQ
/// handler deleted on core 0 for core 1's PPI must mask it on core 1).
/// This core's, every GICv3 one (the redistributors) and SPIs are direct.
#[test]
fn another_cores_gicv2_banked_interrupts_take_a_remote_call() {
    for id in [0, 15, 16, 27, 31] {
        assert!(gic_layout::banked_remote(false, id, 1, 0), "id {id}");
        assert!(gic_layout::banked_remote(false, id, 0, 3), "id {id}");
        assert!(!gic_layout::banked_remote(false, id, 2, 2), "id {id}");
        assert!(!gic_layout::banked_remote(true, id, 1, 0), "id {id}");
    }
    for id in [32, 33, 1019] {
        assert!(!gic_layout::banked_remote(false, id, 1, 0), "id {id}");
        assert!(!gic_layout::banked_remote(true, id, 1, 0), "id {id}");
    }
}

// ---- EL0 access to per-core registers (audit F3) -------------------------------

#[test]
fn el0_debug_channel_and_trace_registers_trap() {
    // MDSCR_EL1.TDCC; no debug events (MDE, KDE, SS clear).
    assert_eq!(el0_access::MDSCR_EL1, 1 << 12);
    // CPACR_EL1.TTA in both FP/SIMD states, which differ only in FPEN.
    for v in [el0_access::CPACR_FP_EL0_TRAP, el0_access::CPACR_FP_NONE] {
        assert_ne!(v & (1 << 28), 0, "{v:#x}");
        // SVE and SME stay trapped (ZEN, SMEN clear).
        assert_eq!(v & (3 << 16 | 3 << 24), 0, "{v:#x}");
    }
    assert_eq!((el0_access::CPACR_FP_EL0_TRAP >> 20) & 3, 1);
    assert_eq!((el0_access::CPACR_FP_NONE >> 20) & 3, 3);
}

/// Audit F5: a core runs beside the boot core only with 16-bit ASIDs and
/// the boot core's access-flag management, PAN, at least its physical
/// address size, and its counter frequency.
#[test]
fn an_application_processor_must_match_the_boot_core() {
    let bsp = ap_caps::Caps { asid16: true, hw_af: true, pan: true, pa_bits: 40, cntfrq: 62_500_000 };
    assert!(ap_caps::ap_matches(&bsp, &bsp));
    assert!(ap_caps::ap_matches(&bsp, &ap_caps::Caps { pa_bits: 48, ..bsp }));
    for ap in [
        ap_caps::Caps { asid16: false, ..bsp },
        ap_caps::Caps { hw_af: false, ..bsp },
        ap_caps::Caps { pan: false, ..bsp },
        ap_caps::Caps { pa_bits: 36, ..bsp },
        ap_caps::Caps { cntfrq: 24_000_000, ..bsp },
        ap_caps::Caps { cntfrq: 0, ..bsp },
    ] {
        assert!(!ap_caps::ap_matches(&bsp, &ap), "{ap:?}");
    }
    // Nor a core with what the boot core lacks: the kernel set up neither.
    let plain = ap_caps::Caps { hw_af: false, pan: false, ..bsp };
    assert!(!ap_caps::ap_matches(&plain, &bsp));
    assert!(!ap_caps::ap_matches(&ap_caps::Caps { cntfrq: 0, ..bsp }, &ap_caps::Caps { cntfrq: 0, ..bsp }));
}

/// Audit F5: EL2 set-up reads PMCR_EL0 only with an architected PMU, as
/// `el0_access::has_pmu` decides: PMUVer 0xf (IMPLEMENTATION DEFINED) has
/// no PMCR_EL0, and reading it there traps before any vector is set.
#[test]
fn el2_setup_reads_pmcr_only_with_an_architected_pmu() {
    let boot = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
    let at = boot.find("mrs     x9, pmcr_el0").expect("PMCR_EL0 read");
    let before: Vec<&str> = boot[..at].lines().rev().skip(1).take(4).map(|l| l.split("/*").next().unwrap().trim()).collect();
    assert_eq!(before, ["b.eq    4f", "cmp     x9, #0xf", "cbz     x9, 4f", "ubfx    x9, x9, #8, #4"]);
}

/// The pointer authentication key registers, APIAKeyLo_EL1 to
/// APGAKeyHi_EL1.
const PAUTH_KEYS: [&str; 10] = ["s3_0_c2_c1_0", "s3_0_c2_c1_1", "s3_0_c2_c1_2", "s3_0_c2_c1_3", "s3_0_c2_c2_0",
    "s3_0_c2_c2_1", "s3_0_c2_c2_2", "s3_0_c2_c2_3", "s3_0_c2_c3_0", "s3_0_c2_c3_1"];

/// `fl4_el_setup` as written in boot.S, comments left out and labels on
/// lines of their own ("7:").
fn el_setup_lines() -> Vec<String> {
    let boot = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
    let at = boot.find("\nfl4_el_setup:\n").expect("fl4_el_setup") + "\nfl4_el_setup:\n".len();
    let end = boot[at..].find("\n\n").map_or(boot.len(), |e| at + e);
    let mut out = vec![];
    let mut comment = false;
    for l in boot[at..end].lines() {
        let mut l = l.to_string();
        if comment {
            match l.find("*/") {
                Some(e) => { l = l[e + 2..].to_string(); comment = false; }
                None => continue,
            }
        }
        while let Some(b) = l.find("/*") {
            match l[b..].find("*/") {
                Some(e) => l.replace_range(b..b + e + 2, ""),
                None => { comment = true; l.truncate(b); }
            }
        }
        let mut l = l.trim().to_string();
        if let Some((n, rest)) = l.split_once(':') {
            if !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()) {
                out.push(format!("{n}:"));
                l = rest.trim().to_string();
            }
        }
        if !l.is_empty() {
            out.push(l.split_whitespace().collect::<Vec<_>>().join(" "));
        }
    }
    out
}

/// A constant of boot.S: a number, an `.equ` name or `(a << b)`.
fn boot_const(e: &str) -> u64 {
    let e = e.trim().trim_start_matches('(').trim_end_matches(')').trim();
    if let Some((a, b)) = e.split_once("<<") {
        return boot_const(a) << boot_const(b);
    }
    if let Some(h) = e.strip_prefix("0x") {
        return u64::from_str_radix(h, 16).unwrap();
    }
    if let Ok(v) = e.parse() {
        return v;
    }
    let boot = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
    let def = boot.lines().find_map(|l| l.strip_prefix(".equ ").and_then(|d| d.split_once(',')).filter(|(n, _)| n.trim() == e));
    boot_const(def.unwrap_or_else(|| panic!("unknown constant {e}")).1)
}

/// Run `fl4_el_setup` on a core entering it at `el` (1 or 2; at 2 with
/// HCR_EL2.E2H as `e2h`), whose ID_AA64ISAR1_EL1 and ID_AA64ISAR2_EL1 are
/// `isar1` and `isar2` and whose other ID registers read zero. Returns the
/// system registers written, with the EL each was written at and the value.
/// Panics on what would trap or be UNDEFINED: a key register access
/// without FEAT_PAuth, one at EL1 entered from EL2 before HCR_EL2.APK is
/// set, or any EL2 register access from a core entered at EL1.
fn run_el_setup(el: u64, e2h: bool, isar1: u64, isar2: u64) -> Vec<(u64, String, u64)> {
    let c = el_setup_lines();
    let entry_el = el;
    let mut el = el;
    let pauth = (isar1 & 0xff0) | (isar2 & 0xf000) != 0;
    let mut x: std::collections::HashMap<String, u64> = Default::default();
    let mut hcr = (e2h as u64) << 34;
    let mut elr = None;
    let mut flags = (0u64, 0u64);
    let mut writes = vec![];
    let label = |pc: usize, t: &str| -> usize {
        let (n, dir) = t.split_at(t.len() - 1);
        let l = format!("{n}:");
        match dir {
            "f" => pc + c[pc..].iter().position(|x| *x == l).unwrap_or_else(|| panic!("no {l} after {pc}")),
            "b" => c[..pc].iter().rposition(|x| *x == l).unwrap_or_else(|| panic!("no {l} before {pc}")),
            _ => panic!("branch to {t}"),
        }
    };
    let el2_reg = |r: &str| r.ends_with("_el2") || r.starts_with("s3_4_");
    let mut pc = 0;
    for _ in 0..10_000 {
        let l = c[pc].clone();
        pc += 1;
        if l.ends_with(':') {
            continue;
        }
        let (op, args) = l.split_once(' ').unwrap_or((&l, ""));
        let a: Vec<&str> = args.split(", ").collect();
        let get = |x: &std::collections::HashMap<String, u64>, o: &str| -> u64 {
            match o.strip_prefix('#') {
                Some(imm) => boot_const(imm),
                None if o == "xzr" => 0,
                None => *x.get(o).unwrap_or_else(|| panic!("{o} read before it is written: {l}")),
            }
        };
        match op {
            "isb" => {}
            "mrs" => {
                let r = a[1].to_ascii_lowercase();
                assert!(!(entry_el == 1 && el2_reg(&r)), "EL2 register read at EL1: {l}");
                let v = match r.as_str() {
                    "currentel" => el << 2,
                    "hcr_el2" => hcr,
                    "id_aa64isar1_el1" => isar1,
                    "s3_0_c0_c6_2" => isar2,
                    _ => 0,
                };
                x.insert(a[0].into(), v);
            }
            "msr" => {
                let r = a[0].to_ascii_lowercase();
                let v = get(&x, a[1]);
                assert!(!(entry_el == 1 && el2_reg(&r)), "EL2 register written at EL1: {l}");
                if PAUTH_KEYS.contains(&r.as_str()) {
                    assert!(pauth, "key register written without FEAT_PAuth (UNDEFINED): {l}");
                    assert!(entry_el == 1 || hcr & (1 << 40) != 0, "key written before HCR_EL2.APK: {l}");
                }
                match r.as_str() {
                    // E2H fixed at 1 (no FEAT_E2H0) stays 1.
                    "hcr_el2" => hcr = v | (e2h as u64) << 34,
                    "elr_el2" => elr = Some(v),
                    _ => {}
                }
                writes.push((el, r, v));
            }
            "mov" => { let v = get(&x, a[1]); x.insert(a[0].into(), v); }
            "ldr" => { x.insert(a[0].into(), boot_const(a[1].strip_prefix('=').expect("literal load"))); }
            "adr" => {
                let v = if a[1].ends_with('f') || a[1].ends_with('b') { 0x1_0000_0000 + label(pc, a[1]) as u64 } else { 0xadd0_0000 };
                x.insert(a[0].into(), v);
            }
            "lsr" => { let v = get(&x, a[1]) >> get(&x, a[2]); x.insert(a[0].into(), v); }
            "and" => { let v = get(&x, a[1]) & get(&x, a[2]); x.insert(a[0].into(), v); }
            "orr" => { let v = get(&x, a[1]) | get(&x, a[2]); x.insert(a[0].into(), v); }
            "ubfx" => {
                let (lsb, w) = (get(&x, a[2]), get(&x, a[3]));
                let v = (get(&x, a[1]) >> lsb) & ((1 << w) - 1);
                x.insert(a[0].into(), v);
            }
            "cmp" => flags = (get(&x, a[0]), get(&x, a[1])),
            "b.ne" | "b.eq" | "b.lo" => {
                let take = match op { "b.ne" => flags.0 != flags.1, "b.eq" => flags.0 == flags.1, _ => flags.0 < flags.1 };
                if take { pc = label(pc, a[0]); }
            }
            "b" => pc = label(pc, a[0]),
            "cbz" => if get(&x, a[0]) == 0 { pc = label(pc, a[1]); },
            "tbz" | "tbnz" => {
                let set = get(&x, a[0]) >> get(&x, a[1]) & 1 != 0;
                if set == (op == "tbnz") { pc = label(pc, a[2]); }
            }
            "eret" => {
                assert_eq!(el, 2, "eret at EL1");
                el = 1;
                pc = (elr.expect("ELR_EL2 set before eret") - 0x1_0000_0000) as usize;
            }
            "ret" => {
                assert_eq!(el, 1, "returns at EL{el}");
                return writes;
            }
            _ => panic!("the model has no {l}"),
        }
    }
    panic!("fl4_el_setup does not return");
}

/// The pointer authentication ID fields: (ISAR1 bits, ISAR2 bits) of APA,
/// API, GPA, GPI, APA3 and GPA3, each set or clear, with every other field
/// of the two registers set.
fn pauth_id_combinations() -> Vec<(u64, u64)> {
    let fields = [(1u64 << 4, 0u64), (1 << 8, 0), (1 << 24, 0), (1 << 28, 0), (0, 1 << 12), (0, 1 << 8)];
    (0..64u32).map(|m| {
        let (mut i1, mut i2) = (0x00f0_000f_u64 | 0xffff_ffff_0000_0000, 0xffff_ffff_ffff_00ff_u64);
        for (b, f) in fields.iter().enumerate() {
            if m & (1 << b) != 0 {
                i1 |= f.0;
                i2 |= f.1;
            }
        }
        (i1, i2)
    }).collect()
}

/// Audit r10 F3: every core clears all ten pointer authentication keys
/// whenever it has FEAT_PAuth (APA, API or APA3), entered at EL1 as at EL2,
/// and writes none without it (an UNDEFINED access). Before, a core entered
/// at EL1 (QEMU's default, KVM and cloud guests) skipped the clearing and
/// kept the firmware's keys, which PACGA, enabled by no SCTLR_EL1 bit, lets
/// EL0 compute with. From EL2, HCR_EL2.{APK,API} are set for any of the six
/// fields before any key is written (`run_el_setup` checks the order).
#[test]
fn pauth_keys_are_cleared_on_every_entry() {
    for (isar1, isar2) in pauth_id_combinations() {
        let feat = (isar1 & 0xff0) | (isar2 & 0xf000) != 0;
        let any = (isar1 & 0xff00_0ff0) | (isar2 & 0xff00) != 0;
        for (el, e2h) in [(1, false), (2, false), (2, true)] {
            let w = run_el_setup(el, e2h, isar1, isar2);
            let keys: Vec<&(u64, String, u64)> = w.iter().filter(|(_, r, _)| PAUTH_KEYS.contains(&r.as_str())).collect();
            let what = format!("EL{el} e2h {e2h} isar1 {isar1:#x} isar2 {isar2:#x}");
            if feat {
                assert_eq!(keys.iter().map(|k| k.1.as_str()).collect::<Vec<_>>(), PAUTH_KEYS, "{what}");
                assert!(keys.iter().all(|k| k.0 == 1 && k.2 == 0), "{what}");
            } else {
                assert!(keys.is_empty(), "{what}");
            }
            if el == 2 {
                let hcr: Vec<u64> = w.iter().filter(|(_, r, _)| r == "hcr_el2").map(|w| w.2).collect();
                assert_eq!(hcr, [1 << 31 | if any { 3 << 40 } else { 0 }], "{what}");
            }
        }
    }
}

/// The code of `label` in boot.S, up to the next blank line, comments and
/// labels' own lines left out.
fn boot_code(label: &str) -> Vec<String> {
    let boot = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
    let at = boot.find(&format!("\n{label}:\n")).unwrap_or_else(|| panic!("{label} not found")) + label.len() + 3;
    let end = boot[at..].find("\n\n").map_or(boot.len(), |e| at + e);
    let mut out = vec![];
    let mut comment = false;
    for l in boot[at..end].lines() {
        let mut l = l.to_string();
        if comment {
            match l.find("*/") {
                Some(e) => { l = l[e + 2..].to_string(); comment = false; }
                None => continue,
            }
        }
        if let Some(b) = l.find("/*") {
            comment = !l[b..].contains("*/");
            l.truncate(b);
        }
        let l = l.trim();
        let l = match l.split_once(':') { Some((n, rest)) if n.chars().all(|c| c.is_ascii_digit()) => rest.trim(), _ => l };
        if !l.is_empty() {
            out.push(l.to_string());
        }
    }
    out
}

/// Audit r7 F1: at EL2, the first thing `fl4_el_setup` does is point
/// VBAR_EL2 at FL4's own vectors, before any register access that could
/// trap (the firmware's VBAR_EL2 lies in memory that becomes user RAM).
/// With pointer authentication HCR_EL2 gets API and APK (PACGA has no
/// SCTLR_EL1 enable: with API clear it traps from EL0 to EL2) and every key
/// is cleared; the fine-grained trap registers and HCRX_EL2 are cleared
/// when implemented. Audit r9 F1: the keys only with FEAT_PAuth (APA, API
/// or APA3), the one condition under which any key register exists.
#[test]
fn el2_setup_leaves_nothing_trapping_to_el2() {
    let c = boot_code("fl4_el_setup");
    let el2 = c.iter().position(|l| l == "b.ne    1f").expect("EL check");
    assert_eq!(&c[el2 + 1..el2 + 4], ["adr     x9, fl4_el2_vectors", "msr     vbar_el2, x9", "isb"]);
    let has = |l: &str| c.iter().any(|x| x == l);
    assert!(has("orr     x9, x9, #(3 << 40)"));
    // HCR_EL2.{APK,API} and the keys for each combination of the pointer
    // authentication ID fields: `pauth_keys_are_cleared_on_every_entry`.
    for r in ["s3_4_c1_c1_4", "s3_4_c1_c1_5", "s3_4_c1_c1_6", "s3_4_c3_c1_4", "s3_4_c3_c1_5", "s3_4_c3_c1_6",
        "s3_4_c3_c1_0", "s3_4_c3_c1_1", "s3_4_c3_c1_2", "s3_4_c3_c1_3", "s3_4_c3_c1_7", "s3_4_c1_c2_2"] {
        assert!(has(&format!("msr     {r}, xzr")), "{r} not cleared");
    }
    // FEAT_FGT, FEAT_HCX and FEAT_AMU fields of the ID registers.
    assert!(has("ubfx    x10, x10, #56, #4") && has("ubfx    x10, x10, #40, #4") && has("ubfx    x11, x11, #44, #4"));
}

/// Audit r7 F1 (r8 F1 for E2H fixed at 1): FL4's EL2 vectors pass a synchronous exception from AArch64
/// EL0 on to EL1 as an Undefined Instruction exception, and stop the core
/// on anything else; nothing at EL2 runs outside the kernel image.
#[test]
fn el2_vectors_reflect_el0_traps_and_halt_on_the_rest() {
    let boot = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
    let at = boot.find("fl4_el2_vectors:").unwrap();
    assert_eq!(boot[..at].lines().next_back().unwrap().trim(), ".balign 2048");
    let v = boot_code("fl4_el2_vectors");
    assert_eq!(v, [".rept 8", "el2_halt", ".endr", ".balign 128", "b       fl4_el2_reflect", ".rept 7", "el2_halt", ".endr"]);
    assert!(boot.contains(".macro el2_halt\n    .balign 128\n    b       fl4_el2_halt\n.endm"));
    let r = boot_code("fl4_el2_reflect");
    assert_eq!(&r[..4], ["msr     tpidr_el2, x0", "mrs     x0, spsr_el2", "tst     x0, #0x1f", "b.ne    fl4_el2_halt"]);
    // The reflection itself, per HCR_EL2.E2H, is run by aarch64_vhe.rs.
    assert_eq!(&r[4..], [
        "mrs     x0, hcr_el2", "tbnz    x0, #34, 13f",
        "el2_reflect_to sctlr_el1, spsr_el1, elr_el1, esr_el1, vbar_el1",
        "el2_reflect_to s3_5_c1_c0_0, s3_5_c4_c0_0, s3_5_c4_c0_1, s3_5_c5_c2_0, s3_5_c12_c0_0",
    ]);
    assert_eq!(boot_code("fl4_el2_halt"), ["wfi", "b       fl4_el2_halt"]);
}

#[test]
fn pmuserenr_is_written_only_with_a_pmu() {
    // PMUVer: neither absent nor IMPLEMENTATION DEFINED.
    assert!(!el0_access::has_pmu(0));
    assert!(!el0_access::has_pmu(0xf << 8));
    assert!(el0_access::has_pmu(4 << 8));
}

/// An interrupt from EL0 records the thread's restart PC (FAULT_IP) before
/// it takes the interrupt: taking a remote-call SGI services a stall
/// (`take_irq` -> `service_remote` -> `fl4_core::smp::stall`), whose
/// acknowledgement lets the calling core restart, rewrite (TCB_WriteRegisters)
/// or delete the thread and retype its memory at once. After `take_irq`,
/// `fl4_entry` must not touch the thread it read before (x86_64 entry.rs
/// likewise saves the user state before `service_remote`).
#[test]
fn an_el0_interrupt_saves_the_restart_pc_before_it_can_be_stalled() {
    let entry = include_str!("../../crates/fl4-kernel-aarch64/src/entry.rs");
    let code: Vec<&str> = entry.lines().map(|l| l.split("//").next().unwrap()).collect();
    let start = code.iter().position(|l| l.contains("fn fl4_entry(")).expect("fl4_entry");
    let irq = start + code[start..].iter().position(|l| l.trim() == "if kind == KIND_IRQ {").expect("IRQ branch");
    let end = irq + code[irq..].iter().position(|l| l.trim() == "exit()").expect("end of the IRQ branch");
    let branch = &code[start..=end];
    let take = branch.iter().position(|l| l.contains("take_irq()")).expect("take_irq in fl4_entry");
    let save = branch.iter().position(|l| l.contains("t.set_reg(s, reg::FAULT_IP, elr)")).expect("FAULT_IP save");
    assert!(save < take, "fl4_entry takes the interrupt (and services stalls) before it saves FAULT_IP");
    for l in &branch[take..] {
        let uses_t = l.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.')).any(|w| w.starts_with("t."));
        assert!(!uses_t, "fl4_entry touches the interrupted thread after take_irq: {}", l.trim());
    }
}

// ---- memory lists -----------------------------------------------------------------

#[test]
fn a_full_range_list_reports_what_it_lost() {
    let mut r = bootmem::Ranges::new();
    for i in 0..bootmem::MAX_RANGES as u64 {
        r.add(i * 0x2000, i * 0x2000 + 0x1000);
    }
    assert!(!r.lost);
    assert_eq!(r.n, bootmem::MAX_RANGES);
    // One more disjoint range, at the top where fl4-efi puts the root task.
    r.add(1 << 40, (1 << 40) + 0x1000);
    assert!(r.lost);
    // And a split by `remove` of a full list.
    let mut r2 = bootmem::Ranges::new();
    for i in 0..bootmem::MAX_RANGES as u64 {
        r2.add(i * 0x4000, i * 0x4000 + 0x3000);
    }
    r2.remove(0x1000, 0x2000);
    assert!(r2.lost);
    // Every entry of the loader's largest memory map fits.
    assert!(bootmem::MAX_RANGES >= fl4_bootinfo::MAX_MMAP + 16);
}

#[test]
fn memory_map_entries_never_wrap() {
    assert_eq!(bootmem::entry_pages(0x1000, 0x3000, u64::MAX), Some((0x1000, 0x4000)));
    assert_eq!(bootmem::entry_pages(0x1800, 0x3000, u64::MAX), Some((0x2000, 0x4000)));
    assert_eq!(bootmem::entry_pages(0x1000, 0x3000, 0x2000), Some((0x1000, 0x2000)));
    assert_eq!(bootmem::entry_pages(u64::MAX - 0xfff, 0x2000, u64::MAX), None);
    assert_eq!(bootmem::entry_pages(0xffff_ffff_ffff_f001, 0x10, u64::MAX), None);
    assert_eq!(bootmem::entry_pages(0x1000, 0, u64::MAX), None);
}

/// The kernel's device area (paging.rs): from the top of the window
/// (fl4-core aarch64 `PPTR_TOP`) to the kernel image (`KERNEL_VBASE`).
const DEVICE_BASE: u64 = 0xffff_ff80_0000_0000;
const DEVICE_TOP: u64 = fl4_bootinfo::KERNEL_VBASE;

/// Audit r10 F1: a device mapping never wraps past 2^64 into the kernel
/// image. `device_pages` lets through any range below the physical address
/// top (up to 2^48), but from DEVICE_BASE only 512 GiB remain to 2^64:
/// before, `va + size` of a 512 GiB GICR range wrapped to 0, passed the
/// `<= DEVICE_TOP` check, and `map` remapped the kernel's own text and data
/// as device memory.
#[test]
fn device_mappings_never_wrap_past_the_device_area() {
    let paging = include_str!("../../crates/fl4-kernel-aarch64/src/paging.rs");
    assert!(paging.contains("const DEVICE_BASE: u64 = PPTR_TOP;") && paging.contains("const DEVICE_TOP: u64 = KERNEL_VBASE;"));
    assert!(paging.contains("crate::bootmem::device_va(s.next_device, size, DEVICE_TOP)"));
    let va = bootmem::device_va;
    // 512 GiB from the base ends exactly at 2^64; one page less than what
    // remains to 2^64; and everything to 2^64.
    assert_eq!(va(DEVICE_BASE, 0x80_0000_0000, DEVICE_TOP), None);
    assert_eq!(va(DEVICE_BASE, u64::MAX - DEVICE_BASE + 1, DEVICE_TOP), None);
    assert_eq!(va(DEVICE_BASE, u64::MAX - DEVICE_BASE, DEVICE_TOP), None);
    assert_eq!(va(DEVICE_BASE, 1 << 48, DEVICE_TOP), None);
    for size in [0x80_0000_1000, 0xff_ffff_f000, (1 << 48) - 0x1000] {
        assert_eq!(va(DEVICE_BASE + 0x1_0000, size, DEVICE_TOP), None, "{size:#x}");
    }
    // The whole area, and one page more.
    assert_eq!(va(DEVICE_BASE, DEVICE_TOP - DEVICE_BASE, DEVICE_TOP), Some((DEVICE_BASE, DEVICE_TOP)));
    assert_eq!(va(DEVICE_BASE, DEVICE_TOP - DEVICE_BASE + 0x1000, DEVICE_TOP), None);
    // Rounding up to 64 KiB near the top: what is left after it.
    let next = DEVICE_TOP - 0x2_0000 + 0x1000;
    assert_eq!(va(next, 0x1_0000, DEVICE_TOP), Some((DEVICE_TOP - 0x1_0000, DEVICE_TOP)));
    assert_eq!(va(next, 0x1_1000, DEVICE_TOP), None);
    assert_eq!(va(DEVICE_TOP, 0x1000, DEVICE_TOP), None);
    // A `next` the rounding would wrap.
    assert_eq!(va(u64::MAX - 0x1000, 0x1000, u64::MAX), None);
    // Ordinary mappings: 64 KiB aligned, each after the last.
    assert_eq!(va(DEVICE_BASE, 0x1000, DEVICE_TOP), Some((DEVICE_BASE, DEVICE_BASE + 0x1000)));
    assert_eq!(va(DEVICE_BASE + 0x1000, 0x2_0000, DEVICE_TOP), Some((DEVICE_BASE + 0x1_0000, DEVICE_BASE + 0x3_0000)));
    // Whatever was asked, an accepted mapping lies inside the area.
    for next in [DEVICE_BASE, DEVICE_BASE + 0x1234_5000, DEVICE_TOP - 0x10_0000, DEVICE_TOP] {
        for shift in 12..64 {
            for size in [1u64 << shift, (1u64 << shift) - 0x1000, (1u64 << shift).wrapping_add(0x1000)] {
                if let Some((v, end)) = va(next, size, DEVICE_TOP) {
                    assert!(v >= next && v % 0x1_0000 == 0 && end == v + size && end <= DEVICE_TOP, "{next:#x} {size:#x}");
                }
            }
        }
    }
}

/// Audit r7 F3: the console UART's pages kept from user space are the
/// pages `map_device` maps for it, a base inside a page included (two
/// pages); before, only the first page was kept and the second went to
/// user space as a device untyped the kernel also mapped.
#[test]
fn the_consoles_kept_pages_are_the_ones_it_maps() {
    let lib = include_str!("../../crates/fl4-kernel-aarch64/src/lib.rs");
    assert!(lib.contains("paging::map_device(h.uart_base, UART_MAP)"));
    assert!(lib.contains("keep(&mut dev_used, h.uart_base, h.uart_base.saturating_add(UART_MAP));"));
    assert!(lib.contains("const UART_MAP: u64 = 0x1000;"));
    assert!(!lib.contains("dev_used.add("), "a kernel device range kept other than by `keep`");
    let top = 1 << 40;
    for base in [0x900_0000u64, 0x900_0800, 0x900_0ffc, 0x900_0001, 0xfe21_5040] {
        let (pa, size) = bootmem::device_pages(base, 0x1000, top).unwrap();
        assert_eq!(bootmem::pages_covering(base, base + 0x1000), (pa, pa + size), "{base:#x}");
    }
    assert_eq!(bootmem::pages_covering(0x900_0800, 0x900_1800), (0x900_0000, 0x900_2000));
}

/// One EFI memory descriptor of `stride` bytes.
fn efi_desc(stride: usize, ty: u32, base: u64, pages: u64, attr: u64) -> Vec<u8> {
    let mut d = vec![0u8; stride];
    d[0..4].copy_from_slice(&ty.to_le_bytes());
    d[8..16].copy_from_slice(&base.to_le_bytes());
    d[24..32].copy_from_slice(&pages.to_le_bytes());
    d[32..40].copy_from_slice(&attr.to_le_bytes());
    d
}

/// Audit r7 F4: the AArch64 loader takes only a map of whole descriptors
/// (stride at least 40 bytes, size a multiple of it, as the x86_64 loader
/// requires), and no descriptor whose size or end passes 2^64: a wrapped
/// length would shrink a RAM region and the kernel would hand the rest out
/// as device memory. Before, stride 0 or below 40 read past the
/// descriptor, and `pages * PAGE` wrapped.
#[test]
fn the_efi_memory_map_is_whole_and_never_wraps() {
    use fl4_bootinfo::{mem, MemRegion};
    let mut out = [MemRegion::default(); 4];
    let wb = 8;
    // Merged: two FREE kinds back to back, then firmware memory.
    let mut map = efi_desc(48, 7, 0x4000_0000, 0x100, wb);
    map.extend(efi_desc(48, 4, 0x4010_0000, 0x10, wb));
    map.extend(efi_desc(48, 5, 0x4011_0000, 1, wb));
    assert_eq!(efi_mmap::regions(&map, 48, &mut out), Some(2));
    assert_eq!((out[0].base, out[0].len, out[0].kind, out[0].cacheable), (0x4000_0000, 0x110_000, mem::FREE, 1));
    assert_eq!((out[1].base, out[1].len, out[1].kind), (0x4011_0000, 0x1000, mem::FIRMWARE));
    // Not contiguous, or not of one cacheability: not merged.
    let mut map = efi_desc(40, 7, 0x4000_0000, 1, wb);
    map.extend(efi_desc(40, 7, 0x4000_2000, 1, wb));
    map.extend(efi_desc(40, 7, 0x4000_3000, 1, 0));
    assert_eq!(efi_mmap::regions(&map, 40, &mut out), Some(3));
    // Layout: a stride of 0, below 40, or not dividing the size.
    let one = efi_desc(48, 7, 0x4000_0000, 1, wb);
    assert_eq!(efi_mmap::regions(&one, 0, &mut out), None);
    assert_eq!(efi_mmap::regions(&one[..32], 32, &mut out), None);
    assert_eq!(efi_mmap::regions(&one[..47], 48, &mut out), None);
    assert_eq!(efi_mmap::regions(&one, 40, &mut out), None);
    assert_eq!(efi_mmap::regions(&[], 48, &mut out), Some(0));
    assert!(efi_mmap::layout_ok(96, 48) && !efi_mmap::layout_ok(96, 36) && !efi_mmap::layout_ok(100, 48));
    // Size or end past 2^64.
    assert_eq!(efi_mmap::regions(&efi_desc(48, 7, 0, 1 << 52, wb), 48, &mut out), None);
    assert_eq!(efi_mmap::regions(&efi_desc(48, 7, 0x1000, u64::MAX / 0x1000 + 1, wb), 48, &mut out), None);
    assert_eq!(efi_mmap::regions(&efi_desc(48, 7, u64::MAX - 0xfff, 2, wb), 48, &mut out), None);
    assert_eq!(efi_mmap::regions(&efi_desc(48, 7, u64::MAX - 0xfff, 1, wb), 48, &mut out), None);
    assert_eq!(efi_mmap::regions(&efi_desc(48, 7, u64::MAX - 0x1fff, 1, wb), 48, &mut out), Some(1));
    // More regions than the record holds.
    let mut map = vec![];
    for i in 0..5u64 {
        map.extend(efi_desc(40, 7, i * 0x2000, 1, wb));
    }
    assert_eq!(efi_mmap::regions(&map, 40, &mut out), None);
    assert_eq!(efi_mmap::regions(&map[..160], 40, &mut out), Some(4));
}

#[test]
fn device_mappings_stay_below_the_physical_address_size() {
    let top = 1 << 40;
    assert_eq!(bootmem::device_pages(0x900_0000, 0x1000, top), Some((0x900_0000, 0x1000)));
    assert_eq!(bootmem::device_pages(0x900_0800, 0x1000, top), Some((0x900_0000, 0x2000)));
    assert_eq!(bootmem::device_pages(top - 0x1000, 0x1000, top), Some((top - 0x1000, 0x1000)));
    assert_eq!(bootmem::device_pages(top - 0x1000, 0x1001, top), None);
    assert_eq!(bootmem::device_pages(1 << 52, 0x1000, top), None);
    assert_eq!(bootmem::device_pages(u64::MAX - 0xff, 0x1000, u64::MAX), None);
    assert_eq!(bootmem::device_pages(0x900_0000, 0, top), None);
}

// ---- ACPI -------------------------------------------------------------------------

fn checksum(table: &mut [u8], offset: usize) {
    table[offset] = 0;
    table[offset] = table.iter().fold(0u8, |sum, byte| sum.wrapping_add(*byte)).wrapping_neg();
}

/// A MADT GICC entry (type 0x0b, 80 bytes): enabled core `mpidr` with its
/// redistributor at `gicr`.
fn gicc(mpidr: u64, gicr: u64) -> Vec<u8> {
    let mut e = vec![0u8; 80];
    e[0] = 0x0b;
    e[1] = 80;
    e[12..16].copy_from_slice(&1u32.to_le_bytes());
    e[60..68].copy_from_slice(&gicr.to_le_bytes());
    e[68..76].copy_from_slice(&mpidr.to_le_bytes());
    e
}

/// A GICD entry (type 0x0c, 24 bytes), GICv3.
fn gicd() -> Vec<u8> {
    let mut e = vec![0u8; 24];
    e[0] = 0x0c;
    e[1] = 24;
    e[8..16].copy_from_slice(&0x800_0000u64.to_le_bytes());
    e[20] = 3;
    e
}

/// A GICR entry (type 0x0e, 16 bytes).
fn gicr(base: u64, len: u32) -> Vec<u8> {
    let mut e = vec![0u8; 16];
    e[0] = 0x0e;
    e[1] = 16;
    e[4..12].copy_from_slice(&base.to_le_bytes());
    e[12..16].copy_from_slice(&len.to_le_bytes());
    e
}

/// Where the tables are in physical memory.
const BASE: u64 = 0x1000;

struct Tables {
    mem: Vec<u8>,
}

impl Tables {
    fn rsdp(&self) -> u64 {
        layout::MEMORY.set((self.mem.as_ptr() as u64, self.mem.len() as u64));
        BASE
    }
    fn buf(&mut self) -> &mut [u8] {
        &mut self.mem[BASE as usize..]
    }
}

/// RSDP (at 0, revision `rev`), XSDT or RSDT (at 64) and a MADT of
/// `entries` (at 128), from physical `BASE` on.
fn tables(entries: &[u8], rev: u8, root_sig: &[u8; 4]) -> Tables {
    let mut mem = vec![0u8; BASE as usize + 128 + 44 + entries.len()];
    let buf = &mut mem[BASE as usize..];
    let base = BASE;
    let madt = &mut buf[128..];
    madt[44..].copy_from_slice(entries);
    let len = madt.len() as u32;
    madt[..4].copy_from_slice(b"APIC");
    madt[4..8].copy_from_slice(&len.to_le_bytes());
    checksum(madt, 9);
    let xsdt = root_sig == b"XSDT";
    let root_len = if xsdt { 44 } else { 40 };
    let root = &mut buf[64..64 + root_len];
    root[..4].copy_from_slice(root_sig);
    root[4..8].copy_from_slice(&(root_len as u32).to_le_bytes());
    if xsdt {
        root[36..44].copy_from_slice(&(base + 128).to_le_bytes());
    } else {
        root[36..40].copy_from_slice(&((base + 128) as u32).to_le_bytes());
    }
    checksum(root, 9);
    let rsdp = &mut buf[..36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = rev;
    if rev >= 2 {
        rsdp[20..24].copy_from_slice(&36u32.to_le_bytes());
        rsdp[24..32].copy_from_slice(&(base + 64).to_le_bytes());
    } else {
        rsdp[16..20].copy_from_slice(&((base + 64) as u32).to_le_bytes());
    }
    checksum(&mut rsdp[..20], 8);
    checksum(rsdp, 32);
    Tables { mem }
}

fn madt(entries: &[Vec<u8>]) -> Vec<u8> {
    entries.concat()
}

#[test]
fn every_cores_redistributor_is_kept_from_user_space() {
    // Sixteen cores, each with its redistributor in its GICC entry: all
    // sixteen ranges are recorded, so the kernel reserves all of them.
    let mut e = vec![gicd()];
    for c in 0..16u64 {
        e.push(gicc(c, 0x80a_0000 + c * 0x2_0000));
    }
    let t = tables(&madt(&e), 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI");
    assert_eq!(h.n_gicr, 16);
    assert!(!h.gicr_lost);
    for c in 0..16u64 {
        assert!(h.gicr[..h.n_gicr].contains(&(0x80a_0000 + c * 0x2_0000, 0x2_0000)), "core {c}");
    }
}

#[test]
fn redistributors_past_the_table_are_a_boot_failure() {
    let mut e = vec![gicd()];
    for c in 0..hw::MAX_GICR as u64 + 1 {
        e.push(gicr(0x1000_0000 + c * 0x10_0000, 0x2_0000));
    }
    let t = tables(&madt(&e), 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI");
    assert_eq!(h.n_gicr, hw::MAX_GICR);
    assert!(h.gicr_lost);
}

/// Audit round 5 F3: a MADT giving both a GICR discovery range and its
/// cores' GICC redistributors, in either order, records the discovery
/// range whole, once; the kernel then keeps all of it from user space.
#[test]
fn a_discovery_range_and_its_cores_redistributors_merge() {
    let b = 0x80a_0000u64;
    let len = 0xf6_0000u32;
    let cores = 100u64;
    let mut gicc_first = vec![gicd()];
    for c in 0..cores {
        gicc_first.push(gicc(c, b + (c % 0x7b) * 0x2_0000));
    }
    gicc_first.push(gicr(b, len));
    let mut gicr_first = vec![gicd(), gicr(b, len)];
    gicr_first.extend_from_slice(&gicc_first[1..cores as usize + 1]);
    for (name, e) in [("GICC first", gicc_first), ("GICR first", gicr_first)] {
        let t = tables(&madt(&e), 2, b"XSDT");
        let h = hw::discover(t.rsdp(), 0).expect("ACPI");
        assert!(!h.gicr_lost, "{name}");
        assert_eq!(&h.gicr[..h.n_gicr], &[(b, len as u64)], "{name}");
        // What boot reserves of it (`gic_layout::reserve`, as lib.rs runs
        // it on the recorded range): the whole discovery range.
        let last = b + len as u64 - 0x2_0000;
        let typer = |a: u64| if a == last { LAST } else { 0 };
        assert_eq!(gic_layout::reserve(b, len as u64, len as u64, typer), Some(len as u64), "{name}");
    }
}

#[test]
fn redistributor_ranges_merge_only_where_they_overlap() {
    let mut r = [(0u64, 0u64); 4];
    let mut n = 0;
    let add = |r: &mut [(u64, u64)], n: &mut usize, b, l| gic_layout::add_redistributors(r, n, b, l);
    // Adjacent ranges stay apart; an overlapping one joins both.
    assert!(add(&mut r, &mut n, 0x10_0000, 0x2_0000));
    assert!(add(&mut r, &mut n, 0x12_0000, 0x2_0000));
    assert_eq!(&r[..n], &[(0x10_0000, 0x2_0000), (0x12_0000, 0x2_0000)]);
    assert!(add(&mut r, &mut n, 0x11_0000, 0x2_0000));
    assert_eq!(&r[..n], &[(0x10_0000, 0x4_0000)]);
    // Contained: nothing new.
    assert!(add(&mut r, &mut n, 0x10_0000, 0x2_0000));
    assert_eq!(&r[..n], &[(0x10_0000, 0x4_0000)]);
    // A wider range from below swallows it.
    assert!(add(&mut r, &mut n, 0xf_0000, 0x10_0000));
    assert_eq!(&r[..n], &[(0xf_0000, 0x10_0000)]);
    // Unbounded ranges are deduplicated, never merged.
    assert!(add(&mut r, &mut n, 0xf_0000, 0));
    assert!(add(&mut r, &mut n, 0xf_0000, 0));
    assert_eq!(&r[..n], &[(0xf_0000, 0x10_0000), (0xf_0000, 0)]);
    // Address 0 and an end past the address space are not recorded.
    assert!(!add(&mut r, &mut n, 0, 0x2_0000));
    assert!(!add(&mut r, &mut n, u64::MAX - 0xffff, 0x2_0000));
    assert_eq!(n, 2);
    // Full: a range that overlaps still merges, a new one does not fit.
    assert!(add(&mut r, &mut n, 0x100_0000, 0x2_0000));
    assert!(add(&mut r, &mut n, 0x200_0000, 0x2_0000));
    assert!(add(&mut r, &mut n, 0x200_0000, 0x4_0000));
    assert!(!add(&mut r, &mut n, 0x300_0000, 0x2_0000));
    assert_eq!(n, 4);
}

#[test]
fn acpi_1_0_rsdps_use_the_rsdt_and_copy_20_bytes() {
    let e = madt(&[gicd(), gicc(0, 0x80a_0000)]);
    let mut t = tables(&e, 0, b"RSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI 1.0");
    assert_eq!(h.n_gicr, 1);
    assert!(h.rsdp[20..].iter().all(|&b| b == 0));
    assert_eq!(&h.rsdp[..20], &t.buf()[..20]);
}

#[test]
fn rsdp_extended_checksum_and_root_signature_are_checked() {
    let e = madt(&[gicd(), gicc(0, 0x80a_0000)]);
    // A revision 2 RSDP whose extended checksum fails: only its ACPI 1.0
    // part is used, and that points at no RSDT.
    let mut t = tables(&e, 2, b"XSDT");
    t.buf()[32] ^= 0xff;
    assert!(hw::discover(t.rsdp(), 0).is_none());
    // An XSDT pointer to something that is not an XSDT.
    let mut t = tables(&e, 2, b"XSDT");
    t.buf()[64..68].copy_from_slice(b"FACP");
    checksum(&mut t.buf()[64..108], 9);
    assert!(hw::discover(t.rsdp(), 0).is_none());
    // Both sound.
    let mut t = tables(&e, 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI 2.0");
    assert_eq!(&h.rsdp[..], &t.buf()[..36]);
}

// ---- device tree (audit F5) -----------------------------------------------------

/// A flattened device tree under construction.
#[derive(Default)]
struct Dtb {
    structs: Vec<u8>,
    strings: Vec<u8>,
}

impl Dtb {
    fn word(&mut self, w: u32) {
        self.structs.extend_from_slice(&w.to_be_bytes());
    }
    fn pad(&mut self) {
        while self.structs.len() % 4 != 0 {
            self.structs.push(0);
        }
    }
    fn begin(&mut self, name: &str) {
        self.word(1);
        self.structs.extend_from_slice(name.as_bytes());
        self.structs.push(0);
        self.pad();
    }
    fn end(&mut self) {
        self.word(2);
    }
    fn prop(&mut self, name: &str, val: &[u8]) {
        let off = self.strings.len() as u32;
        self.strings.extend_from_slice(name.as_bytes());
        self.strings.push(0);
        self.word(3);
        self.word(val.len() as u32);
        self.word(off);
        self.structs.extend_from_slice(val);
        self.pad();
    }
    fn prop_u32(&mut self, name: &str, v: u32) {
        self.prop(name, &v.to_be_bytes());
    }
    fn prop_str(&mut self, name: &str, v: &str) {
        let mut b = v.as_bytes().to_vec();
        b.push(0);
        self.prop(name, &b);
    }
    /// The blob: header, an empty reservation map, then the blocks.
    fn blob(mut self) -> Vec<u8> {
        self.word(9);
        let rsv = 40u32;
        let st = rsv + 16;
        let strs = st + self.structs.len() as u32;
        let total = strs + self.strings.len() as u32;
        let mut b = Vec::new();
        for w in [0xd00d_feed, total, st, strs, rsv, 17, 16, 0, self.strings.len() as u32, self.structs.len() as u32] {
            b.extend_from_slice(&u32::to_be_bytes(w));
        }
        b.extend_from_slice(&[0; 16]);
        b.extend_from_slice(&self.structs);
        b.extend_from_slice(&self.strings);
        b
    }
}

/// `reg` of (address, size) pairs, two cells each.
fn reg2(regs: &[(u64, u64)]) -> Vec<u8> {
    regs.iter().flat_map(|&(a, s)| [a.to_be_bytes(), s.to_be_bytes()].concat()).collect()
}

/// The hardware a device tree with one interrupt controller node
/// (`compat`, `reg`, `#redistributor-regions` if given) describes.
fn dt_hw(compat: &str, regs: &[(u64, u64)], redist: Option<u32>) -> hw::Hw {
    let mut d = Dtb::default();
    d.begin("");
    d.prop_u32("#address-cells", 2);
    d.prop_u32("#size-cells", 2);
    d.begin("intc@8000000");
    d.prop_str("compatible", compat);
    d.prop_u32("#interrupt-cells", 3);
    // reg before #redistributor-regions: a node's facts are used at its end.
    d.prop("reg", &reg2(regs));
    if let Some(n) = redist {
        d.prop_u32("#redistributor-regions", n);
    }
    // A child (an ITS) with its own reg, which is not the GIC's.
    d.begin("msi-controller@8080000");
    d.prop_str("compatible", "arm,gic-v3-its");
    d.prop("reg", &reg2(&[(0x808_0000, 0x2_0000)]));
    d.end();
    d.end();
    d.end();
    let blob = d.blob();
    let mut mem = vec![0u8; BASE as usize + blob.len()];
    mem[BASE as usize..].copy_from_slice(&blob);
    layout::MEMORY.set((mem.as_ptr() as u64, mem.len() as u64));
    let h = hw::discover(0, BASE).expect("device tree");
    layout::MEMORY.set((0, 0));
    h
}

const GICD: (u64, u64) = (0x800_0000, 0x1_0000);

fn gicr_regions(n: u64) -> Vec<(u64, u64)> {
    (0..n).map(|i| (0x1_0000_0000 + i * 0x100_0000, 0x40_0000)).collect()
}

#[test]
fn every_redistributor_region_of_the_device_tree_is_kept() {
    // Five regions (six reg entries), then GICC, GICH and GICV.
    let regions = gicr_regions(5);
    let tail = [(0x2c00_0000, 0x2_0000), (0x2c01_0000, 0x2_0000), (0x2c02_0000, 0x2_0000)];
    for with_tail in [false, true] {
        let mut regs = vec![GICD];
        regs.extend_from_slice(&regions);
        if with_tail {
            regs.extend_from_slice(&tail);
        }
        let h = dt_hw("arm,gic-v3", &regs, Some(5));
        assert_eq!(h.gic_version, 3);
        assert_eq!(h.gicd, GICD.0);
        assert!(!h.gicr_lost, "tail {with_tail}");
        assert_eq!(&h.gicr[..h.n_gicr], &regions[..], "tail {with_tail}");
    }
}

#[test]
fn more_redistributor_regions_than_recorded_are_a_boot_failure() {
    let n = hw::MAX_GICR as u64 + 1;
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(n));
    let h = dt_hw("arm,gic-v3", &regs, Some(n as u32));
    assert!(h.gicr_lost);
    // So is a count the reg property does not hold, or none at all.
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(2));
    assert!(dt_hw("arm,gic-v3", &regs, Some(3)).gicr_lost);
    assert!(dt_hw("arm,gic-v3", &regs, Some(0)).gicr_lost);
    // Exactly as many as recorded is fine.
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(hw::MAX_GICR as u64));
    let h = dt_hw("arm,gic-v3", &regs, Some(hw::MAX_GICR as u32));
    assert!(!h.gicr_lost);
    assert_eq!(h.n_gicr, hw::MAX_GICR);
}

#[test]
fn gicc_gich_and_gicv_are_not_redistributor_regions() {
    // One region (the default, or said), then 128 KiB GICC, GICH and
    // GICV (64 KiB-spaced aliases): none of them is a redistributor.
    let regs = [GICD, (0x80a_0000, 0xf6_0000), (0x2c00_0000, 0x2_0000), (0x2c01_0000, 0x2_0000), (0x2c02_0000, 0x2_0000)];
    for redist in [None, Some(1)] {
        let h = dt_hw("arm,gic-v3", &regs, redist);
        assert!(!h.gicr_lost);
        assert_eq!(&h.gicr[..h.n_gicr], &[(0x80a_0000, 0xf6_0000)], "{redist:?}");
    }
}

#[test]
fn a_gicv2_cpu_interface_is_kept_whole() {
    let h = dt_hw("arm,gic-400", &[(0x2c00_1000, 0x1000), (0x2c02_0000, 0x2_0000)], None);
    assert_eq!(h.gic_version, 2);
    assert_eq!((h.gicc, h.gicc_len), (0x2c02_0000, 0x2_0000));
}

#[test]
fn kernel_device_ranges_are_kept_in_whole_pages() {
    assert_eq!(bootmem::pages_covering(0x800_0000, 0x801_0000), (0x800_0000, 0x801_0000));
    assert_eq!(bootmem::pages_covering(0x800_0800, 0x801_0800), (0x800_0000, 0x801_1000));
    assert_eq!(bootmem::pages_covering(0x800_0fff, 0x800_1001), (0x800_0000, 0x800_2000));
    assert_eq!(bootmem::pages_covering(u64::MAX - 0x10, u64::MAX), (u64::MAX & !0xfff, u64::MAX & !0xfff));
    // Through the device list: no page of an unaligned GIC is left over.
    let mut dev = bootmem::Ranges::new();
    dev.add(0, 0x1000_0000);
    let (s, e) = bootmem::pages_covering(0x800_0800, 0x800_0800 + 0x1_0000);
    dev.remove(s, e);
    assert_eq!(dev.n, 2);
    assert_eq!((dev.r[0].end, dev.r[1].start), (0x800_0000, 0x801_1000));
}

#[test]
fn an_unbounded_redistributor_range_must_end_inside_the_mapping() {
    let b = 0x800_0000;
    // No bound from the tables, mapped for two cores: two redistributors
    // and the last frame, or more redistributors past the mapping.
    let closed = [(b, 0), (b + 0x2_0000, LAST)];
    assert_eq!(gic_layout::reserve(b, 0, 0x8_0000, frames(&closed)), Some(0x8_0000));
    let open = [(b, 0), (b + 0x2_0000, 0), (b + 0x4_0000, 0), (b + 0x6_0000, 0)];
    assert_eq!(gic_layout::reserve(b, 0, 0x8_0000, frames(&open)), None);
    // GICv4: the last frame's VLPI frames may pass the mapping.
    let v4 = [(b, VLPIS), (b + 0x4_0000, VLPIS | LAST)];
    assert_eq!(gic_layout::reserve(b, 0, 0x6_0000, frames(&v4)), Some(0x8_0000));
    // A bound from the tables: all of it, last frame seen or not.
    assert_eq!(gic_layout::reserve(b, 0x8_0000, 0x8_0000, frames(&open)), Some(0x8_0000));
    assert_eq!(gic_layout::reserve(b, 0x2_0000, 0x2_0000, frames(&[(b, VLPIS)])), Some(0x4_0000));
}

/// The hardware a device tree describes whose root has `root` cells and
/// whose GICv3 sits under /soc with `soc` cells and a raw `reg`.
fn dt_soc(root: (u32, u32), soc: (u32, u32), reg: &[u8], redist: u32) -> Option<hw::Hw> {
    let mut d = Dtb::default();
    d.begin("");
    d.prop_u32("#address-cells", root.0);
    d.prop_u32("#size-cells", root.1);
    d.begin("cpus");
    d.prop_u32("#address-cells", 1);
    d.prop_u32("#size-cells", 0);
    d.begin("cpu@0");
    d.prop("reg", &0u32.to_be_bytes());
    d.end();
    d.end();
    d.begin("soc");
    d.prop_u32("#address-cells", soc.0);
    d.prop_u32("#size-cells", soc.1);
    // The root's cells for /soc's own reg.
    d.prop("reg", &[0u8; 12]);
    d.begin("interrupt-controller@8000000");
    d.prop_str("compatible", "arm,gic-v3");
    // The GIC's cells are its children's (an ITS), not its own reg's.
    d.prop_u32("#address-cells", 1);
    d.prop_u32("#size-cells", 1);
    d.prop("reg", reg);
    d.prop_u32("#redistributor-regions", redist);
    d.end();
    d.end();
    d.end();
    let blob = d.blob();
    let mut mem = vec![0u8; BASE as usize + blob.len()];
    mem[BASE as usize..].copy_from_slice(&blob);
    layout::MEMORY.set((mem.as_ptr() as u64, mem.len() as u64));
    let h = hw::discover(0, BASE);
    layout::MEMORY.set((0, 0));
    h
}

/// Proposal 5: reg is read in its parent's cells, not the root's.
#[test]
fn reg_uses_the_parents_cells() {
    let regions = gicr_regions(3);
    let mut regs = vec![GICD];
    regs.extend_from_slice(&regions);
    let h = dt_soc((2, 1), (2, 2), &reg2(&regs), 3).expect("device tree");
    assert_eq!(h.gicd, GICD.0);
    assert!(!h.gicr_lost);
    assert_eq!(&h.gicr[..h.n_gicr], &regions[..]);
    assert_eq!(&h.cpus[..h.n_cpus], &[0]);
    // One address cell and one size cell under /soc.
    let one: Vec<u8> = [(0x800_0000u32, 0x1_0000u32), (0x80a_0000, 0xf6_0000)]
        .iter()
        .flat_map(|&(a, s)| [a.to_be_bytes(), s.to_be_bytes()].concat())
        .collect();
    let h = dt_soc((2, 2), (1, 1), &one, 1).expect("device tree");
    assert_eq!(h.gicd, 0x800_0000);
    assert!(!h.gicr_lost);
    assert_eq!(&h.gicr[..h.n_gicr], &[(0x80a_0000, 0xf6_0000)]);
}

#[test]
fn a_gic_reg_the_kernel_cannot_read_whole_is_never_used() {
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(2));
    // Cells the kernel does not handle: no GIC found, so no boot.
    assert!(dt_soc((2, 2), (3, 2), &reg2(&regs), 2).is_none());
    assert!(dt_soc((2, 2), (2, 0), &reg2(&regs), 2).is_none());
    // A reg that is not whole entries is not read at all: no GIC either.
    let mut bytes = reg2(&regs);
    bytes.extend_from_slice(&[0; 8]);
    assert!(dt_soc((2, 2), (2, 2), &bytes, 2).is_none());
    assert!(dt_soc((2, 2), (2, 2), &reg2(&regs), 2).is_some());
}

/// The AArch64 loader sizes its memory map buffer with `capacity`: the
/// sizing call's map and 16 more descriptors of at least 48 bytes, None
/// where that does not fit (as x86_mmap::capacity).
#[test]
fn the_efi_memory_map_capacity_never_wraps() {
    assert_eq!(efi_mmap::capacity(4800, 48), Some(4800 + 16 * 48));
    assert_eq!(efi_mmap::capacity(4800, 0), Some(4800 + 16 * 48));
    assert_eq!(efi_mmap::capacity(4800, 80), Some(4800 + 16 * 80));
    assert_eq!(efi_mmap::capacity(usize::MAX - 16 * 48, 48), Some(usize::MAX));
    assert_eq!(efi_mmap::capacity(usize::MAX - 16 * 48 + 1, 48), None);
    assert_eq!(efi_mmap::capacity(0, usize::MAX / 16 + 1), None);
    let lib = include_str!("../../crates/fl4-efi/src/lib.rs");
    assert!(lib.contains("let cap = efi_mmap::capacity(size, dsize).unwrap_or_else(|| fail(\"GetMemoryMap\"));"));
}

/// UEFI 2.10 §7.4: after the first ExitBootServices call, even a failed
/// one, firmware may have shut boot services down in part, and the loader
/// may call only GetMemoryMap and ExitBootServices: every failure in the
/// retry loop halts through `handoff_failed`, which uses the console
/// (`fail`) only before that first call.
#[test]
fn the_aarch64_loader_uses_no_console_after_exit_boot_services() {
    let lib = include_str!("../../crates/fl4-efi/src/lib.rs");
    let at = lib.find("    let mut tries = 0;\n    loop {\n").expect("handoff loop");
    let end = at + lib[at..].find("\n    }\n").expect("loop end");
    let body = &lib[at..end];
    assert!(body.contains("(bs().exit_boot_services)(image, key)"));
    assert!(!body.contains(" fail("), "a failure after ExitBootServices writes to the console:\n{body}");
    assert_eq!(body.matches("handoff_failed(tries, ").count(), 3);
    let h = &lib[lib.find("fn handoff_failed(tries: usize, msg: &str) -> ! {").expect("handoff_failed")..];
    let h = &h[..h.find("\n}\n").unwrap()];
    assert!(h.contains("if tries == 0 {\n        fail(msg);\n    }"), "{h}");
    assert!(h.contains("msr daifset, #0xf") && h.contains("wfi"), "{h}");
    assert_eq!(h.matches("fail(").count(), 1);
}

// ---- extra BootInfo ---------------------------------------------------------------

/// The records of an extra BootInfo of `len` bytes, as user space walks
/// them: (id, offset, length); every header inside, none of length 0.
fn bi_records(buf: &[u8], len: usize) -> Vec<(u64, usize, usize)> {
    let mut out = vec![];
    let mut off = 0;
    while off < len {
        assert!(off + 16 <= len, "header at {off:#x} past the end {len:#x}");
        let id = u64::from_le_bytes(buf[off..off + 8].try_into().unwrap());
        let l = u64::from_le_bytes(buf[off + 8..off + 16].try_into().unwrap()) as usize;
        assert!(l >= 16 && off + l <= len, "record {id} at {off:#x} of {l:#x} bytes, end {len:#x}");
        out.push((id, off, l));
        off += l;
    }
    out
}

/// Bytes without 0xAA, the poison of the buffers below.
fn not_poison(i: usize, salt: u8) -> u8 {
    match (i as u8).wrapping_mul(31).wrapping_add(salt) {
        0xaa => 0x55,
        b => b,
    }
}

/// Audit r10 F2: the extra BootInfo is a chain of records each exactly as
/// long as its header says, that ends exactly at the length given to user
/// space, a multiple of 8, and has no byte the kernel did not write: the
/// buffer is free RAM the firmware left, poisoned here. Before, with the
/// ACPI RSDP (52 bytes) the device tree record started 4 bytes off 8, and
/// rounding the end up added 4 bytes past the record (a device tree of a
/// multiple of 8) or none to it (4 more), so the chain ran past or stopped
/// short of the end; the padding and the tail came from the old RAM.
#[test]
fn extra_bootinfo_records_chain_exactly_with_nothing_uninitialized() {
    use fl4_abi::consts::bootinfo_header as id;
    let rsdp: Vec<u8> = (0..36).map(|i| not_poison(i, 1)).collect();
    let regs = [0x1111_2222_3333_4444, 0x0123_4567_89ab_cdef, 0, u64::MAX >> 1, 0x10];
    let all_mods: Vec<fl4_bootinfo::Module> = (0..fl4_bootinfo::MAX_MODULES)
        .map(|m| {
            let mut name = [0u8; fl4_bootinfo::NAME_LEN];
            for (i, c) in name.iter_mut().enumerate().take(10) {
                *c = not_poison(i, m as u8);
            }
            fl4_bootinfo::Module { paddr: 0x4000_0000 + m as u64 * 0x10_0000, size: 0x1234 + m as u64, name }
        })
        .collect();
    for has_rsdp in [false, true] {
        for n_mods in [0, 1, 3, fl4_bootinfo::MAX_MODULES] {
            for dtb_len in [0usize, 40, 41, 44, 45, 48, 0x1000, 0x1003, 0x1004, 0x1_0000] {
                let what = format!("rsdp {has_rsdp} mods {n_mods} dtb {dtb_len:#x}");
                let mut dtb: Vec<u8> = (0..dtb_len).map(|i| not_poison(i, 7)).collect();
                if dtb_len >= 8 {
                    dtb[..4].copy_from_slice(&0xd00d_feedu32.to_be_bytes());
                    dtb[4..8].copy_from_slice(&0x0002_0000u32.to_be_bytes());
                }
                // The kernel's size for it (lib.rs `extra_size`).
                let size = 4096 + ((dtb_len + 16 + 4096) & !4095);
                let mut buf = vec![0xaau8; size];
                let mods = &all_mods[..n_mods];
                let len = extra_bi::build(&mut buf, has_rsdp.then_some(&rsdp[..]), &regs, mods, &dtb).expect(&what);
                assert_eq!(len % 8, 0, "{what}");
                assert!(buf.iter().all(|&b| b != 0xaa), "{what}: uninitialized bytes");
                let recs = bi_records(&buf, len);
                let mut want = vec![];
                if has_rsdp {
                    want.push(id::X86_ACPI_RSDP);
                }
                want.push(id::AARCH64_ID_REGS);
                if n_mods != 0 {
                    want.push(id::X86_BOOT_MODULES);
                }
                if dtb_len != 0 {
                    want.push(id::FDT);
                }
                if recs.last().unwrap().0 == id::PADDING {
                    want.push(id::PADDING);
                }
                assert_eq!(recs.iter().map(|r| r.0).collect::<Vec<_>>(), want, "{what}");
                for &(rid, at, l) in &recs {
                    let body = &buf[at + 16..at + l];
                    match rid {
                        id::X86_ACPI_RSDP => assert_eq!(body, &rsdp[..], "{what}"),
                        id::AARCH64_ID_REGS => {
                            let got: Vec<u64> = body.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
                            assert_eq!(got, regs, "{what}");
                        }
                        id::X86_BOOT_MODULES => {
                            assert_eq!(l, 16 + 8 + 80 * n_mods, "{what}");
                            assert_eq!(u64::from_le_bytes(body[..8].try_into().unwrap()), n_mods as u64);
                            for (m, e) in mods.iter().zip(body[8..].chunks(80)) {
                                assert_eq!(u64::from_le_bytes(e[..8].try_into().unwrap()), m.paddr);
                                assert_eq!(u64::from_le_bytes(e[8..16].try_into().unwrap()), m.size);
                                assert_eq!(&e[16..], &m.name[..]);
                            }
                        }
                        id::FDT => {
                            assert_eq!(l, 16 + dtb_len.div_ceil(8) * 8, "{what}");
                            let total = u32::from_be_bytes(body[4..8].try_into().unwrap()) as usize;
                            assert_eq!(total, dtb_len, "{what}: FDT totalsize");
                            assert_eq!(&body[..4], &dtb[..4]);
                            assert_eq!(&body[8..dtb_len], &dtb[8..], "{what}");
                            assert!(body[dtb_len..].iter().all(|&b| b == 0), "{what}");
                        }
                        id::PADDING => {
                            assert!(l < 24, "{what}");
                            assert!(body.iter().all(|&b| b == 0), "{what}");
                        }
                        _ => panic!("{what}: record {rid}"),
                    }
                }
            }
        }
    }
    // Too small a buffer is refused, not overrun.
    let mut small = [0u8; 64];
    assert_eq!(extra_bi::build(&mut small, Some(&rsdp), &regs, &[], &[]), None);
    let mut small = vec![0u8; 4096];
    assert_eq!(extra_bi::build(&mut small, None, &regs, &[], &[1u8; 4096]), None);
}
