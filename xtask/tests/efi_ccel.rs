//! The UEFI confidential-computing event log (fl4-efi ccel.rs, on the
//! parsing of tcg2.rs): the `CCEL` ACPI table, a SHA-384 crypto agile log and
//! its final events, and the event that measures a boot file into RTMR[2].
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/ccel.rs"]
mod ccel;

use ccel::{area_limit, cc_event, ccel_area, choose, walk_log, MR_INDEX_RTMR2};
use tcg2::{append_final, final_snapshot, main_log, MAX_EVENT_LOG};

const SHA384: u16 = 0xc;

/// A log's Spec ID event listing SHA-384 only, as TDX firmware writes it.
fn spec_id() -> Vec<u8> {
    let mut ev = Vec::new();
    ev.extend(b"Spec ID Event03\0");
    ev.extend([0u8; 4]); // platform class
    ev.extend([0, 2, 0, 2]); // versions, uintn size
    ev.extend(1u32.to_le_bytes());
    ev.extend(SHA384.to_le_bytes());
    ev.extend(48u16.to_le_bytes());
    ev.push(0); // vendor info size
    let mut v = vec![0u8; 32];
    v[4..8].copy_from_slice(&3u32.to_le_bytes()); // EV_NO_ACTION
    v[28..32].copy_from_slice(&(ev.len() as u32).to_le_bytes());
    v.extend(ev);
    v
}

/// A `CC_EVENT` with one SHA-384 digest.
fn event(mr: u32, ty: u32, fill: u8, data: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    v.extend(mr.to_le_bytes());
    v.extend(ty.to_le_bytes());
    v.extend(1u32.to_le_bytes());
    v.extend(SHA384.to_le_bytes());
    v.extend([fill; 48]);
    v.extend((data.len() as u32).to_le_bytes());
    v.extend(data);
    v
}

fn ccel(cc_type: u8, laml: u64, lasa: u64) -> Vec<u8> {
    let mut t = vec![0u8; 56];
    t[0..4].copy_from_slice(b"CCEL");
    t[4..8].copy_from_slice(&56u32.to_le_bytes());
    t[8] = 1;
    t[36] = cc_type;
    t[40..48].copy_from_slice(&laml.to_le_bytes());
    t[48..56].copy_from_slice(&lasa.to_le_bytes());
    t[9] = t.iter().fold(0u8, |s, b| s.wrapping_add(*b)).wrapping_neg();
    t
}

#[test]
fn the_ccel_table_gives_a_tdx_guests_log_area() {
    assert_eq!(ccel_area(&ccel(2, 0x1_0000, 0x7000_0000)[..]), Some((0x7000_0000, 0x1_0000)));
}

#[test]
fn a_ccel_table_is_refused_unless_it_is_a_valid_tdx_one() {
    // SEV's CC type.
    assert_eq!(ccel_area(&ccel(1, 0x1000, 0x7000_0000)[..]), None);
    // No area.
    assert_eq!(ccel_area(&ccel(2, 0, 0x7000_0000)[..]), None);
    assert_eq!(ccel_area(&ccel(2, 0x1000, 0)[..]), None);
    // Checksum.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[40] ^= 1;
    assert_eq!(ccel_area(&t[..]), None);
    // Signature.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[0] = b'X';
    t[9] = t[9].wrapping_sub(b'X'.wrapping_sub(b'C'));
    assert_eq!(ccel_area(&t[..]), None);
    // Shorter than its fields, or than it says.
    let mut t = ccel(2, 0x1000, 0x7000_0000);
    t[4..8].copy_from_slice(&55u32.to_le_bytes());
    assert_eq!(ccel_area(&t[..]), None);
    let t = ccel(2, 0x1000, 0x7000_0000);
    assert_eq!(ccel_area(&t[..40]), None);
}

#[test]
fn a_sha384_log_is_walked_to_its_first_zeroed_entry() {
    let mut log = spec_id();
    let header = log.len();
    log.extend(event(1, 0x8000_0001, 0xaa, b"first"));
    log.extend(event(3, 0xd, 0xbb, b"rootserver"));
    let end = log.len();
    log.resize(end + 256, 0);
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, end);
    assert!(!lost);
    assert_eq!(found.algs.digest_size(SHA384), Some(48));
    assert!(end > header);
}

#[test]
fn a_log_that_fills_its_area_is_complete() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, log.len());
    assert!(!lost);
}

#[test]
fn garbage_after_the_events_is_reported_as_a_truncated_log() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let end = log.len();
    // An event with a digest count above the log's algorithms.
    log.extend([1, 0, 0, 0, 1, 0, 0, 0, 9, 0, 0, 0, 0xc, 0, 0xff, 0xff]);
    log.resize(end + 64, 0xff);
    let (found, lost) = walk_log(&log[..], log.len()).unwrap();
    assert_eq!(found.len, end);
    assert!(lost);
}

#[test]
fn an_event_past_the_area_limit_ends_the_walk() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"inside"));
    let inside = log.len();
    log.extend(event(1, 1, 2, b"past the limit"));
    let (found, lost) = walk_log(&log[..], inside + 10).unwrap();
    assert_eq!(found.len, inside);
    assert!(lost);
}

#[test]
fn a_log_without_a_spec_id_event_is_no_log() {
    assert!(walk_log(&[0u8; 256][..], 256).is_none());
    let log = spec_id();
    assert!(walk_log(&log[..], log.len() - 1).is_none());
}

/// The protocol path: the log as GetEventLog gave it, then what the CC final
/// events table gained after that.
#[test]
fn final_events_are_appended_after_the_snapshot() {
    let mut log = spec_id();
    let last = log.len();
    log.extend(event(1, 1, 1, b"main"));
    let parsed = main_log(&log[..], 0x1000, 0x1000 + last as u64, false).unwrap();
    assert_eq!(parsed.len, log.len());

    let already = event(1, 2, 2, b"already in the log");
    let mut table = Vec::new();
    table.extend(1u64.to_le_bytes());
    table.extend(1u64.to_le_bytes());
    table.extend(&already);
    let snap = final_snapshot(&table[..], &parsed.algs).unwrap();
    assert_eq!(snap.nr_events, 1);

    let exit = event(2, 0x8000_0007, 3, b"Exit Boot Services Invocation");
    table[8..16].copy_from_slice(&2u64.to_le_bytes());
    table.extend(&exit);
    let mut buf = vec![0u8; log.len() + 4096];
    buf[..log.len()].copy_from_slice(&log);
    let (len, lost) = append_final(&table[..], &parsed.algs, &snap, &mut buf, log.len());
    assert!(!lost);
    assert_eq!(len, log.len() + exit.len());
    assert_eq!(&buf[log.len()..len], &exit[..]);
    // The result is one log, whose last event is the appended one.
    let (again, lost) = walk_log(&buf[..], buf.len()).unwrap();
    assert_eq!(again.len, len);
    assert!(!lost);
}

/// `EFI_CC_EVENT`: packed, 14-byte header, RTMR[2] is MR index 3.
#[test]
fn a_measured_file_is_an_ipl_event_for_rtmr2() {
    assert_eq!(MR_INDEX_RTMR2, 3);
    let mut buf = [0u8; 64];
    let n = cc_event(&mut buf, b"rootserver");
    assert_eq!(n, 4 + 14 + 10);
    assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 28);
    assert_eq!(u32::from_le_bytes(buf[4..8].try_into().unwrap()), 14);
    assert_eq!(u16::from_le_bytes(buf[8..10].try_into().unwrap()), 1);
    assert_eq!(u32::from_le_bytes(buf[10..14].try_into().unwrap()), 3);
    assert_eq!(u32::from_le_bytes(buf[14..18].try_into().unwrap()), 0xd);
    assert_eq!(&buf[18..28], b"rootserver");
}

#[test]
fn a_long_name_is_cut_to_fit_the_event() {
    let mut buf = [0u8; 32];
    let n = cc_event(&mut buf, &[b'x'; 100]);
    assert_eq!(n, 32);
    assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 32);
}

#[test]
fn the_area_taken_is_capped() {
    assert_eq!(area_limit(0x1000), 0x1000);
    assert_eq!(area_limit(u64::MAX), MAX_EVENT_LOG);
}

/// The kernel gets the CC log only from a TDX guest and the TPM log only
/// outside one: a TD ignores any TPM.
#[test]
fn the_loader_collects_the_cc_log_in_a_td_and_the_tpm_log_otherwise() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let tpm = x86.find("let tpm = if shared == 0 { tcg2::collect() } else { None };").expect("TPM log collected");
    let cc = x86.find("let cc = if shared != 0 { ccel::collect() } else { None };").expect("CC log collected");
    assert!(tpm < cc);
    assert_eq!(x86.matches("tcg2::collect()").count(), 1, "only outside a TD");
    assert_eq!(x86.matches("ccel::collect()").count(), 1, "only in a TD");
    assert!(x86.contains("MB2_TAG_CC_EVENT_LOG: u32 = 0x464c_3402"));
    assert!(x86.contains("ccel::measure_file(b\"rootserver\", path, pa, len);"), "rootserver= file");
    assert!(x86.contains("ccel::measure_file(b\"module\", path, pa, len);"), "module= files");
}

/// RTMR[2] is a TDX register: the options' files are measured into it only
/// in a TD, and into the TPM only outside one.
#[test]
fn boot_files_are_measured_only_in_a_td() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    for role in ["rootserver", "module"] {
        let call = format!(
            "if measure {{\n                ccel::measure_file(b\"{role}\", path, pa, len);\n            }} else {{\n                tcg2::measure_file(b\"{role}\", path, pa, len).unwrap_or_else(|e| fail(e));\n            }}"
        );
        assert_eq!(x86.matches(&call).count(), 1, "{role}");
    }
    assert_eq!(x86.matches("ccel::measure_file(").count(), 2, "only these two");
    let is_tdx = &x86[x86.find("pub(super) fn is_tdx() -> bool {").expect("is_tdx")..];
    assert!(is_tdx[..is_tdx.find("\n}\n").unwrap()].contains("sev().0 == 0 && tdx_shared_mask() != 0"));
    let start = &x86[x86.find("pub unsafe fn start_default(").expect("start_default")..];
    let start = &start[..start.find("\n}\n").unwrap()];
    let check = start.find("let measure = is_tdx();").expect("TD check");
    assert!(check < start.find("boot_files(li, &opts, measure)").expect("boot_files"));
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    assert!(fw.contains("pub fn is_tdx(&self) -> bool {\n        x86::is_tdx()\n    }"));
}

#[test]
fn a_protocol_log_that_can_follow_its_events_is_used() {
    let table_unused = || -> Option<&str> { panic!("the table is not needed") };
    assert_eq!(choose(Some("protocol"), |_| true, table_unused), Some("protocol"));
}

/// Without usable final events the `CCEL` table, which firmware keeps
/// appending to, is better; the protocol's main log remains the fallback.
#[test]
fn a_protocol_log_without_final_events_falls_back_to_the_table() {
    assert_eq!(choose(Some("protocol"), |_| false, || Some("table")), Some("table"));
    assert_eq!(choose(Some("protocol"), |_| false, || None), Some("protocol"));
    assert_eq!(choose(None, |_: &&str| true, || Some("table")), Some("table"));
    assert_eq!(choose(None::<&str>, |_| true, || None), None);
}

#[test]
fn an_area_ending_inside_an_entry_header_is_complete_if_zeroed() {
    let mut log = spec_id();
    log.extend(event(1, 1, 1, b"x"));
    let end = log.len();
    for tail in 1..16 {
        let mut area = log.clone();
        area.resize(end + tail, 0);
        let (found, lost) = walk_log(&area[..], area.len()).unwrap();
        assert_eq!((found.len, lost), (end, false), "{tail} zero bytes");
        *area.last_mut().unwrap() = 1;
        let (found, lost) = walk_log(&area[..], area.len()).unwrap();
        assert_eq!((found.len, lost), (end, true), "{tail} bytes, the last not zero");
    }
}

/// The five-level handoff turns off what forbids clearing CR0.PG before it
/// leaves long mode, and its GDT needs no write when a selector loads.
#[test]
fn the_five_level_handoff_clears_pcide_and_cet_first() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let blob = &x86[x86.find("\"fl4_handoff_la57:\"").expect("handoff")..x86.find("\"fl4_handoff_la57_end:\"").expect("end")];
    let clear = blob.find("andq $~((1 << 17) | (1 << 23)), %rax").expect("PCIDE and CET cleared");
    assert!(clear < blob.find("ljmpl *la57_to_compat").unwrap());
    for d in ["0x00cf9b000000ffff", "0x00af9b000000ffff", "0x00cf93000000ffff"] {
        assert!(blob.contains(d), "{d}");
    }
}

/// The GUIDs are UEFI's (edk2 MdePkg.dec), checked byte for byte.
#[test]
fn the_cc_guids_are_the_uefi_ones() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    assert!(c.contains("Guid(0x9675_1a3d, 0x72f4, 0x41a6, [0xa7, 0x94, 0xed, 0x5d, 0x0e, 0x67, 0xae, 0x6b])"));
    assert!(c.contains("Guid(0xdd4a_4648, 0x2de7, 0x4665, [0x96, 0x4d, 0x21, 0xd9, 0xef, 0x5f, 0xb4, 0x46])"));
}

/// HashLogExtendEvent's result: success, or `EFI_VOLUME_FULL` (RTMR[2]
/// extended, only the log is full), lets the file boot; anything else, or a
/// TD without the protocol at all, stops the boot.
#[test]
fn a_boot_file_that_cannot_be_measured_is_refused() {
    use ccel::{measure_status, VOLUME_FULL};
    assert_eq!(VOLUME_FULL, (1 << 63) | 11);
    assert!(measure_status(false, 0).is_err(), "no EFI_CC_MEASUREMENT_PROTOCOL");
    assert!(measure_status(false, VOLUME_FULL).is_err());
    assert_eq!(measure_status(true, 0), Ok(()));
    assert_eq!(measure_status(true, VOLUME_FULL), Ok(()));
    for r in [(1 << 63) | 2, (1 << 63) | 3, (1 << 63) | 7, (1 << 63) | 9, 1, u64::MAX] {
        assert!(measure_status(true, r).is_err(), "{r:#x}");
    }
}

/// In a TD a missing protocol fails the boot rather than skipping RTMR[2].
#[test]
fn measure_file_fails_closed_without_the_protocol() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    let f = &c[c.find("pub fn measure_file(").expect("measure_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    assert!(!f.contains("else { return }"), "a missing protocol must not return quietly");
    assert!(f.contains("let Some(cc) = protocol() else {"));
    assert!(f.contains("measure_status(false, 0)"));
    assert!(f.contains("measure_status(true, r as u64)"));
    assert!(f.contains("fail("));
}

/// RTMR[2] gets the descriptor first (role, length, path: never empty),
/// then the contents only of a file that has any: a 0-byte file is not
/// handed to HashLogExtendEvent, which refuses to hash nothing.
#[test]
fn measure_file_extends_the_descriptor_then_nonempty_contents() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    let f = &c[c.find("pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64)").expect("measure_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    let at = |s: &str| f.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("file_descriptor(&mut desc, role, path, len)") < at("cc_event(&mut event, desc)"));
    let desc = at("hash_log_extend_event)(cc, 0, desc.as_ptr() as u64, n as u64, event.as_ptr())");
    let guard = at("if len > 0 {");
    let contents = at("hash_log_extend_event)(cc, 0, pa, len, event.as_ptr())");
    assert!(desc < guard && guard < contents);
    assert_eq!(f.matches("hash_log_extend_event)(").count(), 2);
    assert_eq!(f.matches("measure_status(true, r as u64)").count(), 2, "both extensions fail closed");
}

/// The CC event carries the whole descriptor (role, length, path) as its
/// data, so the log says which file and role a digest is for.
#[test]
fn the_cc_event_carries_the_descriptor() {
    let mut desc = [0u8; tcg2::DESC_MAX];
    let n = tcg2::file_descriptor(&mut desc, b"module", b"\\efi\\m.elf", 7);
    let mut buf = [0u8; 18 + tcg2::DESC_MAX];
    let len = cc_event(&mut buf, &desc[..n]);
    assert_eq!(len, 18 + n);
    assert_eq!(&buf[18..len], &desc[..n]);
}

/// A caller's bytes (`Firmware::measure_cc_file`) fail closed in RTMR[2]:
/// no protocol is `EFI_UNSUPPORTED`, nothing to hash is
/// `EFI_INVALID_PARAMETER`, and a result `measure_status` refuses is
/// returned as firmware gave it; each is said on the console.
#[test]
fn measure_bytes_fails_closed() {
    let c = include_str!("../../crates/fl4-efi/src/ccel.rs");
    assert!(c.contains("const UNSUPPORTED: Status = (1 << 63) | 3;"));
    assert!(c.contains("const INVALID_PARAMETER: Status = (1 << 63) | 2;"));
    let f = &c[c.find("pub fn measure_bytes(name: &[u8], pa: u64, len: u64) -> Result<(), Status> {").expect("measure_bytes")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    let at = |s: &str| f.find(s).unwrap_or_else(|| panic!("{s}"));
    let none = at("let Some(cc) = protocol() else {");
    let unsupported = at("return Err(UNSUPPORTED);");
    let empty = at("if len == 0 {");
    let invalid = at("return Err(INVALID_PARAMETER);");
    let event = at("cc_event(&mut event, name);");
    let ext = at("((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr())");
    let chk = at("measure_status(true, r as u64).map_err(|e| {");
    assert!(none < at("measure_status(false, 0).unwrap_err()") && at("measure_status(false, 0).unwrap_err()") < unsupported);
    assert!(unsupported < empty && empty < invalid && invalid < event && event < ext && ext < chk);
    assert_eq!(f.matches("hash_log_extend_event)(").count(), 1);
    assert_eq!(f.matches("say!(").count(), 3, "every refusal is said");
    assert!(f.trim_end().ends_with("r\n        })"), "firmware's status is the error");
    assert!(!f.contains("fail("), "the caller decides, but must not boot");
}

/// `measure_cc_file` measures only in a TD, and passes a refusal back.
#[test]
fn measure_cc_file_measures_only_in_a_td() {
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    let f = &fw[fw.find("pub fn measure_cc_file(&self, name: &[u8], bytes: &[u8]) -> Result<(), Status> {").expect("measure_cc_file")..];
    let f = &f[..f.find("\n    }\n").unwrap()];
    assert!(f.contains("if x86::is_tdx() {\n            ccel::measure_bytes(name, bytes.as_ptr() as u64, bytes.len() as u64)?;\n        }\n        Ok(())"));
    assert_eq!(fw.matches("ccel::measure_bytes(").count(), 1);
}

/// A command line becomes the Multiboot 2 command line tag (type 1, with
/// its NUL) among the fixed tags, before `tags_end`; none when empty, as
/// for `start_default` and `Firmware::boot`.
#[test]
fn a_command_line_is_a_multiboot2_tag_before_the_memory_map() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("pub(super) fn boot(image: Handle, kernel: &[u8], files: &[BootFile<'_>], cmdline: &core::ffi::CStr) -> ! {"));
    let start = &x86[x86.find("pub unsafe fn start_default(").expect("start_default")..];
    let start = &start[..start.find("\n}\n").unwrap()];
    assert!(start.contains("boot(image, embedded::KERNEL, &files[..n], c\"\")"));
    let boot = &x86[x86.find("pub(super) fn boot(").unwrap()..];
    let at = |s: &str| boot.find(s).unwrap_or_else(|| panic!("{s}"));
    let guard = at("if !cmdline.is_empty() {");
    let bytes = at("let bytes = cmdline.to_bytes_with_nul();");
    let cap = at("if bytes.len() as u64 > PAGE {\n            fail(\"kernel command line too long\");");
    let tag = at("write(info.tag(1, bytes.len() as u64), bytes);");
    assert!(at("used: 8,") < guard && guard < bytes && bytes < cap && cap < tag);
    assert!(tag < at("let tags_end = info.used;"));
    assert_eq!(boot.matches("info.tag(1,").count(), 1);
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    let b = &fw[fw.find("pub unsafe fn boot_with_cmdline(").expect("boot_with_cmdline")..];
    let b = &b[..b.find("\n    }\n").unwrap()];
    assert!(b.contains("cmdline: &core::ffi::CStr,"));
    assert!(b.contains("fail(\"invalid number of boot modules\");"));
    assert!(b.trim_end().ends_with("x86::boot(self.image, kernel, &files[..modules.len()], cmdline)"));
}
