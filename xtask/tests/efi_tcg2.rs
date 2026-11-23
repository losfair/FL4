//! The UEFI loader's TPM event log (fl4-efi tcg2.rs, used by x86.rs
//! `boot` and lib.rs `start_default`): the exact length of the log
//! GetEventLog names, and the events the final events table gains after
//! the copy, appended whole without the ones the copy already holds. All
//! of it is firmware memory: what does not parse is refused, never read
//! past or panicked on.
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;

use tcg2::{AlgTable, FinalSnapshot};

const SHA1: u16 = 0x0004;
const SHA256: u16 = 0x000b;
const SHA384: u16 = 0x000c;
const BANKS: [(u16, u16); 3] = [(SHA1, 20), (SHA256, 32), (SHA384, 48)];

fn le32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}

/// The Spec ID event (a legacy TCG_PCR_EVENT) listing `algs`.
fn spec_id_event(algs: &[(u16, u16)]) -> Vec<u8> {
    let mut ev = b"Spec ID Event03\0".to_vec();
    le32(&mut ev, 0); // platform class
    ev.extend_from_slice(&[0, 2, 0, 2]); // minor, major, errata, uintn size
    le32(&mut ev, algs.len() as u32);
    for &(a, s) in algs {
        ev.extend_from_slice(&a.to_le_bytes());
        ev.extend_from_slice(&s.to_le_bytes());
    }
    ev.push(0); // vendor info size
    let mut v = Vec::new();
    le32(&mut v, 0);
    le32(&mut v, 3);
    v.extend_from_slice(&[0; 20]);
    le32(&mut v, ev.len() as u32);
    v.extend_from_slice(&ev);
    v
}

/// A TCG_PCR_EVENT2 with a digest per bank in `algs` and `data`.
fn event2(pcr: u32, ty: u32, algs: &[(u16, u16)], data: &[u8]) -> Vec<u8> {
    let mut v = Vec::new();
    le32(&mut v, pcr);
    le32(&mut v, ty);
    le32(&mut v, algs.len() as u32);
    for &(a, s) in algs {
        v.extend_from_slice(&a.to_le_bytes());
        v.extend((0..s).map(|i| (i as u8) ^ pcr as u8));
    }
    le32(&mut v, data.len() as u32);
    v.extend_from_slice(data);
    v
}

/// A log: the Spec ID event, then `n` events; with the offset of the last.
fn log(algs: &[(u16, u16)], n: usize) -> (Vec<u8>, usize) {
    let mut v = spec_id_event(algs);
    let mut last = 0;
    for i in 0..n {
        last = v.len();
        v.extend(event2(i as u32 % 24, 0x8000_0001 + i as u32, algs, &vec![i as u8; 10 + i * 7]));
    }
    (v, last)
}

fn table(algs: &[(u16, u16)]) -> AlgTable {
    let mut t = AlgTable::EMPTY;
    t.n = algs.len();
    t.algs[..algs.len()].copy_from_slice(algs);
    t
}

/// A final events table holding `events`.
fn final_table(events: &[Vec<u8>]) -> Vec<u8> {
    let mut v = 1u64.to_le_bytes().to_vec();
    v.extend_from_slice(&(events.len() as u64).to_le_bytes());
    for e in events {
        v.extend_from_slice(e);
    }
    v
}

const LOC: u64 = 0x7e00_0000;

#[test]
fn the_spec_id_event_gives_its_length_and_banks() {
    let ev = spec_id_event(&BANKS);
    let (len, algs) = tcg2::spec_id(&ev[..]).unwrap();
    assert_eq!(len, ev.len());
    assert_eq!(len, 32 + 28 + 4 * 3 + 1);
    assert_eq!(algs, table(&BANKS));
    assert_eq!(algs.digest_size(SHA256), Some(32));
    assert_eq!(algs.digest_size(0x0012), None);
}

#[test]
fn a_multi_bank_event_has_its_exact_length() {
    let algs = table(&BANKS);
    let e = event2(7, 0x8000_0008, &BANKS, b"abcdefg");
    assert_eq!(e.len(), 12 + (2 + 20) + (2 + 32) + (2 + 48) + 4 + 7);
    assert_eq!(tcg2::event2_len(&e[..], 0, &algs), Some(e.len()));
    // Banks in another order, and fewer than the log has.
    let e = event2(0, 1, &[(SHA384, 48), (SHA1, 20)], &[]);
    assert_eq!(tcg2::event2_len(&e[..], 0, &algs), Some(e.len()));
    // At an offset, with more bytes after it.
    let mut v = vec![0xee; 5];
    v.extend(event2(1, 2, &BANKS, b"x"));
    let n = v.len() - 5;
    v.extend([0xff; 100]);
    assert_eq!(tcg2::event2_len(&v[..], 5, &algs), Some(n));
}

#[test]
fn the_main_log_runs_through_its_last_entry() {
    let (v, last) = log(&BANKS, 5);
    let mut mem = v.clone();
    mem.extend([0xcc; 4096]); // what follows the log in firmware memory
    let l = tcg2::main_log(&mem[..], LOC, LOC + last as u64, false).unwrap();
    assert_eq!(l.len, v.len());
    assert_eq!(l.algs, table(&BANKS));
    // Only the Spec ID event: last_entry == location.
    let (v, _) = log(&BANKS[1..2], 0);
    let l = tcg2::main_log(&v[..], LOC, LOC, false).unwrap();
    assert_eq!(l.len, v.len());
    // A TCG 1.2 log: legacy events throughout.
    let mut v = vec![0u8; 32];
    v[28..32].copy_from_slice(&9u32.to_le_bytes());
    v.extend([1; 9]);
    let mut e = vec![0u8; 32];
    e[4] = 1;
    e[28..32].copy_from_slice(&3u32.to_le_bytes());
    v.extend(&e);
    v.extend([2; 3]);
    let l = tcg2::main_log(&v[..], LOC, LOC + 41, true).unwrap();
    assert_eq!(l.len, v.len());
}

#[test]
fn no_log_and_bad_extents_are_refused() {
    let (v, last) = log(&BANKS, 3);
    let last = LOC + last as u64;
    assert_eq!(tcg2::main_log(&v[..], 0, last, false), None);
    assert_eq!(tcg2::main_log(&v[..], LOC, 0, false), None);
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC - 1, false), None, "last entry before the log");
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC + tcg2::MAX_EVENT_LOG as u64, false), None);
    assert_eq!(tcg2::main_log(&v[..], u64::MAX - 4, u64::MAX, false), None);
    // The last entry inside the Spec ID event.
    assert_eq!(tcg2::main_log(&v[..], LOC, LOC + 40, false), None);
    // The log cut short of its last event.
    assert_eq!(tcg2::main_log(&v[..v.len() - 1], LOC, last, false), None);
    // A log that would run past MAX_EVENT_LOG.
    let mut big = spec_id_event(&BANKS);
    let at = big.len();
    let mut e = event2(0, 1, &BANKS[..1], &[]);
    let n = e.len();
    e[n - 4..].copy_from_slice(&(tcg2::MAX_EVENT_LOG as u32).to_le_bytes());
    big.extend(&e);
    big.resize(at + n + tcg2::MAX_EVENT_LOG, 0);
    assert_eq!(tcg2::main_log(&big[..], LOC, LOC + at as u64, false), None);
}

#[test]
fn malformed_spec_id_events_are_refused() {
    let good = spec_id_event(&BANKS);
    let bad = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut v = good.clone();
        f(&mut v);
        tcg2::spec_id(&v[..])
    };
    assert!(bad(&|_| {}).is_some());
    assert_eq!(bad(&|v| v[4] = 1), None, "not EV_NO_ACTION");
    assert_eq!(bad(&|v| v[32] = b's'), None, "signature");
    assert_eq!(bad(&|v| v[32 + 15] = b'!'), None, "signature's NUL");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&0u32.to_le_bytes())), None, "no banks");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&17u32.to_le_bytes())), None, "too many banks");
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    assert_eq!(bad(&|v| v[56..60].copy_from_slice(&4u32.to_le_bytes())), None, "banks past the event");
    assert_eq!(bad(&|v| v[28..32].copy_from_slice(&20u32.to_le_bytes())), None, "event too short");
    assert_eq!(bad(&|v| v[28..32].copy_from_slice(&u32::MAX.to_le_bytes())), None, "event past the buffer");
    assert_eq!(bad(&|v| v.truncate(31)), None);
    assert_eq!(tcg2::spec_id(&[][..]), None);
}

#[test]
fn malformed_events_are_refused() {
    let algs = table(&BANKS);
    let good = event2(3, 5, &BANKS, b"data");
    let bad = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut v = good.clone();
        f(&mut v);
        tcg2::event2_len(&v[..], 0, &algs)
    };
    assert_eq!(bad(&|_| {}), Some(good.len()));
    assert_eq!(bad(&|v| v[8..12].copy_from_slice(&4u32.to_le_bytes())), None, "more digests than banks");
    assert_eq!(bad(&|v| v[8..12].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    assert_eq!(bad(&|v| v[12..14].copy_from_slice(&0x0012u16.to_le_bytes())), None, "unknown algorithm");
    let n = good.len();
    assert_eq!(bad(&|v| v[n - 8..n - 4].copy_from_slice(&5u32.to_le_bytes())), None, "event past the buffer");
    assert_eq!(bad(&|v| v[n - 8..n - 4].copy_from_slice(&u32::MAX.to_le_bytes())), None);
    for cut in 0..n {
        assert_eq!(tcg2::event2_len(&good[..cut], 0, &algs), None, "cut at {cut}");
    }
    // Zeroed memory is no event.
    assert_eq!(tcg2::event2_len(&[0u8; 64][..], 0, &algs), None);
    // Offsets near usize::MAX do not wrap.
    assert_eq!(tcg2::event2_len(&good[..], usize::MAX - 3, &algs), None);
    assert_eq!(tcg2::event1_len(&good[..], usize::MAX - 20), None);
}

/// Linux's efi_tpm_eventlog_init: the events the table held when the log
/// was taken are in it, so only the rest are appended.
#[test]
fn final_events_after_the_copy_are_appended_once() {
    let algs = table(&BANKS);
    let (main, _) = log(&BANKS, 2);
    let evs: Vec<Vec<u8>> = (0..5).map(|i| event2(i, 0x8000_0007, &BANKS, &vec![0x40 + i as u8; 3 + i as usize])).collect();
    for pre in [0usize, 1, 3] {
        // The table at GetEventLog time, then after ExitBootServices.
        let before = final_table(&evs[..pre]);
        let snap = tcg2::final_snapshot(&before[..], &algs).unwrap();
        assert_eq!(snap, FinalSnapshot { nr_events: pre as u64, bytes: evs[..pre].iter().map(Vec::len).sum() });
        let mut after = final_table(&evs);
        after.extend([0xdd; 64]);
        let mut buf = main.clone();
        buf.resize(main.len() + tcg2::FINAL_SLACK, 0);
        let (len, lost) = tcg2::append_final(&after[..], &algs, &snap, &mut buf, main.len());
        assert!(!lost, "pre {pre}");
        let mut want = main.clone();
        for e in &evs[pre..] {
            want.extend(e);
        }
        assert_eq!(&buf[..len], &want[..], "pre {pre}");
        // Fewer events than at the snapshot: a table that went backwards.
        if pre > 0 {
            let fewer = final_table(&evs[..pre - 1]);
            assert_eq!(tcg2::append_final(&fewer[..], &algs, &snap, &mut buf, main.len()), (main.len(), true), "pre {pre}");
        }
        // Nothing new: nothing appended.
        let (len, lost) = tcg2::append_final(&before[..], &algs, &snap, &mut buf, main.len());
        assert_eq!((len, lost), (main.len(), false));
    }
}

/// Without room for every new event, whole events are appended up to the
/// slack and the log is marked truncated: never half an event.
#[test]
fn final_events_past_the_slack_truncate_whole_events() {
    let algs = table(&BANKS);
    let evs: Vec<Vec<u8>> = (0..4).map(|i| event2(i, 1, &BANKS, &[0x11; 100])).collect();
    let e = evs[0].len();
    let after = final_table(&evs);
    let snap = FinalSnapshot { nr_events: 0, bytes: 0 };
    for room in [0, 1, e - 1, e, e + 1, 2 * e + 7, 4 * e - 1] {
        let mut buf = vec![0u8; 10 + room];
        let (len, lost) = tcg2::append_final(&after[..], &algs, &snap, &mut buf, 10);
        let whole = room / e;
        assert_eq!(len, 10 + whole * e, "room {room}");
        assert!(lost, "room {room}");
        assert!(buf[len..].iter().all(|&b| b == 0), "room {room}: bytes past the last whole event");
        for (i, c) in buf[10..len].chunks(e).enumerate() {
            assert_eq!(c, &evs[i][..]);
        }
    }
    let mut buf = vec![0u8; 10 + 4 * e];
    assert_eq!(tcg2::append_final(&after[..], &algs, &snap, &mut buf, 10), (10 + 4 * e, false));
}

#[test]
fn malformed_final_events_tables_are_refused() {
    let algs = table(&BANKS);
    let evs: Vec<Vec<u8>> = (0..3).map(|i| event2(i, 1, &BANKS, b"x")).collect();
    let good = final_table(&evs);
    assert!(tcg2::final_snapshot(&good[..], &algs).is_some());
    let mut v = good.clone();
    v[0] = 2;
    assert_eq!(tcg2::final_snapshot(&v[..], &algs), None, "version");
    // More events than the table holds, up to 2^64 - 1.
    for nr in [4u64, 1 << 40, u64::MAX] {
        let mut v = good.clone();
        v[8..16].copy_from_slice(&nr.to_le_bytes());
        assert_eq!(tcg2::final_snapshot(&v[..], &algs), None, "{nr}");
    }
    assert_eq!(tcg2::final_snapshot(&good[..15], &algs), None);
    // After ExitBootServices: a table that no longer parses, or whose new
    // event is cut short, appends what is whole and marks the log.
    let snap = tcg2::final_snapshot(&final_table(&evs[..1])[..], &algs).unwrap();
    let mut buf = vec![0u8; 4096];
    let mut v = good.clone();
    v[0] = 0;
    assert_eq!(tcg2::append_final(&v[..], &algs, &snap, &mut buf, 0), (0, true));
    let (len, lost) = tcg2::append_final(&good[..good.len() - 1], &algs, &snap, &mut buf, 0);
    assert_eq!((len, lost), (evs[1].len(), true));
    let mut v = good.clone();
    v[8..16].copy_from_slice(&u64::MAX.to_le_bytes());
    let (len, lost) = tcg2::append_final(&v[..], &algs, &snap, &mut buf, 0);
    assert_eq!((len, lost), (evs[1].len() + evs[2].len(), true));
    // A snapshot past the table.
    let far = FinalSnapshot { nr_events: 1, bytes: usize::MAX };
    assert_eq!(tcg2::append_final(&good[..], &algs, &far, &mut buf, 0), (0, true));
    // A length past the buffer appends nothing.
    assert_eq!(tcg2::append_final(&good[..], &algs, &snap, &mut buf, 5000), (5000, true));
}

#[test]
fn the_flags_and_limits_are_the_abis() {
    use fl4_abi::consts::{bootinfo_header, tpm_event_log_flag};
    assert_eq!(bootinfo_header::TPM_EVENT_LOG, 12);
    assert_eq!(tcg2::TRUNCATED, tpm_event_log_flag::TRUNCATED);
    assert_eq!(tcg2::TCG_1_2, tpm_event_log_flag::TCG_1_2);
    assert_eq!(tcg2::MAX_EVENT_LOG as u64, fl4_bootinfo::MAX_TPM_LOG);
    assert!(tcg2::FINAL_SLACK < tcg2::MAX_EVENT_LOG);
    let mboot = include_str!("../../crates/fl4-kernel/src/mboot.rs");
    assert!(mboot.contains("pub const MAX_TPM_LOG: u64 = 1 << 20;"));
    assert!(mboot.contains("pub const MB2_TAG_TPM_EVENT_LOG: u32 = 0x464c_3401;"));
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("const MB2_TAG_TPM_EVENT_LOG: u32 = 0x464c_3401;"));
    let h = include_str!("../../libsel4/include/sel4/bootinfo_types.h");
    assert!(h.contains("SEL4_BOOTINFO_HEADER_TPM_EVENT_LOG      = 12,"));
    assert!(h.contains("#define seL4_TpmEventLog_Truncated (1ul << 0)"));
    assert!(h.contains("#define seL4_TpmEventLog_Tcg12     (1ul << 1)"));
    let t = include_str!("../../crates/fl4-efi/src/tcg2.rs");
    assert!(t.contains("Guid(0x607f_766c, 0x7455, 0x42be, [0x93, 0x0b, 0xe4, 0xd7, 0x6d, 0xb2, 0x72, 0x0f])"));
    assert!(t.contains("Guid(0x1e2e_d096, 0x30e2, 0x4254, [0xbd, 0x89, 0x86, 0x3b, 0xbe, 0xf8, 0x23, 0x25])"));
}

/// A missing or broken log never stops the boot: `collect` has no `fail`.
#[test]
fn collecting_the_log_cannot_fail_the_boot() {
    let t = include_str!("../../crates/fl4-efi/src/tcg2.rs");
    let efi = &t[t.find("mod efi {").expect("efi glue")..];
    assert!(!efi.contains("fail("));
    assert!(!efi.contains("panic!") && !efi.contains(".unwrap()") && !efi.contains(".expect("));
    // finish runs without boot services: no console either.
    let finish = &efi[efi.find("pub fn finish(").unwrap()..];
    let finish = &finish[..finish.find("\n        }\n").unwrap()];
    assert!(!finish.contains("say!") && !finish.contains("bs()"));
}

/// x86: the tag goes among the fixed tags (before `tags_end`), the copy
/// before ExitBootServices, the final events after it and before the jump.
#[test]
fn the_x86_loader_finishes_the_log_after_exit_boot_services() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let body = &x86[x86.find("pub(super) fn boot(").expect("boot")..];
    let at = |s: &str| body.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("tcg2::collect()") < at("let len = "));
    assert!(at("t.copy_main(tpm_dst)") < at("(bs().exit_boot_services)"));
    assert!(at("info.tag(MB2_TAG_TPM_EVENT_LOG, 24)") < at("let tags_end = info.used"));
    let finish = at("t.finish(tpm_dst)");
    assert!(at("(bs().exit_boot_services)") < finish);
    assert!(finish < at("\"cli\","));
}

/// AArch64: the copy before ExitBootServices, the final events after it,
/// before the boot record and the log are cleaned to memory.
#[test]
fn the_aarch64_loader_finishes_the_log_before_cleaning() {
    let lib = include_str!("../../crates/fl4-efi/src/lib.rs");
    let body = &lib[lib.find("pub unsafe fn start_default(").expect("start_default")..];
    let at = |s: &str| body.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("tcg2::collect()") < at("(bs().exit_boot_services)"));
    assert!(at("t.copy_main(pa)") < at("(bs().get_memory_map)"));
    let finish = at("t.finish(*pa)");
    assert!(at("(bs().exit_boot_services)") < finish);
    assert!(finish < at("clean(region, region_len)"));
    assert!(at("clean(bi.tpm_log_paddr, bi.tpm_log_size.div_ceil(PAGE) * PAGE)") < at("enter(region, bi_off)"));
    assert!(at("write_bytes(pa as *mut u8, 0, (pages * PAGE) as usize)") < at("t.copy_main(pa)"));
}

/// `EFI_TCG2_EVENT` (TCG EFI Protocol §6.6), packed: Size covers the whole
/// event, HeaderSize the 14-byte `EFI_TCG2_EVENT_HEADER` (header size,
/// version, PCR index, event type), then the event data.
#[test]
fn a_tcg2_event_has_the_packed_layout() {
    assert_eq!((tcg2::TCG2_HEADER_LEN, tcg2::TCG2_EVENT_FIXED), (14, 18));
    assert_eq!((tcg2::PCR_BOOT_FILES, tcg2::EV_IPL), (9, 0xd));
    let mut buf = [0xaau8; 64];
    let n = tcg2::tcg2_event(&mut buf, tcg2::PCR_BOOT_FILES, tcg2::EV_IPL, b"rootserver");
    assert_eq!(n, 18 + 10);
    assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 28);
    assert_eq!(u32::from_le_bytes(buf[4..8].try_into().unwrap()), 14);
    assert_eq!(u16::from_le_bytes(buf[8..10].try_into().unwrap()), 1);
    assert_eq!(u32::from_le_bytes(buf[10..14].try_into().unwrap()), 9);
    assert_eq!(u32::from_le_bytes(buf[14..18].try_into().unwrap()), 0xd);
    assert_eq!(&buf[18..28], b"rootserver");
    assert_eq!(buf[28], 0xaa, "nothing written past the event");
    // Event data that does not fit is cut to the buffer.
    let mut small = [0u8; 32];
    let n = tcg2::tcg2_event(&mut small, 9, 0xd, &[b'x'; 100]);
    assert_eq!(n, 32);
    assert_eq!(u32::from_le_bytes(small[0..4].try_into().unwrap()), 32);
    assert_eq!(&small[18..], &[b'x'; 14]);
    // No event data: a bare header.
    let n = tcg2::tcg2_event(&mut small, 9, 0xd, b"");
    assert_eq!((n, u32::from_le_bytes(small[0..4].try_into().unwrap())), (18, 18));
}

/// HashLogExtendEvent's result: success, or `EFI_VOLUME_FULL` (the PCR was
/// extended, only the log is full); anything else stops the boot.
#[test]
fn a_tpm_measurement_firmware_refuses_is_an_error() {
    assert_eq!(tcg2::VOLUME_FULL, (1 << 63) | 11);
    assert_eq!(tcg2::measure_status(0), Ok(()));
    assert_eq!(tcg2::measure_status(tcg2::VOLUME_FULL), Ok(()));
    for r in [1, (1 << 63) | 1, (1 << 63) | 2, (1 << 63) | 3, (1 << 63) | 7, (1 << 63) | 9, (1 << 63) | 14, 11, u64::MAX] {
        assert!(tcg2::measure_status(r).is_err(), "{r:#x}");
    }
}

fn desc(role: &[u8], path: &[u8], len: u64) -> Vec<u8> {
    let mut buf = [0u8; tcg2::DESC_MAX];
    let n = tcg2::file_descriptor(&mut buf, role, path, len);
    buf[..n].to_vec()
}

/// The descriptor binds role, length and path, in that order, after a
/// fixed prefix.
#[test]
fn a_file_descriptor_is_prefix_role_length_path() {
    let d = desc(b"module", b"\\efi\\m.elf", 0x1234);
    let mut want = b"fl4-efi\0module\0".to_vec();
    want.extend_from_slice(&0x1234u64.to_le_bytes());
    want.extend_from_slice(b"\\efi\\m.elf");
    assert_eq!(d, want);
}

/// Same path or same bytes in another role, at another length or from
/// another path: always another descriptor, so another PCR value.
#[test]
fn file_descriptors_separate_role_length_and_path() {
    let all = [
        desc(b"rootserver", b"\\a", 10),
        desc(b"module", b"\\a", 10),
        desc(b"cmdline", b"\\a", 10),
        desc(b"module", b"\\b", 10),
        desc(b"module", b"\\a", 11),
        desc(b"module", b"", 10),
        desc(b"cmdline", b"", 10),
        // A role that is a prefix of another, the rest moved into the path.
        desc(b"root", b"server\\a", 10),
    ];
    for (i, a) in all.iter().enumerate() {
        for b in &all[i + 1..] {
            assert_ne!(a, b);
        }
    }
}

/// A 0-byte file still has a descriptor to extend (firmware refuses to
/// hash nothing), with its length 0 in it.
#[test]
fn an_empty_file_has_a_nonempty_descriptor() {
    let d = desc(b"module", b"", 0);
    assert_eq!(d.len(), b"fl4-efi\0module\0".len() + 8);
    assert_eq!(&d[d.len() - 8..], &[0; 8]);
    assert_ne!(d, desc(b"rootserver", b"", 0));
}

/// A path longer than the buffer is cut; the prefix, role and the whole
/// length stay, and nothing panics.
#[test]
fn a_long_path_is_cut_but_keeps_role_and_length() {
    let path = [b'p'; 4096];
    let d = desc(b"rootserver", &path, u64::MAX);
    assert_eq!(d.len(), tcg2::DESC_MAX);
    let head = b"fl4-efi\0rootserver\0".len();
    assert_eq!(&d[..head], b"fl4-efi\0rootserver\0");
    assert_eq!(&d[head..head + 8], &u64::MAX.to_le_bytes());
    assert!(d[head + 8..].iter().all(|&c| c == b'p'));
    // Any path read_file opens (255 bytes) fits whole.
    assert!(tcg2::DESC_MAX >= head + 8 + 255);
    let mut tiny = [0u8; 27];
    assert_eq!(tcg2::file_descriptor(&mut tiny, b"rootserver", &path, 1), 27);
}

fn tcg2_efi() -> &'static str {
    let t = include_str!("../../crates/fl4-efi/src/tcg2.rs");
    &t[t.find("mod efi {").expect("efi glue")..]
}

fn body<'a>(src: &'a str, sig: &str, end: &str) -> &'a str {
    let f = &src[src.find(sig).unwrap_or_else(|| panic!("{sig}"))..];
    &f[..f.find(end).unwrap()]
}

/// `EFI_TCG2_PROTOCOL`'s first three members, in the spec's order.
#[test]
fn the_tcg2_protocol_has_hash_log_extend_event_third() {
    let p = body(tcg2_efi(), "struct Tcg2Protocol {", "\n    }\n");
    let at = |s: &str| p.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("get_capability: usize,") < at("get_event_log: extern \"efiapi\" fn("));
    assert!(at("get_event_log: extern \"efiapi\" fn(") < at("hash_log_extend_event: extern \"efiapi\" fn(*mut Tcg2Protocol, u64, u64, u64, *const u8) -> Status,"));
}

/// No TPM: nothing to measure. A TPM: the descriptor first, the contents
/// only when there are any, both checked; a 0-length extension is never
/// handed to firmware.
#[test]
fn measuring_a_file_extends_the_descriptor_then_nonempty_contents() {
    let efi = tcg2_efi();
    let b = body(efi, "pub fn measure_bytes(", "\n    }\n");
    let at = |s: &str| b.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("let Some(tcg) = protocol() else { return Ok(()) };") < at("if len == 0 {"));
    assert!(at("if len == 0 {") < at("hash_log_extend_event)("));
    assert!(at("tcg2_event(&mut event, pcr, EV_IPL, label)") < at("hash_log_extend_event)("));
    assert!(b.trim_end().ends_with("measure_status(r as u64)"));
    let f = body(efi, "pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64)", "\n    }\n");
    let at = |s: &str| f.find(s).unwrap_or_else(|| panic!("{s}"));
    assert!(at("if protocol().is_none() {\n            return Ok(());") < at("file_descriptor("));
    let d = at("measure_bytes(PCR_BOOT_FILES, desc, desc.as_ptr() as u64, n as u64)?;");
    let guard = at("if len > 0 {");
    let c = at("measure_bytes(PCR_BOOT_FILES, desc, pa, len)?;");
    assert!(at("file_descriptor(&mut desc, role, path, len)") < d && d < guard && guard < c);
}

/// x86: every `rootserver=` and `module=` file extends PCR 9 outside a TD
/// (RTMR[2] instead in a TD, which ignores any TPM), and a refused
/// measurement stops the boot. All before the log is collected in `boot`.
#[test]
fn the_x86_loader_measures_option_files_into_pcr9() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let files = body(x86, "fn boot_files<'a>(", "\n}\n");
    for role in ["rootserver", "module"] {
        let arm = body(files, &format!("strip_prefix(b\"{role}=\")"), "files[");
        let at = |s: &str| arm.find(s).unwrap_or_else(|| panic!("{role}: {s}"));
        let cc = at(&format!("if measure {{\n                ccel::measure_file(b\"{role}\", path, pa, len);\n            }} else {{"));
        let tpm = at(&format!("}} else {{\n                tcg2::measure_file(b\"{role}\", path, pa, len).unwrap_or_else(|e| fail(e));\n            }}"));
        assert!(at("read_file(li, path)") < cc && cc < tpm);
    }
    assert_eq!(files.matches("tcg2::measure_file(").count(), 2);
    let start = body(x86, "pub unsafe fn start_default(", "\n}\n");
    assert!(start.find("boot_files(li, &opts, measure)").unwrap() < start.find("boot(image, ").unwrap());
    let boot = &x86[x86.find("pub(super) fn boot(").unwrap()..];
    assert!(!boot[..boot.find("tcg2::collect()").unwrap()].contains("measure_file("));
    assert!(boot.contains("let tpm = if shared == 0 { tcg2::collect() } else { None };"), "no TPM log in a TD");
}

/// AArch64: the options' modules, root task and kernel command line all
/// extend PCR 9 (fail-closed) before the log is collected.
#[test]
fn the_aarch64_loader_measures_option_files_and_cmdline_into_pcr9() {
    let lib = include_str!("../../crates/fl4-efi/src/lib.rs");
    let body = &lib[lib.find("pub unsafe fn start_default(").expect("start_default")..];
    let at = |s: &str| body.find(s).unwrap_or_else(|| panic!("{s}"));
    let collect = at("tcg2::collect()");
    let module = at("tcg2::measure_file(b\"module\", p, pa, size).unwrap_or_else(|e| fail(e));");
    assert!(at("strip_prefix(b\"module=\")") < module);
    let root = at("tcg2::measure_file(b\"rootserver\", p, pa, size).unwrap_or_else(|e| fail(e));");
    assert!(at("let root_file: &[u8] = match root_path {") < root);
    let cmdline = at("if cl > 0 {\n        tcg2::measure_file(b\"cmdline\", b\"\", bi.cmdline.as_ptr() as u64, cl as u64).unwrap_or_else(|e| fail(e));");
    // After the last word was added to the command line.
    assert!(at("cl += w.len();") < cmdline);
    for m in [module, root, cmdline] {
        assert!(m < collect);
    }
    assert!(root < at("load_segments(root_file, &rl, root_pa)"));
}

/// TDX poisons a TPM firmware exposes: an error `EV_SEPARATOR` into each
/// static locality-0 PCR.
#[test]
fn the_tdx_poison_is_an_error_separator_in_pcrs_0_to_15() {
    assert_eq!(tcg2::EV_SEPARATOR, 4);
    assert_eq!(tcg2::SEPARATOR_ERROR, [0xff; 4]);
    assert_eq!(tcg2::POISON_PCR_COUNT, 16);
    let mut buf = [0xaau8; tcg2::TCG2_EVENT_FIXED + 4];
    for pcr in 0..tcg2::POISON_PCR_COUNT {
        let n = tcg2::tcg2_event(&mut buf, pcr, tcg2::EV_SEPARATOR, &tcg2::SEPARATOR_ERROR);
        assert_eq!(n, 22);
        assert_eq!(u32::from_le_bytes(buf[0..4].try_into().unwrap()), 22);
        assert_eq!(u32::from_le_bytes(buf[4..8].try_into().unwrap()), 14);
        assert_eq!(u16::from_le_bytes(buf[8..10].try_into().unwrap()), 1);
        assert_eq!(u32::from_le_bytes(buf[10..14].try_into().unwrap()), pcr);
        assert_eq!(u32::from_le_bytes(buf[14..18].try_into().unwrap()), 4);
        assert_eq!(&buf[18..22], &[0xff; 4]);
    }
}

/// A poison extension firmware refuses stops the boot; a full log does not.
#[test]
fn a_poison_extension_firmware_refuses_is_an_error() {
    assert_eq!(tcg2::poison_status(0), Ok(()));
    assert_eq!(tcg2::poison_status(tcg2::VOLUME_FULL), Ok(()));
    for r in [1, (1 << 63) | 1, (1 << 63) | 2, (1 << 63) | 3, (1 << 63) | 7, (1 << 63) | 9, (1 << 63) | 14, 11, u64::MAX] {
        assert_eq!(tcg2::poison_status(r), Err("cannot poison TPM PCRs in TDX"), "{r:#x}");
    }
}

/// No TPM: nothing to poison. A TPM: every PCR 0..16 gets the separator,
/// each extension checked, then the console says so.
#[test]
fn poisoning_extends_every_static_pcr_fail_closed() {
    let p = body(tcg2_efi(), "pub fn poison() -> Result<(), &'static str> {", "\n    }\n");
    let at = |s: &str| p.find(s).unwrap_or_else(|| panic!("{s}"));
    let none = at("let Some(tcg) = protocol() else { return Ok(()) };");
    let l = at("for pcr in 0..POISON_PCR_COUNT {");
    let ev = at("tcg2_event(&mut event, pcr, EV_SEPARATOR, &sep);");
    let ext = at("((*tcg).hash_log_extend_event)(tcg, 0, sep.as_ptr() as u64, sep.len() as u64, event.as_ptr())");
    let chk = at("poison_status(r as u64)?;");
    let said = at("say!(\"fl4-efi: TDX guest, poisoned TPM PCRs 0..15\");");
    assert!(none < at("let sep = SEPARATOR_ERROR;") && none < l);
    assert!(l < ev && ev < ext && ext < chk && chk < said);
    assert!(p.trim_end().ends_with("Ok(())"));
}

/// x86: a TD poisons the TPM in `boot` (so for `start_default` and
/// `Firmware::boot` alike), before ExitBootServices, and collects no TPM
/// log.
#[test]
fn the_x86_loader_poisons_the_tpm_in_a_td() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let boot = &x86[x86.find("pub(super) fn boot(").unwrap()..];
    let at = |s: &str| boot.find(s).unwrap_or_else(|| panic!("{s}"));
    let poison = at("if shared != 0 {\n        tcg2::poison().unwrap_or_else(|e| fail(e));\n    }");
    assert!(at("let shared = if mask == 0 { tdx_shared_mask() } else { 0 };") < poison);
    assert!(poison < at("let tpm = if shared == 0 { tcg2::collect() } else { None };"));
    assert!(poison < at("(bs().exit_boot_services)"));
    assert_eq!(x86.matches("tcg2::poison()").count(), 1);
    let fw = include_str!("../../crates/fl4-efi/src/firmware.rs");
    assert!(fw.contains("x86::boot(self.image, kernel, &files[..modules.len()], cmdline)"));
    let b = body(fw, "pub unsafe fn boot(&self, kernel: &[u8], modules: &[(&[u8], &[u8])]) -> ! {", "\n    }\n");
    assert!(b.contains("unsafe { self.boot_with_cmdline(kernel, modules, c\"\") }"), "boot is boot_with_cmdline with none");
    assert_eq!(fw.matches("x86::boot(").count(), 1, "only boot_with_cmdline enters x86::boot");
}
