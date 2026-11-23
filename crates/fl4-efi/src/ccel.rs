//! The UEFI confidential-computing event log (UEFI 2.10 §38,
//! `EFI_CC_MEASUREMENT_PROTOCOL`; ACPI 6.5 §5.2.35, the `CCEL` table): an
//! Intel TDX guest's RTMR measurements, in the crypto agile format of the
//! TPM event log and parsed by tcg2.rs. It is collected beside the TPM log
//! and independently of it.
//!
//! As in tcg2.rs the parsing is plain functions over a byte source, so
//! host tests run it (xtask/tests/efi_ccel.rs). A guest whose log is
//! missing or unusable boots without the record.

use crate::tcg2::{event2_len, spec_id, AlgTable, Log, Mem, EV_IPL, MAX_EVENT_LOG};
/// `EFI_VOLUME_FULL`: extended, but the log had no room for the event.
pub use crate::tcg2::VOLUME_FULL;

/// The `CCEL` table: its fixed part, through the log area's address.
const CCEL_LEN: usize = 56;
/// CC type in the `CCEL` table (ACPI 6.5 table 5.175).
const CC_TYPE_TDX: u8 = 2;
/// The CC measurement register RTMR[2] is (`EFI_CC_MR_INDEX`: 0 is MRTD, 1
/// is RTMR[0]).
pub const MR_INDEX_RTMR2: u32 = 3;
/// `EFI_CC_EVENT_HEADER`, packed: size, version, MR index, event type.
const CC_HEADER_LEN: usize = 14;
/// `EFI_CC_EVENT`: its size field, then the header, then the event data.
const CC_EVENT_FIXED: usize = 4 + CC_HEADER_LEN;

/// The log area (LASA, LAML) of a `CCEL` table in `m`, for a TDX guest.
pub fn ccel_area(m: &(impl Mem + ?Sized)) -> Option<(u64, u64)> {
    if m.bytes(0, 4)? != b"CCEL" {
        return None;
    }
    let len = u32::from_le_bytes(m.bytes(4, 4)?.try_into().ok()?) as usize;
    if !(CCEL_LEN..=4096).contains(&len) {
        return None;
    }
    let table = m.bytes(0, len)?;
    if table.iter().fold(0u8, |s, b| s.wrapping_add(*b)) != 0 || table[36] != CC_TYPE_TDX {
        return None;
    }
    let laml = u64::from_le_bytes(table[40..48].try_into().ok()?);
    let lasa = u64::from_le_bytes(table[48..56].try_into().ok()?);
    (lasa != 0 && laml != 0).then_some((lasa, laml))
}

/// Walk a crypto agile log in `m`, of at most `limit` bytes, to its end: the
/// first entry that is zeroed memory. Returns it and whether events may be
/// missing: the walk stopped at something that is neither that nor the end
/// of the area.
pub fn walk_log(m: &(impl Mem + ?Sized), limit: usize) -> Option<(Log, bool)> {
    let (mut off, algs): (usize, AlgTable) = spec_id(m)?;
    if off > limit {
        return None;
    }
    while let Some(l) = event2_len(m, off, &algs) {
        match off.checked_add(l) {
            Some(end) if end <= limit => off = end,
            _ => break,
        }
    }
    // An area can end less than one entry header after the last event.
    let rem = (limit - off).min(16);
    let clean = m.bytes(off, rem).is_some_and(|b| b.iter().all(|&x| x == 0));
    Some((Log { len: off, algs }, !clean))
}

/// Write an `EFI_CC_EVENT` for code loaded from `name` into `buf`, for
/// RTMR[2]; returns its length. A name that does not fit is cut: the event
/// data only labels the digest.
pub fn cc_event(buf: &mut [u8], name: &[u8]) -> usize {
    let n = name.len().min(buf.len() - CC_EVENT_FIXED);
    let size = CC_EVENT_FIXED + n;
    buf[0..4].copy_from_slice(&(size as u32).to_le_bytes());
    buf[4..8].copy_from_slice(&(CC_HEADER_LEN as u32).to_le_bytes());
    buf[8..10].copy_from_slice(&1u16.to_le_bytes());
    buf[10..14].copy_from_slice(&MR_INDEX_RTMR2.to_le_bytes());
    buf[14..18].copy_from_slice(&EV_IPL.to_le_bytes());
    buf[CC_EVENT_FIXED..size].copy_from_slice(&name[..n]);
    size
}

/// Which log to use. The protocol's when it can follow events to the end;
/// without usable final events the `CCEL` table can (firmware appends to it
/// in place), and the protocol's main log is the fallback if there is no
/// table.
pub fn choose<T>(protocol: Option<T>, complete: impl Fn(&T) -> bool, table: impl FnOnce() -> Option<T>) -> Option<T> {
    match protocol {
        Some(p) if complete(&p) => Some(p),
        Some(p) => table().or(Some(p)),
        None => table(),
    }
}

/// Whether a boot file was measured into RTMR[2] and may boot: there must
/// be an `EFI_CC_MEASUREMENT_PROTOCOL`, and its HashLogExtendEvent must have
/// extended the register (success, or `EFI_VOLUME_FULL`: only the log is
/// full).
pub fn measure_status(has_protocol: bool, status: u64) -> Result<(), &'static str> {
    if !has_protocol {
        return Err("EFI_CC_MEASUREMENT_PROTOCOL unavailable for RTMR[2] measurement");
    }
    match status {
        0 | VOLUME_FULL => Ok(()),
        _ => Err("cannot measure a boot file into RTMR[2]"),
    }
}

/// The largest log area taken.
pub fn area_limit(laml: u64) -> usize {
    laml.min(MAX_EVENT_LOG as u64) as usize
}

#[cfg(not(test))]
pub use efi::*;

/// What runs on firmware.
#[cfg(not(test))]
mod efi {
    use super::*;
    use crate::tcg2::{file_descriptor, final_snapshot, main_log, Raw, TpmLog, DESC_MAX, EFI_TCG2_EVENT_LOG_FORMAT_TCG_2, TCG_1_2, TRUNCATED};
    use crate::{bs, config_table, fail, print, Con, Guid, Status, ACPI_10, ACPI_20, SUCCESS};

    pub const EFI_CC_MEASUREMENT_PROTOCOL_GUID: Guid = Guid(0x9675_1a3d, 0x72f4, 0x41a6, [0xa7, 0x94, 0xed, 0x5d, 0x0e, 0x67, 0xae, 0x6b]);
    pub const EFI_CC_FINAL_EVENTS_TABLE_GUID: Guid = Guid(0xdd4a_4648, 0x2de7, 0x4665, [0x96, 0x4d, 0x21, 0xd9, 0xef, 0x5f, 0xb4, 0x46]);
    /// `EFI_CC_MEASUREMENT_PROTOCOL` up to HashLogExtendEvent.
    #[repr(C)]
    struct CcProtocol {
        get_capability: usize,
        get_event_log: extern "efiapi" fn(*mut CcProtocol, u32, *mut u64, *mut u64, *mut u8) -> Status,
        hash_log_extend_event: extern "efiapi" fn(*mut CcProtocol, u64, u64, u64, *const u8) -> Status,
    }

    fn protocol() -> Option<*mut CcProtocol> {
        let mut p = core::ptr::null_mut();
        let r = (bs().locate_protocol)(&EFI_CC_MEASUREMENT_PROTOCOL_GUID, core::ptr::null(), &mut p);
        (r == SUCCESS && !p.is_null()).then_some(p as *mut CcProtocol)
    }

    /// Measure a file the load options named (`role`: rootserver or
    /// module) into RTMR[2], so that a quote covers it: its descriptor
    /// (tcg2.rs `file_descriptor`: role, length, path), then its contents
    /// in place unless it is empty (firmware refuses to hash nothing).
    /// Called only in a TD: a file that cannot be measured is not booted,
    /// and neither is one when firmware offers no
    /// `EFI_CC_MEASUREMENT_PROTOCOL` (`measure_status`).
    pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64) {
        let Some(cc) = protocol() else {
            fail(measure_status(false, 0).unwrap_err());
        };
        let mut desc = [0u8; DESC_MAX];
        let n = file_descriptor(&mut desc, role, path, len);
        let desc = &desc[..n];
        let mut event = [0u8; CC_EVENT_FIXED + DESC_MAX];
        cc_event(&mut event, desc);
        let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, desc.as_ptr() as u64, n as u64, event.as_ptr()) };
        if let Err(e) = measure_status(true, r as u64) {
            fail(e);
        }
        if len > 0 {
            let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr()) };
            if let Err(e) = measure_status(true, r as u64) {
                fail(e);
            }
        }
    }

    /// `EFI_UNSUPPORTED`: no `EFI_CC_MEASUREMENT_PROTOCOL`.
    const UNSUPPORTED: Status = (1 << 63) | 3;
    /// `EFI_INVALID_PARAMETER`: firmware refuses to hash nothing.
    const INVALID_PARAMETER: Status = (1 << 63) | 2;

    /// Measure caller-built bytes at `(pa, len)` into RTMR[2] as one event
    /// named `name`, so that a quote covers them. Called only in a TD: bytes
    /// that cannot be measured must not be booted, and neither must they
    /// when firmware offers no `EFI_CC_MEASUREMENT_PROTOCOL`
    /// (`measure_status`). The error, said on the console, is the caller's
    /// to act on: it must not boot them.
    pub fn measure_bytes(name: &[u8], pa: u64, len: u64) -> Result<(), Status> {
        let Some(cc) = protocol() else {
            say!("fl4-efi: {}", measure_status(false, 0).unwrap_err());
            return Err(UNSUPPORTED);
        };
        if len == 0 {
            say!("fl4-efi: refusing to measure empty bytes into RTMR[2]");
            return Err(INVALID_PARAMETER);
        }
        let mut event = [0u8; CC_EVENT_FIXED + 256];
        cc_event(&mut event, name);
        let r = unsafe { ((*cc).hash_log_extend_event)(cc, 0, pa, len, event.as_ptr()) };
        measure_status(true, r as u64).map_err(|e| {
            say!("fl4-efi: {}", e);
            r
        })
    }

    /// The log firmware keeps, found before ExitBootServices.
    pub enum CcLog {
        /// From the protocol, with the final events table.
        Protocol(TpmLog),
        /// From the `CCEL` table: firmware keeps appending in place.
        Table { lasa: u64, limit: usize, log: Log, flags: u64 },
    }

    impl CcLog {
        /// Bytes to set aside for the copy.
        pub fn capacity(&self) -> u64 {
            match self {
                CcLog::Protocol(t) => t.capacity(),
                CcLog::Table { limit, .. } => *limit as u64,
            }
        }

        /// The log so far (before ExitBootServices), to `dst`.
        pub fn copy_main(&self, dst: u64) {
            match self {
                CcLog::Protocol(t) => t.copy_main(dst),
                CcLog::Table { lasa, log, .. } => unsafe {
                    core::ptr::copy_nonoverlapping(*lasa as *const u8, dst as *mut u8, log.len)
                },
            }
        }

        /// The size and flags of the copy at `dst` so far.
        pub fn record(&self) -> (u64, u64) {
            match self {
                CcLog::Protocol(t) => t.record(),
                CcLog::Table { log, flags, .. } => (log.len as u64, *flags),
            }
        }

        /// After ExitBootServices: bring the copy at `dst` up to date.
        /// Returns its size and flags. Uses no boot services and does not
        /// print.
        pub fn finish(&self, dst: u64) -> (u64, u64) {
            match self {
                CcLog::Protocol(t) => t.finish(dst),
                CcLog::Table { lasa, limit, log, flags } => {
                    // The area is firmware-reserved and still mapped: read
                    // it again, with what ExitBootServices logged.
                    let m = Raw { base: *lasa, limit: *limit };
                    match walk_log(&m, *limit) {
                        Some((now, lost)) if now.len >= log.len => {
                            unsafe { core::ptr::copy_nonoverlapping(*lasa as *const u8, dst as *mut u8, now.len) };
                            (now.len as u64, flags | if lost { TRUNCATED } else { 0 })
                        }
                        _ => (log.len as u64, flags | TRUNCATED),
                    }
                }
            }
        }
    }

    fn from_protocol(cc: *mut CcProtocol) -> Option<CcLog> {
        let (mut location, mut last, mut truncated) = (0u64, 0u64, 0u8);
        let r = unsafe { ((*cc).get_event_log)(cc, EFI_TCG2_EVENT_LOG_FORMAT_TCG_2, &mut location, &mut last, &mut truncated) };
        if r != SUCCESS || location == 0 || last == 0 {
            return None;
        }
        // Right after GetEventLog: the final events table holds what the
        // log already does.
        let final_table = config_table(EFI_CC_FINAL_EVENTS_TABLE_GUID);
        let m = Raw { base: location, limit: MAX_EVENT_LOG };
        let log = main_log(&m, location, last, false)?;
        let mut flags = if truncated != 0 { TRUNCATED } else { 0 };
        let mut snap = None;
        if final_table != 0 {
            snap = final_snapshot(&Raw { base: final_table, limit: MAX_EVENT_LOG }, &log.algs);
            if snap.is_none() {
                flags |= TRUNCATED;
            }
        } else {
            flags |= TRUNCATED;
        }
        debug_assert!(flags & TCG_1_2 == 0);
        say!("fl4-efi: CC event log {:#x} bytes at {:#x}{}", log.len, location, if snap.is_some() { ", final events table" } else { "" });
        Some(CcLog::Protocol(TpmLog::new(location, log, flags, final_table, snap)))
    }

    /// The `CCEL` table's log area, through the RSDP in the system table.
    fn find_ccel() -> Option<(u64, u64)> {
        let rsdp = match config_table(ACPI_20) {
            0 => config_table(ACPI_10),
            p => p,
        };
        if rsdp == 0 {
            return None;
        }
        let r = Raw { base: rsdp, limit: 36 };
        let revision = r.bytes(15, 1)?[0];
        let (root, entry) = if revision >= 2 {
            match u64::from_le_bytes(r.bytes(24, 8)?.try_into().ok()?) {
                0 => (u32::from_le_bytes(r.bytes(16, 4)?.try_into().ok()?) as u64, 4),
                x => (x, 8),
            }
        } else {
            (u32::from_le_bytes(r.bytes(16, 4)?.try_into().ok()?) as u64, 4)
        };
        if root == 0 {
            return None;
        }
        let head = Raw { base: root, limit: 36 };
        let len = u32::from_le_bytes(head.bytes(4, 4)?.try_into().ok()?) as usize;
        if !(36..=1 << 16).contains(&len) {
            return None;
        }
        let t = Raw { base: root, limit: len };
        for i in 0..(len - 36) / entry {
            let e = t.bytes(36 + i * entry, entry)?;
            let table = if entry == 8 {
                u64::from_le_bytes(e.try_into().ok()?)
            } else {
                u32::from_le_bytes(e.try_into().ok()?) as u64
            };
            if table == 0 {
                continue;
            }
            let header = Raw { base: table, limit: 8 };
            if header.bytes(0, 4)? != b"CCEL" {
                continue;
            }
            let n = u32::from_le_bytes(header.bytes(4, 4)?.try_into().ok()?) as usize;
            if let Some(area) = ccel_area(&Raw { base: table, limit: n.min(4096) }) {
                return Some(area);
            }
        }
        None
    }

    fn from_table() -> Option<CcLog> {
        let (lasa, laml) = find_ccel()?;
        let limit = area_limit(laml);
        let (log, lost) = walk_log(&Raw { base: lasa, limit }, limit)?;
        say!("fl4-efi: CC event log {:#x} bytes at {:#x} (CCEL table)", log.len, lasa);
        Some(CcLog::Table { lasa, limit, log, flags: if lost { TRUNCATED } else { 0 } })
    }

    /// The CC event log, from the protocol or the ACPI table (`choose`).
    /// Never fails the boot: anything else is a line on the console.
    pub fn collect() -> Option<CcLog> {
        let complete = |l: &CcLog| matches!(l, CcLog::Protocol(t) if t.has_final_events());
        let log = choose(protocol().and_then(from_protocol), complete, from_table);
        if log.is_none() {
            say!("fl4-efi: no usable CC event log");
        }
        log
    }
}
