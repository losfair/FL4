//! The UEFI TPM 2.0 event log (TCG EFI Protocol Specification, rev. 1.0
//! v0.13 §6.4, §6.6, §7; TCG PC Client Platform Firmware Profile §10):
//! the log `EFI_TCG2_PROTOCOL.GetEventLog` names, copied out of boot
//! services memory before ExitBootServices, and the events firmware logs
//! in `EFI_TCG2_FINAL_EVENTS_TABLE` after the copy (ExitBootServices
//! itself measures), appended once boot services are gone.
//!
//! The parsing is plain functions over a byte source (`Mem`), so host
//! tests run it (xtask/tests/efi_tcg2.rs). Every length comes from
//! firmware memory: arithmetic is checked, nothing is read past the
//! event a record's own fields describe, and a log that does not parse is
//! no log. A machine without a TPM, or with one whose log is unusable,
//! boots without the record.

/// The largest log handed to the kernel (and the most read from firmware).
pub const MAX_EVENT_LOG: usize = 1 << 20;
/// Room left after the main log for the events firmware adds to the final
/// events table before and during ExitBootServices (within `MAX_EVENT_LOG`).
pub const FINAL_SLACK: usize = 64 << 10;
/// `EFI_TCG2_EVENT_LOG_FORMAT`s.
pub const EFI_TCG2_EVENT_LOG_FORMAT_TCG_1_2: u32 = 1;
pub const EFI_TCG2_EVENT_LOG_FORMAT_TCG_2: u32 = 2;
/// The record's flags (fl4_abi `tpm_event_log_flag`, libsel4
/// `seL4_TpmEventLog_*`): events are missing at the end; the log is in the
/// SHA-1 TCG 1.2 format rather than TCG 2.0 crypto agile.
pub const TRUNCATED: u64 = 1 << 0;
pub const TCG_1_2: u64 = 1 << 1;

/// Digest algorithms a Spec ID event may list.
pub const MAX_ALGS: usize = 16;
/// `EV_NO_ACTION`, the Spec ID event's type.
const EV_NO_ACTION: u32 = 3;
const SPEC_ID_SIGNATURE: &[u8; 16] = b"Spec ID Event03\0";
/// A legacy `TCG_PCR_EVENT`'s fixed part: PCR index, event type, SHA-1
/// digest, event size.
const PCR_EVENT_LEN: usize = 32;
/// `EFI_TCG2_FINAL_EVENTS_TABLE`'s header: version, number of events.
const FINAL_HEADER: usize = 16;

/// Bytes at an offset of a source, if they all lie inside it.
pub trait Mem {
    fn bytes(&self, off: usize, n: usize) -> Option<&[u8]>;
}

impl Mem for [u8] {
    fn bytes(&self, off: usize, n: usize) -> Option<&[u8]> {
        self.get(off..off.checked_add(n)?)
    }
}

fn rd16(m: &(impl Mem + ?Sized), off: usize) -> Option<u16> {
    Some(u16::from_le_bytes(m.bytes(off, 2)?.try_into().ok()?))
}

fn rd32(m: &(impl Mem + ?Sized), off: usize) -> Option<u32> {
    Some(u32::from_le_bytes(m.bytes(off, 4)?.try_into().ok()?))
}

fn rd64(m: &(impl Mem + ?Sized), off: usize) -> Option<u64> {
    Some(u64::from_le_bytes(m.bytes(off, 8)?.try_into().ok()?))
}

/// The digest algorithms of a crypto agile log (`TCG_EfiSpecIdEvent`'s
/// `digestSizes`): (TPM_ALG_ID, digest size) pairs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AlgTable {
    pub n: usize,
    pub algs: [(u16, u16); MAX_ALGS],
}

impl AlgTable {
    pub const EMPTY: AlgTable = AlgTable { n: 0, algs: [(0, 0); MAX_ALGS] };

    pub fn digest_size(&self, alg: u16) -> Option<usize> {
        self.algs[..self.n].iter().find(|a| a.0 == alg).map(|a| a.1 as usize)
    }
}

/// The Spec ID event that starts a crypto agile log (a legacy
/// `TCG_PCR_EVENT` of type `EV_NO_ACTION` whose data is
/// `TCG_EfiSpecIdEvent`): its length and the log's digest algorithms.
pub fn spec_id(m: &(impl Mem + ?Sized)) -> Option<(usize, AlgTable)> {
    if rd32(m, 4)? != EV_NO_ACTION {
        return None;
    }
    let size = rd32(m, 28)? as usize;
    let len = PCR_EVENT_LEN.checked_add(size)?;
    if len > MAX_EVENT_LOG {
        return None;
    }
    let ev = m.bytes(PCR_EVENT_LEN, size)?;
    // Signature, platform class, versions and uintn size, then the count.
    if ev.len() < 28 || &ev[..16] != SPEC_ID_SIGNATURE {
        return None;
    }
    let n = u32::from_le_bytes(ev[24..28].try_into().ok()?) as usize;
    if n == 0 || n > MAX_ALGS || 28 + 4 * n > ev.len() {
        return None;
    }
    let mut t = AlgTable::EMPTY;
    for i in 0..n {
        let e = &ev[28 + 4 * i..32 + 4 * i];
        t.algs[i] = (u16::from_le_bytes([e[0], e[1]]), u16::from_le_bytes([e[2], e[3]]));
    }
    t.n = n;
    Some((len, t))
}

/// The length of the `TCG_PCR_EVENT2` at `off`: PCR index, event type,
/// the digest count, each digest (algorithm ID, then as many bytes as the
/// Spec ID event gives the algorithm), the event size and the event.
pub fn event2_len(m: &(impl Mem + ?Sized), off: usize, algs: &AlgTable) -> Option<usize> {
    let ty = rd32(m, off.checked_add(4)?)?;
    let count = rd32(m, off.checked_add(8)?)? as usize;
    if count > algs.n {
        return None;
    }
    let mut p = off.checked_add(12)?;
    for _ in 0..count {
        let size = algs.digest_size(rd16(m, p)?)?;
        p = p.checked_add(2)?.checked_add(size)?;
    }
    let size = rd32(m, p)?;
    // Zeroed memory is no event (as Linux's __calc_tpm2_event_size).
    if ty == 0 && size == 0 {
        return None;
    }
    let end = p.checked_add(4)?.checked_add(size as usize)?;
    let len = end - off;
    if len > MAX_EVENT_LOG {
        return None;
    }
    m.bytes(off, len)?;
    Some(len)
}

/// The length of the legacy `TCG_PCR_EVENT` at `off` (a TCG 1.2 log).
pub fn event1_len(m: &(impl Mem + ?Sized), off: usize) -> Option<usize> {
    let size = rd32(m, off.checked_add(28)?)? as usize;
    let len = PCR_EVENT_LEN.checked_add(size)?;
    if len > MAX_EVENT_LOG {
        return None;
    }
    m.bytes(off, len)?;
    Some(len)
}

/// A log as GetEventLog described it: its exact length (through the last
/// entry), and for a crypto agile log its digest algorithms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Log {
    pub len: usize,
    pub algs: AlgTable,
}

/// The log at `location` (`m` reads from there) whose last entry starts at
/// `last_entry`, in the crypto agile format or (`tcg_1_2`) the TCG 1.2
/// one. None for no log (either address 0) or one that does not parse
/// or would exceed `MAX_EVENT_LOG`.
pub fn main_log(m: &(impl Mem + ?Sized), location: u64, last_entry: u64, tcg_1_2: bool) -> Option<Log> {
    if location == 0 || last_entry == 0 || last_entry < location {
        return None;
    }
    let last = last_entry - location;
    if last >= MAX_EVENT_LOG as u64 {
        return None;
    }
    let last = last as usize;
    let (algs, last_len) = if tcg_1_2 {
        (AlgTable::EMPTY, event1_len(m, last)?)
    } else {
        let (header, algs) = spec_id(m)?;
        if last == 0 {
            (algs, header)
        } else if last < header {
            return None;
        } else {
            (algs, event2_len(m, last, &algs)?)
        }
    };
    let len = last.checked_add(last_len)?;
    if len > MAX_EVENT_LOG {
        return None;
    }
    Some(Log { len, algs })
}

/// The final events table as the loader found it when it took the main
/// log: the events it already held are in that log too.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FinalSnapshot {
    pub nr_events: u64,
    /// Their bytes after the table's header.
    pub bytes: usize,
}

/// The final events table `m` (version 1) and the length of its events.
pub fn final_snapshot(m: &(impl Mem + ?Sized), algs: &AlgTable) -> Option<FinalSnapshot> {
    if rd64(m, 0)? != 1 {
        return None;
    }
    let nr_events = rd64(m, 8)?;
    // Each event is at least 16 bytes and must lie inside `m`, so a huge
    // count fails well before it is counted out.
    let mut off = FINAL_HEADER;
    let mut i = 0;
    while i < nr_events {
        off = off.checked_add(event2_len(m, off, algs)?)?;
        i += 1;
    }
    Some(FinalSnapshot { nr_events, bytes: off - FINAL_HEADER })
}

/// Append to `buf[..len]` the events the final events table `m` gained
/// since `snap`: whole events only, as many as fit in `buf`. Returns the
/// new length and whether any were left out (no room, or a table or event
/// that no longer parses).
pub fn append_final(m: &(impl Mem + ?Sized), algs: &AlgTable, snap: &FinalSnapshot, buf: &mut [u8], len: usize) -> (usize, bool) {
    let nr = match (rd64(m, 0), rd64(m, 8)) {
        (Some(1), Some(nr)) => nr,
        _ => return (len, true),
    };
    if nr == snap.nr_events {
        return (len, false);
    }
    // Fewer events than before: the table is not the one snapshotted.
    if nr < snap.nr_events {
        return (len, true);
    }
    let Some(mut off) = FINAL_HEADER.checked_add(snap.bytes) else { return (len, true) };
    let mut len = len;
    let mut i = snap.nr_events;
    while i < nr {
        let Some(l) = event2_len(m, off, algs) else { return (len, true) };
        let Some(end) = len.checked_add(l).filter(|&e| e <= buf.len()) else { return (len, true) };
        let Some(ev) = m.bytes(off, l) else { return (len, true) };
        buf[len..end].copy_from_slice(ev);
        len = end;
        off += l;
        i += 1;
    }
    (len, false)
}

/// The PCR boot files the loader reads (the load options' root task and
/// modules, and the AArch64 kernel command line) extend: PCR 9, which the
/// PC Client Platform Firmware Profile gives to the boot loader's files.
pub const PCR_BOOT_FILES: u32 = 9;
/// `EV_IPL`: code or data the boot loader loaded.
pub const EV_IPL: u32 = 0xd;
/// `EFI_VOLUME_FULL`: extended, but the log had no room for the event.
pub const VOLUME_FULL: u64 = (1 << 63) | 11;
/// `EFI_TCG2_EVENT_HEADER`, packed: header size, header version, PCR
/// index, event type (TCG EFI Protocol §6.6).
pub const TCG2_HEADER_LEN: usize = 14;
/// `EFI_TCG2_EVENT`: its size field, then the header, then the event data.
pub const TCG2_EVENT_FIXED: usize = 4 + TCG2_HEADER_LEN;
/// The longest boot file descriptor: the prefix, a role, its separator,
/// the length and a path as long as any `read_file` opens (255 bytes).
pub const DESC_MAX: usize = 320;
/// What every descriptor starts with, so that no other event's data can
/// be mistaken for one.
const DESC_PREFIX: &[u8] = b"fl4-efi\0";

/// Write an `EFI_TCG2_EVENT` for `pcr` into `buf` (at least
/// `TCG2_EVENT_FIXED` bytes), with `data` cut to fit as its event data;
/// returns its length.
pub fn tcg2_event(buf: &mut [u8], pcr: u32, event_type: u32, data: &[u8]) -> usize {
    let n = data.len().min(buf.len() - TCG2_EVENT_FIXED);
    let size = TCG2_EVENT_FIXED + n;
    buf[0..4].copy_from_slice(&(size as u32).to_le_bytes());
    buf[4..8].copy_from_slice(&(TCG2_HEADER_LEN as u32).to_le_bytes());
    buf[8..10].copy_from_slice(&1u16.to_le_bytes());
    buf[10..14].copy_from_slice(&pcr.to_le_bytes());
    buf[14..18].copy_from_slice(&event_type.to_le_bytes());
    buf[TCG2_EVENT_FIXED..size].copy_from_slice(&data[..n]);
    size
}

/// Whether HashLogExtendEvent extended the PCR: success, or
/// `EFI_VOLUME_FULL` (only the log is full).
pub fn measure_status(status: u64) -> Result<(), &'static str> {
    match status {
        0 | VOLUME_FULL => Ok(()),
        _ => Err("cannot measure a boot file into TPM PCR 9"),
    }
}

/// `EV_SEPARATOR` (TCG PC Client PFP §10.4.1).
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub const EV_SEPARATOR: u32 = 4;
/// A separator's event data when an error is signalled: `0xffffffff`.
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub const SEPARATOR_ERROR: [u8; 4] = [0xff; 4];
/// A TD ignores any TPM, but leaves no PCR in a state that looks like a
/// clean boot: the loader extends an error separator into every static
/// locality-0 PCR, 0..16 (firmware's 0..7, the boot loader's and the
/// OS's 8..15).
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub const POISON_PCR_COUNT: u32 = 16;

/// Whether HashLogExtendEvent extended a PCR with the poison: success, or
/// `EFI_VOLUME_FULL` (only the log is full).
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub fn poison_status(status: u64) -> Result<(), &'static str> {
    match status {
        0 | VOLUME_FULL => Ok(()),
        _ => Err("cannot poison TPM PCRs in TDX"),
    }
}

/// The descriptor measured before a boot file's contents (tcg2.rs and
/// ccel.rs): `"fl4-efi\0" || role || "\0" || len (u64 LE) || path`, into
/// `buf` (at least the prefix, the role, 1 and 8 bytes); returns its
/// length. Never empty, so a 0-byte file still extends; the role (no NUL
/// in it) and the length come before the path, which alone is cut to fit.
pub fn file_descriptor(buf: &mut [u8], role: &[u8], path: &[u8], len: u64) -> usize {
    let mut n = 0;
    for part in [DESC_PREFIX, role, b"\0", &len.to_le_bytes()[..]] {
        buf[n..n + part.len()].copy_from_slice(part);
        n += part.len();
    }
    let p = path.len().min(buf.len() - n);
    buf[n..n + p].copy_from_slice(&path[..p]);
    n + p
}

#[cfg(not(test))]
pub use efi::*;

/// What runs on firmware: GetEventLog, the copy, the final events.
#[cfg(not(test))]
mod efi {
    use super::*;
    use crate::{bs, config_table, print, Con, Guid, Status, SUCCESS};

    pub const EFI_TCG2_PROTOCOL_GUID: Guid = Guid(0x607f_766c, 0x7455, 0x42be, [0x93, 0x0b, 0xe4, 0xd7, 0x6d, 0xb2, 0x72, 0x0f]);
    pub const EFI_TCG2_FINAL_EVENTS_TABLE_GUID: Guid =
        Guid(0x1e2e_d096, 0x30e2, 0x4254, [0xbd, 0x89, 0x86, 0x3b, 0xbe, 0xf8, 0x23, 0x25]);

    /// `EFI_TCG2_PROTOCOL` up to HashLogExtendEvent (TCG EFI Protocol §6.4).
    #[repr(C)]
    struct Tcg2Protocol {
        get_capability: usize,
        get_event_log: extern "efiapi" fn(*mut Tcg2Protocol, u32, *mut u64, *mut u64, *mut u8) -> Status,
        hash_log_extend_event: extern "efiapi" fn(*mut Tcg2Protocol, u64, u64, u64, *const u8) -> Status,
    }

    fn protocol() -> Option<*mut Tcg2Protocol> {
        let mut p = core::ptr::null_mut();
        let r = (bs().locate_protocol)(&EFI_TCG2_PROTOCOL_GUID, core::ptr::null(), &mut p);
        (r == SUCCESS && !p.is_null()).then_some(p as *mut Tcg2Protocol)
    }

    /// Extend `pcr` with the `len` (not 0) bytes at `pa`, logged as an
    /// `EV_IPL` event labelled `label`. Without a TPM there is nothing to
    /// extend; with one, a measurement it refuses is an error, which the
    /// caller turns into a failed boot.
    pub fn measure_bytes(pcr: u32, label: &[u8], pa: u64, len: u64) -> Result<(), &'static str> {
        let Some(tcg) = protocol() else { return Ok(()) };
        if len == 0 {
            // Firmware refuses to hash nothing (EFI_INVALID_PARAMETER).
            return Err("empty TPM measurement");
        }
        let mut event = [0u8; TCG2_EVENT_FIXED + DESC_MAX];
        tcg2_event(&mut event, pcr, EV_IPL, label);
        let r = unsafe { ((*tcg).hash_log_extend_event)(tcg, 0, pa, len, event.as_ptr()) };
        measure_status(r as u64)
    }

    /// Measure into PCR 9 a boot file the loader read (`role`: rootserver,
    /// module or cmdline): its descriptor (`file_descriptor`: role, length,
    /// path), then its contents in place unless it is empty. Ok without a
    /// TPM; an error if the TPM refuses either.
    pub fn measure_file(role: &[u8], path: &[u8], pa: u64, len: u64) -> Result<(), &'static str> {
        if protocol().is_none() {
            return Ok(());
        }
        let mut desc = [0u8; DESC_MAX];
        let n = file_descriptor(&mut desc, role, path, len);
        let desc = &desc[..n];
        measure_bytes(PCR_BOOT_FILES, desc, desc.as_ptr() as u64, n as u64)?;
        if len > 0 {
            measure_bytes(PCR_BOOT_FILES, desc, pa, len)?;
        }
        Ok(())
    }

    /// In a TD: extend an error separator (`EV_SEPARATOR`,
    /// `SEPARATOR_ERROR`) into PCRs 0..`POISON_PCR_COUNT` of a TPM firmware
    /// exposes, so that no PCR holds a value a clean boot would give. Ok
    /// without a TPM; an error if the TPM refuses any extension.
    #[cfg(target_arch = "x86_64")]
    pub fn poison() -> Result<(), &'static str> {
        let Some(tcg) = protocol() else { return Ok(()) };
        let sep = SEPARATOR_ERROR;
        let mut event = [0u8; TCG2_EVENT_FIXED + 4];
        for pcr in 0..POISON_PCR_COUNT {
            tcg2_event(&mut event, pcr, EV_SEPARATOR, &sep);
            let r = unsafe { ((*tcg).hash_log_extend_event)(tcg, 0, sep.as_ptr() as u64, sep.len() as u64, event.as_ptr()) };
            poison_status(r as u64)?;
        }
        say!("fl4-efi: TDX guest, poisoned TPM PCRs 0..15");
        Ok(())
    }

    /// Firmware memory at `base`, read at most `limit` bytes in (boot
    /// services memory or ACPI NVS, identity mapped while the loader runs).
    pub struct Raw {
        pub base: u64,
        pub limit: usize,
    }

    impl Mem for Raw {
        fn bytes(&self, off: usize, n: usize) -> Option<&[u8]> {
            if off.checked_add(n)? > self.limit {
                return None;
            }
            let p = self.base.checked_add(off as u64)?;
            p.checked_add(n as u64)?;
            Some(unsafe { core::slice::from_raw_parts(p as *const u8, n) })
        }
    }

    /// The log firmware keeps, found before ExitBootServices.
    pub struct TpmLog {
        location: u64,
        log: Log,
        flags: u64,
        /// The final events table and what it held (crypto agile logs).
        final_table: u64,
        snap: Option<FinalSnapshot>,
    }

    impl TpmLog {
        /// A log found through a protocol with this interface (the
        /// confidential-computing one, ccel.rs, has the same formats).
        #[cfg(target_arch = "x86_64")]
        pub fn new(location: u64, log: Log, flags: u64, final_table: u64, snap: Option<FinalSnapshot>) -> TpmLog {
            TpmLog { location, log, flags, final_table, snap }
        }

        /// Whether events logged after `collect` can be told apart, so
        /// that `finish` can append them.
        #[cfg(target_arch = "x86_64")]
        pub fn has_final_events(&self) -> bool {
            self.snap.is_some()
        }

        /// Bytes to set aside for the copy: the log and the slack.
        pub fn capacity(&self) -> u64 {
            (self.log.len + FINAL_SLACK).min(MAX_EVENT_LOG) as u64
        }

        /// The log so far (before ExitBootServices: it is in boot
        /// services memory) to `dst`, `capacity()` bytes.
        pub fn copy_main(&self, dst: u64) {
            unsafe { core::ptr::copy_nonoverlapping(self.location as *const u8, dst as *mut u8, self.log.len) };
        }

        /// The size and flags of the copy at `dst` so far.
        pub fn record(&self) -> (u64, u64) {
            (self.log.len as u64, self.flags)
        }

        /// After ExitBootServices: append the final events firmware logged
        /// since `collect` to the copy at `dst`. Returns its size and flags.
        /// Uses no boot services and does not print.
        pub fn finish(&self, dst: u64) -> (u64, u64) {
            let mut flags = self.flags;
            let mut len = self.log.len;
            if let Some(snap) = &self.snap {
                let m = Raw { base: self.final_table, limit: MAX_EVENT_LOG };
                let buf = unsafe { core::slice::from_raw_parts_mut(dst as *mut u8, self.capacity() as usize) };
                let (l, lost) = append_final(&m, &self.log.algs, snap, buf, len);
                len = l;
                if lost {
                    flags |= TRUNCATED;
                }
            }
            (len as u64, flags)
        }
    }

    /// The TPM event log, if firmware has a TPM 2.0 protocol with a usable
    /// log. Never fails the boot: anything else is a line on the console.
    pub fn collect() -> Option<TpmLog> {
        let Some(tcg) = protocol() else {
            say!("fl4-efi: no TPM 2.0 protocol, no TPM event log");
            return None;
        };
        // The crypto agile log first; firmware with only a SHA-1 bank may
        // keep the TCG 1.2 one alone.
        for (format, tcg_1_2) in [(EFI_TCG2_EVENT_LOG_FORMAT_TCG_2, false), (EFI_TCG2_EVENT_LOG_FORMAT_TCG_1_2, true)] {
            let (mut location, mut last, mut truncated) = (0u64, 0u64, 0u8);
            let r = unsafe { ((*tcg).get_event_log)(tcg, format, &mut location, &mut last, &mut truncated) };
            if r != SUCCESS {
                continue;
            }
            if location == 0 || last == 0 {
                say!("fl4-efi: TPM event log is empty");
                return None;
            }
            // Right after GetEventLog: the final events table holds what
            // the log already does (TCG EFI Protocol §6.6).
            let final_table = if tcg_1_2 { 0 } else { config_table(EFI_TCG2_FINAL_EVENTS_TABLE_GUID) };
            let m = Raw { base: location, limit: MAX_EVENT_LOG };
            let Some(log) = main_log(&m, location, last, tcg_1_2) else {
                say!("fl4-efi: TPM event log at {:#x} does not parse: not passed on", location);
                return None;
            };
            let mut flags = if tcg_1_2 { TCG_1_2 } else { 0 };
            if truncated != 0 {
                flags |= TRUNCATED;
            }
            let mut snap = None;
            if final_table != 0 {
                snap = final_snapshot(&Raw { base: final_table, limit: MAX_EVENT_LOG }, &log.algs);
                if snap.is_none() {
                    // Later events cannot be told apart from earlier ones.
                    say!("fl4-efi: TPM final events table does not parse: the log may end early");
                    flags |= TRUNCATED;
                }
            } else if !tcg_1_2 {
                // Without the table, events after this point are lost.
                flags |= TRUNCATED;
            }
            say!(
                "fl4-efi: TPM event log ({}) {:#x} bytes at {:#x}{}",
                if tcg_1_2 { "TCG 1.2" } else { "TCG 2.0" },
                log.len,
                location,
                if snap.is_some() { ", final events table" } else { "" }
            );
            return Some(TpmLog { location, log, flags, final_table, snap });
        }
        say!("fl4-efi: TPM GetEventLog failed, no TPM event log");
        None
    }
}
