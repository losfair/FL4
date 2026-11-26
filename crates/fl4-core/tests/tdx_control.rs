//! The bounds of `seL4_X86_TdxControl` (fl4-core tdx.rs): what each method
//! accepts before the backend runs a TDCALL, and how the cap moves from the
//! root task to the task that handles attestation.
#![cfg(not(feature = "aarch64"))]

use fl4_abi::label;
use fl4_core::capability::{Cap, FrameSize, Rights, VM_READ_ONLY, VM_READ_WRITE};
use fl4_core::error::{Exc, KResult, SysError};
use fl4_core::layout::node;
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_set, Slot, Tcb};
use fl4_core::{cnode, msg, objects, sched, tdx};
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory(BTreeMap<u64, u64>);
impl Store for Memory {
    fn read(&self, a: u64) -> u64 { *self.0.get(&a).unwrap_or(&0) }
    fn write(&mut self, a: u64, v: u64) { self.0.insert(a, v); }
    fn zero(&mut self, a: u64, len: u64) {
        for offset in (0..len).step_by(8) { self.write(a + offset, 0); }
    }
    fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len); }
    fn ks_base(&self) -> u64 { 0x100000 }
    fn cur_cpu(&self) -> u64 { 0 }
}

#[derive(Default)]
struct Machine {
    tdx: bool,
    /// Frames `dma_ram` calls RAM from RetypeShared.
    shared_ram: bool,
    reports: Vec<(u64, [u64; 8])>,
    extends: Vec<(u64, [u64; 6])>,
    quotes: Vec<(u64, u64)>,
    status: u64,
}

impl Arch for Machine {
    fn tdx_active(&self) -> bool { self.tdx }
    fn dma_ram(&self, _: u64, _: u64) -> bool { self.shared_ram }
    fn tdx_report(&mut self, f: u64, d0: u64, d1: u64, d2: u64, d3: u64, d4: u64, d5: u64, d6: u64, d7: u64) -> u64 {
        self.reports.push((f, [d0, d1, d2, d3, d4, d5, d6, d7]));
        self.status
    }
    fn tdx_extend_rtmr(&mut self, i: u64, d0: u64, d1: u64, d2: u64, d3: u64, d4: u64, d5: u64) -> u64 {
        self.extends.push((i, [d0, d1, d2, d3, d4, d5]));
        self.status
    }
    fn tdx_get_quote(&mut self, f: u64, len: u64) -> u64 {
        self.quotes.push((f, len));
        self.status
    }
    fn now(&mut self) -> u64 { 0 }
    fn set_deadline(&mut self, _: u64) {}
    fn us_to_ticks(&self, x: u64) -> u64 { x }
    fn ticks_to_us(&self, x: u64) -> u64 { x }
    fn max_us(&self) -> u64 { u64::MAX }
    fn kernel_wcet_ticks(&self) -> u64 { 1 }
    fn irq_pending(&mut self) -> bool { false }
    fn take_pending_irq(&mut self) -> u64 { u64::MAX }
    fn mask_irq(&mut self, _: u64, _: bool) {}
    fn ack_irq(&mut self, _: u64) {}
    fn set_vspace(&mut self, _: u64, _: u64) {}
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, _: u64) {}
    fn invalidate_page_structures(&mut self, _: u64) {}
    fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
    fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool { false }
    fn num_ioapics(&self) -> u64 { 0 }
    fn ioapic_pins(&self, _: u64) -> u64 { 0 }
    fn port_in(&mut self, _: u64, _: u64) -> u64 { 0 }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, _: u64) {}
    fn fpu_sanitise(&mut self, _: u64) {}
    fn fpu_reload(&mut self, _: u64) {}
    fn fpu_release(&mut self, _: u64) {}
    fn remote_stall(&mut self, _: u64) {}
    fn send_reschedule(&mut self, _: u64) {}
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 { 0 }
    fn halt(&mut self) {}
}

const THREAD: Tcb = Tcb(0x40_0000);
/// Where message words past the registers go.
const BUF: u64 = 0x50_0000;
const CAP_SLOT: Slot = Slot(0x60_0000);
const FRAME: u64 = 0xffff_ff80_0020_0000;

fn setup(tdx: bool) -> (Memory, Machine) {
    let mut s = Memory::default();
    node_set(&mut s, 0, node::CUR_THREAD, THREAD.0);
    (s, Machine { tdx, shared_ram: true, ..Machine::default() })
}

fn frame(size: FrameSize, rights: u64, is_device: bool) -> Cap {
    Cap::Frame { ptr: FRAME, size, rights, is_device, mapped: false, is_ept: false, asid: 0, vaddr: 0 }
}

fn invoke(s: &mut Memory, a: &mut Machine, lbl: u64, args: &[u64], cap: Option<Cap>) -> KResult<()> {
    for (i, &v) in args.iter().enumerate() {
        msg::set_mr(s, THREAD, BUF, i as u64, v);
    }
    let extra = match cap {
        Some(c) => {
            CAP_SLOT.set_cap(s, c);
            [CAP_SLOT, Slot(0), Slot(0)]
        }
        None => [Slot(0); 3],
    };
    tdx::decode(s, a, lbl, args.len() as u64, true, BUF, &extra)
}

fn ok(r: KResult<()>) {
    assert!(r.is_ok());
}

fn is_invalid_cap(r: KResult<()>) -> bool {
    matches!(r, Err(Exc::Sys(SysError::InvalidCapability { arg: 1 })))
}

fn is_invalid_arg(r: KResult<()>) -> bool {
    matches!(r, Err(Exc::Sys(SysError::InvalidArgument { arg: 0 })))
}

fn is_truncated(r: KResult<()>) -> bool {
    matches!(r, Err(Exc::Sys(SysError::TruncatedMessage)))
}

fn is_illegal(r: KResult<()>) -> bool {
    matches!(r, Err(Exc::Sys(SysError::IllegalOperation)))
}

const DATA: [u64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

#[test]
fn get_report_writes_to_a_private_writable_4k_frame_only() {
    let (mut s, mut a) = setup(true);
    a.status = 0;
    ok(invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA, Some(frame(FrameSize::Small, VM_READ_WRITE, false))));
    assert_eq!(a.reports, [(FRAME, DATA)]);
    assert_eq!(msg::get_mr(&s, THREAD, 0, 0), 0);
    assert_eq!(THREAD.state(&s), sched::TS_RUNNING);
    let endpoint = Cap::Endpoint { ptr: 0x8000, badge: 0, send: true, recv: true, grant: true, grant_reply: true };
    for bad in [
        endpoint,
        Cap::Null,
        // Read-only.
        frame(FrameSize::Small, VM_READ_ONLY, false),
        // Shared with the VMM: the report would leave the TD.
        frame(FrameSize::Small, VM_READ_WRITE, true),
        // Only a 4 KiB frame.
        frame(FrameSize::Large, VM_READ_WRITE, false),
        frame(FrameSize::Huge, VM_READ_WRITE, false),
    ] {
        let r = invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA, Some(bad));
        assert!(is_invalid_cap(r));
    }
    assert_eq!(a.reports.len(), 1, "no rejected invocation reached the TDX module");
}

#[test]
fn get_report_needs_all_its_arguments_and_a_frame() {
    let (mut s, mut a) = setup(true);
    let good = frame(FrameSize::Small, VM_READ_WRITE, false);
    assert!(is_truncated(invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA[..7], Some(good))));
    assert!(is_truncated(invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA, None)));
    assert!(a.reports.is_empty());
}

#[test]
fn the_tdx_status_is_returned_to_the_caller() {
    let (mut s, mut a) = setup(true);
    a.status = 0xc000_0100_0000_0000;
    ok(invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA, Some(frame(FrameSize::Small, VM_READ_WRITE, false))));
    assert_eq!(msg::get_mr(&s, THREAD, 0, 0), 0xc000_0100_0000_0000);
}

#[test]
fn extend_rtmr_takes_indices_0_to_3() {
    let digest = [11, 12, 13, 14, 15, 16];
    for index in 0..4 {
        let (mut s, mut a) = setup(true);
        let mut args = vec![index];
        args.extend(digest);
        ok(invoke(&mut s, &mut a, label::X86TdxControlExtendRTMR, &args, None));
        assert_eq!(a.extends, [(index, digest)]);
    }
    for index in [4, 5, 64, u64::MAX] {
        let (mut s, mut a) = setup(true);
        let mut args = vec![index];
        args.extend(digest);
        assert!(is_invalid_arg(invoke(&mut s, &mut a, label::X86TdxControlExtendRTMR, &args, None)), "{index}");
        assert!(a.extends.is_empty());
    }
    let (mut s, mut a) = setup(true);
    assert!(is_truncated(invoke(&mut s, &mut a, label::X86TdxControlExtendRTMR, &[0, 1, 2, 3, 4, 5], None)));
}

#[test]
fn get_quote_takes_a_shared_writable_frame_from_retype_shared() {
    let (mut s, mut a) = setup(true);
    ok(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[4096], Some(frame(FrameSize::Small, VM_READ_WRITE, true))));
    ok(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[2 << 20], Some(frame(FrameSize::Large, VM_READ_WRITE, true))));
    assert_eq!(a.quotes, [(FRAME, 4096), (FRAME, 2 << 20)]);
    for bad in [
        // Private: its GPA with the shared bit is a different page.
        frame(FrameSize::Small, VM_READ_WRITE, false),
        frame(FrameSize::Small, VM_READ_ONLY, true),
        frame(FrameSize::Huge, VM_READ_WRITE, true),
        Cap::Notification { ptr: 0x8000, badge: 0, send: true, recv: true },
    ] {
        assert!(is_invalid_cap(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[4096], Some(bad))));
    }
    // A device frame that is not RAM from RetypeShared (real MMIO).
    a.shared_ram = false;
    let mmio = frame(FrameSize::Small, VM_READ_WRITE, true);
    assert!(is_invalid_cap(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[4096], Some(mmio))));
    assert_eq!(a.quotes.len(), 2);
}

#[test]
fn get_quote_length_is_whole_pages_inside_the_frame() {
    let (mut s, mut a) = setup(true);
    let small = frame(FrameSize::Small, VM_READ_WRITE, true);
    let large = frame(FrameSize::Large, VM_READ_WRITE, true);
    for (cap, len) in [(small, 0), (small, 1), (small, 4095), (small, 4097), (small, 8192), (large, 4096 + 1), (large, (2 << 20) + 4096), (large, u64::MAX & !4095)] {
        assert!(is_invalid_arg(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[len], Some(cap))), "{len:#x}");
    }
    assert!(a.quotes.is_empty());
    ok(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[8192], Some(large)));
    assert_eq!(a.quotes, [(FRAME, 8192)]);
    assert!(is_truncated(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[], Some(large))));
    assert!(is_truncated(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[4096], None)));
}

#[test]
fn outside_a_td_and_for_other_labels_the_invocation_is_illegal() {
    let (mut s, mut a) = setup(false);
    let f = frame(FrameSize::Small, VM_READ_WRITE, false);
    assert!(is_illegal(invoke(&mut s, &mut a, label::X86TdxControlGetReport, &DATA, Some(f))));
    assert!(is_illegal(invoke(&mut s, &mut a, label::X86TdxControlExtendRTMR, &[0, 1, 2, 3, 4, 5, 6], None)));
    assert!(is_illegal(invoke(&mut s, &mut a, label::X86TdxControlGetQuote, &[4096], Some(f))));
    assert!(a.reports.is_empty() && a.extends.is_empty() && a.quotes.is_empty());
    let (mut s, mut a) = setup(true);
    assert!(is_illegal(invoke(&mut s, &mut a, label::CNodeCopy, &DATA, Some(f))));
}

#[test]
fn the_cap_survives_its_encoding_and_is_an_arch_cap() {
    let (w0, w1) = Cap::TdxControl.encode();
    assert!(Cap::decode(w0, w1) == Cap::TdxControl);
    assert_eq!(w0 >> 59, 24);
    assert!(Cap::TdxControl.is_arch());
    assert!(objects::same_object_as(Cap::TdxControl, Cap::TdxControl));
    assert!(!objects::same_object_as(Cap::TdxControl, Cap::Domain));
    assert!(!objects::same_region_as(Cap::Domain, Cap::TdxControl));
    assert!(!objects::cap_is_physical(Cap::TdxControl));
    assert!(!objects::is_cap_revocable(Cap::TdxControl, Cap::TdxControl));
}

const ROOT: u64 = 0xffff_ff80_0100_0000;
const CHILD: u64 = 0xffff_ff80_0101_0000;
const RADIX: u64 = 4;

fn cnode(ptr: u64) -> Cap {
    Cap::CNode { ptr, radix: RADIX, guard_size: 64 - RADIX, guard: 0 }
}

/// A root CNode holding the cap in slot 15 and itself in slot 2, and an
/// empty CNode for the attestation task.
fn cspaces() -> (Memory, Machine) {
    let (mut s, a) = setup(true);
    Slot::index(ROOT, 2).set_cap(&mut s, cnode(ROOT));
    Slot::index(ROOT, 15).set_cap(&mut s, Cap::TdxControl);
    (s, a)
}

fn transfer(s: &mut Memory, a: &mut Machine, lbl: u64, length: u64) -> KResult<()> {
    let rights = Rights::all();
    let word = rights.write as u64 | (rights.read as u64) << 1 | (rights.grant as u64) << 2 | (rights.grant_reply as u64) << 3;
    for (i, v) in [3, 64, 15, 64, word].into_iter().enumerate() {
        msg::set_mr(s, THREAD, BUF, i as u64, v);
    }
    cnode::decode(s, a, lbl, length, cnode(CHILD), BUF, &[Slot::index(ROOT, 2), Slot(0), Slot(0)])
}

fn delete_root_copy(s: &mut Memory, a: &mut Machine) {
    msg::set_mr(s, THREAD, BUF, 0, 15);
    msg::set_mr(s, THREAD, BUF, 1, 64);
    ok(cnode::decode(s, a, label::CNodeDelete, 2, cnode(ROOT), BUF, &[Slot(0); 3]));
}

/// The hand-off the design relies on: root copies the cap to the task that
/// does attestation, then drops its own, and only the task holds it.
#[test]
fn the_root_task_can_copy_the_cap_and_drop_its_own() {
    let (mut s, mut a) = cspaces();
    ok(transfer(&mut s, &mut a, label::CNodeCopy, 5));
    assert!(Slot::index(CHILD, 3).cap(&s) == Cap::TdxControl, "copied");
    assert!(Slot::index(ROOT, 15).cap(&s) == Cap::TdxControl, "the source is kept by a copy");
    delete_root_copy(&mut s, &mut a);
    assert!(Slot::index(ROOT, 15).cap(&s) == Cap::Null);
    assert!(Slot::index(CHILD, 3).cap(&s) == Cap::TdxControl, "deleting the root's copy keeps the task's");
}

#[test]
fn the_root_task_can_move_the_cap() {
    let (mut s, mut a) = cspaces();
    ok(transfer(&mut s, &mut a, label::CNodeMove, 4));
    assert!(Slot::index(CHILD, 3).cap(&s) == Cap::TdxControl);
    assert!(Slot::index(ROOT, 15).cap(&s) == Cap::Null);
}

/// A copy cannot be made into an occupied slot, and the last copy's
/// deletion runs no object cleanup: the cap names no memory.
#[test]
fn the_cap_needs_an_empty_destination_and_has_nothing_to_finalise() {
    let (mut s, mut a) = cspaces();
    Slot::index(CHILD, 3).set_cap(&mut s, Cap::Domain);
    let r = transfer(&mut s, &mut a, label::CNodeCopy, 5);
    assert!(matches!(r, Err(Exc::Sys(SysError::DeleteFirst))));
    let (mut s, mut a) = cspaces();
    let (rest, cleanup) = objects::finalise_cap(&mut s, &mut a, Cap::TdxControl, true, false);
    assert!(rest == Cap::Null && cleanup == Cap::Null);
}
