//! AArch64 Stage-2 VSpace (`seL4_ARM_Stage2VSpaceObject`, `Cap::Ept { level: 0 }`).
//!
//! Geometry is selected dynamically from `Arch::s2_ipa_bits()`:
//! - 40-bit IPA (when PA <= 42): 3-level walk, L1 root concatenated (2 pages = 8 KiB, 1024 entries), shifts 30 -> 21 -> 12.
//! - 44-bit IPA (when PA == 44): 4-level walk, L0 root (first 32 entries), shifts 39 -> 30 -> 21 -> 12.
//! - 48-bit IPA (when PA >= 48): 4-level walk, L0 root (512 entries), shifts 39 -> 30 -> 21 -> 12.

use crate::capability::{Cap, FrameSize, VM_KERNEL_ONLY, VM_READ_ONLY, VM_READ_WRITE};
use crate::error::{illegal, invalid_arg, invalid_cap, range, truncated, Exc, KResult, LookupFault, SysError};
use crate::layout;
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::Slot;
use crate::{sched, vspace};
use fl4_abi::consts::arm_vm_attr;
use fl4_abi::label;

const D_VALID: u64 = 1 << 0;
const D_TABLE_OR_PAGE: u64 = 1 << 1;
const S2_MEMATTR_NORMAL_WB: u64 = 0b1111 << 2;
const S2_MEMATTR_DEVICE: u64 = 0b0000 << 2;
const S2_AP_RO: u64 = 0b01 << 6;
const S2_AP_RW: u64 = 0b11 << 6;
const S2_SH_INNER: u64 = 0b11 << 8;
const S2_AF: u64 = 1 << 10;
/// Stage-2 XN[54:53]: 0b10 = no execution at EL1 or EL0; bit 53 always 0.
const S2_XN: u64 = 1 << 54;
const ADDR_MASK: u64 = 0x0000_ffff_ffff_f000;
const PAGE_BITS: u64 = 12;

/// Descriptor bits whose change requires break-before-make (all except S2AP, AF, XN).
const S2_BBM_MASK: u64 = !((3 << 6) | S2_AF | (3 << 53));

#[derive(Clone, Copy)]
pub struct S2Geom {
    pub ipa_bits: u64,
    pub top_shift: u64,
    pub top_mask: u64,
    pub levels: u64,
}

pub fn geom(ipa_bits: u64) -> S2Geom {
    if ipa_bits <= 42 {
        S2Geom { ipa_bits: 40, top_shift: 30, top_mask: 1023, levels: 3 }
    } else if ipa_bits == 44 {
        S2Geom { ipa_bits: 44, top_shift: 39, top_mask: 31, levels: 4 }
    } else {
        S2Geom { ipa_bits: 48, top_shift: 39, top_mask: 511, levels: 4 }
    }
}

pub fn ipa_limit(ipa_bits: u64) -> u64 {
    let g = geom(ipa_bits);
    (1u64 << g.ipa_bits).wrapping_sub(1)
}

fn entry_addr(table: u64, ipa: u64, shift: u64, mask: u64) -> u64 {
    table.wrapping_add(((ipa >> (shift & 63)) & mask).wrapping_mul(8))
}

fn table_of(e: u64) -> u64 {
    layout::pptr(e & ADDR_MASK)
}

fn is_table(e: u64, shift: u64) -> bool {
    shift > PAGE_BITS && e & (D_VALID | D_TABLE_OR_PAGE) == (D_VALID | D_TABLE_OR_PAGE)
}

fn is_leaf(e: u64, shift: u64) -> bool {
    if shift == PAGE_BITS {
        e & (D_VALID | D_TABLE_OR_PAGE) == (D_VALID | D_TABLE_OR_PAGE)
    } else {
        e & (D_VALID | D_TABLE_OR_PAGE) == D_VALID
    }
}

fn leaf_base(e: u64, shift: u64) -> u64 {
    e & ADDR_MASK & !((1u64 << (shift & 63)).wrapping_sub(1))
}

fn s2_rights_of(e: u64) -> u64 {
    let ap = (e >> 6) & 3;
    if ap == 0b11 {
        VM_READ_WRITE
    } else if ap == 0b01 {
        VM_READ_ONLY
    } else {
        VM_KERNEL_ONLY
    }
}

/// Build a Stage-2 table descriptor (no PXNTable).
pub fn make_s2_table(paddr: u64) -> u64 {
    (paddr & ADDR_MASK) | D_VALID | D_TABLE_OR_PAGE
}

/// Build a Stage-2 leaf descriptor (1 GiB / 2 MiB block or 4 KiB page).
/// Returns 0 for `VM_KERNEL_ONLY` (not mapped).
pub fn make_s2_leaf(paddr: u64, rights: u64, cap_read: bool, attr: u64, shift: u64) -> u64 {
    let ap = if rights == VM_READ_WRITE {
        S2_AP_RW
    } else if rights == VM_READ_ONLY {
        S2_AP_RO
    } else {
        return 0;
    };
    let xn = vspace::exec_never(attr, cap_read);
    let cacheable = attr & arm_vm_attr::PAGE_CACHEABLE != 0;
    let (memattr, sh) = if cacheable {
        (S2_MEMATTR_NORMAL_WB, S2_SH_INNER)
    } else {
        (S2_MEMATTR_DEVICE, 0)
    };
    (paddr & ADDR_MASK)
        | (if shift == PAGE_BITS { D_VALID | D_TABLE_OR_PAGE } else { D_VALID })
        | memattr
        | ap
        | sh
        | S2_AF
        | (if xn { S2_XN } else { 0 })
}

#[derive(Clone, Copy)]
pub struct S2Slot {
    pub slot: u64,
    pub shift: u64,
}

pub fn lookup_slot<S: Store>(s: &S, root: u64, ipa: u64, ipa_bits: u64) -> S2Slot {
    let g = geom(ipa_bits);
    let mut shift = g.top_shift;
    let mut slot = entry_addr(root, ipa, shift, g.top_mask);
    let mut rem = g.levels.wrapping_sub(1);
    while rem > 0 && is_table(s.read(slot), shift) {
        rem -= 1;
        shift = shift.wrapping_sub(9);
        slot = entry_addr(table_of(s.read(slot)), ipa, shift, 511);
    }
    S2Slot { slot, shift }
}

/// Look up a Stage-2 root in the ASID pool (tag `vspace::ROOT_S2`).
pub fn find<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    let r = vspace::find_asid_raw(s, asid)?;
    if r & vspace::ROOT_TAG != vspace::ROOT_S2 {
        Err(LookupFault::InvalidRoot)
    } else {
        Ok(r & !vspace::ROOT_TAG)
    }
}

/// Validate a mapped Stage-2 VSpace cap against its ASID pool entry.
pub fn root<S: Store>(s: &S, c: Cap, cap_arg: u64) -> KResult<(u64, u64)> {
    match c {
        Cap::Ept { ptr, level: 0, mapped: true, asid, .. } => {
            let r = find(s, asid).map_err(|lf| Exc::Sys(SysError::FailedLookup { source: false, lf }))?;
            if r != ptr {
                return invalid_cap(cap_arg);
            }
            Ok((r, asid))
        }
        _ => invalid_cap(cap_arg),
    }
}

/// Finalise a Stage-2 VSpace capability on deletion.
pub fn finalise<S: Store, A: Arch>(s: &mut S, a: &mut A, c: Cap) {
    if let Cap::Ept { ptr, level: 0, mapped: true, asid, .. } = c {
        vspace::delete_asid(s, a, asid, ptr | vspace::ROOT_S2);
    }
}

/// Map a 4 KiB `Cap::PageTable` into a Stage-2 VSpace at `ipa`.
pub fn map_table<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    root: u64,
    asid: u64,
    ipa: u64,
    pt: u64,
    slot: Slot,
) -> KResult<()> {
    let ipa_bits = a.s2_ipa_bits();
    if ipa > ipa_limit(ipa_bits) {
        return invalid_arg(0);
    }
    let lu = lookup_slot(s, root, ipa, ipa_bits);
    if lu.shift == PAGE_BITS || s.read(lu.slot) & D_VALID != 0 {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    let base = ipa & !((1u64 << (lu.shift & 63)).wrapping_sub(1));
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, Cap::PageTable { ptr: pt, mapped: true, asid, vaddr: base });
    s.write(lu.slot, make_s2_table(layout::paddr(pt)));
    Ok(())
}

/// Unmap a `Cap::PageTable` from a Stage-2 VSpace.
pub fn unmap_table<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, ipa: u64, pt: u64) {
    let root = match find(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let g = geom(a.s2_ipa_bits());
    let mut table = root;
    let mut shift = g.top_shift;
    let mut mask = g.top_mask;
    let mut rem = g.levels.wrapping_sub(1);
    // As in `vspace::unmap_page_table`: the walk records the slot that
    // points to `pt` and ends with `break` (no early return in the loop).
    let mut found = None;
    while rem > 0 {
        let slot = entry_addr(table, ipa, shift, mask);
        let e = s.read(slot);
        if !is_table(e, shift) {
            break;
        }
        if table_of(e) == pt {
            found = Some(slot);
            break;
        }
        table = table_of(e);
        shift = shift.wrapping_sub(9);
        mask = 511;
        rem -= 1;
    }
    if let Some(slot) = found {
        s.write(slot, 0);
        a.invalidate_stage2_vmid(asid);
    }
}

/// Map a 4 KiB / 2 MiB / 1 GiB frame into a Stage-2 VSpace at `ipa`.
#[allow(clippy::too_many_arguments)]
pub fn map_frame<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    root: u64,
    asid: u64,
    ipa: u64,
    vm: u64,
    attr: u64,
    ptr: u64,
    size: FrameSize,
    rights: u64,
    is_device: bool,
    mapped_asid: u64,
    mapped_vaddr: u64,
    slot: Slot,
) -> KResult<()> {
    let shift = size.bits();
    let ipa_bits = a.s2_ipa_bits();
    if ipa & (1u64 << (shift & 63)).wrapping_sub(1) != 0 {
        return Err(Exc::Sys(SysError::AlignmentError));
    }
    if mapped_asid != 0 {
        if mapped_asid != asid {
            return invalid_cap(1);
        }
        if mapped_vaddr != ipa {
            return invalid_arg(0);
        }
    } else {
        let last = ipa.wrapping_add((1u64 << (shift & 63)).wrapping_sub(1));
        if last > ipa_limit(ipa_bits) || last < ipa {
            return invalid_arg(0);
        }
    }
    let lu = lookup_slot(s, root, ipa, ipa_bits);
    if lu.shift != shift {
        return Err(Exc::Sys(SysError::FailedLookup {
            source: false,
            lf: LookupFault::MissingCapability { bits_left: lu.shift },
        }));
    }
    let cap_read = vspace::rights_readable(rights);
    let e = make_s2_leaf(layout::paddr(ptr), vm, cap_read, attr, shift);
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(
        s,
        Cap::Frame { ptr, size, rights, is_device, mapped: e != 0, is_ept: e != 0, asid: if e != 0 { asid } else { 0 }, vaddr: if e != 0 { ipa } else { 0 } },
    );
    install_s2_leaf(s, a, lu, e, root, asid, ipa, ptr, is_device, attr);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn install_s2_leaf<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lu: S2Slot,
    e: u64,
    _root: u64,
    asid: u64,
    ipa: u64,
    ptr: u64,
    is_device: bool,
    attr: u64,
) {
    let old = s.read(lu.slot);
    if is_leaf(old, lu.shift) {
        if e != 0 && (old ^ e) & S2_BBM_MASK == 0 {
            s.write(lu.slot, e);
            a.invalidate_stage2_page(asid, ipa);
            return;
        }
        s.write(lu.slot, 0);
        a.invalidate_stage2_page(asid, ipa);
    }
    if e != 0 && !is_device && attr & arm_vm_attr::PAGE_CACHEABLE == 0 {
        a.cache_op(vspace::CACHE_CLEAN_INVALIDATE, 0, asid, ipa, 1u64 << (lu.shift & 63), layout::paddr(ptr));
    }
    s.write(lu.slot, e);
}

/// Unmap a Stage-2 frame (matches shared `objects.rs` call signature).
pub fn unmap<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, ipa: u64, ptr: u64, shift: u64, _is_table: bool) {
    let root = match find(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let lu = lookup_slot(s, root, ipa, a.s2_ipa_bits());
    if lu.shift != shift {
        return;
    }
    let e = s.read(lu.slot);
    if !is_leaf(e, lu.shift) || leaf_base(e, lu.shift) != layout::paddr(ptr) {
        return;
    }
    s.write(lu.slot, 0);
    a.invalidate_stage2_page(asid, ipa);
}

/// Cache maintenance on a Stage-2 mapped frame (through the kernel window).
#[allow(clippy::too_many_arguments)]
pub fn flush_frame<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    op: u64,
    invalidate: bool,
    asid: u64,
    ipa: u64,
    ptr: u64,
    size: FrameSize,
    is_device: bool,
    start: u64,
    end: u64,
) -> KResult<()> {
    let root = find(s, asid).map_err(|lf| Exc::Sys(SysError::FailedLookup { source: false, lf }))?;
    let lu = lookup_slot(s, root, ipa, a.s2_ipa_bits());
    let e = s.read(lu.slot);
    if lu.shift != size.bits() || !is_leaf(e, lu.shift) || leaf_base(e, lu.shift) != layout::paddr(ptr) {
        return invalid_cap(0);
    }
    if invalidate && s2_rights_of(e) != VM_READ_WRITE {
        return illegal();
    }
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if is_device {
        return Ok(());
    }
    let pstart = layout::paddr(ptr).wrapping_add(start);
    a.cache_op(op, 0, asid, ipa.wrapping_add(start), end - start, pstart);
    Ok(())
}

/// Stage-2 VSpace invocations (`ARMVSpaceClean_Data`, etc.).
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    cap: Cap,
    _slot: Slot,
    buf: u64,
    _ex: &[Slot; 3],
) -> KResult<()> {
    let op = if lbl == label::ARMVSpaceClean_Data {
        vspace::CACHE_CLEAN
    } else if lbl == label::ARMVSpaceInvalidate_Data {
        vspace::CACHE_INVALIDATE
    } else if lbl == label::ARMVSpaceCleanInvalidate_Data {
        vspace::CACHE_CLEAN_INVALIDATE
    } else if lbl == label::ARMVSpaceUnify_Instruction {
        vspace::CACHE_UNIFY
    } else {
        return illegal();
    };
    let ct = sched::cur_thread(s);
    if length < 2 {
        return truncated();
    }
    let start = msg::syscall_arg(s, ct, buf, 0);
    let end = msg::syscall_arg(s, ct, buf, 1);
    if end <= start {
        return invalid_arg(1);
    }
    let ipa_bits = a.s2_ipa_bits();
    if end - 1 > ipa_limit(ipa_bits) {
        return illegal();
    }
    let (r, asid) = root(s, cap, 0)?;
    let lu = lookup_slot(s, r, start, ipa_bits);
    let e = s.read(lu.slot);
    if !is_leaf(e, lu.shift) {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        return Ok(());
    }
    let m = (1u64 << (lu.shift & 63)).wrapping_sub(1);
    if start & !m != (end - 1) & !m {
        return range(start, (start & !m).wrapping_add(m));
    }
    if lbl == label::ARMVSpaceInvalidate_Data && s2_rights_of(e) != VM_READ_WRITE {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let pstart = leaf_base(e, lu.shift).wrapping_add(start & m);
    a.cache_op(op, 0, asid, start, end - start, pstart);
    Ok(())
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::obj::Tcb;
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::rc::Rc;
    use std::vec;
    use std::vec::Vec;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Ev {
        Write(u64, u64),
        InvS2Page(u64, u64),
        CacheClean(u64, u64),
        InvVmid(u64),
    }

    struct Mem {
        words: BTreeMap<u64, u64>,
        watch: u64,
        log: Rc<RefCell<Vec<Ev>>>,
    }
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 { *self.words.get(&a).unwrap_or(&0) }
        fn write(&mut self, a: u64, v: u64) {
            if a == self.watch { self.log.borrow_mut().push(Ev::Write(a, v)); }
            self.words.insert(a, v);
        }
        fn zero(&mut self, a: u64, len: u64) { for i in (0..len).step_by(8) { self.write(a + i, 0); } }
        fn clear_free(&mut self, a: u64, len: u64) { self.zero(a, len) }
        fn ks_base(&self) -> u64 { 0x10_0000 }
        fn cur_cpu(&self) -> u64 { 0 }
    }

    struct Mach {
        ipa: u64,
        log: Rc<RefCell<Vec<Ev>>>,
    }
    impl Arch for Mach {
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
        fn send_reschedule(&mut self, _: crate::machine::CoreMask) {}
        fn cache_op(&mut self, _: u64, _: u64, _: u64, _: u64, len: u64, paddr: u64) {
            self.log.borrow_mut().push(Ev::CacheClean(paddr, len));
        }
        fn hw_access_flag(&self) -> bool { true }
        fn max_spi(&self) -> u64 { 0 }
        fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
        fn s2_ipa_bits(&self) -> u64 { self.ipa }
        fn invalidate_stage2_page(&mut self, asid: u64, ipa: u64) {
            self.log.borrow_mut().push(Ev::InvS2Page(asid, ipa));
        }
        fn invalidate_stage2_vmid(&mut self, asid: u64) {
            self.log.borrow_mut().push(Ev::InvVmid(asid));
        }
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
    }

    #[test]
    fn stage2_geometry_40_44_48() {
        let g40 = geom(40);
        assert_eq!((g40.ipa_bits, g40.top_shift, g40.top_mask, g40.levels), (40, 30, 1023, 3));
        assert_eq!(geom(42).ipa_bits, 40);
        let g44 = geom(44);
        assert_eq!((g44.ipa_bits, g44.top_shift, g44.top_mask, g44.levels), (44, 39, 31, 4));
        let g48 = geom(48);
        assert_eq!((g48.ipa_bits, g48.top_shift, g48.top_mask, g48.levels), (48, 39, 511, 4));
    }

    #[test]
    fn stage2_descriptors_and_bbm() {
        // Table descriptor has no PXNTable.
        let t = make_s2_table(0x8000_0000);
        assert_eq!(t, 0x8000_0000 | 0b11);
        // Leaf: RW cacheable executable 4K page.
        let p = make_s2_leaf(0x8000_1000, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 12);
        assert_eq!(p & 0b11, 0b11);
        assert_eq!((p >> 2) & 0xf, 0b1111);
        assert_eq!((p >> 6) & 0x3, 0b11);
        assert_eq!((p >> 8) & 0x3, 0b11);
        assert_ne!(p & S2_AF, 0);
        assert_eq!((p >> 53) & 0x3, 0);
        // XN sets only bit 54 (0b10), bit 53 clear.
        let pxn = make_s2_leaf(0x8000_1000, VM_READ_ONLY, true, arm_vm_attr::EXECUTE_NEVER, 21);
        assert_eq!(pxn & 0b11, 0b01); // 2 MiB block
        assert_eq!((pxn >> 2) & 0xf, 0b0000); // device
        assert_eq!((pxn >> 6) & 0x3, 0b01); // RO
        assert_eq!((pxn >> 53) & 0x3, 0b10); // bit 54 only
        // KernelOnly returns 0 (unmapped).
        assert_eq!(make_s2_leaf(0x8000_1000, VM_KERNEL_ONLY, false, 0, 12), 0);

        // 40-bit / 44-bit / 48-bit walk + BBM + uncached RAM clean.
        for ipa_bits in [40u64, 44, 48] {
            let log = Rc::new(RefCell::new(Vec::new()));
            let mut s = Mem { words: BTreeMap::new(), watch: 0, log: log.clone() };
            let mut a = Mach { ipa: ipa_bits, log: log.clone() };
            let ct = Tcb(layout::pptr(0x60_0000));
            sched::set_cur_thread(&mut s, ct);
            let root = layout::pptr(0x10_0000);
            let ipa = if ipa_bits == 40 { 0x80_0000_1000 } else if ipa_bits == 44 { 0x400_0000_1000 } else { 0x8000_0000_1000 };
            let pt1 = layout::pptr(0x11_0000);
            let pt2 = layout::pptr(0x12_0000);
            let pt3 = layout::pptr(0x13_0000);
            let s1 = Slot(layout::pptr(0x70_0000));
            let s2 = Slot(layout::pptr(0x70_0020));
            let s3 = Slot(layout::pptr(0x70_0040));
            let fslot = Slot(layout::pptr(0x70_0060));
            assert!(map_table(&mut s, &mut a, root, 1, ipa, pt1, s1).is_ok());
            assert!(map_table(&mut s, &mut a, root, 1, ipa, pt2, s2).is_ok());
            if ipa_bits >= 44 {
                assert!(map_table(&mut s, &mut a, root, 1, ipa, pt3, s3).is_ok());
            }
            let lu = lookup_slot(&s, root, ipa, ipa_bits);
            assert_eq!(lu.shift, 12, "ipa_bits {ipa_bits}");
            s.watch = lu.slot;
            let frame_va = layout::pptr(0x40_0000);
            // Uncached RAM cleans to PoC before writing descriptor.
            assert!(map_frame(&mut s, &mut a, root, 1, ipa, VM_READ_WRITE, 0, frame_va, FrameSize::Small, VM_READ_WRITE, false, 0, 0, fslot).is_ok());
            let e_nc = make_s2_leaf(0x40_0000, VM_READ_WRITE, true, 0, 12);
            assert_eq!(*log.borrow(), vec![Ev::CacheClean(0x40_0000, 4096), Ev::Write(lu.slot, e_nc)]);
            // Changing memory type triggers BBM (write 0 -> InvS2Page -> write new).
            log.borrow_mut().clear();
            assert!(map_frame(&mut s, &mut a, root, 1, ipa, VM_READ_WRITE, arm_vm_attr::PAGE_CACHEABLE, frame_va, FrameSize::Small, VM_READ_WRITE, false, 1, ipa, fslot).is_ok());
            let e_wb = make_s2_leaf(0x40_0000, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 12);
            assert_eq!(*log.borrow(), vec![Ev::Write(lu.slot, 0), Ev::InvS2Page(1, ipa), Ev::Write(lu.slot, e_wb)]);
            // Changing only permissions updates in place + flushes.
            log.borrow_mut().clear();
            assert!(map_frame(&mut s, &mut a, root, 1, ipa, VM_READ_ONLY, arm_vm_attr::PAGE_CACHEABLE, frame_va, FrameSize::Small, VM_READ_WRITE, false, 1, ipa, fslot).is_ok());
            let e_ro = make_s2_leaf(0x40_0000, VM_READ_ONLY, true, arm_vm_attr::PAGE_CACHEABLE, 12);
            assert_eq!(*log.borrow(), vec![Ev::Write(lu.slot, e_ro), Ev::InvS2Page(1, ipa)]);
        }
    }

    #[test]
    fn stage2_cache_op_exclusive_end_boundary() {
        let log = Rc::new(RefCell::new(Vec::new()));
        let mut s = Mem { words: BTreeMap::new(), watch: 0, log: log.clone() };
        let mut a = Mach { ipa: 40, log: log.clone() };
        let ct = Tcb(layout::pptr(0x60_0000));
        sched::set_cur_thread(&mut s, ct);

        let root = layout::pptr(0x10_0000);
        let asid = 1u64;
        // Register Stage-2 root in ASID pool (bit 0 == 1 marks Stage-2).
        let pool = layout::pptr(0x15_0000);
        crate::obj::ks_set(&mut s, layout::ks::ASID_TABLE, pool);
        s.write(pool + asid * 8, root | 1);
        let cap = Cap::Ept { ptr: root, level: 0, mapped: true, asid, vaddr: 0 };
        let ex = [Slot(0), Slot(0), Slot(0)];

        let lim = ipa_limit(40); // (1 << 40) - 1
        let last_page = lim - 4095;
        // Exclusive end == ipa_limit + 1 (entire last page) succeeds.
        ct.set_reg(&mut s, msg::msg_register(0), last_page);
        ct.set_reg(&mut s, msg::msg_register(1), lim + 1);
        assert!(decode(&mut s, &mut a, label::ARMVSpaceClean_Data, 2, cap, Slot(0), 0, &ex).is_ok());
        // Exclusive end == ipa_limit + 2 (1 byte past limit) fails with IllegalOperation.
        ct.set_reg(&mut s, msg::msg_register(0), last_page);
        ct.set_reg(&mut s, msg::msg_register(1), lim + 2);
        assert!(matches!(
            decode(&mut s, &mut a, label::ARMVSpaceClean_Data, 2, cap, Slot(0), 0, &ex),
            Err(Exc::Sys(SysError::IllegalOperation))
        ));
    }

    struct S2World {
        s: Mem,
        a: Mach,
        log: Rc<RefCell<Vec<Ev>>>,
        ipa: u64,
        /// The page tables on the walk to `ipa`, top first, and the slots
        /// that point to them.
        tables: Vec<u64>,
        slots: Vec<u64>,
    }

    /// A Stage-2 VSpace for ASID 1 with page tables mapped down to the last
    /// table level at an IPA near the top of the `ipa_bits` space.
    fn s2_world(ipa_bits: u64) -> S2World {
        let log = Rc::new(RefCell::new(Vec::new()));
        let mut s = Mem { words: BTreeMap::new(), watch: 0, log: log.clone() };
        let mut a = Mach { ipa: ipa_bits, log: log.clone() };
        sched::set_cur_thread(&mut s, Tcb(layout::pptr(0x60_0000)));
        let root = layout::pptr(0x10_0000);
        let pool = layout::pptr(0x15_0000);
        crate::obj::ks_set(&mut s, layout::ks::ASID_TABLE, pool);
        s.write(pool + 8, root | 1);
        let ipa = if ipa_bits == 40 { 0x80_0000_1000 } else if ipa_bits == 44 { 0x400_0000_1000 } else { 0x8000_0000_1000 };
        let n = geom(ipa_bits).levels - 1;
        let mut tables = Vec::new();
        let mut slots = Vec::new();
        for i in 0..n {
            let pt = layout::pptr(0x11_0000 + i * 0x1_0000);
            slots.push(lookup_slot(&s, root, ipa, ipa_bits).slot);
            assert!(map_table(&mut s, &mut a, root, 1, ipa, pt, Slot(layout::pptr(0x70_0000 + i * 0x20))).is_ok());
            tables.push(pt);
        }
        assert_eq!(lookup_slot(&s, root, ipa, ipa_bits).shift, PAGE_BITS);
        S2World { s, a, log, ipa, tables, slots }
    }

    /// Astra R1 P1: a Stage-2 frame cap at a 48-bit IPA with bit 47 set,
    /// read back from its slot, keeps the IPA unsigned (Stage-1 addresses
    /// are sign-extended, IPAs never): remapping it with new rights works,
    /// and the invalidation gets the IPA as mapped.
    #[test]
    fn a_stage2_frame_at_a_bit_47_ipa_remaps_from_its_slot() {
        let mut w = s2_world(48);
        assert_ne!(w.ipa & (1 << 47), 0);
        let root = layout::pptr(0x10_0000);
        let fslot = Slot(layout::pptr(0x70_1000));
        let frame_va = layout::pptr(0x40_0000);
        assert!(map_frame(&mut w.s, &mut w.a, root, 1, w.ipa, VM_READ_WRITE, arm_vm_attr::PAGE_CACHEABLE, frame_va, FrameSize::Small, VM_READ_WRITE, false, 0, 0, fslot).is_ok());
        let (mapped_asid, mapped_vaddr, is_ept) = match fslot.cap(&w.s) {
            Cap::Frame { asid, vaddr, is_ept, .. } => (asid, vaddr, is_ept),
            _ => panic!("no frame cap"),
        };
        assert!(is_ept);
        assert_eq!((mapped_asid, mapped_vaddr), (1, w.ipa));
        w.log.borrow_mut().clear();
        let r = map_frame(&mut w.s, &mut w.a, root, 1, w.ipa, VM_READ_ONLY, arm_vm_attr::PAGE_CACHEABLE, frame_va, FrameSize::Small, VM_READ_WRITE, false, mapped_asid, mapped_vaddr, fslot);
        assert!(r.is_ok());
        assert_eq!(w.log.borrow().last(), Some(&Ev::InvS2Page(1, w.ipa)));
        assert!(matches!(fslot.cap(&w.s), Cap::Frame { vaddr, .. } if vaddr == w.ipa));
        // A Stage-1 frame cap at the same 48 bits is a TTBR1 address.
        let s1 = Cap::Frame { ptr: frame_va, size: FrameSize::Small, rights: VM_READ_WRITE, is_device: false, mapped: true, is_ept: false, asid: 1, vaddr: w.ipa | 0xffff_0000_0000_0000 };
        let (a0, a1) = s1.encode();
        assert!(Cap::decode(a0, a1) == s1);
    }

    /// Run `f` (an unmap of `w.ipa`): the words it changed and the events.
    fn changes(w: &mut S2World, f: impl FnOnce(&mut Mem, &mut Mach, u64)) -> (Vec<(u64, u64)>, Vec<Ev>) {
        let before = w.s.words.clone();
        w.log.borrow_mut().clear();
        f(&mut w.s, &mut w.a, w.ipa);
        let changed = w.s.words.iter().filter(|&(k, v)| before.get(k).unwrap_or(&0) != v).map(|(&k, &v)| (k, v)).collect();
        let ev = w.log.borrow().clone();
        (changed, ev)
    }

    /// The walk reaches the table at each level (3- and 4-level
    /// geometries): that slot alone is cleared, then the VMID is flushed.
    /// `vspace::unmap_page_table` dispatches a Stage-2 ASID here.
    #[test]
    fn unmap_table_clears_the_slot_pointing_to_the_table() {
        for ipa_bits in [40u64, 44, 48] {
            let n = s2_world(ipa_bits).tables.len();
            for i in 0..n {
                let mut w = s2_world(ipa_bits);
                let (pt, slot) = (w.tables[i], w.slots[i]);
                let got = changes(&mut w, |s, a, ipa| unmap_table(s, a, 1, ipa, pt));
                assert_eq!(got, (vec![(slot, 0)], vec![Ev::InvVmid(1)]), "ipa_bits {ipa_bits} level {i}");
                let mut w = s2_world(ipa_bits);
                let got = changes(&mut w, |s, a, ipa| vspace::unmap_page_table(s, a, 1, ipa, pt));
                assert_eq!(got, (vec![(slot, 0)], vec![Ev::InvVmid(1)]), "dispatch ipa_bits {ipa_bits} level {i}");
            }
        }
    }

    /// Every other exit changes nothing and flushes nothing: an ASID with
    /// no Stage-2 VSpace (none, or a Stage-1 one), a walk that meets an
    /// entry that is not a table descriptor before the table, and a walk
    /// that runs through every table level without meeting it.
    #[test]
    fn unmap_table_without_the_table_on_the_walk_changes_nothing() {
        for ipa_bits in [40u64, 44, 48] {
            let mut w = s2_world(ipa_bits);
            let pt = w.tables[0];
            assert_eq!(changes(&mut w, |s, a, ipa| unmap_table(s, a, 2, ipa, pt)), (vec![], vec![]));
            let mut w = s2_world(ipa_bits);
            let pool = layout::pptr(0x15_0000);
            w.s.write(pool + 8, layout::pptr(0x10_0000));
            assert_eq!(changes(&mut w, |s, a, ipa| unmap_table(s, a, 1, ipa, pt)), (vec![], vec![]));
            let block = make_s2_leaf(0x40_0000, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 30);
            for e in [0, block] {
                let mut w = s2_world(ipa_bits);
                let last = *w.tables.last().unwrap();
                let first = w.slots[0];
                w.s.write(first, e);
                assert_eq!(changes(&mut w, |s, a, ipa| unmap_table(s, a, 1, ipa, last)), (vec![], vec![]), "ipa_bits {ipa_bits} entry {e:#x}");
            }
            let mut w = s2_world(ipa_bits);
            let other = layout::pptr(0x14_0000);
            assert_eq!(changes(&mut w, |s, a, ipa| unmap_table(s, a, 1, ipa, other)), (vec![], vec![]), "ipa_bits {ipa_bits}");
        }
    }
}
