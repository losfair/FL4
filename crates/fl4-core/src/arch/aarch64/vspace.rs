//! AArch64 virtual memory without EL2: VSpaces, page tables, frames, ASIDs,
//! cache maintenance and VM faults (seL4 arch/arm/64/kernel/vspace.c), with
//! l4h's TestAndClearAccessed (0023) and DeriveSubframe (0029).
//!
//! User address spaces use the stage-1 4 KiB-granule format through
//! TTBR0_EL1 with four levels: the VSpace (level 0, a `Cap::Pml4`) and page
//! tables at levels 1-3 (all `Cap::PageTable`; the level is where a table
//! is mapped). The kernel lives in the TTBR1 half, so a VSpace holds no
//! kernel mappings. ASIDs are the 16-bit hardware ASIDs (l4h 0016).

use crate::capability::{mask_vm_rights, Cap, FrameSize, Rights, VM_KERNEL_ONLY, VM_READ_ONLY, VM_READ_WRITE};
use crate::cdt;
use crate::cspace;
use crate::error::{illegal, invalid_arg, invalid_cap, range, truncated, Exc, KResult, LookupFault, SysError};
use crate::layout::{self, ks, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{ks_get, ks_set, Slot, Tcb};
use crate::sched;
use fl4_abi::consts::{arm_vm_attr, bits, USER_TOP};
use fl4_abi::label;

// Descriptor bits (Arm ARM D8.3).
const D_VALID: u64 = 1 << 0;
/// Bit 1: a table at levels 0-2, a page at level 3; clear for a block.
const D_TABLE_OR_PAGE: u64 = 1 << 1;
const D_ATTR_SHIFT: u64 = 2;
/// AP[2:1]: 0 EL1 only, 1 EL1 and EL0 read-write, 3 read-only for both.
const D_AP_SHIFT: u64 = 6;
const D_SH_INNER: u64 = 3 << 8;
const D_AF: u64 = 1 << 10;
const D_NG: u64 = 1 << 11;
const D_PXN: u64 = 1 << 53;
const D_UXN: u64 = 1 << 54;
/// Table descriptors: the kernel never executes anything below them.
const D_PXN_TABLE: u64 = 1 << 59;
const ADDR_MASK: u64 = 0x0000_ffff_ffff_f000;
/// Descriptor bits whose change needs break-before-make (Arm ARM DDI 0487
/// D8.14.1): all but the access permissions, execute-never and the access
/// flag, which may change in place.
const BBM_MASK: u64 = !((3 << D_AP_SHIFT) | D_AF | D_UXN | D_PXN);

/// MAIR_EL1 attribute indices; the backend programs `MAIR`.
pub const ATTR_NORMAL: u64 = 0;
pub const ATTR_DEVICE_NGNRNE: u64 = 1;
pub const ATTR_NORMAL_NC: u64 = 2;
pub const ATTR_DEVICE_NGNRE: u64 = 3;
/// Normal write-back read/write-allocate, Device-nGnRnE, Normal
/// non-cacheable, Device-nGnRE.
pub const MAIR: u64 = 0xff | (0x00 << 8) | (0x44 << 16) | (0x04 << 24);

/// Cache maintenance operations (`Arch::cache_op`).
pub const CACHE_CLEAN: u64 = 0;
pub const CACHE_INVALIDATE: u64 = 1;
pub const CACHE_CLEAN_INVALIDATE: u64 = 2;
pub const CACHE_UNIFY: u64 = 3;

pub const ASID_LOW_BITS: u64 = 9;
/// 16-bit ASIDs: 128 pools of 512.
pub const N_ASID_POOLS: u64 = 1 << bits::NUM_ASID_POOLS;
pub const ASID_BITS: u64 = 16;

const PAGE_BITS: u64 = 12;
const TOP_LEVEL_SHIFT: u64 = 39;

fn entry_addr(table: u64, vaddr: u64, shift: u64) -> u64 {
    table.wrapping_add(((vaddr >> (shift & 63)) & 511).wrapping_mul(8))
}

fn table_of(e: u64) -> u64 {
    layout::pptr(e & ADDR_MASK)
}

/// A table descriptor at a level above 3.
fn is_table(e: u64, shift: u64) -> bool {
    shift > PAGE_BITS && e & (D_VALID | D_TABLE_OR_PAGE) == (D_VALID | D_TABLE_OR_PAGE)
}

/// A page (level 3) or block (levels 1 and 2) descriptor.
fn is_page(e: u64, shift: u64) -> bool {
    if shift == PAGE_BITS {
        e & (D_VALID | D_TABLE_OR_PAGE) == (D_VALID | D_TABLE_OR_PAGE)
    } else {
        e & (D_VALID | D_TABLE_OR_PAGE) == D_VALID
    }
}

/// The physical address a page or block descriptor covering 2^shift maps.
fn page_base(e: u64, shift: u64) -> u64 {
    e & ADDR_MASK & !((1u64 << (shift & 63)).wrapping_sub(1))
}

/// seL4 `lookupPTSlot`: the deepest slot for `vaddr` reachable through
/// table descriptors, and the shift of the region it covers.
#[derive(Clone, Copy)]
struct PtSlot {
    slot: u64,
    shift: u64,
}

fn lookup_pt_slot<S: Store>(s: &S, root: u64, vaddr: u64) -> PtSlot {
    let mut shift = TOP_LEVEL_SHIFT;
    let mut slot = entry_addr(root, vaddr, shift);
    let mut level: u64 = 3;
    while level > 0 && is_table(s.read(slot), shift) {
        level -= 1;
        shift = shift.wrapping_sub(9);
        slot = entry_addr(table_of(s.read(slot)), vaddr, shift);
    }
    PtSlot { slot, shift }
}

// ---- entries ---------------------------------------------------------------

/// seL4 `APFromVMRights` (EL1).
fn ap_bits(rights: u64) -> u64 {
    if rights == VM_READ_WRITE {
        1
    } else if rights == VM_READ_ONLY {
        3
    } else {
        0
    }
}

/// seL4 `vmRightsFromPTE`.
fn rights_of(e: u64) -> u64 {
    let ap = (e >> D_AP_SHIFT) & 3;
    if ap == 1 {
        VM_READ_WRITE
    } else if ap == 3 {
        VM_READ_ONLY
    } else {
        VM_KERNEL_ONLY
    }
}

/// seL4 `makeUserPagePTE`. The kernel never executes user pages (PXN).
fn make_user_page(paddr: u64, rights: u64, cap_read: bool, attr: u64, shift: u64) -> u64 {
    let xn = attr & arm_vm_attr::EXECUTE_NEVER != 0 || !cap_read;
    let cacheable = attr & arm_vm_attr::PAGE_CACHEABLE != 0;
    let (idx, sh) = if cacheable { (ATTR_NORMAL, D_SH_INNER) } else { (ATTR_DEVICE_NGNRNE, 0) };
    (paddr & ADDR_MASK)
        | (if shift == PAGE_BITS { D_VALID | D_TABLE_OR_PAGE } else { D_VALID })
        | (idx << D_ATTR_SHIFT)
        | (ap_bits(rights) << D_AP_SHIFT)
        | sh
        | D_AF
        | D_NG
        | D_PXN
        | (if xn { D_UXN } else { 0 })
}

fn make_user_table(paddr: u64) -> u64 {
    (paddr & ADDR_MASK) | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE
}

/// A page of the initial thread's image (seL4 `map_it_frame_cap`):
/// read-write, cacheable, executable.
pub fn it_page_entry(paddr: u64) -> u64 {
    make_user_page(paddr, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, PAGE_BITS)
}

/// A page table of the initial thread's address space.
pub fn it_table_entry(paddr: u64) -> u64 {
    make_user_table(paddr)
}

fn page_shift(size: FrameSize) -> u64 {
    size.bits()
}

// ---- ASIDs -------------------------------------------------------------------

fn asid_table<S: Store>(s: &S, high: u64) -> u64 {
    ks_get(s, ks::ASID_TABLE.wrapping_add((high & (N_ASID_POOLS - 1)).wrapping_mul(8)))
}

fn set_asid_table<S: Store>(s: &mut S, high: u64, pool: u64) {
    ks_set(s, ks::ASID_TABLE.wrapping_add((high & (N_ASID_POOLS - 1)).wrapping_mul(8)), pool)
}

/// seL4 `findVSpaceForASID`.
pub fn find_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    if asid >> ASID_BITS != 0 {
        return Err(LookupFault::InvalidRoot);
    }
    let pool = asid_table(s, asid >> ASID_LOW_BITS);
    if pool == 0 {
        return Err(LookupFault::InvalidRoot);
    }
    let root = s.read(pool.wrapping_add((asid & 511).wrapping_mul(8)));
    if root == 0 {
        return Err(LookupFault::InvalidRoot);
    }
    Ok(root)
}

pub fn find_vspace_for_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    find_asid(s, asid)
}

pub fn is_valid_vtable_root(c: Cap) -> bool {
    matches!(c, Cap::Pml4 { mapped: true, .. })
}

/// seL4 `checkValidIPCBuffer`.
pub fn check_valid_ipc_buffer(vptr: u64, c: Cap) -> KResult<()> {
    match c {
        Cap::Frame { is_device, .. } => {
            if is_device {
                return illegal();
            }
        }
        _ => return illegal(),
    }
    if vptr & ((1u64 << bits::IPC_BUFFER) - 1) != 0 {
        return Err(Exc::Sys(SysError::AlignmentError));
    }
    Ok(())
}

// ---- address-space switch ------------------------------------------------------

/// The empty user table threads without an address space run on (seL4
/// `armKSGlobalUserVSpace`), with the reserved ASID 0.
pub fn kernel_root<S: Store>(s: &S) -> u64 {
    ks_get(s, ks::KERNEL_ROOT)
}

/// seL4 `setVMRoot`.
#[inline(always)]
pub fn set_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    match t.slot(tl::SLOT_VTABLE).cap(s) {
        Cap::Pml4 { ptr, mapped: true, asid } => match find_vspace_for_asid(s, asid) {
            Ok(r) if r == ptr => a.set_vspace(ptr, asid),
            _ => set_kernel_vm_root(s, a),
        },
        _ => set_kernel_vm_root(s, a),
    }
}

pub fn set_kernel_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let k = kernel_root(s);
    a.set_vspace(k, 0);
}

/// The kernel is in the TTBR1 half: a VSpace holds no kernel mappings.
pub fn copy_global_mappings<S: Store>(s: &mut S, new_root: u64) {
    let _ = (s, new_root);
}

// ---- unmapping -----------------------------------------------------------------

/// seL4 `unmapPage`.
pub fn unmap_page<S: Store, A: Arch>(s: &mut S, a: &mut A, size: FrameSize, asid: u64, vaddr: u64, pptr: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift != page_shift(size) {
        return;
    }
    let e = s.read(lu.slot);
    if !is_page(e, lu.shift) || page_base(e, lu.shift) != layout::paddr(pptr) {
        return;
    }
    s.write(lu.slot, 0);
    a.invalidate_page(asid, vaddr);
}

/// seL4 `unmapPageTable`: find the slot that points to `pt` on the walk to
/// `vaddr`.
pub fn unmap_page_table<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pt: u64) {
    let root = match find_vspace_for_asid(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let mut table = root;
    let mut shift = TOP_LEVEL_SHIFT;
    let mut level: u64 = 0;
    while level < 3 {
        let slot = entry_addr(table, vaddr, shift);
        let e = s.read(slot);
        if !is_table(e, shift) {
            return;
        }
        if table_of(e) == pt {
            s.write(slot, 0);
            a.invalidate_asid(asid);
            return;
        }
        table = table_of(e);
        shift = shift.wrapping_sub(9);
        level += 1;
    }
}

/// x86 levels; AArch64 page tables are all `Cap::PageTable`.
pub fn unmap_page_directory<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pd: u64) {
    unmap_page_table(s, a, asid, vaddr, pd)
}

pub fn unmap_pdpt<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pdpt: u64) {
    unmap_page_table(s, a, asid, vaddr, pdpt)
}

/// seL4 `deleteASID`.
pub fn delete_asid<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, root: u64) {
    let pool = asid_table(s, asid >> ASID_LOW_BITS);
    if pool == 0 {
        return;
    }
    let e = pool.wrapping_add((asid & 511).wrapping_mul(8));
    if s.read(e) == root {
        a.invalidate_asid(asid);
        s.write(e, 0);
        let ct = sched::cur_thread(s);
        set_vm_root(s, a, ct);
    }
}

/// seL4 `deleteASIDPool`.
pub fn delete_asid_pool<S: Store, A: Arch>(s: &mut S, a: &mut A, base: u64, pool: u64) {
    if asid_table(s, base >> ASID_LOW_BITS) != pool {
        return;
    }
    let mut i = 0;
    while i < 512 {
        if s.read(pool.wrapping_add(i * 8)) != 0 {
            a.invalidate_asid(base.wrapping_add(i));
        }
        i += 1;
    }
    set_asid_table(s, base >> ASID_LOW_BITS, 0);
    let ct = sched::cur_thread(s);
    set_vm_root(s, a, ct);
}

// ---- VM faults -------------------------------------------------------------------

/// seL4 `handleVMFault`: `addr` is FAR_EL1 for a data abort and the
/// faulting PC for an instruction abort, `code` the ESR.
pub fn vm_fault(addr: u64, code: u64, instruction: bool) -> crate::error::Fault {
    crate::error::Fault::VmFault { addr, fsr: code, instruction }
}

// ---- invocations -------------------------------------------------------------------

fn extra(extra: &[Slot; 3], i: usize) -> Option<Slot> {
    if i >= 3 || extra[i].is_null() {
        None
    } else {
        Some(extra[i])
    }
}

/// The VSpace and ASID of a mapped VSpace cap that its ASID still names.
fn check_vspace<S: Store>(s: &S, vcap: Cap, cap_arg: u64) -> KResult<(u64, u64)> {
    let (root, asid) = match vcap {
        Cap::Pml4 { ptr, mapped: true, asid } => (ptr, asid),
        _ => return invalid_cap(cap_arg),
    };
    match find_vspace_for_asid(s, asid) {
        Err(lf) => Err(Exc::Sys(SysError::FailedLookup { source: false, lf })),
        Ok(r) => {
            if r != root {
                invalid_cap(cap_arg)
            } else {
                Ok((root, asid))
            }
        }
    }
}

fn reply1<S: Store>(s: &mut S, t: Tcb, call: bool, v: u64) {
    if call {
        let buf = msg::lookup_ipc_buffer(s, true, t);
        t.set_reg(s, crate::layout::reg::BADGE, 0);
        let n = msg::set_mr(s, t, buf, 0, v);
        msg::set_msg_info(s, t, MessageInfo::new(0, 0, 0, n));
    }
    sched::set_thread_state(s, t, sched::TS_RUNNING);
}

/// A frame cap's fields.
#[derive(Clone, Copy)]
struct FrameCap {
    ptr: u64,
    size: FrameSize,
    rights: u64,
    is_device: bool,
    mapped: bool,
    asid: u64,
    vaddr: u64,
}

fn as_frame(c: Cap) -> Option<FrameCap> {
    match c {
        Cap::Frame { ptr, size, rights, is_device, mapped, asid, vaddr, .. } => Some(FrameCap { ptr, size, rights, is_device, mapped, asid, vaddr }),
        _ => None,
    }
}

fn unmapped_frame(f: FrameCap) -> Cap {
    Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: false, is_ept: false, asid: 0, vaddr: 0 }
}

fn is_cache_label(lbl: u64) -> bool {
    lbl == label::ARMPageClean_Data
        || lbl == label::ARMPageInvalidate_Data
        || lbl == label::ARMPageCleanInvalidate_Data
        || lbl == label::ARMPageUnify_Instruction
}

fn page_cache_op(lbl: u64) -> u64 {
    if lbl == label::ARMPageClean_Data || lbl == label::ARMVSpaceClean_Data {
        CACHE_CLEAN
    } else if lbl == label::ARMPageInvalidate_Data || lbl == label::ARMVSpaceInvalidate_Data {
        CACHE_INVALIDATE
    } else if lbl == label::ARMPageCleanInvalidate_Data || lbl == label::ARMVSpaceCleanInvalidate_Data {
        CACHE_CLEAN_INVALIDATE
    } else {
        CACHE_UNIFY
    }
}

fn is_invalidate(lbl: u64) -> bool {
    lbl == label::ARMPageInvalidate_Data || lbl == label::ARMVSpaceInvalidate_Data
}

#[allow(clippy::too_many_arguments)]
fn decode_frame<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let f = match as_frame(cap) {
        Some(f) => f,
        None => return illegal(),
    };
    let ct = sched::cur_thread(s);
    if lbl == label::ARMPageMap {
        decode_page_map(s, a, length, slot, f, buf, ex)
    } else if lbl == label::ARMPageUnmap {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        if f.mapped && f.asid != 0 {
            unmap_page(s, a, f.size, f.asid, f.vaddr, f.ptr);
        }
        slot.set_cap(s, unmapped_frame(f));
        Ok(())
    } else if is_cache_label(lbl) {
        decode_page_flush(s, a, lbl, length, f, buf)
    } else if lbl == label::ARMPageGetAddress {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        reply1(s, ct, call, layout::paddr(f.ptr));
        Ok(())
    } else if lbl == label::ARMPageTestAndClearAccessed {
        decode_test_and_clear_accessed(s, a, f, call)
    } else if lbl == label::ARMPageDeriveSubframe {
        derive_subframe(s, length, slot, cap, buf, ex)
    } else {
        illegal()
    }
}

fn decode_page_map<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, slot: Slot, f: FrameCap, buf: u64, ex: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let vslot = match extra(ex, 0) {
        Some(x) if length >= 3 => x,
        _ => return truncated(),
    };
    let vaddr = msg::syscall_arg(s, ct, buf, 0);
    let rights_mask = msg::syscall_arg(s, ct, buf, 1);
    let attr = msg::syscall_arg(s, ct, buf, 2);
    let vm = mask_vm_rights(f.rights, Rights::from_word(rights_mask));
    let (root, asid) = check_vspace(s, vslot.cap(s), 1)?;
    let shift = page_shift(f.size);
    if vaddr & (1u64 << (shift & 63)).wrapping_sub(1) != 0 {
        return Err(Exc::Sys(SysError::AlignmentError));
    }
    if f.asid != 0 {
        if f.asid != asid {
            return invalid_cap(1);
        }
        if f.vaddr != vaddr {
            return invalid_arg(0);
        }
    } else {
        let last = vaddr.wrapping_add((1u64 << (shift & 63)).wrapping_sub(1));
        if last > USER_TOP || last < vaddr {
            return invalid_arg(0);
        }
    }
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift != shift {
        return Err(Exc::Sys(SysError::FailedLookup { source: false, lf: LookupFault::MissingCapability { bits_left: lu.shift } }));
    }
    let cap_read = f.rights == VM_READ_ONLY || f.rights == VM_READ_WRITE;
    let e = make_user_page(layout::paddr(f.ptr), vm, cap_read, attr, shift);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: true, is_ept: false, asid, vaddr });
    install_page(s, a, lu, e, root, asid, vaddr, f, attr);
    Ok(())
}

/// seL4 `performPageInvocationMap`, with break-before-make (Arm ARM DDI
/// 0487 D8.14.1) where it is needed: a live page or block descriptor whose
/// output address, memory type, shareability, nG or type changes is
/// cleared and its TLB entries are invalidated on every core before the
/// new descriptor is written, so no core ever holds the old and the new
/// translation at once. One that changes only its permissions or access
/// flag, or not at all, is rewritten in place (another core's access then
/// never finds it invalid and faults) and then invalidated: l4h 0023's
/// TestAndClearAccessed clears AF without a flush and relies on a remap to
/// drop the stale entry.
///
/// A RAM frame newly mapped non-cacheable has its lines cleaned and
/// invalidated to the point of coherency before its descriptor: the kernel
/// window maps it write-back, so zeroing (retype, untyped reset) or an
/// earlier cacheable mapping may have left dirty lines that a
/// non-cacheable access would read past (old data in memory) and that
/// would later be written back over it. RAM frames always lie in the
/// kernel window, so this never walks the user mapping. Device frames are
/// never cache-maintained.
#[allow(clippy::too_many_arguments)]
fn install_page<S: Store, A: Arch>(s: &mut S, a: &mut A, lu: PtSlot, e: u64, root: u64, asid: u64, vaddr: u64, f: FrameCap, attr: u64) {
    let old = s.read(lu.slot);
    if is_page(old, lu.shift) {
        if (old ^ e) & BBM_MASK == 0 {
            s.write(lu.slot, e);
            a.invalidate_page(asid, vaddr);
            return;
        }
        s.write(lu.slot, 0);
        a.invalidate_page(asid, vaddr);
    }
    if !f.is_device && attr & arm_vm_attr::PAGE_CACHEABLE == 0 {
        a.cache_op(CACHE_CLEAN_INVALIDATE, root, asid, vaddr, 1u64 << (lu.shift & 63), layout::paddr(f.ptr));
    }
    s.write(lu.slot, e);
}

/// The page or block descriptor mapping `f` at its recorded address, if
/// it still does.
fn mapped_entry<S: Store>(s: &S, f: FrameCap, root: u64) -> Option<PtSlot> {
    let lu = lookup_pt_slot(s, root, f.vaddr);
    let e = s.read(lu.slot);
    if lu.shift != page_shift(f.size) || !is_page(e, lu.shift) || page_base(e, lu.shift) != layout::paddr(f.ptr) {
        return None;
    }
    Some(lu)
}

/// Page Clean_Data, Invalidate_Data, CleanInvalidate_Data and
/// Unify_Instruction: `start` and `end` are offsets in the frame.
fn decode_page_flush<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, f: FrameCap, buf: u64) -> KResult<()> {
    let ct = sched::cur_thread(s);
    if length < 2 {
        return truncated();
    }
    if f.asid == 0 {
        return illegal();
    }
    let root = match find_vspace_for_asid(s, f.asid) {
        Ok(r) => r,
        Err(lf) => return Err(Exc::Sys(SysError::FailedLookup { source: false, lf })),
    };
    let start = msg::syscall_arg(s, ct, buf, 0);
    let end = msg::syscall_arg(s, ct, buf, 1);
    if end <= start {
        return invalid_arg(1);
    }
    let size = 1u64 << (page_shift(f.size) & 63);
    if start >= size || end > size {
        return invalid_arg(0);
    }
    let lu = match mapped_entry(s, f, root) {
        Some(x) => x,
        None => return invalid_cap(0),
    };
    if is_invalidate(lbl) && rights_of(s.read(lu.slot)) != VM_READ_WRITE {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let pstart = layout::paddr(f.ptr).wrapping_add(start);
    a.cache_op(page_cache_op(lbl), root, f.asid, f.vaddr.wrapping_add(start), end - start, pstart);
    Ok(())
}

/// VSpace Clean_Data, Invalidate_Data, CleanInvalidate_Data and
/// Unify_Instruction over [start, end) within one page.
fn decode_vspace_flush<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, cap: Cap, buf: u64) -> KResult<()> {
    let ct = sched::cur_thread(s);
    if length < 2 {
        return truncated();
    }
    let start = msg::syscall_arg(s, ct, buf, 0);
    let end = msg::syscall_arg(s, ct, buf, 1);
    if end <= start {
        return invalid_arg(1);
    }
    if end > USER_TOP {
        return illegal();
    }
    let (root, asid) = match cap {
        Cap::Pml4 { ptr, mapped: true, asid } => (ptr, asid),
        _ => return invalid_cap(0),
    };
    match find_vspace_for_asid(s, asid) {
        Err(lf) => return Err(Exc::Sys(SysError::FailedLookup { source: false, lf })),
        Ok(r) => {
            if r != root {
                return invalid_cap(0);
            }
        }
    }
    let lu = lookup_pt_slot(s, root, start);
    let e = s.read(lu.slot);
    if !is_page(e, lu.shift) {
        // Nothing is mapped, so nothing can be stale.
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        return Ok(());
    }
    let m = (1u64 << (lu.shift & 63)).wrapping_sub(1);
    if start & !m != (end - 1) & !m {
        return range(start, (start & !m).wrapping_add(m));
    }
    if is_invalidate(lbl) && rights_of(e) != VM_READ_WRITE {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let pstart = page_base(e, lu.shift).wrapping_add(start & m);
    a.cache_op(page_cache_op(lbl), root, asid, start, end - start, pstart);
    Ok(())
}

/// l4h 0023: report and clear the access flag of a mapped frame. The
/// flag is only set again by hardware access-flag management.
fn decode_test_and_clear_accessed<S: Store, A: Arch>(s: &mut S, a: &mut A, f: FrameCap, call: bool) -> KResult<()> {
    if matches!(f.size, FrameSize::Huge) || !f.mapped || f.asid == 0 || !a.hw_access_flag() {
        return illegal();
    }
    let root = match find_vspace_for_asid(s, f.asid) {
        Ok(r) => r,
        Err(_) => return invalid_cap(0),
    };
    let lu = match mapped_entry(s, f, root) {
        Some(x) => x,
        None => return invalid_cap(0),
    };
    let ct = sched::cur_thread(s);
    let old = s.read(lu.slot);
    s.write(lu.slot, old & !D_AF);
    reply1(s, ct, call, if old & D_AF != 0 { 1 } else { 0 });
    Ok(())
}

/// A RAM-backed 2 MiB frame's address and rights.
fn large_ram_frame(c: Cap) -> Option<(u64, u64)> {
    match c {
        Cap::Frame { ptr, size: FrameSize::Large, rights, is_device: false, .. } => Some((ptr, rights)),
        _ => None,
    }
}

/// A CNode cap's object and radix.
fn cnode_of(c: Cap) -> Option<(u64, u64)> {
    match c {
        Cap::CNode { ptr, radix, .. } => Some((ptr, radix)),
        _ => None,
    }
}

fn failed_lookup<T>(lf: LookupFault) -> KResult<T> {
    Err(Exc::Sys(SysError::FailedLookup { source: false, lf }))
}

/// l4h 0029: 4 KiB aliases of a RAM-backed 2 MiB frame.
fn derive_subframe<S: Store>(s: &mut S, length: u64, src: Slot, cap: Cap, buf: u64, ex: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let node_slot = match extra(ex, 0) {
        Some(x) if length >= 6 => x,
        _ => return truncated(),
    };
    let (ptr, rights) = match large_ram_frame(cap) {
        Some(x) => x,
        None => return illegal(),
    };
    let node_index = msg::syscall_arg(s, ct, buf, 0);
    let node_depth = msg::syscall_arg(s, ct, buf, 1);
    let node_offset = msg::syscall_arg(s, ct, buf, 2);
    let offset = msg::syscall_arg(s, ct, buf, 3);
    let count = msg::syscall_arg(s, ct, buf, 4);
    if offset >= (1 << 21) || offset & 0xfff != 0 {
        return invalid_arg(3);
    }
    let max = ((1u64 << 21) - offset) >> 12;
    if count < 1 || count > max {
        return range(1, max);
    }
    let dest = subframe_dest(s, node_slot, node_index, node_depth, node_offset, count)?;
    ensure_empty_run(s, dest, node_offset, count)?;
    let mask = msg::syscall_arg(s, ct, buf, 5);
    let vm = mask_vm_rights(rights, Rights::from_word(mask));
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    insert_subframes(s, src, dest, node_offset, ptr.wrapping_add(offset), count, vm);
    Ok(())
}

fn subframe_dest<S: Store>(s: &S, node_slot: Slot, node_index: u64, node_depth: u64, node_offset: u64, count: u64) -> KResult<u64> {
    let mut node_cap = node_slot.cap(s);
    if node_depth != 0 {
        node_cap = cspace::lookup_target_slot(s, node_cap, node_index, node_depth)?.cap(s);
    }
    let (dest, radix) = match cnode_of(node_cap) {
        Some(x) => x,
        None => return failed_lookup(LookupFault::MissingCapability { bits_left: node_depth }),
    };
    let node_size = 1u64 << (radix & 63);
    if node_offset > node_size.wrapping_sub(1) {
        return range(0, node_size.wrapping_sub(1));
    }
    if count > node_size.wrapping_sub(node_offset) {
        return range(1, node_size.wrapping_sub(node_offset));
    }
    Ok(dest)
}

fn ensure_empty_run<S: Store>(s: &S, dest: u64, first: u64, count: u64) -> KResult<()> {
    let mut i = 0;
    while i < count {
        cdt::ensure_empty_slot(s, Slot::index(dest, first.wrapping_add(i)))?;
        i += 1;
    }
    Ok(())
}

fn insert_subframes<S: Store>(s: &mut S, src: Slot, dest: u64, first: u64, base: u64, count: u64, vm: u64) {
    let mut i = 0;
    while i < count {
        let c = Cap::Frame {
            ptr: base.wrapping_add(i << 12),
            size: FrameSize::Small,
            rights: vm,
            is_device: false,
            mapped: false,
            is_ept: false,
            asid: 0,
            vaddr: 0,
        };
        cdt::insert(s, c, src, Slot::index(dest, first.wrapping_add(i)));
        i += 1;
    }
}

/// seL4 `decodeARMPageTableInvocation`.
#[allow(clippy::too_many_arguments)]
fn decode_page_table<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, slot: Slot, cap: Cap, buf: u64, ex: &[Slot; 3]) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let (ptr, mapped, masid, mvaddr) = match cap {
        Cap::PageTable { ptr, mapped, asid, vaddr } => (ptr, mapped, asid, vaddr),
        _ => return illegal(),
    };
    if lbl == label::ARMPageTableUnmap {
        if !cdt::is_final_capability(s, slot) {
            return Err(Exc::Sys(SysError::RevokeFirst));
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        if mapped {
            unmap_page_table(s, a, masid, mvaddr, ptr);
            s.zero(ptr, 4096);
        }
        slot.set_cap(s, Cap::PageTable { ptr, mapped: false, asid: 0, vaddr: 0 });
        return Ok(());
    }
    if lbl != label::ARMPageTableMap {
        return illegal();
    }
    let vslot = match extra(ex, 0) {
        Some(x) if length >= 2 => x,
        _ => return truncated(),
    };
    if mapped {
        return invalid_cap(0);
    }
    let vaddr = msg::syscall_arg(s, ct, buf, 0);
    let vcap = vslot.cap(s);
    if !is_valid_vtable_root(vcap) {
        return invalid_cap(1);
    }
    if vaddr > USER_TOP {
        return invalid_arg(0);
    }
    let (root, asid) = check_vspace(s, vcap, 1)?;
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift == PAGE_BITS || s.read(lu.slot) & D_VALID != 0 {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    let base = vaddr & !((1u64 << (lu.shift & 63)).wrapping_sub(1));
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, Cap::PageTable { ptr, mapped: true, asid, vaddr: base });
    s.write(lu.slot, make_user_table(layout::paddr(ptr)));
    Ok(())
}

/// seL4 `decodeARMMMUInvocation`.
#[allow(clippy::too_many_arguments)]
pub fn decode<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    call: bool,
    buf: u64,
    ex: &[Slot; 3],
) -> KResult<()> {
    let ct = sched::cur_thread(s);
    match cap {
        Cap::Frame { .. } => decode_frame(s, a, lbl, length, slot, cap, call, buf, ex),
        Cap::PageTable { .. } => decode_page_table(s, a, lbl, length, slot, cap, buf, ex),
        Cap::Pml4 { .. } => {
            if lbl == label::ARMVSpaceClean_Data
                || lbl == label::ARMVSpaceInvalidate_Data
                || lbl == label::ARMVSpaceCleanInvalidate_Data
                || lbl == label::ARMVSpaceUnify_Instruction
            {
                decode_vspace_flush(s, a, lbl, length, cap, buf)
            } else {
                illegal()
            }
        }
        Cap::AsidControl => {
            if lbl != label::ARMASIDControlMakePool {
                return illegal();
            }
            let (parent, root_slot) = match (extra(ex, 0), extra(ex, 1)) {
                (Some(x), Some(y)) if length >= 2 => (x, y),
                _ => return truncated(),
            };
            let index = msg::syscall_arg(s, ct, buf, 0);
            let depth = msg::syscall_arg(s, ct, buf, 1);
            let untyped = parent.cap(s);
            let root = root_slot.cap(s);
            let mut i = 0;
            while i < N_ASID_POOLS && asid_table(s, i) != 0 {
                i += 1;
            }
            if i == N_ASID_POOLS {
                return Err(Exc::Sys(SysError::DeleteFirst));
            }
            let base = i << ASID_LOW_BITS;
            let frame = match untyped {
                Cap::Untyped { ptr, size_bits, is_device: false, .. } if size_bits == bits::ASID_POOL => ptr,
                _ => return invalid_cap(1),
            };
            cdt::ensure_no_children(s, parent)?;
            let dest = cspace::lookup_target_slot(s, root, index, depth)?;
            cdt::ensure_empty_slot(s, dest)?;
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            if let Cap::Untyped { ptr, size_bits, is_device, .. } = untyped {
                parent.set_cap(s, Cap::Untyped { ptr, size_bits, free_index: 1u64 << (size_bits & 63), is_device });
            }
            s.clear_free(frame, 4096);
            cdt::insert(s, Cap::AsidPool { ptr: frame, asid_base: base }, parent, dest);
            set_asid_table(s, i, frame);
            Ok(())
        }
        Cap::AsidPool { ptr, asid_base } => {
            if lbl != label::ARMASIDPoolAssign {
                return illegal();
            }
            let vslot = match extra(ex, 0) {
                Some(x) => x,
                None => return truncated(),
            };
            let vroot = match vslot.cap(s) {
                Cap::Pml4 { ptr, mapped: false, .. } => ptr,
                _ => return invalid_cap(1),
            };
            let pool = asid_table(s, asid_base >> ASID_LOW_BITS);
            if pool == 0 {
                return Err(Exc::Sys(SysError::FailedLookup { source: false, lf: LookupFault::InvalidRoot }));
            }
            if pool != ptr {
                return invalid_cap(0);
            }
            let mut i = 0;
            while i < 512 && (asid_base.wrapping_add(i) == 0 || s.read(pool.wrapping_add(i * 8)) != 0) {
                i += 1;
            }
            if i == 512 {
                return Err(Exc::Sys(SysError::DeleteFirst));
            }
            let asid = asid_base.wrapping_add(i);
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            vslot.set_cap(s, Cap::Pml4 { ptr: vroot, mapped: true, asid });
            s.write(pool.wrapping_add((asid & 511) * 8), vroot);
            Ok(())
        }
        _ => invalid_cap(0),
    }
}

#[cfg(test)]
mod tests {
    //! Audit F1/F2 (TCB audit round 3): ARMPageMap's descriptor update
    //! order (break-before-make) and the cache maintenance of RAM frames
    //! mapped non-cacheable, through `decode_page_map` itself.
    extern crate std;
    use super::*;
    use crate::capability::FrameSize;
    use crate::obj::Tcb;
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::rc::Rc;
    use std::vec;
    use std::vec::Vec;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Ev {
        Write(u64, u64),
        InvalidatePage(u64, u64),
        CacheOp { op: u64, asid: u64, vaddr: u64, len: u64, paddr: u64 },
    }

    type Log = Rc<RefCell<Vec<Ev>>>;

    /// Kernel memory; writes to the watched descriptor are logged.
    struct Mem {
        words: BTreeMap<u64, u64>,
        watch: u64,
        log: Log,
    }
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 {
            *self.words.get(&a).unwrap_or(&0)
        }
        fn write(&mut self, a: u64, v: u64) {
            if a == self.watch {
                self.log.borrow_mut().push(Ev::Write(a, v));
            }
            self.words.insert(a, v);
        }
        fn zero(&mut self, a: u64, len: u64) {
            for i in (0..len).step_by(8) {
                self.write(a + i, 0);
            }
        }
        fn clear_free(&mut self, a: u64, len: u64) {
            self.zero(a, len)
        }
        fn ks_base(&self) -> u64 {
            0x10_0000
        }
        fn cur_cpu(&self) -> u64 {
            0
        }
    }

    struct Mach {
        log: Log,
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
        fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
            self.log.borrow_mut().push(Ev::InvalidatePage(asid, vaddr));
        }
        fn invalidate_asid(&mut self, _: u64) { panic!("unexpected invalidate_asid") }
        fn invalidate_page_structures(&mut self, _: u64) { panic!("unexpected invalidate_page_structures") }
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
        fn cache_op(&mut self, op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
            assert_eq!(root, layout::pptr(ROOT));
            self.log.borrow_mut().push(Ev::CacheOp { op, asid, vaddr, len, paddr });
        }
        fn hw_access_flag(&self) -> bool { true }
        fn max_spi(&self) -> u64 { 0 }
        fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
    }

    const ASID: u64 = 0x201;
    const VADDR: u64 = 0x4000_0000;
    // Physical addresses of the tables, the frame and the other frame an
    // earlier mapping used.
    const ROOT: u64 = 0x10_0000;
    const L1: u64 = 0x10_1000;
    const L2: u64 = 0x10_2000;
    const L3: u64 = 0x10_3000;
    const FRAME: u64 = 0x80_0000;
    const OTHER: u64 = 0xa0_0000;

    struct World {
        s: Mem,
        a: Mach,
        log: Log,
        fslot: Slot,
        ex: [Slot; 3],
        /// The descriptor `decode_page_map` writes.
        pte: u64,
        shift: u64,
    }

    /// A VSpace with ASID `ASID` whose tables reach the level that maps
    /// `size` at `VADDR`, and the current thread's arguments for
    /// ARMPageMap(VADDR, all rights, attr).
    fn world(size: FrameSize, attr: u64) -> World {
        let log: Log = Rc::new(RefCell::new(Vec::new()));
        let mut s = Mem { words: BTreeMap::new(), watch: 0, log: log.clone() };
        let root = layout::pptr(ROOT);
        let shift = size.bits();
        // Table descriptors down to the level that maps `shift`.
        let tables = [(ROOT, L1, TOP_LEVEL_SHIFT), (L1, L2, 30), (L2, L3, 21)];
        let mut leaf_table = ROOT;
        for &(t, next, sh) in &tables {
            if sh == shift {
                break;
            }
            s.write(entry_addr(layout::pptr(t), VADDR, sh), make_user_table(next));
            leaf_table = next;
        }
        let pte = entry_addr(layout::pptr(leaf_table), VADDR, shift);
        // The ASID pool and its entry for the VSpace.
        let pool = layout::pptr(0x50_0000);
        set_asid_table(&mut s, ASID >> ASID_LOW_BITS, pool);
        s.write(pool + (ASID & 511) * 8, root);
        // The current thread and its message registers.
        let t = Tcb(layout::pptr(0x60_0000));
        sched::set_cur_thread(&mut s, t);
        t.set_reg(&mut s, msg::msg_register(0), VADDR);
        t.set_reg(&mut s, msg::msg_register(1), u64::MAX);
        t.set_reg(&mut s, msg::msg_register(2), attr);
        let vslot = Slot(layout::pptr(0x70_0000));
        vslot.set_cap(&mut s, Cap::Pml4 { ptr: root, mapped: true, asid: ASID });
        let fslot = Slot(layout::pptr(0x70_0040));
        s.watch = pte;
        World { s, a: Mach { log: log.clone() }, log, fslot, ex: [vslot, Slot(0), Slot(0)], pte, shift }
    }

    fn frame(size: FrameSize, is_device: bool, mapped: bool) -> FrameCap {
        FrameCap {
            ptr: layout::pptr(FRAME),
            size,
            rights: VM_READ_WRITE,
            is_device,
            mapped,
            asid: if mapped { ASID } else { 0 },
            vaddr: if mapped { VADDR } else { 0 },
        }
    }

    fn map(w: &mut World, f: FrameCap) -> Vec<Ev> {
        w.fslot.set_cap(&mut w.s, Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: f.mapped, is_ept: false, asid: f.asid, vaddr: f.vaddr });
        w.log.borrow_mut().clear();
        assert!(decode_page_map(&mut w.s, &mut w.a, 3, w.fslot, f, 0, &w.ex).is_ok());
        let ev = w.log.borrow().clone();
        ev
    }

    fn entry(attr: u64, shift: u64) -> u64 {
        make_user_page(FRAME, VM_READ_WRITE, true, attr, shift)
    }

    fn clean(len: u64) -> Ev {
        Ev::CacheOp { op: CACHE_CLEAN_INVALIDATE, asid: ASID, vaddr: VADDR, len, paddr: FRAME }
    }

    #[test]
    fn ram_mapped_uncached_is_cleaned_to_poc_before_its_descriptor() {
        for size in [FrameSize::Small, FrameSize::Large] {
            let mut w = world(size, 0);
            let f = frame(size, false, false);
            let ev = map(&mut w, f);
            let e = entry(0, w.shift);
            assert_eq!(ev, vec![clean(1 << w.shift), Ev::Write(w.pte, e)], "size {}", size.bits());
            assert_eq!(w.s.read(w.pte), e);
            assert_eq!((e >> D_ATTR_SHIFT) & 7, ATTR_DEVICE_NGNRNE);
        }
    }

    #[test]
    fn device_frames_are_never_cache_maintained() {
        let mut w = world(FrameSize::Small, 0);
        let f = frame(FrameSize::Small, true, false);
        let ev = map(&mut w, f);
        assert_eq!(ev, vec![Ev::Write(w.pte, entry(0, 12))]);
        // Nor when one replaces a live descriptor.
        w.s.write(w.pte, make_user_page(OTHER, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 12));
        let ev = map(&mut w, f);
        assert_eq!(ev, vec![Ev::Write(w.pte, 0), Ev::InvalidatePage(ASID, VADDR), Ev::Write(w.pte, entry(0, 12))]);
    }

    /// Overmapping another frame mapped with the same attributes is a new
    /// output address: break-before-make too.
    #[test]
    fn overmapping_with_the_same_attributes_still_breaks() {
        for attr in [0, arm_vm_attr::PAGE_CACHEABLE] {
            let mut w = world(FrameSize::Small, attr);
            w.s.write(w.pte, make_user_page(OTHER, VM_READ_WRITE, true, attr, 12));
            let ev = map(&mut w, frame(FrameSize::Small, false, false));
            let mut want = vec![Ev::Write(w.pte, 0), Ev::InvalidatePage(ASID, VADDR)];
            if attr == 0 {
                want.push(clean(0x1000));
            }
            want.push(Ev::Write(w.pte, entry(attr, 12)));
            assert_eq!(ev, want, "attr {attr}");
        }
    }

    #[test]
    fn cacheable_ram_mappings_need_no_cache_maintenance() {
        let mut w = world(FrameSize::Small, arm_vm_attr::PAGE_CACHEABLE);
        let f = frame(FrameSize::Small, false, false);
        let ev = map(&mut w, f);
        assert_eq!(ev, vec![Ev::Write(w.pte, entry(arm_vm_attr::PAGE_CACHEABLE, 12))]);
    }

    /// Overmapping a live descriptor (another frame's, cacheable) breaks
    /// it before the new one is made: cleared, flushed on every core,
    /// cleaned for an uncached RAM mapping, and only then written.
    #[test]
    fn overmapping_a_live_descriptor_breaks_before_make() {
        for size in [FrameSize::Small, FrameSize::Large] {
            for attr in [0, arm_vm_attr::PAGE_CACHEABLE] {
                let mut w = world(size, attr);
                let old = make_user_page(OTHER, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, w.shift);
                w.s.write(w.pte, old);
                let f = frame(size, false, false);
                let ev = map(&mut w, f);
                let e = entry(attr, w.shift);
                let mut want = vec![Ev::Write(w.pte, 0), Ev::InvalidatePage(ASID, VADDR)];
                if attr == 0 {
                    want.push(clean(1 << w.shift));
                }
                want.push(Ev::Write(w.pte, e));
                assert_eq!(ev, want, "size {} attr {attr}", size.bits());
                // No non-zero descriptor reaches the slot before the flush.
                let flush = ev.iter().position(|x| matches!(x, Ev::InvalidatePage(..))).unwrap();
                assert!(ev[..flush].iter().all(|x| !matches!(x, Ev::Write(_, v) if *v != 0)));
            }
        }
    }

    /// A remap of the frame's own mapping that changes its cacheability
    /// (memory type and shareability) breaks before make.
    #[test]
    fn remapping_with_another_memory_type_breaks_and_flushes() {
        for (before, after) in [(arm_vm_attr::PAGE_CACHEABLE, 0), (0, arm_vm_attr::PAGE_CACHEABLE)] {
            let mut w = world(FrameSize::Small, after);
            let f = frame(FrameSize::Small, false, true);
            w.s.write(w.pte, entry(before, 12));
            let ev = map(&mut w, f);
            let mut want = vec![Ev::Write(w.pte, 0), Ev::InvalidatePage(ASID, VADDR)];
            if after == 0 {
                want.push(clean(0x1000));
            }
            want.push(Ev::Write(w.pte, entry(after, 12)));
            assert_eq!(ev, want, "{before} -> {after}");
        }
    }

    /// A remap that keeps the frame and its memory type, changing only
    /// permissions, execute-never or the access flag (or nothing), is
    /// rewritten in place and then flushed: never cleared, so another core
    /// cannot fault on it, and the flush that TestAndClearAccessed (l4h
    /// 0023, FL4VM0002) relies on still happens.
    #[test]
    fn remapping_only_permissions_rewrites_in_place_and_flushes() {
        for attr in [0, arm_vm_attr::PAGE_CACHEABLE] {
            let f = frame(FrameSize::Small, false, true);
            let e = entry(attr, 12);
            let olds = [
                e,
                e & !D_AF,
                make_user_page(FRAME, VM_READ_ONLY, true, attr, 12),
                make_user_page(FRAME, VM_READ_WRITE, true, attr | arm_vm_attr::EXECUTE_NEVER, 12),
            ];
            for old in olds {
                let mut w = world(FrameSize::Small, attr);
                w.s.write(w.pte, old);
                let ev = map(&mut w, f);
                assert_eq!(ev, vec![Ev::Write(w.pte, e), Ev::InvalidatePage(ASID, VADDR)], "attr {attr} old {old:#x}");
            }
        }
    }
}
