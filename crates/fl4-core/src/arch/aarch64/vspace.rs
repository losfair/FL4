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
use fl4_abi::consts::{arm_vm_attr, bits, HIGH_VSPACE_BASE, HIGH_VSPACE_TOP, USER_TOP};
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

/// What an ASID pool entry names, in the low bits of its (4 KiB-aligned)
/// root: a VSpace (`Cap::Pml4`), a Stage-2 VSpace (`Cap::Ept`) or an
/// `ArmHighVSpace` (`Cap::HighVSpace`).
pub const ROOT_S1: u64 = 0;
pub const ROOT_S2: u64 = 1;
pub const ROOT_HIGH: u64 = 2;
pub const ROOT_TAG: u64 = 3;

/// The level-0 entry of the TTBR1 half that the high window lies in, and
/// its level-1 entries the window covers (`HIGH_VSPACE_BASE` to
/// `HIGH_VSPACE_TOP`).
const HIGH_L0_INDEX: u64 = 511;
const HIGH_L1_FIRST: u64 = (HIGH_VSPACE_BASE >> 30) & 511;
const HIGH_L1_END: u64 = HIGH_L1_FIRST + ((HIGH_VSPACE_TOP - HIGH_VSPACE_BASE) >> 30);
const _: () = assert!(HIGH_L1_FIRST == 384 && HIGH_L1_END == 496);
const _: () = assert!((HIGH_VSPACE_BASE >> TOP_LEVEL_SHIFT) & 511 == HIGH_L0_INDEX);
const _: () = assert!(HIGH_VSPACE_BASE >= layout::PPTR_TOP);

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

/// Whether a mapping with attributes `attr` from a frame cap with read
/// right `cap_read` is execute-never. (Written as `if`s: a stored `||`,
/// `!` or `==` becomes a Lean `Prop` in the Aeneas output, not a `Bool`.)
#[allow(clippy::needless_bool)]
pub(crate) fn exec_never(attr: u64, cap_read: bool) -> bool {
    if attr & arm_vm_attr::EXECUTE_NEVER != 0 {
        true
    } else if cap_read {
        false
    } else {
        true
    }
}

/// Whether frame-cap rights `rights` include read (seL4 `CapRights` read).
#[allow(clippy::needless_bool, clippy::if_same_then_else)]
pub(crate) fn rights_readable(rights: u64) -> bool {
    if rights == VM_READ_ONLY {
        true
    } else if rights == VM_READ_WRITE {
        true
    } else {
        false
    }
}

/// seL4 `makeUserPagePTE`. The kernel never executes user pages (PXN).
fn make_user_page(paddr: u64, rights: u64, cap_read: bool, attr: u64, shift: u64) -> u64 {
    let xn = exec_never(attr, cap_read);
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

/// Raw ASID pool entry: the root with its `ROOT_*` tag.
pub fn find_asid_raw<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
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

/// seL4 `findVSpaceForASID` (Stage-1 VSpaces only).
pub fn find_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    let root = find_asid_raw(s, asid)?;
    if root & ROOT_TAG != ROOT_S1 {
        return Err(LookupFault::InvalidRoot);
    }
    Ok(root)
}

/// The `ArmHighVSpace` ASID `asid` names.
pub fn find_high_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    let root = find_asid_raw(s, asid)?;
    if root & ROOT_TAG != ROOT_HIGH {
        return Err(LookupFault::InvalidRoot);
    }
    Ok(root & !ROOT_TAG)
}

/// The tables a frame mapped with ASID `asid` is reached through, and the
/// root `Arch::cache_op` may switch to (0 for the high window, which only
/// RAM frames reach through the kernel window).
fn frame_root<S: Store>(s: &S, asid: u64) -> Result<(u64, u64), LookupFault> {
    let raw = find_asid_raw(s, asid)?;
    let tag = raw & ROOT_TAG;
    if tag == ROOT_S1 {
        Ok((raw, raw))
    } else if tag == ROOT_HIGH {
        Ok((raw & !ROOT_TAG, 0))
    } else {
        Err(LookupFault::InvalidRoot)
    }
}

/// A new `ArmHighVSpace` at `base` (8 KiB, zeroed): its level-0 table copies
/// the kernel's TTBR1 level-0 entries `0..511` (RAM window, devices, and the
/// kernel image in `L0[510]`), while entry 511 points to its own empty
/// level-1 table (at `base + 4096`) with `PXNTable` set so the kernel never
/// executes high-window pages. Because `KERNEL_TTBR1.L0[511]` stays invalid,
/// `switch_high` never needs to flush global walk caches on TTBR1 changes.
pub fn init_high_vspace<S: Store, A: Arch>(s: &mut S, a: &mut A, base: u64) {
    let l1 = base.wrapping_add(4096);
    let mut i = 0;
    while i < HIGH_L0_INDEX {
        let e = a.kernel_ttbr1_entry(0, i);
        if e != 0 {
            s.write(base.wrapping_add(i * 8), e);
        }
        i += 1;
    }
    s.write(
        base.wrapping_add(HIGH_L0_INDEX * 8),
        (layout::paddr(l1) & ADDR_MASK) | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE,
    );
}

/// The `ArmHighVSpace` bound to `t` (`TCBSetHighVSpace`), if its ASID
/// still names it; 0 otherwise.
fn high_root_of<S: Store>(s: &S, t: Tcb) -> u64 {
    match t.slot(tl::SLOT_HIGH_VSPACE).cap(s) {
        Cap::HighVSpace { ptr, mapped: true, asid } => match find_high_asid(s, asid) {
            Ok(r) if r == ptr => ptr,
            _ => 0,
        },
        _ => 0,
    }
}

pub fn find_vspace_for_asid<S: Store>(s: &S, asid: u64) -> Result<u64, LookupFault> {
    find_asid(s, asid)
}

pub fn is_valid_vtable_root(c: Cap) -> bool {
    matches!(c, Cap::Pml4 { mapped: true, .. } | Cap::Ept { level: 0, mapped: true, .. })
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

/// Install `t`'s Stage-2 VSpace root (`Cap::Ept`) into `VTTBR_EL2` (or the
/// empty Stage-2 root if `t` has no valid mapped Stage-2 root).
pub fn set_stage2_root<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    match t.slot(tl::SLOT_VTABLE).cap(s) {
        Cap::Ept { ptr, level: 0, mapped: true, asid, .. } => match crate::ept::find(s, asid) {
            Ok(r) if r == ptr => a.set_stage2_vspace(ptr, asid),
            _ => a.set_stage2_vspace(0, 0),
        },
        _ => a.set_stage2_vspace(0, 0),
    }
}

/// seL4 `setVMRoot`: VCPU threads install Stage-2 (`Cap::Ept`) in VTTBR_EL2
/// while keeping TTBR0_EL2 on the empty kernel root; native threads install
/// Stage-1 (`Cap::Pml4`) in TTBR0_EL2, plus the guest's Stage-2 root while
/// running a VCPU via `ARMVCPURun`.
///
/// A native thread on a VSpace also gets its `ArmHighVSpace` as TTBR1, if
/// it has one; a thread with no VSpace (ASID 0, shared by all of them) or
/// running a VCPU never does: the high window's translations are tagged
/// with the TTBR0 ASID, which the backend tracks (`Arch::set_high_vspace`).
#[inline(always)]
pub fn set_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    if crate::vcpu::bound(s, t) != 0 {
        set_kernel_vm_root(s, a);
        set_stage2_root(s, a, t);
        return;
    }
    match t.slot(tl::SLOT_VTABLE).cap(s) {
        Cap::Pml4 { ptr, mapped: true, asid } => match find_vspace_for_asid(s, asid) {
            Ok(r) if r == ptr => {
                let high = if t.state(s) == sched::TS_RUNNING_VM { 0 } else { high_root_of(s, t) };
                if high == 0 {
                    // Leaving a high window: TTBR1 back on the kernel's
                    // tables (L0[511] invalid) before the incoming TTBR0, so
                    // the incoming ASID never runs beside an ArmHighVSpace.
                    a.set_high_vspace(0, asid);
                    a.set_vspace(ptr, asid);
                } else {
                    // Entering a high window: the owner's TTBR0 first (a new
                    // TTBR0 takes TTBR1 back to the kernel's tables on the
                    // way, also from another window), then the window, so
                    // no other ASID runs beside it.
                    a.set_vspace(ptr, asid);
                    a.set_high_vspace(high, asid);
                }
            }
            _ => set_kernel_vm_root(s, a),
        },
        _ => set_kernel_vm_root(s, a),
    }
    if t.state(s) == sched::TS_RUNNING_VM {
        let run_v = s.read(t.0.wrapping_add(tl::RUN_VCPU));
        if run_v != 0 {
            let guest_tcb = s.read(run_v.wrapping_add(crate::vcpu::TCB));
            if guest_tcb != 0 {
                set_stage2_root(s, a, Tcb(guest_tcb));
            }
        }
    }
}

pub fn set_kernel_vm_root<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let k = kernel_root(s);
    a.set_high_vspace(0, 0);
    a.set_vspace(k, 0);
}

/// The kernel is in the TTBR1 half: a VSpace holds no kernel mappings.
pub fn copy_global_mappings<S: Store>(s: &mut S, new_root: u64) {
    let _ = (s, new_root);
}

// ---- unmapping -----------------------------------------------------------------

/// The tables `unmap_page` walks for a frame mapped with ASID `asid`, and
/// whether they are an `ArmHighVSpace`'s; None if it unmaps nothing.
pub fn unmap_root<S: Store>(s: &S, asid: u64) -> Option<(u64, bool)> {
    match find_asid_raw(s, asid) {
        Ok(r) => {
            if r & ROOT_TAG == ROOT_S1 {
                Some((r, false))
            } else if r & ROOT_TAG == ROOT_HIGH {
                Some((r & !ROOT_TAG, true))
            } else {
                None
            }
        }
        Err(_) => None,
    }
}

/// The level-3 entry a small page at `vaddr` in the tables at `root` uses,
/// if they reach level 3 (`localinv`, which locks it): the one entry
/// `unmap_page` may clear and `decode_page_map` may write for a small
/// frame, which otherwise write none.
pub fn small_page_entry<S: Store>(s: &S, root: u64, vaddr: u64) -> Option<u64> {
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift == PAGE_BITS {
        Some(lu.slot)
    } else {
        None
    }
}

/// seL4 `unmapPage`, in a VSpace or an `ArmHighVSpace`.
pub fn unmap_page<S: Store, A: Arch>(s: &mut S, a: &mut A, size: FrameSize, asid: u64, vaddr: u64, pptr: u64) {
    let (root, high) = match unmap_root(s, asid) {
        Some(x) => x,
        None => return,
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
    if high {
        a.invalidate_high_page(vaddr);
    } else {
        a.invalidate_page(asid, vaddr);
    }
}

/// seL4 `unmapPageTable`: find the slot that points to `pt` on the walk to
/// `vaddr` (dispatches to Stage-2 for a Stage-2 VSpace's ASID). In an
/// `ArmHighVSpace` the walk starts at its own level-1 table: level-0 entry
/// 511 is never a page table's to take.
pub fn unmap_page_table<S: Store, A: Arch>(s: &mut S, a: &mut A, asid: u64, vaddr: u64, pt: u64) {
    let raw = match find_asid_raw(s, asid) {
        Ok(r) => r,
        Err(_) => return,
    };
    let tag = raw & ROOT_TAG;
    if tag == ROOT_S2 {
        crate::ept::unmap_table(s, a, asid, vaddr, pt);
        return;
    }
    let high = tag == ROOT_HIGH;
    let root = raw & !ROOT_TAG;
    let (mut table, mut shift, mut level) = if high {
        (table_of(s.read(root.wrapping_add(HIGH_L0_INDEX * 8))), 30u64, 1u64)
    } else {
        (root, TOP_LEVEL_SHIFT, 0u64)
    };
    // The slot that points to `pt`, if the walk reaches it before an entry
    // that is not a table descriptor. (The loop ends with `break` rather
    // than `return`: Aeneas cannot extract an early return from a loop.)
    let mut found = None;
    while level < 3 {
        let slot = entry_addr(table, vaddr, shift);
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
        level += 1;
    }
    if let Some(slot) = found {
        s.write(slot, 0);
        if high {
            a.invalidate_high_vspace(root);
        } else {
            a.invalidate_asid(asid);
        }
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
        let tag = root & ROOT_TAG;
        if tag == ROOT_S2 {
            a.invalidate_stage2_vmid(asid);
        } else if tag == ROOT_HIGH {
            a.invalidate_high_vspace(root & !ROOT_TAG);
        } else {
            a.invalidate_asid(asid);
        }
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
        let r = s.read(pool.wrapping_add(i * 8));
        if r & ROOT_TAG == ROOT_S2 {
            a.invalidate_stage2_vmid(base.wrapping_add(i));
        } else if r & ROOT_TAG == ROOT_HIGH {
            a.invalidate_high_vspace(r & !ROOT_TAG);
        } else if r != 0 {
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

/// The level-0 table and ASID of a mapped `ArmHighVSpace` cap that its
/// ASID still names.
fn check_high_vspace<S: Store>(s: &S, vcap: Cap, cap_arg: u64) -> KResult<(u64, u64)> {
    let (root, asid) = match vcap {
        Cap::HighVSpace { ptr, mapped: true, asid } => (ptr, asid),
        _ => return invalid_cap(cap_arg),
    };
    match find_high_asid(s, asid) {
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
    is_ept: bool,
    asid: u64,
    vaddr: u64,
}

fn as_frame(c: Cap) -> Option<FrameCap> {
    match c {
        Cap::Frame { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr } => {
            Some(FrameCap { ptr, size, rights, is_device, mapped, is_ept, asid, vaddr })
        }
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
            if f.is_ept {
                crate::ept::unmap(s, a, f.asid, f.vaddr, f.ptr, f.size.bits(), false);
            } else {
                unmap_page(s, a, f.size, f.asid, f.vaddr, f.ptr);
            }
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
    let vcap = vslot.cap(s);
    if matches!(vcap, Cap::Ept { .. }) {
        let (root, asid) = crate::ept::root(s, vcap, 1)?;
        if f.asid != 0 && !f.is_ept {
            return invalid_cap(1);
        }
        return crate::ept::map_frame(
            s, a, root, asid, vaddr, vm, attr, f.ptr, f.size, f.rights, f.is_device, f.asid, f.vaddr, slot,
        );
    }
    if f.asid != 0 && f.is_ept {
        return invalid_cap(1);
    }
    if matches!(vcap, Cap::HighVSpace { .. }) {
        return decode_high_page_map(s, a, slot, f, vcap, vaddr, vm, attr);
    }
    let (root, asid) = check_vspace(s, vcap, 1)?;
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
    let cap_read = rights_readable(f.rights);
    let e = make_user_page(layout::paddr(f.ptr), vm, cap_read, attr, shift);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: true, is_ept: false, asid, vaddr });
    install_page(s, a, lu, e, root, asid, vaddr, f, attr, false);
    Ok(())
}

/// ARMPageMap into an `ArmHighVSpace`: 4 KiB pages, 2 MiB and 1 GiB blocks
/// within the high window, made as in a VSpace (EL0 rights, nG, PXN).
#[allow(clippy::too_many_arguments)]
fn decode_high_page_map<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot, f: FrameCap, vcap: Cap, vaddr: u64, vm: u64, attr: u64) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let (root, asid) = check_high_vspace(s, vcap, 1)?;
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
    }
    let last = vaddr.wrapping_add((1u64 << (shift & 63)).wrapping_sub(1));
    if vaddr < HIGH_VSPACE_BASE || last >= HIGH_VSPACE_TOP || last < vaddr {
        return invalid_arg(0);
    }
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift != shift {
        return Err(Exc::Sys(SysError::FailedLookup { source: false, lf: LookupFault::MissingCapability { bits_left: lu.shift } }));
    }
    let cap_read = rights_readable(f.rights);
    let e = make_user_page(layout::paddr(f.ptr), vm, cap_read, attr, shift);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    slot.set_cap(s, Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: true, is_ept: false, asid, vaddr });
    install_page(s, a, lu, e, 0, asid, vaddr, f, attr, true);
    Ok(())
}

/// Drop the translations of one page: in a VSpace by its ASID, in the
/// high window for every ASID (`Arch::invalidate_high_page`).
fn invalidate_mapping<A: Arch>(a: &mut A, high: bool, asid: u64, vaddr: u64) {
    if high {
        a.invalidate_high_page(vaddr);
    } else {
        a.invalidate_page(asid, vaddr);
    }
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
///
/// In the high window (`high`) the invalidations are for every ASID and
/// `root` is 0: the cache maintenance never switches to a user mapping.
fn install_page<S: Store, A: Arch>(s: &mut S, a: &mut A, lu: PtSlot, e: u64, root: u64, asid: u64, vaddr: u64, f: FrameCap, attr: u64, high: bool) {
    let old = s.read(lu.slot);
    if is_page(old, lu.shift) {
        if (old ^ e) & BBM_MASK == 0 {
            s.write(lu.slot, e);
            invalidate_mapping(a, high, asid, vaddr);
            return;
        }
        s.write(lu.slot, 0);
        invalidate_mapping(a, high, asid, vaddr);
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
    let start = msg::syscall_arg(s, ct, buf, 0);
    let end = msg::syscall_arg(s, ct, buf, 1);
    if end <= start {
        return invalid_arg(1);
    }
    let size = 1u64 << (page_shift(f.size) & 63);
    if start >= size || end > size {
        return invalid_arg(0);
    }
    if f.is_ept {
        return crate::ept::flush_frame(s, a, page_cache_op(lbl), is_invalidate(lbl), f.asid, f.vaddr, f.ptr, f.size, f.is_device, start, end);
    }
    let (root, cache_root) = match frame_root(s, f.asid) {
        Ok(r) => r,
        Err(lf) => return Err(Exc::Sys(SysError::FailedLookup { source: false, lf })),
    };
    let lu = match mapped_entry(s, f, root) {
        Some(x) => x,
        None => return invalid_cap(0),
    };
    if is_invalidate(lbl) && rights_of(s.read(lu.slot)) != VM_READ_WRITE {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let pstart = layout::paddr(f.ptr).wrapping_add(start);
    a.cache_op(page_cache_op(lbl), cache_root, f.asid, f.vaddr.wrapping_add(start), end - start, pstart);
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
    if f.is_ept || matches!(f.size, FrameSize::Huge) || !f.mapped || f.asid == 0 || !a.hw_access_flag() {
        return illegal();
    }
    let root = match frame_root(s, f.asid) {
        Ok((r, _)) => r,
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
    if matches!(vcap, Cap::HighVSpace { .. }) {
        return map_high_page_table(s, slot, ptr, vcap, vaddr);
    }
    if !is_valid_vtable_root(vcap) {
        return invalid_cap(1);
    }
    if matches!(vcap, Cap::Ept { .. }) {
        let (root, asid) = crate::ept::root(s, vcap, 1)?;
        return crate::ept::map_table(s, a, root, asid, vaddr, ptr, slot);
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

/// ARMPageTableMap into an `ArmHighVSpace`: a level-2 or level-3 table
/// within the high window (level-0 entry 511 always holds its own level-1
/// table), never executable by the kernel (PXNTable).
fn map_high_page_table<S: Store>(s: &mut S, slot: Slot, ptr: u64, vcap: Cap, vaddr: u64) -> KResult<()> {
    let ct = sched::cur_thread(s);
    let (root, asid) = check_high_vspace(s, vcap, 1)?;
    if vaddr < HIGH_VSPACE_BASE || vaddr >= HIGH_VSPACE_TOP {
        return invalid_arg(0);
    }
    let lu = lookup_pt_slot(s, root, vaddr);
    if lu.shift == PAGE_BITS || lu.shift == TOP_LEVEL_SHIFT || s.read(lu.slot) & D_VALID != 0 {
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
            let (vroot, tag) = match vslot.cap(s) {
                Cap::Pml4 { ptr, mapped: false, .. } => (ptr, ROOT_S1),
                Cap::Ept { ptr, level: 0, mapped: false, .. } => (ptr, ROOT_S2),
                Cap::HighVSpace { ptr, mapped: false, .. } => (ptr, ROOT_HIGH),
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
            if tag == ROOT_S2 {
                vslot.set_cap(s, Cap::Ept { ptr: vroot, level: 0, mapped: true, asid, vaddr: 0 });
            } else if tag == ROOT_HIGH {
                vslot.set_cap(s, Cap::HighVSpace { ptr: vroot, mapped: true, asid });
            } else {
                vslot.set_cap(s, Cap::Pml4 { ptr: vroot, mapped: true, asid });
            }
            s.write(pool.wrapping_add((asid & 511) * 8), vroot | tag);
            Ok(())
        }
        Cap::HighVSpace { .. } => illegal(),
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
        InvalidateAsid(u64),
        InvalidateVmid(u64),
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
        fn invalidate_asid(&mut self, asid: u64) {
            self.log.borrow_mut().push(Ev::InvalidateAsid(asid));
        }
        fn invalidate_stage2_vmid(&mut self, asid: u64) {
            self.log.borrow_mut().push(Ev::InvalidateVmid(asid));
        }
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
        fn send_reschedule(&mut self, _: u128) {}
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
            is_ept: false,
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

    /// Run `unmap_page_table(asid, VADDR, pt)`: the words it changed
    /// (address, new value) and the machine events.
    fn unmap_pt(w: &mut World, asid: u64, pt: u64) -> (Vec<(u64, u64)>, Vec<Ev>) {
        let before = w.s.words.clone();
        w.log.borrow_mut().clear();
        unmap_page_table(&mut w.s, &mut w.a, asid, VADDR, pt);
        let changed = w.s.words.iter().filter(|&(k, v)| before.get(k).unwrap_or(&0) != v).map(|(&k, &v)| (k, v)).collect();
        let ev = w.log.borrow().clone();
        (changed, ev)
    }

    /// The slots on the walk to `VADDR` that hold ROOT -> L1 -> L2 -> L3.
    fn walk_slots() -> [u64; 3] {
        [
            entry_addr(layout::pptr(ROOT), VADDR, TOP_LEVEL_SHIFT),
            entry_addr(layout::pptr(L1), VADDR, 30),
            entry_addr(layout::pptr(L2), VADDR, 21),
        ]
    }

    /// The walk reaches the table at each level: that slot alone is
    /// cleared, then the ASID is flushed.
    #[test]
    fn unmap_page_table_clears_the_slot_pointing_to_the_table() {
        for (i, pt) in [L1, L2, L3].into_iter().enumerate() {
            let mut w = world(FrameSize::Small, 0);
            let (changed, ev) = unmap_pt(&mut w, ASID, layout::pptr(pt));
            assert_eq!(changed, vec![(walk_slots()[i], 0)], "level {i}");
            assert_eq!(ev, vec![Ev::InvalidateAsid(ASID)], "level {i}");
        }
    }

    /// Every other exit changes nothing and flushes nothing: an ASID with
    /// no VSpace, a walk that meets an entry that is not a table descriptor
    /// (invalid, or a block) before the table, and a walk that runs through
    /// all three table levels without meeting it.
    #[test]
    fn unmap_page_table_without_the_table_on_the_walk_changes_nothing() {
        let mut w = world(FrameSize::Small, 0);
        assert_eq!(unmap_pt(&mut w, ASID + 1, layout::pptr(L1)), (vec![], vec![]));
        let block = make_user_page(OTHER, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 30);
        for e in [0, block] {
            let mut w = world(FrameSize::Small, 0);
            w.s.write(walk_slots()[1], e);
            assert_eq!(unmap_pt(&mut w, ASID, layout::pptr(L3)), (vec![], vec![]), "entry {e:#x}");
        }
        let mut w = world(FrameSize::Small, 0);
        assert_eq!(unmap_pt(&mut w, ASID, layout::pptr(0x10_4000)), (vec![], vec![]));
    }

    /// `exec_never` and `rights_readable` agree with the expressions they
    /// replace (`attr & EXECUTE_NEVER != 0 || !cap_read`, `rights ==
    /// VM_READ_ONLY || rights == VM_READ_WRITE`).
    #[test]
    fn exec_never_and_rights_readable_match_the_boolean_expressions() {
        for attr in [0, arm_vm_attr::EXECUTE_NEVER, arm_vm_attr::PAGE_CACHEABLE, u64::MAX] {
            for cap_read in [false, true] {
                assert_eq!(exec_never(attr, cap_read), attr & arm_vm_attr::EXECUTE_NEVER != 0 || !cap_read, "{attr:#x} {cap_read}");
            }
        }
        for rights in 0..8 {
            assert_eq!(rights_readable(rights), rights == VM_READ_ONLY || rights == VM_READ_WRITE, "{rights}");
        }
        // And through the descriptors: no read right means execute-never.
        assert_ne!(make_user_page(FRAME, VM_READ_WRITE, false, arm_vm_attr::PAGE_CACHEABLE, 12) & D_UXN, 0);
        assert_eq!(make_user_page(FRAME, VM_READ_WRITE, true, arm_vm_attr::PAGE_CACHEABLE, 12) & D_UXN, 0);
    }

    fn set_frame(w: &mut World, f: FrameCap) {
        w.fslot.set_cap(&mut w.s, Cap::Frame { ptr: f.ptr, size: f.size, rights: f.rights, is_device: f.is_device, mapped: f.mapped, is_ept: false, asid: f.asid, vaddr: f.vaddr });
    }

    fn map_plan(w: &World) -> Option<crate::localinv::Plan> {
        let t = sched::cur_thread(&w.s);
        crate::localinv::plan_with(&w.s, t, label::ARMPageMap, w.fslot, w.ex)
    }

    /// `localinv`'s plan for an ARMPageMap beside the gate locks the
    /// frame's slot and the very descriptor `decode_page_map` then writes,
    /// for a new mapping and a remap; and its map writes no other
    /// descriptor and makes no Arch operation but the remap's TLBI.
    #[test]
    fn local_map_plan_locks_the_descriptor_the_map_writes() {
        let cacheable = arm_vm_attr::PAGE_CACHEABLE;
        for mapped in [false, true] {
            let mut w = world(FrameSize::Small, cacheable);
            let f = frame(FrameSize::Small, false, mapped);
            if mapped {
                w.s.write(w.pte, entry(0, 12));
            }
            set_frame(&mut w, f);
            let p = map_plan(&w).expect("a local plan");
            assert_eq!(&p.locks[..p.n], &[w.fslot.0, w.pte]);
            assert_eq!(p.pte, 1);
            assert!(p.still_holds(&w.s));
            let before = w.s.words.clone();
            let ev = map(&mut w, f);
            assert!(ev.iter().all(|x| matches!(x, Ev::Write(a, _) if *a == w.pte) || *x == Ev::InvalidatePage(ASID, VADDR)), "{ev:?}");
            assert_eq!(w.s.read(w.pte), entry(cacheable, 12));
            // Of all kernel words, only the locked ones, the caller's and
            // this core's node state changed.
            let t = sched::cur_thread(&w.s).0;
            let tcb = t..t + (1u64 << bits::TCB);
            let nb = crate::obj::node_base(&w.s, 0);
            let node = nb..nb + crate::layout::node::SIZE;
            for (&a, &v) in &w.s.words {
                if before.get(&a) != Some(&v) {
                    assert!(a == w.pte || a == w.fslot.0 + crate::layout::cte::CAP0 || a == w.fslot.0 + crate::layout::cte::CAP1 || tcb.contains(&a) || node.contains(&a), "{a:#x} written");
                }
            }
            assert!(before.keys().all(|a| w.s.words.contains_key(a)));
        }
    }

    /// What the plan leaves to the gate: a non-cacheable map (it cleans
    /// the frame's lines first), a device frame, a large frame, tables
    /// that do not reach level 3, an address above USER_TOP, and a map into
    /// anything but a VSpace.
    #[test]
    fn local_map_plan_declines_what_the_gate_must_do() {
        let small = frame(FrameSize::Small, false, false);
        let cacheable = arm_vm_attr::PAGE_CACHEABLE;
        let mut w = world(FrameSize::Small, 0);
        set_frame(&mut w, small);
        assert!(map_plan(&w).is_none(), "non-cacheable");
        let mut w = world(FrameSize::Small, cacheable);
        set_frame(&mut w, frame(FrameSize::Small, true, false));
        assert!(map_plan(&w).is_none(), "device");
        let mut w = world(FrameSize::Large, cacheable);
        set_frame(&mut w, frame(FrameSize::Large, false, false));
        assert!(map_plan(&w).is_none(), "large frame");
        set_frame(&mut w, small);
        assert!(map_plan(&w).is_none(), "no level-3 table");
        let mut w = world(FrameSize::Small, cacheable);
        set_frame(&mut w, small);
        let t = sched::cur_thread(&w.s);
        t.set_reg(&mut w.s, msg::msg_register(0), USER_TOP + 1);
        assert!(map_plan(&w).is_none(), "above USER_TOP");
        t.set_reg(&mut w.s, msg::msg_register(0), VADDR);
        assert!(map_plan(&w).is_some());
        w.ex[0].set_cap(&mut w.s, Cap::HighVSpace { ptr: layout::pptr(ROOT), mapped: true, asid: ASID });
        assert!(map_plan(&w).is_none(), "ArmHighVSpace");
    }

    /// `localinv`'s plan for a CNode Delete of a mapped small RAM frame
    /// locks the slot and the very descriptor `unmap_page` clears; with
    /// tables that do not reach level 3 or an ASID that names nothing, it
    /// locks no descriptor, and `unmap_page` writes none.
    #[test]
    fn local_delete_plan_locks_the_descriptor_unmap_clears() {
        let cacheable = arm_vm_attr::PAGE_CACHEABLE;
        // A CNode of 16 slots, slot 3 holding the frame cap.
        let cnode = layout::pptr(0x90_0000);
        let dest = Slot(cnode + 3 * 32);
        let plan = |w: &World, asid: u64| {
            let t = sched::cur_thread(&w.s);
            let mut s2 = Mem { words: w.s.words.clone(), watch: 0, log: w.log.clone() };
            Slot(w.fslot.0).set_cap(&mut s2, Cap::CNode { ptr: cnode, radix: 4, guard_size: 0, guard: 0 });
            dest.set_cap(&mut s2, Cap::Frame { ptr: layout::pptr(FRAME), size: FrameSize::Small, rights: VM_READ_WRITE, is_device: false, mapped: true, is_ept: false, asid, vaddr: VADDR });
            t.set_reg(&mut s2, msg::msg_register(0), 3);
            t.set_reg(&mut s2, msg::msg_register(1), 4);
            crate::localinv::plan_with(&s2, t, label::CNodeDelete, w.fslot, w.ex)
        };
        let mut w = world(FrameSize::Small, cacheable);
        w.s.write(w.pte, entry(cacheable, 12));
        let p = plan(&w, ASID).expect("a local plan");
        assert_eq!(&p.locks[..p.n], &[dest.0, w.pte]);
        assert_eq!(p.pte, 1);
        w.log.borrow_mut().clear();
        unmap_page(&mut w.s, &mut w.a, FrameSize::Small, ASID, VADDR, layout::pptr(FRAME));
        assert_eq!(*w.log.borrow(), vec![Ev::Write(w.pte, 0), Ev::InvalidatePage(ASID, VADDR)]);
        // No level-3 table: no descriptor to lock or clear.
        let mut w = world(FrameSize::Large, cacheable);
        w.s.write(w.pte, entry(cacheable, 21));
        let p = plan(&w, ASID).expect("a local plan");
        assert_eq!(&p.locks[..p.n], &[dest.0]);
        assert!(p.pte >= p.n);
        w.log.borrow_mut().clear();
        unmap_page(&mut w.s, &mut w.a, FrameSize::Small, ASID, VADDR, layout::pptr(FRAME));
        assert!(w.log.borrow().is_empty());
        assert_eq!(w.s.read(w.pte), entry(cacheable, 21));
        // A frame mapped in an ArmHighVSpace: the same walk from its
        // level-0 table, and `invalidate_high_page`.
        let mut w = world(FrameSize::Small, cacheable);
        w.s.write(w.pte, entry(cacheable, 12));
        let pool = asid_table(&w.s, ASID >> ASID_LOW_BITS);
        w.s.write(pool + (ASID & 511) * 8, layout::pptr(ROOT) | ROOT_HIGH);
        assert_eq!(unmap_root(&w.s, ASID), Some((layout::pptr(ROOT), true)));
        let p = plan(&w, ASID).expect("a local plan");
        assert_eq!(&p.locks[..p.n], &[dest.0, w.pte]);
        assert_eq!(p.pte, 1);
        w.log.borrow_mut().clear();
        unmap_page(&mut w.s, &mut w.a, FrameSize::Small, ASID, VADDR, layout::pptr(FRAME));
        assert_eq!(*w.log.borrow(), vec![Ev::Write(w.pte, 0)]);
        // An ASID naming nothing.
        let p = plan(&w, ASID + 1).expect("a local plan");
        assert_eq!(&p.locks[..p.n], &[dest.0]);
        assert!(unmap_root(&w.s, ASID + 1).is_none());
    }
}

#[cfg(test)]
mod high_window_tests {
    //! `ArmHighVSpace` (the TTBR1 EL0 window), `TCBSetHighVSpace` and
    //! `TCBSetPACKeys`, through the invocations themselves.
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
        SetVspace(u64, u64),
        SetHigh(u64, u64),
        InvalidatePage(u64, u64),
        InvalidateAsid(u64),
        HighPage(u64),
        HighVspace(u64),
        CacheOp { root: u64, vaddr: u64 },
    }
    type Log = Rc<RefCell<Vec<Ev>>>;

    struct Mem {
        words: BTreeMap<u64, u64>,
    }
    impl Store for Mem {
        fn read(&self, a: u64) -> u64 {
            *self.words.get(&a).unwrap_or(&0)
        }
        fn write(&mut self, a: u64, v: u64) {
            self.words.insert(a, v);
        }
        fn zero(&mut self, a: u64, len: u64) {
            for i in (0..len).step_by(8) {
                self.words.remove(&(a + i));
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
        pauth: bool,
        epoch: u64,
        /// The kernel's TTBR1 tables (`kernel_ttbr1_entry`), or none.
        kernel: Option<(Vec<u64>, Vec<u64>)>,
    }
    impl Mach {
        fn ev(&self, e: Ev) {
            self.log.borrow_mut().push(e);
        }
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
        fn set_vspace(&mut self, root: u64, asid: u64) { self.ev(Ev::SetVspace(root, asid)) }
        fn invalidate_page(&mut self, asid: u64, vaddr: u64) { self.ev(Ev::InvalidatePage(asid, vaddr)) }
        fn invalidate_asid(&mut self, asid: u64) { self.ev(Ev::InvalidateAsid(asid)) }
        fn invalidate_page_structures(&mut self, _: u64) { panic!("unexpected") }
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
        fn send_reschedule(&mut self, _: u128) {}
        fn cache_op(&mut self, _op: u64, root: u64, _asid: u64, vaddr: u64, _len: u64, _paddr: u64) {
            self.ev(Ev::CacheOp { root, vaddr })
        }
        fn hw_access_flag(&self) -> bool { true }
        fn max_spi(&self) -> u64 { 0 }
        fn configure_irq(&mut self, _: u64, _: bool, _: u64) {}
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 { 0 }
        fn halt(&mut self) {}
        fn has_pauth(&self) -> bool { self.pauth }
        fn next_pac_epoch(&mut self) -> u64 {
            self.epoch += 1;
            self.epoch
        }
        fn kernel_ttbr1_entry(&self, level: u64, index: u64) -> u64 {
            match &self.kernel {
                Some((l0, l1)) => if level == 0 { l0[index as usize] } else { l1[index as usize] },
                None => 0,
            }
        }
        fn set_high_vspace(&mut self, root: u64, asid: u64) { self.ev(Ev::SetHigh(root, asid)) }
        fn invalidate_high_page(&mut self, vaddr: u64) { self.ev(Ev::HighPage(vaddr)) }
        fn invalidate_high_vspace(&mut self, root: u64) { self.ev(Ev::HighVspace(root)) }
    }

    const BASE: u64 = HIGH_VSPACE_BASE;
    const POOL_BASE: u64 = 0x200;
    // Physical addresses.
    const HIGH: u64 = 0x20_0000; // 8 KiB
    const VS: u64 = 0x20_4000;
    const L2: u64 = 0x21_0000;
    const L3: u64 = 0x21_1000;
    const POOL: u64 = 0x30_0000;
    const FRAME4K: u64 = 0x40_0000;
    const FRAME2M: u64 = 0x60_0000;
    const FRAME1G: u64 = 0x4000_0000;
    const BUF: u64 = 0x50_0000;

    fn p(pa: u64) -> u64 {
        layout::pptr(pa)
    }

    fn slot(i: u64) -> Slot {
        Slot(p(0x70_0000) + i * 32)
    }

    struct W {
        s: Mem,
        a: Mach,
        log: Log,
        ct: Tcb,
    }

    impl W {
        fn new(kernel: bool) -> W {
            let log: Log = Rc::new(RefCell::new(Vec::new()));
            let mut s = Mem { words: BTreeMap::new() };
            let kernel = if kernel {
                // As the kernel's own: the window, devices and image in 256-510,
                // entry 511 invalid.
                let l0: Vec<u64> = (0..512).map(|i| if (256..511).contains(&i) { 0x9000_0003 + i * 0x1000 } else { 0 }).collect();
                let l1: Vec<u64> = (0..512).map(|i| 0xa000_0003 + i * 0x1000).collect();
                Some((l0, l1))
            } else {
                None
            };
            let a = Mach { log: log.clone(), pauth: true, epoch: 0, kernel };
            let ct = Tcb(p(0x60_0000));
            sched::set_cur_thread(&mut s, ct);
            ct.set_state(&mut s, sched::TS_RUNNING);
            set_asid_table(&mut s, POOL_BASE >> ASID_LOW_BITS, p(POOL));
            W { s, a, log, ct }
        }
        fn args(&mut self, args: &[u64]) -> u64 {
            for (i, &v) in args.iter().enumerate() {
                if (i as u64) < crate::msg::N_MSG_REGISTERS {
                    self.ct.set_reg(&mut self.s, msg::msg_register(i as u64), v);
                } else {
                    self.s.write(p(BUF) + (i as u64 + 1) * 8, v);
                }
            }
            p(BUF)
        }
        fn invoke(&mut self, lbl: u64, length: u64, sl: Slot, args: &[u64], ex: [Slot; 3]) -> KResult<()> {
            let buf = self.args(args);
            self.log.borrow_mut().clear();
            let cap = sl.cap(&self.s);
            decode(&mut self.s, &mut self.a, lbl, length, sl, cap, false, buf, &ex)
        }
        fn events(&self) -> Vec<Ev> {
            self.log.borrow().clone()
        }
        /// A new ArmHighVSpace in slot 0, assigned an ASID (returned).
        fn high(&mut self) -> u64 {
            let c = crate::objects::create_object(&mut self.s, &mut self.a, fl4_abi::consts::object::ArmHighVSpace, p(HIGH), 0, false);
            slot(0).set_cap(&mut self.s, c);
            slot(1).set_cap(&mut self.s, Cap::AsidPool { ptr: p(POOL), asid_base: POOL_BASE });
            assert!(self.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(0), Slot(0), Slot(0)]).is_ok());
            match slot(0).cap(&self.s) {
                Cap::HighVSpace { ptr, mapped: true, asid } => {
                    assert_eq!(ptr, p(HIGH));
                    asid
                }
                _ => panic!("not assigned"),
            }
        }
        fn map_table(&mut self, pt: u64, sl: Slot, vaddr: u64) -> KResult<()> {
            sl.set_cap(&mut self.s, Cap::PageTable { ptr: p(pt), mapped: false, asid: 0, vaddr: 0 });
            self.invoke(label::ARMPageTableMap, 2, sl, &[vaddr], [slot(0), Slot(0), Slot(0)])
        }
        fn map_frame(&mut self, frame: u64, size: FrameSize, sl: Slot, vaddr: u64, attr: u64) -> KResult<()> {
            if !matches!(sl.cap(&self.s), Cap::Frame { .. }) {
                sl.set_cap(&mut self.s, Cap::Frame { ptr: p(frame), size, rights: VM_READ_WRITE, is_device: false, mapped: false, is_ept: false, asid: 0, vaddr: 0 });
            }
            self.invoke(label::ARMPageMap, 3, sl, &[vaddr, u64::MAX, attr], [slot(0), Slot(0), Slot(0)])
        }
    }

    fn l1_slot(i: u64) -> u64 {
        p(HIGH) + 4096 + i * 8
    }

    #[test]
    fn a_high_vspace_copies_the_kernel_tables_but_the_window() {
        let mut w = W::new(true);
        let c = crate::objects::create_object(&mut w.s, &mut w.a, fl4_abi::consts::object::ArmHighVSpace, p(HIGH), 0, false);
        assert!(c == Cap::HighVSpace { ptr: p(HIGH), mapped: false, asid: 0 });
        let (kl0, _kl1) = w.a.kernel.clone().unwrap();
        for i in 0..511 {
            assert_eq!(w.s.read(p(HIGH) + i * 8), kl0[i as usize], "L0[{i}]");
        }
        // L0[511]: its own empty level-1 table with PXNTable (kernel lives in L0[510]).
        assert_eq!(w.s.read(p(HIGH) + 511 * 8), (HIGH + 4096) | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE);
        for i in 0..512 {
            assert_eq!(w.s.read(l1_slot(i)), 0, "L1[{i}]");
        }
        // Without kernel tables (host tests): only the window's path.
        let mut w = W::new(false);
        let _ = crate::objects::create_object(&mut w.s, &mut w.a, fl4_abi::consts::object::ArmHighVSpace, p(HIGH), 0, false);
        let set: Vec<_> = w.s.words.iter().filter(|(&k, &v)| v != 0 && (p(HIGH)..p(HIGH) + 8192).contains(&k)).map(|(&k, &v)| (k, v)).collect();
        assert_eq!(set, vec![(p(HIGH) + 511 * 8, (HIGH + 4096) | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE)]);
    }

    #[test]
    fn asid_pool_assign_tags_a_high_vspace() {
        let mut w = W::new(true);
        let asid = w.high();
        assert_eq!(asid, POOL_BASE);
        assert!(find_asid_raw(&w.s, asid) == Ok(p(HIGH) | ROOT_HIGH));
        assert!(find_high_asid(&w.s, asid) == Ok(p(HIGH)));
        assert!(find_asid(&w.s, asid).is_err());
        assert!(crate::ept::find(&w.s, asid).is_err());
        // Assigned once only.
        assert!(w.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(0), Slot(0), Slot(0)]).is_err());
    }

    #[test]
    fn page_tables_and_frames_map_only_inside_the_window() {
        let mut w = W::new(true);
        let asid = w.high();
        let l0_511 = w.s.read(p(HIGH) + 511 * 8);
        // Outside the window: below it (the device area), at its top, and
        // a user address.
        for va in [BASE - (1 << 30), HIGH_VSPACE_TOP, HIGH_VSPACE_TOP + (1 << 30), 0x4000_0000, layout::PPTR_BASE] {
            assert!(matches!(w.map_table(L2, slot(2), va), Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))), "{va:#x}");
        }
        // Level 2 at L1[384], then level 3 below it.
        assert!(w.map_table(L2, slot(2), BASE + 0x1234).is_ok());
        assert!(slot(2).cap(&w.s) == Cap::PageTable { ptr: p(L2), mapped: true, asid, vaddr: BASE });
        let e = w.s.read(l1_slot(384));
        assert_eq!(e, L2 | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE);
        assert!(w.map_table(L3, slot(3), BASE).is_ok());
        assert_eq!(w.s.read(p(L2)), L3 | D_PXN_TABLE | D_VALID | D_TABLE_OR_PAGE);
        // A table where one is already: delete first.
        assert!(matches!(w.map_table(0x21_2000, slot(9), BASE), Err(Exc::Sys(SysError::DeleteFirst))));
        assert_eq!(w.s.read(p(HIGH) + 511 * 8), l0_511);

        // 4 KiB, 2 MiB and 1 GiB.
        assert!(w.map_frame(FRAME4K, FrameSize::Small, slot(4), BASE + 0x1000, arm_vm_attr::PAGE_CACHEABLE).is_ok());
        assert!(w.map_frame(FRAME2M, FrameSize::Large, slot(5), BASE + 0x20_0000, arm_vm_attr::PAGE_CACHEABLE).is_ok());
        assert!(w.map_frame(FRAME1G, FrameSize::Huge, slot(6), HIGH_VSPACE_TOP - (1 << 30), arm_vm_attr::PAGE_CACHEABLE).is_ok());
        let pte = w.s.read(p(L3) + 8);
        let blk = w.s.read(p(L2) + 8);
        let huge = w.s.read(l1_slot(495));
        for (e, pa, page) in [(pte, FRAME4K, true), (blk, FRAME2M, false), (huge, FRAME1G, false)] {
            assert_eq!(e & ADDR_MASK, pa);
            assert_eq!(e & (D_VALID | D_TABLE_OR_PAGE), if page { 3 } else { 1 });
            assert_ne!(e & D_PXN, 0, "PXN");
            assert_ne!(e & D_NG, 0, "nG");
            assert_eq!((e >> D_AP_SHIFT) & 3, 1, "EL0 read-write");
            assert_eq!(e & D_UXN, 0, "EL0 executable");
        }
        // The frame caps record the window's addresses (sign-extended).
        assert!(slot(4).cap(&w.s) == Cap::Frame { ptr: p(FRAME4K), size: FrameSize::Small, rights: VM_READ_WRITE, is_device: false, mapped: true, is_ept: false, asid, vaddr: BASE + 0x1000 });
        assert!(matches!(slot(6).cap(&w.s), Cap::Frame { vaddr, .. } if vaddr == HIGH_VSPACE_TOP - (1 << 30)));
        // Outside, or ending outside: refused, nothing written.
        let before = w.s.words.clone();
        for (size, va) in [(FrameSize::Huge, HIGH_VSPACE_TOP), (FrameSize::Small, BASE - 0x1000), (FrameSize::Large, HIGH_VSPACE_TOP), (FrameSize::Small, 0x1000)] {
            let r = w.map_frame(FRAME4K, size, slot(7), va, 0);
            assert!(matches!(r, Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))), "{va:#x}");
            slot(7).set_cap(&mut w.s, Cap::Null);
        }
        let tables = |m: &BTreeMap<u64, u64>| -> Vec<(u64, u64)> {
            m.iter().filter(|(&k, _)| (p(HIGH)..p(HIGH) + 8192).contains(&k) || (p(L2)..p(L3) + 4096).contains(&k)).map(|(&k, &v)| (k, v)).collect()
        };
        assert_eq!(tables(&w.s.words), tables(&before));
        // Remapping in place (new rights) flushes the page in every ASID.
        assert!(w.map_frame(FRAME4K, FrameSize::Small, slot(4), BASE + 0x1000, arm_vm_attr::PAGE_CACHEABLE | arm_vm_attr::EXECUTE_NEVER).is_ok());
        assert_eq!(w.events(), vec![Ev::HighPage(BASE + 0x1000)]);
        assert_ne!(w.s.read(p(L3) + 8) & D_UXN, 0);
        // An uncached RAM frame is cleaned through the kernel window only (root 0).
        assert!(w.map_frame(FRAME4K, FrameSize::Small, slot(8), BASE + 0x2000, 0).is_ok());
        assert_eq!(w.events(), vec![Ev::CacheOp { root: 0, vaddr: BASE + 0x2000 }]);
        // A frame mapped in the window cannot be mapped into a VSpace.
        slot(9).set_cap(&mut w.s, Cap::Pml4 { ptr: p(VS), mapped: false, asid: 0 });
        assert!(w.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(9), Slot(0), Slot(0)]).is_ok());
        let r = w.invoke(label::ARMPageMap, 3, slot(4), &[BASE + 0x1000, u64::MAX, 0], [slot(9), Slot(0), Slot(0)]);
        assert!(matches!(r, Err(Exc::Sys(SysError::InvalidCapability { arg: 1 }))));
        // Cache maintenance of a window frame: through the kernel window.
        let r = w.invoke(label::ARMPageClean_Data, 2, slot(4), &[0, 0x1000], [Slot(0); 3]);
        assert!(r.is_ok());
        assert_eq!(w.events(), vec![Ev::CacheOp { root: 0, vaddr: BASE + 0x1000 }]);
    }

    #[test]
    fn unmapping_in_the_window_flushes_it_and_keeps_level_0() {
        let mut w = W::new(true);
        let asid = w.high();
        assert!(w.map_table(L2, slot(2), BASE).is_ok());
        assert!(w.map_table(L3, slot(3), BASE).is_ok());
        assert!(w.map_frame(FRAME4K, FrameSize::Small, slot(4), BASE, arm_vm_attr::PAGE_CACHEABLE).is_ok());
        let l0 = w.s.read(p(HIGH) + 511 * 8);
        assert!(w.invoke(label::ARMPageUnmap, 0, slot(4), &[], [Slot(0); 3]).is_ok());
        assert_eq!(w.events(), vec![Ev::HighPage(BASE)]);
        assert_eq!(w.s.read(p(L3)), 0);
        assert!(matches!(slot(4).cap(&w.s), Cap::Frame { mapped: false, asid: 0, .. }));
        // Level 3, then level 2: the slot pointing at each, the whole
        // window flushed (its tables are about to be freed), L0[511] kept.
        assert!(w.invoke(label::ARMPageTableUnmap, 0, slot(3), &[], [Slot(0); 3]).is_ok());
        assert_eq!(w.events(), vec![Ev::HighVspace(p(HIGH))]);
        assert_eq!(w.s.read(p(L2)), 0);
        assert!(w.invoke(label::ARMPageTableUnmap, 0, slot(2), &[], [Slot(0); 3]).is_ok());
        assert_eq!(w.events(), vec![Ev::HighVspace(p(HIGH))]);
        assert_eq!(w.s.read(l1_slot(384)), 0);
        assert_eq!(w.s.read(p(HIGH) + 511 * 8), l0);
        assert_ne!(l0, 0);
        let _ = asid;
    }

    #[test]
    fn deleting_a_high_vspace_frees_its_asid_and_leaves_it_everywhere() {
        let mut w = W::new(true);
        let asid = w.high();
        let c = slot(0).cap(&w.s);
        w.log.borrow_mut().clear();
        let _ = crate::objects::finalise_cap_object(&mut w.s, &mut w.a, c, true);
        let ev = w.events();
        assert_eq!(ev[0], Ev::HighVspace(p(HIGH)));
        assert!(find_asid_raw(&w.s, asid).is_err());
        // A copy (not final) changes nothing.
        let mut w = W::new(true);
        let _ = w.high();
        let c = slot(0).cap(&w.s);
        w.log.borrow_mut().clear();
        let _ = crate::objects::finalise_cap_object(&mut w.s, &mut w.a, c, false);
        assert_eq!(w.events(), vec![]);
        // Deleting the pool flushes it too.
        let mut w = W::new(true);
        let asid = w.high();
        w.log.borrow_mut().clear();
        delete_asid_pool(&mut w.s, &mut w.a, POOL_BASE, p(POOL));
        assert_eq!(w.events()[0], Ev::HighVspace(p(HIGH)));
        assert!(find_high_asid(&w.s, asid).is_err());
    }

    fn tcb_ctx<'a>(sl: Slot, length: u64, buf: u64, ex: &'a [Slot; 3]) -> crate::tcb::Ctx<'a> {
        crate::tcb::Ctx { length, buf, call: false, slot: sl, extra: ex }
    }

    #[test]
    fn set_high_vspace_binds_a_copy_and_set_vm_root_runs_on_it() {
        let mut w = W::new(true);
        let asid = w.high();
        // The thread's VSpace.
        slot(9).set_cap(&mut w.s, Cap::Pml4 { ptr: p(VS), mapped: false, asid: 0 });
        assert!(w.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(9), Slot(0), Slot(0)]).is_ok());
        let vs_asid = match slot(9).cap(&w.s) { Cap::Pml4 { asid, .. } => asid, _ => panic!() };
        assert_ne!(vs_asid, asid);
        let target = Tcb(p(0x61_0000));
        let vc = slot(9).cap(&w.s);
        crate::cdt::insert(&mut w.s, vc, slot(9), target.slot(tl::SLOT_VTABLE));
        slot(10).set_cap(&mut w.s, Cap::Thread { ptr: target.0 });
        let ex = [slot(0), Slot(0), Slot(0)];
        assert!(crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex)).is_ok());
        assert!(target.slot(tl::SLOT_HIGH_VSPACE).cap(&w.s) == Cap::HighVSpace { ptr: p(HIGH), mapped: true, asid });
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, target);
        assert_eq!(w.events(), vec![Ev::SetVspace(p(VS), vs_asid), Ev::SetHigh(p(HIGH), vs_asid)]);
        // Running a VCPU (ARMVCPURun): never the window (leave TTBR1 before TTBR0).
        target.set_state(&mut w.s, sched::TS_RUNNING_VM);
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, target);
        assert_eq!(w.events(), vec![Ev::SetHigh(0, vs_asid), Ev::SetVspace(p(VS), vs_asid)]);
        target.set_state(&mut w.s, sched::TS_RUNNING);
        // A thread without a VSpace never runs the window (ASID 0 is everyone's).
        let bare = Tcb(p(0x62_0000));
        let hc = slot(0).cap(&w.s);
        crate::cdt::insert(&mut w.s, hc, slot(0), bare.slot(tl::SLOT_HIGH_VSPACE));
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, bare);
        assert_eq!(w.events(), vec![Ev::SetHigh(0, 0), Ev::SetVspace(0, 0)]);
        // Unassigned or the wrong kind of cap: refused.
        slot(11).set_cap(&mut w.s, Cap::HighVSpace { ptr: p(0x22_0000), mapped: false, asid: 0 });
        slot(12).set_cap(&mut w.s, Cap::Pml4 { ptr: p(VS), mapped: true, asid: vs_asid });
        for sl in [slot(11), slot(12)] {
            let ex = [sl, Slot(0), Slot(0)];
            let r = crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex));
            assert!(matches!(r, Err(Exc::Sys(SysError::InvalidCapability { arg: 1 }))));
        }
        let r = crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &[Slot(0); 3]));
        assert!(matches!(r, Err(Exc::Sys(SysError::TruncatedMessage))));
        // Unbinding with a null cap.
        let ex = [slot(13), Slot(0), Slot(0)];
        assert!(crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex)).is_ok());
        assert!(target.slot(tl::SLOT_HIGH_VSPACE).cap(&w.s).is_null());
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, target);
        assert_eq!(w.events(), vec![Ev::SetHigh(0, vs_asid), Ev::SetVspace(p(VS), vs_asid)]);
        // Bound again, then the window deleted: its ASID no longer names
        // it, so the thread runs without it.
        let ex = [slot(0), Slot(0), Slot(0)];
        assert!(crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex)).is_ok());
        delete_asid(&mut w.s, &mut w.a, asid, p(HIGH) | ROOT_HIGH);
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, target);
        assert_eq!(w.events(), vec![Ev::SetHigh(0, vs_asid), Ev::SetVspace(p(VS), vs_asid)]);
    }

    /// A VSpace assigned from the pool (slot 9) for thread `t`, and its ASID.
    fn give_vspace(w: &mut W, t: Tcb) -> u64 {
        slot(9).set_cap(&mut w.s, Cap::Pml4 { ptr: p(VS), mapped: false, asid: 0 });
        assert!(w.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(9), Slot(0), Slot(0)]).is_ok());
        let vc = slot(9).cap(&w.s);
        crate::cdt::insert(&mut w.s, vc, slot(9), t.slot(tl::SLOT_VTABLE));
        match vc {
            Cap::Pml4 { asid, .. } => asid,
            _ => panic!(),
        }
    }

    /// Astra R1 P2: a copy of a window cap whose ASID was deleted is refused
    /// before the thread's binding is touched.
    #[test]
    fn set_high_vspace_refuses_a_stale_cap_and_keeps_the_binding() {
        let mut w = W::new(true);
        let asid = w.high();
        let target = Tcb(p(0x61_0000));
        slot(10).set_cap(&mut w.s, Cap::Thread { ptr: target.0 });
        let ex = [slot(0), Slot(0), Slot(0)];
        assert!(crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex)).is_ok());
        let bound = target.slot(tl::SLOT_HIGH_VSPACE).cap(&w.s);
        assert!(bound == Cap::HighVSpace { ptr: p(HIGH), mapped: true, asid });
        // A second window, assigned, then its ASID deleted: its cap stays
        // `mapped: true` but names nothing.
        let h2 = p(0x22_0000);
        let c2 = crate::objects::create_object(&mut w.s, &mut w.a, fl4_abi::consts::object::ArmHighVSpace, h2, 0, false);
        slot(11).set_cap(&mut w.s, c2);
        assert!(w.invoke(label::ARMASIDPoolAssign, 0, slot(1), &[], [slot(11), Slot(0), Slot(0)]).is_ok());
        let asid2 = match slot(11).cap(&w.s) { Cap::HighVSpace { asid, .. } => asid, _ => panic!() };
        delete_asid(&mut w.s, &mut w.a, asid2, h2 | ROOT_HIGH);
        assert!(matches!(slot(11).cap(&w.s), Cap::HighVSpace { mapped: true, .. }));
        let ex = [slot(11), Slot(0), Slot(0)];
        let r = crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex));
        assert!(matches!(r, Err(Exc::Sys(SysError::InvalidCapability { arg: 1 }))));
        assert!(target.slot(tl::SLOT_HIGH_VSPACE).cap(&w.s) == bound);
        // A window whose ASID now names another root (reused): refused too.
        let raw = find_asid_raw(&w.s, asid).ok().unwrap();
        let pool = asid_table(&w.s, asid >> ASID_LOW_BITS);
        s_write_entry(&mut w.s, pool, asid, p(0x23_0000) | ROOT_HIGH);
        let ex = [slot(0), Slot(0), Slot(0)];
        let r = crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetHighVSpace, target, &tcb_ctx(slot(10), 0, 0, &ex));
        assert!(matches!(r, Err(Exc::Sys(SysError::InvalidCapability { arg: 1 }))));
        assert!(target.slot(tl::SLOT_HIGH_VSPACE).cap(&w.s) == bound);
        s_write_entry(&mut w.s, pool, asid, raw);
    }

    fn s_write_entry(s: &mut Mem, pool: u64, asid: u64, v: u64) {
        s.write(pool + (asid & 511) * 8, v);
    }

    /// Astra R1 P1: an `ARMVCPURun` that ends on the caller's own core, with
    /// no thread switch after it, gives the caller its window back.
    #[test]
    fn a_vcpu_run_returning_to_its_caller_reinstalls_the_window() {
        let mut w = W::new(true);
        let asid = w.high();
        let ct = w.ct;
        let vs_asid = give_vspace(&mut w, ct);
        let hc = slot(0).cap(&w.s);
        crate::cdt::insert(&mut w.s, hc, slot(0), ct.slot(tl::SLOT_HIGH_VSPACE));
        // Running the VCPU: no window.
        let vc = p(0x80_0000);
        ct.set_state(&mut w.s, sched::TS_RUNNING_VM);
        w.s.write(ct.0 + tl::RUN_VCPU, vc);
        w.s.write(vc + crate::vcpu::RUN_CALLER, ct.0);
        w.log.borrow_mut().clear();
        set_vm_root(&mut w.s, &mut w.a, ct);
        assert!(w.events().contains(&Ev::SetHigh(0, vs_asid)));
        // The run ends (a VCPU fault): back with the window, at once.
        w.log.borrow_mut().clear();
        crate::vcpu::complete_run(&mut w.s, &mut w.a, ct, fl4_abi::consts::vcpu_run_stop::VCPUFAULT, 0, 0, 0);
        assert_eq!(ct.state(&w.s), sched::TS_RUNNING);
        assert_eq!(w.events(), vec![Ev::SetVspace(p(VS), vs_asid), Ev::SetHigh(p(HIGH), vs_asid)]);
        // A caller that is not this core's current thread is left alone:
        // it is switched to anew wherever it runs next.
        let other = Tcb(p(0x63_0000));
        other.set_state(&mut w.s, sched::TS_RUNNING_VM);
        w.s.write(other.0 + tl::RUN_VCPU, vc);
        w.log.borrow_mut().clear();
        crate::vcpu::complete_run(&mut w.s, &mut w.a, other, fl4_abi::consts::vcpu_run_stop::VCPUFAULT, 0, 0, 0);
        assert_eq!(other.state(&w.s), sched::TS_RUNNING);
        assert!(w.events().iter().all(|e| !matches!(e, Ev::SetVspace(..) | Ev::SetHigh(..))));
        let _ = asid;
    }

    #[test]
    fn set_pac_keys_checks_its_arguments_and_takes_a_new_generation() {
        let mut w = W::new(false);
        let target = Tcb(p(0x61_0000));
        slot(10).set_cap(&mut w.s, Cap::Thread { ptr: target.0 });
        let keys: Vec<u64> = (1..=10).map(|i| 0x1111_0000_0000_0000 * i + i).collect();
        let call = |w: &mut W, flags: u64, length: u64| {
            let mut args = vec![flags];
            args.extend(&keys);
            let buf = w.args(&args);
            crate::tcb::decode(&mut w.s, &mut w.a, label::TCBSetPACKeys, target, &tcb_ctx(slot(10), length, buf, &[Slot(0); 3]))
        };
        assert!(matches!(call(&mut w, 1, 10), Err(Exc::Sys(SysError::TruncatedMessage))));
        assert!(matches!(call(&mut w, 0x10, 11), Err(Exc::Sys(SysError::InvalidArgument { arg: 0 }))));
        assert_eq!(w.s.read(target.0 + tl::PAC_EPOCH), 0);
        assert!(call(&mut w, 0xf, 11).is_ok());
        assert_eq!(w.s.read(target.0 + tl::PAC_FLAGS), 0xf);
        for i in 0..10 {
            assert_eq!(w.s.read(target.0 + tl::PAC_KEYS + i * 8), keys[i as usize]);
        }
        assert_eq!(w.s.read(target.0 + tl::PAC_EPOCH), 1);
        assert!(call(&mut w, fl4_abi::consts::pac_flag::EN_IA, 11).is_ok());
        assert_eq!(w.s.read(target.0 + tl::PAC_EPOCH), 2);
        assert_eq!(w.ct.state(&w.s), sched::TS_RESTART);
        // Without FEAT_PAuth only "off" is accepted.
        w.a.pauth = false;
        assert!(matches!(call(&mut w, 1, 11), Err(Exc::Sys(SysError::IllegalOperation))));
        assert_eq!(w.s.read(target.0 + tl::PAC_FLAGS), 1);
        assert!(call(&mut w, 0, 11).is_ok());
        assert_eq!(w.s.read(target.0 + tl::PAC_FLAGS), 0);
        assert_eq!(w.s.read(target.0 + tl::PAC_EPOCH), 3);
    }
}
