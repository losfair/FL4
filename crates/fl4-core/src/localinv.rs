//! Frame-capability invocations beside the serial gate (DESIGN.md §7,
//! "Local paths"): CNode Copy and Mint of a frame cap, CNode Delete of a
//! small RAM frame cap, and X86Page_Map of a small frame. A guest maps
//! every page through its own frame-cap copy (l4h's vspace.c), so fork,
//! exit and page faults are mostly these three.
//!
//! `plan` resolves, without locks, the kernel words the general path of
//! the invocation may write besides the caller and this core: capability
//! slots and one page-table entry. It reads each word of those slots it
//! decides from once and records the value (`Plan::read`). The runtime
//! locks them (`fl4_store::lock`), and `syscall::handle_invocation_local`
//! runs the general decode only if every recorded word still holds its
//! value (`Plan::still_holds`), and declines otherwise.
//!
//! What may change outside the gate is exactly what these paths write:
//! the cap words of an empty slot (Copy, Mint) or of a frame-cap slot (Map,
//! Delete), the CDT links of any slot next to one, and a leaf page-table
//! entry of a small page. Every lookup a plan makes reads only other words:
//! CNode caps along a CPtr's path (a path through a slot being written
//! fails, as it does on either side of the write: the type tag is in the
//! first cap word, which a write stores first, and x86 keeps stores and
//! loads in order), the vspace cap, the ASID table and the paging
//! structures above the leaf. CPtrs, depths and the virtual address come
//! from the caller's saved registers; extra caps are looked up once, here,
//! and the decode uses those slots, so a change to the caller's IPC buffer
//! in between cannot move a write onto an unlocked word. x86_64 only.
//!
//! Not yet exercised by fl4-sim, which generates no frame-cap copies,
//! maps or deletes.

use crate::capability::{Cap, FrameSize};
use crate::cspace;
use crate::ipc::{self, ExtraCaps};
use crate::layout::{cte, reg};
use crate::machine::Store;
use crate::msg;
use crate::obj::{Slot, Tcb};
use fl4_abi::label;
use fl4_abi::syscall as sc;

/// Words a local invocation may lock (`fl4_store::lock::MAX_HELD`).
pub const MAX_LOCKS: usize = 4;

/// A local invocation: the invoked slot, the extra caps, and what to lock
/// (capability slots, 32 bytes, then at most one page-table entry, 8).
#[derive(Clone, Copy)]
pub struct Plan {
    pub slot: Slot,
    pub extra: ExtraCaps,
    pub locks: [u64; MAX_LOCKS],
    pub n: usize,
    /// `locks[pte]` is a page-table entry, if `pte < n`.
    pub pte: usize,
    /// Words of the locked slots the plan was read from, and their values:
    /// the rest of what it read changes only under the gate.
    seen: [(u64, u64); MAX_LOCKS],
    nseen: usize,
    ok_words: bool,
}

impl Plan {
    fn new(slot: Slot, extra: ExtraCaps) -> Plan {
        Plan { slot, extra, locks: [0; MAX_LOCKS], n: 0, pte: MAX_LOCKS, seen: [(0, 0); MAX_LOCKS], nseen: 0, ok_words: true }
    }

    fn add(&mut self, addr: u64) -> bool {
        if addr == 0 {
            return true;
        }
        if self.n >= MAX_LOCKS {
            return false;
        }
        self.locks[self.n] = addr;
        self.n += 1;
        true
    }

    fn add_pte(&mut self, addr: u64) -> bool {
        self.pte = self.n;
        self.add(addr)
    }

    /// Read word `addr` of a slot the plan will lock, once: the plan
    /// decides from the value returned, and `still_holds` checks that very
    /// value under the locks. (Reading it again later could see a value
    /// another core's local path wrote since the decision.) Past
    /// `MAX_LOCKS` words, which no plan needs, the plan is refused.
    fn read<S: Store>(&mut self, s: &S, addr: u64) -> u64 {
        if self.nseen >= MAX_LOCKS {
            self.ok_words = false;
            return 0;
        }
        let v = s.read(addr);
        self.seen[self.nseen] = (addr, v);
        self.nseen += 1;
        v
    }

    /// The cap in `slot`, from words read once (`read`).
    fn read_cap<S: Store>(&mut self, s: &S, slot: Slot) -> Cap {
        let w0 = self.read(s, slot.0.wrapping_add(cte::CAP0));
        let w1 = self.read(s, slot.0.wrapping_add(cte::CAP1));
        Cap::decode(w0, w1)
    }

    /// With the plan's words locked: the words it was read from still hold
    /// what it read, so planning again would give the same plan.
    pub fn still_holds<S: Store>(&self, s: &S) -> bool {
        let mut i = 0;
        while i < self.nseen && i < MAX_LOCKS {
            let (addr, v) = self.seen[i];
            if s.read(addr) != v {
                return false;
            }
            i += 1;
        }
        true
    }
}

fn some_if(ok: bool, p: Plan) -> Option<Plan> {
    if ok && p.ok_words {
        Some(p)
    } else {
        None
    }
}

/// Argument `i` of `t`'s invocation, for `i` below msg::N_MSG_REGISTERS:
/// a saved register, which only `t` changes.
fn reg_arg<S: Store>(s: &S, t: Tcb, i: u64) -> u64 {
    msg::syscall_arg(s, t, 0, i)
}

/// A label `plan` may take, by the label alone (a register).
#[inline(always)]
pub fn is_local_label(lbl: u64) -> bool {
    !cfg!(feature = "aarch64") && (lbl == label::CNodeCopy || lbl == label::CNodeMint || lbl == label::CNodeDelete || is_page_map(lbl))
}

#[cfg(not(feature = "aarch64"))]
fn is_page_map(lbl: u64) -> bool {
    lbl == label::X86PageMap
}

#[cfg(feature = "aarch64")]
fn is_page_map(_lbl: u64) -> bool {
    false
}

/// A small, non-device frame cap outside an EPT.
fn small_ram_frame(c: Cap) -> bool {
    matches!(c, Cap::Frame { size: FrameSize::Small, is_device: false, is_ept: false, .. })
}

/// The plan for the current thread's `SysCall`, if it is a local
/// invocation whose lookups all succeed.
pub fn plan<S: Store>(s: &S, number: i64) -> Option<Plan> {
    if number != sc::SysCall {
        return None;
    }
    let t = crate::sched::cur_thread(s);
    let info = msg::msg_info(s, t);
    if !is_local_label(info.label) {
        return None;
    }
    let slot = match cspace::lookup_slot(s, t, t.reg(s, reg::CAP)) {
        Ok(r) => r.slot,
        Err(_) => return None,
    };
    let buf = msg::lookup_ipc_buffer(s, false, t);
    let extra = match ipc::lookup_extra_caps(s, t, buf, info) {
        Ok(e) => e,
        Err(_) => return None,
    };
    plan_with(s, t, info.label, slot, extra)
}

/// The plan for invoking `slot` with `extra`. Under the locks,
/// `Plan::still_holds` checks that it is still the plan.
pub fn plan_with<S: Store>(s: &S, t: Tcb, lbl: u64, slot: Slot, extra: ExtraCaps) -> Option<Plan> {
    let mut p = Plan::new(slot, extra);
    let cap = slot.cap(s);
    if lbl == label::CNodeCopy || lbl == label::CNodeMint {
        if !matches!(cap, Cap::CNode { .. }) || extra[0].is_null() {
            return None;
        }
        let dest = cspace::lookup_target_slot(s, cap, reg_arg(s, t, 0), reg_arg(s, t, 1)).ok()?;
        let src = cspace::lookup_source_slot(s, extra[0].cap(s), reg_arg(s, t, 2), reg_arg(s, t, 3)).ok()?;
        // An empty destination (its type tag, in the first word), the
        // source cap, and the source's CDT link, which names the third slot.
        let dest_w0 = p.read(s, dest.0.wrapping_add(cte::CAP0));
        let src_cap = p.read_cap(s, src);
        let next = Slot::next_of_word(p.read(s, src.0.wrapping_add(cte::NEXT)));
        if !matches!(src_cap, Cap::Frame { is_ept: false, .. }) || !Cap::decode(dest_w0, 0).is_null() {
            return None;
        }
        let ok = p.add(dest.0) && p.add(src.0) && p.add(next.0);
        some_if(ok, p)
    } else if lbl == label::CNodeDelete {
        if !matches!(cap, Cap::CNode { .. }) {
            return None;
        }
        let dest = cspace::lookup_target_slot(s, cap, reg_arg(s, t, 0), reg_arg(s, t, 1)).ok()?;
        // The cap decides the page-table entry; its links the other slots.
        let c = p.read_cap(s, dest);
        let prev = Slot(p.read(s, dest.0.wrapping_add(cte::PREV)));
        let next = Slot::next_of_word(p.read(s, dest.0.wrapping_add(cte::NEXT)));
        if !small_ram_frame(c) {
            return None;
        }
        if !(p.add(dest.0) && p.add(prev.0) && p.add(next.0)) {
            return None;
        }
        match c {
            Cap::Frame { mapped: true, asid, vaddr, .. } if asid != 0 => {
                // As unmap_page: no mapping to clear if the lookups fail.
                match small_page_entry(s, asid, vaddr) {
                    Some(e) => {
                        let ok = p.add_pte(e);
                        some_if(ok, p)
                    }
                    None => some_if(true, p),
                }
            }
            _ => some_if(true, p),
        }
    } else if is_page_map(lbl) {
        // The frame cap, read once (`cap` above is not recorded).
        let frame = p.read_cap(s, slot);
        if !small_ram_frame(frame) || extra[0].is_null() {
            return None;
        }
        let root = match extra[0].cap(s) {
            Cap::Pml4 { ptr, mapped: true, .. } => ptr,
            _ => return None,
        };
        let e = page_entry(s, root, reg_arg(s, t, 0))?;
        let ok = p.add(slot.0) && p.add_pte(e);
        some_if(ok, p)
    } else {
        None
    }
}

#[cfg(not(feature = "aarch64"))]
fn small_page_entry<S: Store>(s: &S, asid: u64, vaddr: u64) -> Option<u64> {
    let root = crate::vspace::find_vspace_for_asid(s, asid).ok()?;
    page_entry(s, root, vaddr)
}

/// Only user addresses: a map above USER_TOP fails in the decode, and a
/// plan for one would walk (and lock) the kernel's half of the tables.
#[cfg(not(feature = "aarch64"))]
fn page_entry<S: Store>(s: &S, root: u64, vaddr: u64) -> Option<u64> {
    if vaddr > fl4_abi::consts::USER_TOP {
        return None;
    }
    crate::vspace::small_page_entry(s, root, vaddr)
}

#[cfg(feature = "aarch64")]
fn small_page_entry<S: Store>(_s: &S, _asid: u64, _vaddr: u64) -> Option<u64> {
    None
}

#[cfg(feature = "aarch64")]
fn page_entry<S: Store>(_s: &S, _root: u64, _vaddr: u64) -> Option<u64> {
    None
}
