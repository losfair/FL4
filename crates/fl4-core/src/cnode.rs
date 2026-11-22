//! CNode invocations (seL4 decodeCNodeInvocation, MCS).

use crate::capability::{Cap, Rights};
use crate::cdt;
use crate::cspace;
use crate::endpoint;
use crate::error::{illegal, truncated, Exc, KResult, LookupFault, SysError};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::Slot;
use crate::objects;
use crate::sched;
use fl4_abi::label;

fn missing_source<T>(depth: u64, source: bool) -> KResult<T> {
    Err(Exc::Sys(SysError::FailedLookup { source, lf: LookupFault::MissingCapability { bits_left: depth } }))
}

pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, cap: Cap, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if lbl < label::CNodeRevoke || lbl > label::CNodeRotate {
        return illegal();
    }
    if length < 2 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let index = msg::syscall_arg(s, ct, buf, 0);
    let depth = msg::syscall_arg(s, ct, buf, 1);
    let dest = cspace::lookup_target_slot(s, cap, index, depth)?;
    if lbl >= label::CNodeCopy && lbl <= label::CNodeMutate {
        decode_copy(s, lbl, length, buf, extra, dest)
    } else if lbl == label::CNodeRevoke {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        cdt::revoke(s, a, dest)
    } else if lbl == label::CNodeDelete {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        cdt::delete(s, a, dest, true)
    } else if lbl == label::CNodeCancelBadgedSends {
        decode_cancel_badged_sends(s, dest)
    } else if lbl == label::CNodeRotate {
        decode_rotate(s, length, buf, extra, dest)
    } else {
        Ok(())
    }
}

/// CNode Copy, Mint, Move and Mutate.
fn decode_copy<S: Store>(s: &mut S, lbl: u64, length: u64, buf: u64, extra: &[Slot; 3], dest: Slot) -> KResult<()> {
    if length < 4 || extra[0].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let src_index = msg::syscall_arg(s, ct, buf, 2);
    let src_depth = msg::syscall_arg(s, ct, buf, 3);
    let src_root = extra[0].cap(s);
    cdt::ensure_empty_slot(s, dest)?;
    let src = cspace::lookup_source_slot(s, src_root, src_index, src_depth)?;
    let src_cap = src.cap(s);
    if src_cap.is_null() {
        return missing_source(src_depth, true);
    }
    let (new_cap, is_move) = copied_cap(s, lbl, length, buf, src, src_cap)?;
    if new_cap.is_null() {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if is_move {
        cdt::move_cap(s, new_cap, src, dest);
    } else {
        cdt::insert_with_cap(s, new_cap, src_cap, src, dest);
    }
    Ok(())
}

/// The cap a Copy, Mint, Move or Mutate puts in the destination, and
/// whether it moves rather than copies.
fn copied_cap<S: Store>(s: &S, lbl: u64, length: u64, buf: u64, src: Slot, src_cap: Cap) -> KResult<(Cap, bool)> {
    let ct = sched::cur_thread(s);
    if lbl == label::CNodeCopy {
        if length < 5 {
            return truncated();
        }
        let r = Rights::from_word(msg::syscall_arg(s, ct, buf, 4));
        let c = crate::capability::mask_cap_rights(r, src_cap);
        Ok((objects::derive_cap(s, src, c)?, false))
    } else if lbl == label::CNodeMint {
        if length < 6 {
            return truncated();
        }
        let r = Rights::from_word(msg::syscall_arg(s, ct, buf, 4));
        let data = msg::syscall_arg(s, ct, buf, 5);
        let c = crate::capability::mask_cap_rights(r, src_cap);
        Ok((objects::derive_cap(s, src, objects::update_cap_data(false, data, c))?, false))
    } else if lbl == label::CNodeMove {
        Ok((src_cap, true))
    } else {
        if length < 5 {
            return truncated();
        }
        let data = msg::syscall_arg(s, ct, buf, 4);
        Ok((objects::update_cap_data(true, data, src_cap), true))
    }
}

/// A full-rights endpoint cap's object and badge.
fn full_endpoint(c: Cap) -> Option<(u64, u64)> {
    match c {
        Cap::Endpoint { ptr, badge, send: true, recv: true, grant: true, grant_reply: true } => Some((ptr, badge)),
        _ => None,
    }
}

fn decode_cancel_badged_sends<S: Store>(s: &mut S, dest: Slot) -> KResult<()> {
    let (ptr, badge) = match full_endpoint(dest.cap(s)) {
        Some(x) => x,
        None => return illegal(),
    };
    let ct = sched::cur_thread(s);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if badge != 0 {
        endpoint::cancel_badged_sends(s, ptr, badge);
    }
    Ok(())
}

fn decode_rotate<S: Store>(s: &mut S, length: u64, buf: u64, extra: &[Slot; 3], dest: Slot) -> KResult<()> {
    if length < 8 || extra[0].is_null() || extra[1].is_null() {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let pivot_data = msg::syscall_arg(s, ct, buf, 2);
    let src_data = msg::syscall_arg(s, ct, buf, 5);
    let (src, pivot) = rotate_slots(s, buf, extra, dest)?;
    let new_src = objects::update_cap_data(true, src_data, src.cap(s));
    let new_pivot = objects::update_cap_data(true, pivot_data, pivot.cap(s));
    if new_src.is_null() || new_pivot.is_null() {
        return illegal();
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    if src == dest {
        cdt::swap(s, new_src, src, new_pivot, pivot);
    } else {
        cdt::move_cap(s, new_pivot, pivot, dest);
        cdt::move_cap(s, new_src, src, pivot);
    }
    Ok(())
}

/// The source and pivot slots of a Rotate, with seL4's checks on them.
fn rotate_slots<S: Store>(s: &S, buf: u64, extra: &[Slot; 3], dest: Slot) -> KResult<(Slot, Slot)> {
    let ct = sched::cur_thread(s);
    let pivot_index = msg::syscall_arg(s, ct, buf, 3);
    let pivot_depth = msg::syscall_arg(s, ct, buf, 4);
    let src_index = msg::syscall_arg(s, ct, buf, 6);
    let src_depth = msg::syscall_arg(s, ct, buf, 7);
    let pivot_root = extra[0].cap(s);
    let src_root = extra[1].cap(s);
    let src = cspace::lookup_source_slot(s, src_root, src_index, src_depth)?;
    let pivot = cspace::lookup_pivot_slot(s, pivot_root, pivot_index, pivot_depth)?;
    if pivot == src || pivot == dest {
        return illegal();
    }
    if src != dest {
        cdt::ensure_empty_slot(s, dest)?;
    }
    if src.cap(s).is_null() {
        return missing_source(src_depth, true);
    }
    if pivot.cap(s).is_null() {
        return missing_source(pivot_depth, false);
    }
    Ok((src, pivot))
}
