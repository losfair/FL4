//! Message transfer, cancellation, and replies (seL4 kernel/thread.c
//! doIPCTransfer and friends, endpoint.c cancelIPC, MCS reply.c).

use crate::capability::Cap;
use crate::cdt;
use crate::cspace;
use crate::endpoint;
use crate::error::Fault;
use crate::faults;
use crate::layout::reg;
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::notification;
use crate::obj::{Reply, Sc, Slot, Tcb};
use crate::objects;
use crate::sched;
use crate::schedcontext;
use crate::sporadic;

/// Up to three extra caps looked up from the sender's IPC buffer.
pub type ExtraCaps = [Slot; 3];

pub const NO_EXTRA_CAPS: ExtraCaps = [Slot(0), Slot(0), Slot(0)];

/// seL4 `lookupExtraCaps`. Errors are lookup faults for the given cptr.
#[inline(always)]
pub fn lookup_extra_caps<S: Store>(s: &S, thread: Tcb, buf: u64, info: MessageInfo) -> Result<ExtraCaps, Fault> {
    let mut caps = NO_EXTRA_CAPS;
    if buf == 0 {
        return Ok(caps);
    }
    let n = info.extra_caps;
    let mut i: u64 = 0;
    while i < n && i < 3 {
        let cptr = msg::buf_get(s, buf, msg::BUF_CAPS.wrapping_add(i));
        match cspace::lookup_slot(s, thread, cptr) {
            Ok(r) => caps[i as usize] = r.slot,
            Err(lf) => return Err(Fault::Cap { addr: cptr, in_recv: false, lf }),
        }
        i += 1;
    }
    Ok(caps)
}

/// seL4 `getReceiveSlots`.
fn get_receive_slot<S: Store>(s: &S, thread: Tcb, buf: u64) -> Slot {
    if buf == 0 {
        return Slot(0);
    }
    let root_cptr = msg::buf_get(s, buf, msg::BUF_RECV_CNODE);
    let index = msg::buf_get(s, buf, msg::BUF_RECV_INDEX);
    let depth = msg::buf_get(s, buf, msg::BUF_RECV_DEPTH);
    let cnode = match cspace::lookup_cap(s, thread, root_cptr) {
        Ok(c) => c,
        Err(_) => return Slot(0),
    };
    match cspace::lookup_target_slot(s, cnode, index, depth) {
        Ok(slot) => {
            if slot.cap(s).is_null() {
                slot
            } else {
                Slot(0)
            }
        }
        Err(_) => Slot(0),
    }
}

/// seL4 `transferCaps`.
/// The badge of `cap` if it is a cap to `ep`: transferring it to a
/// receiver on `ep` unwraps it.
fn unwrapped_badge(cap: Cap, ep: u64) -> Option<u64> {
    if let Cap::Endpoint { ptr, badge, .. } = cap {
        if ptr == ep {
            return Some(badge);
        }
    }
    None
}

fn transfer_caps<S: Store>(s: &mut S, info: MessageInfo, extra: &ExtraCaps, ep: u64, receiver: Tcb, recv_buf: u64) -> MessageInfo {
    let mut out = MessageInfo::new(info.label, 0, 0, info.length);
    if extra[0].is_null() || recv_buf == 0 {
        return out;
    }
    let mut dest = get_receive_slot(s, receiver, recv_buf);
    let mut i: u64 = 0;
    while i < 3 && !extra[i as usize].is_null() {
        let slot = extra[i as usize];
        let cap = slot.cap(s);
        match unwrapped_badge(cap, ep) {
            Some(badge) => {
                msg::buf_set(s, recv_buf, msg::BUF_CAPS.wrapping_add(i), badge);
                out.caps_unwrapped |= 1u64 << (i & 63);
            }
            None => {
                if dest.is_null() {
                    break;
                }
                let derived = match objects::derive_cap(s, slot, cap) {
                    Ok(c) => c,
                    Err(_) => break,
                };
                if derived.is_null() {
                    break;
                }
                cdt::insert(s, derived, slot, dest);
                dest = Slot(0);
            }
        }
        i += 1;
    }
    out.extra_caps = i;
    out
}

/// seL4 `doNormalTransfer`.
fn do_normal_transfer<S: Store>(s: &mut S, sender: Tcb, send_buf: u64, ep: u64, badge: u64, can_grant: bool, receiver: Tcb, recv_buf: u64) {
    let tag = msg::msg_info(s, sender);
    let extra = if can_grant {
        match lookup_extra_caps(s, sender, send_buf, tag) {
            Ok(e) => e,
            Err(_) => NO_EXTRA_CAPS,
        }
    } else {
        NO_EXTRA_CAPS
    };
    let n = msg::copy_mrs(s, sender, send_buf, receiver, recv_buf, tag.length);
    let mut out = transfer_caps(s, tag, &extra, ep, receiver, recv_buf);
    out.length = n;
    msg::set_msg_info(s, receiver, out);
    receiver.set_reg(s, reg::BADGE, badge);
}

/// seL4 `doFaultTransfer`.
#[inline(always)]
fn do_fault_transfer<S: Store, A: Arch>(s: &mut S, a: &A, badge: u64, sender: Tcb, receiver: Tcb, recv_buf: u64) {
    let sent = faults::set_mrs_fault(s, a, sender, receiver, recv_buf);
    let ftype = sender.fault_type(s);
    msg::set_msg_info(s, receiver, MessageInfo::new(ftype, 0, 0, sent));
    receiver.set_reg(s, reg::BADGE, badge);
}

/// seL4 `doIPCTransfer`.
#[inline(always)]
pub fn do_ipc_transfer<S: Store, A: Arch>(s: &mut S, a: &A, sender: Tcb, ep: u64, badge: u64, grant: bool, receiver: Tcb) {
    let recv_buf = msg::lookup_ipc_buffer(s, true, receiver);
    if sender.fault_type(s) == fl4_abi::consts::fault::NullFault {
        let send_buf = msg::lookup_ipc_buffer(s, false, sender);
        do_normal_transfer(s, sender, send_buf, ep, badge, grant, receiver, recv_buf);
    } else {
        do_fault_transfer(s, a, badge, sender, receiver, recv_buf);
    }
}

// ---- replies (MCS call stack) ---------------------------------------------

/// seL4 `reply_unlink`.
#[inline(always)]
pub fn reply_unlink<S: Store>(s: &mut S, r: Reply, t: Tcb) {
    r.set_tcb(s, 0);
    sched::set_thread_state(s, t, sched::TS_INACTIVE);
}

/// seL4 `reply_push`.
#[inline(always)]
pub fn reply_push<S: Store, A: Arch>(s: &mut S, a: &mut A, caller: Tcb, callee: Tcb, r: Reply, can_donate: bool) {
    let sc_donated = Sc(caller.sc(s));
    r.set_tcb(s, caller.0);
    sched::set_blocked_on_reply(s, caller, r.0);
    if !sc_donated.is_null() && callee.sc(s) == 0 && can_donate {
        let old_caller = Reply(sc_donated.reply(s));
        if old_caller.0 != 0 {
            old_caller.set_next(s, r.0, false);
        }
        r.set_prev(s, old_caller.0);
        sc_donated.set_reply(s, r.0);
        r.set_next(s, sc_donated.0, true);
        schedcontext::donate(s, a, sc_donated, callee);
    }
}

/// seL4 `reply_pop`.
pub fn reply_pop<S: Store, A: Arch>(s: &mut S, a: &mut A, r: Reply, t: Tcb) {
    let next = r.next(s);
    let prev = r.prev(s);
    let next_raw = r.next_raw(s);
    Sc(next).set_reply(s, prev);
    if prev != 0 {
        Reply(prev).set_next_raw(s, next_raw);
    }
    r.set_next(s, 0, false);
    if t.sc(s) == 0 {
        schedcontext::donate(s, a, Sc(next), t);
    }
    r.set_prev(s, 0);
    reply_unlink(s, r, t);
}

/// seL4 `reply_remove`.
#[inline(always)]
pub fn reply_remove<S: Store, A: Arch>(s: &mut S, a: &mut A, r: Reply, t: Tcb) {
    let next = r.next(s);
    let prev = r.prev(s);
    if next != 0 && r.next_is_head(s) {
        reply_pop(s, a, r, t);
    } else {
        if next != 0 {
            Reply(next).set_prev(s, 0);
        }
        if prev != 0 {
            Reply(prev).set_next(s, 0, false);
        }
        r.set_prev(s, 0);
        r.set_next(s, 0, false);
        reply_unlink(s, r, t);
    }
}

/// seL4 `reply_remove_tcb`.
pub fn reply_remove_tcb<S: Store>(s: &mut S, t: Tcb) {
    let r = Reply(t.reply_obj(s));
    let next = r.next(s);
    let prev = r.prev(s);
    if next != 0 {
        if r.next_is_head(s) {
            Sc(next).set_reply(s, 0);
        } else {
            Reply(next).set_prev(s, 0);
        }
    }
    if prev != 0 {
        Reply(prev).set_next(s, 0, false);
    }
    r.set_prev(s, 0);
    r.set_next(s, 0, false);
    reply_unlink(s, r, t);
}

/// seL4 `cancelIPC` (MCS).
pub fn cancel_ipc<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    let _ = a;
    faults::clear_fault(s, t);
    let st = t.state(s);
    if st == sched::TS_BLOCKED_ON_SEND || st == sched::TS_BLOCKED_ON_RECV {
        let ep = t.block_obj(s);
        endpoint::ep_dequeue(s, ep, t);
        if st == sched::TS_BLOCKED_ON_RECV {
            let r = Reply(t.reply_obj(s));
            if r.0 != 0 {
                reply_unlink(s, r, t);
            }
        }
        sched::set_thread_state(s, t, sched::TS_INACTIVE);
    } else if st == sched::TS_BLOCKED_ON_NTFN {
        notification::cancel_signal(s, t, t.block_obj(s));
    } else if st == sched::TS_BLOCKED_ON_REPLY {
        reply_remove_tcb(s, t);
    }
}

/// seL4 `doReplyTransfer` (MCS).
#[inline(always)]
pub fn do_reply_transfer<S: Store, A: Arch>(s: &mut S, a: &mut A, sender: Tcb, r: Reply, grant: bool) {
    let receiver = Tcb(r.tcb(s));
    if receiver.is_null() || receiver.state(s) != sched::TS_BLOCKED_ON_REPLY {
        return;
    }
    reply_remove(s, a, r, receiver);
    let rsc = Sc(receiver.sc(s));
    if sporadic::sc_sporadic(s, rsc) && rsc.0 != crate::obj::node_get(s, rsc.cpu(s), crate::layout::node::CUR_SC) {
        sporadic::unblock_check(s, rsc);
    }
    let fault_type = receiver.fault_type(s);
    if fault_type == fl4_abi::consts::fault::NullFault {
        do_ipc_transfer(s, a, sender, 0, 0, grant, receiver);
        sched::set_thread_state(s, receiver, sched::TS_RUNNING);
    } else {
        let restart = faults::handle_fault_reply(s, a, receiver, sender);
        faults::clear_fault(s, receiver);
        sched::set_thread_state(s, receiver, if restart { sched::TS_RESTART } else { sched::TS_INACTIVE });
    }
    let sc = Sc(receiver.sc(s));
    if !sc.is_null() && sched::is_runnable(s, receiver) {
        if sporadic::ready(s, sc) && sporadic::sufficient(s, a, sc, 0) {
            sched::possible_switch_to(s, receiver);
        } else if faults::valid_timeout_handler(s, receiver) && fault_type != fl4_abi::consts::fault::Timeout {
            let badge = sc.badge(s);
            faults::handle_timeout(s, a, receiver, Fault::Timeout { badge });
        } else {
            sched::postpone(s, sc);
        }
    }
}
