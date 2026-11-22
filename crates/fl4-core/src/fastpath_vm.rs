//! Fast paths for the two kernel entries of an l4h guest page fault: a
//! thread's VM fault delivered to the handler waiting on its fault
//! endpoint, and the handler's ReplyRecv that resumes it. They are
//! `fastpath::fault` and `fastpath::reply_recv_found` with a VM fault in
//! place of an UnknownSyscall fault (its message, and the reply that always
//! restarts the thread: `faults::handle_fault_reply`), kept apart so that
//! the proved fast paths stay as they are. They run only beside the serial
//! gate (fl4-sync); under it a page fault takes the general path.
//!
//! Not yet proved, and not yet exercised by fl4-sim, which generates no
//! VM faults (neither `--fastpath-diff` nor the footprint oracle sees them).

use crate::capability::Cap;
use crate::error::Fault;
use crate::faults;
use crate::fastpath::{schedulable_here, switch_to};
use crate::ipc;
use crate::layout::{node, reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{node_get, Ep, Ntfn, Reply, Sc, Tcb, EP_IDLE, EP_RECV, NTFN_ACTIVE};
use crate::sched;
use crate::sporadic;
use fl4_abi::consts::fault as ft;

/// `fastpath::fault` for a VM fault `f` of the current thread `t`.
#[inline(always)]
pub fn vm_fault<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, f: Fault) -> bool {
    if sched::action(s) != sched::ACTION_RESUME_CURRENT {
        return false;
    }
    let (ep_ptr, badge, grant, grant_reply) = match t.slot(tl::SLOT_FAULT_HANDLER).cap(s) {
        Cap::Endpoint { ptr, badge, grant, grant_reply, .. } => (ptr, badge, grant, grant_reply),
        _ => return false,
    };
    let ep = Ep(ep_ptr);
    if !(grant || grant_reply) || ep.state(s) != EP_RECV {
        return false;
    }
    let dest = Tcb(ep.head(s));
    let r = Reply(dest.reply_obj(s));
    if r.0 == 0 || !schedulable_here(s, dest) {
        return false;
    }
    // choose_thread takes the head of the highest nonempty ready queue,
    // where possible_switch_to puts `dest` in front.
    if !sched::is_highest_prio(s, sched::cur_domain(s), dest.prio(s)) {
        return false;
    }

    // send_fault_ipc
    faults::set_fault(s, t, f);
    // send_ipc, a receiver waiting: ep_dequeue of the head
    let tail = ep.tail(s);
    if tail == dest.0 {
        ep.set_queue(s, 0, 0, EP_IDLE);
    } else {
        let after = Tcb(dest.ep_next(s));
        after.set_ep_prev(s, 0);
        ep.set_queue(s, after.0, tail, EP_RECV);
    }
    dest.set_ep_next(s, 0);
    dest.set_ep_prev(s, 0);
    // do_ipc_transfer: the fault message
    let recv_buf = msg::lookup_ipc_buffer(s, true, dest);
    let sent = faults::set_mrs_fault(s, a, t, dest, recv_buf);
    msg::set_msg_info(s, dest, MessageInfo::new(ft::VMFault, 0, 0, sent));
    dest.set_reg(s, reg::BADGE, badge);
    // reply_unlink (`dest` is not the current thread)
    r.set_tcb(s, 0);
    dest.set_state(s, sched::TS_INACTIVE);
    // reply_push: `dest` has a scheduling context, so none is donated.
    // set_blocked_on_reply makes the action CHOOSE_NEW, which switch_to
    // ends as RESUME_CURRENT, as schedule() does.
    r.set_tcb(s, t.0);
    t.set_state(s, sched::TS_BLOCKED_ON_REPLY);
    t.set_reply_obj(s, r.0);
    dest.set_state(s, sched::TS_RUNNING);
    let dsc = Sc(dest.sc(s));
    if sporadic::sc_sporadic(s, dsc) && dsc != sched::cur_sc(s) {
        sporadic::unblock_check(s, dsc);
    }
    // possible_switch_to enqueues `dest`, and schedule() dequeues it again:
    // the queues and bitmaps end as they were, `dest`'s links cleared.
    dest.set_sched_next(s, 0);
    dest.set_sched_prev(s, 0);
    switch_to(s, a, dest);
    true
}


/// `fastpath::reply_recv_found` for a ReplyRecv answering a VM fault.
#[inline(always)]
pub fn reply_recv_vm_found<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, rptr: u64, ep_ptr: u64) -> bool {
    if sched::action(s) != sched::ACTION_RESUME_CURRENT || !sched::is_schedulable(s, t) {
        return false;
    }
    let info = msg::msg_info(s, t);
    if info.extra_caps != 0 || info.label != 0 {
        return false;
    }
    let r = Reply(rptr);
    let u = Tcb(r.tcb(s));
    if u.is_null() || u.state(s) != sched::TS_BLOCKED_ON_REPLY || u.fault_type(s) != ft::VMFault {
        return false;
    }
    // Not the head of a call stack (reply_pop would move a donated SC).
    if r.next(s) != 0 && r.next_is_head(s) {
        return false;
    }
    // do_reply_transfer runs the thread at once (possible_switch_to)
    // rather than raising a timeout fault or postponing it. unblock_check
    // keeps a ready head ready and its amount no smaller, so this holds
    // after it exactly when before.
    let usc = Sc(u.sc(s));
    if usc.is_null() || !sporadic::ready(s, usc) || !sporadic::sufficient(s, a, usc, 0) || !schedulable_here(s, u) {
        return false;
    }
    let ntfn = Ntfn(t.bound_ntfn(s));
    if ntfn.0 != 0 && (ntfn.state(s) == NTFN_ACTIVE || (ntfn.sc(s) != 0 && ntfn.sc(s) == t.sc(s))) {
        return false;
    }
    let ep = Ep(ep_ptr);
    if ep.state(s) != EP_IDLE {
        return false;
    }
    // schedule(): the action is `u`, and `t`, blocked, is not schedulable.
    // (An if, not `||`: see ioport::decode.)
    let fastfail = if t == sched::idle_thread(s) || u.prio(s) < t.prio(s) { true } else { false };
    if fastfail && !sched::is_highest_prio(s, sched::cur_domain(s), u.prio(s)) {
        return false;
    }

    // decode_invocation: `t` stays schedulable, so the action stays.
    t.set_state(s, sched::TS_RESTART);
    // do_reply_transfer
    ipc::reply_remove(s, a, r, u);
    if sporadic::sc_sporadic(s, usc) && usc.0 != node_get(s, usc.cpu(s), node::CUR_SC) {
        sporadic::unblock_check(s, usc);
    }
    let restart = faults::handle_fault_reply(s, a, u, t);
    faults::clear_fault(s, u);
    u.set_state(s, if restart { sched::TS_RESTART } else { sched::TS_INACTIVE });
    // possible_switch_to(u), from RESUME_CURRENT
    sched::set_action(s, u.0);
    // handle_invocation: not a Call
    t.set_state(s, sched::TS_RUNNING);
    // receive_ipc, nothing to take: wait_for_sender on the idle endpoint
    t.set_state(s, sched::TS_BLOCKED_ON_RECV);
    t.set_block_obj(s, ep_ptr);
    t.set_reply_obj(s, r.0);
    r.set_tcb(s, t.0);
    t.set_ep_next(s, 0);
    t.set_ep_prev(s, 0);
    ep.set_queue(s, t.0, t.0, EP_RECV);
    switch_to(s, a, u);
    true
}
