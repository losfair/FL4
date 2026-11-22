//! Fast paths for the two kernel entries of an l4h guest syscall (FL4
//! issue #55): a thread's UnknownSyscall fault delivered to the handler
//! waiting on its fault endpoint, and the handler's ReplyRecv that answers
//! it and waits again. Both run after the same prefix as the general path
//! (`FAULT_IP`, `budget_ok`), and each is meant to leave the state exactly
//! as `handle_syscall` would: every write the general path makes, in an
//! order that gives the same values, and the same Arch calls in the same
//! order. Their preconditions are checked with reads only, so a fast path
//! that declines (`false`) leaves the state to the general path untouched.
//!
//! What they skip is the general path's dispatch: decoding, the second
//! lookup of the reply cap, the possible-switch, enqueue and dequeue pair
//! that leaves the ready queues as they were, and the scheduler's search.
//! Under Safe RET every out-of-line call costs a mispredicted return, so
//! the common case calls only `set_vm_root`'s lookup, `commit_time` and
//! `set_next_interrupt`.
//!
//! Not yet proved: the intended theorem is `fast s = (true, s') ->
//! handle_syscall_general s = s'`. fl4-sim checks it differentially
//! (`--fastpath-diff`), running each syscall both ways from the same state.

use crate::capability::Cap;
use crate::cspace;
use crate::error::Fault;
use crate::faults;
use crate::ipc;
use crate::layout::{node, reg, tcb as tl};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{node_get, node_set, Ep, Ntfn, Reply, Sc, Tcb, EP_IDLE, EP_RECV, NTFN_ACTIVE};
use crate::sched;
use crate::sporadic;
use fl4_abi::consts::fault as ft;

/// Whether `schedule()`, entered with `to` made runnable, would do nothing
/// but choose it: no due timer or released thread to wake (`awaken`), a
/// domain with time left, and `to` local to this core and its domain, with
/// a scheduling context and outside the release queue. Choosing `to` over
/// queued threads is the caller's to check.
#[inline(always)]
pub(crate) fn schedulable_here<S: Store>(s: &S, to: Tcb) -> bool {
    let cpu = s.cur_cpu();
    let now = sched::cur_time(s);
    let tm = Tcb(node_get(s, cpu, node::TIMER_MIN));
    if !tm.is_null() && tm.timer_deadline(s) <= now {
        return false;
    }
    let rh = Tcb(node_get(s, cpu, node::RELEASE_HEAD));
    if !rh.is_null() && sporadic::ready(s, Sc(rh.sc(s))) {
        return false;
    }
    !sched::is_cur_domain_expired(s)
        && sched::domain_time(s) != 0
        && to.affinity(s) == cpu
        && to.domain(s) == sched::cur_domain(s)
        && to.sc(s) != 0
        && !sched::in_release_queue(s, to)
        && !sched::queued(s, to)
}

/// The rest of `schedule()` and `activate_thread()` once it has chosen
/// `to`: switch to it and its scheduling context.
#[inline(always)]
pub(crate) fn switch_to<S: Store, A: Arch>(s: &mut S, a: &mut A, to: Tcb) {
    crate::vspace::set_vm_root(s, a, to);
    sched::set_cur_thread(s, to);
    sched::set_action(s, sched::ACTION_RESUME_CURRENT);
    sched::switch_sched_context(s, a);
    let c = s.cur_cpu();
    if node_get(s, c, node::REPROGRAM) != 0 {
        sched::set_next_interrupt(s, a);
        node_set(s, c, node::REPROGRAM, 0);
    }
    crate::smp::send_pending(s, a);
    sched::activate_thread(s, a);
}

/// `handle_fault` for an UnknownSyscall fault of the current thread `t`,
/// and the `schedule()` after it, when the fault endpoint has a handler
/// waiting with a reply object and its own scheduling context, and the
/// handler is the thread to run next. Returns false, having changed
/// nothing, otherwise.
#[inline(always)]
pub fn fault<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, number: u64) -> bool {
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
    faults::set_fault(s, t, Fault::UnknownSyscall { number });
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
    msg::set_msg_info(s, dest, MessageInfo::new(ft::UnknownSyscall, 0, 0, sent));
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

/// `SysReplyRecv` of the current thread and the `schedule()` after it, when
/// it answers an UnknownSyscall fault through a reply object no scheduling
/// context was donated through, the faulting thread can run at once and is
/// the thread to run next, and the endpoint it waits on next is idle with
/// nothing signalled to its bound notification. Returns false, having
/// changed nothing, otherwise.
#[inline(always)]
pub fn reply_recv<S: Store, A: Arch>(s: &mut S, a: &mut A) -> bool {
    let t = sched::cur_thread(s);
    match reply_caps(s, t) {
        Some((rptr, ep_ptr)) => reply_recv_found(s, a, t, rptr, ep_ptr),
        None => false,
    }
}

/// The objects of the current thread `t`'s ReplyRecv as the general path
/// finds them: the reply object its reply cap names and the endpoint its
/// capability register names, which it may receive on.
#[inline(always)]
pub fn reply_caps<S: Store>(s: &S, t: Tcb) -> Option<(u64, u64)> {
    let root = t.slot(tl::SLOT_CTABLE).cap(s);
    let rptr = match cspace::resolve_address_bits(s, root, t.reg(s, reg::REPLY), cspace::WORD_BITS) {
        Ok(found) => match found.slot.cap(s) {
            Cap::Reply { ptr, .. } => ptr,
            _ => return None,
        },
        Err(_) => return None,
    };
    match cspace::resolve_address_bits(s, root, t.reg(s, reg::CAP), cspace::WORD_BITS) {
        Ok(found) => match found.slot.cap(s) {
            Cap::Endpoint { ptr, recv: true, .. } => Some((rptr, ptr)),
            _ => None,
        },
        Err(_) => None,
    }
}

/// `reply_recv` once `reply_caps` found `rptr` and `ep_ptr`.
#[inline(always)]
pub fn reply_recv_found<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, rptr: u64, ep_ptr: u64) -> bool {
    if sched::action(s) != sched::ACTION_RESUME_CURRENT || !sched::is_schedulable(s, t) {
        return false;
    }
    let info = msg::msg_info(s, t);
    if info.extra_caps != 0 || info.label != 0 {
        return false;
    }
    let r = Reply(rptr);
    let u = Tcb(r.tcb(s));
    if u.is_null() || u.state(s) != sched::TS_BLOCKED_ON_REPLY || u.fault_type(s) != ft::UnknownSyscall {
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
