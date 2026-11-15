//! Notifications (seL4 object/notification.c, MCS).

use crate::layout::WALK_FUEL;
use crate::ipc;
use crate::layout::reg;
use crate::machine::{Arch, Store};
use crate::obj::{Ntfn, Sc, Tcb, NTFN_ACTIVE, NTFN_IDLE, NTFN_WAITING};
use crate::sched;
use crate::schedcontext;
use crate::sporadic;
use crate::tcbqueue::{self, Link, Queue};

fn get_queue<S: Store>(s: &S, n: Ntfn) -> Queue {
    Queue { head: Tcb(n.head(s)), end: Tcb(n.tail(s)) }
}

fn set_queue<S: Store>(s: &mut S, n: Ntfn, q: Queue, state: u64) {
    n.set_queue(s, q.head.0, q.end.0, state);
}

fn ntfn_append<S: Store>(s: &mut S, n: Ntfn, t: Tcb) {
    let q = get_queue(s, n);
    let q = tcbqueue::append_by_prio(s, Link::Ep, q, t);
    set_queue(s, n, q, NTFN_WAITING);
}

fn ntfn_dequeue<S: Store>(s: &mut S, n: Ntfn, t: Tcb) {
    let st = n.state(s);
    let q = get_queue(s, n);
    let q = tcbqueue::remove(s, Link::Ep, q, t);
    set_queue(s, n, q, if q.is_empty() { NTFN_IDLE } else { st });
}

pub fn reorder_ntfn<S: Store>(s: &mut S, n_ptr: u64, t: Tcb) {
    let n = Ntfn(n_ptr);
    let st = n.state(s);
    let q = get_queue(s, n);
    let q = tcbqueue::remove(s, Link::Ep, q, t);
    let q = tcbqueue::append_by_prio(s, Link::Ep, q, t);
    set_queue(s, n, q, st);
}

fn set_active<S: Store>(s: &mut S, n: Ntfn, badge: u64) {
    n.set_state(s, NTFN_ACTIVE);
    n.set_badge(s, badge);
}

fn maybe_donate_sched_context<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, n: Ntfn) {
    if t.sc(s) == 0 {
        let sc = Sc(n.sc(s));
        if !sc.is_null() && sc.tcb(s) == 0 {
            schedcontext::donate(s, a, sc, t);
            schedcontext::resume(s, a, sc);
        }
    }
}

/// seL4 `maybeReturnSchedContext`.
pub fn maybe_return_sched_context<S: Store>(s: &mut S, n: Ntfn, t: Tcb) {
    let sc = Sc(n.sc(s));
    if !sc.is_null() && sc.0 == t.sc(s) {
        t.set_sc(s, 0);
        sc.set_tcb(s, 0);
        if t == sched::cur_thread(s) {
            sched::reschedule_required(s);
        }
    }
}

fn unblock_sporadic<S: Store>(s: &mut S, t: Tcb) {
    let sc = Sc(t.sc(s));
    if sporadic::sc_sporadic(s, sc) && sc != sched::cur_sc(s) {
        sporadic::unblock_check(s, sc);
    }
}

/// seL4 `sendSignal` (MCS).
pub fn send_signal<S: Store, A: Arch>(s: &mut S, a: &mut A, n_ptr: u64, badge: u64) {
    let n = Ntfn(n_ptr);
    let st = n.state(s);
    if st == NTFN_IDLE {
        let t = Tcb(n.bound_tcb(s));
        if !t.is_null() && t.state(s) == sched::TS_BLOCKED_ON_RECV {
            ipc::cancel_ipc(s, a, t);
            sched::set_thread_state(s, t, sched::TS_RUNNING);
            t.set_reg(s, reg::BADGE, badge);
            maybe_donate_sched_context(s, a, t, n);
            if sched::is_schedulable(s, t) {
                sched::possible_switch_to(s, t);
            }
            unblock_sporadic(s, t);
        } else {
            set_active(s, n, badge);
            if !t.is_null() && t.state(s) == sched::TS_RUNNING_VM {
                // The owner checks bound signals before every VM entry.
                // Interrupt an in-flight guest so it reaches that check.
                crate::smp::remote_tcb_stall(s, a, t);
            }
        }
    } else if st == NTFN_WAITING {
        let dest = get_queue(s, n).head;
        ntfn_dequeue(s, n, dest);
        sched::set_thread_state(s, dest, sched::TS_RUNNING);
        dest.set_reg(s, reg::BADGE, badge);
        maybe_donate_sched_context(s, a, dest, n);
        if sched::is_schedulable(s, dest) {
            sched::possible_switch_to(s, dest);
        }
        unblock_sporadic(s, dest);
    } else {
        let b = n.badge(s) | badge;
        n.set_badge(s, b);
    }
}

/// seL4 `receiveSignal`.
pub fn receive_signal<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, n_ptr: u64, blocking: bool) {
    let n = Ntfn(n_ptr);
    let st = n.state(s);
    if st == NTFN_IDLE || st == NTFN_WAITING {
        if blocking {
            t.set_state(s, sched::TS_BLOCKED_ON_NTFN);
            t.set_block_obj(s, n_ptr);
            sched::schedule_tcb(s, t);
            ntfn_append(s, n, t);
            maybe_return_sched_context(s, n, t);
        } else {
            t.set_reg(s, reg::BADGE, 0);
        }
    } else {
        let b = n.badge(s);
        t.set_reg(s, reg::BADGE, b);
        n.set_state(s, NTFN_IDLE);
        maybe_donate_sched_context(s, a, t, n);
        let sc = Sc(t.sc(s));
        if sc != sched::cur_sc(s) && sporadic::sc_sporadic(s, sc) {
            sporadic::unblock_check(s, sc);
        }
    }
}

/// seL4 `cancelAllSignals`.
pub fn cancel_all_signals<S: Store>(s: &mut S, n_ptr: u64) {
    let n = Ntfn(n_ptr);
    if n.state(s) != NTFN_WAITING {
        return;
    }
    let mut t = get_queue(s, n).head;
    let mut fuel: u64 = WALK_FUEL;
    while !t.is_null() && fuel > 0 {
        fuel -= 1;
        let next = tcbqueue::next_of(s, Link::Ep, t);
        ntfn_dequeue(s, n, t);
        sched::set_thread_state(s, t, sched::TS_RESTART);
        unblock_sporadic(s, t);
        sched::possible_switch_to(s, t);
        t = next;
    }
    sched::reschedule_required(s);
}

/// seL4 `cancelSignal`.
pub fn cancel_signal<S: Store>(s: &mut S, t: Tcb, n_ptr: u64) {
    ntfn_dequeue(s, Ntfn(n_ptr), t);
    sched::set_thread_state(s, t, sched::TS_INACTIVE);
}

/// seL4 `completeSignal`.
pub fn complete_signal<S: Store, A: Arch>(s: &mut S, a: &mut A, n: Ntfn, t: Tcb) {
    if t.is_null() || n.state(s) != NTFN_ACTIVE {
        return;
    }
    let b = n.badge(s);
    t.set_reg(s, reg::BADGE, b);
    n.set_state(s, NTFN_IDLE);
    maybe_donate_sched_context(s, a, t, n);
    let sc = Sc(t.sc(s));
    if sporadic::sc_sporadic(s, sc) && sc.0 == n.sc(s) && sc != sched::cur_sc(s) {
        sporadic::unblock_check(s, sc);
    }
}

pub fn unbind_maybe_notification<S: Store>(s: &mut S, n_ptr: u64) {
    let n = Ntfn(n_ptr);
    let t = Tcb(n.bound_tcb(s));
    if !t.is_null() {
        n.set_bound_tcb(s, 0);
        t.set_bound_ntfn(s, 0);
    }
}

pub fn unbind_notification<S: Store>(s: &mut S, t: Tcb) {
    let n = Ntfn(t.bound_ntfn(s));
    if n.0 != 0 {
        n.set_bound_tcb(s, 0);
        t.set_bound_ntfn(s, 0);
    }
}

pub fn bind_notification<S: Store>(s: &mut S, t: Tcb, n_ptr: u64) {
    Ntfn(n_ptr).set_bound_tcb(s, t.0);
    t.set_bound_ntfn(s, n_ptr);
}
