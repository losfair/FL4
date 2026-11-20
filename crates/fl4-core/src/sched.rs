//! Thread states, ready and release queues, the scheduler, and MCS budget
//! accounting (seL4 kernel/thread.c, object/tcb.c queues, thread.h).

use crate::layout::WALK_FUEL;
use crate::error::{Exc, KResult};
use crate::faults;
use crate::layout::{ks, node, NUM_DOMAINS, NUM_PRIORITIES};
use crate::machine::{Arch, Store};
use crate::obj::{ks_get, ks_set, node_get, node_set, Sc, Tcb};
use crate::schedcontext;
use crate::sporadic;
use crate::tcbqueue::{self, Link, Queue};

pub const TS_INACTIVE: u64 = 0;
pub const TS_RUNNING: u64 = 1;
pub const TS_RESTART: u64 = 2;
pub const TS_BLOCKED_ON_RECV: u64 = 3;
pub const TS_BLOCKED_ON_SEND: u64 = 4;
pub const TS_BLOCKED_ON_REPLY: u64 = 5;
pub const TS_BLOCKED_ON_NTFN: u64 = 6;
pub const TS_IDLE: u64 = 7;
pub const TS_RUNNING_VM: u64 = 8;

pub const ACTION_RESUME_CURRENT: u64 = 0;
pub const ACTION_CHOOSE_NEW: u64 = 1;

const Q_QUEUED: u64 = 1;
const Q_RELEASE: u64 = 2;

pub const MAX_WORK_UNITS_PER_PREEMPTION: u64 = 100;

// ---- per-core state -------------------------------------------------------

pub fn cpu<S: Store>(s: &S) -> u64 {
    s.cur_cpu()
}

pub fn cur_thread<S: Store>(s: &S) -> Tcb {
    Tcb(node_get(s, s.cur_cpu(), node::CUR_THREAD))
}

pub fn set_cur_thread<S: Store>(s: &mut S, t: Tcb) {
    let c = s.cur_cpu();
    node_set(s, c, node::CUR_THREAD, t.0)
}

pub fn idle_thread<S: Store>(s: &S) -> Tcb {
    Tcb(node_get(s, s.cur_cpu(), node::IDLE_THREAD))
}

pub fn cur_sc<S: Store>(s: &S) -> Sc {
    Sc(node_get(s, s.cur_cpu(), node::CUR_SC))
}

pub fn idle_sc<S: Store>(s: &S) -> Sc {
    Sc(node_get(s, s.cur_cpu(), node::IDLE_SC))
}

pub fn action<S: Store>(s: &S) -> u64 {
    node_get(s, s.cur_cpu(), node::SCHED_ACTION)
}

pub fn set_action<S: Store>(s: &mut S, v: u64) {
    let c = s.cur_cpu();
    node_set(s, c, node::SCHED_ACTION, v)
}

pub fn cur_time<S: Store>(s: &S) -> u64 {
    node_get(s, s.cur_cpu(), node::CUR_TIME)
}

pub fn consumed<S: Store>(s: &S) -> u64 {
    node_get(s, s.cur_cpu(), node::CONSUMED)
}

fn set_consumed<S: Store>(s: &mut S, v: u64) {
    let c = s.cur_cpu();
    node_set(s, c, node::CONSUMED, v)
}

pub fn set_reprogram_on<S: Store>(s: &mut S, cpu: u64) {
    node_set(s, cpu, node::REPROGRAM, 1)
}

pub fn set_reprogram<S: Store>(s: &mut S) {
    let c = s.cur_cpu();
    node_set(s, c, node::REPROGRAM, 1)
}

pub fn cur_domain<S: Store>(s: &S) -> u64 {
    ks_get(s, ks::CUR_DOMAIN)
}

pub fn domain_time<S: Store>(s: &S) -> u64 {
    ks_get(s, ks::DOMAIN_TIME)
}

// ---- thread state ----------------------------------------------------------

pub fn state<S: Store>(s: &S, t: Tcb) -> u64 {
    t.state(s)
}

pub fn is_runnable<S: Store>(s: &S, t: Tcb) -> bool {
    let st = t.state(s);
    st == TS_RUNNING || st == TS_RESTART || st == TS_RUNNING_VM
}

pub fn is_blocked<S: Store>(s: &S, t: Tcb) -> bool {
    let st = t.state(s);
    st == TS_BLOCKED_ON_RECV || st == TS_BLOCKED_ON_SEND || st == TS_BLOCKED_ON_NTFN || st == TS_BLOCKED_ON_REPLY
}

pub fn is_stopped<S: Store>(s: &S, t: Tcb) -> bool {
    t.state(s) == TS_INACTIVE || is_blocked(s, t)
}

pub fn queued<S: Store>(s: &S, t: Tcb) -> bool {
    t.in_queues(s) & Q_QUEUED != 0
}

pub fn in_release_queue<S: Store>(s: &S, t: Tcb) -> bool {
    t.in_queues(s) & Q_RELEASE != 0
}

fn set_flag<S: Store>(s: &mut S, t: Tcb, f: u64, v: bool) {
    let q = t.in_queues(s);
    t.set_in_queues(s, if v { q | f } else { q & !f });
}

#[inline(always)]
pub fn is_schedulable<S: Store>(s: &S, t: Tcb) -> bool {
    if !is_runnable(s, t) {
        return false;
    }
    let sc = Sc(t.sc(s));
    !sc.is_null() && sporadic::sc_active(s, sc) && !in_release_queue(s, t)
}

/// seL4 `scheduleTCB`.
#[inline(always)]
pub fn schedule_tcb<S: Store>(s: &mut S, t: Tcb) {
    if t == cur_thread(s) && action(s) == ACTION_RESUME_CURRENT && !is_schedulable(s, t) {
        set_action(s, ACTION_CHOOSE_NEW);
    }
}

/// seL4 `setThreadState`.
pub fn set_thread_state<S: Store>(s: &mut S, t: Tcb, st: u64) {
    t.set_state(s, st);
    schedule_tcb(s, t);
}

#[inline(always)]
pub fn set_blocked_on_reply<S: Store>(s: &mut S, t: Tcb, reply: u64) {
    t.set_state(s, TS_BLOCKED_ON_REPLY);
    t.set_reply_obj(s, reply);
    schedule_tcb(s, t);
}

// ---- ready queues ----------------------------------------------------------

fn rq_index(dom: u64, prio: u64) -> u64 {
    if NUM_DOMAINS > 1 {
        dom.wrapping_mul(NUM_PRIORITIES).wrapping_add(prio)
    } else {
        prio
    }
}

fn rq_head_off(dom: u64, prio: u64) -> u64 {
    node::READY_QUEUES.wrapping_add(rq_index(dom, prio).wrapping_mul(16))
}

fn l1_off(dom: u64) -> u64 {
    node::L1_BITMAP.wrapping_add(dom.wrapping_mul(8))
}

fn l2_off(dom: u64, inv: u64) -> u64 {
    node::L2_BITMAP.wrapping_add((dom.wrapping_mul(4).wrapping_add(inv)).wrapping_mul(8))
}

fn bitmap_dom(dom: u64) -> u64 {
    if NUM_DOMAINS > 1 {
        dom
    } else {
        0
    }
}

#[inline(always)]
fn add_to_bitmap<S: Store>(s: &mut S, cpu: u64, dom: u64, prio: u64) {
    let d = bitmap_dom(dom);
    let l1 = prio >> 6;
    let inv = 3 - (l1 & 3);
    let v1 = node_get(s, cpu, l1_off(d));
    node_set(s, cpu, l1_off(d), v1 | (1u64 << (l1 & 63)));
    let v2 = node_get(s, cpu, l2_off(d, inv));
    node_set(s, cpu, l2_off(d, inv), v2 | (1u64 << (prio & 63)));
}

fn remove_from_bitmap<S: Store>(s: &mut S, cpu: u64, dom: u64, prio: u64) {
    let d = bitmap_dom(dom);
    let l1 = prio >> 6;
    let inv = 3 - (l1 & 3);
    let v2 = node_get(s, cpu, l2_off(d, inv)) & !(1u64 << (prio & 63));
    node_set(s, cpu, l2_off(d, inv), v2);
    if v2 == 0 {
        let v1 = node_get(s, cpu, l1_off(d));
        node_set(s, cpu, l1_off(d), v1 & !(1u64 << (l1 & 63)));
    }
}

/// Index of the highest set bit; `w` is nonzero (callers check).
fn highest_set_bit(w: u64) -> u64 {
    63u64.wrapping_sub(w.leading_zeros() as u64) & 63
}

pub fn highest_prio<S: Store>(s: &S, dom: u64) -> u64 {
    let cpu = s.cur_cpu();
    let d = bitmap_dom(dom);
    let l1 = node_get(s, cpu, l1_off(d));
    let l1i = highest_set_bit(l1);
    let inv = 3 - (l1i & 3);
    let l2 = node_get(s, cpu, l2_off(d, inv));
    (l1i << 6) | highest_set_bit(l2)
}

pub fn is_highest_prio<S: Store>(s: &S, dom: u64, prio: u64) -> bool {
    let d = bitmap_dom(dom);
    node_get(s, s.cur_cpu(), l1_off(d)) == 0 || prio >= highest_prio(s, dom)
}

fn q_get<S: Store>(s: &S, cpu: u64, off: u64) -> Queue {
    Queue { head: Tcb(node_get(s, cpu, off)), end: Tcb(node_get(s, cpu, off.wrapping_add(8))) }
}

fn q_set<S: Store>(s: &mut S, cpu: u64, off: u64, q: Queue) {
    node_set(s, cpu, off, q.head.0);
    node_set(s, cpu, off.wrapping_add(8), q.end.0);
}

/// seL4 `tcbSchedEnqueue`.
#[inline(always)]
pub fn enqueue<S: Store>(s: &mut S, t: Tcb) {
    if queued(s, t) {
        return;
    }
    let cpu = t.affinity(s);
    let dom = t.domain(s);
    let prio = t.prio(s);
    let off = rq_head_off(dom, prio);
    let q = q_get(s, cpu, off);
    if q.is_empty() {
        add_to_bitmap(s, cpu, dom, prio);
    }
    let q = tcbqueue::prepend(s, Link::Sched, q, t);
    q_set(s, cpu, off, q);
    set_flag(s, t, Q_QUEUED, true);
    crate::smp::remote_queue_update(s, t);
}

/// seL4 `tcbSchedAppend`.
pub fn append<S: Store>(s: &mut S, t: Tcb) {
    if queued(s, t) {
        return;
    }
    let cpu = t.affinity(s);
    let dom = t.domain(s);
    let prio = t.prio(s);
    let off = rq_head_off(dom, prio);
    let q = q_get(s, cpu, off);
    if q.is_empty() {
        add_to_bitmap(s, cpu, dom, prio);
    }
    let q = tcbqueue::append(s, Link::Sched, q, t);
    q_set(s, cpu, off, q);
    set_flag(s, t, Q_QUEUED, true);
    crate::smp::remote_queue_update(s, t);
}

/// seL4 `tcbSchedDequeue`.
#[inline(always)]
pub fn dequeue<S: Store>(s: &mut S, t: Tcb) {
    if !queued(s, t) {
        return;
    }
    let cpu = t.affinity(s);
    let dom = t.domain(s);
    let prio = t.prio(s);
    let off = rq_head_off(dom, prio);
    let q = q_get(s, cpu, off);
    let q = tcbqueue::remove(s, Link::Sched, q, t);
    q_set(s, cpu, off, q);
    set_flag(s, t, Q_QUEUED, false);
    if q.is_empty() {
        remove_from_bitmap(s, cpu, dom, prio);
    }
}

// ---- release queue ---------------------------------------------------------

fn ready_time<S: Store>(s: &S, t: Tcb) -> u64 {
    sporadic::head(s, Sc(t.sc(s))).time
}

/// seL4 `tcbReleaseRemove`.
pub fn release_remove<S: Store>(s: &mut S, t: Tcb) {
    if !in_release_queue(s, t) {
        return;
    }
    let cpu = t.affinity(s);
    if node_get(s, cpu, node::RELEASE_HEAD) == t.0 {
        set_reprogram_on(s, cpu);
    }
    let q = q_get(s, cpu, node::RELEASE_HEAD);
    let q = tcbqueue::remove(s, Link::Sched, q, t);
    q_set(s, cpu, node::RELEASE_HEAD, q);
    set_flag(s, t, Q_RELEASE, false);
}

/// seL4 `tcbReleaseEnqueue`: the release queue is ordered by ready time.
pub fn release_enqueue<S: Store>(s: &mut S, t: Tcb) {
    let cpu = t.affinity(s);
    let q = q_get(s, cpu, node::RELEASE_HEAD);
    let new_time = ready_time(s, t);
    if q.is_empty() || new_time < ready_time(s, q.head) {
        let nq = tcbqueue::prepend(s, Link::Sched, q, t);
        q_set(s, cpu, node::RELEASE_HEAD, nq);
    } else if ready_time(s, q.end) <= new_time {
        let nq = tcbqueue::append(s, Link::Sched, q, t);
        q_set(s, cpu, node::RELEASE_HEAD, nq);
    } else {
        // The first thread released after new_time exists and is not the
        // head, because of the checks above.
        let mut after = q.head;
        let mut fuel: u64 = WALK_FUEL;
        while !after.is_null() && new_time >= ready_time(s, after) && fuel > 0 {
            fuel -= 1;
            after = Tcb(after.sched_next(s));
        }
        tcbqueue::insert_before(s, Link::Sched, t, after);
    }
    set_flag(s, t, Q_RELEASE, true);
    if node_get(s, cpu, node::RELEASE_HEAD) != q.head.0 {
        set_reprogram_on(s, cpu);
    }
    crate::smp::remote_queue_update(s, t);
}

// ---- scheduling decisions --------------------------------------------------

/// seL4 `rescheduleRequired`.
#[inline(always)]
pub fn reschedule_required<S: Store>(s: &mut S) {
    let act = action(s);
    if act != ACTION_RESUME_CURRENT && act != ACTION_CHOOSE_NEW && is_schedulable(s, Tcb(act)) {
        enqueue(s, Tcb(act));
    }
    set_action(s, ACTION_CHOOSE_NEW);
}

/// seL4 `possibleSwitchTo`.
#[inline(always)]
pub fn possible_switch_to<S: Store>(s: &mut S, t: Tcb) {
    if t.sc(s) == 0 || in_release_queue(s, t) {
        return;
    }
    if cur_domain(s) != t.domain(s) || t.affinity(s) != s.cur_cpu() {
        enqueue(s, t);
    } else if action(s) != ACTION_RESUME_CURRENT {
        reschedule_required(s);
        enqueue(s, t);
    } else {
        set_action(s, t.0);
    }
}

/// seL4 `postpone`.
pub fn postpone<S: Store>(s: &mut S, sc: Sc) {
    let t = Tcb(sc.tcb(s));
    dequeue(s, t);
    release_enqueue(s, t);
    let cpu = sc.cpu(s);
    set_reprogram_on(s, cpu);
}

/// seL4 `setNextInterrupt`.
pub fn set_next_interrupt<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let now = cur_time(s);
    let csc = Sc(cur_thread(s).sc(s));
    let mut next = now.wrapping_add(sporadic::head(s, csc).amount);
    if NUM_DOMAINS > 1 {
        let d = now.wrapping_add(domain_time(s));
        if d < next {
            next = d;
        }
    }
    let rlq = Tcb(node_get(s, s.cur_cpu(), node::RELEASE_HEAD));
    if !rlq.is_null() {
        let t = ready_time(s, rlq);
        if t < next {
            next = t;
        }
    }
    let prec = a.us_to_ticks(1);
    let mut deadline = next.wrapping_sub(prec);
    // l4h 0003: deadline timers are armed for the deadline itself, so they
    // never fire early; a due one sets a deadline in the past.
    let td = crate::timer::earliest(s);
    if td != 0 && td < deadline {
        deadline = td;
    }
    // l4h 0006: keep an earlier deadline that is still pending.
    let c = s.cur_cpu();
    let armed = node_get(s, c, node::ARMED);
    if armed > now && armed <= deadline {
        return;
    }
    node_set(s, c, node::ARMED, deadline);
    a.set_deadline(deadline);
}

/// seL4 `commitTime`.
pub fn commit_time<S: Store, A: Arch>(s: &mut S, a: &A) {
    let sc = cur_sc(s);
    if sporadic::sc_active(s, sc) && sc != idle_sc(s) {
        let c = consumed(s);
        if c > 0 {
            if sporadic::is_round_robin(s, sc) {
                let hi = sc.refill_head(s);
                let ti = sc.refill_tail(s);
                let h = sporadic::get(s, sc, hi);
                sporadic::put(s, sc, hi, sporadic::Refill { time: h.time, amount: h.amount.wrapping_sub(c) });
                let t = sporadic::get(s, sc, ti);
                sporadic::put(s, sc, ti, sporadic::Refill { time: t.time, amount: t.amount.wrapping_add(c) });
            } else {
                sporadic::budget_check(s, a, c);
            }
        }
        let used = sc.consumed(s).wrapping_add(c);
        sc.set_consumed(s, used);
    }
    set_consumed(s, 0);
}

/// seL4 `updateTimestamp`.
pub fn update_timestamp<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let prev = cur_time(s);
    let now = a.now();
    let c = s.cur_cpu();
    node_set(s, c, node::CUR_TIME, now);
    let used = now.wrapping_sub(prev);
    let total = consumed(s).wrapping_add(used);
    set_consumed(s, total);
    if NUM_DOMAINS > 1 {
        let dt = domain_time(s);
        // Saturating: a wrapped sum would make `dt - used` underflow.
        if used.saturating_add(sporadic::min_budget(a)) >= dt {
            ks_set(s, ks::DOMAIN_TIME, 0);
        } else {
            ks_set(s, ks::DOMAIN_TIME, dt - used);
        }
    }
}

pub fn is_cur_domain_expired<S: Store>(s: &S) -> bool {
    NUM_DOMAINS > 1 && domain_time(s) == 0
}

fn check_domain_time<S: Store>(s: &mut S) {
    if is_cur_domain_expired(s) {
        set_reprogram(s);
        reschedule_required(s);
    }
}

/// seL4 `endTimeslice`.
pub fn end_timeslice<S: Store, A: Arch>(s: &mut S, a: &mut A, can_timeout_fault: bool) {
    let sc = cur_sc(s);
    let ct = cur_thread(s);
    let rr = sporadic::is_round_robin(s, sc);
    let valid = ct.state(s) != TS_RUNNING_VM && faults::valid_timeout_handler(s, ct);
    if can_timeout_fault && !rr && valid {
        let badge = sc.badge(s);
        faults::handle_timeout(s, a, ct, crate::error::Fault::Timeout { badge });
    } else if sporadic::ready(s, sc) && sporadic::sufficient(s, a, sc, 0) {
        append(s, ct);
    } else {
        postpone(s, sc);
    }
}

/// seL4 `chargeBudget`.
pub fn charge_budget<S: Store, A: Arch>(s: &mut S, a: &mut A, used: u64, can_timeout_fault: bool) {
    let sc = cur_sc(s);
    if sc != idle_sc(s) {
        if sporadic::is_round_robin(s, sc) {
            let hi = sc.refill_head(s);
            let ti = sc.refill_tail(s);
            let h = sporadic::get(s, sc, hi);
            let t = sporadic::get(s, sc, ti);
            sporadic::put(s, sc, hi, sporadic::Refill { time: h.time, amount: h.amount.wrapping_add(t.amount) });
            sporadic::put(s, sc, ti, sporadic::Refill { time: t.time, amount: 0 });
        } else {
            sporadic::budget_check(s, a, used);
        }
        let total = sc.consumed(s).wrapping_add(used);
        sc.set_consumed(s, total);
    }
    set_consumed(s, 0);
    let ct = cur_thread(s);
    if is_schedulable(s, ct) {
        end_timeslice(s, a, can_timeout_fault);
        reschedule_required(s);
        set_reprogram(s);
    }
}

/// seL4 `checkBudget`.
pub fn check_budget<S: Store, A: Arch>(s: &mut S, a: &mut A) -> bool {
    let sc = cur_sc(s);
    let c = consumed(s);
    if sporadic::sufficient(s, a, sc, c) {
        return !is_cur_domain_expired(s);
    }
    charge_budget(s, a, c, true);
    false
}

/// seL4 `checkBudgetRestart`.
#[inline(always)]
pub fn check_budget_restart<S: Store, A: Arch>(s: &mut S, a: &mut A) -> bool {
    let r = check_budget(s, a);
    let ct = cur_thread(s);
    if !r && is_runnable(s, ct) {
        set_thread_state(s, ct, TS_RESTART);
    }
    r
}

/// seL4 `awaken`: move released threads from the release queue.
#[inline(always)]
pub fn awaken<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    crate::timer::fire(s, a);
    let mut fuel: u64 = WALK_FUEL;
    while fuel > 0 {
        fuel -= 1;
        let h = Tcb(node_get(s, s.cur_cpu(), node::RELEASE_HEAD));
        if h.is_null() || !sporadic::ready(s, Sc(h.sc(s))) {
            return;
        }
        release_remove(s, h);
        possible_switch_to(s, h);
    }
}

fn next_domain<S: Store>(s: &mut S) {
    let mut idx = ks_get(s, ks::DOM_SCHED_IDX).wrapping_add(1);
    if idx >= crate::layout::NUM_DOMAIN_SCHEDULES || dom_sched_duration(s, idx) == 0 {
        idx = ks_get(s, ks::DOM_SCHED_START);
    }
    ks_set(s, ks::DOM_SCHED_IDX, idx);
    set_reprogram(s);
    ks_set(s, ks::WORK_UNITS, 0);
    let d = dom_sched_domain(s, idx);
    let t = dom_sched_duration(s, idx);
    ks_set(s, ks::CUR_DOMAIN, d);
    ks_set(s, ks::DOMAIN_TIME, t);
}

pub fn dom_sched_domain<S: Store>(s: &S, i: u64) -> u64 {
    ks_get(s, ks::DOM_SCHEDULE.wrapping_add(i.wrapping_mul(16)))
}

pub fn dom_sched_duration<S: Store>(s: &S, i: u64) -> u64 {
    ks_get(s, ks::DOM_SCHEDULE.wrapping_add(i.wrapping_mul(16)).wrapping_add(8))
}

pub fn set_dom_sched<S: Store>(s: &mut S, i: u64, dom: u64, duration: u64) {
    ks_set(s, ks::DOM_SCHEDULE.wrapping_add(i.wrapping_mul(16)), dom);
    ks_set(s, ks::DOM_SCHEDULE.wrapping_add(i.wrapping_mul(16)).wrapping_add(8), duration);
}

#[inline(always)]
fn switch_to_thread<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    crate::vspace::set_vm_root(s, a, t);
    dequeue(s, t);
    set_cur_thread(s, t);
}

pub fn switch_to_idle_thread<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let idle = idle_thread(s);
    crate::vspace::set_kernel_vm_root(s, a);
    set_cur_thread(s, idle);
}

#[inline(always)]
fn choose_thread<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let dom = if NUM_DOMAINS > 1 { cur_domain(s) } else { 0 };
    let cpu = s.cur_cpu();
    if node_get(s, cpu, l1_off(bitmap_dom(dom))) != 0 {
        let prio = highest_prio(s, dom);
        let t = q_get(s, cpu, rq_head_off(dom, prio)).head;
        switch_to_thread(s, a, t);
    } else {
        switch_to_idle_thread(s, a);
    }
}

#[inline(always)]
fn schedule_choose_new_thread<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    if domain_time(s) == 0 {
        next_domain(s);
    }
    choose_thread(s, a);
}

#[inline(always)]
fn switch_sched_context<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let ct = cur_thread(s);
    let tsc = Sc(ct.sc(s));
    if cur_sc(s) != tsc {
        set_reprogram(s);
        if sporadic::sc_constant_bandwidth(s, tsc) {
            sporadic::unblock_check(s, tsc);
        }
    }
    if node_get(s, s.cur_cpu(), node::REPROGRAM) != 0 {
        commit_time(s, a);
    }
    let c = s.cur_cpu();
    node_set(s, c, node::CUR_SC, tsc.0);
}

/// seL4 `schedule`.
pub fn schedule<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    awaken(s, a);
    check_domain_time(s);
    let act = action(s);
    if act != ACTION_RESUME_CURRENT {
        let ct = cur_thread(s);
        let was_runnable = is_schedulable(s, ct);
        if was_runnable {
            enqueue(s, ct);
        }
        if act == ACTION_CHOOSE_NEW {
            schedule_choose_new_thread(s, a);
        } else {
            let cand = Tcb(act);
            let ct = cur_thread(s);
            // (An if, not `||`: see ioport::decode.)
            let fastfail = if ct == idle_thread(s) || cand.prio(s) < ct.prio(s) { true } else { false };
            if fastfail && !is_highest_prio(s, cur_domain(s), cand.prio(s)) {
                enqueue(s, cand);
                set_action(s, ACTION_CHOOSE_NEW);
                schedule_choose_new_thread(s, a);
            } else if was_runnable && cand.prio(s) == ct.prio(s) {
                append(s, cand);
                set_action(s, ACTION_CHOOSE_NEW);
                schedule_choose_new_thread(s, a);
            } else {
                switch_to_thread(s, a, cand);
            }
        }
    }
    set_action(s, ACTION_RESUME_CURRENT);
    switch_sched_context(s, a);
    let c = s.cur_cpu();
    if node_get(s, c, node::REPROGRAM) != 0 {
        set_next_interrupt(s, a);
        node_set(s, c, node::REPROGRAM, 0);
    }
    crate::smp::send_pending(s, a);
}

/// seL4 `activateThread`.
#[inline(always)]
pub fn activate_thread<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let ct = cur_thread(s);
    if ct.yield_to(s) != 0 {
        schedcontext::complete_yield_to(s, a, ct);
    }
    let st = ct.state(s);
    if st == TS_RESTART {
        let pc = ct.reg(s, crate::layout::reg::FAULT_IP);
        ct.set_reg(s, crate::layout::reg::NEXT_IP, pc);
        set_thread_state(s, ct, TS_RUNNING);
    }
}

/// seL4 `setDomain`.
pub fn set_domain<S: Store>(s: &mut S, t: Tcb, dom: u64) {
    dequeue(s, t);
    t.set_domain(s, dom);
    if is_schedulable(s, t) {
        enqueue(s, t);
    }
    if t == cur_thread(s) {
        reschedule_required(s);
    }
}

/// seL4 `setPriority` (MCS).
pub fn set_priority<S: Store>(s: &mut S, t: Tcb, prio: u64) {
    let st = t.state(s);
    if st == TS_RUNNING || st == TS_RESTART || st == TS_RUNNING_VM {
        if queued(s, t) || t == cur_thread(s) {
            dequeue(s, t);
            t.set_prio(s, prio);
            enqueue(s, t);
            reschedule_required(s);
        } else {
            t.set_prio(s, prio);
        }
    } else if st == TS_BLOCKED_ON_RECV || st == TS_BLOCKED_ON_SEND {
        t.set_prio(s, prio);
        crate::endpoint::reorder_ep(s, t.block_obj(s), t);
    } else if st == TS_BLOCKED_ON_NTFN {
        t.set_prio(s, prio);
        crate::notification::reorder_ntfn(s, t.block_obj(s), t);
    } else {
        t.set_prio(s, prio);
    }
}

/// seL4 `preemptionPoint` (MCS).
pub fn preemption_point<S: Store, A: Arch>(s: &mut S, a: &mut A) -> KResult<()> {
    let w = ks_get(s, ks::WORK_UNITS).wrapping_add(1);
    ks_set(s, ks::WORK_UNITS, w);
    if w >= MAX_WORK_UNITS_PER_PREEMPTION {
        ks_set(s, ks::WORK_UNITS, 0);
        update_timestamp(s, a);
        let sc = cur_sc(s);
        let c = consumed(s);
        let ok = sporadic::sc_active(s, sc) && sporadic::sufficient(s, a, sc, c);
        if !ok || is_cur_domain_expired(s) || a.irq_pending() {
            return Err(Exc::Preempted);
        }
    }
    Ok(())
}

/// seL4 `suspend` (MCS).
pub fn suspend<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    crate::ipc::cancel_ipc(s, a, t);
    if t.state(s) == TS_RUNNING {
        let ip = t.reg(s, crate::layout::reg::NEXT_IP);
        t.set_reg(s, crate::layout::reg::FAULT_IP, ip);
    }
    dequeue(s, t);
    release_remove(s, t);
    schedcontext::cancel_yield_to(s, t);
    set_thread_state(s, t, TS_INACTIVE);
}

/// seL4 `restart` (MCS).
pub fn restart<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    if is_stopped(s, t) {
        crate::ipc::cancel_ipc(s, a, t);
        set_thread_state(s, t, TS_RESTART);
        let sc = Sc(t.sc(s));
        if sporadic::sc_sporadic(s, sc) && sc != cur_sc(s) {
            sporadic::unblock_check(s, sc);
        }
        schedcontext::resume(s, a, sc);
        if is_schedulable(s, t) {
            possible_switch_to(s, t);
        }
    }
}
