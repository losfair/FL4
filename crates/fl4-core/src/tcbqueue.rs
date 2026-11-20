//! TCB queues (seL4 tcb_queue_t). Ready queues and the release queue link
//! through `sched_next`/`sched_prev`; endpoint and notification queues
//! through `ep_next`/`ep_prev`, as in seL4. Operations take and return the
//! queue by value; the caller stores it back.

use crate::layout::WALK_FUEL;
use crate::machine::Store;
use crate::obj::Tcb;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Queue {
    pub head: Tcb,
    pub end: Tcb,
}

/// Which pair of TCB fields links the queue.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Link {
    Sched,
    Ep,
}

fn next<S: Store>(s: &S, l: Link, t: Tcb) -> u64 {
    match l {
        Link::Sched => t.sched_next(s),
        Link::Ep => t.ep_next(s),
    }
}

fn prev<S: Store>(s: &S, l: Link, t: Tcb) -> u64 {
    match l {
        Link::Sched => t.sched_prev(s),
        Link::Ep => t.ep_prev(s),
    }
}

fn set_next<S: Store>(s: &mut S, l: Link, t: Tcb, v: u64) {
    match l {
        Link::Sched => t.set_sched_next(s, v),
        Link::Ep => t.set_ep_next(s, v),
    }
}

fn set_prev<S: Store>(s: &mut S, l: Link, t: Tcb, v: u64) {
    match l {
        Link::Sched => t.set_sched_prev(s, v),
        Link::Ep => t.set_ep_prev(s, v),
    }
}

/// The TCB after `t` in a queue linked by `l`.
pub fn next_of<S: Store>(s: &S, l: Link, t: Tcb) -> Tcb {
    Tcb(next(s, l, t))
}

impl Queue {
    pub fn empty() -> Queue {
        Queue { head: Tcb(0), end: Tcb(0) }
    }
    pub fn is_empty(self) -> bool {
        self.head.is_null()
    }
}

pub fn prepend<S: Store>(s: &mut S, l: Link, q: Queue, t: Tcb) -> Queue {
    if q.is_empty() {
        set_next(s, l, t, 0);
        set_prev(s, l, t, 0);
        Queue { head: t, end: t }
    } else {
        set_next(s, l, t, q.head.0);
        set_prev(s, l, t, 0);
        set_prev(s, l, q.head, t.0);
        Queue { head: t, end: q.end }
    }
}

pub fn append<S: Store>(s: &mut S, l: Link, q: Queue, t: Tcb) -> Queue {
    if q.is_empty() {
        set_next(s, l, t, 0);
        set_prev(s, l, t, 0);
        Queue { head: t, end: t }
    } else {
        set_next(s, l, q.end, t.0);
        set_prev(s, l, t, q.end.0);
        set_next(s, l, t, 0);
        Queue { head: q.head, end: t }
    }
}

pub fn remove<S: Store>(s: &mut S, l: Link, q: Queue, t: Tcb) -> Queue {
    let before = Tcb(prev(s, l, t));
    let after = Tcb(next(s, l, t));
    let r = if q.head == t && q.end == t {
        Queue::empty()
    } else if q.head == t {
        set_prev(s, l, after, 0);
        Queue { head: after, end: q.end }
    } else if q.end == t {
        set_next(s, l, before, 0);
        Queue { head: q.head, end: before }
    } else {
        set_next(s, l, before, after.0);
        set_prev(s, l, after, before.0);
        q
    };
    set_next(s, l, t, 0);
    set_prev(s, l, t, 0);
    r
}

/// `tcb_queue_insert`: put `t` immediately before `after`, which is not the
/// head.
pub fn insert_before<S: Store>(s: &mut S, l: Link, t: Tcb, after: Tcb) {
    let before = Tcb(prev(s, l, after));
    set_prev(s, l, after, t.0);
    set_next(s, l, t, after.0);
    set_prev(s, l, t, before.0);
    set_next(s, l, before, t.0);
}

/// `tcb_queue_insert_after`: put `t` immediately after `before`, which is
/// not the end.
pub fn insert_after<S: Store>(s: &mut S, l: Link, t: Tcb, before: Tcb) {
    let after = Tcb(next(s, l, before));
    set_prev(s, l, t, before.0);
    set_next(s, l, t, after.0);
    set_prev(s, l, after, t.0);
    set_next(s, l, before, t.0);
}

/// seL4 MCS `tcbAppend`: insert in priority order (FIFO among equals).
#[inline(always)]
pub fn append_by_prio<S: Store>(s: &mut S, l: Link, q: Queue, t: Tcb) -> Queue {
    let p = t.prio(s);
    if q.is_empty() || p > q.head.prio(s) {
        prepend(s, l, q, t)
    } else if q.end.prio(s) >= p {
        append(s, l, q, t)
    } else {
        let mut before = q.end;
        let mut fuel: u64 = WALK_FUEL;
        while !before.is_null() && p > before.prio(s) && fuel > 0 {
            fuel -= 1;
            before = Tcb(prev(s, l, before));
        }
        insert_after(s, l, t, before);
        q
    }
}
