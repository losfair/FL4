//! MCS refills (seL4 kernel/sporadic.c and kernel/sporadic.h). The refill
//! ring lives after the scheduling context's 128-byte header.

use crate::layout::{node, sc as scl, WALK_FUEL};
use crate::machine::{Arch, Store};
use crate::obj::{node_get, node_set, Sc};

pub const MIN_REFILLS: u64 = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Refill {
    pub time: u64,
    pub amount: u64,
}

fn cur_time<S: Store>(s: &S) -> u64 {
    node_get(s, s.cur_cpu(), node::CUR_TIME)
}

/// `MIN_BUDGET`: twice the kernel's WCET (KernelWcetScale is fixed at 1).
pub fn min_budget<A: Arch>(a: &A) -> u64 {
    a.kernel_wcet_ticks().wrapping_mul(2)
}

pub fn min_budget_us() -> u64 {
    2 * 10
}

/// `MAX_PERIOD_US` with KernelStaticMaxPeriodUs = 0.
pub fn max_period_us<A: Arch>(a: &A) -> u64 {
    a.max_us() / 8
}

pub fn max_release_time<A: Arch>(a: &A) -> u64 {
    let p = a.us_to_ticks(max_period_us(a));
    u64::MAX.wrapping_sub(p.wrapping_mul(5))
}

/// Number of refills that fit in a scheduling context of `size_bits`.
pub fn refill_absolute_max(size_bits: u64) -> u64 {
    if size_bits >= 64 {
        return 0;
    }
    let bytes = 1u64 << (size_bits & 63);
    if bytes < scl::REFILLS {
        0
    } else {
        (bytes - scl::REFILLS) / scl::REFILL_SIZE
    }
}

pub fn get<S: Store>(s: &S, sc: Sc, i: u64) -> Refill {
    Refill { time: sc.r_time(s, i), amount: sc.r_amount(s, i) }
}

pub fn put<S: Store>(s: &mut S, sc: Sc, i: u64, r: Refill) {
    sc.set_r_time(s, i, r.time);
    sc.set_r_amount(s, i, r.amount);
}

pub fn head<S: Store>(s: &S, sc: Sc) -> Refill {
    get(s, sc, sc.refill_head(s))
}

pub fn tail<S: Store>(s: &S, sc: Sc) -> Refill {
    get(s, sc, sc.refill_tail(s))
}

fn set_head<S: Store>(s: &mut S, sc: Sc, r: Refill) {
    let h = sc.refill_head(s);
    put(s, sc, h, r)
}

fn set_tail<S: Store>(s: &mut S, sc: Sc, r: Refill) {
    let t = sc.refill_tail(s);
    put(s, sc, t, r)
}

fn next_index<S: Store>(s: &S, sc: Sc, i: u64) -> u64 {
    if i == sc.refill_max(s).wrapping_sub(1) {
        0
    } else {
        i.wrapping_add(1)
    }
}

pub fn size<S: Store>(s: &S, sc: Sc) -> u64 {
    let h = sc.refill_head(s);
    let t = sc.refill_tail(s);
    if h <= t {
        t.wrapping_sub(h).wrapping_add(1)
    } else {
        t.wrapping_add(1).wrapping_add(sc.refill_max(s).wrapping_sub(h))
    }
}

pub fn full<S: Store>(s: &S, sc: Sc) -> bool {
    size(s, sc) == sc.refill_max(s)
}

pub fn single<S: Store>(s: &S, sc: Sc) -> bool {
    sc.refill_head(s) == sc.refill_tail(s)
}

pub fn capacity<S: Store>(s: &S, sc: Sc, usage: u64) -> u64 {
    let amount = head(s, sc).amount;
    if usage > amount {
        0
    } else {
        amount - usage
    }
}

pub fn sufficient<S: Store, A: Arch>(s: &S, a: &A, sc: Sc, usage: u64) -> bool {
    capacity(s, sc, usage) >= min_budget(a)
}

pub fn ready<S: Store>(s: &S, sc: Sc) -> bool {
    head(s, sc).time <= cur_time(s)
}

pub fn sc_active<S: Store>(s: &S, sc: Sc) -> bool {
    sc.refill_max(s) > 0
}

pub fn sc_released<S: Store>(s: &S, sc: Sc) -> bool {
    sc_active(s, sc) && ready(s, sc)
}

pub fn sc_sporadic<S: Store>(s: &S, sc: Sc) -> bool {
    !sc.is_null() && sc.sporadic(s) != 0
}

pub fn sc_constant_bandwidth<S: Store>(s: &S, sc: Sc) -> bool {
    sc.sporadic(s) == 0
}

pub fn is_round_robin<S: Store>(s: &S, sc: Sc) -> bool {
    sc.period(s) == 0
}

fn pop_head<S: Store>(s: &mut S, sc: Sc) -> Refill {
    let r = head(s, sc);
    let h = sc.refill_head(s);
    let n = next_index(s, sc, h);
    sc.set_refill_head(s, n);
    r
}

fn add_tail<S: Store>(s: &mut S, sc: Sc, r: Refill) {
    let t = sc.refill_tail(s);
    let nt = next_index(s, sc, t);
    sc.set_refill_tail(s, nt);
    put(s, sc, nt, r);
}

fn maybe_add_empty_tail<S: Store>(s: &mut S, sc: Sc) {
    if is_round_robin(s, sc) {
        let t = head(s, sc).time;
        add_tail(s, sc, Refill { time: t, amount: 0 });
    }
}

/// seL4 `refill_new`.
pub fn refill_new<S: Store>(s: &mut S, sc: Sc, max_refills: u64, budget: u64, period: u64) {
    sc.set_period(s, period);
    sc.set_refill_head(s, 0);
    sc.set_refill_tail(s, 0);
    sc.set_refill_max(s, max_refills);
    let now = cur_time(s);
    put(s, sc, 0, Refill { time: now, amount: budget });
    maybe_add_empty_tail(s, sc);
}

/// seL4 `refill_update`.
pub fn refill_update<S: Store>(s: &mut S, sc: Sc, new_period: u64, new_budget: u64, new_max_refills: u64) {
    // Move the head refill to index 0 first, as seL4 does by construction.
    let h = head(s, sc);
    put(s, sc, 0, h);
    sc.set_refill_head(s, 0);
    sc.set_refill_tail(s, 0);
    sc.set_refill_max(s, new_max_refills);
    sc.set_period(s, new_period);
    if ready(s, sc) {
        let now = cur_time(s);
        let a = head(s, sc).amount;
        set_head(s, sc, Refill { time: now, amount: a });
    }
    let hd = head(s, sc);
    if hd.amount >= new_budget {
        set_head(s, sc, Refill { time: hd.time, amount: new_budget });
        maybe_add_empty_tail(s, sc);
    } else {
        add_tail(s, sc, Refill { time: hd.time.wrapping_add(new_period), amount: new_budget - hd.amount });
    }
}

fn schedule_used<S: Store>(s: &mut S, sc: Sc, new: Refill) {
    let t = tail(s, sc);
    if t.time.wrapping_add(t.amount) >= new.time {
        set_tail(s, sc, Refill { time: t.time, amount: t.amount.wrapping_add(new.amount) });
    } else if !full(s, sc) {
        add_tail(s, sc, new);
    } else {
        set_tail(s, sc, Refill { time: new.time.wrapping_sub(t.amount), amount: t.amount.wrapping_add(new.amount) });
    }
}

fn head_overlapping<S: Store>(s: &S, sc: Sc) -> bool {
    if single(s, sc) {
        return false;
    }
    let h = head(s, sc);
    let end = h.time.wrapping_add(h.amount);
    let n = next_index(s, sc, sc.refill_head(s));
    get(s, sc, n).time <= end
}

/// seL4 `refill_budget_check`: charge `usage` to the current SC.
pub fn budget_check<S: Store, A: Arch>(s: &mut S, a: &A, usage_in: u64) {
    let sc = Sc(node_get(s, s.cur_cpu(), node::CUR_SC));
    let mrt = max_release_time(a);
    let period = sc.period(s);
    let mut usage = usage_in;
    // handle_overrun: each round removes one refill's worth of usage or
    // moves the head on by a period, so it ends; seL4 has no bound. (A
    // bound of a few rounds once cut a long overrun short, after which
    // the head's amount went below zero: found by P1.)
    let mut fuel: u64 = WALK_FUEL;
    loop {
        let h = head(s, sc);
        // A head with no budget takes nothing off the usage, so the loop
        // would not end. The refill invariants rule it out; a transaction
        // that has been doomed reads zeros until it reaches commit and
        // retries, and must get there (GitHub issue #5).
        if !(h.amount <= usage && h.time < mrt) || h.amount == 0 || fuel == 0 {
            break;
        }
        fuel -= 1;
        if single(s, sc) {
            set_head(s, sc, Refill { time: h.time.wrapping_add(period), amount: h.amount });
        } else {
            let old = pop_head(s, sc);
            schedule_used(s, sc, Refill { time: old.time.wrapping_add(period), amount: old.amount });
        }
        usage = usage.wrapping_sub(h.amount);
    }
    // seL4 asserts here that the head holds more than the usage left,
    // which the loop's exit condition gives whenever h.time < mrt.
    let h = head(s, sc);
    if usage > 0 && h.time < mrt && h.amount > usage {
        let used = Refill { time: h.time.wrapping_add(period), amount: usage };
        set_head(s, sc, Refill { time: h.time.wrapping_add(usage), amount: h.amount.wrapping_sub(usage) });
        schedule_used(s, sc, used);
    }
    let mb = min_budget(a);
    let mut fuel2 = sc.refill_max(s).wrapping_add(2);
    while head(s, sc).amount < mb && !single(s, sc) && fuel2 > 0 {
        fuel2 -= 1;
        let old = pop_head(s, sc);
        let h = head(s, sc);
        set_head(s, sc, Refill { time: h.time.wrapping_sub(old.amount), amount: h.amount.wrapping_add(old.amount) });
    }
}

/// seL4 `refill_unblock_check`.
#[inline(always)]
pub fn unblock_check<S: Store>(s: &mut S, sc: Sc) {
    if is_round_robin(s, sc) {
        return;
    }
    if ready(s, sc) {
        let now = cur_time(s);
        let h = head(s, sc);
        set_head(s, sc, Refill { time: now, amount: h.amount });
        let cpu = s.cur_cpu();
        node_set(s, cpu, node::REPROGRAM, 1);
        let mut fuel = sc.refill_max(s).wrapping_add(1);
        while head_overlapping(s, sc) && fuel > 0 {
            fuel -= 1;
            let old = pop_head(s, sc);
            let h = head(s, sc);
            set_head(s, sc, Refill { time: old.time, amount: h.amount.wrapping_add(old.amount) });
        }
    }
}
