//! Scheduling contexts and SchedControl (seL4 object/schedcontext.c,
//! object/schedcontrol.c).

use crate::capability::Cap;
use crate::error::{illegal, invalid_cap, range, truncated, KResult};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{Ntfn, Reply, Sc, Slot, Tcb};
use crate::sched;
use crate::sporadic::{self, MIN_REFILLS};
use fl4_abi::label;

/// seL4 `schedContext_resume`.
pub fn resume<S: Store, A: Arch>(s: &mut S, a: &mut A, sc: Sc) {
    if sc.is_null() {
        return;
    }
    let t = Tcb(sc.tcb(s));
    if !t.is_null() && sched::is_schedulable(s, t) && !(sporadic::ready(s, sc) && sporadic::sufficient(s, a, sc, 0)) {
        sched::postpone(s, sc);
    }
}

/// seL4 `schedContext_bindTCB`.
pub fn bind_tcb<S: Store, A: Arch>(s: &mut S, a: &mut A, sc: Sc, t: Tcb) {
    t.set_sc(s, sc.0);
    sc.set_tcb(s, t.0);
    crate::smp::migrate_tcb(s, a, t, sc.cpu(s));
    if sporadic::sc_sporadic(s, sc) && sporadic::sc_active(s, sc) && sc != sched::cur_sc(s) {
        sporadic::unblock_check(s, sc);
    }
    resume(s, a, sc);
    if sched::is_schedulable(s, t) {
        sched::enqueue(s, t);
        sched::reschedule_required(s);
    }
}

/// seL4 `schedContext_unbindTCB`.
pub fn unbind_tcb<S: Store>(s: &mut S, sc: Sc) {
    let t = Tcb(sc.tcb(s));
    if t.is_null() {
        return;
    }
    if t == sched::cur_thread(s) {
        sched::reschedule_required(s);
    }
    sched::dequeue(s, t);
    sched::release_remove(s, t);
    t.set_sc(s, 0);
    sc.set_tcb(s, 0);
}

/// seL4 `schedContext_unbindAllTCBs`: the thread is stalled first if it
/// runs on another core.
pub fn unbind_all_tcbs<S: Store, A: Arch>(s: &mut S, a: &mut A, sc: Sc) {
    if sc.tcb(s) != 0 {
        crate::smp::remote_tcb_stall(s, a, Tcb(sc.tcb(s)));
        unbind_tcb(s, sc);
    }
}

/// seL4 `schedContext_donate`.
pub fn donate<S: Store, A: Arch>(s: &mut S, a: &mut A, sc: Sc, to: Tcb) {
    let from = Tcb(sc.tcb(s));
    if !from.is_null() {
        crate::smp::remote_tcb_stall(s, a, from);
        sched::dequeue(s, from);
        sched::release_remove(s, from);
        from.set_sc(s, 0);
        if from == sched::cur_thread(s) || from.0 == sched::action(s) {
            sched::reschedule_required(s);
        }
    }
    sc.set_tcb(s, to.0);
    to.set_sc(s, sc.0);
    crate::smp::migrate_tcb(s, a, to, sc.cpu(s));
}

pub fn bind_ntfn<S: Store>(s: &mut S, sc: Sc, n: Ntfn) {
    n.set_sc(s, sc.0);
    sc.set_ntfn(s, n.0);
}

pub fn unbind_ntfn<S: Store>(s: &mut S, sc: Sc) {
    if !sc.is_null() && sc.ntfn(s) != 0 {
        Ntfn(sc.ntfn(s)).set_sc(s, 0);
        sc.set_ntfn(s, 0);
    }
}

pub fn maybe_unbind_ntfn<S: Store>(s: &mut S, n: Ntfn) {
    let sc = Sc(n.sc(s));
    if !sc.is_null() {
        unbind_ntfn(s, sc);
    }
}

pub fn unbind_reply<S: Store>(s: &mut S, sc: Sc) {
    if !sc.is_null() && sc.reply(s) != 0 {
        let r = Reply(sc.reply(s));
        r.set_next(s, 0, false);
        sc.set_reply(s, 0);
    }
}

/// seL4 `schedContext_updateConsumed`: consumed time in microseconds.
pub fn update_consumed<S: Store, A: Arch>(s: &mut S, a: &A, sc: Sc) -> u64 {
    let c = sc.consumed(s);
    let max = u64::MAX;
    if c >= max {
        sc.set_consumed(s, c - max);
        a.ticks_to_us(max)
    } else {
        sc.set_consumed(s, 0);
        a.ticks_to_us(c)
    }
}

fn set_consumed<S: Store, A: Arch>(s: &mut S, a: &A, sc: Sc, t: Tcb, write_msg: bool) {
    let c = update_consumed(s, a, sc);
    if write_msg {
        let buf = msg::lookup_ipc_buffer(s, true, t);
        t.set_reg(s, crate::layout::reg::BADGE, 0);
        let len = msg::set_mr(s, t, buf, 0, c);
        msg::set_msg_info(s, t, MessageInfo::new(0, 0, 0, len));
    }
}

pub fn cancel_yield_to<S: Store>(s: &mut S, t: Tcb) {
    if !t.is_null() && t.yield_to(s) != 0 {
        Sc(t.yield_to(s)).set_yield_from(s, 0);
        t.set_yield_to(s, 0);
    }
}

/// seL4 `schedContext_completeYieldTo`.
pub fn complete_yield_to<S: Store, A: Arch>(s: &mut S, a: &mut A, yielder: Tcb) {
    if !yielder.is_null() && yielder.yield_to(s) != 0 {
        let sc = Sc(yielder.yield_to(s));
        set_consumed(s, a, sc, yielder, true);
        cancel_yield_to(s, yielder);
    }
}

fn extra_cap<S: Store>(s: &S, extra: &[Slot; 3], i: usize) -> Option<Cap> {
    if i >= 3 || extra[i].is_null() {
        None
    } else {
        Some(extra[i].cap(s))
    }
}

fn yield_to<S: Store, A: Arch>(s: &mut S, a: &mut A, sc: Sc, call: bool) {
    let yf = Tcb(sc.yield_from(s));
    if !yf.is_null() {
        complete_yield_to(s, a, yf);
    }
    resume(s, a, sc);
    let ct = sched::cur_thread(s);
    if !yield_switches(s, sc, ct) {
        set_consumed(s, a, sc, ct, call);
        sched::set_thread_state(s, ct, sched::TS_RUNNING);
    }
}

/// The scheduling part of `YieldTo`: true if the caller now waits for the
/// SC's thread to run, false if the call returns at once.
fn yield_switches<S: Store>(s: &mut S, sc: Sc, ct: Tcb) -> bool {
    let t = Tcb(sc.tcb(s));
    if !sched::is_schedulable(s, t) {
        return false;
    }
    if sc.cpu(s) != s.cur_cpu() || t.prio(s) < ct.prio(s) {
        sched::dequeue(s, t);
        sched::enqueue(s, t);
        return false;
    }
    ct.set_yield_to(s, sc.0);
    sc.set_yield_from(s, ct.0);
    sched::dequeue(s, t);
    sched::enqueue(s, ct);
    sched::enqueue(s, t);
    sched::reschedule_required(s);
    true
}

/// seL4 `decodeSchedContextInvocation`.
pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, sc: Sc, call: bool, extra: &[Slot; 3]) -> KResult<()> {
    // seL4 maybeStallSC: the bound thread may be running on another core.
    if sc.tcb(s) != 0 {
        crate::smp::remote_tcb_stall(s, a, Tcb(sc.tcb(s)));
    }
    let ct = sched::cur_thread(s);
    if lbl == label::SchedContextConsumed {
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        set_consumed(s, a, sc, ct, call);
        sched::set_thread_state(s, ct, sched::TS_RUNNING);
        Ok(())
    } else if lbl == label::SchedContextBind {
        let cap = match extra_cap(s, extra, 0) {
            Some(c) => c,
            None => return truncated(),
        };
        match cap {
            Cap::Thread { ptr } => {
                let t = Tcb(ptr);
                if sc.tcb(s) != 0 || t.sc(s) != 0 {
                    return illegal();
                }
                if sched::is_blocked(s, t) && !sporadic::sc_released(s, sc) {
                    return illegal();
                }
                // A thread without an SC runs nowhere, except an AArch64
                // guest TCB in `ARMVCPURun`, live on its `RUN_CALLER`'s
                // core: stop it there before `migrate_tcb` flushes its
                // state and changes its affinity.
                #[cfg(feature = "aarch64")]
                crate::smp::remote_tcb_stall(s, a, t);
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                bind_tcb(s, a, sc, t);
                Ok(())
            }
            Cap::Notification { ptr, .. } => {
                let n = Ntfn(ptr);
                if sc.ntfn(s) != 0 || n.sc(s) != 0 {
                    return illegal();
                }
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                bind_ntfn(s, sc, n);
                Ok(())
            }
            _ => invalid_cap(1),
        }
    } else if lbl == label::SchedContextUnbindObject {
        let cap = match extra_cap(s, extra, 0) {
            Some(c) => c,
            None => return truncated(),
        };
        match cap {
            Cap::Thread { ptr } => {
                if sc.tcb(s) != ptr || ptr == ct.0 {
                    return illegal();
                }
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                unbind_tcb(s, sc);
                Ok(())
            }
            Cap::Notification { ptr, .. } => {
                if sc.ntfn(s) != ptr {
                    return illegal();
                }
                sched::set_thread_state(s, ct, sched::TS_RESTART);
                unbind_ntfn(s, sc);
                Ok(())
            }
            _ => invalid_cap(1),
        }
    } else if lbl == label::SchedContextUnbind {
        if sc.tcb(s) == ct.0 {
            return illegal();
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        unbind_all_tcbs(s, a, sc);
        unbind_ntfn(s, sc);
        unbind_reply(s, sc);
        Ok(())
    } else if lbl == label::SchedContextYieldTo {
        let t = Tcb(sc.tcb(s));
        if t.is_null() || t == ct || t.prio(s) > ct.mcp(s) || ct.yield_to(s) != 0 {
            return illegal();
        }
        sched::set_thread_state(s, ct, sched::TS_RESTART);
        yield_to(s, a, sc, call);
        Ok(())
    } else {
        illegal()
    }
}

/// seL4 `invokeSchedControl_ConfigureFlags`.
#[allow(clippy::too_many_arguments)]
fn configure_flags<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    target: Sc,
    cpu: u64,
    budget: u64,
    period: u64,
    max_refills: u64,
    badge: u64,
    flags: u64,
) {
    let thread = Tcb(target.tcb(s));
    if !thread.is_null() {
        crate::smp::remote_tcb_stall(s, a, thread);
        sched::release_remove(s, thread);
        sched::dequeue(s, thread);
        if sched::cur_sc(s) == target {
            sched::commit_time(s, a);
        }
    }
    if budget == period {
        sporadic::refill_new(s, target, MIN_REFILLS, budget, 0);
    } else if cpu == target.cpu(s)
        && sporadic::sc_active(s, target)
        && !thread.is_null()
        && sched::is_runnable(s, thread)
    {
        sporadic::refill_update(s, target, period, budget, max_refills);
    } else {
        sporadic::refill_new(s, target, max_refills, budget, period);
    }
    target.set_cpu(s, cpu);
    if !thread.is_null() {
        crate::smp::migrate_tcb(s, a, thread, cpu);
        resume(s, a, target);
        if cpu == s.cur_cpu() {
            if sched::is_runnable(s, thread) && thread != sched::cur_thread(s) {
                sched::possible_switch_to(s, thread);
            }
        } else if sched::is_schedulable(s, thread) {
            // l4h 0013: only a schedulable thread joins a remote ready
            // queue; the remote core still reprograms its timer.
            sched::enqueue(s, thread);
            crate::smp::remote_reschedule(s, a, cpu);
        } else {
            sched::set_reprogram_on(s, cpu);
            crate::smp::remote_reschedule(s, a, cpu);
        }
        if thread == sched::cur_thread(s) {
            sched::reschedule_required(s);
        }
    }
    target.set_badge(s, badge);
    target.set_sporadic(s, if flags & fl4_abi::consts::sc_flag::SPORADIC != 0 { 1 } else { 0 });
}

/// seL4 `decodeSchedControlInvocation`.
pub fn decode_sched_control<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    cpu: u64,
    length: u64,
    buf: u64,
    extra: &[Slot; 3],
) -> KResult<()> {
    if lbl != label::SchedControlConfigureFlags {
        return illegal();
    }
    let ct = sched::cur_thread(s);
    let target_cap = match extra_cap(s, extra, 0) {
        Some(c) => c,
        None => return truncated(),
    };
    if length < 5 {
        return truncated();
    }
    let max_us = sporadic::max_period_us(a);
    let min_us = sporadic::min_budget_us();
    let budget_us = msg::syscall_arg(s, ct, buf, 0);
    if budget_us > max_us {
        return range(min_us, max_us);
    }
    let budget = a.us_to_ticks(budget_us);
    let period_us = msg::syscall_arg(s, ct, buf, 1);
    if period_us > max_us {
        return range(min_us, max_us);
    }
    let period = a.us_to_ticks(period_us);
    let mb = sporadic::min_budget(a);
    if budget < mb || period < mb {
        return range(min_us, max_us);
    }
    if budget > period {
        return range(min_us, period_us);
    }
    let (sc_ptr, size_bits) = match target_cap {
        Cap::SchedContext { ptr, size_bits } => (ptr, size_bits),
        _ => return invalid_cap(1),
    };
    let extra_refills = msg::syscall_arg(s, ct, buf, 2);
    let max_refills = sporadic::refill_absolute_max(size_bits);
    if extra_refills > max_refills.wrapping_sub(MIN_REFILLS) {
        return range(0, max_refills.wrapping_sub(MIN_REFILLS));
    }
    let badge = msg::syscall_arg(s, ct, buf, 3);
    let flags = msg::syscall_arg(s, ct, buf, 4);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    configure_flags(s, a, Sc(sc_ptr), cpu, budget, period, extra_refills.wrapping_add(MIN_REFILLS), badge, flags);
    Ok(())
}
