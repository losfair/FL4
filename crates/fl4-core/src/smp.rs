//! Cross-core operations (seL4 kernel/smp, with SMP_COND_STATEMENT paths).
//! On one core they reduce to seL4's uniprocessor behaviour.

use crate::layout::node;
use crate::machine::{Arch, Store};
use crate::obj::{node_get, node_set, Tcb};
use crate::sched;

/// seL4 `migrateTCB`: move a thread to the core of its new SC. Its FPU
/// state may be live in the old core's registers (seL4 `Arch_migrateTCB`).
/// The per-core debug list is keyed by affinity, so the thread moves from
/// the old core's list to the new one's; otherwise deleting it later would
/// leave the old core's `DEBUG_TCBS` pointing at freed memory.
pub fn migrate_tcb<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, cpu: u64) {
    if t.affinity(s) != cpu {
        crate::objects::debug_remove(s, t);
        a.fpu_flush(t.0);
        a.fpu_release(t.0);
        t.set_affinity(s, cpu);
        crate::objects::debug_append(s, t);
    }
}

/// seL4 `remoteTCBStall`: a thread running on another core is stopped
/// there before its state changes.
/// The stalled core is left idle with the thread back in its ready queue;
/// it is asked to reschedule once this entry is done (seL4 leaves it to the
/// core's next interrupt).
pub fn remote_tcb_stall<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb) {
    let cpu = t.affinity(s);
    if cpu != s.cur_cpu() && node_get(s, cpu, node::CUR_THREAD) == t.0 {
        a.remote_stall(cpu);
        remote_reschedule(s, a, cpu);
    }
}

/// The stalled core's side of `remote_tcb_stall` (seL4
/// `ipiStallCoreCallback`): runs on that core, on behalf of the core that
/// holds the serial gate.
pub fn stall<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let ct = sched::cur_thread(s);
    if ct != sched::idle_thread(s) {
        // The gate holder may delete or donate this SC as soon as the
        // stall is acknowledged. Settle its time while it is still live.
        sched::update_timestamp(s, a);
        sched::check_budget(s, a);
        sched::commit_time(s, a);
        if ct.state(s) == sched::TS_RUNNING {
            sched::set_thread_state(s, ct, sched::TS_RESTART);
        }
        if sched::is_schedulable(s, ct) {
            sched::enqueue(s, ct);
        }
        sched::switch_to_idle_thread(s, a);
        let cpu = s.cur_cpu();
        let idle_sc = sched::idle_sc(s);
        node_set(s, cpu, node::CUR_SC, idle_sc.0);
        node_set(s, cpu, node::CONSUMED, 0);
        sched::set_reprogram(s);
        sched::set_action(s, sched::ACTION_RESUME_CURRENT);
    }
}

/// Ask `cpu` to reschedule (and reprogram its timer) at the end of this
/// kernel entry.
pub fn remote_reschedule<S: Store, A: Arch>(s: &mut S, a: &mut A, cpu: u64) {
    let _ = a;
    if cpu != s.cur_cpu() {
        let c = s.cur_cpu();
        let m = node_get(s, c, node::IPI_PENDING) | (1u64 << (cpu & 63));
        node_set(s, c, node::IPI_PENDING, m);
    }
}

/// seL4 `remoteQueueUpdate`: `t` was queued on another core; that core
/// must reschedule if it is idle, runs a lower priority, or must reprogram
/// its timer.
#[inline(always)]
pub fn remote_queue_update<S: Store>(s: &mut S, t: Tcb) {
    let cpu = t.affinity(s);
    if cpu == s.cur_cpu() || t.domain(s) != sched::cur_domain(s) {
        return;
    }
    let target = Tcb(node_get(s, cpu, node::CUR_THREAD));
    let idle = node_get(s, cpu, node::IDLE_THREAD);
    if target.0 == idle || t.prio(s) > target.prio(s) || node_get(s, cpu, node::REPROGRAM) != 0 {
        let c = s.cur_cpu();
        let m = node_get(s, c, node::IPI_PENDING) | (1u64 << (cpu & 63));
        node_set(s, c, node::IPI_PENDING, m);
    }
}

/// Send the reschedule IPIs this entry asked for.
pub fn send_pending<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let c = s.cur_cpu();
    let m = node_get(s, c, node::IPI_PENDING);
    if m != 0 {
        node_set(s, c, node::IPI_PENDING, 0);
        a.send_reschedule(m);
    }
}

arch_items!("smp.rs");
