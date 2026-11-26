//! The local paths of the kernel timer interrupt and of `TCB_SetTimer`
//! (GitHub issue #94, DESIGN.md §7): what they check and what they run.
//! `fl4-sync` wraps them in the gate's handshake and the object locks
//! (`local_timer_irq`, `local_syscall`), as it wraps `fastpath`,
//! `fastpath_vm` and `localinv`.
//!
//! Each local path checks with reads only that the general path's own
//! code, which it then calls, writes nothing but this core's state, threads
//! and scheduling contexts on this core, this core's timer tree and the
//! objects `fl4-sync` has locked for it.
//!
//! # Proof obligations (P2)
//!
//! * Refinement. For `handle_set_timer_local` and `handle_timer_irq_local`
//!   (`local`) and the general entry (`general`: `handle_syscall` for
//!   `SysCall`, `handle_interrupt_entry` for the interrupt), from the same
//!   state, `local s = (true, s')` implies `general s = s'`, and both make
//!   the same `Arch` calls with effects (`now`, `set_deadline`, `ack_irq`,
//!   `set_vspace`, `send_reschedule`: the same values in the same order;
//!   configuration queries such as `kernel_wcet_ticks`, `us_to_ticks` and
//!   `max_us` have no effect, and their order does not matter). By
//!   construction: once the checks pass, `local` runs `general`'s own
//!   fl4-core functions in `general`'s order, and the checks show that
//!   `general` would take no other branch before them (no fault, no
//!   preemption, budget left). For `TCB_SetTimer` the target is given, as
//!   `fl4-sync` found it with the slots of its lookup locked: `general`'s
//!   own lookup (`cspace::lookup_slot`) finds the same thread.
//! * Decline. `local s = (false, s')`: `s'` differs from `s` at most by the
//!   caller's `FAULT_IP` (set to what `general` sets it to first) and by
//!   `sched::update_timestamp`, which `general` begins with; with one
//!   domain two updates leave what the later one alone would. So `general
//!   s'` ends where `general s` does, but for the clock read.
//! * Frame. Beside the gate other cores run local paths only, and every
//!   word a local path writes is in its footprint: this core's node state,
//!   threads with `affinity` this core (and their IPC buffers), scheduling
//!   contexts with `cpu` this core, the objects it locked with the queue
//!   links of the threads queued on them, and the timer links
//!   (`TIMER_LEFT..=TIMER_HEIGHT`) of the threads in this core's timer tree
//!   (fl4-sim's footprint oracle checks exactly this). It rests on the P1
//!   invariant of the timer trees: a nonzero `TIMER_MIN` or `TIMER_ROOT`
//!   of a core is a node of that core's tree, and the `TIMER_LEFT`,
//!   `TIMER_RIGHT` and `TIMER_PARENT` links of a node of a core's tree lead
//!   only to nodes of that tree (or 0), each with `TIMER_HEIGHT >> 8` that
//!   core. The local paths check `TIMER_HEIGHT >> 8` of the nodes they
//!   remove or rearm, but walk links as `crate::timer` does.
//! * Timer ownership. A thread's timer fields, `TIMER_DEADLINE..=
//!   TIMER_HEIGHT`, belong while it is armed to the core whose tree holds
//!   it (`TIMER_HEIGHT >> 8`), and while it is disarmed to its `affinity`.
//!   Under the gate any core may move them; beside it only their owner
//!   writes them, and a local path never moves them to another core: it
//!   arms only threads with `affinity` this core, into this core's tree,
//!   and disarms only threads of this core's tree with `affinity` this
//!   core. `in_core_timer_tree` reads only nodes of this core's tree.

use crate::capability::Cap;
use crate::interrupt;
use crate::layout::{irq as irqn, node, reg, NUM_DOMAINS, TREE_FUEL};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::obj::{node_get, Ntfn, Sc, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE, NTFN_WAITING};
use crate::sched;
use crate::sporadic;
use crate::timer;
use crate::vcpu;
use fl4_abi::consts::tcb_flag;
use fl4_abi::label;
use fl4_abi::syscall as sc;

/// Bytes of the syscall instruction, which `FAULT_IP` points back at (as
/// `syscall::syscall_insn_len!`).
pub const SYSCALL_INSN_LEN: u64 = if cfg!(feature = "aarch64") { 4 } else { 2 };
// `handle_set_timer_local` reads its two arguments from registers.
const _: () = assert!(msg::N_MSG_REGISTERS >= 2);

/// The core whose timer tree holds an armed thread (`timer.rs`).
pub fn core_of<S: Store>(s: &S, t: Tcb) -> u64 {
    t.timer_height(s) >> 8
}

/// How far `in_core_timer_tree` searches: its stack, and the nodes it
/// visits. Beyond them it answers no, and the local path declines.
pub const TREE_STACK: usize = 32;
pub const TREE_VISITS: u64 = 64;

/// Whether `target`, armed for deadline `d`, is a node of core `cpu`'s
/// timer tree. Reads only nodes of that tree, never `target`'s links
/// unless it is one: a thread of this core may be armed in another core's
/// tree (armed there under the gate, or migrated since), whose links that
/// core's local paths write. A binary search for `d`, both ways where a
/// node's deadline equals it (equal deadlines can sit on either side
/// after rotations), within `TREE_STACK` and `TREE_VISITS`.
pub fn in_core_timer_tree<S: Store>(s: &S, cpu: u64, target: Tcb, d: u64) -> bool {
    if target.is_null() {
        return false;
    }
    let root = node_get(s, cpu, node::TIMER_ROOT);
    if node_get(s, cpu, node::TIMER_MIN) == target.0 || root == target.0 {
        return true;
    }
    let mut stack = [0u64; TREE_STACK];
    let mut sp: usize = 0;
    if root != 0 {
        stack[0] = root;
        sp = 1;
    }
    let mut visits: u64 = 0;
    let mut found = false;
    let mut overflow = false;
    while sp > 0 && visits < TREE_VISITS && !found && !overflow {
        visits += 1;
        sp -= 1;
        let cur = Tcb(stack[sp]);
        if cur == target {
            found = true;
        } else {
            let cd = cur.timer_deadline(s);
            if d <= cd {
                let l = cur.timer_left(s);
                if l != 0 {
                    if sp == TREE_STACK {
                        overflow = true;
                    } else {
                        stack[sp] = l;
                        sp += 1;
                    }
                }
            }
            if !overflow && d >= cd {
                let r = cur.timer_right(s);
                if r != 0 {
                    if sp == TREE_STACK {
                        overflow = true;
                    } else {
                        stack[sp] = r;
                        sp += 1;
                    }
                }
            }
        }
    }
    found
}

/// Whether `schedule()`'s `awaken` would release a thread of this core's
/// release queue (at the time `update_timestamp` set).
pub(crate) fn release_due<S: Store>(s: &S, cpu: u64) -> bool {
    let rh = Tcb(node_get(s, cpu, node::RELEASE_HEAD));
    !rh.is_null() && sporadic::ready(s, Sc(rh.sc(s)))
}

/// Whether `awaken`'s `timer::fire` would fire a timer of this core at
/// `now`.
pub(crate) fn timer_due<S: Store>(s: &S, cpu: u64, now: u64) -> bool {
    let tm = Tcb(node_get(s, cpu, node::TIMER_MIN));
    !tm.is_null() && tm.timer_deadline(s) <= now
}

/// This core's scheduler state as the local paths need it at entry: no
/// reschedule pending (`schedule()` keeps or chooses among this core's
/// threads, and `schedule_choose_new_thread` never moves the domain, which
/// `domain_time` does when it is 0), no reschedule IPI owed.
#[cfg(not(feature = "aarch64"))]
pub(crate) fn sched_quiet<S: Store>(s: &S, cpu: u64) -> bool {
    sched::action(s) == sched::ACTION_RESUME_CURRENT
        && sched::domain_time(s) != 0
        && node_get(s, cpu, node::IPI_PENDING) == 0
}

/// AArch64: the same, with both words of `IPI_PENDING`.
#[cfg(feature = "aarch64")]
pub(crate) fn sched_quiet<S: Store>(s: &S, cpu: u64) -> bool {
    sched::action(s) == sched::ACTION_RESUME_CURRENT
        && sched::domain_time(s) != 0
        && crate::smp::none_pending(s, cpu)
}

/// A thread `schedule()` may make current on this core and `exit` run
/// without the gate: this core's, not running a VM (whose VCPU state is
/// the gate's), with no yield to complete (`activate_thread`), on AArch64
/// no VCPU bound (its `exit` loads it; on x86 a thread with a bound VCPU
/// outside `TS_RUNNING_VM` is a native thread to `exit`, `vcpu::check`
/// and `set_vm_root`, as an l4h vCPU thread handling its guest's exit is)
/// and its scheduling context, if any, on this core.
pub(crate) fn may_run_here<S: Store>(s: &S, cpu: u64, t: Tcb) -> bool {
    !t.is_null()
        && t.affinity(s) == cpu
        && t.state(s) != sched::TS_RUNNING_VM
        && t.yield_to(s) == 0
        && (!cfg!(feature = "aarch64") || vcpu::bound(s, t) == 0)
        && (t.sc(s) == 0 || Sc(t.sc(s)).cpu(s) == cpu)
}

/// The current thread `ct` and scheduling context `csc` at entry: both
/// this core's, `ct` running on `csc` (the idle thread on the idle SC).
pub(crate) fn current_ok<S: Store>(s: &S, cpu: u64, ct: Tcb, csc: Sc) -> bool {
    may_run_here(s, cpu, ct)
        && ct.sc(s) == csc.0
        && csc.cpu(s) == cpu
        && (ct == sched::idle_thread(s) || ct.domain(s) == sched::cur_domain(s))
}

// ---- TCB_SetTimer ------------------------------------------------------------

fn cnode_mask(bits: u64) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << (bits & 63)).wrapping_sub(1)
    }
}

/// One level of `cspace::resolve_address_bits`, which reads no slot: the
/// slot that CNode cap `node_cap` resolves `cptr` to with `bits_left` bits
/// left, and the bits left after it; None where `resolve_address_bits`
/// fails at this level (not a CNode, a CNode resolving no bits, a guard or
/// depth mismatch). The caller reads (`fl4-sync`: locks, then reads) the
/// slot, and goes on from its cap if bits are left and it is a CNode.
pub fn cspace_step(node_cap: Cap, cptr: u64, bits_left: u64) -> Option<(Slot, u64)> {
    let (ptr, radix, guard_size, guard) = match node_cap {
        Cap::CNode { ptr, radix, guard_size, guard } => (ptr, radix, guard_size, guard),
        _ => return None,
    };
    let level = radix.wrapping_add(guard_size);
    if level == 0 {
        return None;
    }
    let shift = bits_left.wrapping_sub(guard_size) & 63;
    let g = (cptr >> shift) & cnode_mask(guard_size);
    if guard_size > bits_left || g != guard || level > bits_left {
        return None;
    }
    let offset = (cptr >> ((bits_left - level) & 63)) & cnode_mask(radix);
    Some((Slot::index(ptr, offset), bits_left - level))
}

/// `target`'s timer is this core's to move (Timer ownership): `target` is
/// on this core and disarmed, or armed in this core's tree. On AArch64
/// `tcb::decode` begins with `remote_tcb_stall`, which also stalls the
/// core running a VCPU bound to `target`: none may be bound.
fn set_timer_target_ok<S: Store>(s: &S, cpu: u64, target: Tcb) -> bool {
    if target.affinity(s) != cpu || (cfg!(feature = "aarch64") && vcpu::bound(s, target) != 0) {
        return false;
    }
    let d = target.timer_deadline(s);
    d == 0 || (in_core_timer_tree(s, cpu, target, d) && core_of(s, target) == cpu)
}

/// `handle_syscall` for a `TCB_SetTimer` invocation (`SysCall`) of the
/// current thread `t` on `target`, the thread its capability register
/// names (`fl4-sync` `local_set_timer` found it, and holds the locks of
/// the slots that lookup read, so the general path's lookup finds it too),
/// beside the serial gate: when `target` is this core's, `t` keeps running
/// and nothing becomes due, the general path is `handle_invocation`
/// through `tcb::decode` to `timer::insert`, its reply, and a `schedule()`
/// that keeps `t`. Returns false otherwise, having written only `FAULT_IP`
/// and the timestamp, which the general path repeats (Decline).
pub fn handle_set_timer_local<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64, target: Tcb) -> bool {
    let t = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    let info = msg::msg_info(s, t);
    // A thread with trapSyscalls faults (`syscall`); extra caps are looked
    // up, which may fault; fewer than two words are an error reply.
    if NUM_DOMAINS != 1
        || number != sc::SysCall
        || t.flags(s) & tcb_flag::TRAP_SYSCALLS != 0
        || info.label != label::TCBSetTimer
        || info.extra_caps != 0
        || info.length < 2
    {
        return false;
    }
    let csc = sched::cur_sc(s);
    // `t` stays schedulable and current: `restart_caller` and the reply
    // leave the action as it is (`schedule_tcb`).
    if !set_timer_target_ok(s, cpu, target)
        || !current_ok(s, cpu, t, csc)
        || t.state(s) != sched::TS_RUNNING
        || !sched::is_schedulable(s, t)
        || !sched_quiet(s, cpu)
    {
        return false;
    }
    // As `syscall` and `budget_ok` begin.
    let next = t.reg(s, reg::NEXT_IP);
    t.set_reg(s, reg::FAULT_IP, next.wrapping_sub(SYSCALL_INSN_LEN));
    sched::update_timestamp(s, a);
    let now = sched::cur_time(s);
    // `tcb::decode`'s two arguments, both in message registers
    // (`msg::N_MSG_REGISTERS`), so not from the IPC buffer.
    let deadline = msg::syscall_arg(s, t, 0, 0);
    let badge = msg::syscall_arg(s, t, 0, 1);
    // `budget_ok` charges nothing; `awaken` fires no timer (the new
    // deadline neither) and releases no thread.
    if !sporadic::sufficient(s, a, csc, sched::consumed(s))
        || timer_due(s, cpu, now)
        || release_due(s, cpu)
        || (deadline != 0 && deadline <= now)
    {
        return false;
    }
    // `handle_invocation`: `tcb::decode` (`remote_tcb_stall` stalls
    // nothing: `target` is this core's), its TCBSetTimer case, the reply.
    sched::set_thread_state(s, t, sched::TS_RESTART);
    timer::insert(s, target, deadline, badge);
    msg::reply_success_empty(s, t);
    sched::set_thread_state(s, t, sched::TS_RUNNING);
    // `finish`.
    sched::schedule(s, a);
    sched::activate_thread(s, a);
    vcpu::check(s, a, sched::cur_thread(s));
    true
}

// ---- the kernel timer interrupt ----------------------------------------------

/// Most objects a timer interrupt's local path locks: a notification, and
/// for a signal that wakes its thread from `Recv`, the endpoint and the
/// reply object.
pub const MAX_TIMER_LOCKS: usize = 3;

/// What a timer interrupt's local path will look at, found with reads
/// before it locks anything (`plan_timer_irq`), and found again, equal,
/// once it holds the locks (`handle_timer_irq_local`).
#[derive(Clone, Copy)]
pub struct TimerIrqPlan {
    /// The earliest armed thread, `TIMER_MIN`, if it is this core's (its
    /// `affinity`, in this core's tree): the one this interrupt may fire.
    /// 0 otherwise.
    pub tm: u64,
    /// `tm`'s bound notification, which its timer signals, or 0.
    pub ntfn: u64,
    /// For an idle `ntfn` whose bound thread, `tm`, waits in `Recv`: that
    /// thread, the endpoint it waits on and its reply object (or 0), which
    /// `cancel_ipc` writes when the signal wakes it.
    pub waiter: u64,
    pub ep: u64,
    pub reply: u64,
    /// The objects to lock, as (address, bytes): `ntfn` (64), `ep` (16),
    /// `reply` (32); the first `n`.
    pub objects: [(u64, u64); MAX_TIMER_LOCKS],
    pub n: usize,
}

pub(crate) fn plan_objects<S: Store>(s: &S) -> TimerIrqPlan {
    let cpu = s.cur_cpu();
    let mut p = TimerIrqPlan { tm: 0, ntfn: 0, waiter: 0, ep: 0, reply: 0, objects: [(0, 0); MAX_TIMER_LOCKS], n: 0 };
    let tm = Tcb(node_get(s, cpu, node::TIMER_MIN));
    if tm.is_null() || tm.affinity(s) != cpu || core_of(s, tm) != cpu {
        return p;
    }
    p.tm = tm.0;
    let n = tm.bound_ntfn(s);
    if n == 0 {
        return p;
    }
    p.ntfn = n;
    p.objects[0] = (n, 64);
    p.n = 1;
    let nt = Ntfn(n);
    if nt.state(s) != NTFN_IDLE || nt.bound_tcb(s) != tm.0 || tm.state(s) != sched::TS_BLOCKED_ON_RECV {
        return p;
    }
    let ep = tm.block_obj(s);
    if ep == 0 {
        return p;
    }
    p.waiter = tm.0;
    p.ep = ep;
    p.objects[1] = (ep, 16);
    p.n = 2;
    let r = tm.reply_obj(s);
    if r != 0 {
        p.reply = r;
        p.objects[2] = (r, 32);
        p.n = 3;
    }
    p
}

pub(crate) fn same_plan(x: &TimerIrqPlan, y: &TimerIrqPlan) -> bool {
    x.tm == y.tm && x.ntfn == y.ntfn && x.waiter == y.waiter && x.ep == y.ep && x.reply == y.reply && x.n == y.n
}

/// The plan of a local path for interrupt `irq`, a kernel timer interrupt
/// (`IRQ_TIMER`), with reads only; None if it has none.
pub fn plan_timer_irq<S: Store>(s: &S, irq: u64) -> Option<TimerIrqPlan> {
    if NUM_DOMAINS != 1 || irq > irqn::MAX || interrupt::irq_state(s, irq) != interrupt::IRQ_TIMER {
        return None;
    }
    Some(plan_objects(s))
}

/// The head of this core's highest nonempty ready queue, which
/// `choose_thread` takes, may run here (or there is none).
fn top_ok<S: Store>(s: &S, cpu: u64) -> bool {
    if node_get(s, cpu, node::L1_BITMAP) == 0 {
        return true;
    }
    let prio = sched::highest_prio(s, sched::cur_domain(s));
    let top = Tcb(node_get(s, cpu, node::READY_QUEUES.wrapping_add(prio.wrapping_mul(16))));
    may_run_here(s, cpu, top)
}

/// A budget expiry that `charge_budget` ends with the current thread `ct`
/// appended to its ready queue, its round-robin SC `csc` refilled
/// (`end_timeslice`: ready and sufficient, so neither a timeout fault nor
/// `postpone`), and that `choose_thread` then takes again: no other thread
/// of this core is ready at its priority or above.
pub(crate) fn round_robin_ok<S: Store, A: Arch>(s: &S, a: &A, cpu: u64, ct: Tcb, csc: Sc, now: u64) -> bool {
    if csc == sched::idle_sc(s) || !sporadic::is_round_robin(s, csc) || !sched::is_schedulable(s, ct) || sched::queued(s, ct) {
        return false;
    }
    let hi = csc.refill_head(s);
    let ti = csc.refill_tail(s);
    if hi == ti {
        return false;
    }
    let h = sporadic::get(s, csc, hi);
    let t = sporadic::get(s, csc, ti);
    if h.time > now || h.amount.wrapping_add(t.amount) < sporadic::min_budget(a) {
        return false;
    }
    node_get(s, cpu, node::L1_BITMAP) == 0 || sched::highest_prio(s, sched::cur_domain(s)) < ct.prio(s)
}

/// `send_signal` makes `w` (not the current thread `ct`) runnable from a
/// wait on notification `n`: `possible_switch_to` may choose it, or
/// `schedule()` the head of this core's ready queue, and no scheduling
/// context is donated (`maybe_donate_sched_context`).
fn wake_ok<S: Store>(s: &S, cpu: u64, ct: Tcb, w: Tcb, n: Ntfn) -> bool {
    w != ct
        && may_run_here(s, cpu, w)
        && w.domain(s) == sched::cur_domain(s)
        && !sched::queued(s, w)
        && !(w.sc(s) == 0 && n.sc(s) != 0)
        && top_ok(s, cpu)
}

/// The due timer `p.tm` is the only one due, and `send_signal` of its
/// bound notification (locked, with what `p` names) writes only what the
/// local path may write: it ORs the badge into an active notification,
/// makes an idle one active, or wakes a thread of this core that may then
/// run here (Frame).
pub(crate) fn fire_ok<S: Store>(s: &S, cpu: u64, ct: Tcb, p: &TimerIrqPlan, now: u64) -> bool {
    if p.tm == 0 {
        return false;
    }
    let tm = Tcb(p.tm);
    // `timer::remove` makes the successor `TIMER_MIN`; `fire` stops there.
    let r = Tcb(tm.timer_right(s));
    let mut next = Tcb(tm.timer_parent(s));
    if !r.is_null() {
        next = r;
        let mut fuel: u64 = TREE_FUEL;
        while next.timer_left(s) != 0 && fuel > 0 {
            fuel -= 1;
            next = Tcb(next.timer_left(s));
        }
    }
    if !next.is_null() && next.timer_deadline(s) <= now {
        return false;
    }
    if p.ntfn == 0 {
        return true;
    }
    let n = Ntfn(p.ntfn);
    let st = n.state(s);
    if st == NTFN_ACTIVE {
        true
    } else if st == NTFN_IDLE {
        let b = n.bound_tcb(s);
        if b == 0 {
            return true;
        }
        if b != tm.0 {
            return false;
        }
        let bs = tm.state(s);
        if bs == sched::TS_RUNNING_VM {
            // `vcpu::report` or `kick_guest`: the gate's.
            false
        } else if bs == sched::TS_BLOCKED_ON_RECV {
            p.waiter == tm.0 && p.ep != 0 && wake_ok(s, cpu, ct, tm, n)
        } else {
            true
        }
    } else if st == NTFN_WAITING {
        wake_ok(s, cpu, ct, Tcb(n.head(s)), n)
    } else {
        false
    }
}

/// `handle_interrupt_entry` for interrupt `irq`, the kernel timer, beside
/// the serial gate (`fl4-sync` `local_timer_irq`), holding the locks of `p`,
/// which `plan_timer_irq` returned: when it charges a round-robin budget
/// and keeps the current thread, fires the one due timer of a thread of
/// this core (signalling its bound notification), or does neither (a
/// timer interrupt for the budget or a timer already dealt with), and
/// `schedule()` stays on this core. Returns false otherwise, having
/// written only the timestamp, which the general path repeats (Decline).
pub fn handle_timer_irq_local<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64, p: &TimerIrqPlan) -> bool {
    let cpu = s.cur_cpu();
    if NUM_DOMAINS != 1 || irq > irqn::MAX || interrupt::irq_state(s, irq) != interrupt::IRQ_TIMER {
        return false;
    }
    // What is locked is what the plan locked, and as it found it.
    if !same_plan(&plan_objects(s), p) {
        return false;
    }
    let ct = sched::cur_thread(s);
    let csc = sched::cur_sc(s);
    if !current_ok(s, cpu, ct, csc) || !sched_quiet(s, cpu) {
        return false;
    }
    // As `handle_interrupt_entry` begins.
    sched::update_timestamp(s, a);
    let now = sched::cur_time(s);
    if release_due(s, cpu) {
        return false;
    }
    let expired = !sporadic::sufficient(s, a, csc, sched::consumed(s));
    let due = timer_due(s, cpu, now);
    let ok = if expired && due {
        false
    } else if expired {
        round_robin_ok(s, a, cpu, ct, csc, now)
    } else if due {
        fire_ok(s, cpu, ct, p, now)
    } else {
        true
    };
    if !ok {
        return false;
    }
    let _ = sched::check_budget(s, a);
    interrupt::handle_interrupt(s, a, irq);
    // `finish`.
    sched::schedule(s, a);
    sched::activate_thread(s, a);
    vcpu::check(s, a, sched::cur_thread(s));
    true
}
