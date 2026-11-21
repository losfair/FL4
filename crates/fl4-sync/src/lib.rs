//! FL4 transaction runtime: the serial gate (trusted, sim-tested).
//!
//! A quiet multi-core machine can take the existing serial gate and execute
//! an entry directly. Contenders may queue behind an existing serial ticket,
//! up to a bound the environment sets (`EntryEnv::probe_successors`); more
//! contention backs off these probes and entries run concurrently as
//! transactions (fl4-store's `tx`). An irrevocable entry, or one that
//! exhausts its retries, waits for the gate
//! in ticket order. Both forms close the gate and exclude all transactions
//! before touching memory directly (DESIGN.md §7). Every blocking wait
//! services remote calls, as seL4's CLH lock does.
#![no_std]

use core::sync::atomic::{AtomicU64, Ordering};
use fl4_store::tx::Mem;

// The transaction state and hardware per-core storage both support this
// many participants. Do not scan flags for cores the runtime cannot run.
pub const MAX_CPUS: usize = fl4_store::tx::MAX_CPUS;
/// Extra entries to defer after observing a new contention generation.
/// The observation itself already sends one entry through STM.
const PROBE_BACKOFF: u64 = 0;
/// Queued successors a probe may join (`EntryEnv::probe_successors`);
/// deeper queues defer to concurrent transactions. The simulator keeps
/// this short bound, so transactions keep overlapping serial entries.
pub const PROBE_SUCCESSORS: u64 = 2;
/// A bound no queue of other cores reaches: direct execution unless the
/// gate is closed for an irrevocable entry. On x86_64 a transaction costs
/// several times the same entry run directly (DESIGN.md §7), so waiting
/// for the gate behind other cores' short entries is the faster choice.
pub const DEEP_PROBE_SUCCESSORS: u64 = MAX_CPUS as u64 - 1;

// Written only by its CPU. Padding keeps backoff updates off other CPUs'
// cache lines. These relaxed atomics are policy, not synchronization, and
// go through Mem so the simulator observes every runtime access.
#[repr(align(64))]
struct Policy {
    seen: AtomicU64,
    retry: AtomicU64,
    /// Whether this core's last syscall outside the gate ran its fast path.
    local_hit: AtomicU64,
}

// Read on every SMP entry; keep it off the ticket/owner cache line.
#[repr(align(64))]
struct Contention(AtomicU64);

/// A value alone on its cache line.
#[repr(align(64))]
struct Line<T>(T);

impl<T> core::ops::Deref for Line<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.0
    }
}

#[repr(C, align(64))]
struct Head {
    serving: AtomicU64,
    /// 0: open; 1: closed, transactions may still be draining;
    /// 2: closed and the serving ticket has excluded transaction bodies.
    /// A successor that acquires `serving` can inherit state 2 while the
    /// gate remains closed. A failed opportunistic scan leaves state 1.
    closed: AtomicU64,
}

/// The ticket counters and the gate state, on separate cache lines: probes
/// take tickets with a CAS on `next` while queued successors spin on
/// `serving`, and the holder writes `owner` twice per entry.
pub struct SerialGate {
    /// Changed when a probe loses or a transaction waits for the gate.
    contention: Contention,
    policy: [Policy; MAX_CPUS],
    next: Line<AtomicU64>,
    /// `serving` and `closed`: a successor reads both as its turn comes.
    head: Head,

    /// Cores running a transaction (0 or 1). Its store and the gate
    /// holder's store of `closed` are SeqCst, followed by a load of the
    /// other: a Dekker handshake, which needs the store-load order that
    /// x86 gives only to locked stores.
    active: Line<[AtomicU64; MAX_CPUS]>,
    /// Core holding the gate, or u64::MAX.
    owner: Line<AtomicU64>,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate {
            contention: Contention(AtomicU64::new(0)),
            policy: [const {
                Policy {
                    seen: AtomicU64::new(0),
                    retry: AtomicU64::new(0),
                    local_hit: AtomicU64::new(1),
                }
            }; MAX_CPUS],
            next: Line(AtomicU64::new(0)),
            head: Head { serving: AtomicU64::new(0), closed: AtomicU64::new(0) },
            active: Line([const { AtomicU64::new(0) }; MAX_CPUS]),
            owner: Line(AtomicU64::new(u64::MAX)),
        }
    }

    /// Start a transaction on core `cpu`: wait while the gate is closed.
    pub fn enter_tx<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let a = &self.active[cpu as usize];
        let mut notified = false;
        loop {
            while m.a_load(&self.head.closed, Ordering::Acquire) != 0 {
                // Tell a successful probe to back off at its next entry,
                // so a busy core cannot repeatedly barge ahead of STM.
                if !notified {
                    m.a_add(&self.contention.0, 1, Ordering::Relaxed);
                    notified = true;
                }
                wait();
                core::hint::spin_loop();
            }
            // (Mutation test: `mutant-gate-release` drops the store-load
            // order, which only the store-buffer model can show.)
            let o = if cfg!(feature = "mutant-gate-release") {
                Ordering::Release
            } else {
                Ordering::SeqCst
            };
            m.a_store(a, 1, o);
            if m.a_load(&self.head.closed, Ordering::SeqCst) == 0 {
                return;
            }
            m.a_store(a, 0, Ordering::Release);
        }
    }

    /// `enter_tx` without waiting: false, with nothing changed, while the
    /// gate is closed or closing.
    #[inline(always)]
    pub fn try_enter_tx<M: Mem>(&self, m: &M, cpu: u64) -> bool {
        let a = &self.active[cpu as usize];
        if m.a_load(&self.head.closed, Ordering::Acquire) != 0 {
            return false;
        }
        m.a_store(a, 1, Ordering::SeqCst);
        if m.a_load(&self.head.closed, Ordering::SeqCst) == 0 {
            return true;
        }
        m.a_store(a, 0, Ordering::Release);
        false
    }

    /// The transaction on `cpu` has committed or given up.
    pub fn leave_tx<M: Mem>(&self, m: &M, cpu: u64) {
        m.a_store(&self.active[cpu as usize], 0, Ordering::Release);
    }

    /// Opportunistically reserve a serial ticket, allowing at most
    /// `successors` queued successors. A new contention generation sends the
    /// next entry through STM, with no extra cooldown. Successors service
    /// IPIs while waiting. The caller must not have an active transaction,
    /// as for `acquire`.
    ///
    /// The CAS reserves the next ticket only if the queue is empty or has
    /// at most `successors` tickets; losing it to another prober retries
    /// while that still holds. After that ticket is served, closing the gate and
    /// checking every active flag use the same SeqCst handshake as
    /// `acquire`/`enter_tx`, unless the predecessor passes an already closed
    /// and drained gate through the release/acquire of `serving`:
    /// either the probe sees the transaction or it sees the closed gate.
    /// A failed scan releases its ticket before returning; it never runs
    /// an entry, waits for a transaction, or changes the version clock.
    #[inline(always)]
    pub fn opportunistic_acquire<M: Mem>(&self, m: &M, cpu: u64, successors: u64, mut wait: impl FnMut()) -> bool {
        let p = &self.policy[cpu as usize];
        let generation = m.a_load(&self.contention.0, Ordering::Relaxed);
        if m.a_load(&p.seen, Ordering::Relaxed) != generation {
            m.a_store(&p.seen, generation, Ordering::Relaxed);
            m.a_store(&p.retry, PROBE_BACKOFF, Ordering::Relaxed);
            return false;
        }
        let remaining = m.a_load(&p.retry, Ordering::Relaxed);
        if remaining != 0 {
            m.a_store(&p.retry, remaining - 1, Ordering::Relaxed);
            return false;
        }
        let (next, queued) = loop {
            // `serving` first: the ticket it names was taken, from `next`,
            // before it was served, so `next` read after it is no smaller.
            let ticket = m.a_load(&self.head.serving, Ordering::Acquire);
            let next = m.a_load(&self.next, Ordering::Relaxed);
            if next.wrapping_sub(ticket) > successors {
                m.a_add(&self.contention.0, 1, Ordering::Relaxed);
                return false;
            }
            // Another prober took this ticket: the queue moved, which
            // is progress; try for the next one.
            if m.a_cas(&self.next, next, next.wrapping_add(1), Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                break (next, next != ticket);
            }
        };
        if queued {
            while m.a_load(&self.head.serving, Ordering::Acquire) != next {
                wait();
                core::hint::spin_loop();
            }
        }
        if m.a_load(&self.head.closed, Ordering::Relaxed) != 2 {
            m.a_store(&self.head.closed, 1, Ordering::SeqCst);
            for (c, a) in self.active.iter().enumerate() {
                if c as u64 != cpu
                    && !cfg!(feature = "mutant-gate-no-wait")
                    && m.a_load(a, Ordering::SeqCst) != 0
                {
                    m.a_add(&self.contention.0, 1, Ordering::Relaxed);
                    self.release(m);
                    return false;
                }
            }
            m.a_store(&self.head.closed, 2, Ordering::Relaxed);
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
        true
    }

    /// Take the gate for core `cpu`: wait for earlier serial entries, then
    /// inherit their exclusion or close and drain the gate. Observing the
    /// predecessor's `serving` release orders the quiescence certificate.
    pub fn acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let ticket = m.a_add(&self.next, 1, Ordering::Relaxed);
        while m.a_load(&self.head.serving, Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        if m.a_load(&self.head.closed, Ordering::Relaxed) != 2 {
            m.a_store(&self.head.closed, 1, Ordering::SeqCst);
            for (c, a) in self.active.iter().enumerate() {
                // (Mutation test: `mutant-gate-no-wait` does not wait.)
                if c as u64 == cpu || cfg!(feature = "mutant-gate-no-wait") {
                    continue;
                }
                while m.a_load(a, Ordering::SeqCst) != 0 {
                    wait();
                    core::hint::spin_loop();
                }
            }
            m.a_store(&self.head.closed, 2, Ordering::Relaxed);
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
    }

    pub fn release<M: Mem>(&self, m: &M) {
        m.a_store(&self.owner, u64::MAX, Ordering::Relaxed);
        let s = m.a_load(&self.head.serving, Ordering::Relaxed);
        let next = s.wrapping_add(1);
        // Keep the gate closed if another serial entry is waiting.
        if m.a_load(&self.next, Ordering::Relaxed) == next {
            m.a_store(&self.head.closed, 0, Ordering::Release);
        }
        m.a_store(&self.head.serving, next, Ordering::Release);
    }

    pub fn owner(&self) -> u64 {
        self.owner.load(Ordering::Relaxed)
    }
}

impl Default for SerialGate {
    fn default() -> Self {
        Self::new()
    }
}

/// What a kernel entry needs from its environment: the kernel on hardware,
/// or the simulator.
pub trait EntryEnv {
    type S: fl4_core::machine::Store;
    type A: fl4_core::machine::Arch;
    type M: fl4_store::tx::Mem;
    fn cpu(&self) -> u64;
    /// More than one core runs the kernel.
    fn multi(&self) -> bool;
    /// Skip speculation when the entry is expected to require the gate.
    /// This changes admission policy only: the body still validates the
    /// request, and waits still service stalls and accepted interrupts.
    fn prefer_serial(&self) -> bool {
        false
    }
    /// How many queued successors a probe for the gate may join before the
    /// entry runs as a transaction instead.
    fn probe_successors(&self) -> u64 {
        PROBE_SUCCESSORS
    }
    /// Transaction attempts before the serial gate. With none, entries
    /// queue for the gate, and syscalls may also take `run_syscall`'s
    /// local fast paths, which need that no transaction runs.
    fn tx_attempts(&self) -> u32 {
        TX_ATTEMPTS
    }
    /// The store, inside this core's transaction or direct.
    fn store(&self, tx: bool) -> Self::S;
    fn arch(&self) -> Self::A;
    fn mem(&self) -> &Self::M;
    /// Service a remote call; true if it stalled this core's thread.
    fn service_remote(&self) -> bool;
    /// Arch operations are queued (inside a transaction) or run directly.
    fn set_tx(&self, on: bool);
    /// Run (`committed`) or drop the queued Arch effects.
    fn finish_effects(&self, committed: bool);
    /// The entry has completed (it will not run again).
    #[inline(always)]
    fn entry_done(&self);
    /// An interrupt this entry accepted that the run which took effect did
    /// not handle, now forgotten: an aborted attempt polled it at a
    /// preemption point and the rerun did not reach one, or a stall
    /// cancelled the entry. It is still in service and needs an entry of
    /// its own, or it blocks every interrupt of its priority and below
    /// (GitHub issue #6).
    fn unhandled_irq(&self) -> Option<u64>;
    /// This core now holds the serial gate (released when it leaves the
    /// kernel).
    #[inline(always)]
    fn holding_gate(&self);
    fn count(&self, _what: Count) {}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Count {
    Commit,
    Abort,
    Serial,
    /// A syscall's fast path ran without the gate (`run_syscall`).
    Local,
}

/// Transaction attempts before an entry runs under the serial gate (none
/// with the test-only `serial-gate` feature).
pub const TX_ATTEMPTS: u32 = if cfg!(feature = "serial-gate") { 0 } else { 4 };

/// Run the kernel's part of an entry (DESIGN.md §7): directly on one core;
/// otherwise probe for exclusive access with at most two queued successors,
/// then use transactions on contention, rerun on conflict, and wait for the
/// serial gate if an entry cannot run as a transaction or keeps conflicting.
/// `body` must be repeatable:
/// everything it reads or writes goes through the store and Arch it is
/// given. An interrupt the entry accepted but did not handle in the run
/// that took effect gets an entry of its own afterwards (`unhandled_irq`).
/// Returns false when a stall cancelled a non-interrupt entry before
/// it ran.
#[inline(always)]
pub fn run_entry<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    let (ran, mut serial) = attempts(env, gate, irq, body);
    while let Some(v) = env.unhandled_irq() {
        let irq_body =
            |s: &mut E::S, a: &mut E::A| fl4_core::syscall::handle_interrupt_entry(s, a, v);
        if serial {
            // This core still holds the gate (until it leaves the kernel),
            // so the interrupt's entry runs directly too.
            irq_body(&mut env.store(false), &mut env.arch());
            env.entry_done();
        } else {
            serial = attempts(env, gate, true, irq_body).1;
        }
    }
    ran
}

/// A syscall: on several cores with transactions off (`EntryEnv::
/// tx_attempts`), first try its fast path without the serial gate
/// (`fl4_core::syscall::handle_syscall_local`), then `run_entry`. Returns
/// as `run_entry` does.
///
/// The fast paths write only memory of this core (its scheduler state, and
/// threads and scheduling contexts on it, which they check before writing),
/// the endpoint and reply object involved, and a receiver's IPC buffer.
/// Every other kernel word they read changes only under the gate, and any
/// write other cores' kernel entries make outside the gate is another such
/// fast path. So: the core is active, like a transaction, which the gate
/// drains; and the endpoint and the reply object, which threads on several
/// cores may share, are locked in the version table, unused without
/// transactions. A fast path that cannot take them, or declines, leaves the
/// entry to `run_entry`. (IPC buffers are user memory: a frame shared by
/// threads on two cores is the user's race, as on a single core.)
///
/// `local` runs `local_syscall` on the store it is given, or a faster
/// equivalent of it (the kernel's specialized direct store); `body` returns
/// whether a fast path ran (`fl4_core::syscall::handle_syscall_fast`).
#[inline(always)]
pub fn run_syscall<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    number: i64,
    mut local: impl FnMut(&mut E::S, &mut E::A) -> bool,
    mut body: impl FnMut(&mut E::S, &mut E::A) -> bool,
) -> bool {
    let candidate = local_candidate(&env.store(false), number);
    if !(env.multi() && env.tx_attempts() == 0 && !env.prefer_serial() && candidate != Candidate::No) {
        return run_entry(env, gate, false, |s, a| {
            let _ = body(s, a);
        });
    }
    match local_entry(env, gate, &mut local) {
        Local::Done => return true,
        Local::Stalled => return false,
        Local::Closed | Local::Declined => {}
    }
    // Whether a fast path ran under the gate decides, as one beside it
    // does, whether this core waits for the gate next time. An I/O port
    // access has no fast path under the gate, and one declined beside it
    // (a timer due, the budget spent) would usually run there next time.
    let fast = core::cell::Cell::new(false);
    let ran = run_entry(env, gate, false, |s, a| fast.set(body(s, a)));
    let hit = fast.get() || candidate == Candidate::Port;
    env.mem().a_store(&gate.policy[env.cpu() as usize].local_hit, hit as u64, Ordering::Relaxed);
    ran
}

/// `tx::try_lock_object`. (Mutation test: `mutant-local-no-lock` takes
/// nothing.)
#[inline(always)]
fn lock_object<M: Mem>(m: &M, addr: u64, held: &mut fl4_store::tx::Held) -> bool {
    cfg!(feature = "mutant-local-no-lock") || fl4_store::tx::try_lock_object(m, addr, held)
}

/// A syscall a fast path may take: a trapped one, or ReplyRecv. (Read
/// without the gate: the current thread's flags change only while it is
/// stalled, and `local_syscall` checks again.)
#[inline(always)]
fn local_candidate<S: fl4_core::machine::Store>(s: &S, number: i64) -> Candidate {
    let t = fl4_core::sched::cur_thread(s);
    if number == fl4_abi::syscall::SysReplyRecv || t.flags(s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0 {
        Candidate::Fast
    } else if (number == fl4_abi::syscall::SysCall || number == fl4_abi::syscall::SysSend)
        // An I/O port access by its label alone (a register).
        && fl4_core::ioport::is_port_label(fl4_core::msg::msg_info(s, t).label)
    {
        Candidate::Port
    } else {
        Candidate::No
    }
}

#[derive(PartialEq, Clone, Copy)]
enum Candidate {
    No,
    /// A guest syscall's fault or reply (`fastpath`).
    Fast,
    /// An I/O port access (`handle_ioport_local`).
    Port,
}

/// How long `local_entry` waits for a closed gate to open: some tens of
/// microseconds, several serial entries.
const LOCAL_WAIT_SPINS: u32 = 1024;

enum Local {
    Done,
    Declined,
    /// The gate stayed closed.
    Closed,
    Stalled,
}

#[inline(always)]
fn local_entry<E: EntryEnv>(env: &E, gate: &SerialGate, local: &mut impl FnMut(&mut E::S, &mut E::A) -> bool) -> Local {
    let cpu = env.cpu();
    // While the gate is closed, wait for it to open, servicing remote
    // calls, rather than take a ticket: queued syscalls would keep it closed
    // for each other. But only after a fast path that ran: one that then
    // declined would have waited for the gate twice.
    // The wait is bounded: serial entries queued back to back keep the
    // gate closed (`release`), and this core would wait out of FIFO order,
    // without its interrupts, for as long as they come; after
    // `LOCAL_WAIT_SPINS` it takes a ticket.
    let hit = &gate.policy[cpu as usize].local_hit;
    let mut spins = 0;
    // (Mutation test: `mutant-local-no-active` does not mark the core.)
    while !cfg!(feature = "mutant-local-no-active") && !gate.try_enter_tx(env.mem(), cpu) {
        if env.mem().a_load(hit, Ordering::Relaxed) == 0 || spins == LOCAL_WAIT_SPINS {
            return Local::Closed;
        }
        spins += 1;
        if env.service_remote() {
            // A remote stall took this core's thread: no entry for it now.
            return Local::Stalled;
        }
        core::hint::spin_loop();
    }
    let done = local(&mut env.store(false), &mut env.arch());
    env.mem().a_store(hit, done as u64, Ordering::Relaxed);
    if !cfg!(feature = "mutant-local-no-active") {
        gate.leave_tx(env.mem(), cpu);
    }
    if done {
        env.count(Count::Local);
        env.entry_done();
        Local::Done
    } else {
        Local::Declined
    }
}

/// The fast path of a syscall made outside the gate (`run_syscall`), with
/// its endpoint and reply object locked; true if it ran.
#[inline(always)]
pub fn local_syscall<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(s: &mut S, a: &mut A, m: &M, number: i64) -> bool {
    use fl4_core::capability::Cap;
    use fl4_core::layout::tcb as tl;
    use fl4_core::obj::{Ep, Reply};
    use fl4_store::tx;
    let t = fl4_core::sched::cur_thread(s);
    let mut held = tx::Held::new();
    // The endpoint and reply object the fast path will use, each locked
    // (`tx::try_lock_object`) before the fast path reads them again.
    let mut found = (0, 0);
    let ok = if t.flags(s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0 {
        match t.slot(tl::SLOT_FAULT_HANDLER).cap(s) {
            Cap::Endpoint { ptr, .. } => {
                // (A receiver waiting is the fast path's first condition:
                // without one, decline before touching anything.)
                lock_object(m, ptr, &mut held) && Ep(ptr).state(s) == fl4_core::obj::EP_RECV && {
                    let dest = fl4_core::obj::Tcb(Ep(ptr).head(s));
                    let r = if dest.is_null() { 0 } else { dest.reply_obj(s) };
                    r != 0 && lock_object(m, r, &mut held)
                }
            }
            _ => false,
        }
    } else if number == fl4_abi::syscall::SysReplyRecv {
        match fl4_core::fastpath::reply_caps(s, t) {
            Some((r, ep)) => {
                found = (r, ep);
                lock_object(m, r, &mut held)
                    // reply_remove would write the reply objects next to
                    // it on the call stack, which are not locked.
                    && Reply(r).prev(s) == 0
                    && Reply(r).next(s) == 0
                    && {
                        let u = fl4_core::obj::Tcb(Reply(r).tcb(s));
                        !u.is_null() && u.state(s) == fl4_core::sched::TS_BLOCKED_ON_REPLY
                    }
                    && lock_object(m, ep, &mut held)
            }
            None => false,
        }
    } else {
        // An I/O port access writes only the caller and this core's
        // state: nothing to lock.
        return fl4_core::syscall::handle_ioport_local(s, a, number);
    };
    let done = ok && fl4_core::syscall::handle_syscall_local(s, a, number, found);
    tx::unlock_held(m, &mut held);
    done
}

#[inline(always)]
fn attempts<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> (bool, bool) {
    use fl4_store::tx;
    let cpu = env.cpu();
    let max_attempts = if env.prefer_serial() { 0 } else { env.tx_attempts() };
    let mut a = env.arch();
    if !env.multi() {
        body(&mut env.store(false), &mut a);
        env.entry_done();
        return (true, false);
    }
    let stalled = core::cell::Cell::new(false);
    let wait = || {
        if env.service_remote() {
            stalled.set(true);
        }
    };
    if max_attempts != 0 && gate.opportunistic_acquire(env.mem(), cpu, env.probe_successors(), wait) {
        env.count(Count::Serial);
        env.holding_gate();
        if stalled.get() && !irq {
            return (false, true);
        }
        body(&mut env.store(false), &mut a);
        env.entry_done();
        return (true, true);
    }
    for _ in 0..max_attempts {
        gate.enter_tx(env.mem(), cpu, wait);
        if stalled.get() && !irq {
            gate.leave_tx(env.mem(), cpu);
            return (false, false);
        }
        tx::begin(cpu, env.mem());
        env.set_tx(true);
        let mut s = env.store(true);
        body(&mut s, &mut a);
        env.set_tx(false);
        let ok = tx::commit(cpu, env.mem());
        let serial = tx::needs_serial(cpu);
        tx::end(cpu);
        env.finish_effects(ok);
        // Committed effects may still use objects that a serial entry can
        // delete. Keep its exclusion until those effects have completed.
        gate.leave_tx(env.mem(), cpu);
        if ok {
            env.count(Count::Commit);
            env.entry_done();
            return (true, false);
        }
        env.count(Count::Abort);
        if serial {
            break;
        }
    }
    env.count(Count::Serial);
    gate.acquire(env.mem(), cpu, wait);
    env.holding_gate();
    if stalled.get() && !irq {
        return (false, true);
    }
    body(&mut env.store(false), &mut a);
    env.entry_done();
    (true, true)
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    struct Atomics;
    impl Mem for Atomics {
        fn load(&self, _: u64) -> u64 {
            unreachable!()
        }
        fn store(&self, _: u64, _: u64) {
            unreachable!()
        }
    }

    #[test]
    fn active_transaction_rejects_probe_and_contention_yields_to_stm() {
        let gate = SerialGate::new();
        gate.enter_tx(&Atomics, 1, || panic!("open gate"));
        assert!(!gate.opportunistic_acquire(&Atomics, 0, PROBE_SUCCESSORS, || panic!("unexpected wait")));
        assert_eq!(gate.owner(), u64::MAX);
        // A failed probe must give its ticket back and reopen the gate.
        gate.enter_tx(&Atomics, 2, || panic!("probe stranded the gate"));
        gate.leave_tx(&Atomics, 1);
        gate.leave_tx(&Atomics, 2);
        // Even now that it is empty, contenders get a window for STM.
        assert!(!gate.opportunistic_acquire(&Atomics, 0, PROBE_SUCCESSORS, || panic!("unexpected wait")));
        assert!(!gate.opportunistic_acquire(&Atomics, 1, PROBE_SUCCESSORS, || panic!("unexpected wait")));
        let recovered = (0..1024).any(|_| gate.opportunistic_acquire(&Atomics, 0, PROBE_SUCCESSORS, || panic!("unexpected wait")));
        assert!(
            recovered,
            "uncontended entries must recover the direct path"
        );
        gate.release(&Atomics);
    }

    #[test]
    fn failed_probe_cannot_pass_exclusivity_to_its_queued_successor() {
        use std::sync::{mpsc, Arc};
        use std::sync::atomic::AtomicBool;
        use std::thread;
        struct QueueDuringScan {
            gate: Arc<SerialGate>,
            start: mpsc::Sender<()>,
            fired: AtomicBool,
        }
        impl Mem for QueueDuringScan {
            fn load(&self, _: u64) -> u64 { unreachable!() }
            fn store(&self, _: u64, _: u64) { unreachable!() }
            fn a_load(&self, a: &AtomicU64, o: Ordering) -> u64 {
                if core::ptr::eq(a, &self.gate.active[1]) && !self.fired.swap(true, Ordering::Relaxed) {
                    // Queue another real probe before the current one sees
                    // the active transaction and releases its ticket.
                    self.start.send(()).unwrap();
                    while self.gate.next.load(Ordering::Relaxed) != 2 {
                        thread::yield_now();
                    }
                }
                a.load(o)
            }
        }
        let gate = Arc::new(SerialGate::new());
        gate.enter_tx(&Atomics, 1, || panic!("open gate"));
        let (tx, rx) = mpsc::channel();
        let successor_gate = Arc::clone(&gate);
        let successor = thread::spawn(move || {
            rx.recv().unwrap();
            successor_gate.opportunistic_acquire(&Atomics, 2, PROBE_SUCCESSORS, thread::yield_now)
        });
        let m = QueueDuringScan { gate: Arc::clone(&gate), start: tx, fired: AtomicBool::new(false) };
        assert!(!gate.opportunistic_acquire(&m, 0, PROBE_SUCCESSORS, || panic!("first ticket")));
        assert!(!successor.join().unwrap(), "a failed scan does not establish exclusion");
        assert_eq!(gate.owner(), u64::MAX);
        gate.leave_tx(&Atomics, 1);
        gate.enter_tx(&Atomics, 3, || panic!("failed probes stranded the gate"));
        gate.leave_tx(&Atomics, 3);
    }

    #[test]
    fn queued_probe_preserves_ticket_order_and_services_calls_across_wraparound() {
        queued_probes(PROBE_SUCCESSORS);
    }

    #[test]
    fn deeper_bound_queues_more_probes() {
        queued_probes(6);
    }

    /// `successors` probes queue behind a mandatory entry, are served in
    /// ticket order across the counter's wraparound, and one more is refused.
    fn queued_probes(successors: u64) {
        use std::sync::{mpsc, Arc, Mutex};
        use std::thread;
        let gate = Arc::new(SerialGate::new());
        gate.next.store(u64::MAX - 1, Ordering::Relaxed);
        gate.head.serving.store(u64::MAX - 1, Ordering::Relaxed);
        // A mandatory entry is served before the opportunistic successor.
        gate.acquire(&Atomics, 0, || panic!("empty gate"));
        let order = Arc::new(Mutex::new(std::vec::Vec::new()));
        let (tx, rx) = mpsc::channel();
        let mut workers = std::vec::Vec::new();
        for cpu in 1..=successors {
            let gate = Arc::clone(&gate);
            let order = Arc::clone(&order);
            let tx = tx.clone();
            workers.push(thread::spawn(move || {
                let mut notified = false;
                assert!(gate.opportunistic_acquire(&Atomics, cpu, successors, || {
                    if !notified {
                        tx.send(cpu).unwrap();
                        notified = true;
                    }
                    thread::yield_now();
                }));
                assert!(notified);
                assert_eq!(gate.owner(), cpu);
                order.lock().unwrap().push(cpu);
                gate.release(&Atomics);
            }));
            assert_eq!(rx.recv().unwrap(), cpu);
        }
        assert!(!gate.opportunistic_acquire(&Atomics, successors + 1, successors, || panic!("full queue")));
        assert_eq!(gate.next.load(Ordering::Relaxed), successors - 1);
        gate.release(&Atomics);
        for worker in workers { worker.join().unwrap(); }
        assert_eq!(*order.lock().unwrap(), (1..=successors).collect::<std::vec::Vec<_>>());
        assert_eq!(gate.head.serving.load(Ordering::Acquire), successors - 1);
        gate.enter_tx(&Atomics, successors + 1, || panic!("successor stranded the gate"));
        gate.leave_tx(&Atomics, successors + 1);
    }

    #[derive(Default)]
    struct NoopArch;
    impl fl4_core::machine::Arch for NoopArch {
        fn now(&mut self) -> u64 {
            0
        }
        fn set_deadline(&mut self, _: u64) {}
        fn us_to_ticks(&self, x: u64) -> u64 {
            x
        }
        fn ticks_to_us(&self, x: u64) -> u64 {
            x
        }
        fn max_us(&self) -> u64 {
            u64::MAX
        }
        fn kernel_wcet_ticks(&self) -> u64 {
            1
        }
        fn irq_pending(&mut self) -> bool {
            false
        }
        fn take_pending_irq(&mut self) -> u64 {
            u64::MAX
        }
        fn mask_irq(&mut self, irq: u64, mask: bool) {
            let _ = (irq, mask);
        }
        fn ack_irq(&mut self, _: u64) {}
        fn irq_free(&mut self, irq: u64) {
            let _ = irq;
        }
        fn set_vspace(&mut self, _: u64, _: u64) {}
        fn invalidate_page(&mut self, _: u64, _: u64) {}
        fn invalidate_asid(&mut self, _: u64) {}
        fn invalidate_page_structures(&mut self, _: u64) {}
        fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
            false
        }
        fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
            false
        }
        fn num_ioapics(&self) -> u64 {
            0
        }
        fn ioapic_pins(&self, _: u64) -> u64 {
            0
        }
        fn port_in(&mut self, _: u64, _: u64) -> u64 {
            0
        }
        fn port_out(&mut self, _: u64, _: u64, _: u64) {}
        fn fpu_flush(&mut self, _: u64) {}
        fn fpu_sanitise(&mut self, _: u64) {}
        fn fpu_reload(&mut self, _: u64) {}
        fn fpu_release(&mut self, _: u64) {}
        fn remote_stall(&mut self, _: u64) {}
        fn send_reschedule(&mut self, _: u64) {}
        fn putc(&mut self, _: u64) {}
        fn get_char(&mut self) -> u64 {
            0
        }
        fn halt(&mut self) {}
    }

    // One test owns CPU 0's process-global STM state across both outcomes.
    #[cfg(not(feature = "serial-gate"))]
    #[test]
    fn serial_entries_cannot_overtake_committed_or_discarded_effects() {
        use core::cell::Cell;
        struct Env<'a> {
            gate: &'a SerialGate,
            abort: bool,
            finishes: Cell<u64>,
            held: Cell<bool>,
        }
        impl EntryEnv for Env<'_> {
            type S = fl4_store::PhysStore;
            type A = NoopArch;
            type M = Atomics;
            fn cpu(&self) -> u64 { 0 }
            fn multi(&self) -> bool { true }
            fn store(&self, tx: bool) -> Self::S { fl4_store::PhysStore { frame_masks: (0, 0), ks_base: 0, cpu: 0, tx } }
            fn arch(&self) -> NoopArch { NoopArch }
            fn mem(&self) -> &Atomics { &Atomics }
            fn service_remote(&self) -> bool { false }
            fn set_tx(&self, _: bool) {}
            fn finish_effects(&self, committed: bool) {
                assert_eq!(committed, !self.abort);
                assert!(!fl4_store::tx::active(0));
                // The blocker forced run_entry through STM; remove it now
                // so only unfinished effects can exclude a serial probe.
                self.gate.leave_tx(&Atomics, 1);
                let generation = self.gate.contention.0.load(Ordering::Relaxed);
                self.gate.policy[2].seen.store(generation, Ordering::Relaxed);
                assert!(!self.gate.opportunistic_acquire(&Atomics, 2, PROBE_SUCCESSORS, || panic!("empty ticket queue")),
                    "serial code could delete an object still used by queued effects");
                self.finishes.set(self.finishes.get() + 1);
            }
            fn entry_done(&self) {}
            fn unhandled_irq(&self) -> Option<u64> { None }
            fn holding_gate(&self) { self.held.set(true); }
        }
        for abort in [false, true] {
            let gate = SerialGate::new();
            gate.enter_tx(&Atomics, 1, || panic!("open gate"));
            let env = Env { gate: &gate, abort, finishes: Cell::new(0), held: Cell::new(false) };
            let mut bodies = 0;
            assert!(run_entry(&env, &gate, false, |_, _| {
                bodies += 1;
                if abort && fl4_store::tx::active(0) { fl4_store::tx::doom_serial(0); }
            }));
            assert_eq!(env.finishes.get(), 1);
            assert_eq!(bodies, if abort { 2 } else { 1 });
            if env.held.get() { gate.release(&Atomics); }
            // Exclusion must end after effects finish.
            let generation = gate.contention.0.load(Ordering::Relaxed);
            gate.policy[2].seen.store(generation, Ordering::Relaxed);
            assert!(gate.opportunistic_acquire(&Atomics, 2, PROBE_SUCCESSORS, || panic!("gate stranded")));
            gate.release(&Atomics);
        }
    }

}
