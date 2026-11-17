//! FL4 transaction runtime: the serial gate (trusted, sim-tested).
//!
//! A quiet multi-core machine can take the existing serial gate and execute
//! an entry directly. Two contenders may queue behind an existing serial
//! ticket; more contention backs off these probes and entries run concurrently
//! as transactions (fl4-store's `tx`). An irrevocable entry, or one that
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
/// Bounded direct execution remains useful with a short ticket queue;
/// deeper queues defer to concurrent transactions.
const PROBE_SUCCESSORS: u64 = 2;

// Written only by its CPU. Padding keeps backoff updates off other CPUs'
// cache lines. These relaxed atomics are policy, not synchronization, and
// go through Mem so the simulator observes every runtime access.
#[repr(align(64))]
struct Policy {
    seen: AtomicU64,
    retry: AtomicU64,
}

// Read on every SMP entry; keep it off the ticket/owner cache line.
#[repr(align(64))]
struct Contention(AtomicU64);

pub struct SerialGate {
    /// Changed when a probe loses or a transaction waits for the gate.
    contention: Contention,
    policy: [Policy; MAX_CPUS],
    next: AtomicU64,
    serving: AtomicU64,
    /// 0: open; 1: closed, transactions may still be draining;
    /// 2: closed and the serving ticket has excluded transaction bodies.
    /// A successor that acquires `serving` can inherit state 2 while the
    /// gate remains closed. A failed opportunistic scan leaves state 1.
    closed: AtomicU64,
    /// Cores running a transaction (0 or 1). Its store and the gate
    /// holder's store of `closed` are SeqCst, followed by a load of the
    /// other: a Dekker handshake, which needs the store-load order that
    /// x86 gives only to locked stores.
    active: [AtomicU64; MAX_CPUS],
    /// Core holding the gate, or u64::MAX.
    owner: AtomicU64,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate {
            contention: Contention(AtomicU64::new(0)),
            policy: [const {
                Policy {
                    seen: AtomicU64::new(0),
                    retry: AtomicU64::new(0),
                }
            }; MAX_CPUS],
            next: AtomicU64::new(0),
            serving: AtomicU64::new(0),
            closed: AtomicU64::new(0),
            active: [const { AtomicU64::new(0) }; MAX_CPUS],
            owner: AtomicU64::new(u64::MAX),
        }
    }

    /// Start a transaction on core `cpu`: wait while the gate is closed.
    pub fn enter_tx<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let a = &self.active[cpu as usize];
        let mut notified = false;
        loop {
            while m.a_load(&self.closed, Ordering::Acquire) != 0 {
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
            if m.a_load(&self.closed, Ordering::SeqCst) == 0 {
                return;
            }
            m.a_store(a, 0, Ordering::Release);
        }
    }

    /// The transaction on `cpu` has committed or given up.
    pub fn leave_tx<M: Mem>(&self, m: &M, cpu: u64) {
        m.a_store(&self.active[cpu as usize], 0, Ordering::Release);
    }

    /// Opportunistically reserve a serial ticket, allowing at most two
    /// queued successors. A new contention generation sends the next entry
    /// through STM, with no extra cooldown. Successors service IPIs while waiting.
    /// The caller must not have an active transaction, as for `acquire`.
    ///
    /// The CAS reserves the next ticket only if the queue is empty or has
    /// at most two tickets. After that ticket is served, closing the gate and
    /// checking every active flag use the same SeqCst handshake as
    /// `acquire`/`enter_tx`, unless the predecessor passes an already closed
    /// and drained gate through the release/acquire of `serving`:
    /// either the probe sees the transaction or it sees the closed gate.
    /// A failed scan releases its ticket before returning; it never runs
    /// an entry, waits for a transaction, or changes the version clock.
    pub fn opportunistic_acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) -> bool {
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
        let ticket = m.a_load(&self.serving, Ordering::Acquire);
        let next = m.a_load(&self.next, Ordering::Relaxed);
        let queued = next != ticket;
        if (next.wrapping_sub(ticket) > PROBE_SUCCESSORS)
            || m.a_cas(
                &self.next,
                next,
                next.wrapping_add(1),
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_err()
        {
            m.a_add(&self.contention.0, 1, Ordering::Relaxed);
            return false;
        }
        if queued {
            while m.a_load(&self.serving, Ordering::Acquire) != next {
                wait();
                core::hint::spin_loop();
            }
        }
        if m.a_load(&self.closed, Ordering::Relaxed) != 2 {
            m.a_store(&self.closed, 1, Ordering::SeqCst);
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
            m.a_store(&self.closed, 2, Ordering::Relaxed);
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
        true
    }

    /// Take the gate for core `cpu`: wait for earlier serial entries, then
    /// inherit their exclusion or close and drain the gate. Observing the
    /// predecessor's `serving` release orders the quiescence certificate.
    pub fn acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let ticket = m.a_add(&self.next, 1, Ordering::Relaxed);
        while m.a_load(&self.serving, Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        if m.a_load(&self.closed, Ordering::Relaxed) != 2 {
            m.a_store(&self.closed, 1, Ordering::SeqCst);
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
            m.a_store(&self.closed, 2, Ordering::Relaxed);
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
    }

    pub fn release<M: Mem>(&self, m: &M) {
        m.a_store(&self.owner, u64::MAX, Ordering::Relaxed);
        let s = m.a_load(&self.serving, Ordering::Relaxed);
        let next = s.wrapping_add(1);
        // Keep the gate closed if another serial entry is waiting.
        if m.a_load(&self.next, Ordering::Relaxed) == next {
            m.a_store(&self.closed, 0, Ordering::Release);
        }
        m.a_store(&self.serving, next, Ordering::Release);
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
    fn holding_gate(&self);
    fn count(&self, _what: Count) {}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Count {
    Commit,
    Abort,
    Serial,
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

fn attempts<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> (bool, bool) {
    use fl4_store::tx;
    let cpu = env.cpu();
    let max_attempts = if env.prefer_serial() { 0 } else { TX_ATTEMPTS };
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
    if max_attempts != 0 && gate.opportunistic_acquire(env.mem(), cpu, wait) {
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
        gate.leave_tx(env.mem(), cpu);
        env.finish_effects(ok);
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
        assert!(!gate.opportunistic_acquire(&Atomics, 0, || panic!("unexpected wait")));
        assert_eq!(gate.owner(), u64::MAX);
        // A failed probe must give its ticket back and reopen the gate.
        gate.enter_tx(&Atomics, 2, || panic!("probe stranded the gate"));
        gate.leave_tx(&Atomics, 1);
        gate.leave_tx(&Atomics, 2);
        // Even now that it is empty, contenders get a window for STM.
        assert!(!gate.opportunistic_acquire(&Atomics, 0, || panic!("unexpected wait")));
        assert!(!gate.opportunistic_acquire(&Atomics, 1, || panic!("unexpected wait")));
        let recovered = (0..1024).any(|_| gate.opportunistic_acquire(&Atomics, 0, || panic!("unexpected wait")));
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
            successor_gate.opportunistic_acquire(&Atomics, 2, thread::yield_now)
        });
        let m = QueueDuringScan { gate: Arc::clone(&gate), start: tx, fired: AtomicBool::new(false) };
        assert!(!gate.opportunistic_acquire(&m, 0, || panic!("first ticket")));
        assert!(!successor.join().unwrap(), "a failed scan does not establish exclusion");
        assert_eq!(gate.owner(), u64::MAX);
        gate.leave_tx(&Atomics, 1);
        gate.enter_tx(&Atomics, 3, || panic!("failed probes stranded the gate"));
        gate.leave_tx(&Atomics, 3);
    }

    #[test]
    fn queued_probe_preserves_ticket_order_and_services_calls_across_wraparound() {
        use std::sync::{mpsc, Arc, Mutex};
        use std::thread;
        let gate = Arc::new(SerialGate::new());
        gate.next.store(u64::MAX - 1, Ordering::Relaxed);
        gate.serving.store(u64::MAX - 1, Ordering::Relaxed);
        // A mandatory entry is served before the opportunistic successor.
        gate.acquire(&Atomics, 0, || panic!("empty gate"));
        let order = Arc::new(Mutex::new(std::vec::Vec::new()));
        let (tx, rx) = mpsc::channel();
        let mut workers = std::vec::Vec::new();
        for cpu in 1..=PROBE_SUCCESSORS {
            let gate = Arc::clone(&gate);
            let order = Arc::clone(&order);
            let tx = tx.clone();
            workers.push(thread::spawn(move || {
                let mut notified = false;
                assert!(gate.opportunistic_acquire(&Atomics, cpu, || {
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
        assert!(!gate.opportunistic_acquire(&Atomics, 3, || panic!("full queue")));
        assert_eq!(gate.next.load(Ordering::Relaxed), 1);
        gate.release(&Atomics);
        for worker in workers { worker.join().unwrap(); }
        assert_eq!(*order.lock().unwrap(), [1, 2]);
        assert_eq!(gate.serving.load(Ordering::Acquire), 1);
        gate.enter_tx(&Atomics, 3, || panic!("successor stranded the gate"));
        gate.leave_tx(&Atomics, 3);
    }
}
