//! FL4 kernel entry runtime (trusted, sim-tested; DESIGN.md §7): the
//! serial gate, and the local paths that run beside it.
//!
//! On one core an entry runs directly. On several, it takes the serial
//! gate, a ticket lock, and runs directly on memory with no other entry
//! running, except local paths: syscalls whose footprint is known (this
//! core's state, objects they lock) run beside the gate on any number of
//! cores. A local path marks its core active; the gate holder closes the
//! gate and waits for active cores to drain (a Dekker handshake). Every
//! blocking wait services remote calls, as seL4's CLH lock does.
#![no_std]

// The mutants (Cargo.toml, DESIGN.md §10) are known-broken runtimes for
// the simulator's mutation testing: a kernel built with one would run
// without the gate's exclusion. Both kernel targets are bare metal
// (x86_64-unknown-none, aarch64-unknown-none-softfloat); the simulator
// is a host program.
#[cfg(all(
    target_os = "none",
    any(
        feature = "mutant-gate-no-wait",
        feature = "mutant-gate-release",
        feature = "mutant-local-no-active",
        feature = "mutant-local-no-lock",
    )
))]
compile_error!("fl4-sync's mutant features are for the host simulator (cargo xtask mutants), never for a kernel");

use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::machine::{Arch, Store};
use fl4_core::{localtimer, localvm};
use fl4_store::lock::{self, Held, Mem};

/// Cores the runtime supports. Do not scan flags for cores it cannot run.
pub const MAX_CPUS: usize = lock::MAX_CPUS;

// Written only by its CPU, off other CPUs' cache lines. A relaxed atomic:
// policy, not synchronization, through Mem so the simulator observes it.
#[repr(align(64))]
struct Policy {
    /// Whether this core's last syscall outside the gate ran its fast path.
    local_hit: AtomicU64,
}

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

/// `serving` and `closed`, each on its own line: queued cores spin on
/// `serving` and every local path reads `closed`, so a handoff while the
/// gate stays closed (`release`) moves only the queued cores' line. On one
/// line, every handoff pulled it back to every core (64 cores on a GCE N4A:
/// getpid 19M ops/s, 24M apart).
#[repr(C)]
struct Head {
    serving: Line<AtomicU64>,
    /// 0: open; 1: closed, local paths may still be draining; 2: closed
    /// and drained. A successor that acquires `serving` inherits state 2
    /// while the gate remains closed.
    closed: Line<AtomicU64>,
}

// `acquire` drains the active flags through a u128 mask.
const _: () = assert!(MAX_CPUS <= 128);

/// The ticket counters and the gate state, on separate cache lines: a core
/// takes a ticket with an add on `next` while queued successors spin on
/// `serving`, and the holder writes `owner` twice per entry.
pub struct SerialGate {
    policy: [Policy; MAX_CPUS],
    next: Line<AtomicU64>,
    /// `serving` and `closed`: a successor reads both as its turn comes.
    head: Head,
    /// Cores running a local path (0 or 1), each on its own cache line:
    /// every local path writes its core's twice. Its store and the gate
    /// holder's store of `closed` are SeqCst, followed by a load of the
    /// other: a Dekker handshake, which needs the store-load order that
    /// x86 gives only to locked stores.
    active: [Line<AtomicU64>; MAX_CPUS],
    /// Core holding the gate, or u64::MAX.
    owner: Line<AtomicU64>,
    /// How many of `active` the gate holder drains (`set_cores`).
    cores: AtomicU64,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate {
            policy: [const { Policy { local_hit: AtomicU64::new(1) } }; MAX_CPUS],
            next: Line(AtomicU64::new(0)),
            head: Head { serving: Line(AtomicU64::new(0)), closed: Line(AtomicU64::new(0)) },
            active: [const { Line(AtomicU64::new(0)) }; MAX_CPUS],
            owner: Line(AtomicU64::new(u64::MAX)),
            cores: AtomicU64::new(MAX_CPUS as u64),
        }
    }

    /// Only cores 0..n will ever run an entry: the gate holder drains
    /// those cores' flags, not all `MAX_CPUS`. Set at boot, before any of
    /// them is started.
    pub fn set_cores(&self, n: usize) {
        assert!(n >= 1 && n <= MAX_CPUS);
        self.cores.store(n as u64, Ordering::Relaxed);
    }

    /// Mark core `cpu` active for a local path: false, with nothing
    /// changed, while the gate is closed or closing.
    #[inline(always)]
    pub fn try_enter_local<M: Mem>(&self, m: &M, cpu: u64) -> bool {
        let a = &*self.active[cpu as usize];
        if m.a_load(&self.head.closed, Ordering::Acquire) != 0 {
            return false;
        }
        // (Mutation test: `mutant-gate-release` drops the store-load
        // order, which only the store-buffer model can show.)
        let o = if cfg!(feature = "mutant-gate-release") { Ordering::Release } else { Ordering::SeqCst };
        m.a_store(a, 1, o);
        if m.a_load(&self.head.closed, Ordering::SeqCst) == 0 {
            return true;
        }
        m.a_store(a, 0, Ordering::Release);
        false
    }

    /// The local path on `cpu` has finished.
    #[inline(always)]
    pub fn leave_local<M: Mem>(&self, m: &M, cpu: u64) {
        m.a_store(&self.active[cpu as usize], 0, Ordering::Release);
    }

    /// Take the gate for core `cpu`: wait for earlier serial entries, then
    /// inherit their exclusion or close the gate and wait for local paths
    /// to drain. Observing the predecessor's `serving` release orders the
    /// exclusion it passes on.
    pub fn acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let ticket = m.a_add(&self.next, 1, Ordering::Relaxed);
        while m.a_load(&self.head.serving, Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        if m.a_load(&self.head.closed, Ordering::Relaxed) != 2 {
            m.a_store(&self.head.closed, 1, Ordering::SeqCst);
            // The store, then every core's flag: one SeqCst fence orders
            // them, and the flags are read with plain loads, whose misses
            // overlap. SeqCst loads would be one after another on AArch64
            // (LDAR), a cache miss each: with 64 cores, microseconds that
            // every serial entry would wait.
            m.fence(Ordering::SeqCst);
            let cores = self.cores.load(Ordering::Relaxed) as usize;
            let mut busy = 0u128;
            for (c, a) in self.active[..cores].iter().enumerate() {
                // (Mutation test: `mutant-gate-no-wait` does not wait.)
                if c as u64 == cpu || cfg!(feature = "mutant-gate-no-wait") {
                    continue;
                }
                if m.a_load(&a.0, Ordering::Relaxed) != 0 {
                    busy |= 1 << c;
                }
            }
            while busy != 0 {
                wait();
                core::hint::spin_loop();
                let mut left = busy;
                while left != 0 {
                    let c = left.trailing_zeros() as usize;
                    left &= left - 1;
                    if m.a_load(&self.active[c].0, Ordering::Relaxed) == 0 {
                        busy &= !(1 << c);
                    }
                }
            }
            // What the drained local paths wrote (their `leave_local`
            // releases) happens before this entry.
            m.fence(Ordering::Acquire);
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
    type M: Mem;
    fn cpu(&self) -> u64;
    /// More than one core runs the kernel.
    fn multi(&self) -> bool;
    /// Direct access to kernel memory.
    fn store(&self) -> Self::S;
    fn arch(&self) -> Self::A;
    fn mem(&self) -> &Self::M;
    /// Service a remote call; true if it stalled this core's thread.
    fn service_remote(&self) -> bool;
    /// This core now holds the serial gate (released when it leaves the
    /// kernel).
    fn holding_gate(&self);
    fn count(&self, _what: Count) {}
    /// The time `local_wait_over` measures from, in the kernel's clock
    /// ticks (read only once a local path finds the gate closed).
    fn now(&self) -> u64 {
        0
    }
    /// Whether `local_entry` has waited long enough for a closed gate to
    /// open: `spins` spins since `start` (`now`). Without a clock, after
    /// `LOCAL_WAIT_SPINS`. A kernel bounds the time instead (`LOCAL_WAIT_US`),
    /// because what a spin costs depends on the CPU: an x86 `pause` takes
    /// tens to over a hundred cycles, an AArch64 `yield` a few.
    fn local_wait_over(&self, spins: u32, _start: u64) -> bool {
        spins >= LOCAL_WAIT_SPINS
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Count {
    Serial,
    /// A local path ran beside the gate (`run_syscall`, `run_vm_fault`,
    /// `run_timer_irq`).
    Local,
}

/// Run the kernel's part of an entry (DESIGN.md §7): directly on one core;
/// otherwise under the serial gate. Returns false when a stall cancelled a
/// non-interrupt entry before it ran (it accepted no interrupt then: it
/// polls for them only in its body).
#[inline(always)]
pub fn run_entry<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    serial(env, gate, irq, &mut body)
}

/// A syscall: on several cores, first try its local path beside the serial
/// gate (`fl4_core::syscall::handle_syscall_local`, `handle_ioport_local`,
/// `handle_invocation_local`, `localtimer::handle_set_timer_local`), then
/// `run_entry`. Returns as `run_entry` does.
///
/// The fast paths write only memory of this core (its scheduler state, its
/// timer tree, and threads and scheduling contexts on it, which they check
/// before writing), the endpoint and reply object involved, and a
/// receiver's IPC buffer. Every other kernel word they read changes only
/// under the gate, and any write other cores' kernel entries make outside
/// the gate is another such local path. So: the core is marked active,
/// which the gate drains; and the endpoint and the reply object, which
/// threads on several cores may share, are locked (`fl4_store::lock`). A local path that cannot take
/// them, or declines, leaves the entry to `run_entry`. (IPC buffers are user memory: a frame shared by
/// threads on two cores is the user's race, as on a single core.)
///
/// `local` runs `local_syscall` on the store it is given; `body` returns
/// whether a fast path ran (`fl4_core::syscall::handle_syscall_fast`).
#[inline(always)]
pub fn run_syscall<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    number: i64,
    mut local: impl FnMut(&mut E::S, &mut E::A) -> bool,
    mut body: impl FnMut(&mut E::S, &mut E::A) -> bool,
) -> bool {
    let candidate = local_candidate(&env.store(), number);
    if !env.multi() || candidate == Candidate::No {
        return run_entry(env, gate, false, |s, a| {
            let _ = body(s, a);
        });
    }
    let res = local_entry(env, gate, &mut local);
    match res {
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
    // An invocation candidate is so by its label alone: one that declined
    // may be no frame cap's (a TCB's CNode_Delete), whose local attempt
    // will decline again, so it does not wait next time. Nor does a
    // TCB_SetTimer or VM syscall that declined (another core's thread or
    // VCPU, nVHE); one that found the gate closed may run beside it. Any
    // other candidate that found the gate closed leaves `local_hit` as it
    // was: a closed gate says nothing about the syscall. Clearing it made
    // a core that timed out waiting take a ticket for its next frame-cap
    // invocation or fault reply whenever the gate was closed, keeping it
    // closed for the next core, until every core's local paths ran
    // serially (an l4h guest's page faults on 64 AArch64 cores); setting
    // it made a core whose last attempt declined, and so did not wait,
    // wait next time, every other call of a stream that declines.
    let prev = env.mem().a_load(&gate.policy[env.cpu() as usize].local_hit, Ordering::Relaxed) != 0;
    let hit = local_hit_after(candidate, fast.get(), &res, prev);
    env.mem().a_store(&gate.policy[env.cpu() as usize].local_hit, hit as u64, Ordering::Relaxed);
    ran
}

/// Whether a syscall `run_syscall` ran under the gate after local attempt
/// `res` leaves this core waiting for a closed gate next time (`local_hit`),
/// `prev` before. `local_entry` writes `local_hit` only when its local path
/// ran, so on `Local::Closed` it is still the one that attempt waited, or
/// did not wait, by.
#[inline(always)]
fn local_hit_after(c: Candidate, fast: bool, res: &Local, prev: bool) -> bool {
    fast || c == Candidate::Port
        || (matches!(res, Local::Closed) && (prev || matches!(c, Candidate::SetTimer | Candidate::Vm)))
}

/// A VM fault from user code: on several cores, first try its fast path
/// beside the serial gate (`local_vm_fault`), then `run_entry`. Returns as
/// `run_entry` does. `local` runs `local_vm_fault` on the store it is given.
#[inline(always)]
pub fn run_vm_fault<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    mut local: impl FnMut(&mut E::S, &mut E::A) -> bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    if !env.multi() {
        return run_entry(env, gate, false, |s, a| body(s, a));
    }
    match local_entry(env, gate, &mut local) {
        Local::Done => return true,
        Local::Stalled => return false,
        Local::Closed | Local::Declined => {}
    }
    let ran = run_entry(env, gate, false, |s, a| body(s, a));
    // As for an I/O port access: the general path has no VM-fault fast
    // path, and a fault that declined beside the gate (its handler not
    // waiting yet) usually runs there next time, so the next one waits
    // for a closed gate rather than take a ticket.
    env.mem().a_store(&gate.policy[env.cpu() as usize].local_hit, 1, Ordering::Relaxed);
    ran
}

/// The local path of a VM fault (`fl4_core::syscall::handle_vm_fault_local`)
/// with its fault endpoint and the waiting handler's reply object locked,
/// as for a trapped syscall's fault in `local_syscall`; true if it ran.
#[inline(always)]
pub fn local_vm_fault<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    addr: u64,
    code: u64,
    observe: impl FnOnce(&S, &[(u64, u64)]),
) -> bool {
    use fl4_core::capability::Cap;
    use fl4_core::layout::tcb as tl;
    use fl4_core::obj::Ep;
    let t = fl4_core::sched::cur_thread(s);
    let mut held = lock::Held::new();
    let mut held_objects = [(0, 0); 2];
    let ok = match t.slot(tl::SLOT_FAULT_HANDLER).cap(s) {
        Cap::Endpoint { ptr, .. } => {
            lock_object(m, ptr, &mut held) && Ep(ptr).state(s) == fl4_core::obj::EP_RECV && {
                let dest = fl4_core::obj::Tcb(Ep(ptr).head(s));
                let r = if dest.is_null() { 0 } else { dest.reply_obj(s) };
                held_objects = [(ptr, 16), (r, 32)];
                r != 0 && lock_object(m, r, &mut held)
            }
        }
        _ => false,
    };
    let done = ok && {
        observe(s, &held_objects);
        fl4_core::syscall::handle_vm_fault_local(s, a, addr, code)
    };
    lock::unlock_held(m, &mut held);
    done
}

/// `lock::try_lock_object`. (Mutation test: `mutant-local-no-lock` takes
/// nothing.)
#[inline(always)]
fn lock_object<M: Mem>(m: &M, addr: u64, held: &mut lock::Held) -> bool {
    cfg!(feature = "mutant-local-no-lock") || lock::try_lock_object(m, addr, held)
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
    } else if number == fl4_abi::syscall::SysCall
        // A frame-cap invocation, by its label alone.
        && fl4_core::localinv::is_local_label(fl4_core::msg::msg_info(s, t).label)
    {
        Candidate::Invocation
    } else if number == fl4_abi::syscall::SysCall
        // A TCB_SetTimer, by its label alone.
        && fl4_core::msg::msg_info(s, t).label == fl4_abi::label::TCBSetTimer
    {
        Candidate::SetTimer
    } else if localvm::is_vm_syscall(s, t, number) {
        Candidate::Vm
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
    /// A frame-cap invocation (`handle_invocation_local`).
    Invocation,
    /// A `TCB_SetTimer` (`localtimer::handle_set_timer_local`).
    SetTimer,
    /// A VM's syscall (`localvm`).
    Vm,
}

/// How long `local_entry` waits for a closed gate to open, through
/// `EntryEnv::local_wait_over`: many serial entries' worth. Too short a
/// wait sends local paths into the gate's queue, which then keeps the gate
/// closed (`release`) for the next ones to time out on, until nearly every
/// syscall is serial. Measured on a 64-core GCE N4A (AArch64), getpid on
/// 32/48/64 cores: 1024 spins (a few microseconds there) 0.4M/-/0.25M ops/s;
/// 50 us 24M/0.27M/0.23M; 500 us 26M/23M/19M; 5 ms 26M/19M/16M (cores
/// waiting out of FIFO order for longer).
pub const LOCAL_WAIT_US: u64 = 500;
/// The bound without a clock (the simulator), in spins.
const LOCAL_WAIT_SPINS: u32 = 1024;

/// How a local path beside the gate went (`try_local`).
pub enum Local {
    Done,
    Declined,
    /// The gate stayed closed.
    Closed,
    /// A remote stall took this core's thread while it waited for the gate.
    Stalled,
}

/// On several cores, local path `local` beside the serial gate, as `run_syscall`
/// tries one (on one core, Declined); the caller takes the gate unless Done.
#[inline(always)]
pub fn try_local<E: EntryEnv>(env: &E, gate: &SerialGate, mut local: impl FnMut(&mut E::S, &mut E::A) -> bool) -> Local {
    if !env.multi() {
        return Local::Declined;
    }
    local_entry(env, gate, &mut local)
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
    // `LOCAL_WAIT_US` (`EntryEnv::local_wait_over`) it takes a ticket.
    let hit = &gate.policy[cpu as usize].local_hit;
    let mut spins = 0;
    let mut start = 0;
    // (Mutation test: `mutant-local-no-active` does not mark the core.)
    while !cfg!(feature = "mutant-local-no-active") && !gate.try_enter_local(env.mem(), cpu) {
        if env.mem().a_load(hit, Ordering::Relaxed) == 0 {
            return Local::Closed;
        }
        if spins == 0 {
            start = env.now();
        } else if env.local_wait_over(spins, start) {
            return Local::Closed;
        }
        spins += 1;
        if env.service_remote() {
            // A remote stall took this core's thread: no entry for it now.
            return Local::Stalled;
        }
        core::hint::spin_loop();
    }
    let done = local(&mut env.store(), &mut env.arch());
    env.mem().a_store(hit, done as u64, Ordering::Relaxed);
    if !cfg!(feature = "mutant-local-no-active") {
        gate.leave_local(env.mem(), cpu);
    }
    if done {
        env.count(Count::Local);
        Local::Done
    } else {
        Local::Declined
    }
}

const _: () = assert!(fl4_core::localinv::MAX_LOCKS <= lock::MAX_HELD);

/// A frame-cap invocation beside the gate (`fl4_core::localinv`): lock
/// the words its plan names (capability slots, 32 bytes, and at most one
/// page-table entry, 8), then run it, which checks the plan again.
#[inline(always)]
fn local_invocation<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    number: i64,
    observe: impl FnOnce(&S, &[(u64, u64)]),
) -> bool {
    use fl4_core::localinv::MAX_LOCKS;
    let p = match fl4_core::localinv::plan(s, number) {
        Some(p) => p,
        None => return false,
    };
    let mut objects = [(0, 0); MAX_LOCKS];
    for i in 0..p.n {
        objects[i] = (p.locks[i], if i == p.pte { 8 } else { 32 });
    }
    with_locks(m, Held::new(), &objects[..p.n], |o| {
        observe(s, o);
        fl4_core::syscall::handle_invocation_local(s, a, number, &p)
    })
}

/// `cspace::lookup_slot` of `cptr` in the CSpace of thread `t`, locking
/// each slot (`lock::try_lock_object`) before reading it: other cores'
/// frame-cap invocations write slots of a shared CSpace beside the gate,
/// under those locks (`local_invocation`). The slot found, with every
/// slot read locked in `held`; None if a lock is taken, the lookup fails,
/// or it needs more than `lock::MAX_HELD` levels. (The root, `t`'s CTable
/// slot, is no CNode's: only the gate's entries write it.)
#[inline(always)]
fn lookup_slot_locked<S: fl4_core::machine::Store, M: Mem>(
    s: &S,
    m: &M,
    t: fl4_core::obj::Tcb,
    cptr: u64,
    held: &mut lock::Held,
) -> Option<fl4_core::obj::Slot> {
    use fl4_core::capability::Cap;
    let mut cap = t.slot(fl4_core::layout::tcb::SLOT_CTABLE).cap(s);
    let mut bits = fl4_core::cspace::WORD_BITS;
    for _ in 0..lock::MAX_HELD {
        let (slot, rest) = localtimer::cspace_step(cap, cptr, bits)?;
        if !lock_object(m, slot.0, held) {
            return None;
        }
        let next = slot.cap(s);
        match next {
            Cap::CNode { .. } if rest != 0 => {
                cap = next;
                bits = rest;
            }
            _ => return Some(slot),
        }
    }
    None
}

/// A `TCB_SetTimer` beside the gate (`localtimer::handle_set_timer_local`),
/// on the thread its capability register names, found with the slots of its
/// lookup locked (`lookup_slot_locked`) and kept locked while it runs. It
/// writes no slot; it writes this core's state, the caller, the target
/// thread and the timer tree of this core, all of them this core's alone
/// while the gate is open (`localtimer`'s Timer ownership): `observe` sees
/// no object.
#[inline(always)]
fn local_set_timer<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    number: i64,
    observe: impl FnOnce(&S, &[(u64, u64)]),
) -> bool {
    let t = fl4_core::sched::cur_thread(s);
    let cptr = t.reg(s, fl4_core::layout::reg::CAP);
    let mut held = lock::Held::new();
    let target = match lookup_slot_locked(s, m, t, cptr, &mut held).map(|slot| slot.cap(s)) {
        Some(fl4_core::capability::Cap::Thread { ptr }) => fl4_core::obj::Tcb(ptr),
        _ => {
            lock::unlock_held(m, &mut held);
            return false;
        }
    };
    observe(s, &[]);
    let done = localtimer::handle_set_timer_local(s, a, number, target);
    lock::unlock_held(m, &mut held);
    done
}

const _: () = assert!(localtimer::MAX_TIMER_LOCKS <= lock::MAX_HELD);

/// A kernel timer interrupt (`IRQ_TIMER`) on a multi-core system: first
/// its local path beside the serial gate (`local_timer_irq`), then
/// `run_entry`. The interrupt has been accepted, so it is handled whatever
/// happens: a stall while the local path waits for the gate to open, or a
/// local path that declines, leaves it to `body` under the gate, which runs
/// even after a stall (`run_entry` with `irq`). Returns as `run_entry`
/// does: true.
///
/// `local` runs `local_timer_irq` on the store it is given (and, on
/// AArch64, acknowledges the interrupt first); `body` is the general path.
#[inline(always)]
pub fn run_timer_irq<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    mut local: impl FnMut(&mut E::S, &mut E::A) -> bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    if !env.multi() {
        return run_entry(env, gate, true, |s, a| body(s, a));
    }
    let res = local_entry(env, gate, &mut local);
    if let Local::Done = res {
        return true;
    }
    let ran = run_entry(env, gate, true, |s, a| body(s, a));
    // The general path has no timer fast path. One that found the gate
    // closed (or was stalled waiting for it) may run beside it next time;
    // one that declined (`local_entry` stored 0) usually declines again.
    if !matches!(res, Local::Declined) {
        env.mem().a_store(&gate.policy[env.cpu() as usize].local_hit, 1, Ordering::Relaxed);
    }
    ran
}

/// The local path of kernel timer interrupt `irq`
/// (`localtimer::handle_timer_irq_local`): plan with reads only, lock the
/// notification the due timer signals (and, if that wakes its thread from
/// `Recv`, the endpoint and reply object `cancel_ipc` writes), let
/// `observe` see them, then run; true if it ran. As `local_syscall`, it
/// writes nothing before `observe`.
#[inline(always)]
pub fn local_timer_irq<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    irq: u64,
    observe: impl FnOnce(&S, &[(u64, u64)]),
) -> bool {
    let p = match localtimer::plan_timer_irq(s, irq) {
        Some(p) => p,
        None => return false,
    };
    with_locks(m, Held::new(), &p.objects[..p.n], |o| {
        observe(s, o);
        localtimer::handle_timer_irq_local(s, a, irq, &p)
    })
}

/// The local path of a syscall made outside the gate (`run_syscall`), with
/// its endpoint and reply object locked; true if it ran. `observe` sees
/// the objects it holds, as (address, bytes), once it holds them and
/// before it writes anything: the simulator's footprint oracle (DESIGN.md
/// §10); a no-op in the kernels.
#[inline(always)]
pub fn local_syscall<S: fl4_core::machine::Store, A: fl4_core::machine::Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    number: i64,
    observe: impl FnOnce(&S, &[(u64, u64)]),
) -> bool {
    use fl4_core::capability::Cap;
    use fl4_core::layout::tcb as tl;
    use fl4_core::obj::{Ep, Reply};
    let t = fl4_core::sched::cur_thread(s);
    let mut held = lock::Held::new();
    // What `held` holds, for `observe`: endpoints 16 bytes, replies 32.
    let mut held_objects = [(0, 0); 2];
    // The endpoint and reply object the fast path will use, each locked
    // (`lock::try_lock_object`) before the fast path reads them again.
    let mut found = (0, 0);
    let ok = if t.flags(s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0 {
        match t.slot(tl::SLOT_FAULT_HANDLER).cap(s) {
            Cap::Endpoint { ptr, .. } => {
                // (A receiver waiting is the fast path's first condition:
                // without one, decline before touching anything.)
                lock_object(m, ptr, &mut held) && Ep(ptr).state(s) == fl4_core::obj::EP_RECV && {
                    let dest = fl4_core::obj::Tcb(Ep(ptr).head(s));
                    let r = if dest.is_null() { 0 } else { dest.reply_obj(s) };
                    held_objects = [(ptr, 16), (r, 32)];
                    r != 0 && lock_object(m, r, &mut held)
                }
            }
            _ => false,
        }
    } else if number == fl4_abi::syscall::SysReplyRecv {
        match fl4_core::fastpath::reply_caps(s, t) {
            Some((r, ep)) => {
                found = (r, ep);
                held_objects = [(r, 32), (ep, 16)];
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
    } else if number == fl4_abi::syscall::SysCall
        && fl4_core::localinv::is_local_label(fl4_core::msg::msg_info(s, t).label)
    {
        return local_invocation(s, a, m, number, observe);
    } else if number == fl4_abi::syscall::SysCall
        && fl4_core::msg::msg_info(s, t).label == fl4_abi::label::TCBSetTimer
    {
        return local_set_timer(s, a, m, number, observe);
    } else {
        #[cfg(not(feature = "aarch64"))]
        if localvm::is_vm_syscall(s, t, number) {
            return local_vm_syscall(s, a, m, number, observe);
        }
        // An I/O port access writes only the caller and this core's
        // state: nothing to lock.
        observe(s, &[]);
        return fl4_core::syscall::handle_ioport_local(s, a, number);
    };
    let done = ok && {
        observe(s, &held_objects);
        // A reply to a VM fault takes `fastpath_vm`'s path, any other
        // `fastpath`'s: one or the other, so the entry's prefix runs once.
        // (`found` is set for a ReplyRecv only, not for a trapped thread's
        // syscall with that number.)
        if found.0 != 0
            && fl4_core::obj::Tcb(Reply(found.0).tcb(s)).fault_type(s) == fl4_abi::consts::fault::VMFault
        {
            fl4_core::syscall::handle_reply_recv_vm_local(s, a, found)
        } else {
            fl4_core::syscall::handle_syscall_local(s, a, number, found)
        }
    };
    lock::unlock_held(m, &mut held);
    done
}

/// `observe`: the simulator's footprint oracle (a no-op in the kernels).
pub trait Observe<S>: FnOnce(&S, &[(u64, u64)]) {}
impl<S, F: FnOnce(&S, &[(u64, u64)])> Observe<S> for F {}

/// Lock each of `objs` (address, bytes) once, skipping 0, beside `held`;
/// if all were free, `f` on those locked; release all. Else the default.
#[inline(always)]
fn with_locks<M: Mem, R: Default>(m: &M, mut held: Held, objs: &[(u64, u64)], f: impl FnOnce(&[(u64, u64)]) -> R) -> R {
    let (mut locked, mut k, mut ok) = ([(0, 0); lock::MAX_HELD], 0, true);
    for &(o, bytes) in objs {
        if ok && o != 0 && !locked[..k].iter().any(|&(x, _)| x == o) {
            ok = lock_object(m, o, &mut held);
            locked[k] = (o, bytes);
            k += 1;
        }
    }
    let r = if ok { f(&locked[..k]) } else { R::default() };
    lock::unlock_held(m, &mut held);
    r
}

const _: () = assert!(localvm::MAX_VM_LOCKS <= lock::MAX_HELD);

/// A VM local path (`localvm`): declined without a VCPU, else `l`'s
/// objects locked beside `held`, `observe`, then `run`.
#[inline(always)]
fn vm_local<S: Store, M: Mem>(
    s: &mut S,
    m: &M,
    mut held: Held,
    l: &localvm::VmLocks,
    observe: impl Observe<S>,
    run: impl FnOnce(&mut S) -> bool,
) -> bool {
    if l.vcpu == 0 {
        lock::unlock_held(m, &mut held);
        return false;
    }
    with_locks(m, held, &l.objects, |o| {
        observe(s, o);
        run(s)
    })
}

/// The VCPU cap the current thread's capability register names: its slot
/// and VCPU (0: none), the lookup's slots locked (`lookup_slot_locked`).
#[inline(always)]
fn vcpu_cap_locked<S: Store, M: Mem>(s: &S, m: &M, held: &mut Held) -> (fl4_core::obj::Slot, u64) {
    let t = fl4_core::sched::cur_thread(s);
    match lookup_slot_locked(s, m, t, t.reg(s, fl4_core::layout::reg::CAP), held).map(|slot| (slot, slot.cap(s))) {
        Some((slot, fl4_core::capability::Cap::Vcpu { ptr })) => (slot, ptr),
        _ => (fl4_core::obj::Slot(0), 0),
    }
}

/// x86: `SysVMEnter`, or a VCPU state invocation on the VCPU its cap names.
#[cfg(not(feature = "aarch64"))]
#[inline(always)]
fn local_vm_syscall<S: Store, A: Arch, M: Mem>(s: &mut S, a: &mut A, m: &M, number: i64, observe: impl Observe<S>) -> bool {
    if number == fl4_abi::syscall::SysVMEnter {
        let l = localvm::vm_locks(s, localvm::cur_vcpu(s));
        return vm_local(s, m, Held::new(), &l, observe, |s| localvm::handle_vm_enter_local(s, a, number, l.vcpu, l.ntfn));
    }
    let mut held = Held::new();
    let (slot, v) = vcpu_cap_locked(s, m, &mut held);
    vm_local(s, m, held, &localvm::vcpu_locks(v), observe, |s| localvm::handle_vcpu_invocation_local(s, a, number, slot, v))
}

/// x86: the checks before entering the current thread's guest, its bound
/// notification locked: the EPT root to enter on, or None for the gate.
#[cfg(not(feature = "aarch64"))]
#[inline(always)]
pub fn local_vm_entry<S: Store, M: Mem>(s: &S, m: &M) -> Option<u64> {
    let l = localvm::vm_locks(s, localvm::cur_vcpu(s));
    with_locks(m, Held::new(), &[(l.ntfn, localvm::NTFN_BYTES)], |_| localvm::vm_entry_ready(s, l.vcpu, l.ntfn))
}

/// x86: a VM exit of the current thread, with no host interrupt (`NO_IRQ`)
/// or the kernel timer's.
#[cfg(not(feature = "aarch64"))]
#[inline(always)]
pub fn local_vm_exit<S: Store, A: Arch, M: Mem>(s: &mut S, a: &mut A, m: &M, irq: u64, observe: impl Observe<S>) -> bool {
    if irq != fl4_core::syscall::NO_IRQ {
        return local_vm_timer_irq(s, a, m, irq, observe);
    }
    let l = localvm::vm_locks(s, localvm::cur_vcpu(s));
    vm_local(s, m, Held::new(), &l, observe, |s| localvm::handle_vcpu_exit_local(s, a, l.vcpu, l.ntfn))
}

/// The kernel timer interrupt `irq` while the current thread runs a guest.
#[inline(always)]
pub fn local_vm_timer_irq<S: Store, A: Arch, M: Mem>(s: &mut S, a: &mut A, m: &M, irq: u64, observe: impl Observe<S>) -> bool {
    let Some(p) = localtimer::plan_timer_irq(s, irq) else { return false };
    let l = localvm::vm_timer_locks(s, localvm::cur_vcpu(s), &p);
    vm_local(s, m, Held::new(), &l, observe, |s| localvm::handle_vm_timer_irq_local(s, a, irq, &p, l.ntfn))
}

/// AArch64: an `ARMVCPURun` on the VCPU its cap names; `hw_ok(s, vc,
/// guest)` is the kernel's word on its hardware state, asked under the locks.
#[cfg(feature = "aarch64")]
#[inline(always)]
pub fn local_arm_vcpu_run<S: Store, A: Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    number: i64,
    hw_ok: impl FnOnce(&S, u64, fl4_core::obj::Tcb) -> bool,
    observe: impl Observe<S>,
) -> bool {
    let mut held = Held::new();
    let (slot, vc) = vcpu_cap_locked(s, m, &mut held);
    let l = localvm::vm_locks(s, vc);
    let run = |s: &mut S| {
        let guest = localvm::vcpu_guest(s, vc);
        let hw = !guest.is_null() && hw_ok(s, vc, guest);
        localvm::handle_arm_vcpu_run_local(s, a, number, slot, vc, l.ntfn, hw)
    };
    vm_local(s, m, held, &l, observe, run)
}

/// AArch64: the check before an `ARMVCPURun` caller's guest runs, its
/// bound notification locked.
#[cfg(feature = "aarch64")]
#[inline(always)]
pub fn local_arm_vm_entry<S: Store, M: Mem>(s: &S, m: &M) -> bool {
    let l = localvm::vm_locks(s, localvm::cur_vcpu(s));
    with_locks(m, Held::new(), &[(l.ntfn, localvm::NTFN_BYTES)], |_| localvm::arm_vm_entry_ready(s, l.ntfn))
}

/// AArch64: an exit of an `ARMVCPURun` caller's guest.
#[cfg(feature = "aarch64")]
#[inline(always)]
pub fn local_arm_vcpu_run_exit<S: Store, A: Arch, M: Mem>(
    s: &mut S,
    a: &mut A,
    m: &M,
    stop: u64,
    w: (u64, u64, u64),
    hvc: Option<(fl4_core::obj::Tcb, u64)>,
    observe: impl Observe<S>,
) -> bool {
    let vc = localvm::cur_vcpu(s);
    let run = |s: &mut S| localvm::handle_arm_vcpu_run_exit_local(s, a, vc, stop, w.0, w.1, w.2, hvc);
    vm_local(s, m, Held::new(), &localvm::vcpu_locks(vc), observe, run)
}

#[inline(always)]
fn serial<E: EntryEnv>(env: &E, gate: &SerialGate, irq: bool, body: &mut impl FnMut(&mut E::S, &mut E::A)) -> bool {
    let mut a = env.arch();
    if !env.multi() {
        body(&mut env.store(), &mut a);
        return true;
    }
    let mut stalled = false;
    gate.acquire(env.mem(), env.cpu(), || {
        if env.service_remote() {
            stalled = true;
        }
    });
    env.count(Count::Serial);
    env.holding_gate();
    if stalled && !irq {
        return false;
    }
    body(&mut env.store(), &mut a);
    true
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::sync::Arc;
    use std::thread;

    struct Atomics;
    impl Mem for Atomics {}

    /// Every mutant feature is refused on the kernel targets: the
    /// `compile_error!` guard names each one Cargo.toml declares.
    #[test]
    fn every_mutant_is_refused_on_bare_metal() {
        let manifest = include_str!("../Cargo.toml");
        let src = include_str!("lib.rs");
        let at = src.find("#[cfg(all(\n    target_os = \"none\",").expect("the bare-metal guard");
        let guard = &src[at..at + src[at..].find("compile_error!").expect("compile_error")];
        let mutants: std::vec::Vec<&str> =
            manifest.lines().filter_map(|l| l.strip_suffix(" = []")).filter(|f| f.starts_with("mutant-")).collect();
        assert_eq!(mutants.len(), 4, "{mutants:?}");
        for m in mutants {
            assert!(guard.contains(&std::format!("feature = \"{m}\"")), "{m} is not refused on bare metal");
        }
    }

    /// A core waits for a closed gate next time after a fast path ran under
    /// it, an I/O port access, or a `TCB_SetTimer` or VM syscall that found
    /// it closed; any other attempt that found it closed keeps what the core
    /// did (waiting after a timeout, not after a decline: no oscillation);
    /// none waits after one that declined (or was stalled) with no fast path.
    #[test]
    fn only_closed_gates_or_fast_paths_keep_the_core_waiting() {
        for prev in [false, true] {
            for c in [Candidate::Fast, Candidate::Invocation, Candidate::SetTimer, Candidate::Vm] {
                assert!(local_hit_after(c, true, &Local::Declined, prev));
                assert!(!local_hit_after(c, false, &Local::Declined, prev) && !local_hit_after(c, false, &Local::Stalled, prev));
            }
            for c in [Candidate::SetTimer, Candidate::Vm] {
                assert!(local_hit_after(c, false, &Local::Closed, prev));
            }
            for c in [Candidate::Fast, Candidate::Invocation] {
                assert_eq!(local_hit_after(c, false, &Local::Closed, prev), prev);
            }
            assert!(local_hit_after(Candidate::Port, false, &Local::Declined, prev));
        }
    }

    #[test]
    fn a_local_path_cannot_start_while_the_gate_is_held() {
        let gate = SerialGate::new();
        assert!(gate.try_enter_local(&Atomics, 1));
        gate.leave_local(&Atomics, 1);
        gate.acquire(&Atomics, 0, || panic!("empty gate"));
        assert_eq!(gate.owner(), 0);
        assert!(!gate.try_enter_local(&Atomics, 1));
        gate.release(&Atomics);
        assert!(gate.try_enter_local(&Atomics, 1));
        gate.leave_local(&Atomics, 1);
    }

    #[test]
    fn the_gate_holder_waits_for_active_local_paths() {
        let gate = Arc::new(SerialGate::new());
        assert!(gate.try_enter_local(&Atomics, 1));
        let g = Arc::clone(&gate);
        let holder = thread::spawn(move || {
            g.acquire(&Atomics, 0, thread::yield_now);
            g.release(&Atomics);
        });
        // The holder closes the gate, then waits for core 1.
        while gate.head.closed.load(Ordering::Relaxed) == 0 {
            thread::yield_now();
        }
        assert_eq!(gate.owner(), u64::MAX);
        assert!(!gate.try_enter_local(&Atomics, 2));
        gate.leave_local(&Atomics, 1);
        holder.join().unwrap();
        assert!(gate.try_enter_local(&Atomics, 2));
        gate.leave_local(&Atomics, 2);
    }

    /// Serial entries are served in ticket order across the counter's
    /// wraparound, and the gate stays closed (state 2) between queued ones.
    #[test]
    fn tickets_are_served_in_order_and_queued_ones_inherit_exclusion() {
        use std::sync::{mpsc, Mutex};
        let gate = Arc::new(SerialGate::new());
        gate.next.store(u64::MAX - 1, Ordering::Relaxed);
        gate.head.serving.store(u64::MAX - 1, Ordering::Relaxed);
        gate.acquire(&Atomics, 0, || panic!("empty gate"));
        let order = Arc::new(Mutex::new(std::vec::Vec::new()));
        let (tx, rx) = mpsc::channel();
        let mut workers = std::vec::Vec::new();
        for cpu in 1..=4u64 {
            let gate = Arc::clone(&gate);
            let order = Arc::clone(&order);
            let tx = tx.clone();
            workers.push(thread::spawn(move || {
                let mut notified = false;
                gate.acquire(&Atomics, cpu, || {
                    if !notified {
                        tx.send(cpu).unwrap();
                        notified = true;
                    }
                    thread::yield_now();
                });
                assert_eq!(gate.head.closed.load(Ordering::Relaxed), 2);
                order.lock().unwrap().push(cpu);
                gate.release(&Atomics);
            }));
            assert_eq!(rx.recv().unwrap(), cpu);
        }
        gate.release(&Atomics);
        for w in workers {
            w.join().unwrap();
        }
        assert_eq!(*order.lock().unwrap(), (1..=4).collect::<std::vec::Vec<_>>());
        assert_eq!(gate.head.closed.load(Ordering::Relaxed), 0);
        assert!(gate.try_enter_local(&Atomics, 5));
        gate.leave_local(&Atomics, 5);
    }

    /// The tests that take object locks (`lock::try_lock_object`), whose
    /// table is the process's, run one at a time: one test's held lock
    /// would make another's lookup decline.
    static LOCK_TABLE_TEST: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// Kernel memory as a map, recording the words read.
    struct MapStore {
        m: std::collections::HashMap<u64, u64>,
        cpu: u64,
        reads: core::cell::RefCell<std::vec::Vec<u64>>,
    }

    /// Threads at `TCB_BASE + i * TCB_STRIDE`; the global state below.
    const KS_BASE: u64 = 0x1000_0000;
    const TCB_BASE: u64 = 0x10_0000_0000;
    const TCB_STRIDE: u64 = 0x10000;

    impl fl4_core::machine::Store for MapStore {
        fn read(&self, addr: u64) -> u64 {
            self.reads.borrow_mut().push(addr);
            *self.m.get(&addr).unwrap_or(&0)
        }
        fn write(&mut self, addr: u64, v: u64) {
            self.m.insert(addr, v);
        }
        fn zero(&mut self, addr: u64, len: u64) {
            for a in (addr..addr + len).step_by(8) {
                self.m.insert(a, 0);
            }
        }
        fn clear_free(&mut self, addr: u64, len: u64) {
            self.zero(addr, len)
        }
        fn ks_base(&self) -> u64 {
            KS_BASE
        }
        fn cur_cpu(&self) -> u64 {
            self.cpu
        }
    }

    fn thread(i: u64) -> fl4_core::obj::Tcb {
        fl4_core::obj::Tcb(TCB_BASE + i * TCB_STRIDE)
    }

    /// Core `c`'s timer tree, through fl4-core's own insert.
    fn arm(s: &mut MapStore, c: u64, i: u64, deadline: u64) {
        s.cpu = c;
        fl4_core::timer::insert(s, thread(i), deadline, i);
    }

    /// The threads of core `c`'s tree, walked from its root.
    fn tree(s: &MapStore, c: u64) -> std::collections::HashSet<u64> {
        let mut out = std::collections::HashSet::new();
        let mut stack = std::vec![fl4_core::obj::node_get(s, c, fl4_core::layout::node::TIMER_ROOT)];
        while let Some(u) = stack.pop() {
            if u != 0 && out.insert(u) {
                stack.push(fl4_core::obj::Tcb(u).timer_left(s));
                stack.push(fl4_core::obj::Tcb(u).timer_right(s));
            }
        }
        out
    }

    /// `in_core_timer_tree(cpu, target, d)`, checking that it read no
    /// thread outside core `cpu`'s tree (`target`'s links included, unless
    /// it is in that tree).
    fn in_tree(s: &MapStore, cpu: u64, target: u64, d: u64) -> bool {
        let mine = tree(s, cpu);
        s.reads.borrow_mut().clear();
        let r = localtimer::in_core_timer_tree(s, cpu, thread(target), d);
        for &a in s.reads.borrow().iter() {
            if a >= TCB_BASE {
                let t = TCB_BASE + (a - TCB_BASE) / TCB_STRIDE * TCB_STRIDE;
                assert!(mine.contains(&t), "read {a:#x} of thread {t:#x}, outside core {cpu}'s tree");
            }
        }
        r
    }

    /// Exact answers on two cores' trees with equal deadlines on both
    /// sides of nodes, as rotations leave them, and none read outside
    /// the core's own tree; after removals too.
    #[test]
    fn in_core_timer_tree_finds_this_cores_nodes_only() {
        let mut s = MapStore { m: std::collections::HashMap::new(), cpu: 0, reads: Default::default() };
        let ds = [5, 3, 8, 3, 3, 9, 1, 5, 5, 7, 2, 8, 3, 5, 5];
        let n = ds.len() as u64;
        for (i, &d) in ds.iter().enumerate() {
            arm(&mut s, 0, i as u64, d);
            arm(&mut s, 1, n + i as u64, d);
        }
        assert_eq!(tree(&s, 0).len(), ds.len());
        for i in 0..n {
            let d = ds[i as usize];
            assert!(in_tree(&s, 0, i, d), "thread {i} in core 0's tree");
            assert!(!in_tree(&s, 1, i, d), "thread {i} not in core 1's tree");
            assert!(in_tree(&s, 1, n + i, d), "thread {} in core 1's tree", n + i);
            assert!(!in_tree(&s, 0, n + i, d), "thread {} not in core 0's tree", n + i);
            assert_eq!(localtimer::core_of(&s, thread(i)), 0);
        }
        // A thread armed on neither.
        assert!(!in_tree(&s, 0, 2 * n, 5));
        // Removed threads are found no more, the others still are.
        for i in (0..n).step_by(3) {
            fl4_core::timer::remove(&mut s, thread(i));
        }
        for i in 0..n {
            assert_eq!(in_tree(&s, 0, i, ds[i as usize]), i % 3 != 0, "thread {i} after removals");
        }
    }

    /// Past its bounds (`TREE_STACK`, `TREE_VISITS`) the search answers no,
    /// which only declines the local path; never yes for another tree's
    /// node. The earliest node and the root are found at once.
    #[test]
    fn in_core_timer_tree_is_bounded() {
        let mut s = MapStore { m: std::collections::HashMap::new(), cpu: 0, reads: Default::default() };
        let n = 300;
        for i in 0..n {
            arm(&mut s, 0, i, 42);
            arm(&mut s, 1, n + i, 42);
        }
        let min = fl4_core::obj::node_get(&s, 0, fl4_core::layout::node::TIMER_MIN);
        let root = fl4_core::obj::node_get(&s, 0, fl4_core::layout::node::TIMER_ROOT);
        assert!(in_tree(&s, 0, (min - TCB_BASE) / TCB_STRIDE, 42));
        assert!(in_tree(&s, 0, (root - TCB_BASE) / TCB_STRIDE, 42));
        let mut found = 0;
        for i in 0..n {
            found += in_tree(&s, 0, i, 42) as u64;
            assert!(!in_tree(&s, 1, i, 42));
            assert!(!in_tree(&s, 0, n + i, 42));
        }
        assert!(found >= localtimer::TREE_VISITS / 2 && found < n, "{found} of {n} found within the bounds");
    }

    /// A CSpace: root CNode `R` (radix 4, a 56-bit guard of 0), whose slot 1
    /// holds CNode `C` (radix 2, a 2-bit guard of 1, resolving the last 4
    /// bits), slot 2 a thread (found with bits left), slot 3 a CNode that
    /// resolves more bits than are left, slot 4 one that resolves none;
    /// `C`'s slots threads and nothing. Thread `T` has `R` as its CSpace.
    fn cspace() -> (MapStore, fl4_core::obj::Tcb) {
        use fl4_core::capability::Cap;
        use fl4_core::obj::Slot;
        let mut s = MapStore { m: std::collections::HashMap::new(), cpu: 0, reads: Default::default() };
        let (r, c, d, e) = (0x30_0000_0000u64, 0x31_0000_0000u64, 0x32_0000_0000u64, 0x33_0000_0000u64);
        let t = thread(1000);
        t.slot(fl4_core::layout::tcb::SLOT_CTABLE).set_cap(&mut s, Cap::CNode { ptr: r, radix: 4, guard_size: 56, guard: 0 });
        Slot::index(r, 1).set_cap(&mut s, Cap::CNode { ptr: c, radix: 2, guard_size: 2, guard: 1 });
        Slot::index(r, 2).set_cap(&mut s, Cap::Thread { ptr: thread(1).0 });
        Slot::index(r, 3).set_cap(&mut s, Cap::CNode { ptr: d, radix: 4, guard_size: 1, guard: 0 });
        Slot::index(r, 4).set_cap(&mut s, Cap::CNode { ptr: e, radix: 0, guard_size: 0, guard: 0 });
        Slot::index(c, 0).set_cap(&mut s, Cap::Thread { ptr: thread(2).0 });
        Slot::index(c, 3).set_cap(&mut s, Cap::Thread { ptr: thread(3).0 });
        (s, t)
    }

    /// `lookup_slot_locked`, one level at a time through `localtimer::cspace_step`,
    /// finds the slot `cspace::lookup_slot` finds, and fails where it fails
    /// (guard and depth mismatches, a CNode resolving no bits, not a CNode),
    /// on one level and two; it reads only slots it has locked.
    #[test]
    fn locked_lookup_finds_what_lookup_slot_finds() {
        let _guard = LOCK_TABLE_TEST.lock().unwrap_or_else(|e| e.into_inner());
        let (s, t) = cspace();
        let mut x: u64 = 0x2545_f491_4f6c_dd1d;
        let mut found = 0;
        for i in 0..4000u64 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // Mostly the guard of 0 above the low 8 bits; sometimes not.
            let cptr = if i % 8 == 0 { x } else { x & 0xff };
            let mut held = lock::Held::new();
            let got = lookup_slot(&s, t, cptr, &mut held);
            let want = fl4_core::cspace::lookup_slot(&s, t, cptr).ok().map(|r| r.slot.0);
            assert_eq!(got, want, "cptr {cptr:#x}");
            found += got.is_some() as u64;
            lock::unlock_held(&Atomics, &mut held);
        }
        assert!(found > 1000, "{found} lookups found a slot");
    }

    /// `lookup_slot_locked` and `cspace::lookup_slot` on the CSpace of
    /// `t`; checks that every slot word read was locked first.
    fn lookup_slot(s: &MapStore, t: fl4_core::obj::Tcb, cptr: u64, held: &mut lock::Held) -> Option<u64> {
        s.reads.borrow_mut().clear();
        let got = lookup_slot_locked(s, &Atomics, t, cptr, held).map(|sl| sl.0);
        let reads: std::vec::Vec<u64> = s.reads.borrow().clone();
        for a in reads {
            let ctable = t.slot(fl4_core::layout::tcb::SLOT_CTABLE).0;
            if a >= 0x30_0000_0000 && a < 0x40_0000_0000 {
                let slot = a & !31;
                let mut other = lock::Held::new();
                assert!(!lock::try_lock_object(&Atomics, slot, &mut other), "slot {slot:#x} read unlocked");
            } else {
                assert!(a >= ctable && a < ctable + 32, "read {a:#x} outside the lookup");
            }
        }
        got
    }

    /// A slot another core holds (a frame-cap invocation writing it) is
    /// not read: the lookup gives up, and finds it once it is free.
    #[test]
    fn locked_lookup_declines_on_a_slot_another_core_holds() {
        let _guard = LOCK_TABLE_TEST.lock().unwrap_or_else(|e| e.into_inner());
        let (s, t) = cspace();
        let terminal = fl4_core::obj::Slot::index(0x31_0000_0000, 3).0;
        // Root slot 1 (C), then C's slot 3: 0b0001 << 4 | 0b01 << 2 | 3.
        let cptr = (1 << 4) | (1 << 2) | 3;
        let mut other = lock::Held::new();
        assert!(lock::try_lock_object(&Atomics, terminal, &mut other));
        let mut held = lock::Held::new();
        s.reads.borrow_mut().clear();
        assert!(lookup_slot_locked(&s, &Atomics, t, cptr, &mut held).is_none());
        assert!(s.reads.borrow().iter().all(|&a| a & !31 != terminal), "read the held slot");
        lock::unlock_held(&Atomics, &mut held);
        lock::unlock_held(&Atomics, &mut other);
        let got = lookup_slot_locked(&s, &Atomics, t, cptr, &mut held);
        assert!(matches!(got.map(|sl| sl.cap(&s)), Some(fl4_core::capability::Cap::Thread { ptr }) if ptr == thread(3).0));
        lock::unlock_held(&Atomics, &mut held);
    }

    /// Whether `o`'s lock is free (taken and released at once).
    fn free(o: u64) -> bool {
        let mut h = Held::new();
        let ok = lock::try_lock_object(&Atomics, o, &mut h);
        lock::unlock_held(&Atomics, &mut h);
        ok
    }
    const OBJ: [u64; 4] = [0x50_0000_0000, 0x50_0000_1000, 0x50_0000_2000, 0x50_0000_3000];

    /// `with_locks` and `vm_local` lock each object once, skipping 0 (a
    /// guest's own timer names its notification twice), run under all of
    /// them, and release them and the `held` given; one another core holds,
    /// or no VCPU, runs nothing and releases `held` too.
    #[test]
    fn vm_lock_wrappers_lock_once_and_release_all() {
        let _guard = LOCK_TABLE_TEST.lock().unwrap_or_else(|e| e.into_inner());
        let [a, b, c, d] = OBJ;
        let pre = || {
            let mut h = Held::new();
            assert!(lock::try_lock_object(&Atomics, d, &mut h));
            h
        };
        let seen = with_locks(&Atomics, pre(), &[(0, 0), (a, 8), (b, 64), (a, 8)], |o| {
            assert!(!free(a) && !free(b) && !free(d));
            o.to_vec()
        });
        assert_eq!(seen, std::vec![(a, 8), (b, 64)]);
        let mut other = Held::new();
        assert!(lock::try_lock_object(&Atomics, c, &mut other));
        assert!(!with_locks(&Atomics, pre(), &[(a, 8), (c, 8), (b, 8)], |_| true));
        let l = |vcpu| localvm::VmLocks { vcpu, ntfn: b, objects: [(a, 8), (0, 0), (b, 64), (vcpu, 32), (b, 64)] };
        let mut s = MapStore { m: Default::default(), cpu: 0, reads: Default::default() };
        let never = |_: &MapStore, _: &[(u64, u64)]| panic!("observed");
        assert!(!vm_local(&mut s, &Atomics, pre(), &l(0), never, |_| true), "no VCPU");
        assert!(!vm_local(&mut s, &Atomics, pre(), &l(c), never, |_| true), "a held VCPU");
        lock::unlock_held(&Atomics, &mut other);
        let mut obs = std::vec::Vec::new();
        assert!(vm_local(&mut s, &Atomics, pre(), &l(c), |_, o: &[(u64, u64)]| obs = o.to_vec(), |_| !free(c)));
        assert_eq!(obs, std::vec![(a, 8), (b, 64), (c, 32)]);
        assert!(OBJ.iter().all(|&o| free(o)));
    }

    /// The check before a guest's entry declines while another core holds
    /// the current thread's bound notification, and leaves no lock.
    #[test]
    fn vm_entry_check_declines_on_a_held_notification() {
        let _guard = LOCK_TABLE_TEST.lock().unwrap_or_else(|e| e.into_inner());
        let (t, [_, vc, n, _]) = (thread(7), OBJ);
        let mut s = MapStore { m: Default::default(), cpu: 0, reads: Default::default() };
        fl4_core::obj::node_set(&mut s, 0, fl4_core::layout::node::CUR_THREAD, t.0);
        t.set_state(&mut s, fl4_core::sched::TS_RUNNING_VM);
        t.set_bound_ntfn(&mut s, n);
        #[cfg(not(feature = "aarch64"))]
        let (ready, at) = (|s: &MapStore| local_vm_entry(s, &Atomics).is_some(), fl4_core::layout::tcb::VCPU);
        #[cfg(feature = "aarch64")]
        let (ready, at) = (|s: &MapStore| local_arm_vm_entry(s, &Atomics), fl4_core::layout::tcb::RUN_VCPU);
        s.write(t.0 + at, vc);
        assert!(ready(&s));
        let mut other = Held::new();
        assert!(lock::try_lock_object(&Atomics, n, &mut other));
        assert!(!ready(&s));
        lock::unlock_held(&Atomics, &mut other);
        assert!(ready(&s) && free(n));
    }
}
