//! fl4-sim: deterministic simulation of FL4 on several cores (DESIGN.md
//! §10). The real fl4-core runs against a simulated memory (`SimStore`) and
//! machine (`SimArch`). A seeded scheduler picks which core takes the next
//! kernel entry; user threads issue random, often malformed, syscalls;
//! timers and IPIs are delivered in virtual time. After every entry the
//! oracles check the kernel's invariants. The same seed replays the same
//! run.
//!
//! Without `--conc`, kernel entries run one at a time, as under the serial
//! gate. With it, each simulated core is a coroutine, and all of them run
//! on one host thread, switching at memory accesses. A campaign boots once
//! and forks a child process per run from the booted state, one child per
//! host CPU at a time.
//!
//! Usage: fl4-sim [--seeds N] [--first S] [--cores C] [--steps K] [--conc]
//!        [--pct D] [--tso] [--scenario ep|ntfn|guest|timer] [--fastpath-diff] [--suite] [--jobs J]

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::cell::{Cell, RefCell};
use std::sync::{Arc, Mutex};

use corosensei::stack::DefaultStack;
use corosensei::{Coroutine, CoroutineResult, Yielder};

use fl4_abi::consts::{bits, object as ot, root_slot as rs};
use fl4_abi::{label, syscall as sc};
use fl4_core::boot::{self, BootParams, Region, MAX_REGIONS};
use fl4_core::capability::Cap;
use fl4_core::layout::{self, irq, ks, node, reg, tcb as tl, PPTR_BASE};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_get, Slot, Tcb};
use fl4_core::{sched, syscall};
use fl4_store::lock;
use fl4_sync::SerialGate;

/// Simulated physical memory: 0..MEM_BYTES, seen through the kernel window.
const MEM_BYTES: u64 = 96 << 20;
/// Kernel state, idle threads and the extra BootInfo live in "kernel image"
/// memory: the top 8 MiB of simulated memory, not given to user space.
const IMAGE_BYTES: u64 = 8 << 20;

struct Memory {
    words: Vec<AtomicU64>,
    /// Per 32-byte line (one capability slot): written since the oracles
    /// last looked, and the list of such lines.
    dirty: Vec<AtomicBool>,
    dirty_list: Mutex<Vec<u64>>,
    watch: Mutex<SlotWatch>,
    /// `--fastpath-diff`: while logging, each store's word index and the
    /// value it replaced, oldest first.
    undo: Mutex<Option<Vec<(usize, u64)>>>,
    logging: AtomicBool,
}

/// What the slot oracles saw at their last check (`Sim::slots_to_check`):
/// the slot regions of `Sim::slot_regions` then, and the slots in them that
/// were not empty and unlinked.
#[derive(Default)]
struct SlotWatch {
    regions: Vec<(u64, u64)>,
    live: Vec<u64>,
}

/// `n` zero words, on zero pages the host maps when first touched: a run
/// pays only for the memory it uses, not for all of `MEM_BYTES`.
fn zeroed_words(n: usize) -> Vec<AtomicU64> {
    let mut v = std::mem::ManuallyDrop::new(vec![0u64; n]);
    // SAFETY: AtomicU64 has the size and alignment of u64 on x86-64.
    unsafe { Vec::from_raw_parts(v.as_mut_ptr().cast(), v.len(), v.capacity()) }
}

fn zeroed_flags(n: usize) -> Vec<AtomicBool> {
    let mut v = std::mem::ManuallyDrop::new(vec![0u8; n]);
    // SAFETY: AtomicBool has the size and alignment of u8, and 0 is false.
    unsafe { Vec::from_raw_parts(v.as_mut_ptr().cast(), v.len(), v.capacity()) }
}

impl Memory {
    fn index(&self, addr: u64) -> usize {
        let p = addr.wrapping_sub(PPTR_BASE);
        assert!(addr % 8 == 0, "fl4-sim: unaligned kernel access at {addr:#x}");
        assert!(p < MEM_BYTES, "fl4-sim: kernel access outside memory at {addr:#x}");
        (p / 8) as usize
    }
    fn get(&self, addr: u64) -> u64 {
        self.words[self.index(addr)].load(Ordering::Relaxed)
    }
    fn set(&self, addr: u64, v: u64) {
        let i = self.index(addr);
        if self.logging.load(Ordering::Relaxed) {
            let old = self.words[i].load(Ordering::Relaxed);
            self.undo.lock().unwrap().as_mut().unwrap().push((i, old));
        }
        self.words[i].store(v, Ordering::Relaxed);
        let line = &self.dirty[i / 4];
        if !line.load(Ordering::Relaxed) {
            line.store(true, Ordering::Relaxed);
            self.dirty_list.lock().unwrap().push(PPTR_BASE + (i / 4) as u64 * 32);
        }
    }

    /// The `n` words at `addr`, as memory holds them (no store buffer).
    fn words_at(&self, addr: u64, n: u64) -> &[AtomicU64] {
        let i = self.index(addr);
        self.index(addr + (n - 1) * 8);
        &self.words[i..i + n as usize]
    }

    fn start_log(&self) {
        *self.undo.lock().unwrap() = Some(Vec::new());
        self.logging.store(true, Ordering::Relaxed);
    }

    fn take_log(&self) -> Vec<(usize, u64)> {
        self.logging.store(false, Ordering::Relaxed);
        self.undo.lock().unwrap().take().unwrap()
    }

    /// The 32-byte lines written since the last call.
    fn take_dirty(&self) -> Vec<u64> {
        let v = std::mem::take(&mut *self.dirty_list.lock().unwrap());
        for &a in &v {
            self.dirty[((a - PPTR_BASE) / 32) as usize].store(false, Ordering::Relaxed);
        }
        v
    }
}

/// Concurrent mode: one coroutine per simulated core, all on one host
/// thread, run one at a time in an order the seed decides, switching at
/// memory accesses and spins. A switch is a stack switch, not a host
/// context switch.
struct Conc {
    baton: Mutex<Baton>,
    /// Cores asked to service a remote stall.
    call_pending: AtomicU64,
    in_kernel: Vec<AtomicBool>,
    gate_held: Vec<AtomicBool>,
    /// Cores that have run all their steps.
    out_of_steps: AtomicU64,
    /// Per core, while it runs a local path beside the gate: the words it
    /// writes, for the footprint oracle (`Sim::check_footprint`).
    footprint: Vec<Mutex<Option<Vec<u64>>>>,
    /// Per core, while it runs a frame-cap invocation's local path
    /// (`fl4_core::localinv`): the one local path that may invalidate TLB
    /// entries (`SimArch::local_tlb`).
    local_tlb: Vec<AtomicBool>,
    /// Per core, while it runs a kernel timer interrupt's local path
    /// (`fl4_sync::local_timer_irq`): the one local path that ends an
    /// interrupt, the timer's (`SimArch::ack_irq`).
    local_timer: Vec<AtomicBool>,
    /// x86-TSO (DESIGN.md §10): per core, the stores not yet visible to
    /// other cores, oldest first. Off unless `--tso`.
    tso: bool,
    sb: Vec<Mutex<StoreBuffer>>,
}

/// What a buffered store writes: a word of simulated memory, or one of the
/// runtime's atomics (serial gate, object locks).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Target {
    Word(u64),
    Atomic(usize),
}

struct Baton {
    turn: u64,
    rng: Rng,
    done: Vec<bool>,
    /// Per core: out of steps, only answering remote stalls.
    idle: Vec<bool>,
    pct: Option<Pct>,
    /// Per core: spins since the core last finished a kernel entry.
    spins: Vec<u64>,
    explore: Option<Explore>,
}

/// Bounded exhaustive search (DESIGN.md §10, `--explore`): the schedule is
/// fixed by the list of scheduling points at which the running core is
/// preempted. Points are the runtime's atomic operations only (the gate,
/// object locks): data accesses happen with the gate held or inside a
/// local path's footprint, so their order against another core's matters
/// only at those. Otherwise a
/// core runs until it spins or runs out of steps, then the next one runs.
struct Explore {
    points: u64,
    switches: Vec<u64>,
}

/// PCT, probabilistic concurrency testing (Burckhardt et al., ASPLOS
/// 2010): the live core with the highest priority runs. Priorities start
/// as a random order above `depth`; at `depth - 1` scheduling points drawn
/// at random the running core drops to a priority below every start
/// priority. A bug that needs `depth` ordering constraints is found with
/// probability at least 1/(n k^(depth-1)) per run, for n cores and k
/// scheduling points. A spinning core drops below everyone else, since it
/// waits for another core.
struct Pct {
    prio: Vec<i64>,
    change_points: Vec<u64>,
    next_low: i64,
    points: u64,
}

impl Pct {
    /// Below every other core.
    fn demote(&mut self, cpu: u64) {
        self.prio[cpu as usize] = self.next_low;
        self.next_low -= 1;
    }
}

thread_local! {
    /// Per core: its coroutine's yielder, for `Conc::wait_turn`.
    static YIELDERS: RefCell<Vec<*const Yielder<(), ()>>> = const { RefCell::new(Vec::new()) };
}

/// Spins without finishing an entry after which a core is taken to be
/// livelocked or deadlocked (DESIGN.md §10, liveness oracle).
const SPIN_LIMIT: u64 = 2_000_000;

/// `--fastpath-diff`: run each serial syscall both through the general
/// path and through `handle_syscall` from the same state, and require the
/// same memory and machine state (fl4_core::fastpath). Counts: syscalls
/// checked, and those a fast path ran.
static FASTPATH_DIFF: AtomicBool = AtomicBool::new(false);
static FASTPATH_COUNTS: Mutex<(u64, u64)> = Mutex::new((0, 0));

/// The local paths beside the gate that PR #71 and issue #94 added, as
/// tried (serially under `--fastpath-diff`, or beside the gate with
/// `--conc`) and as run: frame-cap invocations (`fl4_core::localinv`), VM
/// faults (`fastpath_vm::vm_fault`) and ReplyRecv answering one
/// (`fastpath_vm::reply_recv_vm_found`, run only), `TCB_SetTimer` and kernel
/// timer interrupts (`fl4_core::localtimer`).
#[derive(Default, Clone, Copy, Debug)]
struct LocalCounts {
    inv_tried: u64,
    inv_ran: u64,
    vm_fault_tried: u64,
    vm_fault_ran: u64,
    vm_reply_ran: u64,
    /// TLB invalidations frame-cap invocations made beside the gate
    /// (`--conc`): of a page, of an address space.
    tlb_page: u64,
    tlb_asid: u64,
    /// `TCB_SetTimer`: tried, run; of those run, disarming (deadline 0)
    /// and re-arming a timer armed in this core's tree.
    set_timer_tried: u64,
    set_timer_ran: u64,
    set_timer_disarm: u64,
    set_timer_rearm: u64,
    /// Kernel timer interrupts: tried, run; of those run, what they did
    /// (`TimerCase`), and how many switched from the idle thread to a
    /// thread or from one thread to another.
    timer_irq_tried: u64,
    timer_irq_ran: u64,
    timer_irq_noop: u64,
    timer_irq_rr: u64,
    timer_irq_fire_unbound: u64,
    timer_irq_fire_active: u64,
    timer_irq_fire_set_active: u64,
    timer_irq_fire_wake_recv: u64,
    timer_irq_fire_wake_ntfn: u64,
    timer_irq_idle_wake: u64,
    timer_irq_switch: u64,
    /// NBWait on a notification (`handle_nbwait_local`): tried, run.
    poll_tried: u64,
    poll_ran: u64,
}

impl LocalCounts {
    const ZERO: LocalCounts = LocalCounts {
        inv_tried: 0,
        inv_ran: 0,
        vm_fault_tried: 0,
        vm_fault_ran: 0,
        vm_reply_ran: 0,
        tlb_page: 0,
        tlb_asid: 0,
        set_timer_tried: 0,
        set_timer_ran: 0,
        set_timer_disarm: 0,
        set_timer_rearm: 0,
        timer_irq_tried: 0,
        timer_irq_ran: 0,
        timer_irq_noop: 0,
        timer_irq_rr: 0,
        timer_irq_fire_unbound: 0,
        timer_irq_fire_active: 0,
        timer_irq_fire_set_active: 0,
        timer_irq_fire_wake_recv: 0,
        timer_irq_fire_wake_ntfn: 0,
        timer_irq_idle_wake: 0,
        timer_irq_switch: 0,
        poll_tried: 0,
        poll_ran: 0,
    };

    /// Every count by name, for the runs' output and a campaign's totals.
    fn fields(&mut self) -> [(&'static str, &mut u64); 24] {
        [
            ("inv_tried", &mut self.inv_tried),
            ("inv_ran", &mut self.inv_ran),
            ("vm_fault_tried", &mut self.vm_fault_tried),
            ("vm_fault_ran", &mut self.vm_fault_ran),
            ("vm_reply_ran", &mut self.vm_reply_ran),
            ("tlb_page", &mut self.tlb_page),
            ("tlb_asid", &mut self.tlb_asid),
            ("set_timer_tried", &mut self.set_timer_tried),
            ("set_timer_ran", &mut self.set_timer_ran),
            ("set_timer_disarm", &mut self.set_timer_disarm),
            ("set_timer_rearm", &mut self.set_timer_rearm),
            ("timer_irq_tried", &mut self.timer_irq_tried),
            ("timer_irq_ran", &mut self.timer_irq_ran),
            ("timer_irq_noop", &mut self.timer_irq_noop),
            ("timer_irq_rr", &mut self.timer_irq_rr),
            ("timer_irq_fire_unbound", &mut self.timer_irq_fire_unbound),
            ("timer_irq_fire_active", &mut self.timer_irq_fire_active),
            ("timer_irq_fire_set_active", &mut self.timer_irq_fire_set_active),
            ("timer_irq_fire_wake_recv", &mut self.timer_irq_fire_wake_recv),
            ("timer_irq_fire_wake_ntfn", &mut self.timer_irq_fire_wake_ntfn),
            ("timer_irq_idle_wake", &mut self.timer_irq_idle_wake),
            ("timer_irq_switch", &mut self.timer_irq_switch),
            ("poll_tried", &mut self.poll_tried),
            ("poll_ran", &mut self.poll_ran),
        ]
    }

    /// `name=value` pairs, as a run prints them (`LOCAL_COUNTS_TAG`).
    fn line(mut self) -> String {
        self.fields().iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join(" ")
    }

    /// Add the counts of a run's output line (`line`).
    fn add_line(&mut self, l: &str) {
        for kv in l.split_whitespace() {
            let Some((k, v)) = kv.split_once('=') else { continue };
            let Ok(v) = v.parse::<u64>() else { continue };
            for (name, f) in self.fields() {
                if name == k {
                    *f += v;
                }
            }
        }
    }

    /// Count a timer interrupt's local attempt that ran (`ran`) as `case`.
    fn timer_irq(&mut self, ran: bool, case: Option<TimerCase>) {
        self.timer_irq_tried += 1;
        if !ran {
            return;
        }
        self.timer_irq_ran += 1;
        let Some(c) = case else { return };
        match c.kind {
            TimerKind::Noop => self.timer_irq_noop += 1,
            TimerKind::RoundRobin => self.timer_irq_rr += 1,
            TimerKind::FireUnbound => self.timer_irq_fire_unbound += 1,
            TimerKind::FireActive => self.timer_irq_fire_active += 1,
            TimerKind::FireSetActive => self.timer_irq_fire_set_active += 1,
            TimerKind::FireWakeRecv => self.timer_irq_fire_wake_recv += 1,
            TimerKind::FireWakeNtfn => self.timer_irq_fire_wake_ntfn += 1,
        }
        self.timer_irq_idle_wake += c.idle_wake as u64;
        self.timer_irq_switch += c.switch as u64;
    }
}

static LOCAL_COUNTS: Mutex<LocalCounts> = Mutex::new(LocalCounts::ZERO);

/// What starts a run's line of `LocalCounts`.
const LOCAL_COUNTS_TAG: &str = "local path counts: ";

/// What a kernel timer interrupt's local path did (for `LocalCounts`):
/// read before it runs, once it holds its locks (`TimerSnap`), and after.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TimerKind {
    /// Neither a budget expiry nor a due timer.
    Noop,
    /// A round-robin budget ran out; the thread goes on.
    RoundRobin,
    /// A timer fired: of a thread with no bound notification, or
    /// signalling one that was active (badges ORed), idle with its thread
    /// not waiting (made active), idle with its thread in `Recv` (woken,
    /// `cancel_ipc`), or waiting (its waiter woken).
    FireUnbound,
    FireActive,
    FireSetActive,
    FireWakeRecv,
    FireWakeNtfn,
}

#[derive(Clone, Copy, Debug)]
struct TimerCase {
    kind: TimerKind,
    idle_wake: bool,
    switch: bool,
}

/// The state a timer interrupt's local path starts from, as `TimerCase`
/// needs it.
#[derive(Clone, Copy)]
struct TimerSnap {
    ct: u64,
    idle: u64,
    tm: u64,
    ntfn_state: Option<u64>,
    bound_state: u64,
    csc: u64,
    rr: bool,
}

impl TimerSnap {
    /// Read without scheduling points, as `footprint`.
    fn take(s: &SimStore) -> TimerSnap {
        let s = SimStore { conc: None, ..s.clone() };
        let cpu = s.cpu;
        let tm = Tcb(node_get(&s, cpu, node::TIMER_MIN));
        let n = if tm.is_null() { 0 } else { tm.bound_ntfn(&s) };
        let csc = fl4_core::obj::Sc(node_get(&s, cpu, node::CUR_SC));
        TimerSnap {
            ct: node_get(&s, cpu, node::CUR_THREAD),
            idle: node_get(&s, cpu, node::IDLE_THREAD),
            tm: tm.0,
            ntfn_state: (n != 0).then(|| fl4_core::obj::Ntfn(n).state(&s)),
            bound_state: if n == 0 { 0 } else { Tcb(fl4_core::obj::Ntfn(n).bound_tcb(&s)).state(&s) },
            csc: csc.0,
            rr: csc.0 != node_get(&s, cpu, node::IDLE_SC) && csc.period(&s) == 0,
        }
    }

    /// What the local path that started from this did, read after it ran.
    fn case(&self, s: &SimStore) -> TimerCase {
        let s = s.peek();
        let ct = node_get(&s, s.cpu, node::CUR_THREAD);
        let fired = self.tm != 0 && Tcb(self.tm).timer_deadline(&s) == 0;
        let kind = if fired {
            match self.ntfn_state {
                None => TimerKind::FireUnbound,
                Some(fl4_core::obj::NTFN_ACTIVE) => TimerKind::FireActive,
                Some(fl4_core::obj::NTFN_WAITING) => TimerKind::FireWakeNtfn,
                Some(_) if self.bound_state == sched::TS_BLOCKED_ON_RECV => TimerKind::FireWakeRecv,
                Some(_) => TimerKind::FireSetActive,
            }
        } else if self.rr && fl4_core::sporadic::tail(&s, fl4_core::obj::Sc(self.csc)).amount == 0 {
            // `charge_budget` empties a round-robin tail, which the commit
            // of a budget not run out fills.
            TimerKind::RoundRobin
        } else {
            TimerKind::Noop
        };
        TimerCase { kind, idle_wake: self.ct == self.idle && ct != self.idle, switch: ct != self.ct }
    }
}

/// A local syscall path ran on the objects `held` (`fl4_sync::local_syscall`'s
/// `observe`): whether it is a ReplyRecv answering a VM fault, which holds
/// its reply object (32 bytes) then its endpoint (16), and whose reply
/// names a thread with a VM fault. Read beside the locks, without
/// scheduling points (as `footprint`).
fn replies_to_vm_fault(s: &SimStore, held: &[(u64, u64)]) -> bool {
    let s = SimStore { conc: None, ..s.clone() };
    match held {
        [(r, 32), (_, 16)] => {
            let u = Tcb(fl4_core::obj::Reply(*r).tcb(&s));
            !u.is_null() && u.fault_type(&s) == fl4_abi::consts::fault::VMFault
        }
        _ => false,
    }
}

impl Conc {
    /// `pct`: run PCT of that depth over about `points` scheduling points.
    fn new(n: u64, seed: u64, pct: Option<(u64, u64)>, tso: bool, explore: Option<Vec<u64>>) -> Conc {
        let mut rng = Rng(seed ^ 0x5DEE_CE66_D1CE_4E5B | 1);
        let pct = pct.map(|(depth, points)| {
            let mut prio: Vec<i64> = (0..n as i64).map(|i| depth as i64 + 1 + i).collect();
            for i in (1..prio.len()).rev() {
                let j = rng.below(i as u64 + 1) as usize;
                prio.swap(i, j);
            }
            let change_points = (1..depth).map(|_| 1 + rng.below(points.max(1))).collect();
            Pct { prio, change_points, next_low: depth as i64 - 1, points: 0 }
        });
        let turn = pct.as_ref().map_or(0, |p| (0..n).max_by_key(|&c| p.prio[c as usize]).unwrap());
        Conc {
            baton: Mutex::new(Baton {
                turn,
                rng,
                done: vec![false; n as usize],
                idle: vec![false; n as usize],
                pct,
                spins: vec![0; n as usize],
                explore: explore.map(|switches| Explore { points: 0, switches }),
            }),
            call_pending: AtomicU64::new(0),
            in_kernel: (0..n).map(|_| AtomicBool::new(false)).collect(),
            gate_held: (0..n).map(|_| AtomicBool::new(false)).collect(),
            out_of_steps: AtomicU64::new(0),
            footprint: (0..n).map(|_| Mutex::new(None)).collect(),
            local_tlb: (0..n).map(|_| AtomicBool::new(false)).collect(),
            local_timer: (0..n).map(|_| AtomicBool::new(false)).collect(),
            tso,
            sb: (0..n).map(|_| Mutex::new(StoreBuffer::default())).collect(),
        }
    }

    fn pass(&self, b: &mut Baton) {
        let mut live: Vec<u64> = (0..b.done.len() as u64).filter(|&c| !b.done[c as usize]).collect();
        // A core out of steps that relaxes passes to one with steps left,
        // if any: it has nothing to do until one of those asks it for a
        // stall, and the asker's spins pass to every live core.
        if b.explore.is_none() && b.pct.is_none() && b.idle[b.turn as usize] && live.iter().any(|&c| !b.idle[c as usize]) {
            live.retain(|&c| !b.idle[c as usize]);
        }
        if !live.is_empty() {
            b.turn = if b.explore.is_some() {
                // The next live core after the current one.
                *live.iter().find(|&&c| c > b.turn).unwrap_or(&live[0])
            } else {
                match &b.pct {
                    Some(p) => *live.iter().max_by_key(|&&c| p.prio[c as usize]).unwrap(),
                    None => live[b.rng.below(live.len() as u64) as usize],
                }
            };
        }
    }

    /// Back to the scheduler loop (`run_one`) until it is `cpu`'s turn.
    fn wait_turn(&self, cpu: u64, b: std::sync::MutexGuard<'_, Baton>) {
        let mut mine = b.turn == cpu;
        drop(b);
        while !mine {
            let y = YIELDERS.with(|v| v.borrow()[cpu as usize]);
            // SAFETY: set by `cpu`'s coroutine, which is the one running.
            unsafe { (*y).suspend(()) };
            mine = self.baton.lock().unwrap().turn == cpu;
        }
    }

    /// A scheduling point: maybe let another core run.
    fn pause(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        if b.explore.is_some() {
            return;
        }
        if let Some(p) = &mut b.pct {
            p.points += 1;
            if !p.change_points.contains(&p.points) {
                return;
            }
            p.demote(cpu);
        } else if b.rng.below(4) != 0 {
            return;
        }
        self.pass(&mut b);
        self.wait_turn(cpu, b);
    }

    /// A core waiting for another (the gate, a stall it asked for): a scheduling point, counted for the liveness oracle.
    fn spin(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        b.spins[cpu as usize] += 1;
        assert!(b.spins[cpu as usize] < SPIN_LIMIT, "liveness: core {cpu} spun {SPIN_LIMIT} times without finishing a kernel entry");
        match &mut b.pct {
            Some(p) => p.demote(cpu),
            None => {
                if b.explore.is_none() && b.rng.below(4) != 0 {
                    return;
                }
            }
        }
        self.pass(&mut b);
        self.wait_turn(cpu, b);
    }

    /// A scheduling point of the exhaustive search (a runtime atomic).
    fn explore_point(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        let Some(e) = &mut b.explore else { return };
        let k = e.points;
        e.points += 1;
        if e.switches.contains(&k) {
            self.pass(&mut b);
            self.wait_turn(cpu, b);
        }
    }

    /// The core finished a kernel entry.
    fn progress(&self, cpu: u64) {
        self.baton.lock().unwrap().spins[cpu as usize] = 0;
    }

    /// A core with nothing to do always lets another core run.
    fn relax(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        b.idle[cpu as usize] = true;
        if let Some(p) = &mut b.pct {
            p.demote(cpu);
        }
        self.pass(&mut b);
        self.wait_turn(cpu, b);
    }

    fn start(&self, cpu: u64) {
        let b = self.baton.lock().unwrap();
        self.wait_turn(cpu, b);
    }

    fn finish(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        b.done[cpu as usize] = true;
        self.pass(&mut b);
    }
}

#[derive(Clone)]
struct SimStore {
    mem: Arc<Memory>,
    ks_base: u64,
    cpu: u64,
    conc: Option<Arc<Conc>>,
    /// Reads are no scheduling points (`peek`).
    peek: bool,
}

impl SimStore {
    /// This store, read without scheduling points but, under x86-TSO, with
    /// this core's own buffered stores: what the core itself now sees, for
    /// the counts of what a local path did (`TimerSnap::case`).
    fn peek(&self) -> SimStore {
        SimStore { peek: true, ..self.clone() }
    }

    fn pause(&self) {
        if let Some(c) = &self.conc {
            c.pause(self.cpu);
        }
    }

    fn direct_set(&self, addr: u64, v: u64) {
        if let Some(c) = &self.conc {
            if let Some(w) = c.footprint[self.cpu as usize].lock().unwrap().as_mut() {
                w.push(addr);
            }
        }
        if self.tso().is_some() {
            self.buffer(Target::Word(addr), v);
        } else {
            self.mem.set(addr, v)
        }
    }
}

/// A core's store buffer (x86-TSO): its stores not yet visible, oldest
/// first, and per target the newest buffered value and how many stores to
/// it are buffered, for store forwarding.
#[derive(Default)]
struct StoreBuffer {
    q: std::collections::VecDeque<(Target, u64)>,
    newest: HashMap<Target, (u64, usize)>,
}

impl StoreBuffer {
    fn push(&mut self, t: Target, v: u64) {
        self.q.push_back((t, v));
        let e = self.newest.entry(t).or_insert((v, 0));
        *e = (v, e.1 + 1);
    }

    fn pop(&mut self) -> Option<(Target, u64)> {
        let (t, v) = self.q.pop_front()?;
        let e = self.newest.get_mut(&t).unwrap();
        e.1 -= 1;
        if e.1 == 0 {
            self.newest.remove(&t);
        }
        Some((t, v))
    }
}

impl SimStore {
    fn tso(&self) -> Option<&Arc<Conc>> {
        self.conc.as_ref().filter(|c| c.tso)
    }

    /// This core's newest buffered store to `t`, if any (store forwarding).
    fn forward(&self, t: Target) -> Option<u64> {
        let c = self.tso()?;
        c.sb[self.cpu as usize].lock().unwrap().newest.get(&t).map(|e| e.0)
    }

    fn buffer(&self, t: Target, v: u64) {
        self.tso().unwrap().sb[self.cpu as usize].lock().unwrap().push(t, v);
    }

    fn apply(&self, t: Target, v: u64) {
        match t {
            Target::Word(a) => self.mem.set(a, v),
            Target::Atomic(p) => unsafe { (*(p as *const AtomicU64)).store(v, Ordering::SeqCst) },
        }
    }

    /// Make this core's buffered stores visible, oldest first (a locked
    /// instruction, MFENCE, or the end of a kernel entry).
    fn drain(&self) {
        if let Some(c) = self.tso() {
            let pending: Vec<_> = {
                let mut sb = c.sb[self.cpu as usize].lock().unwrap();
                sb.newest.clear();
                sb.q.drain(..).collect()
            };
            for (t, v) in pending {
                self.apply(t, v);
            }
        }
    }

    /// Now and then the oldest buffered store becomes visible by itself.
    fn maybe_drain_one(&self) {
        if let Some(c) = self.tso() {
            if c.baton.lock().unwrap().rng.below(8) == 0 {
                let e = c.sb[self.cpu as usize].lock().unwrap().pop();
                if let Some((t, v)) = e {
                    self.apply(t, v);
                }
            }
        }
    }

    /// A plain load of kernel memory: this core's own buffered stores
    /// first.
    fn mem_get(&self, addr: u64) -> u64 {
        self.forward(Target::Word(addr)).unwrap_or_else(|| self.mem.get(addr))
    }
}

impl lock::Mem for SimStore {
    fn a_load(&self, a: &AtomicU64, o: Ordering) -> u64 {
        self.pause();
        if let Some(c) = &self.conc {
            c.explore_point(self.cpu);
        }
        self.maybe_drain_one();
        let _ = o;
        self.forward(Target::Atomic(a as *const _ as usize)).unwrap_or_else(|| a.load(Ordering::SeqCst))
    }
    fn a_store(&self, a: &AtomicU64, v: u64, o: Ordering) {
        self.pause();
        if let Some(c) = &self.conc {
            c.explore_point(self.cpu);
        }
        // On x86 only a SeqCst store is a locked instruction (XCHG);
        // release and relaxed stores are plain MOVs into the buffer.
        if self.tso().is_some() && o != Ordering::SeqCst {
            self.buffer(Target::Atomic(a as *const _ as usize), v);
        } else {
            self.drain();
            a.store(v, Ordering::SeqCst)
        }
    }
    fn a_cas(&self, a: &AtomicU64, old: u64, new: u64, _ok: Ordering, _err: Ordering) -> Result<u64, u64> {
        self.pause();
        if let Some(c) = &self.conc {
            c.explore_point(self.cpu);
        }
        self.drain();
        a.compare_exchange(old, new, Ordering::SeqCst, Ordering::SeqCst)
    }
    fn a_add(&self, a: &AtomicU64, v: u64, _o: Ordering) -> u64 {
        self.pause();
        if let Some(c) = &self.conc {
            c.explore_point(self.cpu);
        }
        self.drain();
        a.fetch_add(v, Ordering::SeqCst)
    }
    fn fence(&self, o: Ordering) {
        self.pause();
        if let Some(c) = &self.conc {
            c.explore_point(self.cpu);
        }
        // On x86 only a SeqCst fence (MFENCE) orders stores before loads.
        if o == Ordering::SeqCst {
            self.drain();
        }
    }
}

impl Store for SimStore {
    fn read(&self, addr: u64) -> u64 {
        if !self.peek {
            self.pause();
        }
        self.mem_get(addr)
    }
    fn read_pair(&self, addr: u64) -> (u64, u64) {
        (self.read(addr), self.read(addr.wrapping_add(8)))
    }
    fn write(&mut self, addr: u64, v: u64) {
        self.pause();
        self.direct_set(addr, v)
    }
    fn fetch_and(&mut self, addr: u64, mask: u64) -> u64 {
        // A locked instruction: one step, after the store buffer drains,
        // and its store is not buffered.
        self.pause();
        self.drain();
        let old = self.mem.get(addr);
        self.direct_set(addr, old & mask);
        self.drain();
        old
    }
    fn zero(&mut self, addr: u64, len: u64) {
        assert!(len % 8 == 0);
        self.pause();
        let mut a = addr;
        while a < addr + len {
            self.direct_set(a, 0);
            a += 8;
        }
    }
    fn clear_free(&mut self, addr: u64, len: u64) {
        self.zero(addr, len)
    }
    fn ks_base(&self) -> u64 {
        self.ks_base
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}

/// An `Arch` call with an effect on the machine, as `Machine::effects`
/// records them.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Effect {
    Deadline(u64),
    Reschedule(u64),
    Putc(u8),
    /// An I/O port write: port, size, value.
    PortOut(u64, u64, u64),
    /// End of interrupt `irq`, which must be the one in service.
    Ack(u64),
    /// An address space loaded: root and ASID.
    SetVSpace(u64, u64),
    /// The clock read, and what it gave.
    Now(u64),
}

/// Per-core machine state.
#[derive(Default, Clone, PartialEq, Debug)]
struct Core {
    /// The address space last loaded (`Arch::set_vspace`): root and ASID.
    vspace: (u64, u64),
    deadline: u64,
    /// Pending IRQs (bit = irq number, up to 191).
    pending: [u64; 3],
    /// The interrupt the local APIC has accepted and not yet seen an EOI
    /// for. Until then it blocks interrupts of its priority class and
    /// below, the timer and IPIs among them (GitHub issue #6).
    in_service: Option<u64>,
}

#[derive(Clone, PartialEq, Debug)]
struct Machine {
    now: u64,
    cores: Vec<Core>,
    console: Vec<u8>,
    /// I/O port writes, in order.
    ports: Vec<(u64, u64, u64)>,
    rng: Rng,
    halted: bool,
    /// Boot as an Intel TDX guest (`Arch::tdx_active`).
    tdx: bool,
    /// The frames TDG.MR.REPORT wrote.
    tdx_reports: Vec<u64>,
    /// `--fastpath-diff`, while one entry is checked: the `Arch` calls with
    /// an effect it made, in order (`SimArch::apply`), which its local or
    /// fast path and the general path must make alike (`Sim::diff_general`).
    effects: Option<Vec<Effect>>,
}

#[derive(Clone)]
struct SimArch {
    m: Arc<Mutex<Machine>>,
    mem: Arc<Memory>,
    ks_base: u64,
    cpu: u64,
    conc: Option<Arc<Conc>>,
}

impl SimArch {
    /// The footprint oracle's half for Arch (DESIGN.md §10): an operation
    /// no local path may make, since it concerns other cores, the
    /// hardware's shared state, or another thread's FPU state.
    fn gate_only(&self, what: &str) {
        if let Some(c) = &self.conc {
            assert!(c.footprint[self.cpu as usize].lock().unwrap().is_none(), "footprint: core {}'s local path called {what}", self.cpu);
        }
    }

    /// `gate_only`, except in a frame-cap invocation's local path, which
    /// invalidates what it unmaps or remaps itself: a page (an unmap, a
    /// remap that raises rights) or the address space (a remap that lowers
    /// them, without `DEFER_FLUSH`), shooting other cores down under
    /// `CALL_LOCK` (fl4-arch-x86_64 smp.rs). Whether it returns true: such
    /// a local path made it.
    fn local_tlb(&self, what: &str) -> bool {
        let Some(c) = &self.conc else { return false };
        let cpu = self.cpu as usize;
        let local = c.footprint[cpu].lock().unwrap().is_some();
        assert!(!local || c.local_tlb[cpu].load(Ordering::SeqCst), "footprint: core {cpu}'s local path called {what}");
        local
    }

    fn apply(&self, e: Effect) {
        let cpu = self.cpu as usize;
        let mut m = self.m.lock().unwrap();
        if let Some(log) = &mut m.effects {
            log.push(e);
        }
        match e {
            Effect::Deadline(t) => m.cores[cpu].deadline = t,
            Effect::Reschedule(mask) => {
                for c in 0..m.cores.len() {
                    if mask & (1 << c) != 0 && c != cpu {
                        m.cores[c].pending[(irq::RESCHEDULE_IPI / 64) as usize] |= 1 << (irq::RESCHEDULE_IPI % 64);
                    }
                }
            }
            Effect::Putc(b) => m.console.push(b),
            Effect::PortOut(p, n, v) => m.ports.push((p, n, v)),
            Effect::Ack(irq) => {
                // Exactly the interrupt in service, once.
                let got = m.cores[cpu].in_service.take();
                assert_eq!(got, Some(irq), "core {cpu} ended interrupt {irq} with {got:?} in service");
            }
            Effect::SetVSpace(root, asid) => m.cores[cpu].vspace = (root, asid),
            Effect::Now(_) => unreachable!("SimArch::now records its reads"),
        }
    }
}

/// 1 tick = 1/100 us: a 100 MHz clock.
const TICKS_PER_US: u64 = 100;

impl Arch for SimArch {
    fn tdx_active(&self) -> bool {
        self.m.lock().unwrap().tdx
    }
    fn tdx_report(&mut self, frame: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> u64 {
        self.gate_only("tdx_report");
        self.m.lock().unwrap().tdx_reports.push(frame);
        0
    }
    fn now(&mut self) -> u64 {
        let mut m = self.m.lock().unwrap();
        // Time passes during kernel entries too, and now and then a lot
        // of it: a core descheduled by its hypervisor for 2 s, which
        // charges the running SC dozens of budgets at once.
        let d = if m.rng.below(4000) == 0 { 2_000_000 * TICKS_PER_US } else { 1 + m.rng.below(50) };
        m.now += d;
        let now = m.now;
        if let Some(log) = &mut m.effects {
            log.push(Effect::Now(now));
        }
        now
    }
    fn set_deadline(&mut self, ticks: u64) {
        self.apply(Effect::Deadline(ticks));
    }
    fn us_to_ticks(&self, us: u64) -> u64 {
        us.saturating_mul(TICKS_PER_US)
    }
    fn ticks_to_us(&self, ticks: u64) -> u64 {
        ticks / TICKS_PER_US
    }
    fn max_us(&self) -> u64 {
        u64::MAX / TICKS_PER_US
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        10 * TICKS_PER_US
    }
    fn irq_pending(&mut self) -> bool {
        let m = self.m.lock().unwrap();
        m.cores[self.cpu as usize].pending.iter().any(|w| *w != 0)
    }
    fn take_pending_irq(&mut self) -> u64 {
        self.gate_only("take_pending_irq");
        let mut m = self.m.lock().unwrap();
        let c = &mut m.cores[self.cpu as usize];
        for w in 0..3 {
            if c.pending[w] != 0 {
                let b = c.pending[w].trailing_zeros() as u64;
                c.pending[w] &= !(1 << b);
                let i = w as u64 * 64 + b;
                c.in_service = Some(i);
                return i;
            }
        }
        syscall::NO_IRQ
    }
    fn mask_irq(&mut self, _irq: u64, _mask: bool) {
        self.gate_only("mask_irq");
    }
    fn ack_irq(&mut self, irq: u64) {
        // A kernel timer interrupt's local path ends its own interrupt.
        let local_timer = irq == irq::TIMER && self.conc.as_ref().is_some_and(|c| c.local_timer[self.cpu as usize].load(Ordering::SeqCst));
        if !local_timer {
            self.gate_only("ack_irq");
        }
        self.apply(Effect::Ack(irq));
    }
    fn set_vspace(&mut self, root: u64, asid: u64) {
        self.apply(Effect::SetVSpace(root, asid));
    }
    // The simulator has no TLBs: it checks who invalidates them.
    fn invalidate_page(&mut self, _asid: u64, _vaddr: u64) {
        if self.local_tlb("invalidate_page") {
            LOCAL_COUNTS.lock().unwrap().tlb_page += 1;
        }
    }
    fn invalidate_asid(&mut self, _asid: u64) {
        if self.local_tlb("invalidate_asid") {
            LOCAL_COUNTS.lock().unwrap().tlb_asid += 1;
        }
    }
    fn invalidate_page_structures(&mut self, _asid: u64) {
        self.gate_only("invalidate_page_structures");
    }
    fn ioapic_map(&mut self, _i: u64, _p: u64, _l: u64, _q: u64, _v: u64) -> bool {
        self.gate_only("ioapic_map");
        true
    }
    fn ioapic_map_remapped(&mut self, _i: u64, _p: u64, _l: u64, _q: u64, _v: u64, _h: u64) -> bool {
        self.gate_only("ioapic_map_remapped");
        true
    }
    fn num_ioapics(&self) -> u64 {
        1
    }
    fn ioapic_pins(&self, _i: u64) -> u64 {
        24
    }
    fn port_in(&mut self, port: u64, size: u64) -> u64 {
        (port * 0x9e37 ^ 0x5a5a) & ((1 << (8 * size)) - 1)
    }
    fn port_out(&mut self, port: u64, size: u64, v: u64) {
        self.apply(Effect::PortOut(port, size, v));
    }
    fn fpu_flush(&mut self, _tcb: u64) {
        self.gate_only("fpu_flush");
    }
    fn fpu_sanitise(&mut self, _tcb: u64) {
        self.gate_only("fpu_sanitise");
    }
    fn fpu_reload(&mut self, _tcb: u64) {
        self.gate_only("fpu_reload");
    }
    fn fpu_release(&mut self, _tcb: u64) {
        self.gate_only("fpu_release");
    }
    fn remote_stall(&mut self, cpu: u64) {
        self.gate_only("remote_stall");
        match &self.conc {
            // Entries run one at a time: the target services the stall at
            // once, on the gate holder's behalf.
            None => {
                let mut s = SimStore { mem: self.mem.clone(), ks_base: self.ks_base, cpu, conc: None, peek: false };
                let mut a = SimArch { cpu, ..self.clone() };
                fl4_core::smp::stall(&mut s, &mut a);
                fl4_core::smp::send_pending(&mut s, &mut a);
            }
            Some(c) => {
                // Ask the target and wait until it has serviced the stall.
                c.call_pending.fetch_or(1 << cpu, Ordering::SeqCst);
                while c.call_pending.load(Ordering::SeqCst) & (1 << cpu) != 0 {
                    c.spin(self.cpu);
                }
            }
        }
    }
    fn send_reschedule(&mut self, mask: u64) {
        self.gate_only("send_reschedule");
        self.apply(Effect::Reschedule(mask));
    }
    fn putc(&mut self, c: u64) {
        self.apply(Effect::Putc(c as u8));
    }
    fn get_char(&mut self) -> u64 {
        u64::MAX
    }
    fn halt(&mut self) {
        // seL4_DebugHalt (or a debug call that halts on bad arguments)
        // stops the machine: the run ends there.
        self.m.lock().unwrap().halted = true;
    }
}

/// The serial gate of the simulated machine.
static GATE: SerialGate = SerialGate::new();

/// The simulator's side of `fl4_sync::run_entry`.
struct SimEnv {
    s: SimStore,
    a: SimArch,
    conc: Arc<Conc>,
}

impl SimEnv {
    /// Service a remote stall addressed to this core, if any.
    fn service(&self) -> bool {
        let me = 1u64 << self.s.cpu;
        if self.conc.call_pending.load(Ordering::SeqCst) & me == 0 {
            return false;
        }
        let mut s = self.s.clone();
        let mut a = self.a.clone();
        fl4_core::smp::stall(&mut s, &mut a);
        // As the kernels' `service_remote`: the stalled thread may be
        // queued on another core, which is owed a reschedule IPI.
        fl4_core::smp::send_pending(&mut s, &mut a);
        // The acknowledgement is a locked instruction: it drains.
        s.drain();
        self.conc.call_pending.fetch_and(!me, Ordering::SeqCst);
        true
    }
}

impl fl4_sync::EntryEnv for SimEnv {
    type S = SimStore;
    type A = SimArch;
    type M = SimStore;
    fn cpu(&self) -> u64 {
        self.s.cpu
    }
    fn multi(&self) -> bool {
        true
    }
    fn store(&self) -> SimStore {
        self.s.clone()
    }
    fn arch(&self) -> SimArch {
        self.a.clone()
    }
    fn mem(&self) -> &SimStore {
        &self.s
    }
    // Called while waiting for the serial gate.
    fn service_remote(&self) -> bool {
        let r = self.service();
        self.conc.spin(self.s.cpu);
        r
    }
    fn holding_gate(&self) {
        self.conc.gate_held[self.s.cpu as usize].store(true, Ordering::SeqCst);
    }
    fn count(&self, what: fl4_sync::Count) {
        let mut st = STATS.lock().unwrap();
        match what {
            fl4_sync::Count::Serial => st.0 += 1,
            fl4_sync::Count::Local => st.1 += 1,
        }
    }
}

/// Entries run under the gate, and syscalls whose local path ran beside it.
static STATS: Mutex<(u64, u64)> = Mutex::new((0, 0));

/// The footprint oracle (DESIGN.md §10): the memory a local path beside
/// the gate on core `cpu` may write, as (address, bytes): the core's
/// node state, threads on the core and their IPC buffers, scheduling
/// contexts on the core, the timer links of the threads in the core's
/// timer tree, and the objects it holds (`locked`: endpoints 16 bytes
/// long, notifications 64), with the queue links of the threads queued on
/// a locked endpoint or waiting notification, which belong to the queue.
/// Of a thread on the core, not the queue links while it is blocked on an
/// endpoint or notification (they belong to that object's queue), nor its
/// timer fields while it is armed in another core's tree (`fl4_core::localtimer`'s
/// Timer ownership: that core's). Read without scheduling points, once
/// the path holds its locks (`fl4_sync::local_syscall`'s `observe`).
fn footprint(s: &SimStore, ncores: u64, cpu: u64, locked: &[(u64, u64)]) -> Vec<(u64, u64)> {
    let s = SimStore { conc: None, ..s.clone() };
    let mut v = vec![(fl4_core::obj::node_base(&s, cpu), node::SIZE)];
    // TIMER_LEFT, _RIGHT, _PARENT and _HEIGHT, adjacent, after
    // TIMER_DEADLINE and _BADGE; EP_NEXT and EP_PREV, adjacent.
    const _: () = assert!(tl::TIMER_HEIGHT == tl::TIMER_LEFT + 24 && tl::TIMER_LEFT == tl::TIMER_DEADLINE + 16);
    const _: () = assert!(tl::EP_PREV == tl::EP_NEXT + 8);
    let tree: HashSet<u64> = timer_tree(&s, cpu).into_iter().collect();
    for &u in &tree {
        v.push((u + tl::TIMER_LEFT, 32));
    }
    for &(o, n) in locked.iter().filter(|o| o.0 != 0) {
        v.push((o, n));
        let queue = n == 16 || (n == 64 && fl4_core::obj::Ntfn(o).state(&s) == fl4_core::obj::NTFN_WAITING);
        if queue {
            let mut t = s.read(o);
            let mut fuel = 10_000;
            while t != 0 && fuel > 0 {
                // EP_NEXT and EP_PREV, adjacent.
                v.push((t + tl::EP_NEXT, 16));
                t = Tcb(t).ep_next(&s);
                fuel -= 1;
            }
        }
    }
    let mut scs = vec![node_get(&s, cpu, node::CUR_SC), node_get(&s, cpu, node::IDLE_SC)];
    for c in 0..ncores {
        let mut t = node_get(&s, c, node::DEBUG_TCBS);
        while t != 0 {
            let tt = Tcb(t);
            scs.push(tt.sc(&s));
            if tt.affinity(&s) == cpu {
                let mut holes = Vec::new();
                if tt.timer_deadline(&s) != 0 && !tree.contains(&t) {
                    holes.push((t + tl::TIMER_DEADLINE, 48));
                }
                let st = tt.state(&s);
                if st == sched::TS_BLOCKED_ON_SEND || st == sched::TS_BLOCKED_ON_RECV || st == sched::TS_BLOCKED_ON_NTFN {
                    holes.push((t + tl::EP_NEXT, 16));
                }
                push_except(&mut v, (t, 1 << fl4_abi::consts::bits::TCB), &mut holes);
                let buf = fl4_core::msg::lookup_ipc_buffer(&s, true, tt);
                if buf != 0 {
                    v.push((buf, 1 << fl4_abi::consts::bits::IPC_BUFFER));
                }
            }
            t = tt.debug_next(&s);
        }
    }
    for sc in scs {
        let c = fl4_core::obj::Sc(sc);
        if sc != 0 && c.cpu(&s) == cpu {
            v.push((sc, fl4_core::layout::sc::REFILLS + c.refill_max(&s) * fl4_core::layout::sc::REFILL_SIZE));
        }
    }
    v
}

/// Region `r`, as (address, bytes), without the regions `holes` (inside
/// it, not overlapping), into `v`.
fn push_except(v: &mut Vec<(u64, u64)>, r: (u64, u64), holes: &mut [(u64, u64)]) {
    holes.sort();
    let mut at = r.0;
    for &(h, n) in holes.iter() {
        assert!(h >= at && h + n <= r.0 + r.1, "footprint: hole {h:#x}+{n} outside {:#x}+{}", r.0, r.1);
        if h > at {
            v.push((at, h - at));
        }
        at = h + n;
    }
    if at < r.0 + r.1 {
        v.push((at, r.0 + r.1 - at));
    }
}

/// The nodes of core `cpu`'s timer tree, from its root (at most 100 000).
fn timer_tree(s: &SimStore, cpu: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut stack = vec![node_get(s, cpu, node::TIMER_ROOT)];
    while let Some(u) = stack.pop() {
        if u == 0 || out.len() >= 100_000 {
            continue;
        }
        out.push(u);
        stack.push(Tcb(u).timer_left(s));
        stack.push(Tcb(u).timer_right(s));
    }
    out
}

/// The footprint oracle: every word the local path for `what` (a syscall,
/// a VM fault) on core `cpu` wrote lies in `allowed` (`Sim::footprint`).
fn check_footprint(cpu: u64, what: &str, allowed: &[(u64, u64)], writes: impl Iterator<Item = u64>) {
    for w in writes {
        assert!(
            allowed.iter().any(|&(a, n)| w >= a && w < a + n),
            "footprint: core {cpu}'s local path for {what} wrote {w:#x}, outside its footprint"
        );
    }
}

/// Run a local path beside the gate on core `cpu` under the footprint
/// oracle: `path` runs it with `observe`, which reads its footprint once
/// it holds its locks; every word it wrote must lie in that footprint, and
/// one that never took its locks must have written nothing. `tlb`: it is a
/// frame-cap invocation's, which may invalidate TLB entries.
fn under_footprint(conc: &Conc, ncores: u64, cpu: u64, what: &str, tlb: bool, path: impl FnOnce(&mut dyn FnMut(&SimStore, &[(u64, u64)])) -> bool) -> bool {
    let mut allowed = None;
    *conc.footprint[cpu as usize].lock().unwrap() = Some(Vec::new());
    conc.local_tlb[cpu as usize].store(tlb, Ordering::SeqCst);
    let ran = path(&mut |s: &SimStore, held: &[(u64, u64)]| allowed = Some(footprint(s, ncores, cpu, held)));
    conc.local_tlb[cpu as usize].store(false, Ordering::SeqCst);
    let writes = conc.footprint[cpu as usize].lock().unwrap().take().unwrap();
    match &allowed {
        Some(allowed) => check_footprint(cpu, what, allowed, writes.into_iter()),
        None => assert!(writes.is_empty(), "footprint: core {cpu}'s local path for {what} wrote {:#x} without its locks", writes[0]),
    }
    ran
}

/// xorshift64*, seeded.
#[derive(Clone, PartialEq, Debug)]
struct Rng(u64);

/// The workload's RNG state for `seed`.
fn seed_rng(seed: u64) -> u64 {
    seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1
}

/// The seed boot runs with, whatever the run's: every run of a campaign
/// starts from the same booted state, which the campaign boots once and
/// forks (`spawn`).
const BOOT_SEED: u64 = 0;

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
}

#[derive(Clone)]
struct Sim {
    s: SimStore,
    a: SimArch,
    ncores: u64,
    /// Root CNode slots holding objects the workload created.
    objs: Vec<u64>,
    next_slot: u64,
    /// Root CNode slots of the workers' fault endpoint and the root task's
    /// reply object: the root task serves the workers' faults.
    fault_ep: u64,
    reply: u64,
    /// A targeted scenario (`--scenario`, DESIGN.md §10): the root CNode
    /// slot most calls go to, and the object type the root task keeps
    /// deleting and retyping there.
    focus: Option<(u64, u64)>,
    /// A small untyped the root task retypes a TCB from and deletes again,
    /// so each retype resets it (`Store::clear_free`, while other cores
    /// run local paths).
    reset_ut: u64,
    reset_child: u64,
    /// An IoPort cap for ports 0x60-0x6f, which the root task reads and
    /// writes (out of range too).
    port: u64,
    /// `--scenario guest`: l4h vCPUs, each a handler thread waiting in
    /// ReplyRecv on an endpoint and a thread with trapSyscalls faulting to
    /// it, both on one core: (handler, trapping thread, endpoint slot,
    /// handler's reply slot, handler's TCB slot).
    guest: Vec<(Tcb, Tcb, u64, u64, u64)>,
    /// `--scenario timer`: every worker with a notification bound, which
    /// its TCB timer signals, and a reply object of its own.
    timer: Vec<TimerWorker>,
    /// `--scenario timer`: an endpoint per core, which its workers wait on
    /// in `Recv` (woken by their timers through `cancel_ipc`) and send to.
    timer_eps: Vec<u64>,
    /// `first_untyped`'s last answer: (slot, size).
    big_ut: Cell<(u64, u64)>,
    /// Empty root CNode slots for copies of frame caps, each with a small
    /// page of the root VSpace (one whose page table exists) to map its
    /// copy at: (slot, vaddr). The root task copies, mints, maps and
    /// deletes in them, and workers delete, as a guest's pager does
    /// (`fl4_core::localinv`).
    frame_slots: Vec<(u64, u64)>,
}

fn pptr(p: u64) -> u64 {
    p + PPTR_BASE
}

/// A `--scenario timer` worker: its TCB and its root CNode slots (TCB,
/// bound notification, reply object).
#[derive(Clone, Copy)]
struct TimerWorker {
    tcb: Tcb,
    slot: u64,
    ntfn: u64,
    reply: u64,
}

/// How many `Sim::frame_slots`.
const FRAME_SLOTS: u64 = 6;

/// `seL4_CapRights_t` with every right (bit 0 write, 1 read, 2 grant,
/// 3 grant reply), and with read only.
const ALL_RIGHTS: u64 = 0xf;
const READ_ONLY: u64 = 2;

/// A user address under no page table of the root VSpace.
const UNMAPPED_VA: u64 = 0x1000_0000_0000;

impl Sim {
    fn new(seed: u64, ncores: u64) -> Sim {
        let mem = Arc::new(Memory {
            words: zeroed_words((MEM_BYTES / 8) as usize),
            dirty: zeroed_flags((MEM_BYTES / 32) as usize),
            dirty_list: Mutex::new(Vec::new()),
            watch: Mutex::new(SlotWatch::default()),
            undo: Mutex::new(None),
            logging: AtomicBool::new(false),
        });
        let image = MEM_BYTES - IMAGE_BYTES;
        let ks_base = pptr(image);
        let m = Arc::new(Mutex::new(Machine {
            now: 1_000_000,
            cores: vec![Core::default(); ncores as usize],
            console: Vec::new(),
            ports: Vec::new(),
            halted: false,
            tdx: false,
            tdx_reports: Vec::new(),
            effects: None,
            rng: Rng(seed_rng(seed)),
        }));
        let s = SimStore { mem: mem.clone(), ks_base, cpu: 0, conc: None, peek: false };
        let a = SimArch { m, mem, ks_base, cpu: 0, conc: None };
        Sim { s, a, ncores, objs: Vec::new(), next_slot: 0, fault_ep: 0, reply: 0, focus: None, reset_ut: 0, reset_child: 0, port: 0, guest: Vec::new(), timer: Vec::new(), timer_eps: Vec::new(), big_ut: Cell::new((0, 0)), frame_slots: Vec::new() }
    }

    /// Run the kernel part of an entry: directly, or (concurrent mode)
    /// through fl4_sync::run_entry as the kernel does.
    fn enter(&mut self, irq: bool, body: impl FnMut(&mut SimStore, &mut SimArch)) {
        let mut body = body;
        let Some(conc) = self.s.conc.clone() else {
            return body(&mut self.s, &mut self.a);
        };
        let cpu = self.s.cpu as usize;
        conc.in_kernel[cpu].store(true, Ordering::SeqCst);
        let env = SimEnv { s: self.s.clone(), a: self.a.clone(), conc: conc.clone() };
        fl4_sync::run_entry(&env, &GATE, irq, &mut body);
        if conc.gate_held[cpu].swap(false, Ordering::SeqCst) {
            GATE.release(&self.s);
        }
        let stuck = self.a.m.lock().unwrap().cores[cpu].in_service;
        assert!(stuck.is_none(), "liveness: core {cpu} left the kernel with interrupt {stuck:?} accepted and never acknowledged");
        // Leaving the kernel (IRET, SYSRET after a serializing write)
        // drains the store buffer.
        self.s.drain();
        conc.in_kernel[cpu].store(false, Ordering::SeqCst);
    }

    /// Oracles may run: no other core is inside the kernel.
    fn quiet(&self) -> bool {
        match &self.s.conc {
            None => true,
            Some(c) => (0..self.ncores).all(|i| i == self.s.cpu || !c.in_kernel[i as usize].load(Ordering::SeqCst)),
        }
    }

    fn on(&mut self, cpu: u64) {
        self.s.cpu = cpu;
        self.a.cpu = cpu;
    }

    fn boot(&mut self) {
        if self.try_boot(&[], &[], 0).is_err() {
            panic!("create_root_task failed");
        }
    }

    /// Boot with `more_devices` after the standard device regions, and
    /// `backend` (`backend_len` bytes of it) as the backend's extra
    /// BootInfo records.
    fn try_boot(&mut self, more_devices: &[Region], backend: &[u64], backend_len: u64) -> Result<(), boot::BootError> {
        let image = MEM_BYTES - IMAGE_BYTES;
        let idle_base = pptr(image + (1 << 20));
        let extra = pptr(image + (2 << 20));
        // The "root task image": 4 pages at 1 MiB, mapped at 0x400000.
        let ui_p = 1 << 20;
        let mut p = BootParams {
            free: [Region::EMPTY; MAX_REGIONS],
            n_free: 1,
            zeroed: [Region::EMPTY; MAX_REGIONS],
            n_zeroed: 0,
            device: [Region::EMPTY; MAX_REGIONS],
            n_device: 2,
            ui_p_start: ui_p,
            ui_p_end: ui_p + 4 * 4096,
            pv_offset: ui_p.wrapping_sub(0x40_0000),
            v_entry: 0x40_0000,
            extra_bi: extra,
            extra_bi_len: backend_len,
            num_nodes: self.ncores,
            idle_base,
            idle_stride: 8192,
            kernel_image: Region { start: pptr(image), end: pptr(MEM_BYTES) },
        };
        p.free[0] = Region { start: pptr(2 << 20), end: pptr(image) };
        p.device[0] = Region { start: MEM_BYTES, end: MEM_BYTES + (1 << 30) };
        // A 64-bit BAR far above the kernel window, where physical and
        // pointer alignment differ (GitHub issue #2).
        p.device[1] = Region { start: 0x3800_0000_0000, end: 0x3800_0000_0000 + (1 << 44) };
        for (i, &r) in more_devices.iter().enumerate() {
            p.device[2 + i] = r;
            p.n_device += 1;
        }
        for (i, &w) in backend.iter().enumerate() {
            self.s.write(extra + 8 * i as u64, w);
        }
        self.on(0);
        let ks_base = self.s.ks_base;
        self.s.zero(ks_base, ks::SIZE);
        let root = pptr(image + (3 << 20));
        fl4_core::obj::ks_set(&mut self.s, ks::KERNEL_ROOT, root);
        boot::create_root_task(&mut self.s, &mut self.a, &mut p)?;
        sched::schedule(&mut self.s, &mut self.a);
        sched::activate_thread(&mut self.s, &mut self.a);
        let bi = 0x40_0000 + 4 * 4096 + 4096;
        let _ = bi;
        self.next_slot = self.first_empty();
        self.check("boot");
        Ok(())
    }

    /// The first empty slot BootInfo reports (seL4_BootInfo.empty.start).
    fn first_empty(&self) -> u64 {
        let rt = self.root_cnode();
        (rs::NumInitialCaps..(1 << boot::ROOT_CNODE_BITS)).find(|&i| Slot::index(rt, i).cap(&self.s).is_null()).unwrap()
    }

    fn root_cnode(&self) -> u64 {
        match Tcb(self.root_tcb()).slot(tl::SLOT_CTABLE).cap(&self.s) {
            Cap::CNode { ptr, .. } => ptr,
            c => panic!("root CNode cap is {:?}", cap_name(c)),
        }
    }

    fn root_tcb(&self) -> u64 {
        let rt_slot = self.root_cnode_slot(rs::InitThreadTCB);
        match rt_slot {
            Cap::Thread { ptr } => ptr,
            _ => 0,
        }
    }

    fn root_cnode_slot(&self, i: u64) -> Cap {
        // Find the root CNode through any core's debug list: the root
        // server is the TCB named "rootserver".
        let t = self.find_thread(|s, t| name_of(s, t) == "rootserver").expect("root server");
        let rt = match t.slot(tl::SLOT_CTABLE).cap(&self.s) {
            Cap::CNode { ptr, .. } => ptr,
            _ => panic!("no root CNode"),
        };
        Slot::index(rt, i).cap(&self.s)
    }

    fn threads(&self) -> Vec<Tcb> {
        let mut v = Vec::new();
        for c in 0..self.ncores {
            let mut t = node_get(&self.s, c, node::DEBUG_TCBS);
            let mut fuel = 100_000;
            while t != 0 && fuel > 0 {
                v.push(Tcb(t));
                t = Tcb(t).debug_next(&self.s);
                fuel -= 1;
            }
            assert!(fuel > 0, "debug TCB list of core {c} does not end");
        }
        v
    }

    fn find_thread(&self, f: impl Fn(&SimStore, Tcb) -> bool) -> Option<Tcb> {
        self.threads().into_iter().find(|&t| f(&self.s, t))
    }

    // ---- the workload ---------------------------------------------------

    /// Run a syscall as the current thread of `cpu`.
    fn syscall(&mut self, cpu: u64, number: i64, cptr: u64, info: u64, mrs: [u64; 4]) {
        self.load_syscall(cpu, number, cptr, info, mrs);
        if FASTPATH_DIFF.load(Ordering::Relaxed) && self.s.conc.is_none() {
            return self.diff_syscall(number);
        }
        // A frame-cap invocation: not a trapped syscall, and by its label
        // (as fl4_sync::local_syscall chooses `local_invocation`). The flags
        // are read without a scheduling point: only a stall, under the
        // gate, changes them, and this core's stores are drained.
        let t = sched::cur_thread(&self.s);
        let flags = t.flags(&SimStore { conc: None, ..self.s.clone() });
        let trap = flags & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0;
        let inv = !trap && number == sc::SysCall && fl4_core::localinv::is_local_label(info >> 12);
        let set_timer = !trap && number == sc::SysCall && info >> 12 == label::TCBSetTimer;
        self.enter_syscall(number, inv, set_timer);
    }

    /// The current thread of `cpu` executes a syscall instruction: its
    /// registers as the kernel entry saves them.
    fn load_syscall(&mut self, cpu: u64, number: i64, cptr: u64, info: u64, mrs: [u64; 4]) {
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        if TRACE.load(Ordering::Relaxed) {
            let c = self.objs.iter().position(|&o| o == cptr).map(|_| {
                let cap = Slot::index(self.root_cnode(), cptr).cap(&self.s);
                cap_kind(cap)
            });
            println!(
                "  core {cpu} thread {:#x} ({}) syscall {number} cptr {cptr} {:?} label {} len {} mrs {:x?}",
                t.0,
                name_of(&self.s, t),
                c,
                info >> 12,
                info & 127,
                mrs
            );
        }
        t.set_reg(&mut self.s, reg::CAP, cptr);
        t.set_reg(&mut self.s, reg::MSG_INFO, info);
        t.set_reg(&mut self.s, reg::R10, mrs[0]);
        t.set_reg(&mut self.s, reg::R8, mrs[1]);
        t.set_reg(&mut self.s, reg::R9, mrs[2]);
        t.set_reg(&mut self.s, reg::R15, mrs[3]);
        t.set_reg(&mut self.s, reg::RDX, number as u64);
        let ip = t.reg(&self.s, reg::NEXT_IP);
        t.set_reg(&mut self.s, reg::NEXT_IP, ip.wrapping_add(2));
    }

    /// The thread a `TCB_SetTimer` of the current thread names, as the
    /// workload addresses caps (a root CNode slot), and its deadline then:
    /// for `LocalCounts`. Read without scheduling points.
    fn set_timer_target(&self) -> (Tcb, u64) {
        let s = SimStore { conc: None, ..self.s.clone() };
        let t = sched::cur_thread(&s);
        match fl4_core::cspace::lookup_slot(&s, t, t.reg(&s, reg::CAP)) {
            Ok(r) => match r.slot.cap(&s) {
                Cap::Thread { ptr } => (Tcb(ptr), Tcb(ptr).timer_deadline(&s)),
                _ => (Tcb(0), 0),
            },
            Err(_) => (Tcb(0), 0),
        }
    }

    /// Count a `TCB_SetTimer`'s local attempt: it ran (`ran`), with the
    /// deadline of `target` `d_old` before.
    fn count_set_timer(&self, ran: bool, target: Tcb, d_old: u64) {
        let s = self.s.peek();
        let mut c = LOCAL_COUNTS.lock().unwrap();
        c.set_timer_tried += 1;
        if ran {
            c.set_timer_ran += 1;
            c.set_timer_disarm += (target.timer_deadline(&s) == 0) as u64;
            c.set_timer_rearm += (d_old != 0) as u64;
        }
    }

    /// A VM fault (a page fault, error code `code`, at `addr`) of the
    /// current thread of `cpu`, as the kernel takes one (fl4-kernel
    /// entry.rs): the thread's registers saved with `FAULT_IP` at the
    /// faulting instruction, then `fl4_sync::run_vm_fault`; serially,
    /// `handle_vm_fault`.
    fn vm_fault(&mut self, cpu: u64, addr: u64, code: u64) {
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        if TRACE.load(Ordering::Relaxed) {
            println!("  core {cpu} thread {:#x} ({}) VM fault at {addr:#x} code {code:#x}", t.0, name_of(&self.s, t));
        }
        let ip = t.reg(&self.s, reg::NEXT_IP);
        t.set_reg(&mut self.s, reg::FAULT_IP, ip);
        if FASTPATH_DIFF.load(Ordering::Relaxed) && self.s.conc.is_none() {
            return self.diff_vm_fault(addr, code);
        }
        self.enter_vm_fault(addr, code);
    }

    /// A VM fault's kernel entry (fl4_sync::run_vm_fault, its local path
    /// under the footprint oracle); serially, `handle_vm_fault`.
    fn enter_vm_fault(&mut self, addr: u64, code: u64) {
        let Some(conc) = self.s.conc.clone() else {
            return syscall::handle_vm_fault(&mut self.s, &mut self.a, addr, code);
        };
        let cpu = self.s.cpu as usize;
        conc.in_kernel[cpu].store(true, Ordering::SeqCst);
        let env = SimEnv { s: self.s.clone(), a: self.a.clone(), conc: conc.clone() };
        let m = self.s.clone();
        let ncores = self.ncores;
        let local = |s: &mut SimStore, a: &mut SimArch| {
            let ran = under_footprint(&conc, ncores, cpu as u64, "a VM fault", false, |observe| fl4_sync::local_vm_fault(s, a, &m, addr, code, |s, held| observe(s, held)));
            let mut c = LOCAL_COUNTS.lock().unwrap();
            c.vm_fault_tried += 1;
            c.vm_fault_ran += ran as u64;
            ran
        };
        fl4_sync::run_vm_fault(&env, &GATE, local, |s, a| syscall::handle_vm_fault(s, a, addr, code));
        self.leave_kernel(&conc);
    }

    /// The end of an entry made with `fl4_sync`: release the gate if this
    /// core holds it, check that no accepted interrupt is left
    /// unacknowledged, and drain the store buffer (IRET, SYSRET after a
    /// serializing write).
    fn leave_kernel(&mut self, conc: &Conc) {
        let cpu = self.s.cpu as usize;
        if conc.gate_held[cpu].swap(false, Ordering::SeqCst) {
            GATE.release(&self.s);
        }
        let stuck = self.a.m.lock().unwrap().cores[cpu].in_service;
        assert!(stuck.is_none(), "liveness: core {cpu} left the kernel with interrupt {stuck:?} accepted and never acknowledged");
        self.s.drain();
        conc.in_kernel[cpu].store(false, Ordering::SeqCst);
    }

    /// `--fastpath-diff` for a VM fault: the local path
    /// (`fl4_sync::local_vm_fault`, under the footprint oracle) and, if it
    /// declined, `handle_vm_fault`, as a core entering beside the gate
    /// takes it; undone, then `handle_vm_fault` alone; both must end in the
    /// same memory and machine state.
    fn diff_vm_fault(&mut self, addr: u64, code: u64) {
        let mem = self.s.mem.clone();
        let m0 = self.start_diff();
        let cpu = self.s.cpu;
        let ncores = self.ncores;
        let time0 = node_get(&self.s, cpu, node::CUR_TIME);
        let mut allowed = None;
        let locks = SimStore { conc: None, ..self.s.clone() };
        mem.start_log();
        let ran_local = fl4_sync::local_vm_fault(&mut self.s, &mut self.a, &locks, addr, code, |s, held| allowed = Some(footprint(s, ncores, cpu, held)));
        // A local attempt that declined after reading the clock.
        let read_clock = !ran_local && node_get(&self.s, cpu, node::CUR_TIME) != time0;
        if !ran_local {
            syscall::handle_vm_fault(&mut self.s, &mut self.a, addr, code);
        }
        let fast_log = mem.take_log();
        if ran_local {
            check_footprint(cpu, "a VM fault", allowed.as_ref().unwrap(), fast_log.iter().map(|&(i, _)| PPTR_BASE + i as u64 * 8));
        }
        {
            let mut c = LOCAL_COUNTS.lock().unwrap();
            c.vm_fault_tried += 1;
            c.vm_fault_ran += ran_local as u64;
        }
        let what = format!("VM fault at {addr:#x} code {code:#x} (locally: {ran_local})");
        self.diff_general(&what, m0, fast_log, read_clock, |s, a| syscall::handle_vm_fault(s, a, addr, code));
    }

    /// A syscall's kernel entry, as the kernel makes it (fl4_sync::
    /// run_syscall); serially, `handle_syscall`. `inv`: a frame-cap
    /// invocation (`localinv`), whose local path may invalidate TLB
    /// entries. `set_timer`: a `TCB_SetTimer`, by its label.
    fn enter_syscall(&mut self, number: i64, inv: bool, set_timer: bool) {
        let Some(conc) = self.s.conc.clone() else {
            return syscall::handle_syscall(&mut self.s, &mut self.a, number);
        };
        let cpu = self.s.cpu as usize;
        conc.in_kernel[cpu].store(true, Ordering::SeqCst);
        let env = SimEnv { s: self.s.clone(), a: self.a.clone(), conc: conc.clone() };
        let m = self.s.clone();
        let ncores = self.ncores;
        // The local path, under the footprint oracle. The footprint is
        // read once the path holds its locks: its core is active and its
        // objects locked, so nothing it reads changes meanwhile.
        let me = &*self;
        let local = |s: &mut SimStore, a: &mut SimArch| {
            let mut vm_reply = false;
            let what = format!("syscall {number}");
            // An NBWait candidate: not a trapped thread's syscall.
            let poll = number == sc::SysNBWait && sched::cur_thread(&*s).flags(&*s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS == 0;
            // (Read once the core is active: its timer tree is its own.)
            let (target, d_old) = if set_timer { me.set_timer_target() } else { (Tcb(0), 0) };
            let ran = under_footprint(&conc, ncores, cpu as u64, &what, inv, |observe| {
                fl4_sync::local_syscall(s, a, &m, number, |s, held| {
                    vm_reply = replies_to_vm_fault(s, held);
                    observe(s, held)
                })
            });
            if set_timer {
                me.count_set_timer(ran, target, d_old);
            }
            let mut c = LOCAL_COUNTS.lock().unwrap();
            c.inv_tried += inv as u64;
            c.inv_ran += (inv && ran) as u64;
            c.vm_reply_ran += (vm_reply && ran) as u64;
            c.poll_tried += poll as u64;
            c.poll_ran += (poll && ran) as u64;
            ran
        };
        fl4_sync::run_syscall(&env, &GATE, number, local, |s, a| syscall::handle_syscall_fast(s, a, number));
        self.leave_kernel(&conc);
    }

    /// A kernel timer interrupt `irq` the core has accepted, as the kernel
    /// takes it (fl4_sync::run_timer_irq, its local path under the
    /// footprint oracle); serially, `handle_interrupt_entry`.
    fn enter_timer_irq(&mut self, irq: u64) {
        let Some(conc) = self.s.conc.clone() else {
            return syscall::handle_interrupt_entry(&mut self.s, &mut self.a, irq);
        };
        let cpu = self.s.cpu as usize;
        conc.in_kernel[cpu].store(true, Ordering::SeqCst);
        let env = SimEnv { s: self.s.clone(), a: self.a.clone(), conc: conc.clone() };
        let m = self.s.clone();
        let ncores = self.ncores;
        let local = |s: &mut SimStore, a: &mut SimArch| {
            let mut snap = None;
            conc.local_timer[cpu].store(true, Ordering::SeqCst);
            let ran = under_footprint(&conc, ncores, cpu as u64, "a timer interrupt", false, |observe| {
                fl4_sync::local_timer_irq(s, a, &m, irq, |s, held| {
                    snap = Some(TimerSnap::take(s));
                    observe(s, held)
                })
            });
            conc.local_timer[cpu].store(false, Ordering::SeqCst);
            let case = snap.filter(|_| ran).map(|p| p.case(s));
            LOCAL_COUNTS.lock().unwrap().timer_irq(ran, case);
            ran
        };
        fl4_sync::run_timer_irq(&env, &GATE, local, |s, a| syscall::handle_interrupt_entry(s, a, irq));
        self.leave_kernel(&conc);
    }

    /// `--fastpath-diff` for a kernel timer interrupt `irq` the core has
    /// accepted: its local path (`fl4_sync::local_timer_irq`, under the
    /// footprint oracle) and, if it declined, `handle_interrupt_entry`, as
    /// a core taking it beside the gate does; undone, then
    /// `handle_interrupt_entry` alone; both must end in the same memory
    /// and machine state. Returns whether the local path ran.
    fn diff_timer_irq(&mut self, irq: u64) -> bool {
        let mem = self.s.mem.clone();
        let m0 = self.start_diff();
        let cpu = self.s.cpu;
        let ncores = self.ncores;
        let time0 = node_get(&self.s, cpu, node::CUR_TIME);
        let mut allowed = None;
        let mut snap = None;
        let locks = SimStore { conc: None, ..self.s.clone() };
        mem.start_log();
        let ran_local = fl4_sync::local_timer_irq(&mut self.s, &mut self.a, &locks, irq, |s, held| {
            snap = Some(TimerSnap::take(s));
            allowed = Some(footprint(s, ncores, cpu, held))
        });
        // A local attempt that declined after reading the clock.
        let read_clock = !ran_local && node_get(&self.s, cpu, node::CUR_TIME) != time0;
        if !ran_local {
            syscall::handle_interrupt_entry(&mut self.s, &mut self.a, irq);
        }
        let fast_log = mem.take_log();
        if ran_local {
            check_footprint(cpu, "a timer interrupt", allowed.as_ref().unwrap(), fast_log.iter().map(|&(i, _)| PPTR_BASE + i as u64 * 8));
        }
        let case = snap.filter(|_| ran_local).map(|p| p.case(&self.s));
        LOCAL_COUNTS.lock().unwrap().timer_irq(ran_local, case);
        let what = format!("timer interrupt {irq} (locally: {ran_local}, {case:?})");
        self.diff_general(&what, m0, fast_log, read_clock, |s, a| syscall::handle_interrupt_entry(s, a, irq));
        ran_local
    }

    /// `--fastpath-diff` (serial runs): the syscall through `handle_syscall`
    /// (or the local fast path first), undone, then through the general
    /// path; every word either wrote and the machine state (time, RNG,
    /// deadlines, effects, address space) must end the same.
    fn diff_syscall(&mut self, number: i64) {
        // Every other syscall as a core entering without the gate makes it
        // (fl4_sync::run_syscall): the local fast path, then all of
        // `handle_syscall` if it declined.
        let local = FASTPATH_COUNTS.lock().unwrap().0 % 2 == 0;
        self.diff_syscall_with(number, local);
    }

    /// `diff_syscall`, trying the local path first if `local` (and the
    /// syscall is a candidate); whether it ran.
    fn diff_syscall_with(&mut self, number: i64, local: bool) -> bool {
        let mem = self.s.mem.clone();
        let m0 = self.start_diff();
        let t = sched::cur_thread(&self.s);
        let trap = t.flags(&self.s) & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0;
        // The syscalls fl4_sync::run_syscall tries a local path for: a
        // trapped syscall, ReplyRecv, an I/O port access, or a frame-cap
        // invocation (`fl4_core::localinv`), by its label.
        let lbl = fl4_core::msg::msg_info(&self.s, t).label;
        let port = !trap && (number == sc::SysCall || number == sc::SysSend) && fl4_core::ioport::is_port_label(lbl);
        let local_inv = !trap && number == sc::SysCall && fl4_core::localinv::is_local_label(lbl);
        let set_timer = !trap && number == sc::SysCall && lbl == label::TCBSetTimer;
        let poll = !trap && number == sc::SysNBWait;
        let try_local = local && (trap || number == sc::SysReplyRecv || port || local_inv || set_timer || poll);
        let (target, d_old) = if set_timer { self.set_timer_target() } else { (Tcb(0), 0) };
        let cpu = self.s.cpu;
        let ncores = self.ncores;
        let time0 = node_get(&self.s, cpu, node::CUR_TIME);
        let mut allowed = None;
        let mut vm_reply = false;
        let locks = SimStore { conc: None, ..self.s.clone() };
        mem.start_log();
        let ran_local = try_local
            && fl4_sync::local_syscall(&mut self.s, &mut self.a, &locks, number, |s, held| {
                vm_reply = replies_to_vm_fault(s, held);
                allowed = Some(footprint(s, ncores, cpu, held))
            });
        // A local attempt that declined after reading the clock.
        let read_clock = try_local && !ran_local && node_get(&self.s, cpu, node::CUR_TIME) != time0;
        let fast = ran_local || syscall::handle_syscall_fast(&mut self.s, &mut self.a, number);
        let fast_log = mem.take_log();
        if ran_local {
            check_footprint(cpu, &format!("syscall {number}"), allowed.as_ref().unwrap(), fast_log.iter().map(|&(i, _)| PPTR_BASE + i as u64 * 8));
        }
        if set_timer && try_local {
            self.count_set_timer(ran_local, target, d_old);
        }
        {
            let mut c = LOCAL_COUNTS.lock().unwrap();
            c.inv_tried += (local_inv && try_local) as u64;
            c.inv_ran += (local_inv && ran_local) as u64;
            c.poll_tried += (poll && try_local) as u64;
            c.poll_ran += (poll && ran_local) as u64;
            c.vm_reply_ran += (vm_reply && ran_local) as u64;
        }
        {
            let mut c = FASTPATH_COUNTS.lock().unwrap();
            c.0 += 1;
            c.1 += fast as u64;
        }
        let what = format!("syscall {number} (fast path ran: {fast}, locally: {ran_local})");
        self.diff_general(&what, m0, fast_log, read_clock, |s, a| syscall::handle_syscall_general(s, a, number));
        ran_local
    }

    /// The first half of a `--fastpath-diff` check: record the entry's
    /// `Arch` effects from here (`Machine::effects`); the machine state it
    /// starts from.
    fn start_diff(&mut self) -> Machine {
        let mut m = self.a.m.lock().unwrap();
        m.effects = Some(Vec::new());
        m.clone()
    }

    /// The second half of a `--fastpath-diff` check: the entry `what` ran
    /// from machine state `m0` and wrote `fast_log` (and read the clock
    /// once more, `read_clock`, in a local attempt that declined); undo
    /// it, run `general` from the same state, and require every word
    /// either wrote and the machine state to end the same.
    fn diff_general(&mut self, what: &str, m0: Machine, fast_log: Vec<(usize, u64)>, read_clock: bool, general: impl FnOnce(&mut SimStore, &mut SimArch)) {
        let mem = self.s.mem.clone();
        let m_fast = self.a.m.lock().unwrap().clone();
        let mut orig: HashMap<usize, u64> = HashMap::new();
        let mut want: HashMap<usize, u64> = HashMap::new();
        for &(i, old) in &fast_log {
            orig.entry(i).or_insert(old);
            want.insert(i, mem.words[i].load(Ordering::Relaxed));
        }
        for &(i, old) in fast_log.iter().rev() {
            mem.words[i].store(old, Ordering::Relaxed);
        }
        *self.a.m.lock().unwrap() = m0;
        // A local attempt that declined read the clock once more. Here
        // reading it moves simulated time and the RNG; the kernel's clock
        // read changes nothing.
        if read_clock {
            let _ = self.a.now();
        }
        mem.start_log();
        general(&mut self.s, &mut self.a);
        for (i, old) in mem.take_log() {
            orig.entry(i).or_insert(old);
        }
        let mut bad: Vec<(u64, u64, u64, u64)> = orig
            .iter()
            .filter_map(|(&i, &o)| {
                let f = *want.get(&i).unwrap_or(&o);
                let g = mem.words[i].load(Ordering::Relaxed);
                (g != f).then_some((PPTR_BASE + i as u64 * 8, o, g, f))
            })
            .collect();
        bad.sort();
        let m_general = {
            let mut m = self.a.m.lock().unwrap();
            let g = m.clone();
            m.effects = None;
            g
        };
        // `Machine` includes the effects each made, in order.
        if !bad.is_empty() || m_fast != m_general {
            for (a, o, g, f) in &bad {
                println!("  {a:#x}: was {o:#x}, general {g:#x}, fast {f:#x}");
            }
            if m_fast != m_general {
                println!("  machine: general {m_general:?}\n  fast    {m_fast:?}");
            }
            panic!("fastpath: {what} left {} words and the machine state {} from the general path's", bad.len(), if m_fast == m_general { "equal" } else { "different" });
        }
    }

    /// Message words beyond the registers go in the IPC buffer.
    fn set_buffer_mr(&mut self, cpu: u64, i: u64, v: u64) {
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        let buf = fl4_core::msg::lookup_ipc_buffer(&self.s, false, t);
        if buf != 0 {
            fl4_core::msg::buf_set(&mut self.s, buf, i + 1, v);
        }
    }

    fn invoke(&mut self, cpu: u64, cptr: u64, lbl: u64, args: &[u64], extra_caps: &[u64]) {
        let mut mrs = [0u64; 4];
        for (i, &v) in args.iter().enumerate() {
            if i < 4 {
                mrs[i] = v;
            } else {
                self.set_buffer_mr(cpu, i as u64, v);
            }
        }
        for (i, &c) in extra_caps.iter().enumerate() {
            self.set_buffer_mr(cpu, fl4_core::msg::BUF_CAPS - 1 + i as u64, c);
        }
        let info = (lbl << 12) | ((extra_caps.len() as u64) << 7) | args.len() as u64;
        self.syscall(cpu, sc::SysCall, cptr, info, mrs);
    }

    /// Retype objects from the first untyped into free root CNode slots.
    fn setup(&mut self) {
        let ut = self.first_untyped();
        let plan: &[(u64, u64, u64)] = &[
            (ot::Endpoint, 0, 4),
            (ot::Notification, 0, 4),
            (ot::Reply, 0, 4),
            (ot::Tcb, 0, 8),
            // Room for 10 refills.
            (ot::SchedContext, bits::MIN_SCHED_CONTEXT + 1, 8),
            (ot::CapTable, 4, 2),
            (ot::X86Page4K, 0, 4),
        ];
        for &(ty, size, n) in plan {
            let dest = self.next_slot;
            self.invoke(0, ut, label::UntypedRetype, &[ty, size, rs::InitThreadCNode, 0, dest, n], &[rs::InitThreadCNode]);
            self.after("setup retype");
            for i in 0..n {
                if !Slot::index(self.root_cnode(), dest + i).cap(&self.s).is_null() {
                    self.objs.push(dest + i);
                }
            }
            self.next_slot += n;
        }
        let dest = self.next_slot;
        self.invoke(0, ut, label::UntypedRetype, &[ot::Untyped, 13, rs::InitThreadCNode, 0, dest, 1], &[rs::InitThreadCNode]);
        self.after("setup reset untyped");
        self.reset_ut = dest;
        self.reset_child = dest + 1;
        self.next_slot += 2;
        let dest = self.next_slot;
        self.invoke(0, rs::IOPortControl, label::X86IOPortControlIssue, &[0x60, 0x6f, dest, 64], &[rs::InitThreadCNode]);
        self.after("setup port");
        self.port = dest;
        self.next_slot += 1;
        // Slots for frame-cap copies, each with an unmapped small page of
        // the root VSpace under a page table that exists (the one over the
        // root task's image), so that a map can take the local path.
        let root = match self.root_cnode_slot(rs::InitThreadVSpace) {
            Cap::Pml4 { ptr, .. } => ptr,
            c => panic!("root VSpace cap is {:?}", cap_name(c)),
        };
        let free_pages = (0..512u64)
            .rev()
            .map(|i| 0x40_0000 + i * 4096)
            .filter(|&va| fl4_core::vspace::small_page_entry(&self.s, root, va).is_some_and(|e| self.s.read(e) == 0));
        let first = self.next_slot;
        let frame_slots = free_pages.take(FRAME_SLOTS as usize).enumerate().map(|(i, va)| (first + i as u64, va)).collect::<Vec<_>>();
        self.frame_slots = frame_slots;
        assert_eq!(self.frame_slots.len() as u64, FRAME_SLOTS, "setup: no room for frame-cap mappings in the root VSpace");
        self.next_slot += FRAME_SLOTS;
        // Give each new TCB a CSpace, VSpace, priority, an SC on some core,
        // and start it: these become the threads running random programs.
        let tcbs: Vec<u64> = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
        let scs: Vec<u64> = self.objs_of(|c| matches!(c, Cap::SchedContext { .. }));
        self.fault_ep = self.objs_of(|c| matches!(c, Cap::Endpoint { .. }))[0];
        self.reply = self.objs_of(|c| matches!(c, Cap::Reply { .. }))[0];
        let fault_ep = self.fault_ep;
        for (k, &t) in tcbs.iter().enumerate() {
            self.invoke(0, t, label::TCBSetSpace, &[0, 0], &[fault_ep, rs::InitThreadCNode, rs::InitThreadVSpace]);
            self.after("set space");
            self.invoke(0, t, label::TCBSetPriority, &[100 + k as u64 % 3], &[rs::InitThreadTCB]);
            self.after("sched params");
            if let Some(&scap) = scs.get(k) {
                let core = k as u64 % self.ncores;
                let ctrl = self.sched_control(core);
                // Full budget, or 30% of the period, some sporadic, so
                // threads run out of budget and the refill code runs.
                let budget = if k % 2 == 1 { 300 } else { 1000 } * TICKS_PER_US;
                let flags = if k % 3 == 1 { 1 } else { 0 };
                self.invoke(0, ctrl, label::SchedControlConfigureFlags, &[budget, 1000 * TICKS_PER_US, k as u64 % 4, k as u64, flags], &[scap]);
                self.after("sc configure");
                let sc = fl4_core::obj::Sc(Slot::index(self.root_cnode(), scap).cap(&self.s).ptr());
                assert!(fl4_core::sporadic::sc_active(&self.s, sc), "setup: SchedControl_ConfigureFlags failed");
                self.invoke(0, scap, label::SchedContextBind, &[], &[t]);
                self.after("sc bind");
            }
            self.invoke(0, t, label::TCBResume, &[], &[]);
            self.after("resume");
        }
    }

    /// `--scenario guest`: on each core but the root task's, the first two
    /// workers there become an l4h vCPU's user context, which traps its
    /// syscalls to an endpoint, and (the one of higher priority) its kernel
    /// thread, which serves them with ReplyRecv there through its own reply
    /// object and has a notification bound.
    fn setup_guest(&mut self) {
        let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
        let eps = self.objs_of(|c| matches!(c, Cap::Endpoint { .. }));
        let replies = self.objs_of(|c| matches!(c, Cap::Reply { .. }));
        let ntfns = self.objs_of(|c| matches!(c, Cap::Notification { .. }));
        let cap = |sim: &Sim, i: u64| Tcb(Slot::index(sim.root_cnode(), i).cap(&sim.s).ptr());
        // Half the runs share one endpoint among all the vCPUs, so fast
        // paths on different cores meet on it.
        let shared = self.a.m.lock().unwrap().rng.below(2) == 1;
        for core in 1..self.ncores.max(2) {
            let i = self.guest.len() + 1;
            if i >= eps.len().min(replies.len()).min(ntfns.len()) {
                break;
            }
            let on: Vec<u64> = (0..tcbs.len()).filter(|&k| k as u64 % self.ncores == core % self.ncores).map(|k| tcbs[k]).collect();
            if on.len() < 2 {
                continue;
            }
            let (a, b) = (on[0], on[1]);
            let (k, u) = if cap(self, a).prio(&self.s) > cap(self, b).prio(&self.s) { (a, b) } else { (b, a) };
            let (ep, reply) = (eps[if shared { 1 } else { i }], replies[i]);
            self.invoke(0, u, label::TCBSetSpace, &[0, 0], &[ep, rs::InitThreadCNode, rs::InitThreadVSpace]);
            self.after("guest fault endpoint");
            self.invoke(0, u, label::TCBSetFlags, &[0, fl4_abi::consts::tcb_flag::TRAP_SYSCALLS], &[]);
            self.after("guest trapSyscalls");
            self.invoke(0, k, label::TCBBindNotification, &[], &[ntfns[i]]);
            self.after("guest notification");
            let g = (cap(self, k), cap(self, u), ep, reply, k);
            self.guest.push(g);
        }
    }

    /// `--scenario timer`: each worker gets a notification bound and a
    /// reply object of its own, each core an endpoint; half the workers'
    /// SCs become round-robin with budgets of 40 to 80 us, which run out
    /// under load (the timer interrupt's round-robin case).
    fn setup_timer(&mut self) {
        let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
        let scs = self.objs_of(|c| matches!(c, Cap::SchedContext { .. }));
        let n = tcbs.len() as u64;
        let retype = |sim: &mut Sim, ty: u64, count: u64| {
            let ut = sim.first_untyped();
            let dest = sim.next_slot;
            sim.setup_invoke(ut, label::UntypedRetype, &[ty, 0, rs::InitThreadCNode, 0, dest, count], &[rs::InitThreadCNode]);
            sim.after("timer retype");
            sim.next_slot += count;
            for i in 0..count {
                assert!(!Slot::index(sim.root_cnode(), dest + i).cap(&sim.s).is_null(), "setup: timer scenario retype failed");
            }
            dest
        };
        let ntfn0 = retype(self, ot::Notification, n);
        let reply0 = retype(self, ot::Reply, n);
        let ncores = self.ncores;
        let ep0 = retype(self, ot::Endpoint, ncores);
        self.timer_eps = (0..ncores).map(|c| ep0 + c).collect();
        let cap = |sim: &Sim, i: u64| Tcb(Slot::index(sim.root_cnode(), i).cap(&sim.s).ptr());
        for (k, &t) in tcbs.iter().enumerate() {
            let k = k as u64;
            self.setup_invoke(t, label::TCBBindNotification, &[], &[ntfn0 + k]);
            self.after("timer notification");
            assert_eq!(cap(self, t).bound_ntfn(&self.s), Slot::index(self.root_cnode(), ntfn0 + k).cap(&self.s).ptr(), "setup: TCB_BindNotification failed");
            self.timer.push(TimerWorker { tcb: cap(self, t), slot: t, ntfn: ntfn0 + k, reply: reply0 + k });
        }
        for (k, &scap) in scs.iter().enumerate() {
            if k % 2 == 0 {
                // In microseconds, as SchedControl_ConfigureFlags takes them.
                let budget = 40 + 20 * (k as u64 % 3);
                let ctrl = self.sched_control(k as u64 % self.ncores);
                self.setup_invoke(ctrl, label::SchedControlConfigureFlags, &[budget, budget, 0, k as u64, 0], &[scap]);
                self.after("timer round-robin SC");
                let sc = fl4_core::obj::Sc(Slot::index(self.root_cnode(), scap).cap(&self.s).ptr());
                let head = fl4_core::sporadic::head(&self.s, sc).amount;
                assert!(sc.period(&self.s) == 0 && head == budget * TICKS_PER_US, "setup: round-robin SC of {budget} us has period {} and a head refill of {head} ticks", sc.period(&self.s));
            }
        }
    }

    /// The root task's invocation during setup (on core 0), made again
    /// while the kernel restarted it rather than ran it: its budget ran
    /// out at the entry (`check_budget_restart` rewinds it to the syscall,
    /// `NEXT_IP` to `FAULT_IP`).
    fn setup_invoke(&mut self, cptr: u64, lbl: u64, args: &[u64], extra_caps: &[u64]) {
        for _ in 0..8 {
            self.invoke(0, cptr, lbl, args, extra_caps);
            let t = sched::cur_thread(&self.s);
            let restarted = self.is_root(t) && t.reg(&self.s, reg::NEXT_IP) == t.reg(&self.s, reg::FAULT_IP);
            if !restarted {
                return;
            }
        }
        panic!("setup: the root task's invocation {lbl} was restarted 8 times");
    }

    fn sched_control(&self, core: u64) -> u64 {
        let rt = self.root_cnode();
        (rs::NumInitialCaps..self.next_slot)
            .find(|&i| matches!(Slot::index(rt, i).cap(&self.s), Cap::SchedControl { cpu } if cpu == core))
            .unwrap_or(0)
    }

    /// The largest RAM untyped in the root CNode (the first, of several).
    /// The root task knows where its caps are: it rescans only when the
    /// last answer's slot holds something else now.
    fn first_untyped(&self) -> u64 {
        let rt = self.root_cnode();
        let (slot, bits) = self.big_ut.get();
        if slot != 0 && matches!(Slot::index(rt, slot).cap(&self.s), Cap::Untyped { size_bits, is_device: false, .. } if size_bits == bits) {
            return slot;
        }
        let mut best = (0, 0);
        for i in rs::NumInitialCaps..(1 << boot::ROOT_CNODE_BITS) {
            if let Cap::Untyped { size_bits, is_device: false, .. } = Slot::index(rt, i).cap(&self.s) {
                if size_bits > best.1 {
                    best = (i, size_bits);
                }
            }
        }
        self.big_ut.set(best);
        best.0
    }

    fn objs_of(&self, f: impl Fn(Cap) -> bool) -> Vec<u64> {
        let rt = self.root_cnode();
        self.objs.iter().copied().filter(|&i| f(Slot::index(rt, i).cap(&self.s))).collect()
    }

    /// The root task's turn: mostly serve the workers' faults (reply with
    /// label 0, which restarts the faulting thread, and wait for the next),
    /// sometimes a random invocation on a valid cap (it has no fault
    /// handler, so it avoids cap faults).
    fn root_turn(&mut self, cpu: u64) {
        // Invoking an endpoint or notification could block the root task
        // for good (nobody would serve faults then): it invokes other objects.
        let targets = self.objs_of(|c| !matches!(c, Cap::Endpoint { .. } | Cap::Notification { .. } | Cap::Reply { .. }));
        let (serve, lbl, len, target, other) = {
            let mut g = self.a.m.lock().unwrap();
            let r = &mut g.rng;
            let n = self.objs.len() as u64;
            let t = if targets.is_empty() { 0 } else { targets[r.below(targets.len() as u64) as usize] };
            (r.below(10) < 7 || targets.is_empty(), r.below(80), r.below(6), t, self.objs[r.below(n) as usize])
        };
        let mode = self.a.m.lock().unwrap().rng.below(10);
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        t.set_reg(&mut self.s, reg::REPLY, self.reply);
        let _ = serve;
        if self.reset_ut != 0 && self.a.m.lock().unwrap().rng.below(4) == 0 {
            let child = self.reset_child;
            if Slot::index(self.root_cnode(), child).cap(&self.s).is_null() {
                let ut = self.reset_ut;
                self.invoke(cpu, ut, label::UntypedRetype, &[ot::Tcb, 0, rs::InitThreadCNode, 0, child, 1], &[rs::InitThreadCNode]);
            } else {
                self.invoke(cpu, rs::InitThreadCNode, label::CNodeDelete, &[child, 64], &[]);
            }
            return;
        }
        if let Some((slot, ty)) = self.focus {
            if self.a.m.lock().unwrap().rng.below(2) == 0 {
                // Delete the focus object's capability (its last one, so
                // the object is finalised while other cores use it), or
                // make a new object in the empty slot.
                if Slot::index(self.root_cnode(), slot).cap(&self.s).is_null() {
                    let ut = self.first_untyped();
                    self.invoke(cpu, ut, label::UntypedRetype, &[ty, 0, rs::InitThreadCNode, 0, slot, 1], &[rs::InitThreadCNode]);
                } else {
                    self.invoke(cpu, rs::InitThreadCNode, label::CNodeDelete, &[slot, 64], &[]);
                }
                return;
            }
        }
        if !self.frame_slots.is_empty() && self.a.m.lock().unwrap().rng.below(4) == 0 {
            return self.frame_turn(cpu);
        }
        if self.a.m.lock().unwrap().rng.below(10) == 0 {
            return self.root_timer_turn(cpu);
        }
        if self.port != 0 && self.a.m.lock().unwrap().rng.below(8) == 0 {
            // An I/O port access (fl4_core::syscall::handle_ioport_local),
            // sometimes out of the cap's range or with too few arguments.
            let (r, w, p, v, n) = {
                let rng = &mut self.a.m.lock().unwrap().rng;
                (rng.below(3), rng.below(2) == 0, 0x5e + rng.below(0x14), rng.below(256), rng.below(4))
            };
            let lbls = if w {
                [label::X86IOPortOut8, label::X86IOPortOut16, label::X86IOPortOut32]
            } else {
                [label::X86IOPortIn8, label::X86IOPortIn16, label::X86IOPortIn32]
            };
            let args = [p, v];
            let len = if n == 0 { 0 } else if w { 2 } else { 1 };
            let info = (lbls[r as usize] << 12) | len;
            let port = self.port;
            self.syscall(cpu, if n == 1 { sc::SysSend } else { sc::SysCall }, port, info, [args[0], args[1], 0, 0]);
            return;
        }
        if mode < 3 {
            // Reply to the last fault (label 0: restart the faulter).
            let r = self.reply;
            self.syscall(cpu, sc::SysSend, r, 0, [0; 4]);
        } else if mode < 6 {
            // Poll for the next fault without blocking.
            let ep = self.fault_ep;
            self.syscall(cpu, sc::SysNBRecv, ep, 0, [0; 4]);
        } else if mode < 7 {
            // Resume a worker (stuck or stopped ones run again).
            let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
            let w = tcbs[self.a.m.lock().unwrap().rng.below(tcbs.len() as u64) as usize];
            self.invoke(cpu, w, label::TCBResume, &[], &[]);
        } else {
            let mrs = [other, 1, 0, 4];
            self.invoke(cpu, target, lbl, &mrs[..len.min(4) as usize], &[other]);
        }
    }

    /// The root task's frame-cap invocation (`fl4_core::localinv`), as a
    /// guest's pager makes them: copy or mint a frame cap (one of the
    /// workload's frames, or another copy) into a frame slot, read-write or
    /// read-only; map the copy in a frame slot at its page, or remap it
    /// there with other rights (a remap that lowers them invalidates the
    /// address space, unless `DEFER_FLUSH`; one that raises them, the
    /// page); or delete it, which unmaps it. Some fail (an occupied
    /// destination, an empty source, a copy mapped elsewhere, another
    /// slot's page, a page without a page table), as they may in a guest.
    fn frame_turn(&mut self, cpu: u64) {
        let frames = self.objs_of(|c| matches!(c, Cap::Frame { .. }));
        let (op, i, j, rights, badge, attr, at) = {
            let r = &mut self.a.m.lock().unwrap().rng;
            let n = self.frame_slots.len() as u64;
            (
                r.below(4),
                r.below(n) as usize,
                r.below(n + frames.len() as u64) as usize,
                if r.below(3) == 0 { READ_ONLY } else { ALL_RIGHTS },
                r.below(1 << 20),
                if r.below(2) == 0 { 0 } else { fl4_abi::consts::vm_attr::DEFER_FLUSH },
                r.below(16),
            )
        };
        let (slot, va) = self.frame_slots[i];
        let src = if j < frames.len() { frames[j] } else { self.frame_slots[j - frames.len()].0 };
        // Mostly the slot's own page; sometimes another slot's, or one no
        // page table covers (the plan's lookup declines).
        let va = match at {
            0 | 1 => self.frame_slots[(i + 1) % self.frame_slots.len()].1,
            2 => UNMAPPED_VA,
            _ => va,
        };
        match op {
            0 => self.invoke(cpu, rs::InitThreadCNode, label::CNodeCopy, &[slot, 64, src, 64, rights], &[rs::InitThreadCNode]),
            1 => self.invoke(cpu, rs::InitThreadCNode, label::CNodeMint, &[slot, 64, src, 64, rights, badge], &[rs::InitThreadCNode]),
            2 => self.invoke(cpu, slot, label::X86PageMap, &[va, rights, attr], &[rs::InitThreadVSpace]),
            _ => self.invoke(cpu, rs::InitThreadCNode, label::CNodeDelete, &[slot, 64], &[]),
        }
    }

    /// A deadline in ticks for soon: within 200 us.
    fn soon(&self) -> u64 {
        let mut m = self.a.m.lock().unwrap();
        let now = m.now;
        now + 1 + m.rng.below(200 * TICKS_PER_US)
    }

    /// A deadline of any kind: soon, now or in the past (which the kernel
    /// fires at once), much later, or 0 (disarm).
    fn random_deadline(&self) -> u64 {
        let k = self.a.m.lock().unwrap().rng.below(8);
        match k {
            0 => 0,
            1 => {
                let mut m = self.a.m.lock().unwrap();
                let now = m.now;
                now.saturating_sub(m.rng.below(1000))
            }
            2 => self.a.m.lock().unwrap().now + 100_000 * TICKS_PER_US,
            _ => self.soon(),
        }
    }

    /// `TCB_SetTimer(deadline, badge)` on the TCB in root CNode slot
    /// `target`, by the current thread of `cpu`.
    fn set_timer(&mut self, cpu: u64, target: u64, deadline: u64, badge: u64) {
        self.invoke(cpu, target, label::TCBSetTimer, &[deadline, badge], &[]);
    }

    /// The root task's timer work: a TCB timer on its own thread (which
    /// has no notification bound) or a worker's, mostly of another core;
    /// with `--scenario timer`, also moving a worker to another core while
    /// its timer stays in the old core's tree (SchedControl_ConfigureFlags
    /// migrates the thread its SC is bound to), with a round-robin budget
    /// or a sporadic one, and binding a worker's notification again (after
    /// the focus deleted it).
    fn root_timer_turn(&mut self, cpu: u64) {
        let (k, i) = {
            let r = &mut self.a.m.lock().unwrap().rng;
            (r.below(8), r.next())
        };
        if !self.timer.is_empty() && k == 0 {
            let scs = self.objs_of(|c| matches!(c, Cap::SchedContext { .. }));
            if scs.is_empty() {
                return;
            }
            let (core, rr, extra) = {
                let r = &mut self.a.m.lock().unwrap().rng;
                (r.below(self.ncores), r.below(2) == 0, r.below(3))
            };
            let ctrl = self.sched_control(core);
            // In microseconds, as SchedControl_ConfigureFlags takes them.
            let (budget, period) = if rr { (60, 60) } else { (300, 1000) };
            return self.invoke(cpu, ctrl, label::SchedControlConfigureFlags, &[budget, period, extra, i % 64, 0], &[scs[i as usize % scs.len()]]);
        }
        if !self.timer.is_empty() && k == 1 {
            let w = self.timer[i as usize % self.timer.len()];
            return self.invoke(cpu, w.slot, label::TCBBindNotification, &[], &[w.ntfn]);
        }
        let d = self.random_deadline();
        if k < 4 {
            return self.set_timer(cpu, rs::InitThreadTCB, d, i);
        }
        let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
        let target = if tcbs.is_empty() || k == 4 { self.reset_child } else { tcbs[i as usize % tcbs.len()] };
        self.set_timer(cpu, target, d, i)
    }

    /// `--scenario timer`: a worker arms its own timer, or another
    /// thread's (another core's too), disarms or sets one in the past, and
    /// waits for its timer on its bound notification (`Wait`) or in `Recv`
    /// on its core's endpoint (with its reply object or none), polls its
    /// notification, or sends to an endpoint, so that timers fire on
    /// running, idle and waiting cores, and signal notifications idle,
    /// active and waited on. False to make a random syscall instead.
    fn timer_turn(&mut self, cpu: u64, w: TimerWorker) -> bool {
        let (pick, j, e, badge) = {
            let r = &mut self.a.m.lock().unwrap().rng;
            (r.below(100), r.next(), r.next(), r.below(1 << 20))
        };
        let armed = w.tcb.timer_deadline(&SimStore { conc: None, ..self.s.clone() }) != 0;
        let ep = self.timer_eps[(e % self.timer_eps.len() as u64) as usize];
        let own_ep = self.timer_eps[(cpu % self.timer_eps.len() as u64) as usize];
        match pick {
            0..=24 => {
                let d = self.soon();
                self.set_timer(cpu, w.slot, d, badge)
            }
            25..=31 => {
                let o = self.timer[(j % self.timer.len() as u64) as usize];
                let d = self.random_deadline();
                self.set_timer(cpu, o.slot, d, badge)
            }
            32..=35 => {
                let d = if j % 2 == 0 { 0 } else { self.a.m.lock().unwrap().now };
                self.set_timer(cpu, w.slot, d, badge)
            }
            36..=70 if !armed => {
                let d = self.soon();
                self.set_timer(cpu, w.slot, d, badge)
            }
            36..=55 => self.syscall(cpu, sc::SysWait, w.ntfn, 0, [0; 4]),
            56..=65 => {
                w.tcb.set_reg(&mut self.s, reg::REPLY, w.reply);
                self.syscall(cpu, sc::SysRecv, own_ep, 0, [0; 4])
            }
            66..=70 => self.syscall(cpu, sc::SysWait, own_ep, 0, [0; 4]),
            71..=77 => self.syscall(cpu, sc::SysNBWait, w.ntfn, 0, [0; 4]),
            78..=83 => self.syscall(cpu, sc::SysNBSend, ep, 0, [badge, 0, 0, 0]),
            _ => return false,
        }
        true
    }

    fn is_root(&self, t: Tcb) -> bool {
        name_of(&self.s, t) == "rootserver"
    }

    /// One random user-level action by the current thread of `cpu`.
    fn random_syscall(&mut self, cpu: u64) {
        self.on(cpu);
        if self.is_root(sched::cur_thread(&self.s)) {
            return self.root_turn(cpu);
        }
        let ct = sched::cur_thread(&self.s);
        if let Some(&(k, u, ep, reply, k_slot)) = self.guest.iter().find(|g| g.0 == ct || g.1 == ct) {
            let (pick, n, len, lbl, mrs) = {
                let mut g = self.a.m.lock().unwrap();
                let r = &mut g.rng;
                let lens = [0, 18, 4, 1, r.below(20)];
                (r.below(10), r.below(400) as i64, lens[r.below(5) as usize], if r.below(20) == 0 { 1 } else { 0 }, [r.next(), r.below(16), r.next(), r.below(1 << 20)])
            };
            if ct == k && pick < 9 {
                // Answer the last fault (the label restarts it) and wait.
                ct.set_reg(&mut self.s, reg::REPLY, reply);
                return self.syscall(cpu, sc::SysReplyRecv, ep, (lbl << 12) | len, mrs);
            }
            if ct == k && mrs[1] < 8 {
                // Arm its own timer, as a VMM does for its guest's: it
                // fires while the handler waits in ReplyRecv, and its
                // bound notification wakes it there (`cancel_ipc`).
                let d = self.soon();
                return self.set_timer(cpu, k_slot, d, mrs[3]);
            }
            if ct == u && (pick == 7 || pick == 8) {
                // A page fault (l4h: a guest page not mapped yet), at a
                // user address, user mode, any of the other error bits.
                let (addr, code) = (mrs[0] & 0x7fff_ffff_f000 | mrs[1] << 3, mrs[3] & 0x1b | 4);
                return self.vm_fault(cpu, addr, code);
            }
            if ct == u && pick < 7 {
                // Any number: with trapSyscalls each one faults.
                return self.syscall(cpu, n - 200, 0, len, mrs);
            }
        }
        if let Some(w) = self.timer.iter().copied().find(|w| w.tcb == ct) {
            if self.timer_turn(cpu, w) {
                return;
            }
        }
        // A TCB timer: the thread's own or another's, on this core or not,
        // for soon, the past, much later, or disarmed.
        if self.a.m.lock().unwrap().rng.below(20) == 0 {
            let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
            if !tcbs.is_empty() {
                let i = self.a.m.lock().unwrap().rng.below(tcbs.len() as u64) as usize;
                let d = self.random_deadline();
                return self.set_timer(cpu, tcbs[i], d, i as u64);
            }
        }
        // Another core's frame-cap copy deleted under it, beside the gate.
        if !self.frame_slots.is_empty() && self.a.m.lock().unwrap().rng.below(16) == 0 {
            let i = self.a.m.lock().unwrap().rng.below(self.frame_slots.len() as u64) as usize;
            let slot = self.frame_slots[i].0;
            return self.invoke(cpu, rs::InitThreadCNode, label::CNodeDelete, &[slot, 64], &[]);
        }
        let mut guard = self.a.m.lock().unwrap();
        let rng = &mut guard.rng;
        let pick = rng.below(100);
        let n = self.objs.len() as u64;
        let cptr = match self.focus {
            Some((slot, _)) if rng.below(10) < 8 => slot,
            _ if n > 0 && rng.below(10) < 8 => self.objs[rng.below(n) as usize],
            _ => rng.below(64),
        };
        let other = if n > 0 { self.objs[rng.below(n) as usize] } else { 0 };
        let lbl = rng.below(80);
        let len = rng.below(8);
        let mut mrs = [0u64; 4];
        for m in mrs.iter_mut() {
            *m = match rng.below(4) {
                0 => rng.next(),
                1 => rng.below(16),
                2 => other,
                _ => rng.below(1 << 20),
            };
        }
        let extra = rng.below(3);
        let number = match pick {
            0..=29 => sc::SysCall,
            30..=39 => sc::SysSend,
            40..=49 => sc::SysNBSend,
            50..=59 => sc::SysRecv,
            60..=64 => sc::SysNBRecv,
            65..=69 => sc::SysWait,
            70..=74 => sc::SysReplyRecv,
            75..=79 => sc::SysYield,
            80..=84 => sc::SysNBWait,
            85..=89 => sc::SysNBSendRecv,
            90..=94 => sc::SysDebugPutChar,
            _ => {
                // Any number, except the debug calls that stop the machine.
                let n = -(rng.below(40) as i64);
                if n == sc::SysDebugHalt || n == sc::SysDebugNameThread {
                    sc::SysYield
                } else {
                    n
                }
            }
        };
        drop(guard);
        if extra > 0 {
            self.set_buffer_mr(cpu, fl4_core::msg::BUF_CAPS - 1, other);
        }
        let info = (lbl << 12) | (extra << 7) | len;
        // Reply objects in R12, the NBSendRecv destination in R13.
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        t.set_reg(&mut self.s, reg::REPLY, other);
        t.set_reg(&mut self.s, reg::NBSEND_RECV_DEST, cptr);
        self.syscall(cpu, number, cptr, info, mrs);
    }

    /// The next thing that happens on core `cpu`.
    fn step(&mut self, cpu: u64) {
        self.on(cpu);
        // At user level a core takes a remote stall's IPI at once.
        if let Some(conc) = self.s.conc.clone() {
            SimEnv { s: self.s.clone(), a: self.a.clone(), conc }.service();
        }
        // A due timer raises its interrupt.
        {
            let mut m = self.a.m.lock().unwrap();
            let now = m.now;
            let core = &mut m.cores[cpu as usize];
            if core.deadline != 0 && core.deadline <= now {
                core.deadline = 0;
                core.pending[(irq::TIMER / 64) as usize] |= 1 << (irq::TIMER % 64);
            }
        }
        // The interrupt the core takes now (not one the kernel polls for,
        // so it is not held for the entry).
        let pending = {
            let mut m = self.a.m.lock().unwrap();
            let c = &mut m.cores[cpu as usize];
            match (0..3).find(|&w| c.pending[w] != 0) {
                Some(w) => {
                    let b = c.pending[w].trailing_zeros() as u64;
                    c.pending[w] &= !(1 << b);
                    c.in_service = Some(w as u64 * 64 + b);
                    w as u64 * 64 + b
                }
                None => syscall::NO_IRQ,
            }
        };
        if pending != syscall::NO_IRQ {
            if TRACE.load(Ordering::Relaxed) {
                println!("  core {cpu} irq {pending}");
            }
            if pending == irq::TIMER && FASTPATH_DIFF.load(Ordering::Relaxed) && self.s.conc.is_none() {
                self.diff_timer_irq(pending);
            } else if pending == irq::TIMER {
                self.enter_timer_irq(pending);
            } else {
                self.enter(true, |s, a| syscall::handle_interrupt_entry(s, a, pending));
            }
            self.after("interrupt");
            return;
        }
        let ct = sched::cur_thread(&self.s);
        if ct == sched::idle_thread(&self.s) {
            // Idle: time passes to this core's next deadline.
            let mut m = self.a.m.lock().unwrap();
            let d = m.cores[cpu as usize].deadline;
            if d > m.now {
                m.now = d.min(m.now + 100 * TICKS_PER_US);
            } else {
                m.now += 10;
            }
            return;
        }
        self.random_syscall(cpu);
        self.after("syscall");
    }

    fn after(&mut self, what: &str) {
        if !self.quiet() {
            return;
        }
        // Check on a copy that does not let other cores run meanwhile.
        let mut q = self.clone();
        q.s.conc = None;
        q.a.conc = None;
        let slots = q.slots_to_check();
        q.check(what);
        q.check_cdt(what, &slots);
        q.check_queues(what);
        q.check_timers(what);
        q.check_refills(what, &slots);
        let s = &q.s;
        q.s.mem.watch.lock().unwrap().live = slots.into_iter().filter(|sl| !(sl.cap(s).is_null() && sl.prev(s).is_null() && sl.next(s).is_null())).map(|sl| sl.0).collect();
    }

    // ---- oracles ----------------------------------------------------------

    fn check(&self, what: &str) {
        let s = &self.s;
        // A TCB made from the reset untyped keeps what creation wrote: a
        // reset's in-place clear of a region that is live by then (a stale
        // `clear_free`) would zero it.
        if self.reset_child != 0 {
            if let Cap::Thread { ptr } = Slot::index(self.root_cnode(), self.reset_child).cap(s) {
                assert_eq!(s.read(Tcb(ptr).fpu_addr()), 0x037f, "{what}: a live TCB in the reset untyped was cleared");
            }
        }
        let threads = self.threads();
        // Debug TCB lists: well linked, and each thread is on the list of
        // the core it runs on (deletion unlinks it from that core's list
        // only, so a thread left on another core's list would leave a
        // dangling head there once deleted).
        for c in 0..self.ncores {
            let mut t = node_get(s, c, node::DEBUG_TCBS);
            let mut prev = 0;
            while t != 0 {
                let tt = Tcb(t);
                assert_eq!(tt.debug_prev(s), prev, "{what}: debug list of core {c} badly linked at {t:#x}");
                assert_eq!(tt.affinity(s), c, "{what}: thread {t:#x} of core {} is on core {c}'s debug list", tt.affinity(s));
                prev = t;
                t = tt.debug_next(s);
            }
        }
        for c in 0..self.ncores {
            let ct = Tcb(node_get(s, c, node::CUR_THREAD));
            let idle = Tcb(node_get(s, c, node::IDLE_THREAD));
            if ct != idle {
                let st = ct.state(s);
                assert!(
                    st == sched::TS_RUNNING || st == sched::TS_RESTART,
                    "{what}: core {c} runs thread {:#x} in state {st}",
                    ct.0
                );
                assert!(ct.sc(s) != 0, "{what}: core {c} runs thread {:#x} without an SC", ct.0);
                assert_eq!(ct.affinity(s), c, "{what}: core {c} runs a thread of core {}", ct.affinity(s));
            }
            // Liveness: an idle core with ready threads has been asked to
            // reschedule (or will choose at its next entry).
            // Per priority: head and tail. The oracles run on a copy without
            // store buffers (`after`), so this is what `node_get` reads.
            let rq = s.mem.words_at(fl4_core::obj::node_base(s, c) + node::READY_QUEUES, 2 * layout::NUM_PRIORITIES);
            if ct == idle && node_get(s, c, node::SCHED_ACTION) == sched::ACTION_RESUME_CURRENT {
                let ready = (0..layout::NUM_PRIORITIES).any(|p| rq[2 * p as usize].load(Ordering::Relaxed) != 0);
                if ready {
                    let m = self.a.m.lock().unwrap();
                    let pend = m.cores[c as usize].pending;
                    let ipi = pend[(irq::RESCHEDULE_IPI / 64) as usize] & (1 << (irq::RESCHEDULE_IPI % 64)) != 0;
                    let timer = pend[(irq::TIMER / 64) as usize] & (1 << (irq::TIMER % 64)) != 0;
                    assert!(ipi || timer || m.halted, "{what}: core {c} is idle with ready threads and no reschedule pending");
                }
            }
            // Ready queues: well linked, runnable, on this core.
            for prio in 0..layout::NUM_PRIORITIES {
                let head = rq[2 * prio as usize].load(Ordering::Relaxed);
                let tail = rq[2 * prio as usize + 1].load(Ordering::Relaxed);
                if head == 0 && tail == 0 {
                    continue;
                }
                let mut t = head;
                let mut prev = 0;
                let mut n = 0;
                while t != 0 {
                    let tt = Tcb(t);
                    assert_eq!(tt.sched_prev(s), prev, "{what}: ready queue {prio} of core {c} badly linked");
                    assert!(sched::queued(s, tt), "{what}: thread in a ready queue without its flag");
                    assert_eq!(tt.prio(s), prio, "{what}: thread in the wrong ready queue");
                    assert_eq!(tt.affinity(s), c, "{what}: thread in another core's ready queue");
                    assert!(sched::is_runnable(s, tt), "{what}: blocked thread {t:#x} in a ready queue");
                    assert_ne!(t, ct.0, "{what}: the current thread of core {c} is also queued");
                    prev = t;
                    t = tt.sched_next(s);
                    n += 1;
                    assert!(n < 10_000, "{what}: ready queue does not end");
                }
                assert_eq!(tail, prev, "{what}: ready queue {prio} of core {c} has a wrong tail");
            }
        }
        for t in threads {
            if sched::queued(s, t) {
                let off = node::READY_QUEUES + t.prio(s) * 16;
                let mut x = node_get(s, t.affinity(s), off);
                let mut found = false;
                while x != 0 {
                    if x == t.0 {
                        found = true;
                        break;
                    }
                    x = Tcb(x).sched_next(s);
                }
                assert!(found, "{what}: thread {:#x} flagged queued but not in its queue", t.0);
            }
            let st = t.state(s);
            if st == sched::TS_BLOCKED_ON_SEND || st == sched::TS_BLOCKED_ON_RECV {
                let ep = t.block_obj(s);
                let mut x = s.read(ep);
                let mut found = false;
                while x != 0 {
                    if x == t.0 {
                        found = true;
                        break;
                    }
                    x = Tcb(x).ep_next(s);
                }
                assert!(found, "{what}: thread {:#x} blocked on {ep:#x} but not in its queue", t.0);
            }
        }
    }
}

impl Sim {
    /// Every capability slot the workload can reach, as (address, bytes)
    /// regions: the root CNode, the CNodes it created, and the slots of
    /// every TCB.
    fn slot_regions(&self) -> Vec<(u64, u64)> {
        let size = layout::cte::SIZE;
        let rt = self.root_cnode();
        let mut v = vec![(rt, (1u64 << boot::ROOT_CNODE_BITS) * size)];
        for &o in &self.objs {
            if let Cap::CNode { ptr, radix, .. } = Slot::index(rt, o).cap(&self.s) {
                v.push((ptr, (1u64 << radix.min(12)) * size));
            }
        }
        for t in self.threads() {
            v.push((t.slot(0).0, tl::NUM_SLOTS * size));
        }
        v
    }

    /// The slots of `slot_regions` that the slot oracles must look at to
    /// check all of them: those not empty and unlinked at the last check,
    /// those written since, and every slot of a region that is new. Any
    /// other slot is as the last check saw it, empty and unlinked, which
    /// passes.
    fn slots_to_check(&self) -> Vec<Slot> {
        let regions = self.slot_regions();
        let dirty = self.s.mem.take_dirty();
        let mut w = self.s.mem.watch.lock().unwrap();
        let inside = |a: &u64| regions.iter().any(|&(b, n)| *a >= b && *a < b + n);
        let mut v: Vec<u64> = w.live.iter().chain(&dirty).copied().filter(inside).collect();
        for &(b, n) in &regions {
            if !w.regions.contains(&(b, n)) {
                v.extend((b..b + n).step_by(layout::cte::SIZE as usize));
            }
        }
        w.regions = regions;
        v.sort_unstable();
        v.dedup();
        v.into_iter().map(Slot).collect()
    }

    /// The CDT is a well-formed doubly linked list, and empty slots are
    /// off it.
    fn check_cdt(&self, what: &str, slots: &[Slot]) {
        let s = &self.s;
        for &sl in slots {
            let c = sl.cap(s);
            let (p, n) = (sl.prev(s), sl.next(s));
            // l4v cap_aligned for untypeds: retype aligns pointers, so an
            // untyped's pointer must be aligned to its size.
            if let Cap::Untyped { ptr, size_bits, .. } = c {
                assert!(ptr & ((1u64 << size_bits) - 1) == 0, "{what}: untyped cap in slot {:#x} at {ptr:#x} is not aligned to its 2^{size_bits} bytes", sl.0);
            }
            if c.is_null() {
                assert!(p.is_null() && n.is_null(), "{what}: empty slot {:#x} is linked into the CDT", sl.0);
                continue;
            }
            if !n.is_null() {
                assert!(n.prev(s) == sl, "{what}: CDT next of {:#x} does not point back", sl.0);
                assert!(!n.cap(s).is_null(), "{what}: CDT next of {:#x} is empty", sl.0);
            }
            if !p.is_null() {
                assert!(p.next(s) == sl, "{what}: CDT prev of {:#x} does not point back", sl.0);
            }
        }
    }

    /// The refill invariants of P1: l4v's `cfg_valid_refills`
    /// (DetSchedInvs_AI, rt branch), less the parts about the budget, which
    /// the kernel does not store. Every active scheduling context's ring
    /// fits its object, with head and tail inside it, and its head refill
    /// holds at least MIN_BUDGET. A round-robin one (period 0) has exactly
    /// MIN_REFILLS refills, as `rr_valid_refills` requires. A periodic one
    /// (`sp_valid_refills`) has refills in time order without overlap
    /// (`ordered_disjoint`), none empty and none running past the end of
    /// time (`no_overflow`), totalling at most the period, with the last
    /// starting within a period of the head (`window`).
    fn check_refills(&self, what: &str, slots: &[Slot]) {
        use fl4_core::sporadic;
        let s = &self.s;
        let min_budget = 2 * 10 * TICKS_PER_US;
        let mut seen = HashSet::new();
        for &sl in slots {
            let Cap::SchedContext { ptr, size_bits } = sl.cap(s) else { continue };
            if !seen.insert(ptr) {
                continue;
            }
            let sc = fl4_core::obj::Sc(ptr);
            let max = sc.refill_max(s);
            if max == 0 {
                continue;
            }
            let (h, tl) = (sc.refill_head(s), sc.refill_tail(s));
            assert!(max >= sporadic::MIN_REFILLS, "{what}: SC {ptr:#x} has refill_max {max}");
            assert!(max <= sporadic::refill_absolute_max(size_bits), "{what}: SC {ptr:#x}: {max} refills do not fit 2^{size_bits} bytes");
            assert!(h < max && tl < max, "{what}: SC {ptr:#x}: head {h} or tail {tl} outside {max} refills");
            let n = sporadic::size(s, sc);
            let refills: Vec<_> = (0..n).map(|k| sporadic::get(s, sc, (h + k) % max)).collect();
            let head = refills[0];
            assert!(head.amount >= min_budget, "{what}: SC {ptr:#x}: head refill holds {} ticks, less than MIN_BUDGET", head.amount);
            let period = sc.period(s);
            if period == 0 {
                assert!(n == sporadic::MIN_REFILLS && max == sporadic::MIN_REFILLS, "{what}: round-robin SC {ptr:#x} has {n} of {max} refills");
                continue;
            }
            let mut sum = 0u64;
            for (k, r) in refills.iter().enumerate() {
                assert!(r.amount > 0, "{what}: SC {ptr:#x}: refill {k} is empty");
                assert!(r.time.checked_add(r.amount).is_some(), "{what}: SC {ptr:#x}: refill {k} runs past the end of time");
                if k > 0 {
                    let p = refills[k - 1];
                    assert!(p.time + p.amount <= r.time, "{what}: SC {ptr:#x}: refill {k} at {} overlaps the one before, which ends at {}", r.time, p.time + p.amount);
                }
                sum = sum.saturating_add(r.amount);
            }
            assert!(sum <= period, "{what}: SC {ptr:#x}: refills total {sum}, more than the period {period}");
            let last = refills[refills.len() - 1];
            assert!(last.time <= head.time.saturating_add(period), "{what}: SC {ptr:#x}: last refill at {} is more than a period after the head at {}", last.time, head.time);
        }
    }

    /// Deadline timers (fl4-core timer.rs): each core's tree is a red-black
    /// search tree by deadline, well linked, of threads armed for that core
    /// (`TIMER_HEIGHT >> 8`), with its earliest as `TIMER_MIN`; every armed
    /// thread is in its core's tree and every disarmed one in none, with
    /// its timer fields clear.
    fn check_timers(&self, what: &str) {
        let s = &self.s;
        let red = |t: Tcb| t.timer_height(s) & 1 != 0;
        let mut in_tree = HashSet::new();
        for c in 0..self.ncores {
            let root = Tcb(node_get(s, c, node::TIMER_ROOT));
            let min = node_get(s, c, node::TIMER_MIN);
            if root.is_null() {
                assert_eq!(min, 0, "{what}: core {c}'s empty timer tree has a minimum");
                continue;
            }
            assert_eq!(root.timer_parent(s), 0, "{what}: core {c}'s timer tree root has a parent");
            assert!(!red(root), "{what}: core {c}'s timer tree root is red");
            // (node, lower bound, upper bound): an in-order walk would
            // give the deadlines in order.
            let mut black_height = None;
            let mut stack = vec![(root, 0u64, u64::MAX, 0u64)];
            let mut leftmost = root;
            let mut n = 0;
            while leftmost.timer_left(s) != 0 && n < 100_000 {
                leftmost = Tcb(leftmost.timer_left(s));
                n += 1;
            }
            assert_eq!(min, leftmost.0, "{what}: core {c}'s TIMER_MIN is not its timer tree's earliest");
            while let Some((t, lo, hi, blacks)) = stack.pop() {
                assert!(in_tree.insert(t.0), "{what}: thread {:#x} is twice in the timer trees", t.0);
                assert!(in_tree.len() < 100_000, "{what}: timer trees do not end");
                let d = t.timer_deadline(s);
                assert!(d != 0, "{what}: disarmed thread {:#x} in core {c}'s timer tree", t.0);
                assert!(lo <= d && d <= hi, "{what}: core {c}'s timer tree is out of order at {:#x}", t.0);
                assert_eq!(t.timer_height(s) >> 8, c, "{what}: thread {:#x} in core {c}'s timer tree is marked for core {}", t.0, t.timer_height(s) >> 8);
                let blacks = blacks + !red(t) as u64;
                for (child, lo, hi) in [(Tcb(t.timer_left(s)), lo, d), (Tcb(t.timer_right(s)), d, hi)] {
                    if child.is_null() {
                        match black_height {
                            None => black_height = Some(blacks),
                            Some(b) => assert_eq!(b, blacks, "{what}: core {c}'s timer tree has paths of different black heights"),
                        }
                        continue;
                    }
                    assert_eq!(child.timer_parent(s), t.0, "{what}: core {c}'s timer tree badly linked at {:#x}", child.0);
                    assert!(!(red(t) && red(child)), "{what}: core {c}'s timer tree has a red child of a red node at {:#x}", child.0);
                    stack.push((child, lo, hi, blacks));
                }
            }
        }
        for t in self.threads() {
            if t.timer_deadline(s) != 0 {
                assert!(in_tree.contains(&t.0), "{what}: armed thread {:#x} is in no timer tree", t.0);
            } else {
                assert!(!in_tree.contains(&t.0), "{what}: disarmed thread {:#x} is in a timer tree", t.0);
                let links = [t.timer_left(s), t.timer_right(s), t.timer_parent(s), t.timer_height(s)];
                assert_eq!(links, [0; 4], "{what}: disarmed thread {:#x} keeps timer links", t.0);
            }
        }
    }

    /// Endpoint and notification queues hold exactly threads blocked on
    /// them; release queues are in ready-time order.
    fn check_queues(&self, what: &str) {
        let s = &self.s;
        let rt = self.root_cnode();
        // Threads found on endpoint and notification queues.
        let mut queued = HashSet::new();
        let mut objects = HashSet::new();
        for &o in &self.objs {
            let (ptr, want) = match Slot::index(rt, o).cap(s) {
                Cap::Endpoint { ptr, .. } => (ptr, [sched::TS_BLOCKED_ON_SEND, sched::TS_BLOCKED_ON_RECV]),
                Cap::Notification { ptr, .. } => (ptr, [sched::TS_BLOCKED_ON_NTFN, sched::TS_BLOCKED_ON_NTFN]),
                _ => continue,
            };
            objects.insert(ptr);
            let state = s.read(ptr + 8) & 3;
            let mut t = s.read(ptr);
            if state == 0 || (want[0] == sched::TS_BLOCKED_ON_NTFN && state != 1) {
                assert_eq!(t, 0, "{what}: idle object {ptr:#x} has a queue");
            }
            let mut prev = 0;
            let mut n = 0;
            while t != 0 {
                let tt = Tcb(t);
                let st = tt.state(s);
                assert!(want.contains(&st), "{what}: thread {t:#x} queued on {ptr:#x} in state {st}");
                assert_eq!(tt.block_obj(s), ptr, "{what}: thread {t:#x} on {ptr:#x}'s queue blocks on another object");
                assert_eq!(tt.ep_prev(s), prev, "{what}: queue of {ptr:#x} badly linked");
                queued.insert(t);
                prev = t;
                t = tt.ep_next(s);
                n += 1;
                assert!(n < 10_000, "{what}: queue of {ptr:#x} does not end");
            }
            assert_eq!(s.read(ptr + 8) & !3, prev, "{what}: queue of {ptr:#x} has a wrong tail");
        }
        // And the converse: a thread blocked on one of these is queued there.
        for t in self.threads() {
            let st = t.state(s);
            if [sched::TS_BLOCKED_ON_SEND, sched::TS_BLOCKED_ON_RECV, sched::TS_BLOCKED_ON_NTFN].contains(&st) && objects.contains(&t.block_obj(s)) {
                assert!(queued.contains(&t.0), "{what}: thread {:#x} blocks on {:#x} in state {st} but is not on its queue", t.0, t.block_obj(s));
            }
        }
        for c in 0..self.ncores {
            let mut t = node_get(s, c, node::RELEASE_HEAD);
            let mut last = 0;
            let mut prev = 0;
            let mut n = 0;
            while t != 0 {
                let tt = Tcb(t);
                assert!(sched::in_release_queue(s, tt), "{what}: thread in core {c}'s release queue without its flag");
                assert_eq!(tt.affinity(s), c, "{what}: thread {t:#x} in core {c}'s release queue belongs to another core");
                assert_eq!(tt.sched_prev(s), prev, "{what}: release queue of core {c} badly linked at {t:#x}");
                prev = t;
                let rtime = fl4_core::sporadic::head(s, fl4_core::obj::Sc(tt.sc(s))).time;
                assert!(rtime >= last, "{what}: release queue of core {c} out of order");
                last = rtime;
                t = tt.sched_next(s);
                n += 1;
                assert!(n < 10_000, "{what}: release queue does not end");
            }
            assert_eq!(node_get(s, c, node::RELEASE_TAIL), prev, "{what}: release queue of core {c} has a wrong tail");
        }
    }
}

/// Print every kernel entry (--trace).
static TRACE: AtomicBool = AtomicBool::new(false);

fn cap_kind(c: Cap) -> &'static str {
    match c {
        Cap::Null => "null",
        Cap::Untyped { .. } => "untyped",
        Cap::Endpoint { .. } => "endpoint",
        Cap::Notification { .. } => "notification",
        Cap::Reply { .. } => "reply",
        Cap::CNode { .. } => "cnode",
        Cap::Thread { .. } => "tcb",
        Cap::SchedContext { .. } => "sc",
        Cap::SchedControl { .. } => "schedcontrol",
        Cap::Frame { .. } => "frame",
        _ => "other",
    }
}

fn name_of(s: &SimStore, t: Tcb) -> String {
    let mut out = Vec::new();
    for w in 0..8 {
        let v = s.read(t.name_addr() + w * 8);
        for k in 0..8 {
            let b = (v >> (k * 8)) as u8;
            if b == 0 {
                return String::from_utf8_lossy(&out).into_owned();
            }
            out.push(b);
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn cap_name(c: Cap) -> &'static str {
    match c {
        Cap::Null => "null",
        Cap::CNode { .. } => "cnode",
        _ => "other",
    }
}

impl Sim {
    fn summary(&self) -> String {
        let mut states = [0u32; 8];
        let threads = self.threads();
        for t in &threads {
            states[(t.state(&self.s) & 7) as usize] += 1;
        }
        let cur: Vec<String> = (0..self.ncores)
            .map(|c| {
                let t = Tcb(node_get(&self.s, c, node::CUR_THREAD));
                name_of(&self.s, t)
            })
            .collect();
        let (console, now) = {
            let m = self.a.m.lock().unwrap();
            (m.console.len(), m.now)
        };
        format!(
            "{} objects, {} threads (inactive/running/restart/recv/send/reply/ntfn/idle {:?}), current {:?}, {} console bytes, time {}",
            self.objs.len(),
            threads.len(),
            states,
            cur,
            console,
            now
        )
    }
}

#[allow(clippy::too_many_arguments)]
/// A simulator with `ncores` cores, booted.
fn booted(ncores: u64) -> Sim {
    let mut sim = Sim::new(BOOT_SEED, ncores);
    sim.boot();
    sim
}

/// One run from `sim`, booted with `ncores` cores.
fn run_one(mut sim: Sim, seed: u64, ncores: u64, steps: u64, verbose: bool, concurrent: bool, pct: Option<u64>, tso: bool, switches: Option<Vec<u64>>, scenario: Option<&str>) {
    sim.a.m.lock().unwrap().rng = Rng(seed_rng(seed));
    sim.setup();
    sim.focus = match scenario {
        // An endpoint other than the workers' fault endpoint.
        Some("ep") => sim.objs_of(|c| matches!(c, Cap::Endpoint { .. })).get(1).map(|&s| (s, ot::Endpoint)),
        Some("ntfn") => sim.objs_of(|c| matches!(c, Cap::Notification { .. })).first().map(|&s| (s, ot::Notification)),
        Some("guest") => {
            sim.setup_guest();
            None
        }
        // A worker's bound notification, deleted (unbinding it) and made
        // again (the root task binds it again) while its timer fires.
        Some("timer") => {
            sim.setup_timer();
            sim.timer.first().map(|w| (w.ntfn, ot::Notification))
        }
        Some(other) => panic!("unknown scenario {other}"),
        None => None,
    };
    if verbose {
        println!("seed {seed} after setup: {}", sim.summary());
        for c in 0..ncores {
            let m = sim.a.m.lock().unwrap();
            println!("  core {c}: pending {:x?} deadline {} ipi-pending {:#x}", m.cores[c as usize].pending, m.cores[c as usize].deadline, node_get(&sim.s, c, node::IPI_PENDING));
        }
        for t in sim.threads() {
            let sc = fl4_core::obj::Sc(t.sc(&sim.s));
            println!(
                "  thread {:#x} {:?} state {} core {} prio {} sc {:#x} active {} release-queued {} queued {}",
                t.0,
                name_of(&sim.s, t),
                t.state(&sim.s),
                t.affinity(&sim.s),
                t.prio(&sim.s),
                sc.0,
                sc.0 != 0 && fl4_core::sporadic::sc_active(&sim.s, sc),
                sched::in_release_queue(&sim.s, t),
                sched::queued(&sim.s, t)
            );
        }
    }
    if concurrent && ncores > 1 {
        // One coroutine per core, interleaved at memory accesses.
        let conc = Arc::new(Conc::new(ncores, seed, pct.map(|d| (d, steps * 50)), tso, switches.clone()));
        sim.s.conc = Some(conc.clone());
        sim.a.conc = Some(conc.clone());
        let per_core = steps / ncores;
        YIELDERS.with(|v| *v.borrow_mut() = vec![std::ptr::null(); ncores as usize]);
        let mut cores: Vec<Option<Coroutine<(), (), (), DefaultStack>>> = (0..ncores)
            .map(|cpu| {
                let mut core_sim = sim.clone();
                let conc = conc.clone();
                let stack = DefaultStack::new(16 << 20).unwrap();
                Some(Coroutine::with_stack(stack, move |y: &Yielder<(), ()>, ()| {
                    YIELDERS.with(|v| v.borrow_mut()[cpu as usize] = y);
                    core_sim.on(cpu);
                    conc.start(cpu);
                    for _ in 0..per_core {
                        if core_sim.a.m.lock().unwrap().halted {
                            break;
                        }
                        core_sim.step(cpu);
                        conc.progress(cpu);
                        conc.pause(cpu);
                    }
                    // Out of steps, the core still answers remote stalls, as
                    // an idle core would, until every core is out of steps.
                    conc.out_of_steps.fetch_add(1, Ordering::SeqCst);
                    while conc.out_of_steps.load(Ordering::SeqCst) < ncores {
                        SimEnv { s: core_sim.s.clone(), a: core_sim.a.clone(), conc: conc.clone() }.service();
                        conc.relax(cpu);
                    }
                    conc.finish(cpu);
                }))
            })
            .collect();
        // Run whichever core has the turn until every core has finished.
        while cores.iter().any(Option::is_some) {
            let t = conc.baton.lock().unwrap().turn as usize;
            let c = cores[t].as_mut().expect("fl4-sim: the turn passed to a finished core");
            if let CoroutineResult::Return(()) = c.resume(()) {
                cores[t] = None;
            }
        }
        sim.s.conc = None;
        sim.a.conc = None;
        sim.after("end");
        if let Some(e) = &conc.baton.lock().unwrap().explore {
            println!("explore: {} points", e.points);
        }
        if verbose {
            let st = STATS.lock().unwrap();
            println!("seed {seed}: {} serial entries, {} local paths", st.0, st.1);
            if let Some(p) = &conc.baton.lock().unwrap().pct {
                println!("seed {seed}: PCT: {} scheduling points, change points {:?}", p.points, p.change_points);
            }
        }
    } else {
        for _ in 0..steps {
            if sim.a.m.lock().unwrap().halted {
                break;
            }
            let cpu = sim.a.m.lock().unwrap().rng.below(ncores);
            sim.step(cpu);
        }
    }
    if verbose {
        println!("seed {seed} at the end: {}", sim.summary());
    }
    if FASTPATH_DIFF.load(Ordering::Relaxed) {
        let c = FASTPATH_COUNTS.lock().unwrap();
        println!("seed {seed}: fastpath diff: {} syscalls checked, {} through a fast path", c.0, c.1);
    }
    if FASTPATH_DIFF.load(Ordering::Relaxed) || (concurrent && ncores > 1) {
        let c = *LOCAL_COUNTS.lock().unwrap();
        println!(
            "seed {seed}: local paths: frame-cap invocations {}/{}, VM faults {}/{}, VM fault replies {}, TCB_SetTimer {}/{}, timer interrupts {}/{} (run/tried); their TLB invalidations: page {}, address space {}",
            c.inv_ran, c.inv_tried, c.vm_fault_ran, c.vm_fault_tried, c.vm_reply_ran, c.set_timer_ran, c.set_timer_tried, c.timer_irq_ran, c.timer_irq_tried, c.tlb_page, c.tlb_asid
        );
        println!("{LOCAL_COUNTS_TAG}{}", c.line());
    }
}

/// One campaign run: a seed and how to run it.
#[derive(Clone)]
struct Run {
    seed: u64,
    cores: u64,
    steps: u64,
    conc: bool,
    pct: Option<u64>,
    tso: bool,
    scenario: Option<String>,
    /// `--explore`: the scheduling points at which to preempt.
    switches: Option<Vec<u64>>,
    /// `--fastpath-diff`.
    diff: bool,
}

/// How a run ended.
struct Outcome {
    /// Why it failed, if it did.
    failure: Option<String>,
    stdout: String,
}

/// A run going on in a child process.
struct Child {
    pid: libc::pid_t,
    out: std::fs::File,
    err: std::fs::File,
    deadline: std::time::Instant,
}

impl Run {
    fn args(&self) -> Vec<String> {
        let mut v = vec!["--one".into(), self.seed.to_string(), "--cores".into(), self.cores.to_string(), "--steps".into(), self.steps.to_string()];
        if self.conc {
            v.push("--conc".into());
        }
        if self.tso {
            v.push("--tso".into());
        }
        if let Some(s) = &self.scenario {
            v.push("--scenario".into());
            v.push(s.clone());
        }
        if let Some(d) = self.pct {
            v.push("--pct".into());
            v.push(d.to_string());
        }
        if self.diff {
            v.push("--fastpath-diff".into());
        }
        v
    }

    /// Run in a child process (the kernel crates build with panic = abort,
    /// so a failed oracle aborts only the child): a fork of this one, which
    /// goes on from the one of `bases` booted with the run's core count, or
    /// boots if there is none. The caller must be single-threaded.
    fn spawn(&self, bases: &[Sim], timeout: u64) -> Child {
        let memfd = |name: &std::ffi::CStr| -> std::fs::File {
            use std::os::fd::FromRawFd;
            let fd = unsafe { libc::memfd_create(name.as_ptr(), 0) };
            assert!(fd >= 0, "fl4-sim: memfd_create failed");
            unsafe { std::fs::File::from_raw_fd(fd) }
        };
        let (out, err) = (memfd(c"fl4-sim-out"), memfd(c"fl4-sim-err"));
        use std::io::Write;
        let _ = std::io::stdout().flush();
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0, "fl4-sim: fork failed");
        if pid == 0 {
            use std::os::fd::AsRawFd;
            unsafe {
                libc::dup2(out.as_raw_fd(), 1);
                libc::dup2(err.as_raw_fd(), 2);
            }
            let sim = bases.iter().find(|b| b.ncores == self.cores).cloned().unwrap_or_else(|| booted(self.cores));
            FASTPATH_DIFF.store(self.diff, Ordering::Relaxed);
            run_one(sim, self.seed, self.cores, self.steps, VERBOSE.load(Ordering::Relaxed), self.conc || self.tso || self.switches.is_some(), self.pct, self.tso, self.switches.clone(), self.scenario.as_deref());
            let _ = std::io::stdout().flush();
            unsafe { libc::_exit(0) };
        }
        Child { pid, out, err, deadline: std::time::Instant::now() + std::time::Duration::from_secs(timeout) }
    }

    /// Run in a child process and wait for it.
    fn exec(&self, bases: &[Sim], timeout: u64) -> Outcome {
        run_all(bases, std::slice::from_ref(self), timeout, 1).pop().unwrap()
    }

    /// The shortest run of the same seed that still fails: a prefix of
    /// the failing run, which ends at the failure.
    fn shrink(&self, bases: &[Sim], timeout: u64) -> Run {
        let (mut lo, mut hi) = (0, self.steps);
        while lo + 1 < hi {
            let mid = (lo + hi) / 2;
            if (Run { steps: mid, ..self.clone() }).exec(bases, timeout).failure.is_some() {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        Run { steps: hi, ..self.clone() }
    }

    fn line(&self) -> String {
        format!(
            "{} {} {} {} {}{}{}",
            self.seed,
            self.cores,
            self.steps,
            if self.tso { "tso" } else if self.conc { "conc" } else { "serial" },
            self.pct.map_or("random".to_string(), |d| format!("pct{d}")),
            self.scenario.as_ref().map_or(String::new(), |s| format!(" {s}")),
            if self.diff { " diff" } else { "" }
        )
    }

    fn parse(l: &str) -> Option<Run> {
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() < 5 || f.len() > 9 || l.starts_with('#') {
            return None;
        }
        // After the five fields: a scenario name, `diff`.
        let diff = f[5..].iter().any(|t| *t == "diff");
        let scenario = f[5..].iter().find(|t| **t != "diff").map(|s| s.to_string());
        Some(Run {
            seed: f[0].parse().ok()?,
            cores: f[1].parse().ok()?,
            steps: f[2].parse().ok()?,
            conc: f[3] == "conc" || f[3] == "tso",
            pct: f[4].strip_prefix("pct").and_then(|d| d.parse().ok()),
            tso: f[3] == "tso",
            scenario,
            switches: None,
            diff,
        })
    }
}

impl Child {
    /// Whether it has ended (or hung, and has been killed), and how.
    fn poll(&mut self, timeout: u64) -> Option<Outcome> {
        let mut status = 0;
        let hung = match unsafe { libc::waitpid(self.pid, &mut status, libc::WNOHANG) } {
            0 if std::time::Instant::now() > self.deadline => {
                // A run that never ends is a hang (deadlock or livelock).
                unsafe {
                    libc::kill(self.pid, libc::SIGKILL);
                    libc::waitpid(self.pid, &mut status, 0);
                }
                true
            }
            0 => return None,
            _ => false,
        };
        let text = |f: &mut std::fs::File| {
            use std::io::{Read, Seek};
            let mut t = String::new();
            f.seek(std::io::SeekFrom::Start(0)).unwrap();
            let mut b = Vec::new();
            f.read_to_end(&mut b).unwrap();
            t.push_str(&String::from_utf8_lossy(&b));
            t
        };
        let stdout = text(&mut self.out);
        let failure = if hung {
            Some(format!("no progress after {timeout} s"))
        } else if libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0 {
            None
        } else {
            let err = text(&mut self.err);
            Some(err.lines().find(|l| !l.is_empty() && !l.starts_with("thread") && !l.starts_with("note:")).unwrap_or("").to_string())
        };
        Some(Outcome { failure, stdout })
    }
}

/// Every run, `jobs` at a time, each in a child process forked from this
/// one (`Run::spawn`); the outcomes in the order of `runs`.
fn run_all(bases: &[Sim], runs: &[Run], timeout: u64, jobs: usize) -> Vec<Outcome> {
    let mut outcomes: Vec<Option<Outcome>> = runs.iter().map(|_| None).collect();
    let mut live: Vec<(usize, Child)> = Vec::new();
    let mut next = 0;
    while next < runs.len() || !live.is_empty() {
        while live.len() < jobs && next < runs.len() {
            live.push((next, runs[next].spawn(bases, timeout)));
            next += 1;
        }
        let before = live.len();
        live.retain_mut(|(i, c)| match c.poll(timeout) {
            Some(o) => {
                outcomes[*i] = Some(o);
                false
            }
            None => true,
        });
        if live.len() == before {
            std::thread::sleep(std::time::Duration::from_micros(200));
        }
    }
    outcomes.into_iter().map(Option::unwrap).collect()
}

/// One child process per host CPU.
fn host_jobs() -> usize {
    std::thread::available_parallelism().map_or(4, |n| n.get())
}

/// Bounded exhaustive search (DESIGN.md §10): every schedule of `seed`'s
/// small scenario with at most `bound` preemptions at runtime atomics.
struct Search {
    seed: u64,
    cores: u64,
    steps: u64,
    bound: u64,
    max_runs: u64,
}

impl Search {
    fn run(&self, switches: Vec<u64>) -> Run {
        Run { seed: self.seed, cores: self.cores, steps: self.steps, conc: true, pct: None, tso: false, scenario: None, switches: Some(switches), diff: false }
    }

    /// The scheduling points of the unpreempted schedule, from its run.
    fn points(&self, o: &Outcome) -> u64 {
        if let Some(why) = &o.failure {
            println!("fl4-sim: explore: seed {}: the unpreempted schedule fails: {why}", self.seed);
            std::process::exit(1);
        }
        o.stdout.lines().find_map(|l| l.strip_prefix("explore: ")?.strip_suffix(" points")?.parse().ok()).unwrap()
    }

    /// All runs with at most `bound` of the `points` preempted, fewest
    /// first.
    fn runs(&self, points: u64) -> Vec<Run> {
        fn next(set: &mut [u64], n: u64) -> bool {
            // The next combination of 0..n in lexicographic order.
            let k = set.len();
            let mut i = k;
            while i > 0 {
                i -= 1;
                if set[i] < n - (k - i) as u64 {
                    set[i] += 1;
                    for j in i + 1..k {
                        set[j] = set[j - 1] + 1;
                    }
                    return true;
                }
            }
            false
        }
        let mut runs = Vec::new();
        for k in 1..=(self.bound.min(points)) as usize {
            let mut set: Vec<u64> = (0..k as u64).collect();
            loop {
                if runs.len() as u64 == self.max_runs {
                    println!("fl4-sim: explore: seed {}: stopped at --max-runs {}", self.seed, self.max_runs);
                    return runs;
                }
                runs.push(self.run(set.clone()));
                if !next(&mut set, points) {
                    break;
                }
            }
        }
        runs
    }

    /// Prints the result; whether every schedule passed.
    fn report(&self, points: u64, runs: &[Run], outcomes: &[Outcome]) -> bool {
        let list = |sw: &[u64]| sw.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        let failures: Vec<String> = runs.iter().zip(outcomes).filter_map(|(r, o)| o.failure.as_ref().map(|why| format!("switches {}: {why}", list(r.switches.as_deref().unwrap())))).collect();
        for f in failures.iter().take(20) {
            println!("fl4-sim: explore: seed {}: {f}", self.seed);
        }
        println!(
            "fl4-sim: explore: seed {}, {} cores, {} steps, {points} scheduling points, preemption bound {}: {} schedules, {} failed",
            self.seed,
            self.cores,
            self.steps,
            self.bound,
            runs.len(),
            failures.len()
        );
        failures.is_empty()
    }
}

/// A campaign: seeds `first..first + seeds` of one configuration.
struct Campaign {
    seeds: u64,
    first: u64,
    cores: u64,
    steps: u64,
    conc: bool,
    pct: Option<u64>,
    tso: bool,
    scenario: Option<String>,
    diff: bool,
}

impl Campaign {
    fn runs(&self) -> Vec<Run> {
        (self.first..self.first + self.seeds)
            .map(|seed| Run { seed, cores: self.cores, steps: self.steps, conc: self.conc || self.tso, pct: self.pct, tso: self.tso, scenario: self.scenario.clone(), switches: None, diff: self.diff })
            .collect()
    }

    /// Prints the result, shrinking each failing run (and recording it with
    /// `record`); the number that failed.
    fn report(&self, runs: &[Run], outcomes: &[Outcome], bases: &[Sim], timeout: u64, shrink: bool, record: bool) -> usize {
        let mut failed = 0;
        for (r, o) in runs.iter().zip(outcomes) {
            let Some(why) = &o.failure else { continue };
            failed += 1;
            println!("fl4-sim: seed {} ({} cores) failed: {why}", r.seed, r.cores);
            if !shrink {
                continue;
            }
            let small = r.shrink(bases, timeout);
            println!("fl4-sim: shrunk to {} steps; replay with: fl4-sim {}", small.steps, small.args().join(" "));
            if record {
                use std::io::Write;
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(REGRESSIONS).unwrap();
                writeln!(f, "{}", small.line()).unwrap();
            }
        }
        let mode = if self.tso { "tso" } else if self.conc { "conc" } else { "serial" };
        let extra = self.pct.map_or(String::new(), |d| format!(", PCT depth {d}"))
            + &self.scenario.as_ref().map_or(String::new(), |s| format!(", scenario {s}"))
            + if self.diff { ", fast paths checked against the general path" } else { "" };
        println!("fl4-sim: {} seeds, {} cores, {} steps each, {mode}{extra}: {failed} failed", self.seeds, self.cores, self.steps);
        // The local paths the runs took, summed over them.
        let mut total = LocalCounts::ZERO;
        let mut any = false;
        for o in outcomes {
            for l in o.stdout.lines() {
                if let Some(rest) = l.strip_prefix(LOCAL_COUNTS_TAG) {
                    total.add_line(rest);
                    any = true;
                }
            }
        }
        if any {
            let t = total;
            println!(
                "fl4-sim:   local paths (run/tried): TCB_SetTimer {}/{} (disarm {}, re-arm {}); timer interrupts {}/{} (no-op {}, round-robin {}, fired: unbound {}, active {}, set active {}, woke Recv {}, woke Wait {}; from idle {}, switched {}); frame-cap invocations {}/{}; VM faults {}/{}, replies {}; NBWait {}/{}",
                t.set_timer_ran,
                t.set_timer_tried,
                t.set_timer_disarm,
                t.set_timer_rearm,
                t.timer_irq_ran,
                t.timer_irq_tried,
                t.timer_irq_noop,
                t.timer_irq_rr,
                t.timer_irq_fire_unbound,
                t.timer_irq_fire_active,
                t.timer_irq_fire_set_active,
                t.timer_irq_fire_wake_recv,
                t.timer_irq_fire_wake_ntfn,
                t.timer_irq_idle_wake,
                t.timer_irq_switch,
                t.inv_ran,
                t.inv_tried,
                t.vm_fault_ran,
                t.vm_fault_tried,
                t.vm_reply_ran,
                t.poll_ran,
                t.poll_tried
            );
        }
        failed
    }
}

/// The regressions, replayed first; the number that failed.
fn regressions(bases: &[Sim], timeout: u64, jobs: usize) -> usize {
    let known: Vec<Run> = std::fs::read_to_string(REGRESSIONS).unwrap_or_default().lines().filter_map(Run::parse).collect();
    let outcomes = run_all(bases, &known, timeout, jobs);
    let mut failed = 0;
    for (r, o) in known.iter().zip(&outcomes) {
        if let Some(why) = &o.failure {
            failed += 1;
            println!("fl4-sim: regression {} failed: {why}", r.line());
        }
    }
    println!("fl4-sim: {} regressions: {failed} failed", known.len());
    failed
}

/// `--verbose` on a campaign: its runs print what they do.
static VERBOSE: AtomicBool = AtomicBool::new(false);

/// Failing runs, shrunk, that every campaign replays first (DESIGN.md §10).
const REGRESSIONS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/regressions");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |name: &str, def: u64| -> u64 {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).and_then(|v| v.parse().ok()).unwrap_or(def)
    };
    let cores = opt("--cores", 4);
    let steps = opt("--steps", 2000);
    let verbose = args.iter().any(|a| a == "--verbose");
    let conc = args.iter().any(|a| a == "--conc");
    let pct = args.iter().position(|a| a == "--pct").map(|_| opt("--pct", 3));
    let tso = args.iter().any(|a| a == "--tso");
    FASTPATH_DIFF.store(args.iter().any(|a| a == "--fastpath-diff"), Ordering::Relaxed);
    if let Some(i) = args.iter().position(|a| a == "--one") {
        let seed = args[i + 1].parse().unwrap();
        TRACE.store(args.iter().any(|a| a == "--trace"), Ordering::Relaxed);
        let switches = args.iter().position(|a| a == "--switches").map(|i| {
            args[i + 1].split(',').filter(|s| !s.is_empty() && *s != "none").map(|s| s.parse().unwrap()).collect::<Vec<u64>>()
        });
        let scenario = args.iter().position(|a| a == "--scenario").map(|i| args[i + 1].as_str());
        run_one(booted(cores), seed, cores, steps, verbose, conc || tso || switches.is_some(), pct, tso, switches, scenario);
        return;
    }
    let jobs = if verbose { 1 } else { opt("--jobs", host_jobs() as u64) as usize };
    if let Some(i) = args.iter().position(|a| a == "--explore") {
        let e = Search { seed: opt("--first", 1), cores, steps, bound: args[i + 1].parse().unwrap(), max_runs: opt("--max-runs", 50_000) };
        let timeout = opt("--timeout", 60);
        let bases = [booted(cores)];
        let points = e.points(&e.run(Vec::new()).exec(&bases, timeout));
        let runs = e.runs(points);
        let outcomes = run_all(&bases, &runs, timeout, jobs);
        if !e.report(points, &runs, &outcomes) {
            std::process::exit(1);
        }
        return;
    }
    let seeds = opt("--seeds", 100);
    let first = opt("--first", 1);
    let timeout = opt("--timeout", 120);
    let record = args.iter().any(|a| a == "--record");
    let shrink = !args.iter().any(|a| a == "--no-shrink");
    VERBOSE.store(verbose, Ordering::Relaxed);
    let scenario = args.iter().position(|a| a == "--scenario").map(|i| args[i + 1].clone());
    // `--suite`: every campaign of `cargo xtask sim` (DESIGN.md §10) in one
    // pool of child processes, so no campaign waits for another's slowest
    // run. Otherwise the one campaign the options describe.
    let suite = args.iter().any(|a| a == "--suite");
    let c = |steps, conc, pct, tso, scenario: Option<&str>, seeds| Campaign { seeds, first, cores, steps, conc, pct, tso, scenario: scenario.map(String::from), diff: false };
    let quarter = (seeds / 4).max(1);
    let campaigns = if suite {
        vec![
            c(20000, false, None, false, None, seeds),
            c(8000, true, None, false, None, seeds),
            c(8000, true, Some(3), false, None, seeds),
            c(8000, false, None, true, None, seeds),
            // Targeted races: most calls on one endpoint or notification
            // while the root task deletes and recreates it.
            c(8000, true, None, false, Some("ep"), quarter),
            c(8000, false, None, true, Some("ep"), quarter),
            c(8000, true, None, false, Some("ntfn"), quarter),
            c(8000, false, None, true, Some("ntfn"), quarter),
            // The syscall fast paths (fl4_core::fastpath): each serial
            // syscall also run through the general path from the same
            // state, with an l4h vCPU's trap and reply pattern and without;
            // and the pattern on every core at once, beside the gate.
            Campaign { diff: true, ..c(20000, false, None, false, Some("guest"), quarter) },
            Campaign { diff: true, ..c(20000, false, None, false, None, quarter) },
            c(20000, true, None, false, Some("guest"), quarter),
            c(20000, true, Some(3), false, Some("guest"), quarter),
            c(20000, false, None, true, Some("guest"), quarter),
            // The kernel timer interrupt and TCB_SetTimer beside the gate
            // (fl4_core::localtimer): checked against the general path, and on
            // every core at once.
            Campaign { diff: true, ..c(20000, false, None, false, Some("timer"), quarter) },
            c(20000, true, None, false, Some("timer"), quarter),
            c(20000, true, Some(3), false, Some("timer"), quarter),
            c(20000, false, None, true, Some("timer"), quarter),
        ]
    } else {
        vec![Campaign { diff: args.iter().any(|a| a == "--fastpath-diff"), ..c(steps, conc, pct, tso, scenario.as_deref(), seeds) }]
    };
    // Every schedule with one preemption at a runtime atomic, for small
    // two-core scenarios.
    let explores: Vec<Search> = if suite { (1..=4).map(|seed| Search { seed, cores: 2, steps: 6, bound: 1, max_runs: 50_000 }).collect() } else { Vec::new() };
    let bases = [booted(cores), booted(2)];
    let mut failed = regressions(&bases, timeout, jobs);
    let firsts: Vec<Run> = explores.iter().map(|e| e.run(Vec::new())).collect();
    let points: Vec<u64> = explores.iter().zip(run_all(&bases, &firsts, timeout, jobs)).map(|(e, o)| e.points(&o)).collect();
    let groups: Vec<Vec<Run>> = campaigns.iter().map(Campaign::runs).chain(explores.iter().zip(&points).map(|(e, &p)| e.runs(p))).collect();
    let all: Vec<Run> = groups.iter().flatten().cloned().collect();
    let outcomes = run_all(&bases, &all, timeout, jobs);
    if verbose {
        for o in &outcomes {
            print!("{}", o.stdout);
        }
    }
    let mut outcomes = outcomes.into_iter();
    for (k, runs) in groups.iter().enumerate() {
        let o: Vec<Outcome> = outcomes.by_ref().take(runs.len()).collect();
        if k < campaigns.len() {
            failed += campaigns[k].report(runs, &o, &bases, timeout, shrink, record);
        } else if !explores[k - campaigns.len()].report(points[k - campaigns.len()], runs, &o) {
            failed += 1;
        }
    }
    if failed > 0 {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Word `w` of the root task's BootInfo frame.
    fn bi_word(sim: &Sim, w: u64) -> u64 {
        match sim.root_cnode_slot(rs::BootInfoFrame) {
            Cap::Frame { ptr, .. } => sim.s.read(ptr + 8 * w),
            _ => panic!("no BootInfo frame cap"),
        }
    }

    /// Kernel address of the extra BootInfo (its first frame).
    fn extra_bi(sim: &Sim) -> u64 {
        // seL4_BootInfo.extraBIPages.start
        match sim.root_cnode_slot(bi_word(sim, 15)) {
            Cap::Frame { ptr, .. } => ptr,
            _ => panic!("no extra BootInfo frame"),
        }
    }

    use fl4_abi::consts::bootinfo_header as hdr;

    /// Boot with `total` untypeds and the backend's extra BootInfo
    /// `backend` of `backend_len` bytes. A device region `[base, base + x)`
    /// with `pptr(base)` 2^39-aligned and `x` a multiple of 16 below 2^39
    /// splits into exactly `popcount(x)` untypeds, so regions of up to 35
    /// make up what the standard boot lacks.
    fn boot_with(total: u64, backend: &[u64], backend_len: u64) -> (Sim, Result<(), boot::BootError>) {
        let std = booted(1);
        let base = bi_word(&std, 5) - bi_word(&std, 21);
        assert!(total >= base, "the standard boot has {base} untypeds");
        let mut more = Vec::new();
        let mut left = total - base;
        while left > 0 {
            let k = left.min(35);
            let start = 0x3900_0000_0000 + ((more.len() as u64) << 39);
            more.push(Region { start, end: start + (((1u64 << k) - 1) << 4) });
            left -= k;
        }
        let mut sim = Sim::new(BOOT_SEED, 1);
        let r = sim.try_boot(&more, backend, backend_len);
        (sim, r)
    }

    /// The extra BootInfo's records as (offset, ID, len), walked by `len`
    /// from offset 0 up to `extraLen`, which the walk must end on exactly.
    fn records(sim: &Sim) -> Vec<(u64, u64, u64)> {
        let (e, extra_len) = (extra_bi(sim), bi_word(sim, 0));
        let mut v = Vec::new();
        let mut off = 0;
        while off < extra_len {
            let (id, len) = (sim.s.read(e + off), sim.s.read(e + off + 8));
            assert!(len >= 16, "record at {off} has len {len}");
            v.push((off, id, len));
            off += len;
        }
        assert_eq!(off, extra_len);
        v
    }

    /// The untyped descriptors at `desc` match the caps from `slot` on.
    fn check_descriptors(sim: &Sim, desc: u64, slot: u64, n: u64) {
        for j in 0..n {
            let (paddr, d) = (sim.s.read(desc + 16 * j), sim.s.read(desc + 16 * j + 8));
            match sim.root_cnode_slot(slot + j) {
                Cap::Untyped { ptr, size_bits, is_device, .. } => {
                    assert_eq!(layout::pptr(paddr), ptr, "descriptor {j}");
                    assert_eq!(d, size_bits | (is_device as u64) << 8, "descriptor {j}");
                }
                _ => panic!("slot {} is not an untyped", slot + j),
            }
        }
    }

    /// (untyped.start, untyped.end, empty.start) from BootInfo.
    fn ut_range(sim: &Sim) -> (u64, u64, u64) {
        (bi_word(sim, 21), bi_word(sim, 22), bi_word(sim, 5))
    }

    /// l4h 0047: exactly 230 untypeds need no record; the extra BootInfo's
    /// two pages are one padding record, all of them in `extraLen`.
    #[test]
    fn x86_extra_untypeds_absent_at_230() {
        let (sim, r) = boot_with(230, &[], 0);
        assert!(r.is_ok());
        let (start, end, empty) = ut_range(&sim);
        assert_eq!((end - start, empty - start), (230, 230));
        assert_eq!(bi_word(&sim, 0), 8192);
        assert_eq!(records(&sim), [(0, hdr::PADDING, 8192)]);
    }

    /// The standard boot: no ID 10 record, the same padding.
    #[test]
    fn x86_extra_untypeds_absent_without_overflow() {
        let sim = booted(1);
        let (start, end, empty) = ut_range(&sim);
        assert!(end - start < boot::MAX_BOOTINFO_UNTYPEDS);
        assert_eq!(empty, end);
        assert_eq!(records(&sim), [(0, hdr::PADDING, 8192)]);
    }

    /// 231 untypeds: one descriptor in an ID 10 record, its cap after
    /// `untyped.end`; the base list still describes the first 230.
    #[test]
    fn x86_extra_untypeds_spill_one() {
        let (sim, r) = boot_with(231, &[], 0);
        assert!(r.is_ok());
        let (start, end, empty) = ut_range(&sim);
        assert_eq!((end - start, empty - start), (230, 231));
        assert_eq!(hdr::X86_EXTRA_UNTYPEDS, 10);
        assert_eq!(records(&sim), [(0, 10, 32), (32, hdr::PADDING, 8192 - 32)]);
        check_descriptors(&sim, extra_bi(&sim) + 16, end, 1);
        // seL4_BootInfo.untypedList is at word 23.
        let bi = match sim.root_cnode_slot(rs::BootInfoFrame) {
            Cap::Frame { ptr, .. } => ptr,
            _ => panic!("no BootInfo frame cap"),
        };
        check_descriptors(&sim, bi + 8 * 23, start, 230);
    }

    /// 486 untypeds fill the record; the free RAM, created last, is in it.
    #[test]
    fn x86_extra_untypeds_spill_full() {
        let (sim, r) = boot_with(486, &[], 0);
        assert!(r.is_ok());
        let (start, end, empty) = ut_range(&sim);
        assert_eq!((end - start, empty - start), (230, 486));
        let len = 16 + 16 * 256;
        assert_eq!(records(&sim), [(0, hdr::X86_EXTRA_UNTYPEDS, len), (len, hdr::PADDING, 8192 - len)]);
        check_descriptors(&sim, extra_bi(&sim) + 16, end, 256);
        assert!(matches!(sim.root_cnode_slot(end + 255), Cap::Untyped { is_device: false, .. }));
    }

    /// One more fails boot.
    #[test]
    fn x86_extra_untypeds_overflow_fails_boot() {
        assert!(matches!(boot_with(487, &[], 0).1, Err(boot::BootError::TooManyUntypeds)));
    }

    /// The record goes after the backend's records, which stay intact.
    #[test]
    fn x86_extra_untypeds_after_backend_records() {
        // A 24-byte record of an ID the root ignores.
        let fake = [0x7f, 24, 0x1234_5678_9abc_def0];
        let (sim, r) = boot_with(240, &fake, 24);
        assert!(r.is_ok());
        let e = extra_bi(&sim);
        assert_eq!([sim.s.read(e), sim.s.read(e + 8), sim.s.read(e + 16)], fake);
        let used = 24 + 16 + 16 * 10;
        assert_eq!(records(&sim), [(0, 0x7f, 24), (24, hdr::X86_EXTRA_UNTYPEDS, 16 + 16 * 10), (used, hdr::PADDING, 8192 - used)]);
        check_descriptors(&sim, e + 24 + 16, ut_range(&sim).1, 10);
    }

    /// The root task's thread: its message registers hold a reply.
    fn root_thread(sim: &Sim) -> Tcb {
        Tcb(sim.root_tcb())
    }

    /// The label of the reply the last `seL4_Call` got (0: success).
    fn reply_label(sim: &Sim) -> u64 {
        fl4_core::msg::msg_info(&sim.s, root_thread(sim)).label
    }

    fn tdx_boot(ncores: u64) -> Sim {
        let mut sim = Sim::new(BOOT_SEED, ncores);
        sim.a.m.lock().unwrap().tdx = true;
        sim.boot();
        sim
    }

    /// A free 4 KiB frame cap in the root CNode, from the first untyped.
    fn retype_frame(sim: &mut Sim) -> u64 {
        let (ut, dest) = (sim.first_untyped(), sim.first_empty());
        sim.invoke(0, ut, label::UntypedRetype, &[ot::X86Page4K, 0, rs::InitThreadCNode, 0, dest, 1], &[rs::InitThreadCNode]);
        assert!(matches!(sim.root_cnode_slot(dest), Cap::Frame { .. }), "the frame was created");
        dest
    }

    /// Only a TDX boot puts the cap in slot 15, and elsewhere the slot's
    /// invocation is an invalid capability, not a TDCALL.
    #[test]
    fn tdx_control_is_in_slot_15_of_a_tdx_boot_only() {
        let mut sim = booted(1);
        assert!(sim.root_cnode_slot(rs::SMC).is_null());
        let frame = retype_frame(&mut sim);
        sim.invoke(0, rs::SMC, label::X86TdxControlGetReport, &[1, 2, 3, 4, 5, 6, 7, 8], &[frame]);
        assert_eq!(reply_label(&sim), 2, "seL4_InvalidCapability");
        assert!(sim.a.m.lock().unwrap().tdx_reports.is_empty());

        let sim = tdx_boot(1);
        assert!(matches!(sim.root_cnode_slot(rs::SMC), Cap::TdxControl));
    }

    /// The whole hand-off through real syscalls: root copies the cap to
    /// another slot, deletes its own, and only the copy still works.
    #[test]
    fn tdx_control_moves_to_another_holder_through_syscalls() {
        let mut sim = tdx_boot(1);
        let frame = retype_frame(&mut sim);
        let holder = sim.first_empty();
        // The root CNode's guard and radix resolve all 64 bits.
        let depth = 64;
        sim.invoke(0, rs::InitThreadCNode, label::CNodeCopy, &[holder, depth, rs::SMC, depth, 0xf], &[rs::InitThreadCNode]);
        assert_eq!(reply_label(&sim), 0);
        assert!(matches!(sim.root_cnode_slot(holder), Cap::TdxControl));
        sim.invoke(0, rs::InitThreadCNode, label::CNodeDelete, &[rs::SMC, depth], &[]);
        assert_eq!(reply_label(&sim), 0);
        assert!(sim.root_cnode_slot(rs::SMC).is_null());
        // The old slot no longer reaches the TDX module, the copy does.
        sim.invoke(0, rs::SMC, label::X86TdxControlGetReport, &[0; 8], &[frame]);
        assert_eq!(reply_label(&sim), 2);
        assert!(sim.a.m.lock().unwrap().tdx_reports.is_empty());
        sim.invoke(0, holder, label::X86TdxControlGetReport, &[0; 8], &[frame]);
        assert_eq!(reply_label(&sim), 0);
        assert_eq!(sim.a.m.lock().unwrap().tdx_reports.len(), 1);
    }

    /// A backend length that is not a word multiple leaves no room for the
    /// record: overflow fails boot, otherwise `extraLen` is unchanged.
    #[test]
    fn x86_extra_untypeds_misaligned_backend() {
        let fake = [0x7f, 20, 0x1234_5678];
        assert!(matches!(boot_with(231, &fake, 20).1, Err(boot::BootError::TooManyUntypeds)));
        let (sim, r) = boot_with(230, &fake, 20);
        assert!(r.is_ok());
        assert_eq!(bi_word(&sim, 0), 20);
    }

    // ---- the timer local paths (fl4_core::localtimer) --------------------------

    /// A new object of type `ty` in the first empty root CNode slot.
    fn retype(sim: &mut Sim, ty: u64) -> u64 {
        let (ut, dest) = (sim.first_untyped(), sim.first_empty());
        sim.invoke(0, ut, label::UntypedRetype, &[ty, 0, rs::InitThreadCNode, 0, dest, 1], &[rs::InitThreadCNode]);
        assert!(!sim.root_cnode_slot(dest).is_null(), "retype of type {ty}");
        dest
    }

    fn now(sim: &Sim) -> u64 {
        sim.a.m.lock().unwrap().now
    }

    /// Time passes on the machine by `ticks`.
    fn wait(sim: &mut Sim, ticks: u64) {
        sim.a.m.lock().unwrap().now += ticks;
    }

    /// The root task's `TCB_SetTimer(deadline, badge)` on the thread in
    /// `slot`, through its local path first and checked against the general
    /// path (`diff_syscall_with`): whether the local path ran.
    fn local_set_timer(sim: &mut Sim, slot: u64, deadline: u64, badge: u64) -> bool {
        sim.load_syscall(0, sc::SysCall, slot, (label::TCBSetTimer << 12) | 2, [deadline, badge, 0, 0]);
        let ran = sim.diff_syscall_with(sc::SysCall, true);
        assert_eq!(reply_label(sim), 0, "TCB_SetTimer failed");
        ran
    }

    /// Core `cpu` takes its timer interrupt: through its local path first,
    /// checked against the general path (`diff_timer_irq`); whether the
    /// local path ran. Its end of interrupt is checked.
    fn local_timer_irq(sim: &mut Sim, cpu: u64) -> bool {
        sim.on(cpu);
        sim.a.m.lock().unwrap().cores[cpu as usize].in_service = Some(irq::TIMER);
        let ran = sim.diff_timer_irq(irq::TIMER);
        assert_eq!(sim.a.m.lock().unwrap().cores[cpu as usize].in_service, None, "the timer interrupt was not acknowledged");
        sim.after("timer interrupt");
        ran
    }

    /// A thread (not started) whose SC is on core `core`, so it is that
    /// core's (`migrate_tcb`): its root CNode slot.
    fn thread_on(sim: &mut Sim, core: u64) -> u64 {
        let t = retype(sim, ot::Tcb);
        let dest = sim.first_empty();
        let ut = sim.first_untyped();
        sim.invoke(0, ut, label::UntypedRetype, &[ot::SchedContext, bits::MIN_SCHED_CONTEXT, rs::InitThreadCNode, 0, dest, 1], &[rs::InitThreadCNode]);
        let ctrl = sim.sched_control(core);
        sim.invoke(0, ctrl, label::SchedControlConfigureFlags, &[1000, 1000, 0, 0, 0], &[dest]);
        sim.invoke(0, dest, label::SchedContextBind, &[], &[t]);
        assert_eq!(tcb_of(sim, t).affinity(&sim.s), core);
        t
    }

    fn tcb_of(sim: &Sim, slot: u64) -> Tcb {
        Tcb(sim.root_cnode_slot(slot).ptr())
    }

    /// `TCB_SetTimer` beside the gate: arming, re-arming in this core's tree,
    /// disarming; declined (and then run by the general path) for a deadline
    /// already past and for a thread of another core.
    #[test]
    fn set_timer_runs_locally_on_this_cores_threads_only() {
        let mut sim = booted(2);
        let root = root_thread(&sim);
        let t = now(&sim) + 500 * TICKS_PER_US;
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, t, 7));
        assert_eq!((root.timer_deadline(&sim.s), root.timer_badge(&sim.s)), (t, 7));
        assert_eq!(node_get(&sim.s, 0, node::TIMER_MIN), root.0);
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, t + 100, 8), "re-arming in this core's tree");
        assert_eq!(root.timer_deadline(&sim.s), t + 100);
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, 0, 0), "disarming");
        assert_eq!((root.timer_deadline(&sim.s), node_get(&sim.s, 0, node::TIMER_ROOT)), (0, 0));
        // A deadline already past fires at once, in the general path.
        assert!(!local_set_timer(&mut sim, rs::InitThreadTCB, 1, 9));
        assert_eq!(root.timer_deadline(&sim.s), 0);
        // Another core's thread, armed by the general path in this core's
        // tree, whatever its affinity (timer::insert).
        let other = thread_on(&mut sim, 1);
        let ot_ = tcb_of(&sim, other);
        assert!(!local_set_timer(&mut sim, other, t, 1));
        assert_eq!((ot_.timer_deadline(&sim.s), ot_.timer_height(&sim.s) >> 8), (t, 0));
        // This core's thread, disarmed or armed here.
        let mine = thread_on(&mut sim, 0);
        assert!(local_set_timer(&mut sim, mine, t + 5, 2));
        assert!(local_set_timer(&mut sim, mine, t - 5, 3));
        assert_eq!(node_get(&sim.s, 0, node::TIMER_MIN), tcb_of(&sim, mine).0);
        sim.after("set timer");
    }

    /// NBWait beside the gate, checked against the general path
    /// (`diff_syscall_with`): an idle notification (badge 0), then an
    /// active one (its badge, made idle).
    #[test]
    fn nbwait_runs_locally() {
        use fl4_core::obj::{Ntfn, NTFN_ACTIVE, NTFN_IDLE};
        let mut sim = booted(2);
        let root = root_thread(&sim);
        let n = retype(&mut sim, ot::Notification);
        let ntfn = Ntfn(sim.root_cnode_slot(n).ptr());
        sim.load_syscall(0, sc::SysNBWait, n, 0, [0; 4]);
        assert!(sim.diff_syscall_with(sc::SysNBWait, true), "an idle notification");
        assert_eq!(root.reg(&sim.s, reg::BADGE), 0);
        ntfn.set_badge(&mut sim.s, 5);
        ntfn.set_state(&mut sim.s, NTFN_ACTIVE);
        sim.load_syscall(0, sc::SysNBWait, n, 0, [0; 4]);
        assert!(sim.diff_syscall_with(sc::SysNBWait, true), "an active notification");
        assert_eq!(root.reg(&sim.s, reg::BADGE), 5);
        assert_eq!(ntfn.state(&sim.s), NTFN_IDLE);
    }

    /// The kernel timer interrupt beside the gate: nothing due, a timer of
    /// a thread with no notification, signalling an idle notification
    /// (made active) and an active one (badges ORed), a round-robin budget
    /// run out, a waiter woken on an idle core; declined when a budget runs
    /// out and a timer is due at once, and for a timer of another core's
    /// thread in this core's tree.
    #[test]
    fn timer_interrupt_runs_locally_in_its_cases() {
        use fl4_core::obj::{Ntfn, NTFN_ACTIVE};
        let mut sim = booted(2);
        let root = root_thread(&sim);
        assert!(local_timer_irq(&mut sim, 0), "nothing due");
        // A timer of a thread without a notification.
        let d = now(&sim) + 50 * TICKS_PER_US;
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, d, 1));
        wait(&mut sim, 60 * TICKS_PER_US);
        assert!(local_timer_irq(&mut sim, 0), "an unbound timer");
        assert_eq!(root.timer_deadline(&sim.s), 0);
        // With a notification bound: idle, then active.
        let n = retype(&mut sim, ot::Notification);
        sim.invoke(0, rs::InitThreadTCB, label::TCBBindNotification, &[], &[n]);
        let ntfn = Ntfn(sim.root_cnode_slot(n).ptr());
        assert_eq!(root.bound_ntfn(&sim.s), ntfn.0);
        for (badge, want) in [(1, 1), (6, 7)] {
            let d = now(&sim) + 50 * TICKS_PER_US;
            assert!(local_set_timer(&mut sim, rs::InitThreadTCB, d, badge));
            wait(&mut sim, 60 * TICKS_PER_US);
            assert!(local_timer_irq(&mut sim, 0), "signal with badge {badge}");
            assert_eq!((ntfn.state(&sim.s), ntfn.badge(&sim.s)), (NTFN_ACTIVE, want));
        }
        sim.syscall(0, sc::SysNBWait, n, 0, [0; 4]);
        // The root task's round-robin budget runs out.
        let budget = fl4_core::sporadic::head(&sim.s, fl4_core::obj::Sc(root.sc(&sim.s))).amount;
        assert_eq!(fl4_core::obj::Sc(root.sc(&sim.s)).period(&sim.s), 0, "the root task's SC is round-robin");
        wait(&mut sim, budget + 1);
        assert!(local_timer_irq(&mut sim, 0), "a round-robin budget run out");
        assert_eq!(sched::cur_thread(&sim.s).0, root.0);
        // Both at once: declined.
        let d = now(&sim) + 50 * TICKS_PER_US;
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, d, 1));
        let budget = fl4_core::sporadic::head(&sim.s, fl4_core::obj::Sc(root.sc(&sim.s))).amount;
        wait(&mut sim, budget + 1);
        assert!(!local_timer_irq(&mut sim, 0), "a budget and a timer at once");
        assert_eq!(root.timer_deadline(&sim.s), 0, "the general path fired it");
        sim.syscall(0, sc::SysNBWait, n, 0, [0; 4]);
        // The root task waits for its timer; its core idles; the timer
        // wakes it.
        let d = now(&sim) + 50 * TICKS_PER_US;
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, d, 5));
        sim.syscall(0, sc::SysWait, n, 0, [0; 4]);
        assert_eq!(sched::cur_thread(&sim.s).0, sched::idle_thread(&sim.s).0, "the root task waits");
        wait(&mut sim, 60 * TICKS_PER_US);
        assert!(local_timer_irq(&mut sim, 0), "a waiter woken from idle");
        assert_eq!(sched::cur_thread(&sim.s).0, root.0);
        assert_eq!(root.reg(&sim.s, reg::BADGE), 5);
        // A thread of core 1 armed in core 0's tree: core 0 does not fire
        // it beside the gate.
        let other = thread_on(&mut sim, 1);
        let d = now(&sim) + 50 * TICKS_PER_US;
        assert!(!local_set_timer(&mut sim, other, d, 1));
        wait(&mut sim, 60 * TICKS_PER_US);
        assert!(!local_timer_irq(&mut sim, 0), "another core's thread");
        assert_eq!(tcb_of(&sim, other).timer_deadline(&sim.s), 0, "the general path fired it");
    }

    /// A timer wakes its thread from `Recv` on an endpoint (with its reply
    /// object): `cancel_ipc`, under the locks of the notification, the
    /// endpoint and the reply object.
    #[test]
    fn timer_interrupt_wakes_a_thread_in_recv() {
        let mut sim = booted(2);
        let root = root_thread(&sim);
        let n = retype(&mut sim, ot::Notification);
        let ep = retype(&mut sim, ot::Endpoint);
        let r = retype(&mut sim, ot::Reply);
        sim.invoke(0, rs::InitThreadTCB, label::TCBBindNotification, &[], &[n]);
        let d = now(&sim) + 50 * TICKS_PER_US;
        assert!(local_set_timer(&mut sim, rs::InitThreadTCB, d, 3));
        root.set_reg(&mut sim.s, reg::REPLY, r);
        sim.syscall(0, sc::SysRecv, ep, 0, [0; 4]);
        assert_eq!(root.state(&sim.s), sched::TS_BLOCKED_ON_RECV);
        assert_eq!(root.reply_obj(&sim.s), sim.root_cnode_slot(r).ptr());
        wait(&mut sim, 60 * TICKS_PER_US);
        assert!(local_timer_irq(&mut sim, 0));
        assert_eq!((sched::cur_thread(&sim.s).0, root.state(&sim.s), root.reg(&sim.s, reg::BADGE)), (root.0, sched::TS_RUNNING, 3));
        assert_eq!(fl4_core::obj::Reply(sim.root_cnode_slot(r).ptr()).tcb(&sim.s), 0, "the reply object is unlinked");
        assert_eq!(sim.s.read(sim.root_cnode_slot(ep).ptr()), 0, "the endpoint's queue is empty");
    }

    /// Whether `footprint` lets a local path write the word at `a`.
    fn allows(f: &[(u64, u64)], a: u64) -> bool {
        f.iter().any(|&(s, n)| a >= s && a < s + n)
    }

    /// The footprint gives a thread's timer fields to the core that owns
    /// them (`fl4_core::localtimer`'s Timer ownership): a thread of core 1 armed
    /// in core 0's tree has its links written by core 0 only, and its
    /// deadline and badge by neither (core 0 fires it only under the gate);
    /// core 1 writes none of its timer fields, though the rest of the
    /// thread is core 1's.
    #[test]
    fn footprint_gives_timer_fields_to_their_owner() {
        let mut sim = booted(2);
        let other = thread_on(&mut sim, 1);
        let x = tcb_of(&sim, other);
        let d = now(&sim) + 500 * TICKS_PER_US;
        assert!(!local_set_timer(&mut sim, other, d, 1));
        assert_eq!((x.timer_deadline(&sim.s), x.timer_height(&sim.s) >> 8), (d, 0), "armed in core 0's tree");
        let (f0, f1) = (footprint(&sim.s, 2, 0, &[]), footprint(&sim.s, 2, 1, &[]));
        for off in [tl::TIMER_LEFT, tl::TIMER_RIGHT, tl::TIMER_PARENT, tl::TIMER_HEIGHT] {
            assert!(allows(&f0, x.0 + off), "core 0 owns the links of its tree's nodes");
        }
        for off in [tl::TIMER_DEADLINE, tl::TIMER_BADGE] {
            assert!(!allows(&f0, x.0 + off), "core 0 writes another core's thread's deadline");
        }
        for off in [tl::TIMER_DEADLINE, tl::TIMER_BADGE, tl::TIMER_LEFT, tl::TIMER_RIGHT, tl::TIMER_PARENT, tl::TIMER_HEIGHT] {
            assert!(!allows(&f1, x.0 + off), "core 1 writes a timer of core 0's tree");
        }
        assert!(allows(&f1, x.0 + tl::STATE) && !allows(&f0, x.0 + tl::STATE));
        // Disarmed, the timer fields are its own core's again.
        assert!(!local_set_timer(&mut sim, other, 0, 0));
        assert!(allows(&footprint(&sim.s, 2, 1, &[]), x.0 + tl::TIMER_DEADLINE));
    }

    /// A thread of the core blocked on an endpoint or a notification has
    /// its queue links in the footprint only with that object locked.
    #[test]
    fn footprint_gives_queue_links_to_the_locked_queue() {
        for (ty, n, bytes) in [(ot::Endpoint, sc::SysWait, 16), (ot::Notification, sc::SysWait, 64)] {
            let mut sim = booted(2);
            let root = root_thread(&sim);
            let o = retype(&mut sim, ty);
            let ptr = sim.root_cnode_slot(o).ptr();
            sim.syscall(0, n, o, 0, [0; 4]);
            assert!(sched::is_blocked(&sim.s, root), "the root task waits on object type {ty}");
            let f = footprint(&sim.s, 2, 0, &[]);
            assert!(!allows(&f, root.0 + tl::EP_NEXT) && !allows(&f, root.0 + tl::EP_PREV), "queue links without the lock");
            assert!(allows(&f, root.0 + tl::STATE));
            let f = footprint(&sim.s, 2, 0, &[(ptr, bytes)]);
            assert!(allows(&f, root.0 + tl::EP_NEXT) && allows(&f, root.0 + tl::EP_PREV), "queue links with the lock");
        }
    }

    /// An end of interrupt must end the interrupt in service, once.
    #[test]
    #[should_panic(expected = "ended interrupt")]
    fn a_second_end_of_interrupt_fails() {
        let mut sim = booted(1);
        sim.a.m.lock().unwrap().cores[0].in_service = Some(irq::TIMER);
        sim.a.ack_irq(irq::TIMER);
        sim.a.ack_irq(irq::TIMER);
    }

    #[test]
    #[should_panic(expected = "ended interrupt")]
    fn ending_another_interrupt_fails() {
        let mut sim = booted(1);
        sim.a.m.lock().unwrap().cores[0].in_service = Some(irq::TIMER);
        sim.a.ack_irq(irq::RESCHEDULE_IPI);
    }

    /// `--fastpath-diff` compares the `Arch` effects in order: the same
    /// calls in another order fail the check.
    #[test]
    fn the_fast_path_check_compares_arch_effects_in_order() {
        let run = |general_first: bool| {
            let mut sim = booted(1);
            let m0 = sim.start_diff();
            sim.s.mem.start_log();
            sim.a.set_deadline(5);
            sim.a.set_vspace(1, 2);
            let fast_log = sim.s.mem.take_log();
            sim.diff_general("effects", m0, fast_log, false, |_, a| {
                if general_first {
                    a.set_vspace(1, 2);
                    a.set_deadline(5);
                } else {
                    a.set_deadline(5);
                    a.set_vspace(1, 2);
                }
            });
            assert_eq!(sim.a.m.lock().unwrap().effects, None, "the log stops after the check");
        };
        run(false);
        assert!(std::panic::catch_unwind(move || run(true)).is_err(), "the effects in another order passed");
    }

    /// Clock reads are effects too: reading the clock before or after the
    /// end of interrupt makes a different run.
    #[test]
    fn the_fast_path_check_orders_clock_reads() {
        let run = |general_swapped: bool| {
            let mut sim = booted(1);
            sim.a.m.lock().unwrap().cores[0].in_service = Some(irq::TIMER);
            let m0 = sim.start_diff();
            sim.s.mem.start_log();
            let _ = sim.a.now();
            sim.a.ack_irq(irq::TIMER);
            let fast_log = sim.s.mem.take_log();
            sim.diff_general("clock", m0, fast_log, false, |_, a| {
                if general_swapped {
                    a.ack_irq(irq::TIMER);
                    let _ = a.now();
                } else {
                    let _ = a.now();
                    a.ack_irq(irq::TIMER);
                }
            });
        };
        run(false);
        assert!(std::panic::catch_unwind(move || run(true)).is_err(), "a clock read in another order passed");
    }
}
