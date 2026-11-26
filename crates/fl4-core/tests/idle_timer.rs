//! `sched::set_next_interrupt` and the deadline it leaves armed (l4h 0006):
//! between threads an earlier pending deadline is kept, but the idle thread
//! re-arms for its own next event, so a core going idle is not woken when
//! the budget of the thread that ran before it would have run out.
#![cfg(not(feature = "aarch64"))]

use fl4_core::layout::node;
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_get, node_set, Sc, Tcb};
use fl4_core::sched;
use std::collections::BTreeMap;

#[derive(Default)]
struct Memory {
    words: BTreeMap<u64, u64>,
}
impl Store for Memory {
    fn read(&self, a: u64) -> u64 {
        *self.words.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        self.words.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len);
    }
    fn ks_base(&self) -> u64 {
        0x100000
    }
    fn cur_cpu(&self) -> u64 {
        0
    }
}

/// Records every deadline written to the timer; one tick per microsecond.
#[derive(Default)]
struct Machine {
    deadlines: Vec<u64>,
}
impl Arch for Machine {
    fn now(&mut self) -> u64 {
        0
    }
    fn set_deadline(&mut self, t: u64) {
        self.deadlines.push(t);
    }
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
    fn mask_irq(&mut self, _: u64, _: bool) {}
    fn ack_irq(&mut self, _: u64) {}
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

const IDLE: Tcb = Tcb(0x40_0000);
const IDLE_SC: Sc = Sc(0x50_0000);
/// The idle SC's budget: hours, as the kernel gives it.
const IDLE_BUDGET: u64 = 1 << 40;
/// A component's or a vCPU's default budget, 5 ms.
const BUDGET: u64 = 5_000;

/// A thread bound to its own SC with `budget` at the refill head.
fn thread(s: &mut Memory, t: u64, sc: u64, budget: u64) -> Tcb {
    let (t, sc) = (Tcb(t), Sc(sc));
    t.set_sc(s, sc.0);
    sc.set_tcb(s, t.0);
    sc.set_r_amount(s, 0, budget);
    t
}

/// Core 0 at time `now`, its idle thread set up and no timers armed.
fn core(now: u64) -> Memory {
    let mut s = Memory::default();
    thread(&mut s, IDLE.0, IDLE_SC.0, IDLE_BUDGET);
    node_set(&mut s, 0, node::IDLE_THREAD, IDLE.0);
    node_set(&mut s, 0, node::IDLE_SC, IDLE_SC.0);
    node_set(&mut s, 0, node::CUR_TIME, now);
    s
}

/// Run `set_next_interrupt` at `now` with `t` current, as `schedule` does
/// after switching to it.
fn run(s: &mut Memory, a: &mut Machine, now: u64, t: Tcb) {
    node_set(s, 0, node::CUR_TIME, now);
    sched::set_cur_thread(s, t);
    node_set(s, 0, node::CUR_SC, t.sc(s));
    sched::set_next_interrupt(s, a);
}

fn armed(s: &Memory) -> u64 {
    node_get(s, 0, node::ARMED)
}

/// An idle core wakes for a thread with a 5 ms budget, which blocks a few
/// ticks later: going idle again re-arms the timer for the idle thread's
/// own next event, here the end of its budget, not 5 ms on.
#[test]
fn going_idle_rearms_past_the_last_threads_budget() {
    let mut s = core(1_000);
    let mut a = Machine::default();
    let t = thread(&mut s, 0x60_0000, 0x70_0000, BUDGET);
    run(&mut s, &mut a, 1_000, t);
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1]);
    run(&mut s, &mut a, 1_010, IDLE);
    let idle_end = 1_010 + IDLE_BUDGET - 1;
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1, idle_end], "the core would wake 5 ms on for nothing");
    assert_eq!(armed(&s), idle_end);
}

/// The same with a thread's timer due in 250 ms: the idle thread arms for
/// the timer.
#[test]
fn going_idle_rearms_for_a_far_thread_timer() {
    let mut s = core(1_000);
    let mut a = Machine::default();
    let t = thread(&mut s, 0x60_0000, 0x70_0000, BUDGET);
    let sleeper = Tcb(0x80_0000);
    let far = 1_000 + 250_000;
    sleeper.set_timer_deadline(&mut s, far);
    node_set(&mut s, 0, node::TIMER_MIN, sleeper.0);
    run(&mut s, &mut a, 1_000, t);
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1]);
    run(&mut s, &mut a, 1_010, IDLE);
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1, far]);
    assert_eq!(armed(&s), far);
    // Still armed for the timer: nothing is written again.
    run(&mut s, &mut a, 2_000, IDLE);
    assert_eq!(a.deadlines.len(), 2, "the same deadline was written twice");
}

/// Between two threads (not idle) an earlier pending deadline is kept
/// (l4h 0006), and a later one replaces it only when it is earlier.
#[test]
fn switching_between_threads_keeps_an_earlier_pending_deadline() {
    let mut s = core(1_000);
    let mut a = Machine::default();
    let t1 = thread(&mut s, 0x60_0000, 0x70_0000, BUDGET);
    let t2 = thread(&mut s, 0x61_0000, 0x71_0000, 2 * BUDGET);
    let t3 = thread(&mut s, 0x62_0000, 0x72_0000, 100);
    run(&mut s, &mut a, 1_000, t1);
    run(&mut s, &mut a, 1_010, t2);
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1], "a pending earlier deadline was rewritten");
    assert_eq!(armed(&s), 1_000 + BUDGET - 1);
    run(&mut s, &mut a, 1_020, t3);
    assert_eq!(a.deadlines, [1_000 + BUDGET - 1, 1_020 + 100 - 1]);
}
