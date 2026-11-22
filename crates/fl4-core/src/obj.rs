//! Typed object handles. Each handle is the kernel virtual address of the
//! object; fields are words at fixed offsets (see `layout`).

use crate::capability::Cap;
use crate::layout;
use crate::machine::Store;

macro_rules! fields {
    ($t:ident { $($get:ident / $set:ident = $off:expr;)* }) => {
        impl $t {
            $(
                #[inline]
                pub fn $get<S: Store>(self, s: &S) -> u64 {
                    s.read(self.0.wrapping_add($off))
                }
                #[inline]
                pub fn $set<S: Store>(self, s: &mut S, v: u64) {
                    s.write(self.0.wrapping_add($off), v)
                }
            )*
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Tcb(pub u64);
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ep(pub u64);
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Ntfn(pub u64);
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Reply(pub u64);
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Sc(pub u64);
/// A capability slot (seL4's cte_t).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Slot(pub u64);

use layout::tcb as t;
fields!(Tcb {
    state / set_state = t::STATE;
    block_obj / set_block_obj = t::BLOCK_OBJ;
    block_badge / set_block_badge = t::BLOCK_BADGE;
    block_flags / set_block_flags = t::BLOCK_FLAGS;
    reply_obj / set_reply_obj = t::REPLY_OBJ;
    bound_ntfn / set_bound_ntfn = t::BOUND_NTFN;
    fault_type / set_fault_type = t::FAULT_TYPE;
    fault_w0 / set_fault_w0 = t::FAULT_W0;
    fault_w1 / set_fault_w1 = t::FAULT_W1;
    fault_w2 / set_fault_w2 = t::FAULT_W2;
    lf_type / set_lf_type = t::LF_TYPE;
    lf_w0 / set_lf_w0 = t::LF_W0;
    lf_w1 / set_lf_w1 = t::LF_W1;
    domain / set_domain = t::DOMAIN;
    mcp / set_mcp = t::MCP;
    prio / set_prio = t::PRIO;
    flags / set_flags = t::FLAGS;
    sc / set_sc = t::SC;
    yield_to / set_yield_to = t::YIELD_TO;
    sched_next / set_sched_next = t::SCHED_NEXT;
    sched_prev / set_sched_prev = t::SCHED_PREV;
    ep_next / set_ep_next = t::EP_NEXT;
    ep_prev / set_ep_prev = t::EP_PREV;
    ipc_buffer / set_ipc_buffer = t::IPC_BUFFER;
    affinity / set_affinity = t::AFFINITY;
    timer_deadline / set_timer_deadline = t::TIMER_DEADLINE;
    timer_badge / set_timer_badge = t::TIMER_BADGE;
    timer_left / set_timer_left = t::TIMER_LEFT;
    timer_right / set_timer_right = t::TIMER_RIGHT;
    timer_parent / set_timer_parent = t::TIMER_PARENT;
    timer_height / set_timer_height = t::TIMER_HEIGHT;
    debug_next / set_debug_next = t::DEBUG_NEXT;
    debug_prev / set_debug_prev = t::DEBUG_PREV;
    in_queues / set_in_queues = t::IN_QUEUES;
});

impl Tcb {
    pub fn slot(self, i: u64) -> Slot {
        Slot(self.0.wrapping_add(i.wrapping_mul(layout::cte::SIZE)))
    }
    pub fn reg<S: Store>(self, s: &S, r: u64) -> u64 {
        s.read(self.0.wrapping_add(t::REGS).wrapping_add(r.wrapping_mul(8)))
    }
    pub fn set_reg<S: Store>(self, s: &mut S, r: u64, v: u64) {
        s.write(self.0.wrapping_add(t::REGS).wrapping_add(r.wrapping_mul(8)), v)
    }
    pub fn debug_reg<S: Store>(self, s: &S, i: u64) -> u64 {
        s.read(self.0.wrapping_add(t::DEBUG).wrapping_add(i.wrapping_mul(8)))
    }
    pub fn set_debug_reg<S: Store>(self, s: &mut S, i: u64, v: u64) {
        s.write(self.0.wrapping_add(t::DEBUG).wrapping_add(i.wrapping_mul(8)), v)
    }
    pub fn fpu_addr(self) -> u64 {
        self.0.wrapping_add(t::FPU)
    }
    pub fn name_addr(self) -> u64 {
        self.0.wrapping_add(t::NAME)
    }
    pub fn is_null(self) -> bool {
        self.0 == 0
    }
}

use layout::ep as e;
fields!(Ep {
    head / set_head = e::HEAD;
    tail_state / set_tail_state = e::TAIL_STATE;
});

pub const EP_IDLE: u64 = 0;
pub const EP_SEND: u64 = 1;
pub const EP_RECV: u64 = 2;

impl Ep {
    pub fn state<S: Store>(self, s: &S) -> u64 {
        self.tail_state(s) & 3
    }
    pub fn tail<S: Store>(self, s: &S) -> u64 {
        self.tail_state(s) & !3u64
    }
    pub fn set_queue<S: Store>(self, s: &mut S, head: u64, tail: u64, state: u64) {
        self.set_head(s, head);
        self.set_tail_state(s, (tail & !3u64) | (state & 3));
    }
}

use layout::ntfn as n;
fields!(Ntfn {
    head / set_head = n::HEAD;
    tail_state / set_tail_state = n::TAIL_STATE;
    badge / set_badge = n::BADGE;
    bound_tcb / set_bound_tcb = n::BOUND_TCB;
    sc / set_sc = n::SC;
});

pub const NTFN_IDLE: u64 = 0;
pub const NTFN_WAITING: u64 = 1;
pub const NTFN_ACTIVE: u64 = 2;

impl Ntfn {
    pub fn state<S: Store>(self, s: &S) -> u64 {
        self.tail_state(s) & 3
    }
    pub fn tail<S: Store>(self, s: &S) -> u64 {
        self.tail_state(s) & !3u64
    }
    pub fn set_queue<S: Store>(self, s: &mut S, head: u64, tail: u64, state: u64) {
        self.set_head(s, head);
        self.set_tail_state(s, (tail & !3u64) | (state & 3));
    }
    pub fn set_state<S: Store>(self, s: &mut S, state: u64) {
        let t = self.tail(s);
        self.set_tail_state(s, t | (state & 3));
    }
}

use layout::reply as r;
fields!(Reply {
    tcb / set_tcb = r::TCB;
    prev_raw / set_prev_raw = r::PREV;
    next_raw / set_next_raw = r::NEXT;
});

impl Reply {
    /// The reply object below this one on the call stack (or 0).
    pub fn prev<S: Store>(self, s: &S) -> u64 {
        self.prev_raw(s) & !1u64
    }
    pub fn set_prev<S: Store>(self, s: &mut S, v: u64) {
        self.set_prev_raw(s, v & !1u64)
    }
    /// The next element: a reply object, or the scheduling context when
    /// `next_is_head`.
    pub fn next<S: Store>(self, s: &S) -> u64 {
        self.next_raw(s) & !1u64
    }
    pub fn next_is_head<S: Store>(self, s: &S) -> bool {
        self.next_raw(s) & 1 != 0
    }
    pub fn set_next<S: Store>(self, s: &mut S, v: u64, is_head: bool) {
        self.set_next_raw(s, (v & !1u64) | if is_head { 1 } else { 0 })
    }
}

use layout::sc as c;
fields!(Sc {
    period / set_period = c::PERIOD;
    consumed / set_consumed = c::CONSUMED;
    cpu / set_cpu = c::CORE;
    tcb / set_tcb = c::TCB;
    reply / set_reply = c::REPLY;
    ntfn / set_ntfn = c::NTFN;
    badge / set_badge = c::BADGE;
    yield_from / set_yield_from = c::YIELD_FROM;
    sporadic / set_sporadic = c::SPORADIC;
    refill_max / set_refill_max = c::REFILL_MAX;
    refill_head / set_refill_head = c::REFILL_HEAD;
    refill_tail / set_refill_tail = c::REFILL_TAIL;
});

impl Sc {
    fn refill_addr(self, i: u64) -> u64 {
        self.0.wrapping_add(c::REFILLS).wrapping_add(i.wrapping_mul(c::REFILL_SIZE))
    }
    pub fn r_time<S: Store>(self, s: &S, i: u64) -> u64 {
        s.read(self.refill_addr(i))
    }
    pub fn r_amount<S: Store>(self, s: &S, i: u64) -> u64 {
        s.read(self.refill_addr(i).wrapping_add(8))
    }
    pub fn set_r_time<S: Store>(self, s: &mut S, i: u64, v: u64) {
        s.write(self.refill_addr(i), v)
    }
    pub fn set_r_amount<S: Store>(self, s: &mut S, i: u64, v: u64) {
        s.write(self.refill_addr(i).wrapping_add(8), v)
    }
    pub fn is_null(self) -> bool {
        self.0 == 0
    }
}

const MDB_PTR_MASK: u64 = 0x0000_ffff_ffff_ffff;
const MDB_REVOCABLE: u64 = 1 << 48;
const MDB_FIRST_BADGED: u64 = 1 << 49;

fn sext48(p: u64) -> u64 {
    let p = p & MDB_PTR_MASK;
    if p & 0x0000_8000_0000_0000 != 0 {
        p | 0xffff_0000_0000_0000
    } else {
        p
    }
}

impl Slot {
    #[inline(always)]
    pub fn cap<S: Store>(self, s: &S) -> Cap {
        let (w0, w1) = s.read_pair(self.0);
        Cap::decode(w0, w1)
    }
    pub fn set_cap<S: Store>(self, s: &mut S, c: Cap) {
        let (w0, w1) = c.encode();
        s.write(self.0, w0);
        s.write(self.0.wrapping_add(8), w1);
    }
    pub fn prev<S: Store>(self, s: &S) -> Slot {
        Slot(s.read(self.0.wrapping_add(layout::cte::PREV)))
    }
    pub fn set_prev<S: Store>(self, s: &mut S, p: Slot) {
        s.write(self.0.wrapping_add(layout::cte::PREV), p.0)
    }
    fn next_word<S: Store>(self, s: &S) -> u64 {
        s.read(self.0.wrapping_add(layout::cte::NEXT))
    }
    pub fn next<S: Store>(self, s: &S) -> Slot {
        Slot(sext48(self.next_word(s)))
    }
    /// The slot a NEXT word names, as `next` reads it (`localinv`, which
    /// decides from words it read once).
    pub fn next_of_word(w: u64) -> Slot {
        Slot(sext48(w))
    }
    pub fn set_next<S: Store>(self, s: &mut S, n: Slot) {
        let w = self.next_word(s);
        s.write(self.0.wrapping_add(layout::cte::NEXT), (w & !MDB_PTR_MASK) | (n.0 & MDB_PTR_MASK));
    }
    /// Set the link and both flags together, preserving the other bits.
    /// Insertion and movement know all three fields: avoid three separate
    /// read/modify/write operations.
    pub fn set_next_flags<S: Store>(self, s: &mut S, n: Slot, revocable: bool, first_badged: bool) {
        let w = self.next_word(s) & !(MDB_PTR_MASK | MDB_REVOCABLE | MDB_FIRST_BADGED);
        let r = if revocable { MDB_REVOCABLE } else { 0 };
        let f = if first_badged { MDB_FIRST_BADGED } else { 0 };
        s.write(self.0.wrapping_add(layout::cte::NEXT), w | (n.0 & MDB_PTR_MASK) | r | f);
    }
    pub fn revocable<S: Store>(self, s: &S) -> bool {
        self.next_word(s) & MDB_REVOCABLE != 0
    }
    pub fn set_revocable<S: Store>(self, s: &mut S, v: bool) {
        let w = self.next_word(s) & !MDB_REVOCABLE;
        s.write(self.0.wrapping_add(layout::cte::NEXT), w | if v { MDB_REVOCABLE } else { 0 });
    }
    pub fn first_badged<S: Store>(self, s: &S) -> bool {
        self.next_word(s) & MDB_FIRST_BADGED != 0
    }
    pub fn set_first_badged<S: Store>(self, s: &mut S, v: bool) {
        let w = self.next_word(s) & !MDB_FIRST_BADGED;
        s.write(self.0.wrapping_add(layout::cte::NEXT), w | if v { MDB_FIRST_BADGED } else { 0 });
    }
    /// Clear the whole slot: null cap, no links, no flags.
    pub fn clear<S: Store>(self, s: &mut S) {
        s.write(self.0, 0);
        s.write(self.0.wrapping_add(8), 0);
        s.write(self.0.wrapping_add(16), 0);
        s.write(self.0.wrapping_add(24), 0);
    }
    pub fn is_null(self) -> bool {
        self.0 == 0
    }
    /// The `i`-th slot of the CNode at `base`.
    pub fn index(base: u64, i: u64) -> Slot {
        Slot(base.wrapping_add(i.wrapping_mul(layout::cte::SIZE)))
    }
}

/// Global and per-core kernel state.
pub fn ks_get<S: Store>(s: &S, off: u64) -> u64 {
    s.read(s.ks_base().wrapping_add(off))
}

pub fn ks_set<S: Store>(s: &mut S, off: u64, v: u64) {
    let b = s.ks_base();
    s.write(b.wrapping_add(off), v)
}

pub fn node_base<S: Store>(s: &S, cpu: u64) -> u64 {
    s.ks_base().wrapping_add(layout::ks::NODES).wrapping_add(cpu.wrapping_mul(layout::node::SIZE))
}

pub fn node_get<S: Store>(s: &S, cpu: u64, off: u64) -> u64 {
    s.read(node_base(s, cpu).wrapping_add(off))
}

pub fn node_set<S: Store>(s: &mut S, cpu: u64, off: u64, v: u64) {
    let b = node_base(s, cpu);
    s.write(b.wrapping_add(off), v)
}
