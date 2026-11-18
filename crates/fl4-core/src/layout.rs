//! Where things are in kernel memory: object layouts and the kernel's
//! global state. Sizes follow FL4's libsel4 (`fl4_abi::consts::bits`).

use fl4_abi::config;

pub const WORD: u64 = 8;

/// Bound on walks over kernel lists (endpoint, notification, ready and
/// release queues, the CDT). It is never reached when the lists are well
/// formed (a P1 invariant); it makes termination evident to P0.
pub const WALK_FUEL: u64 = u64::MAX;
/// Bound on descents of a deadline-timer tree: a red-black tree of 2^64
/// nodes is at most 128 deep.
pub const TREE_FUEL: u64 = 128;

/// x86_64 kernel window: physical address `p` is at `PPTR_BASE + p`.
pub const PPTR_BASE: u64 = 0xffff_ff80_0000_0000;
/// End of the kernel window (the kernel image is mapped from here).
pub const PPTR_TOP: u64 = 0xffff_ffff_8000_0000;
/// Highest physical address the window covers.
pub const PADDR_TOP: u64 = PPTR_TOP - PPTR_BASE;

pub fn pptr(paddr: u64) -> u64 {
    paddr.wrapping_add(PPTR_BASE)
}

pub fn paddr(pptr: u64) -> u64 {
    pptr.wrapping_sub(PPTR_BASE)
}

/// Capability slot: two words of capability, two of derivation-tree links.
pub mod cte {
    pub const SIZE: u64 = 32;
    pub const CAP0: u64 = 0;
    pub const CAP1: u64 = 8;
    pub const PREV: u64 = 16;
    pub const NEXT: u64 = 24;
}

/// TCB object, 4 KiB: slots, registers, debug state, FPU image, fields.
pub mod tcb {
    pub const SLOT_CTABLE: u64 = 0;
    pub const SLOT_VTABLE: u64 = 1;
    pub const SLOT_BUFFER: u64 = 2;
    pub const SLOT_FAULT_HANDLER: u64 = 3;
    pub const SLOT_TIMEOUT_HANDLER: u64 = 4;
    pub const SLOT_EPT: u64 = 5;
    pub const NUM_SLOTS: u64 = 6;

    /// User registers, in the order of `reg::*`. The entry code saves
    /// straight into this array.
    pub const REGS: u64 = 0x100;
    /// Hardware debug state: DR0-DR3, DR6, DR7, single-step flag.
    pub const DEBUG: u64 = 0x1c0;
    /// XSAVE image (standard layout), 64-byte aligned.
    pub const FPU: u64 = 0x200;
    pub const FPU_SIZE: u64 = 2752;
    /// The x86 backend's lazy-FPU counter (fpu.rs), after the image. Only
    /// the core running the thread writes it, outside transactions.
    pub const FPU_USE: u64 = FPU + FPU_SIZE;

    const F: u64 = 0xd00;
    pub const STATE: u64 = F;
    pub const BLOCK_OBJ: u64 = F + 8;
    pub const BLOCK_BADGE: u64 = F + 16;
    /// bit 0 canGrant, bit 1 canGrantReply, bit 2 isCall.
    pub const BLOCK_FLAGS: u64 = F + 24;
    pub const REPLY_OBJ: u64 = F + 32;
    pub const BOUND_NTFN: u64 = F + 40;
    pub const FAULT_TYPE: u64 = F + 48;
    pub const FAULT_W0: u64 = F + 56;
    pub const FAULT_W1: u64 = F + 64;
    pub const FAULT_W2: u64 = F + 72;
    pub const LF_TYPE: u64 = F + 80;
    pub const LF_W0: u64 = F + 88;
    pub const LF_W1: u64 = F + 96;
    pub const DOMAIN: u64 = F + 104;
    pub const MCP: u64 = F + 112;
    pub const PRIO: u64 = F + 120;
    pub const FLAGS: u64 = F + 128;
    pub const SC: u64 = F + 136;
    pub const YIELD_TO: u64 = F + 144;
    pub const SCHED_NEXT: u64 = F + 152;
    pub const SCHED_PREV: u64 = F + 160;
    pub const EP_NEXT: u64 = F + 168;
    pub const EP_PREV: u64 = F + 176;
    pub const IPC_BUFFER: u64 = F + 184;
    pub const AFFINITY: u64 = F + 192;
    /// l4h 0003 deadline timer: absolute deadline (0 = disarmed), badge,
    /// and AVL tree links in the per-core timer tree.
    pub const TIMER_DEADLINE: u64 = F + 200;
    pub const TIMER_BADGE: u64 = F + 208;
    pub const TIMER_LEFT: u64 = F + 216;
    pub const TIMER_RIGHT: u64 = F + 224;
    pub const TIMER_PARENT: u64 = F + 232;
    pub const TIMER_HEIGHT: u64 = F + 240;
    pub const DEBUG_NEXT: u64 = F + 248;
    pub const DEBUG_PREV: u64 = F + 256;
    /// Bitmask of `state` flags kept beside the state (see `thread`).
    pub const IN_QUEUES: u64 = F + 264;
    /// Thread name for debugging, NUL-terminated, 64 bytes.
    pub const NAME: u64 = F + 272;
    pub const NAME_LEN: u64 = 64;
    pub const VCPU: u64 = NAME + NAME_LEN;
    pub const END: u64 = VCPU + 8;
}

/// Register indices into `tcb::REGS` (seL4's x86_64 `enum _register`).
pub mod reg {
    pub const RDI: u64 = 0;
    pub const RSI: u64 = 1;
    pub const RAX: u64 = 2;
    pub const RBX: u64 = 3;
    pub const RBP: u64 = 4;
    pub const R12: u64 = 5;
    pub const R13: u64 = 6;
    pub const R14: u64 = 7;
    pub const RDX: u64 = 8;
    pub const R10: u64 = 9;
    pub const R8: u64 = 10;
    pub const R9: u64 = 11;
    pub const R15: u64 = 12;
    pub const FLAGS: u64 = 13;
    pub const NEXT_IP: u64 = 14;
    pub const ERROR: u64 = 15;
    pub const RSP: u64 = 16;
    pub const FAULT_IP: u64 = 17;
    pub const R11: u64 = 18;
    pub const RCX: u64 = 19;
    pub const CS: u64 = 20;
    pub const SS: u64 = 21;
    pub const FS_BASE: u64 = 22;
    pub const GS_BASE: u64 = 23;
    pub const COUNT: u64 = 24;

    pub const CAP: u64 = RDI;
    pub const BADGE: u64 = RDI;
    pub const MSG_INFO: u64 = RSI;
    pub const REPLY: u64 = R12;
    pub const NBSEND_RECV_DEST: u64 = R13;
    pub const TLS_BASE: u64 = FS_BASE;
}

/// Endpoint, 16 bytes: queue head, queue tail with the state in bits 0-1.
pub mod ep {
    pub const HEAD: u64 = 0;
    pub const TAIL_STATE: u64 = 8;
}

/// Notification, 64 bytes.
pub mod ntfn {
    pub const HEAD: u64 = 0;
    pub const TAIL_STATE: u64 = 8;
    pub const BADGE: u64 = 16;
    pub const BOUND_TCB: u64 = 24;
    pub const SC: u64 = 32;
}

/// Reply object, 32 bytes. `PREV` and `NEXT` hold a pointer with the
/// "is head" flag in bit 0 (seL4's call_stack_t).
pub mod reply {
    pub const TCB: u64 = 0;
    pub const PREV: u64 = 8;
    pub const NEXT: u64 = 16;
}

/// Scheduling context: a 96-byte header (sizeof(sched_context_t)) followed
/// by the refill ring; the smallest SC (2^7 bytes) holds the header and
/// MIN_REFILLS refills (seL4_CoreSchedContextBytes).
pub mod sc {
    pub const PERIOD: u64 = 0;
    pub const CONSUMED: u64 = 8;
    pub const CORE: u64 = 16;
    pub const TCB: u64 = 24;
    pub const REPLY: u64 = 32;
    pub const NTFN: u64 = 40;
    pub const BADGE: u64 = 48;
    pub const YIELD_FROM: u64 = 56;
    pub const SPORADIC: u64 = 64;
    pub const REFILL_MAX: u64 = 72;
    pub const REFILL_HEAD: u64 = 80;
    pub const REFILL_TAIL: u64 = 88;
    pub const REFILLS: u64 = 96;
    pub const REFILL_SIZE: u64 = 16;
    pub const R_TIME: u64 = 0;
    pub const R_AMOUNT: u64 = 8;
}

pub const NUM_DOMAINS: u64 = config::NUM_DOMAINS;
pub const NUM_DOMAIN_SCHEDULES: u64 = config::NUM_DOMAIN_SCHEDULES;
// As in seL4 (KernelMaxNumNodes depends on KernelNumDomains = 1): the
// domain schedule is global, and switching it does not reach other cores.
const _: () = assert!(NUM_DOMAINS == 1 || config::MAX_NUM_NODES == 1);
pub const NUM_PRIORITIES: u64 = 256;
pub const L2_BITMAP_WORDS: u64 = NUM_PRIORITIES / 64;
/// Upper bound on cores (DESIGN.md §3): the user setting, at most 64.
pub const MAX_NODES: u64 = if config::MAX_NUM_NODES > 64 { 64 } else { config::MAX_NUM_NODES };

/// x86 interrupt numbering (seL4 pc99): IRQ n is vector n + 0x20.
pub mod irq {
    pub const INT_OFFSET: u64 = 0x20;
    pub const ISA_MIN: u64 = 0;
    pub const ISA_MAX: u64 = 15;
    pub const USER_MIN: u64 = 16;
    pub const USER_MAX: u64 = 155 - 0x20;
    pub const TIMER: u64 = 157 - 0x20;
    pub const REMOTE_CALL_IPI: u64 = 158 - 0x20;
    pub const RESCHEDULE_IPI: u64 = 159 - 0x20;
    pub const MAX: u64 = 159 - 0x20;
    pub const COUNT: u64 = MAX + 1;
}

/// Per-core state ("node" in seL4).
pub mod node {
    use super::*;
    pub const CUR_THREAD: u64 = 0;
    pub const IDLE_THREAD: u64 = 8;
    pub const SCHED_ACTION: u64 = 16;
    pub const CUR_SC: u64 = 24;
    pub const IDLE_SC: u64 = 32;
    pub const CONSUMED: u64 = 40;
    pub const CUR_TIME: u64 = 48;
    pub const REPROGRAM: u64 = 56;
    /// The release queue: (head, tail), adjacent like every queue that
    /// sched.rs reads as a pair.
    pub const RELEASE_HEAD: u64 = 64;
    pub const RELEASE_TAIL: u64 = RELEASE_HEAD + 8;
    /// l4h 0006: the deadline the hardware timer is armed for (0 = none).
    pub const ARMED: u64 = 80;
    pub const DEBUG_TCBS: u64 = 88;
    pub const SCHED_CONTROL_USED: u64 = 96;
    /// l4h 0003: root of this core's deadline-timer tree.
    pub const TIMER_ROOT: u64 = 104;
    /// l4h 0003: the armed TCB with the earliest deadline.
    pub const TIMER_MIN: u64 = 112;
    /// Cores this entry must send a reschedule IPI to (seL4
    /// ipiReschedulePending).
    pub const IPI_PENDING: u64 = 120;
    pub const L1_BITMAP: u64 = 128;
    pub const L2_BITMAP: u64 = L1_BITMAP + NUM_DOMAINS * WORD;
    pub const READY_QUEUES: u64 = L2_BITMAP + NUM_DOMAINS * L2_BITMAP_WORDS * WORD;
    /// Each queue is (head, tail).
    pub const SIZE_RAW: u64 = READY_QUEUES + NUM_DOMAINS * NUM_PRIORITIES * 2 * WORD;
    pub const SIZE: u64 = (SIZE_RAW + 63) / 64 * 64;
}

/// Global state, relative to `Store::ks_base`.
pub mod ks {
    use super::*;
    pub const NUM_NODES: u64 = 0;
    pub const CUR_DOMAIN: u64 = 8;
    pub const DOMAIN_TIME: u64 = 16;
    pub const DOM_SCHED_IDX: u64 = 24;
    pub const DOM_SCHED_START: u64 = 32;
    pub const WORK_UNITS: u64 = 40;
    pub const KERNEL_ROOT: u64 = 48;
    pub const BOOT_TIME: u64 = 56;
    /// Index of the next free slot in the boot root CNode (boot only).
    pub const BOOT_SCRATCH: u64 = 64;
    /// CPU features the core needs to know (set at boot).
    pub const FEATURES: u64 = 72;
    pub const FEATURE_NX: u64 = 1;
    pub const VCPU_HEAD: u64 = 80;
    // Bytes 88..192 are free.
    /// Domain schedule: (domain, duration) pairs.
    pub const DOM_SCHEDULE: u64 = 24 * WORD;
    pub const IRQ_STATE: u64 = DOM_SCHEDULE + NUM_DOMAIN_SCHEDULES * 2 * WORD;
    /// One capability slot per IRQ: the notification an IRQ signals.
    pub const IRQ_NODE: u64 = (IRQ_STATE + irq::COUNT * WORD + 31) / 32 * 32;
    pub const IOPORT_BITMAP: u64 = IRQ_NODE + irq::COUNT * cte::SIZE;
    pub const IOPORT_WORDS: u64 = 65536 / 64;
    pub const NODES: u64 = (IOPORT_BITMAP + IOPORT_WORDS * WORD + 63) / 64 * 64;
    /// The ASID table: one pool pointer per 512 ASIDs.
    pub const ASID_TABLE: u64 = NODES + MAX_NODES * node::SIZE;
    pub const NUM_ASID_POOLS: u64 = 2048;
    pub const SIZE: u64 = ASID_TABLE + NUM_ASID_POOLS * WORD;
}
