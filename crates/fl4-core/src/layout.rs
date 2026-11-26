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

arch_items!("layout.rs");
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
/// Upper bound on cores (DESIGN.md §3): the user setting, at most 64 on
/// x86-64 and 128 on AArch64 (`machine::CoreMask`).
#[cfg(not(feature = "aarch64"))]
pub const MAX_NODES: u64 = if config::MAX_NUM_NODES > 64 { 64 } else { config::MAX_NUM_NODES };
#[cfg(feature = "aarch64")]
pub const MAX_NODES: u64 = if config::MAX_NUM_NODES > 128 { 128 } else { config::MAX_NUM_NODES };

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
    /// ipiReschedulePending). AArch64: cores 0-63 here, 64-127 in
    /// `IPI_PENDING_HI`.
    pub const IPI_PENDING: u64 = 120;
    #[cfg(not(feature = "aarch64"))]
    pub const L1_BITMAP: u64 = 128;
    #[cfg(feature = "aarch64")]
    pub const IPI_PENDING_HI: u64 = 128;
    #[cfg(feature = "aarch64")]
    pub const L1_BITMAP: u64 = 136;
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
    /// x86_64: every core takes 1 GiB pages (CPUID Page1GB), which the
    /// kernel window then uses; without it native mappings of 1 GiB
    /// frames are refused.
    pub const FEATURE_HUGE_PAGES: u64 = 2;
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
