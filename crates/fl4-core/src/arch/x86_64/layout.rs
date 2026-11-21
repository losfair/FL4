/// x86_64 kernel window: physical address `p` is at `PPTR_BASE + p`.
pub const PPTR_BASE: u64 = 0xffff_ff80_0000_0000;

/// End of the kernel window (the kernel image is mapped from here).
pub const PPTR_TOP: u64 = 0xffff_ffff_8000_0000;

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
    /// the core running the thread writes it.
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
