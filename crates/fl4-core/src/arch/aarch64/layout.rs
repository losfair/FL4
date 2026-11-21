/// AArch64 kernel window: the lower 127.5 TiB of the TTBR1 half, since RAM
/// often sits high in the physical address space. The kernel image and
/// device mappings are above it.
pub const PPTR_BASE: u64 = 0xffff_8000_0000_0000;

pub const PPTR_TOP: u64 = 0xffff_ff80_0000_0000;

/// AArch64 TCB, 4 KiB: the same fields, with the 37 registers, the
/// breakpoint state and the FP/SIMD image laid out for AArch64.
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
    /// Hardware debug state (`debug` module): 64 words.
    pub const DEBUG: u64 = 0x240;
    /// V0-V31, FPSR, FPCR (`FPU_STATE_SIZE`), 64-byte aligned.
    pub const FPU: u64 = 0x440;
    pub const FPU_SIZE: u64 = 576;
    /// The backend's lazy-FPU counter, after the image. Only the core
    /// running the thread writes it.
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
    pub const RUN_VCPU: u64 = VCPU + 8;
    pub const END: u64 = RUN_VCPU + 8;
}

/// Register indices into `tcb::REGS` (seL4's AArch64 `enum _register`).
pub mod reg {
    pub const X0: u64 = 0;
    pub const X1: u64 = 1;
    pub const X2: u64 = 2;
    pub const X3: u64 = 3;
    pub const X4: u64 = 4;
    pub const X5: u64 = 5;
    pub const X6: u64 = 6;
    pub const X7: u64 = 7;
    pub const X8: u64 = 8;
    pub const X9: u64 = 9;
    pub const X10: u64 = 10;
    pub const X11: u64 = 11;
    pub const X12: u64 = 12;
    pub const X13: u64 = 13;
    pub const X14: u64 = 14;
    pub const X15: u64 = 15;
    pub const X16: u64 = 16;
    pub const X17: u64 = 17;
    pub const X18: u64 = 18;
    pub const X19: u64 = 19;
    pub const X20: u64 = 20;
    pub const X21: u64 = 21;
    pub const X22: u64 = 22;
    pub const X23: u64 = 23;
    pub const X24: u64 = 24;
    pub const X25: u64 = 25;
    pub const X26: u64 = 26;
    pub const X27: u64 = 27;
    pub const X28: u64 = 28;
    pub const X29: u64 = 29;
    pub const X30: u64 = 30;
    pub const SP_EL0: u64 = 31;
    pub const ELR_EL1: u64 = 32;
    pub const SPSR_EL1: u64 = 33;
    pub const FAULT_IP: u64 = 34;
    pub const TPIDR_EL0: u64 = 35;
    pub const TPIDRRO_EL0: u64 = 36;
    pub const COUNT: u64 = 37;

    pub const NEXT_IP: u64 = ELR_EL1;
    pub const CAP: u64 = X0;
    pub const BADGE: u64 = X0;
    pub const MSG_INFO: u64 = X1;
    pub const REPLY: u64 = X6;
    pub const NBSEND_RECV_DEST: u64 = X8;
    /// The syscall number of seL4's ABI; a trapped foreign syscall's is x8
    /// (l4h 0015).
    pub const SYSCALL: u64 = X7;
    pub const TLS_BASE: u64 = TPIDR_EL0;
}

/// AArch64 interrupt numbering. GIC interrupt IDs 0-15 (SGIs) and 16-31
/// (PPIs) are banked per core and 32-1019 (SPIs) are shared. An SPI's IRQ
/// is its ID; a banked interrupt's is `BANKED_BASE + 32 * core + ID`, so
/// every core has its own state and handler slot for it.
pub mod irq {
    pub const NUM_BANKED: u64 = 32;
    pub const SPI_MIN: u64 = 32;
    pub const SPI_MAX: u64 = 1019;
    pub const BANKED_BASE: u64 = 1024;
    /// Cores with banked interrupt state (the backend's core limit).
    pub const BANKED_CORES: u64 = 16;
    /// The VGIC maintenance interrupt PPI (SBSA).
    pub const VGIC_MAINT_ID: u64 = 25;
    /// The EL2 physical timer's PPI (SBSA), the kernel timer in EL2 VHE mode.
    pub const HYP_TIMER_ID: u64 = 26;
    /// The EL1 virtual timer's PPI (SBSA), the kernel timer in EL1 mode.
    pub const TIMER_ID: u64 = 27;
    /// The EL1 non-secure physical timer's PPI (SBSA), the kernel timer in EL2 nVHE mode.
    pub const PHYS_TIMER_ID: u64 = 30;
    /// SGIs the kernel sends between cores.
    pub const REMOTE_CALL_ID: u64 = 0;
    pub const RESCHEDULE_ID: u64 = 1;
    pub const MAX: u64 = BANKED_BASE + BANKED_CORES * NUM_BANKED - 1;
    pub const COUNT: u64 = MAX + 1;

    /// The IRQ of interrupt `id` as `cpu` takes it.
    pub fn of(id: u64, cpu: u64) -> u64 {
        if id < NUM_BANKED {
            BANKED_BASE.wrapping_add((cpu % BANKED_CORES).wrapping_mul(NUM_BANKED)).wrapping_add(id)
        } else {
            id
        }
    }

    /// The GIC interrupt ID of `irq`.
    pub fn id(irq: u64) -> u64 {
        if irq >= BANKED_BASE {
            (irq - BANKED_BASE) % NUM_BANKED
        } else {
            irq
        }
    }

    /// The core a banked `irq` belongs to (0 for SPIs).
    pub fn core(irq: u64) -> u64 {
        if irq >= BANKED_BASE {
            (irq - BANKED_BASE) / NUM_BANKED
        } else {
            0
        }
    }
}
