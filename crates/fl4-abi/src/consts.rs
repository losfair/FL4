//! Constants of FL4's libsel4 that the kernel must agree with. Values follow
//! `libsel4/` (FL4's copy); where FL4 differs from seL4 the libsel4 header
//! says so too.

/// `seL4_Error`.
pub mod error {
    pub const NoError: u64 = 0;
    pub const InvalidArgument: u64 = 1;
    pub const InvalidCapability: u64 = 2;
    pub const IllegalOperation: u64 = 3;
    pub const RangeError: u64 = 4;
    pub const AlignmentError: u64 = 5;
    pub const FailedLookup: u64 = 6;
    pub const TruncatedMessage: u64 = 7;
    pub const DeleteFirst: u64 = 8;
    pub const RevokeFirst: u64 = 9;
    pub const NotEnoughMemory: u64 = 10;
}

/// `seL4_ObjectType` for x86_64 MCS with huge pages.
pub mod object {
    pub const Untyped: u64 = 0;
    pub const Tcb: u64 = 1;
    pub const Endpoint: u64 = 2;
    pub const Notification: u64 = 3;
    pub const CapTable: u64 = 4;
    pub const SchedContext: u64 = 5;
    pub const Reply: u64 = 6;
    pub const NonArchCount: u64 = 7;
    pub const X86Pdpt: u64 = 7;
    pub const X64Pml4: u64 = 8;
    pub const X64HugePage: u64 = 9;
    pub const X86Page4K: u64 = 10;
    pub const X86LargePage: u64 = 11;
    pub const X86PageTable: u64 = 12;
    pub const X86PageDirectory: u64 = 13;
    pub const X86Vcpu: u64 = 14;
    pub const X86EptPml4: u64 = 15;
    pub const X86EptPdpt: u64 = 16;
    pub const X86EptPd: u64 = 17;
    pub const X86EptPt: u64 = 18;
    pub const Count: u64 = 19;
}

/// Object sizes (`seL4_*Bits`).
pub mod bits {
    pub const WORD_BITS: u64 = 64;
    pub const WORD_SIZE_BITS: u64 = 3;
    pub const PAGE: u64 = 12;
    pub const LARGE_PAGE: u64 = 21;
    pub const HUGE_PAGE: u64 = 30;
    pub const SLOT: u64 = 5;
    /// FL4: 4 KiB, to hold the AVX-512 XSAVE image (DESIGN.md §2).
    pub const TCB: u64 = 12;
    pub const VCPU: u64 = 15;
    pub const ENDPOINT: u64 = 4;
    pub const NOTIFICATION: u64 = 6;
    pub const REPLY: u64 = 5;
    pub const PAGE_TABLE: u64 = 12;
    pub const ASID_POOL: u64 = 12;
    pub const ASID_POOL_INDEX: u64 = 9;
    pub const NUM_ASID_POOLS: u64 = 11;
    pub const MIN_UNTYPED: u64 = 4;
    pub const MAX_UNTYPED: u64 = 47;
    pub const MIN_SCHED_CONTEXT: u64 = 7;
    pub const IPC_BUFFER: u64 = 10;
}

pub const CORE_SCHED_CONTEXT_BYTES: u64 = 10 * 8 + 6 * 8;
pub const REFILL_SIZE_BYTES: u64 = 16;

pub const MSG_MAX_LENGTH: u64 = 120;
pub const MSG_MAX_EXTRA_CAPS: u64 = 3;
pub const FAST_MESSAGE_REGISTERS: u64 = 4;
/// The kernel's `USER_TOP` (C seL4 pc99 `hardware.h`): the last address
/// below the sign-extension hole. Not libsel4's `seL4_UserTop`, which is a
/// page lower.
pub const USER_TOP: u64 = 0x0000_7fff_ffff_ffff;
pub const NUM_PRIORITIES: u64 = 256;
pub const MAX_PRIO: u64 = NUM_PRIORITIES - 1;
/// FL4: standard-layout XSAVE image up to PKRU (DESIGN.md §2, §3).
pub const FPU_STATE_SIZE: u64 = 2696;

/// `seL4_FaultType` tags.
pub mod fault {
    pub const NullFault: u64 = 0;
    pub const CapFault: u64 = 1;
    pub const UnknownSyscall: u64 = 2;
    pub const UserException: u64 = 3;
    pub const DebugException: u64 = 4;
    pub const Timeout: u64 = 5;
    pub const VMFault: u64 = 6;
}

/// `seL4_LookupFailureType`.
pub mod lookup {
    pub const NoFailure: u64 = 0;
    pub const InvalidRoot: u64 = 1;
    pub const MissingCapability: u64 = 2;
    pub const DepthMismatch: u64 = 3;
    pub const GuardMismatch: u64 = 4;
}

/// `seL4_TCBFlag`.
pub mod tcb_flag {
    pub const FPU_DISABLED: u64 = 0x1;
    /// l4h 0001: every syscall instruction becomes an UnknownSyscall fault.
    pub const TRAP_SYSCALLS: u64 = 0x2;
    pub const MASK: u64 = FPU_DISABLED | TRAP_SYSCALLS;
}

/// `seL4_SchedContextFlag`.
pub mod sc_flag {
    pub const SPORADIC: u64 = 0x1;
}

/// `seL4_X86_VMAttributes`.
pub mod vm_attr {
    pub const WRITE_BACK: u64 = 0;
    pub const WRITE_THROUGH: u64 = 1;
    pub const CACHE_DISABLED: u64 = 2;
    pub const UNCACHEABLE: u64 = 3;
    pub const WRITE_COMBINING: u64 = 4;
    /// l4h 0009.
    pub const EXECUTE_NEVER: u64 = 8;
    /// l4h 0017.
    pub const DEFER_FLUSH: u64 = 16;
}

/// Root task CSpace slots (`seL4_RootCNodeCapSlots`).
pub mod root_slot {
    pub const Null: u64 = 0;
    pub const InitThreadTCB: u64 = 1;
    pub const InitThreadCNode: u64 = 2;
    pub const InitThreadVSpace: u64 = 3;
    pub const IRQControl: u64 = 4;
    pub const ASIDControl: u64 = 5;
    pub const InitThreadASIDPool: u64 = 6;
    pub const IOPortControl: u64 = 7;
    pub const IOSpace: u64 = 8;
    pub const BootInfoFrame: u64 = 9;
    pub const InitThreadIPCBuffer: u64 = 10;
    pub const Domain: u64 = 11;
    pub const SMMUSIDControl: u64 = 12;
    pub const SMMUCBControl: u64 = 13;
    pub const InitThreadSC: u64 = 14;
    pub const SMC: u64 = 15;
    pub const NumInitialCaps: u64 = 16;
}

/// `SEL4_BOOTINFO_HEADER_*`.
pub mod bootinfo_header {
    pub const PADDING: u64 = 0;
    pub const X86_VBE: u64 = 1;
    pub const X86_MBMMAP: u64 = 2;
    pub const X86_ACPI_RSDP: u64 = 3;
    pub const X86_FRAMEBUFFER: u64 = 4;
    pub const X86_TSC_FREQ: u64 = 5;
    pub const FDT: u64 = 6;
    pub const AARCH64_ID_REGS: u64 = 7;
    pub const X86_BOOT_MODULES: u64 = 8;
}
