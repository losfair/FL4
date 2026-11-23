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
#[cfg(not(feature = "aarch64"))]
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

/// `seL4_ObjectType` for AArch64 MCS without EL2. The x86 types follow as
/// numbers no caller can pass, so the x86 object code in fl4-core compiles
/// and never matches.
#[cfg(feature = "aarch64")]
pub mod object {
    pub const Untyped: u64 = 0;
    pub const Tcb: u64 = 1;
    pub const Endpoint: u64 = 2;
    pub const Notification: u64 = 3;
    pub const CapTable: u64 = 4;
    pub const SchedContext: u64 = 5;
    pub const Reply: u64 = 6;
    pub const NonArchCount: u64 = 7;
    pub const ArmHugePage: u64 = 7;
    pub const ArmVSpace: u64 = 8;
    pub const ArmSmallPage: u64 = 9;
    pub const ArmLargePage: u64 = 10;
    pub const ArmPageTable: u64 = 11;
    pub const ArmVcpu: u64 = 12;
    pub const ArmStage2VSpace: u64 = 13;
    pub const Count: u64 = 14;
    pub const X86Pdpt: u64 = u64::MAX - 11;
    pub const X64Pml4: u64 = u64::MAX - 10;
    pub const X64HugePage: u64 = u64::MAX - 9;
    pub const X86Page4K: u64 = u64::MAX - 8;
    pub const X86LargePage: u64 = u64::MAX - 7;
    pub const X86PageTable: u64 = u64::MAX - 6;
    pub const X86PageDirectory: u64 = u64::MAX - 5;
    pub const X86Vcpu: u64 = u64::MAX - 4;
    pub const X86EptPml4: u64 = u64::MAX - 3;
    pub const X86EptPdpt: u64 = u64::MAX - 2;
    pub const X86EptPd: u64 = u64::MAX - 1;
    pub const X86EptPt: u64 = u64::MAX;
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
    #[cfg(not(feature = "aarch64"))]
    pub const VCPU: u64 = 15;
    #[cfg(feature = "aarch64")]
    pub const VCPU: u64 = 12;
    pub const STAGE2_VSPACE: u64 = 13;
    pub const ENDPOINT: u64 = 4;
    pub const NOTIFICATION: u64 = 6;
    pub const REPLY: u64 = 5;
    pub const PAGE_TABLE: u64 = 12;
    pub const ASID_POOL: u64 = 12;
    pub const ASID_POOL_INDEX: u64 = 9;
    #[cfg(not(feature = "aarch64"))]
    pub const NUM_ASID_POOLS: u64 = 11;
    /// AArch64: 16-bit hardware ASIDs (l4h 0016, `TCR_EL1.AS`).
    #[cfg(feature = "aarch64")]
    pub const NUM_ASID_POOLS: u64 = 7;
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
/// page lower. AArch64 without EL2 has the same value (`seL4_UserTop`).
pub const USER_TOP: u64 = 0x0000_7fff_ffff_ffff;
pub const NUM_PRIORITIES: u64 = 256;
pub const MAX_PRIO: u64 = NUM_PRIORITIES - 1;
/// FL4: standard-layout XSAVE image up to PKRU (DESIGN.md §2, §3).
#[cfg(not(feature = "aarch64"))]
pub const FPU_STATE_SIZE: u64 = 2696;
/// AArch64: V0-V31, then FPSR and FPCR as 32-bit words.
#[cfg(feature = "aarch64")]
pub const FPU_STATE_SIZE: u64 = 64 * 8 + 8;

/// `seL4_FaultType` tags.
pub mod fault {
    pub const NullFault: u64 = 0;
    pub const CapFault: u64 = 1;
    pub const UnknownSyscall: u64 = 2;
    pub const UserException: u64 = 3;
    pub const DebugException: u64 = 4;
    pub const Timeout: u64 = 5;
    pub const VMFault: u64 = 6;
    #[cfg(feature = "aarch64")]
    pub const VGICMaintenance: u64 = 7;
    #[cfg(feature = "aarch64")]
    pub const VCPUFault: u64 = 8;
    #[cfg(feature = "aarch64")]
    pub const VPPIEvent: u64 = 9;
}

/// AArch64 `seL4_VCPUReg` indices (0..=24 match upstream seL4; 25..=63 are
/// FL4 extensions for hypervisor/debug/VGIC state).
#[cfg(feature = "aarch64")]
pub mod vcpu_reg {
    pub const SCTLR: u64 = 0;
    pub const CPACR: u64 = 1;
    pub const TCR: u64 = 2;
    pub const TTBR0: u64 = 3;
    pub const TTBR1: u64 = 4;
    pub const MAIR: u64 = 5;
    pub const AMAIR: u64 = 6;
    pub const CIDR: u64 = 7;
    pub const AFSR0: u64 = 8;
    pub const AFSR1: u64 = 9;
    pub const ESR: u64 = 10;
    pub const FAR: u64 = 11;
    pub const PAR: u64 = 12;
    pub const VBAR: u64 = 13;
    pub const TPIDR_EL1: u64 = 14;
    pub const VMPIDR_EL2: u64 = 15;
    pub const SP_EL1: u64 = 16;
    pub const ELR_EL1: u64 = 17;
    pub const SPSR_EL1: u64 = 18;
    pub const CSSELR_EL1: u64 = 19;
    pub const VDISR_EL2: u64 = 20;
    pub const CNTV_CTL: u64 = 21;
    pub const CNTV_CVAL: u64 = 22;
    pub const CNTVOFF: u64 = 23;
    pub const CNTKCTL_EL1: u64 = 24;
    pub const VPIDR_EL2: u64 = 25;
    pub const HCR_EL2: u64 = 26;
    pub const VSESR_EL2: u64 = 27;
    pub const ACTLR_EL1: u64 = 28;
    pub const MDSCR_EL1: u64 = 29;
    pub const MDCCINT_EL1: u64 = 30;
    pub const FAR_EL2: u64 = 31;
    pub const HPFAR_EL2: u64 = 32;
    pub const ESR_EL2: u64 = 33;
    pub const VGIC_VTR: u64 = 34;
    pub const VGIC_HCR: u64 = 35;
    pub const VGIC_VMCR: u64 = 36;
    pub const VGIC_MISR: u64 = 37;
    pub const VGIC_EISR: u64 = 38;
    pub const VGIC_ELRSR: u64 = 39;
    pub const VGIC_AP0R0: u64 = 40;
    pub const VGIC_AP0R1: u64 = 41;
    pub const VGIC_AP0R2: u64 = 42;
    pub const VGIC_AP0R3: u64 = 43;
    pub const VGIC_AP1R0: u64 = 44;
    pub const VGIC_AP1R1: u64 = 45;
    pub const VGIC_AP1R2: u64 = 46;
    pub const VGIC_AP1R3: u64 = 47;
    pub const VGIC_LR0: u64 = 48;
    pub const VGIC_LR15: u64 = 63;
    pub const NUM: u64 = 64;
}

/// Bitmask for `ARMVCPUReadState` / `ARMVCPUWriteState`.
#[cfg(feature = "aarch64")]
pub mod vcpu_state_mask {
    pub const EL1_SYSREGS: u64 = 1 << 0;
    pub const HYP: u64 = 1 << 1;
    pub const TIMER: u64 = 1 << 2;
    pub const VGIC: u64 = 1 << 3;
    pub const GPRS: u64 = 1 << 4;
    pub const VGIC_LR: u64 = 1 << 5;
    pub const ALL: u64 = EL1_SYSREGS | HYP | TIMER | VGIC | GPRS | VGIC_LR;
    pub const SIZE: u64 = 1024;
}

/// Exit reasons (`stop` word) returned by `ARMVCPURun`.
#[cfg(feature = "aarch64")]
pub mod vcpu_run_stop {
    pub const INTERRUPT: u64 = 0;
    pub const VMFAULT: u64 = 1;
    pub const VCPUFAULT: u64 = 2;
    pub const VGIC_MAINT: u64 = 3;
    pub const VPPI: u64 = 4;
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

/// `seL4_ARM_VMAttributes`.
#[cfg(feature = "aarch64")]
pub mod arm_vm_attr {
    pub const PAGE_CACHEABLE: u64 = 1;
    pub const PARITY_ENABLED: u64 = 2;
    pub const EXECUTE_NEVER: u64 = 4;
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

/// `seL4_AArch64VirtInfo::flags` bits (`bootinfo_header::AARCH64_VIRT_INFO`).
#[cfg(feature = "aarch64")]
pub mod virt_info_flag {
    pub const VIRT_READY: u64 = 1 << 0;
    pub const EL2_VHE: u64 = 1 << 1;
    pub const VMID16: u64 = 1 << 2;
    pub const EL2_NVHE: u64 = 1 << 3;
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
    pub const SHARED_DMA: u64 = 9;
    /// l4h 0047: untyped descriptors past the BootInfo's 230, whose caps
    /// follow `untyped.end`.
    pub const X86_EXTRA_UNTYPEDS: u64 = 10;
    /// AArch64 EL2/VHE virtualization capabilities and GIC/ID metadata.
    pub const AARCH64_VIRT_INFO: u64 = 11;
    /// UEFI TPM event log (seL4_TpmEventLog: paddr, size, flags).
    pub const TPM_EVENT_LOG: u64 = 12;
    /// UEFI confidential-computing event log (seL4_CcEventLog: paddr,
    /// size, flags; the flags are `tpm_event_log_flag`'s).
    pub const CC_EVENT_LOG: u64 = 13;
    /// Intel TDX guest facts (seL4_X86_TdxInfo: gpaw, attributes, td_ctls,
    /// num_vcpus, max_vcpus).
    pub const TDX_INFO: u64 = 14;
    /// AArch64 MSIs through a GICv3 ITS (seL4_AArch64MsiInfo: doorbell,
    /// num_lpis, num_events, num_devices), when the kernel drives one.
    pub const AARCH64_MSI_INFO: u64 = 15;
}

/// `bootinfo_header::TPM_EVENT_LOG` flags (libsel4 `seL4_TpmEventLog_*`).
pub mod tpm_event_log_flag {
    /// Events are missing at the end of the log.
    pub const TRUNCATED: u64 = 1 << 0;
    /// The log is in the TCG 1.2 (SHA-1) format; clear for TCG 2.0 crypto agile.
    pub const TCG_1_2: u64 = 1 << 1;
}

/// `bootinfo_header::CC_EVENT_LOG` flags (libsel4 `seL4_CcEventLog_*`).
pub mod cc_event_log_flag {
    pub const TRUNCATED: u64 = super::tpm_event_log_flag::TRUNCATED;
    pub const TCG_1_2: u64 = super::tpm_event_log_flag::TCG_1_2;
}
