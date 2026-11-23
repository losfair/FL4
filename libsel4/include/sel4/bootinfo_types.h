/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/config.h>
#include <sel4/macros.h>
#include <sel4/sel4_arch/constants.h>

/* caps with fixed slot positions in the root CNode */
enum seL4_RootCNodeCapSlots {
    seL4_CapNull                =  0, /* null cap */
    seL4_CapInitThreadTCB       =  1, /* initial thread's TCB cap */
    seL4_CapInitThreadCNode     =  2, /* initial thread's root CNode cap */
    seL4_CapInitThreadVSpace    =  3, /* initial thread's VSpace cap */
    seL4_CapIRQControl          =  4, /* global IRQ controller cap */
    seL4_CapASIDControl         =  5, /* global ASID controller cap */
    seL4_CapInitThreadASIDPool  =  6, /* initial thread's ASID pool cap */
    seL4_CapIOPortControl       =  7, /* global IO port control cap (null cap if not supported) */
    seL4_CapIOSpace             =  8, /* global IO space cap (null cap if no IOMMU support) */
    seL4_CapBootInfoFrame       =  9, /* bootinfo frame cap */
    seL4_CapInitThreadIPCBuffer = 10, /* initial thread's IPC buffer frame cap */
    seL4_CapDomain              = 11, /* global domain controller cap */
    seL4_CapSMMUSIDControl      = 12, /* global SMMU SID controller cap, null cap if not supported */
    seL4_CapSMMUCBControl       = 13, /* global SMMU CB controller cap, null cap if not supported */
    seL4_CapInitThreadSC        = 14, /* initial thread's scheduling context cap, null cap if not supported */
    seL4_CapSMC                 = 15, /* global SMC cap, null cap if not supported */
    seL4_NumInitialCaps         = 16
};

/* An Intel TDX guest's attestation control cap shares the slot of the SMC cap,
 * which x86 does not have. It is a null cap outside a TDX guest. */
#define seL4_CapX86TdxControl seL4_CapSMC

/* Legacy code will have assumptions on the vspace root being a Page Directory
 * type, so for now we define one to the other */
#define seL4_CapInitThreadPD seL4_CapInitThreadVSpace

/* types */
typedef seL4_Word seL4_SlotPos;

typedef struct seL4_SlotRegion {
    seL4_SlotPos start; /* first CNode slot position OF region */
    seL4_SlotPos end;   /* first CNode slot position AFTER region */
} seL4_SlotRegion;

typedef struct seL4_UntypedDesc {
    seL4_Word  paddr;   /* physical address of untyped cap  */
    seL4_Uint8 sizeBits;/* size (2^n) bytes of each untyped */
    seL4_Uint8 isDevice;/* whether the untyped is a device  */
    seL4_Uint8 padding[sizeof(seL4_Word) - 2 * sizeof(seL4_Uint8)];
} seL4_UntypedDesc;

SEL4_COMPILE_ASSERT(
    invalid_seL4_UntypedDesc,
    sizeof(seL4_UntypedDesc) == 2 * sizeof(seL4_Word));

typedef struct seL4_BootInfo {
    seL4_Word         extraLen;        /* length of any additional bootinfo information */
    seL4_NodeId       nodeID;          /* ID [0..numNodes-1] of the seL4 node (0 if uniprocessor) */
    seL4_Word         numNodes;        /* number of seL4 nodes (1 if uniprocessor) */
    seL4_Word         numIOPTLevels;   /* number of IOMMU PT levels (0 if no IOMMU support) */
    seL4_IPCBuffer   *ipcBuffer;       /* pointer to initial thread's IPC buffer */
    seL4_SlotRegion   empty;           /* empty slots (null caps) */
    seL4_SlotRegion   sharedFrames;    /* shared-frame caps (shared between seL4 nodes) */
    seL4_SlotRegion   userImageFrames; /* userland-image frame caps */
    seL4_SlotRegion   userImagePaging; /* userland-image paging structure caps */
    seL4_SlotRegion   ioSpaceCaps;     /* IOSpace caps for ARM SMMU */
    seL4_SlotRegion   extraBIPages;    /* caps for any pages used to back the additional bootinfo information */
    seL4_Word         initThreadCNodeSizeBits; /* initial thread's root CNode size (2^n slots) */
    seL4_Domain       initThreadDomain; /* Initial thread's domain ID */
#ifdef CONFIG_KERNEL_MCS
    seL4_SlotRegion   schedcontrol; /* Caps to sched_control for each node */
#endif
    seL4_SlotRegion   untyped;         /* untyped-object caps (untyped caps) */
    seL4_UntypedDesc  untypedList[CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS]; /* information about each untyped */
    /* the untypedList should be the last entry in this struct, in order
     * to make this struct easier to represent in other languages */
} seL4_BootInfo;

/* The boot info frame must be large enough to hold the seL4_BootInfo data
 * structure. Due to internal restrictions, the size must be of the form 2^n and
 * the minimum is one page.
 */
#define seL4_BootInfoFrameBits  seL4_PageBits
#define seL4_BootInfoFrameSize  LIBSEL4_BIT(seL4_BootInfoFrameBits)

SEL4_COMPILE_ASSERT(
    invalid_seL4_BootInfoFrameSize,
    sizeof(seL4_BootInfo) <= seL4_BootInfoFrameSize)

/* If seL4_BootInfo.extraLen > 0, this indicate the presence of additional boot
 * information chunks starting at the offset seL4_BootInfoFrameSize. Userland
 * code often contains the hard-coded assumption that the offset is 4 KiByte,
 * because the boot info frame usually is one page, which is 4 KiByte on x86,
 * Arm and RISC-V.
 * The additional boot info chunks are arch/platform specific, they may or may
 * not exist in any given execution. Each chunk has a header that contains an ID
 * to describe the chunk. All IDs share a global namespace to ensure uniqueness.
 */

typedef enum {
    SEL4_BOOTINFO_HEADER_PADDING            = 0,
    SEL4_BOOTINFO_HEADER_X86_VBE            = 1,
    SEL4_BOOTINFO_HEADER_X86_MBMMAP         = 2,
    SEL4_BOOTINFO_HEADER_X86_ACPI_RSDP      = 3,
    SEL4_BOOTINFO_HEADER_X86_FRAMEBUFFER    = 4,
    SEL4_BOOTINFO_HEADER_X86_TSC_FREQ       = 5, /* frequency is in MHz */
    SEL4_BOOTINFO_HEADER_FDT                = 6, /* device tree */
    SEL4_BOOTINFO_HEADER_AARCH64_ID_REGS    = 7, /* seL4_AArch64IdRegs */
    SEL4_BOOTINFO_HEADER_X86_BOOT_MODULES   = 8, /* seL4_X86_BootModules */
    SEL4_BOOTINFO_HEADER_SHARED_DMA         = 9, /* Header only. DMA requires RetypeShared frames. */
    SEL4_BOOTINFO_HEADER_X86_EXTRA_UNTYPEDS = 10, /* seL4_UntypedDesc[], slots follow untyped.end */
    SEL4_BOOTINFO_HEADER_AARCH64_VIRT_INFO  = 11, /* seL4_AArch64VirtInfo */
    SEL4_BOOTINFO_HEADER_TPM_EVENT_LOG      = 12, /* seL4_TpmEventLog */
    SEL4_BOOTINFO_HEADER_CC_EVENT_LOG       = 13, /* seL4_CcEventLog */
    SEL4_BOOTINFO_HEADER_TDX_INFO           = 14, /* seL4_X86_TdxInfo */
    SEL4_BOOTINFO_HEADER_AARCH64_MSI_INFO   = 15, /* seL4_AArch64MsiInfo */
    /* Add more IDs here, the two elements below must always be at the end. */
    SEL4_BOOTINFO_HEADER_NUM,
    SEL4_FORCE_LONG_ENUM(seL4_BootInfoID)
} seL4_BootInfoID;

/* Common header for all additional bootinfo chunks to describe the chunk. */
typedef struct seL4_BootInfoHeader {
    seL4_Word id;  /* identifier of the following blob */
    seL4_Word len; /* length of the chunk, including this header */
} seL4_BootInfoHeader;

/* SEL4_BOOTINFO_HEADER_AARCH64_ID_REGS: the boot CPU's feature ID
 * registers, which EL0 cannot read.  Unallocated registers read as zero. */
typedef struct seL4_AArch64IdRegs {
    seL4_Word id_aa64isar0;
    seL4_Word id_aa64isar1;
    seL4_Word id_aa64isar2;
    seL4_Word id_aa64pfr0;
    seL4_Word id_aa64pfr1;
} seL4_AArch64IdRegs;

/* SEL4_BOOTINFO_HEADER_AARCH64_VIRT_INFO: EL2/VHE virtualization metadata. */
#define seL4_AArch64VirtInfo_VirtReady (1ul << 0)
#define seL4_AArch64VirtInfo_EL2_VHE   (1ul << 1)
#define seL4_AArch64VirtInfo_VMID16    (1ul << 2)
#define seL4_AArch64VirtInfo_EL2_NVHE  (1ul << 3)

typedef struct seL4_AArch64VirtInfo {
    seL4_Word flags;           /* bit 0 = virt_ready, bit 1 = el2_vhe, bit 2 = vmid16, bit 3 = el2_nvhe */
    seL4_Word ipa_bits;
    seL4_Word gic_version;
    seL4_Word vgic_vtr;
    seL4_Word gicv_paddr;
    seL4_Word gicv_size;
    seL4_Word midr_el1;
    seL4_Word ctr_el0;
    seL4_Word id_aa64mmfr0_el1;
    seL4_Word id_aa64mmfr1_el1;
    seL4_Word id_aa64mmfr2_el1;
    seL4_Word id_aa64dfr0_el1;
    seL4_Word id_aa64dfr1_el1;
} seL4_AArch64VirtInfo;

/* SEL4_BOOTINFO_HEADER_TPM_EVENT_LOG: the UEFI TPM event log, copied by the
 * loader, in device untyped memory (retyping it does not clear it). */
#define seL4_TpmEventLog_Truncated (1ul << 0)
#define seL4_TpmEventLog_Tcg12     (1ul << 1)

typedef struct seL4_TpmEventLog {
    seL4_Word paddr; /* 4 KiB-aligned physical address (in device untypeds) */
    seL4_Word size;  /* exact byte length of the finalized event log */
    seL4_Word flags; /* bit 0 = truncated, bit 1 = tcg_1_2 (0 = TCG 2.0) */
} seL4_TpmEventLog;

/* SEL4_BOOTINFO_HEADER_CC_EVENT_LOG: the UEFI confidential-computing event
 * log (RTMR measurements on Intel TDX), in the same format as the TPM log. */
#define seL4_CcEventLog_Truncated (1ul << 0)
#define seL4_CcEventLog_Tcg12     (1ul << 1)

typedef struct seL4_CcEventLog {
    seL4_Word paddr; /* 4 KiB-aligned physical address (in device untypeds) */
    seL4_Word size;  /* exact byte length of the finalized event log */
    seL4_Word flags; /* bit 0 = truncated, bit 1 = tcg_1_2 (0 = TCG 2.0) */
} seL4_CcEventLog;

/* SEL4_BOOTINFO_HEADER_TDX_INFO: facts about this Intel TDX guest, from
 * TDG.VP.INFO and TDG.VM.RD. */
typedef struct seL4_X86_TdxInfo {
    seL4_Word gpaw;       /* guest physical address width: 48 or 52 */
    seL4_Word attributes; /* TD attributes */
    seL4_Word td_ctls;    /* TDCS.TD_CTLS, 0 if the TDX module has none */
    seL4_Word num_vcpus;
    seL4_Word max_vcpus;
} seL4_X86_TdxInfo;

/* SEL4_BOOTINFO_HEADER_AARCH64_MSI_INFO: the kernel drives a GICv3 ITS, so
 * seL4_IRQControl_GetMSI issues handlers for MSIs.  A device signals event
 * `event` by writing it (32 bits) to `doorbell`, the ITS's GITS_TRANSLATER;
 * its device ID is its PCI requester ID (bus << 8 | devfn). */
typedef struct seL4_AArch64MsiInfo {
    seL4_Word doorbell;    /* physical address of GITS_TRANSLATER */
    seL4_Word num_lpis;    /* GetMSI's irq is below this */
    seL4_Word num_events;  /* its event is below this */
    seL4_Word num_devices; /* its device ID is below this */
} seL4_AArch64MsiInfo;

SEL4_COMPILE_ASSERT(
    invalid_seL4_BootInfoHeader,
    sizeof(seL4_BootInfoHeader) == 2 * sizeof(seL4_Word));
