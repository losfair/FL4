/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the VCPU field tables** (proofs/VIRT-PLAN.md §3).

The abstract VCPU state is not FL4's 32 KiB image (`vcpu.rs`: VMCB page,
VMCS software image, metadata, I/O bitmap) but a table of *fields*, per
backend, each with a class: readable (ReadVMCS / ReadVMCB / ReadMSR may
return it), writable (WriteVMCS / WriteVMCB / WriteMSR may set it,
through the sanitize rule of `Ext/VirtSanitize`), guest-changed (one
guest step may change it, `Ext/VirtGuest`), or none of these.

* `VField.vmcs enc`: a VMCS field by its encoding (Intel SDM Vol. 3D
  App. B; bits 14:13 width, 11:10 type: 0 control, 1 VM-exit
  information, 2 guest state, 3 host state). FL4's tables are
  `vcpu::WRITE_FIELDS` (73) and `vcpu::READ_FIELDS` (84), 86 fields in
  all; host-state fields are in neither (the trusted layer writes them).
* `VField.vmcb off`: a VMCB word by byte offset (AMD APM Vol. 2 App. B,
  control area 0x000..0x3ff, state save area from 0x400). Readable: any
  8-aligned offset below `svmEnd` (0x6e8) that is not hidden; writable:
  the 50 offsets of `vcpu::sanitize_vmcb`.
* `VField.gpr i`: the 15 general registers of the VMEnter layout (RAX,
  RBX, RCX, RDX, RSI, RDI, RBP, R8..R15; MR 10 + i; FL4 `vcpu::REGS`).
* `VField.msr m`: the l4h VCPU MSRs (ReadMSR / WriteMSR): `IA32_STAR`,
  `IA32_LSTAR`, `IA32_CSTAR`, `IA32_FMASK`, `IA32_KERNEL_GS_BASE`, and
  FL4's pseudo-MSRs `SEL4_VCPU_MSR_CR2` (0xffffffff) and
  `SEL4_VCPU_MSR_XCR0` (0xfffffffe) (libsel4 `sel4/arch/vmenter.h`).

One value has one place: on SVM the syscall MSRs and CR2 *are* VMCB
save-area words and the VMCB's RAX is GPR 0 (FL4 keeps both copies in
sync, `vcpu::decode` WriteRegisters/WriteVMCB and `vm::run`).
`VField.canon` maps every field to its single representative, and the
abstract state (`Ext/VirtState`) stores only representatives.

Out of the spec (refinement only, VIRT-PLAN.md §3.4): the VCPU list
words `NEXT`/`PREV`, `VALID`/`PENDING` as words (they are the exit
record's flags), `SVM_CPU` (SVM ASID retention), the VMCB clean bits
(0x0c0) and ASID word (0x058), the physical pointers the trusted layer
writes into the VMCB (0x040, 0x048, 0x0b0), per-core VMCS caches.
The VMCB clean bits and ASID word read as 0 in the spec
(`Svm.hiddenRead`, decision Q4 of 2026-11-21; FL4 code differs until
FINDING V3 is fixed).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtBackend

namespace Fl4Spec

noncomputable section
open Classical

-- `VField` itself is in `Ext/VirtObj` (the heap object needs it).

namespace Vmx
/-- `GUEST_ES_SELECTOR` (SDM Vol. 3D App. B). -/
def guestEsSelector : Word := 0x00000800
/-- `GUEST_CS_SELECTOR` (SDM Vol. 3D App. B). -/
def guestCsSelector : Word := 0x00000802
/-- `GUEST_SS_SELECTOR` (SDM Vol. 3D App. B). -/
def guestSsSelector : Word := 0x00000804
/-- `GUEST_DS_SELECTOR` (SDM Vol. 3D App. B). -/
def guestDsSelector : Word := 0x00000806
/-- `GUEST_FS_SELECTOR` (SDM Vol. 3D App. B). -/
def guestFsSelector : Word := 0x00000808
/-- `GUEST_GS_SELECTOR` (SDM Vol. 3D App. B). -/
def guestGsSelector : Word := 0x0000080a
/-- `GUEST_LDTR_SELECTOR` (SDM Vol. 3D App. B). -/
def guestLdtrSelector : Word := 0x0000080c
/-- `GUEST_TR_SELECTOR` (SDM Vol. 3D App. B). -/
def guestTrSelector : Word := 0x0000080e
/-- `CONTROL_TSC_OFFSET` (SDM Vol. 3D App. B). -/
def controlTscOffset : Word := 0x00002010
/-- `DATA_GUEST_PHYSICAL` (SDM Vol. 3D App. B). -/
def dataGuestPhysical : Word := 0x00002400
/-- `GUEST_DEBUGCTRL` (SDM Vol. 3D App. B). -/
def guestDebugctrl : Word := 0x00002802
/-- `GUEST_PAT` (SDM Vol. 3D App. B). -/
def guestPat : Word := 0x00002804
/-- `GUEST_EFER` (SDM Vol. 3D App. B). -/
def guestEfer : Word := 0x00002806
/-- `GUEST_PERF_GLOBAL_CTRL` (SDM Vol. 3D App. B). -/
def guestPerfGlobalCtrl : Word := 0x00002808
/-- `GUEST_PDPTE0` (SDM Vol. 3D App. B). -/
def guestPdpte0 : Word := 0x0000280a
/-- `GUEST_PDPTE1` (SDM Vol. 3D App. B). -/
def guestPdpte1 : Word := 0x0000280c
/-- `GUEST_PDPTE2` (SDM Vol. 3D App. B). -/
def guestPdpte2 : Word := 0x0000280e
/-- `GUEST_PDPTE3` (SDM Vol. 3D App. B). -/
def guestPdpte3 : Word := 0x00002810
/-- `CONTROL_PIN_EXECUTION_CONTROLS` (SDM Vol. 3D App. B). -/
def controlPinExecutionControls : Word := 0x00004000
/-- `CONTROL_PRIMARY_PROCESSOR_CONTROLS` (SDM Vol. 3D App. B). -/
def controlPrimaryProcessorControls : Word := 0x00004002
/-- `CONTROL_EXCEPTION_BITMAP` (SDM Vol. 3D App. B). -/
def controlExceptionBitmap : Word := 0x00004004
/-- `CONTROL_EXIT_CONTROLS` (SDM Vol. 3D App. B). -/
def controlExitControls : Word := 0x0000400c
/-- `CONTROL_ENTRY_CONTROLS` (SDM Vol. 3D App. B). -/
def controlEntryControls : Word := 0x00004012
/-- `CONTROL_ENTRY_INTERRUPTION_INFO` (SDM Vol. 3D App. B). -/
def controlEntryInterruptionInfo : Word := 0x00004016
/-- `CONTROL_ENTRY_EXCEPTION_ERROR_CODE` (SDM Vol. 3D App. B). -/
def controlEntryExceptionErrorCode : Word := 0x00004018
/-- `CONTROL_ENTRY_INSTRUCTION_LENGTH` (SDM Vol. 3D App. B). -/
def controlEntryInstructionLength : Word := 0x0000401a
/-- `CONTROL_SECONDARY_PROCESSOR_CONTROLS` (SDM Vol. 3D App. B). -/
def controlSecondaryProcessorControls : Word := 0x0000401e
/-- `DATA_INSTRUCTION_ERROR` (SDM Vol. 3D App. B). -/
def dataInstructionError : Word := 0x00004400
/-- `DATA_EXIT_INTERRUPT_INFO` (SDM Vol. 3D App. B). -/
def dataExitInterruptInfo : Word := 0x00004404
/-- `DATA_EXIT_INTERRUPT_ERROR` (SDM Vol. 3D App. B). -/
def dataExitInterruptError : Word := 0x00004406
/-- `DATA_IDT_VECTOR_INFO` (SDM Vol. 3D App. B). -/
def dataIdtVectorInfo : Word := 0x00004408
/-- `DATA_IDT_VECTOR_ERROR` (SDM Vol. 3D App. B). -/
def dataIdtVectorError : Word := 0x0000440a
/-- `DATA_EXIT_INSTRUCTION_LENGTH` (SDM Vol. 3D App. B). -/
def dataExitInstructionLength : Word := 0x0000440c
/-- `DATA_EXIT_INSTRUCTION_INFO` (SDM Vol. 3D App. B). -/
def dataExitInstructionInfo : Word := 0x0000440e
/-- `GUEST_ES_LIMIT` (SDM Vol. 3D App. B). -/
def guestEsLimit : Word := 0x00004800
/-- `GUEST_CS_LIMIT` (SDM Vol. 3D App. B). -/
def guestCsLimit : Word := 0x00004802
/-- `GUEST_SS_LIMIT` (SDM Vol. 3D App. B). -/
def guestSsLimit : Word := 0x00004804
/-- `GUEST_DS_LIMIT` (SDM Vol. 3D App. B). -/
def guestDsLimit : Word := 0x00004806
/-- `GUEST_FS_LIMIT` (SDM Vol. 3D App. B). -/
def guestFsLimit : Word := 0x00004808
/-- `GUEST_GS_LIMIT` (SDM Vol. 3D App. B). -/
def guestGsLimit : Word := 0x0000480a
/-- `GUEST_LDTR_LIMIT` (SDM Vol. 3D App. B). -/
def guestLdtrLimit : Word := 0x0000480c
/-- `GUEST_TR_LIMIT` (SDM Vol. 3D App. B). -/
def guestTrLimit : Word := 0x0000480e
/-- `GUEST_GDTR_LIMIT` (SDM Vol. 3D App. B). -/
def guestGdtrLimit : Word := 0x00004810
/-- `GUEST_IDTR_LIMIT` (SDM Vol. 3D App. B). -/
def guestIdtrLimit : Word := 0x00004812
/-- `GUEST_ES_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestEsAccessRights : Word := 0x00004814
/-- `GUEST_CS_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestCsAccessRights : Word := 0x00004816
/-- `GUEST_SS_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestSsAccessRights : Word := 0x00004818
/-- `GUEST_DS_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestDsAccessRights : Word := 0x0000481a
/-- `GUEST_FS_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestFsAccessRights : Word := 0x0000481c
/-- `GUEST_GS_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestGsAccessRights : Word := 0x0000481e
/-- `GUEST_LDTR_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestLdtrAccessRights : Word := 0x00004820
/-- `GUEST_TR_ACCESS_RIGHTS` (SDM Vol. 3D App. B). -/
def guestTrAccessRights : Word := 0x00004822
/-- `GUEST_INTERRUPTABILITY` (SDM Vol. 3D App. B). -/
def guestInterruptability : Word := 0x00004824
/-- `GUEST_ACTIVITY` (SDM Vol. 3D App. B). -/
def guestActivity : Word := 0x00004826
/-- `GUEST_SMBASE` (SDM Vol. 3D App. B). -/
def guestSmbase : Word := 0x00004828
/-- `GUEST_SYSENTER_CS` (SDM Vol. 3D App. B). -/
def guestSysenterCs : Word := 0x0000482a
/-- `GUEST_PREEMPTION_TIMER_VALUE` (SDM Vol. 3D App. B). -/
def guestPreemptionTimerValue : Word := 0x0000482e
/-- `CONTROL_CR0_MASK` (SDM Vol. 3D App. B). -/
def controlCr0Mask : Word := 0x00006000
/-- `CONTROL_CR4_MASK` (SDM Vol. 3D App. B). -/
def controlCr4Mask : Word := 0x00006002
/-- `CONTROL_CR0_READ_SHADOW` (SDM Vol. 3D App. B). -/
def controlCr0ReadShadow : Word := 0x00006004
/-- `CONTROL_CR4_READ_SHADOW` (SDM Vol. 3D App. B). -/
def controlCr4ReadShadow : Word := 0x00006006
/-- `DATA_IO_RCX` (SDM Vol. 3D App. B). -/
def dataIoRcx : Word := 0x00006402
/-- `DATA_IO_RSI` (SDM Vol. 3D App. B). -/
def dataIoRsi : Word := 0x00006404
/-- `DATA_IO_RDI` (SDM Vol. 3D App. B). -/
def dataIoRdi : Word := 0x00006406
/-- `DATA_IO_RIP` (SDM Vol. 3D App. B). -/
def dataIoRip : Word := 0x00006408
/-- `DATA_GUEST_LINEAR_ADDRESS` (SDM Vol. 3D App. B). -/
def dataGuestLinearAddress : Word := 0x0000640a
/-- `GUEST_CR0` (SDM Vol. 3D App. B). -/
def guestCr0 : Word := 0x00006800
/-- `GUEST_CR3` (SDM Vol. 3D App. B). -/
def guestCr3 : Word := 0x00006802
/-- `GUEST_CR4` (SDM Vol. 3D App. B). -/
def guestCr4 : Word := 0x00006804
/-- `GUEST_ES_BASE` (SDM Vol. 3D App. B). -/
def guestEsBase : Word := 0x00006806
/-- `GUEST_CS_BASE` (SDM Vol. 3D App. B). -/
def guestCsBase : Word := 0x00006808
/-- `GUEST_SS_BASE` (SDM Vol. 3D App. B). -/
def guestSsBase : Word := 0x0000680a
/-- `GUEST_DS_BASE` (SDM Vol. 3D App. B). -/
def guestDsBase : Word := 0x0000680c
/-- `GUEST_FS_BASE` (SDM Vol. 3D App. B). -/
def guestFsBase : Word := 0x0000680e
/-- `GUEST_GS_BASE` (SDM Vol. 3D App. B). -/
def guestGsBase : Word := 0x00006810
/-- `GUEST_LDTR_BASE` (SDM Vol. 3D App. B). -/
def guestLdtrBase : Word := 0x00006812
/-- `GUEST_TR_BASE` (SDM Vol. 3D App. B). -/
def guestTrBase : Word := 0x00006814
/-- `GUEST_GDTR_BASE` (SDM Vol. 3D App. B). -/
def guestGdtrBase : Word := 0x00006816
/-- `GUEST_IDTR_BASE` (SDM Vol. 3D App. B). -/
def guestIdtrBase : Word := 0x00006818
/-- `GUEST_DR7` (SDM Vol. 3D App. B). -/
def guestDr7 : Word := 0x0000681a
/-- `GUEST_RSP` (SDM Vol. 3D App. B). -/
def guestRsp : Word := 0x0000681c
/-- `GUEST_RIP` (SDM Vol. 3D App. B). -/
def guestRip : Word := 0x0000681e
/-- `GUEST_RFLAGS` (SDM Vol. 3D App. B). -/
def guestRflags : Word := 0x00006820
/-- `GUEST_PENDING_DEBUG_EXCEPTIONS` (SDM Vol. 3D App. B). -/
def guestPendingDebugExceptions : Word := 0x00006822
/-- `GUEST_SYSENTER_ESP` (SDM Vol. 3D App. B). -/
def guestSysenterEsp : Word := 0x00006824
/-- `GUEST_SYSENTER_EIP` (SDM Vol. 3D App. B). -/
def guestSysenterEip : Word := 0x00006826

/-- FL4 `vcpu::WRITE_FIELDS`: the VMCS fields WriteVMCS accepts, in FL4's order (73). -/
def vmxWriteFields : List Word :=
  [guestRip,
   guestRsp,
   guestEsSelector,
   guestCsSelector,
   guestSsSelector,
   guestDsSelector,
   guestFsSelector,
   guestGsSelector,
   guestLdtrSelector,
   guestTrSelector,
   guestDebugctrl,
   guestPat,
   guestEfer,
   guestPerfGlobalCtrl,
   guestPdpte0,
   guestPdpte1,
   guestPdpte2,
   guestPdpte3,
   guestEsLimit,
   guestCsLimit,
   guestSsLimit,
   guestDsLimit,
   guestFsLimit,
   guestGsLimit,
   guestLdtrLimit,
   guestTrLimit,
   guestGdtrLimit,
   guestIdtrLimit,
   guestEsAccessRights,
   guestCsAccessRights,
   guestSsAccessRights,
   guestDsAccessRights,
   guestFsAccessRights,
   guestGsAccessRights,
   guestLdtrAccessRights,
   guestTrAccessRights,
   guestInterruptability,
   guestSmbase,
   guestSysenterCs,
   guestPreemptionTimerValue,
   guestEsBase,
   guestCsBase,
   guestSsBase,
   guestDsBase,
   guestFsBase,
   guestGsBase,
   guestLdtrBase,
   guestTrBase,
   guestGdtrBase,
   guestIdtrBase,
   guestDr7,
   guestRflags,
   guestPendingDebugExceptions,
   guestSysenterEsp,
   guestSysenterEip,
   controlCr0ReadShadow,
   controlCr4ReadShadow,
   guestCr3,
   controlEntryInterruptionInfo,
   controlEntryExceptionErrorCode,
   controlEntryInstructionLength,
   controlTscOffset,
   guestActivity,
   controlExceptionBitmap,
   controlCr0Mask,
   controlCr4Mask,
   controlPinExecutionControls,
   controlPrimaryProcessorControls,
   controlSecondaryProcessorControls,
   controlEntryControls,
   controlExitControls,
   guestCr0,
   guestCr4]

/-- FL4 `vcpu::READ_FIELDS`: the VMCS fields ReadVMCS accepts, in FL4's order (84). -/
def vmxReadFields : List Word :=
  [guestRip,
   guestRsp,
   guestEsSelector,
   guestCsSelector,
   guestSsSelector,
   guestDsSelector,
   guestFsSelector,
   guestGsSelector,
   guestLdtrSelector,
   guestTrSelector,
   guestDebugctrl,
   guestPat,
   guestEfer,
   guestPerfGlobalCtrl,
   guestPdpte0,
   guestPdpte1,
   guestPdpte2,
   guestPdpte3,
   guestEsLimit,
   guestCsLimit,
   guestSsLimit,
   guestDsLimit,
   guestFsLimit,
   guestGsLimit,
   guestLdtrLimit,
   guestTrLimit,
   guestGdtrLimit,
   guestIdtrLimit,
   guestEsAccessRights,
   guestCsAccessRights,
   guestSsAccessRights,
   guestDsAccessRights,
   guestFsAccessRights,
   guestGsAccessRights,
   guestLdtrAccessRights,
   guestTrAccessRights,
   guestInterruptability,
   guestActivity,
   guestSmbase,
   guestSysenterCs,
   guestPreemptionTimerValue,
   guestEsBase,
   guestCsBase,
   guestSsBase,
   guestDsBase,
   guestFsBase,
   guestGsBase,
   guestLdtrBase,
   guestTrBase,
   guestGdtrBase,
   guestIdtrBase,
   guestDr7,
   guestRflags,
   guestPendingDebugExceptions,
   guestSysenterEsp,
   guestSysenterEip,
   controlCr0Mask,
   controlCr4Mask,
   controlCr0ReadShadow,
   controlCr4ReadShadow,
   dataInstructionError,
   dataExitInterruptInfo,
   dataExitInterruptError,
   dataIdtVectorInfo,
   dataIdtVectorError,
   dataExitInstructionLength,
   dataExitInstructionInfo,
   dataGuestPhysical,
   dataIoRcx,
   dataIoRsi,
   dataIoRdi,
   dataIoRip,
   dataGuestLinearAddress,
   controlEntryInterruptionInfo,
   controlTscOffset,
   controlPinExecutionControls,
   controlPrimaryProcessorControls,
   controlSecondaryProcessorControls,
   controlExceptionBitmap,
   controlEntryControls,
   controlExitControls,
   guestCr0,
   guestCr3,
   guestCr4]

/-- The VMCS field type, bits 11:10 of the encoding (SDM Vol. 3D B.1):
0 control, 1 VM-exit information (read-only data), 2 guest state, 3 host
state. -/
def fieldType (f : Word) : Word := (f >>> 10) &&& 3

/-- The VMCS field width, bits 14:13 (SDM Vol. 3D B.1): 0 16-bit,
1 64-bit, 2 32-bit, 3 natural width. -/
def fieldWidth (f : Word) : Word := f >>> 13

/-- Writable on VMX: FL4's `WRITE_FIELDS` (73). -/
def writable (f : Word) : Bool := decide (f ∈ vmxWriteFields)

/-- Readable on VMX: FL4's `READ_FIELDS` (84). Two of them read as 0
when the processor's VMCS lacks them (`GUEST_PERF_GLOBAL_CTRL` without the
entry control "load IA32_PERF_GLOBAL_CTRL", `GUEST_PREEMPTION_TIMER_VALUE`
without the pin control "activate VMX-preemption timer"; FL4
`vm::vmcs_field_exists`, `vcpu::decode` ReadVMCS): `readSupported`. -/
def readable (f : Word) : Bool := decide (f ∈ vmxReadFields)

/-- FL4 `vcpu::decode` ReadVMCS's `supported` (the allowed-1 bit 13 of
`IA32_VMX_ENTRY_CTLS` 0x484, bit 6 of `IA32_VMX_PINBASED_CTLS` 0x481). -/
def readSupported (f : Word) : Bool :=
  if f = guestPerfGlobalCtrl then (vcpuCapability 0x484 >>> 32) &&& (1 <<< 13) ≠ 0
  else if f = guestPreemptionTimerValue then (vcpuCapability 0x481 >>> 32) &&& (1 <<< 6) ≠ 0
  else true

/-- The fields a guest step may change on VMX (the trusted layer's
`vm::run` stores them back): every readable guest-state or VM-exit
information field, and the two event-injection fields the exit rewrites
(the valid bit of `CONTROL_ENTRY_INTERRUPTION_INFO` cleared on a valid
exit (SDM Vol. 3C §27.8: a VM exit after a successful entry clears it);
reinjection of an event interrupted by a host exit writes both). -/
def guestChanged (f : Word) : Bool :=
  (readable f && (fieldType f = 1 || fieldType f = 2)) ||
  f = controlEntryInterruptionInfo || f = controlEntryExceptionErrorCode

end Vmx

namespace Svm

/-- VMCB control-area offsets FL4 names (`vcpu::svm`; APM Vol. 2 Table B-1). -/
def interceptCr : Word := 0x000
def interceptExc : Word := 0x008
def interceptMisc2 : Word := 0x010
def pauseFilter : Word := 0x038
def iopmBase : Word := 0x040
def msrpmBase : Word := 0x048
def tscOffset : Word := 0x050
def asid : Word := 0x058
def intCtl : Word := 0x060
def intState : Word := 0x068
def exitCode : Word := 0x070
def exitInfo1 : Word := 0x078
def exitInfo2 : Word := 0x080
def exitIntInfo : Word := 0x088
def nestedCtl : Word := 0x090
def avicVapicBar : Word := 0x098
def ghcb : Word := 0x0a0
def eventInj : Word := 0x0a8
def nestedCr3 : Word := 0x0b0
def virtExt : Word := 0x0b8
def clean : Word := 0x0c0
def nextRip : Word := 0x0c8
def insnBytes : Word := 0x0d0
def avicBacking : Word := 0x0e0
def avicLogical : Word := 0x0f0
def avicPhysical : Word := 0x0f8
def vmsa : Word := 0x108
/-- The state save area (APM Vol. 2 Table B-2) starts at 0x400. -/
def save : Word := 0x400
def cpl : Word := save + 0x0c8
def efer : Word := save + 0x0d0
def cr4 : Word := save + 0x148
def cr3 : Word := save + 0x150
def cr0 : Word := save + 0x158
def dr7 : Word := save + 0x160
def dr6 : Word := save + 0x168
def rflags : Word := save + 0x170
def rip : Word := save + 0x178
def rsp : Word := save + 0x1d8
def rax : Word := save + 0x1f8
def star : Word := save + 0x200
def lstar : Word := save + 0x208
def cstar : Word := save + 0x210
def sfmask : Word := save + 0x218
def kernelGsBase : Word := save + 0x220
def sysenterCs : Word := save + 0x228
def sysenterEsp : Word := save + 0x230
def sysenterEip : Word := save + 0x238
def cr2 : Word := save + 0x240
def gPat : Word := save + 0x268
/-- FL4 `svm::END`: the end of the words FL4 keeps. -/
def svmEnd : Word := save + 0x2e8

/-- FL4 `vcpu::vmcb_hidden`: physical pointers and AVIC/GHCB/VMSA
addresses, which read as 0. -/
def hidden (f : Word) : Bool :=
  decide (f ∈ [iopmBase, msrpmBase, avicVapicBar, ghcb, nestedCr3, avicBacking,
    avicLogical, avicPhysical, vmsa])

/-- Words the trusted layer rewrites with host cache state on every entry
(`vm::run`: the ASID word with its flush request, the clean bits). FL4
lets ReadVMCB return them (VIRT-PLAN.md FINDING V3); the spec leaves
their value unspecified (`Ext/VirtState`). -/
def hostCache (f : Word) : Bool := f = asid || f = clean

/-- What ReadVMCB returns 0 for: the hidden words and the host-cache
words (decision Q4 of 2026-11-21: FL4 should hide 0x058 and 0x0c0 as
well). -- FL4 code differs until V3 (`vcpu::vmcb_hidden` lacks 0x058,
0x0c0). -/
def hiddenRead (f : Word) : Bool := hidden f || hostCache f

/-- Readable on SVM: FL4 `vcpu::decode` ReadVMCB, `f & 7 == 0 && f < END`. -/
def readable (f : Word) : Bool := f &&& 7 = 0 && f < svmEnd

/-- One row of FL4's `vcpu::sanitize_vmcb` table: the bits the VMM
writes (`mask`), the bits forced to one (`forced`), and whether the value
must be a canonical address (`addr`). -/
structure WriteRule where
  mask : Word
  forced : Word
  addr : Bool

/-- Segment registers in the save area: ES CS SS DS FS GS GDTR LDTR IDTR TR,
each 16 bytes (selector, attributes, limit; then base). -/
def segAttrOffsets : List Word :=
  [0x400, 0x410, 0x420, 0x430, 0x440, 0x450, 0x460, 0x470, 0x480, 0x490]
/-- The segment bases (canonical-checked). -/
def segBaseOffsets : List Word :=
  [0x408, 0x418, 0x428, 0x438, 0x448, 0x458, 0x468, 0x478, 0x488, 0x498]

/-- FL4 `SVM_I1_FORCED` (intercept vector 3 at 0x00c: INTR, NMI, SMI,
INIT, selective CR0 write, RDPMC, INVD, INVLPGA, IOIO, MSR, shutdown;
APM Vol. 2 Table B-1). -/
def i1Forced : Word := 0x9c40_802f
/-- FL4 `SVM_I1_WRITABLE`: the rest of vector 3. -/
def i1Writable : Word := 0x63bf_7fd0
/-- FL4 `SVM_I2_FORCED` (vector 4 at 0x010: VMRUN, VMLOAD, VMSAVE, STGI,
CLGI, SKINIT, WBINVD, MONITOR, MWAIT, MWAIT-armed, XSETBV, RDPRU). -/
def i2Forced : Word := 0x7e7d
/-- FL4 `SVM_EVENT`: the defined bits of EVENTINJ (vector, type, EV, V,
error code; APM Vol. 2 §15.20). -/
def eventMask : Word := 0xffff_ffff_8000_0fff

end Svm

/-- FL4 `vcpu::EXCEPTIONS`: #DB, #AC, #MC are always intercepted (Xen
XSA-156 / CVE-2015-5307, CVE-2015-8104: a guest that loops on #AC or #DB
delivery hangs the host core; #MC belongs to the host). -/
def vcpuExceptions : Word := (1 <<< 1) ||| (1 <<< 17) ||| (1 <<< 18)

namespace Svm

/-- FL4's `sanitize_vmcb` table (50 writable words): `none` for a word
WriteVMCB rejects with `IllegalOperation`. -/
def writeRule (f : Word) : Option WriteRule :=
  if f = interceptCr then some ⟨0xffff_ffff, 0xffff_ffff_0010_0000, false⟩
  else if f = interceptExc then
    some ⟨0xffff_ffff ||| (i1Writable <<< 32), vcpuExceptions ||| (i1Forced <<< 32), false⟩
  else if f = interceptMisc2 then some ⟨0x182, i2Forced, false⟩
  else if f = pauseFilter then some ⟨0xffff_ffff_0000_0000, 0, false⟩
  else if f = tscOffset then some ⟨~~~0, 0, false⟩
  else if f = intCtl then some ⟨0xff_001f_01ff, 1 <<< 24, false⟩
  else if f = intState then some ⟨1, 0, false⟩
  else if f = eventInj then some ⟨eventMask, 0, false⟩
  else if f = nextRip then some ⟨~~~0, 0, false⟩
  else if f = cpl then some ⟨0xff00_0000, 0, false⟩
  else if f = efer then some ⟨~~~0, 1 <<< 12, false⟩
  else if f = cr4 then some ⟨(0x0fff : Word) ||| (1 <<< 16) ||| (1 <<< 17) ||| (1 <<< 18)
      ||| (1 <<< 20) ||| (1 <<< 21), 0, false⟩
  else if f ∈ segAttrOffsets ++ [cr3, cr0, dr7, dr6, rflags, rip, rsp, rax, star, sfmask,
      sysenterCs, cr2, gPat] then some ⟨~~~0, 0, false⟩
  else if f ∈ segBaseOffsets ++ [lstar, cstar, kernelGsBase, sysenterEsp, sysenterEip] then
    some ⟨~~~0, 0, true⟩
  else none

/-- Writable on SVM. -/
def writable (f : Word) : Bool := (writeRule f).isSome

/-- The VMCB words a guest step may change (APM Vol. 2 §15.6, "#VMEXIT":
the processor writes the state save area, `EXITCODE`, `EXITINFO1/2`,
`EXITINTINFO`, the interrupt shadow, V_TPR/V_IRQ in `VINTR`,
`NRIP` and the fetched instruction bytes; FL4's `vm::run` also clears or
reinjects `EVENTINJ` and clears `NRIP`). -/
def guestChanged (f : Word) : Bool :=
  readable f && !hidden f && !hostCache f &&
  (save ≤ f || decide (f ∈ [intCtl, intState, exitCode, exitInfo1, exitInfo2, exitIntInfo,
    eventInj, nextRip, insnBytes, insnBytes + 8]))

end Svm

/-- The l4h VCPU MSRs and FL4's pseudo-MSRs (libsel4 `vmenter.h`). -/
def msrStar : Word := 0xc000_0081
def msrLstar : Word := 0xc000_0082
def msrCstar : Word := 0xc000_0083
def msrFmask : Word := 0xc000_0084
def msrKernelGsBase : Word := 0xc000_0102
def msrCr2 : Word := 0xffff_ffff
def msrXcr0 : Word := 0xffff_fffe
/-- `IA32_VMX_MISC`: ReadMSR answers `vcpu_capability(0x485)` on VMX and 0
on SVM; it is not VCPU state. -/
def msrVmxMisc : Word := 0x485

/-- The MSR fields of a VCPU (FL4 `vcpu::msr_addr`; both backends). -/
def vcpuMsrs : List Word := [msrStar, msrLstar, msrCstar, msrFmask, msrKernelGsBase, msrCr2, msrXcr0]

/-- The single place of a field's value (module docstring): on SVM the
MSRs but XCR0 are VMCB words and the VMCB's RAX is GPR 0. -/
def VField.canon (k : VirtKind) : VField → VField
  | .msr m =>
    if k = .svm then
      if m = msrStar then .vmcb Svm.star
      else if m = msrLstar then .vmcb Svm.lstar
      else if m = msrCstar then .vmcb Svm.cstar
      else if m = msrFmask then .vmcb Svm.sfmask
      else if m = msrKernelGsBase then .vmcb Svm.kernelGsBase
      else if m = msrCr2 then .vmcb Svm.cr2
      else .msr m
    else .msr m
  | .vmcb off => if k = .svm ∧ off = Svm.rax then .gpr 0 else .vmcb off
  | f => f

/-- The fields that exist on backend `k` (the domain of its table). -/
def VField.valid (k : VirtKind) : VField → Bool
  | .vmcs f => k = .vmx && (Vmx.writable f || Vmx.readable f)
  | .vmcb f => k = .svm && Svm.readable f
  | .gpr _ => k = .vmx || k = .svm
  | .msr m => (k = .vmx || k = .svm) && decide (m ∈ vcpuMsrs)

/-- Readable through the invocations (ReadVMCS / ReadVMCB / ReadMSR). A
hidden VMCB word is readable and reads 0. -/
def VField.readable (k : VirtKind) : VField → Bool
  | .vmcs f => k = .vmx && Vmx.readable f
  | .vmcb f => k = .svm && Svm.readable f
  | .gpr _ => false
  | .msr m => (k = .vmx || k = .svm) && decide (m ∈ vcpuMsrs)

/-- Writable through the invocations (WriteVMCS / WriteVMCB / WriteMSR /
WriteRegisters for the GPRs). -/
def VField.writable (k : VirtKind) : VField → Bool
  | .vmcs f => k = .vmx && Vmx.writable f
  | .vmcb f => k = .svm && Svm.writable f
  | .gpr _ => k = .vmx || k = .svm
  | .msr m => (k = .vmx || k = .svm) && decide (m ∈ vcpuMsrs)

/-- Changed by a guest step. XCR0 is not: XSETBV always exits on VMX
(SDM Vol. 3C §26.1.2) and FL4 forces its intercept on SVM (`SVM_I2_FORCED`
bit 13). On VMX the syscall MSRs come back through the VM-exit MSR-store
list and CR2 from the processor (`vm::run`). -/
def VField.guestChanged (k : VirtKind) : VField → Bool
  | .vmcs f => k = .vmx && Vmx.guestChanged f
  | .vmcb f => k = .svm && Svm.guestChanged f
  | .gpr _ => k = .vmx || k = .svm
  | .msr m => k = .vmx && decide (m ∈ vcpuMsrs) && m ≠ msrXcr0

end

end Fl4Spec
