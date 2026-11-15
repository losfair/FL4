/-
x86-64 data types of the seL4 abstract specification (MCS).

Ports, in theory order:
- `spec/abstract/X64/ArchVMAttributes_A`;
- `spec/design/skel/Structs_B` (Haskell `SEL4/Object/Structures.lhs`, only
  `TcbFlag`, `tcbFlagToWord`, `tcbFlagMask`);
- `spec/design/skel/X64/Arch_Structs_B` (Haskell
  `SEL4/Model/StateData/X64.lhs` `X64VSpaceRegionUse` and
  `SEL4/Object/Structures/X64.lhs` `parseTimeArg`);
- `spec/abstract/X64/Arch_Structs_A`.

Omitted (no IOMMU): l4v already comments out the IOSpace and IO page table
caps, the IO table objects and the VT-d `arch_state` fields; the remaining
VT-d declarations of Arch_Structs_A (`translation_type`, `iocte`, `iopte`,
`iorte`, `iotable_size`, `iopt_bits`, `vtd_cte_size_bits`, `vtd_pt_bits`,
`x64_num_io_pt_levels`) are not ported either.

l4v's `rt` branch has not been ported to X64. The MCS definitions that every
other `rt` architecture provides in Arch_Structs_A (`arch_cap_badge`,
`reply_bits`, `parse_time_arg`, `words_from_time`) are added here from
RISCV64 `Arch_Structs_A`, and `ntfn_bits` is the MCS value (each marked
"rt X64 gap").
-/
import Fl4Spec.Types

namespace Fl4Spec

open Classical

noncomputable section

/-! ## ArchVMAttributes_A -/

/-- l4v: ArchVMAttributes_A.X64_A.table_attr. -/
inductive TableAttr where
  | accessed
  | cacheDisabled
  | writeThrough
  | executeDisable
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchVMAttributes_A.X64_A.table_attrs. -/
abbrev TableAttrs := Set TableAttr

/-- l4v: ArchVMAttributes_A.X64_A.vm_attribute: the attributes of a page
mapping, including kernel-only ones. -/
inductive VMAttribute where
  | ptAttr (a : TableAttr)
  | global
  | pat
  | dirty
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchVMAttributes_A.X64_A.vm_attributes. -/
abbrev VMAttributes := Set VMAttribute

/-- l4v: ArchVMAttributes_A.X64_A.arch_raw_vmattrs. -/
abbrev ArchRawVmattrs := Word32

/-- l4v: ArchVMAttributes_A.X64_A.attribs_from_word. -/
def attribsFromWord (w : Word) : VMAttributes :=
  let V : VMAttributes := if testBit w 0 then {.ptAttr .writeThrough} else ∅
  let V' := if testBit w 1 then insert (.ptAttr .cacheDisabled) V else V
  if testBit w 2 then insert .pat V' else V'

/-- l4v: ArchVMAttributes_A.X64_A.attribs_to_word. -/
def attribsToWord (attribs : VMAttributes) : Word :=
  let V : Word := if VMAttribute.ptAttr .writeThrough ∈ attribs then 1 else 0
  let V' := if VMAttribute.ptAttr .cacheDisabled ∈ attribs then V + 2 else V
  if VMAttribute.pat ∈ attribs then V' + 4 else V'

/-! ## Structs_B -/

/-- l4v: Structs_B.tcb_flag (Haskell `TcbFlag`). -/
inductive TcbFlag where
  | fpuDisabled
deriving DecidableEq, Repr, Inhabited

/-- l4v: Structs_B.tcbFlagToWord. -/
def tcbFlagToWord : TcbFlag → Word
  | .fpuDisabled => 1 <<< 0

/-- l4v: Structs_B.tcbFlagMask. -/
def tcbFlagMask : Word := if config_HAVE_FPU then tcbFlagToWord .fpuDisabled else 0

-- l4v Structs_B.ticks_len / ticks: see `Ticks` (Machine, from Time).

/-- l4v: Structs_B.timeArgLen. -/
def timeArgLen : Nat := 64 / 64

/-! ## Arch_Structs_B -/

/-- l4v: Arch_Structs_B.X64_H.x64vspace_region_use (Haskell
`X64VSpaceRegionUse`). -/
inductive X64VSpaceRegionUse where
  | x64VSpaceUserRegion
  | x64VSpaceInvalidRegion
  | x64VSpaceKernelWindow
  | x64VSpaceDeviceWindow
deriving DecidableEq, Repr, Inhabited

/-- l4v: Arch_Structs_B.X64_H.parseTimeArg. -/
def parseTimeArg (i : Nat) (args : List Word) : Ticks := the args[i]?

/-- l4v: Arch_Structs_B.X64_H.timerPrecision (rt X64 gap; RISCV64
`Arch_Structs_B` includes Haskell `timerPrecision = usToTicks 1`, with
`usToTicks` the abbreviation for `us_to_ticks`). The C kernel's x86
`getTimerPrecision` is also `usToTicks(1)`. -/
def timerPrecision : Word64 := usToTicks 1

/-! ## Arch_Structs_A -/

/-- l4v: Arch_Structs_A.X64_A.io_port. -/
abbrev IoPort := BitVec 16
/-- l4v: Arch_Structs_A.X64_A.io_asid. -/
abbrev IoAsid := BitVec 16

/-- l4v: Arch_Structs_A.X64_A.arch_cap. The IOSpace and IO page table caps
are commented out in l4v (`FIXME x64-vtd`) and not ported (no IOMMU). -/
inductive ArchCap where
  | vcpuCap (ref : ObjRef)
  | eptCap (ref : ObjRef) (level : Nat) (mapped : Option (Asid × VSpaceRef))
  | asidPoolCap (acapAsidPool : ObjRef) (acapAsidBase : Asid)
  | asidControlCap
  | ioPortCap (acapIoPortFirstPort : IoPort) (acapIoPortLastPort : IoPort)
  | ioPortControlCap
  | pageCap (isDevice : Bool) (ref : ObjRef) (acapRights : CapRights) (mapType : VMMapType)
      (size : VMPageSize) (mapped : Option (Asid × VSpaceRef))
  | pageTableCap (ref : ObjRef) (mapped : Option (Asid × VSpaceRef))
  | pageDirectoryCap (ref : ObjRef) (mapped : Option (Asid × VSpaceRef))
  | pdPointerTableCap (ref : ObjRef) (mapped : Option (Asid × VSpaceRef))
  | pml4Cap (ref : ObjRef) (mapped : Option Asid)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.acap_asid_pool (selector). -/
def ArchCap.acapAsidPool : ArchCap → ObjRef
  | .asidPoolCap p _ => p
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.acap_asid_base (selector). -/
def ArchCap.acapAsidBase : ArchCap → Asid
  | .asidPoolCap _ b => b
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.acap_io_port_first_port (selector). -/
def ArchCap.acapIoPortFirstPort : ArchCap → IoPort
  | .ioPortCap f _ => f
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.acap_io_port_last_port (selector). -/
def ArchCap.acapIoPortLastPort : ArchCap → IoPort
  | .ioPortCap _ l => l
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.acap_rights (selector). -/
def ArchCap.acapRights : ArchCap → CapRights
  | .pageCap _ _ r _ _ _ => r
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.cr3 (`cr3 obj_ref asid`). -/
inductive Cr3 where
  | cr3 (addr : ObjRef) (pcid : Asid)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Arch_Structs_A.X64_A.cr3_base_address. -/
def cr3BaseAddress : Cr3 → ObjRef
  | .cr3 addr _ => addr

/-- l4v: Arch_Structs_A.X64_A.cr3_pcid. -/
def cr3Pcid : Cr3 → Asid
  | .cr3 _ pcid => pcid

/-- l4v: Arch_Structs_A.X64_A.pml4e. -/
inductive PML4E where
  | invalidPML4E
  | pdPointerTablePML4E (pml4Table : ObjRef) (pml4eAttrs : TableAttrs) (pml4eRights : VMRights)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.pml4_table (selector). -/
def PML4E.pml4Table : PML4E → ObjRef
  | .pdPointerTablePML4E t _ _ => t
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pml4e_attrs (selector). -/
def PML4E.pml4eAttrs : PML4E → TableAttrs
  | .pdPointerTablePML4E _ a _ => a
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pml4e_rights (selector). -/
def PML4E.pml4eRights : PML4E → VMRights
  | .pdPointerTablePML4E _ _ r => r
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.pdpte. -/
inductive PDPTE where
  | invalidPDPTE
  | pageDirectoryPDPTE (pdptTable : ObjRef) (pdptTableAttrs : TableAttrs) (pdptRights : VMRights)
  | hugePagePDPTE (pdptFrame : ObjRef) (pdptAttrs : VMAttributes) (pdptRights : VMRights)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.pdpt_table (selector). -/
def PDPTE.pdptTable : PDPTE → ObjRef
  | .pageDirectoryPDPTE t _ _ => t
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pdpt_table_attrs (selector). -/
def PDPTE.pdptTableAttrs : PDPTE → TableAttrs
  | .pageDirectoryPDPTE _ a _ => a
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pdpt_rights (selector of two constructors). -/
def PDPTE.pdptRights : PDPTE → VMRights
  | .pageDirectoryPDPTE _ _ r => r
  | .hugePagePDPTE _ _ r => r
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pdpt_frame (selector). -/
def PDPTE.pdptFrame : PDPTE → ObjRef
  | .hugePagePDPTE f _ _ => f
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pdpt_attrs (selector). -/
def PDPTE.pdptAttrs : PDPTE → VMAttributes
  | .hugePagePDPTE _ a _ => a
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.pde. -/
inductive PDE where
  | invalidPDE
  | pageTablePDE (table : ObjRef) (ptAttrs : TableAttrs) (pdeRights : CapRights)
  | largePagePDE (frame : ObjRef) (pdeAttrs : VMAttributes) (pdeRights : CapRights)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.pt_attrs (selector). -/
def PDE.ptAttrs : PDE → TableAttrs
  | .pageTablePDE _ a _ => a
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pde_rights (selector of two constructors). -/
def PDE.pdeRights : PDE → CapRights
  | .pageTablePDE _ _ r => r
  | .largePagePDE _ _ r => r
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pde_attrs (selector). -/
def PDE.pdeAttrs : PDE → VMAttributes
  | .largePagePDE _ a _ => a
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.pte. -/
inductive PTE where
  | invalidPTE
  | smallPagePTE (pteFrame : ObjRef) (pteAttrs : VMAttributes) (pteRights : CapRights)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.pte_frame (selector). -/
def PTE.pteFrame : PTE → ObjRef
  | .smallPagePTE f _ _ => f
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pte_attrs (selector). -/
def PTE.pteAttrs : PTE → VMAttributes
  | .smallPagePTE _ a _ => a
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.pte_rights (selector). -/
def PTE.pteRights : PTE → CapRights
  | .smallPagePTE _ _ r => r
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.vm_page_entry. -/
inductive VMPageEntry where
  | vmPTE (e : PTE)
  | vmPDE (e : PDE)
  | vmPDPTE (e : PDPTE)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.arch_kernel_obj. The IO root, context and page
tables are commented out in l4v (`FIXME x64-vtd`) and not ported. -/
inductive ArchKernelObj where
  | vcpu (words : Word → Word)
  | ept (level : Nat) (entries : BitVec 9 → Word)
  | asidPool (pool : BitVec 9 → Option ObjRef)
  | pageTable (pt : BitVec 9 → PTE)
  | pageDirectory (pd : BitVec 9 → PDE)
  | pdPointerTable (pdpt : BitVec 9 → PDPTE)
  | pageMapL4 (pm : BitVec 9 → PML4E)
  | dataPage (isDevice : Bool) (size : VMPageSize)
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.table_size. -/
def tableSize : Nat := ptTranslationBits + wordSizeBits

/-- l4v: Arch_Structs_A.X64_A.cte_level_bits. -/
def cteLevelBits : Nat := 5

/-- l4v: Arch_Structs_A.X64_A.arch_obj_size. -/
def archObjSize : ArchCap → Nat
  | .vcpuCap _ => 15
  | .eptCap _ _ _ => tableSize
  | .asidPoolCap _ _ => pageBits
  | .asidControlCap => 0
  | .ioPortCap _ _ => 0
  | .ioPortControlCap => 0
  | .pageCap _ _ _ _ sz _ => pageBitsForSize sz
  | .pageTableCap _ _ => tableSize
  | .pageDirectoryCap _ _ => tableSize
  | .pdPointerTableCap _ _ => tableSize
  | .pml4Cap _ _ => tableSize

/-- l4v: Arch_Structs_A.X64_A.arch_cap_is_device. -/
def archCapIsDevice : ArchCap → Bool
  | .vcpuCap _ | .eptCap _ _ _ => false
  | .asidPoolCap _ _ => false
  | .asidControlCap => false
  | .ioPortCap _ _ => false
  | .ioPortControlCap => false
  | .pageCap isDev _ _ _ _ _ => isDev
  | .pageTableCap _ _ => false
  | .pageDirectoryCap _ _ => false
  | .pdPointerTableCap _ _ => false
  | .pml4Cap _ _ => false

/-- l4v: Arch_Structs_A.X64_A.arch_cap_badge (rt X64 gap; RISCV64
`arch_cap_badge`): no badges on arch caps. -/
def archCapBadge (_acap : ArchCap) : Option Word := none

/-- l4v: Arch_Structs_A.X64_A.tcb_bits. -/
def tcbBits : Nat := 11
/-- l4v: Arch_Structs_A.X64_A.endpoint_bits. -/
def endpointBits : Nat := 4
/-- l4v: Arch_Structs_A.X64_A.ntfn_bits. rt X64 gap: the X64 theory still
has the non-MCS value 5; this is the MCS value 6 (C `seL4_NotificationBits`
with `CONFIG_KERNEL_MCS`, RISCV64 `rt` `ntfn_bits`). -/
def ntfnBits : Nat := 6
/-- l4v: Arch_Structs_A.X64_A.reply_bits (rt X64 gap; RISCV64 `reply_bits`,
C `seL4_ReplyBits`). -/
def replyBits : Nat := 5
/-- l4v: Arch_Structs_A.X64_A.untyped_min_bits. -/
def untypedMinBits : Nat := 4
/-- l4v: Arch_Structs_A.X64_A.untyped_max_bits. -/
def untypedMaxBits : Nat := 47

/-- l4v: Arch_Structs_A.X64_A.arch_kobj_size. -/
def archKobjSize : ArchKernelObj → Nat
  | .vcpu _ => 15
  | .ept _ _ => tableSize
  | .asidPool _ => pageBits
  | .pageTable _ => tableSize
  | .pageDirectory _ => tableSize
  | .pdPointerTable _ => tableSize
  | .pageMapL4 _ => tableSize
  | .dataPage _ sz => pageBitsForSize sz

/-- l4v: Arch_Structs_A.X64_A.aobj_ref. -/
def aobjRef : ArchCap → Option ObjRef
  | .vcpuCap p | .eptCap p _ _ => some p
  | .asidPoolCap x _ => some x
  | .asidControlCap => none
  | .ioPortCap _ _ => none
  | .ioPortControlCap => none
  | .pageCap _ x _ _ _ _ => some x
  | .pageDirectoryCap x _ => some x
  | .pageTableCap x _ => some x
  | .pdPointerTableCap x _ => some x
  | .pml4Cap x _ => some x

/-- l4v: Arch_Structs_A.X64_A.acap_rights_update. -/
def acapRightsUpdate (rs : CapRights) (ac : ArchCap) : ArchCap :=
  match ac with
  | .pageCap dev x _ m sz as => .pageCap dev x (validateVmRights rs) m sz as
  | _ => ac

/-- l4v: Arch_Structs_A.X64_A.aobject_type. -/
inductive AObjectType where
  | smallPageObj
  | largePageObj
  | hugePageObj
  | pageTableObj
  | pageDirectoryObj
  | pdptObj
  | pml4Obj
  | asidPoolObj
  | vcpuObj
  | eptPml4Obj
  | eptPdptObj
  | eptPdObj
  | eptPtObj
deriving DecidableEq, Repr, Inhabited

/-- l4v: Arch_Structs_A.X64_A.X64IRQState. -/
inductive X64IRQState where
  | irqFree
  | irqReserved
  | irqMSI (msiBus msiDev msiFunc msiHandle : Word)
  | irqIOAPIC (irqIoapic irqPin irqLevel irqPolarity : Word) (irqMasked : Bool)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Arch_Structs_A.X64_A.MSIBus (selector). -/
def X64IRQState.msiBus : X64IRQState → Word
  | .irqMSI b _ _ _ => b
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.MSIDev (selector). -/
def X64IRQState.msiDev : X64IRQState → Word
  | .irqMSI _ d _ _ => d
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.MSIFunc (selector). -/
def X64IRQState.msiFunc : X64IRQState → Word
  | .irqMSI _ _ f _ => f
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.MSIHandle (selector). -/
def X64IRQState.msiHandle : X64IRQState → Word
  | .irqMSI _ _ _ h => h
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.IRQioapic (selector). -/
def X64IRQState.irqIoapic : X64IRQState → Word
  | .irqIOAPIC i _ _ _ _ => i
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.IRQPin (selector). -/
def X64IRQState.irqPin : X64IRQState → Word
  | .irqIOAPIC _ p _ _ _ => p
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.IRQLevel (selector). -/
def X64IRQState.irqLevel : X64IRQState → Word
  | .irqIOAPIC _ _ l _ _ => l
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.IRQPolarity (selector). -/
def X64IRQState.irqPolarity : X64IRQState → Word
  | .irqIOAPIC _ _ _ p _ => p
  | _ => undefined
/-- l4v: Arch_Structs_A.X64_A.IRQMasked (selector). -/
def X64IRQState.irqMasked : X64IRQState → Bool
  | .irqIOAPIC _ _ _ _ m => m
  | _ => undefined

/-- l4v: Arch_Structs_A.X64_A.arch_is_frame_type. -/
def archIsFrameType (aobj : AObjectType) : Bool :=
  match aobj with
  | .smallPageObj => true
  | .largePageObj => true
  | .hugePageObj => true
  | _ => false

/-- l4v: Arch_Structs_A.X64_A.arch_default_cap. -/
def archDefaultCap (tp : AObjectType) (r : ObjRef) (_n : Nat) (dev : Bool) : ArchCap :=
  match tp with
  | .smallPageObj => .pageCap dev r vmReadWrite .vmNoMap .x64SmallPage none
  | .largePageObj => .pageCap dev r vmReadWrite .vmNoMap .x64LargePage none
  | .hugePageObj => .pageCap dev r vmReadWrite .vmNoMap .x64HugePage none
  | .pageTableObj => .pageTableCap r none
  | .pageDirectoryObj => .pageDirectoryCap r none
  | .pdptObj => .pdPointerTableCap r none
  | .pml4Obj => .pml4Cap r none
  | .asidPoolObj => .asidPoolCap r 0 -- unused
  | .vcpuObj => .vcpuCap r
  | .eptPml4Obj => .eptCap r 0 none
  | .eptPdptObj => .eptCap r 39 none
  | .eptPdObj => .eptCap r 30 none
  | .eptPtObj => .eptCap r 21 none

/-- l4v: Arch_Structs_A.X64_A.default_arch_object. -/
def defaultArchObject (tp : AObjectType) (dev : Bool) (_n : Nat) : ArchKernelObj :=
  match tp with
  | .smallPageObj => .dataPage dev .x64SmallPage
  | .largePageObj => .dataPage dev .x64LargePage
  | .hugePageObj => .dataPage dev .x64HugePage
  | .pageTableObj => .pageTable fun _ => .invalidPTE
  | .pageDirectoryObj => .pageDirectory fun _ => .invalidPDE
  | .pdptObj => .pdPointerTable fun _ => .invalidPDPTE
  | .pml4Obj => .pageMapL4 fun _ => .invalidPML4E
  | .asidPoolObj => .asidPool fun _ => none
  | .vcpuObj => .vcpu fun _ => 0
  | .eptPml4Obj => .ept 0 fun _ => 0
  | .eptPdptObj => .ept 39 fun _ => 0
  | .eptPdObj => .ept 30 fun _ => 0
  | .eptPtObj => .ept 21 fun _ => 0

/-- l4v: Arch_Structs_A.X64_A.x64_vspace_region_uses. -/
abbrev X64VSpaceRegionUses := VSpaceRef → X64VSpaceRegionUse

/-- l4v: Arch_Structs_A.X64_A.arch_state. The VT-d fields are commented out
in l4v (`FIXME x64-vtd`) and not ported. -/
structure ArchState where
  x64AsidTable : AsidHighIndex → Option ObjRef
  x64GlobalPml4 : ObjRef
  x64KernelVspace : X64VSpaceRegionUses
  x64GlobalPts : List ObjRef
  x64GlobalPdpts : List ObjRef
  x64GlobalPds : List ObjRef
  x64CurrentCr3 : Cr3
  x64AllocatedIoPorts : IoPort → Bool
  x64NumIoapics : Word64
  x64IoapicNirqs : Word → BitVec 8
  x64IrqState : BitVec 8 → X64IRQState
  x64CurrentFpuOwner : Option ObjRef
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.pd_shift_bits. -/
def pdShiftBits : Nat := pageBits + ptTranslationBits
/-- l4v: Arch_Structs_A.X64_A.pt_shift_bits. -/
def ptShiftBits : Nat := pageBits
/-- l4v: Arch_Structs_A.X64_A.pdpt_shift_bits. -/
def pdptShiftBits : Nat := pageBits + ptTranslationBits + ptTranslationBits
/-- l4v: Arch_Structs_A.X64_A.pml4_shift_bits. -/
def pml4ShiftBits : Nat := pageBits + ptTranslationBits + ptTranslationBits + ptTranslationBits

/-- l4v: Arch_Structs_A.X64_A.pt_bits. -/
def ptBits : Nat := tableSize
/-- l4v: Arch_Structs_A.X64_A.pd_bits. -/
def pdBits : Nat := tableSize
/-- l4v: Arch_Structs_A.X64_A.pdpt_bits. -/
def pdptBits : Nat := tableSize
/-- l4v: Arch_Structs_A.X64_A.pml4_bits. -/
def pml4Bits : Nat := tableSize

/-- l4v: Arch_Structs_A.X64_A.aa_type (the datatype). -/
inductive AAType where
  | aASIDPool
  | aVcpu
  | aEpt (level : Nat)
  | aPageTable
  | aPageDirectory
  | aPDPointerTable
  | aPageMapL4
  | aUserData (sz : VMPageSize)
  | aDeviceData (sz : VMPageSize)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Arch_Structs_A.X64_A.aa_type (the function). -/
def aaType (ao : ArchKernelObj) : AAType :=
  match ao with
  | .vcpu _ => .aVcpu
  | .ept level _ => .aEpt level
  | .pageTable _ => .aPageTable
  | .pageDirectory _ => .aPageDirectory
  | .dataPage dev sz => if dev then .aDeviceData sz else .aUserData sz
  | .asidPool _ => .aASIDPool
  | .pdPointerTable _ => .aPDPointerTable
  | .pageMapL4 _ => .aPageMapL4

/-- l4v: Arch_Structs_A.X64_A.badge_bits. -/
def badgeBits : Nat := 64

/-- l4v: Arch_Structs_A.X64_A.arch_tcb. `tcb_cur_fpu` is a ghost flag
recording whether the TCB is the current FPU owner. -/
structure ArchTcb where
  tcbContext : UserContext
  tcbCurFpu : Bool
deriving Inhabited

/-- l4v: Arch_Structs_A.X64_A.default_arch_tcb. -/
def defaultArchTcb : ArchTcb := { tcbContext := newContext, tcbCurFpu := false }

/-- l4v: Arch_Structs_A.X64_A.arch_tcb_context_set. -/
def archTcbContextSet (uc : UserContext) (aTcb : ArchTcb) : ArchTcb :=
  { aTcb with tcbContext := uc }

/-- l4v: Arch_Structs_A.X64_A.arch_tcb_context_get. -/
def archTcbContextGet (aTcb : ArchTcb) : UserContext := aTcb.tcbContext

/-- l4v: Arch_Structs_A.X64_A.arch_tcb_set_registers. -/
def archTcbSetRegisters (regs : Register → Word) (aTcb : ArchTcb) : ArchTcb :=
  { aTcb with tcbContext := ⟨aTcb.tcbContext.userFpuState, regs⟩ }

/-- l4v: Arch_Structs_A.X64_A.arch_tcb_get_registers. -/
def archTcbGetRegisters (aTcb : ArchTcb) : Register → Word := aTcb.tcbContext.userRegs

/-- l4v: Arch_Structs_A.X64_A.parse_time_arg (rt X64 gap; RISCV64
`parse_time_arg`). -/
def parseTimeArgA (i : Nat) (args : List Word) : Time := ucast 64 (the args[i]?)

/-- l4v: Arch_Structs_A.X64_A.words_from_time (rt X64 gap; RISCV64
`words_from_time`). -/
def wordsFromTime (t : Time) : List Word := [ucast 64 t]

end

end Fl4Spec
