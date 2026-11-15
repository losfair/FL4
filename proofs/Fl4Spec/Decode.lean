/-
Decoding system calls: checking the user's arguments and turning them into
invocations (MCS, x86-64).

Ports, in theory order:
- `spec/abstract/X64/ArchDecode_A` (imports Interrupt_A);
- `spec/abstract/Decode_A`.

Omitted (no IOMMU): the VT-d decoders of X64 ArchDecode_A
(`pci_request_id_from_cap`, `decode_io_pt_invocation`,
`decode_io_frame_map_invocation`, `decode_io_map_invocation`) are commented
out in l4v (`FIXME x64-vtd`) and not ported; `decode_io_unmap_invocation`
(an l4v `X64STUB`, defined as `undefined`) and the helpers only those
decoders use (`page_cap_set_vmmap_type`, `get_iovm_rights`) are ported.
-/
import Fl4Spec.Interrupt

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Enumerations of invocation labels

Isabelle's `[a .e. b]` (Enumeration `upto_enum`, `map toEnum [fromEnum a
..< Suc (fromEnum b)]`) on `gen_invocation_labels`, with `fromEnum` and
`toEnum` of the derived `Enum` instance (the order of
`GenInvocationLabels.enum`). -/

/-- l4v: Enumeration.fromEnum on `gen_invocation_labels`. -/
def GenInvocationLabels.fromEnum (l : GenInvocationLabels) : Nat := GenInvocationLabels.enum.idxOf l

/-- l4v: Enumeration.toEnum on `gen_invocation_labels`. -/
def GenInvocationLabels.toEnum (n : Nat) : GenInvocationLabels := the (GenInvocationLabels.enum[n]?)

/-- l4v: Enumeration.upto_enum (`[a .e. b]`) on `gen_invocation_labels`. -/
def GenInvocationLabels.uptoEnum (a b : GenInvocationLabels) : List GenInvocationLabels :=
  (List.range' a.fromEnum (b.fromEnum + 1 - a.fromEnum)).map GenInvocationLabels.toEnum

/-! ## ArchDecode_A: helper definitions -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.check_vp_alignment. -/
def checkVpAlignment (sz : VMPageSize) (vptr : Word) : SEMonad Z Unit :=
  NonDetE.unlessE (isAligned vptr (pageBitsForSize sz)) <|
    NonDetE.throwError .alignmentError

end

/-! ## ArchDecode_A: architecture calls -/

/-- l4v: ArchDecode_A.X64_A.page_base. -/
def pageBase (vaddr : VSpaceRef) (vmsize : VMPageSize) : VSpaceRef :=
  vaddr &&& ~~~(mask (pageBitsForSize vmsize))

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.arch_decode_irq_control_invocation: issue an IRQ
handler for an IOAPIC pin or an MSI. -/
def archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr)
    (cps : List Cap) : SEMonad Z ArchIrqControlInvocation :=
  if invocationType label = .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC
  then (if args.length ≥ 7 ∧ cps.length ≥ 1
    then
      let preIrq := the args[6]?
      let index := the args[0]?
      let depth := the args[1]?
      let cnode := the cps[0]?
      let irqv : Irq := ucast 8 preIrq + minUserIRQ
      let ioapic := the args[2]?
      let pin := the args[3]?
      let level := the args[4]?
      let polarity := the args[5]?
      let vector : Word := ucast 64 irqv + irqIntOffset
      do
        NonDetE.whenE (preIrq > ucast 64 (maxUserIRQ - minUserIRQ)) <|
          NonDetE.throwError (.rangeError 0 (ucast 64 (maxUserIRQ - minUserIRQ)))
        let irqActive ← NonDetE.liftE <| isIrqActive irqv
        NonDetE.whenE irqActive <| NonDetE.throwError .revokeFirst
        let destSlot ← lookupTargetSlot cnode (dataToCptr index) (unat depth)
        ensureEmpty destSlot
        let numIOAPICs ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64NumIoapics
        let ioapicNirqs ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64IoapicNirqs
        NonDetE.whenE (numIOAPICs = 0) <| NonDetE.throwError .illegalOperation
        NonDetE.whenE (ioapic > numIOAPICs - 1) <| NonDetE.throwError (.rangeError 0 (numIOAPICs - 1))
        NonDetE.whenE (pin > ucast 64 (ioapicNirqs ioapic - 1)) <|
          NonDetE.throwError (.rangeError 0 (ucast 64 (ioapicNirqs ioapic - 1)))
        NonDetE.whenE (level > 1) <| NonDetE.throwError (.rangeError 0 1)
        NonDetE.whenE (polarity > 1) <| NonDetE.throwError (.rangeError 0 1)
        NonDetE.returnOk <| .issueIRQHandlerIOAPIC irqv destSlot srcSlot
          ioapic pin level polarity vector
    else NonDetE.throwError .truncatedMessage)
  else (if invocationType label = .archInvocationLabel .x64IRQIssueIRQHandlerMSI
    then (if args.length ≥ 7 ∧ cps.length ≥ 1
      then
        let preIrq := the args[6]?
        let index := the args[0]?
        let depth := the args[1]?
        let cnode := the cps[0]?
        let irqv : Irq := ucast 8 preIrq + minUserIRQ
        let bus := the args[2]?
        let dev := the args[3]?
        let func := the args[4]?
        let handle := the args[5]?
        do
          NonDetE.whenE (preIrq > ucast 64 (maxUserIRQ - minUserIRQ)) <|
            NonDetE.throwError (.rangeError 0 (ucast 64 (maxUserIRQ - minUserIRQ)))
          let irqActive ← NonDetE.liftE <| isIrqActive irqv
          NonDetE.whenE irqActive <| NonDetE.throwError .revokeFirst
          let destSlot ← lookupTargetSlot cnode (dataToCptr index) (unat depth)
          ensureEmpty destSlot
          -- l4v: Following should be wrapped in to a function like what c did
          -- since it is pc99 related, problem is where to put this function
          NonDetE.whenE (bus > maxPCIBus) <| NonDetE.throwError (.rangeError 0 maxPCIBus)
          NonDetE.whenE (dev > maxPCIDev) <| NonDetE.throwError (.rangeError 0 maxPCIDev)
          NonDetE.whenE (func > maxPCIFunc) <| NonDetE.throwError (.rangeError 0 maxPCIFunc)
          NonDetE.returnOk <| .issueIRQHandlerMSI irqv destSlot srcSlot bus dev func handle
      else NonDetE.throwError .truncatedMessage)
    else NonDetE.throwError .illegalOperation)

/-- l4v: ArchDecode_A.X64_A.args_at_least (`abbreviation (input)`). -/
abbrev argsAtLeast (n : Nat) (args : List Data) : SEMonad Z Unit :=
  NonDetE.whenE (n > args.length) <| NonDetE.throwError .truncatedMessage

/-- l4v: ArchDecode_A.X64_A.ensure_port_operation_allowed: the ports
`startPort ..< startPort + sz` are in the range of the IO port cap. -/
def ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : SEMonad Z Unit :=
  match cap with
  | .ioPortCap firstAllowed lastAllowed => do
    let endPort ← NonDetE.returnOk (startPort + BitVec.ofNat 32 sz - 1)
    NonDetE.assertE (firstAllowed ≤ lastAllowed)
    NonDetE.assertE (startPort ≤ endPort)
    NonDetE.whenE (startPort < ucast 32 firstAllowed ∨ endPort > ucast 32 lastAllowed) <|
      NonDetE.throwError .illegalOperation
  | _ => NonDetE.liftE NonDet.fail

/-- l4v: ArchDecode_A.X64_A.decode_port_invocation: IO port reads and
writes. -/
def decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) :
    SEMonad Z ArchInvocation :=
  match invocationType label with
  | .archInvocationLabel .x64IOPortIn8 => do
    argsAtLeast 1 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 1
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortIn8
  | .archInvocationLabel .x64IOPortIn16 => do
    argsAtLeast 1 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 2
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortIn16
  | .archInvocationLabel .x64IOPortIn32 => do
    argsAtLeast 1 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 4
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortIn32
  | .archInvocationLabel .x64IOPortOut8 => do
    argsAtLeast 2 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 1
    let outputData ← NonDetE.returnOk (ucast 8 (the args[1]?))
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortOut8 outputData
  | .archInvocationLabel .x64IOPortOut16 => do
    argsAtLeast 2 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 2
    let outputData ← NonDetE.returnOk (ucast 16 (the args[1]?))
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortOut16 outputData
  | .archInvocationLabel .x64IOPortOut32 => do
    argsAtLeast 2 args
    let port ← NonDetE.returnOk (ucast 16 (the args[0]?))
    ensurePortOperationAllowed cap (ucast 32 port) 4
    let outputData ← NonDetE.returnOk (ucast 32 (the args[1]?))
    NonDetE.returnOk <| .invokeIOPort <| .ioPortInvocation port <| .ioPortOut32 outputData
  | _ => NonDetE.throwError .illegalOperation

/-- l4v: ArchDecode_A.X64_A.is_ioport_range_free. -/
def isIoportRangeFree (f l : IoPort) : SMonad Z Bool := do
  let allocPorts ← NonDet.gets fun s : State Z => s.archState.x64AllocatedIoPorts
  return decide ({x | f ≤ x ∧ x ≤ l} ∩ {x | allocPorts x = true} = ∅)

/-- l4v: ArchDecode_A.X64_A.decode_ioport_control_invocation: issue an IO
port cap for a free range of ports. -/
def decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr)
    (_cap : ArchCap) (extraCaps : List Cap) : SEMonad Z ArchInvocation :=
  if invocationType label = .archInvocationLabel .x64IOPortControlIssue then
    if args.length ≥ 4 ∧ extraCaps.length ≥ 1 then
      let firstPort : IoPort := ucast 16 (the args[0]?)
      let lastPort : IoPort := ucast 16 (the args[1]?)
      let index := the args[2]?
      let depth := the args[3]?
      let cnode := the extraCaps[0]?
      do
        NonDetE.whenE (firstPort > lastPort) <| NonDetE.throwError (.invalidArgument 1)
        let check ← NonDetE.liftE <| isIoportRangeFree firstPort lastPort
        NonDetE.whenE (¬check) <| NonDetE.throwError .revokeFirst
        let destSlot ← lookupTargetSlot cnode (dataToCptr index) (unat depth)
        ensureEmpty destSlot
        NonDetE.returnOk <| .invokeIOPortControl <|
          .ioPortControlInvocation firstPort lastPort destSlot slot
    else NonDetE.throwError .truncatedMessage
  else NonDetE.throwError .illegalOperation

/-- l4v: ArchDecode_A.X64_A.decode_io_unmap_invocation (an l4v `X64STUB`,
`undefined`; VT-d). -/
def decodeIoUnmapInvocation (_label : Data) (_args : List Data) (_cte : CslotPtr) (_cap : ArchCap)
    (_extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  undefined

end

/-- l4v: ArchDecode_A.X64_A.page_cap_set_vmmap_type. -/
def pageCapSetVmmapType (cap : ArchCap) (t : VMMapType) : ArchCap :=
  match cap with
  | .pageCap dev p R _mapType pgsz mappedAddress => .pageCap dev p R t pgsz mappedAddress
  | _ => undefined

/-- l4v: ArchDecode_A.X64_A.get_iovm_rights. -/
def getIovmRights (cover base : VMRights) : VMRights :=
  if cover = {.allowRead} then (if Rights.allowRead ∈ base then {.allowRead} else ∅) else
  if Rights.allowRead ∈ cover then
    {.allowRead} ∪ (if Rights.allowWrite ∈ base then {.allowWrite} else ∅)
  else (if Rights.allowWrite ∈ base then {.allowWrite} else ∅)

-- l4v ArchDecode_A.pci_request_id_from_cap, decode_io_pt_invocation,
-- decode_io_frame_map_invocation, decode_io_map_invocation are commented out
-- (FIXME x64-vtd); not ported (no IOMMU).

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.decode_page_invocation: map, unmap or get the
address of a frame. The `VMIOSpaceMap` case of `X64PageUnmap` and the
`X64PageMapIO` label are cancelled in l4v (VT-d). -/
def decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  match cap with
  | .pageCap dev p R mapType pgsz mappedAddress =>
    if invocationType label = .archInvocationLabel .x64PageMap then
    if args.length > 2 ∧ extraCaps.length > 0
    then
      let vaddr := the args[0]?
      let rightsMask := the args[1]?
      let attr := the args[2]?
      let vspaceCap := (the extraCaps[0]?).1
      do
        let (vspace, asid) ← match vspaceCap with
          | .archObjectCap (.pml4Cap pm (some asid)) => NonDetE.returnOk (pm, asid)
          | _ => NonDetE.throwError (.invalidCapability 1)
        match mappedAddress with
        | some (asid', vaddr') => do
          NonDetE.whenE (asid' ≠ asid) (NonDetE.throwError (.invalidCapability 1))
          NonDetE.whenE (mapType ≠ .vmVSpaceMap) <| NonDetE.throwError .illegalOperation
          NonDetE.whenE (vaddr' ≠ vaddr) (NonDetE.throwError (.invalidArgument 0))
        | none => do
          let vtop ← NonDetE.returnOk (vaddr + (1 <<< pageBitsForSize pgsz))
          NonDetE.whenE (vaddr > userVtop ∨ vtop > userVtop) <|
            NonDetE.throwError (.invalidArgument 0)
        let vspace' ← lookupErrorOnFailure false <| findVspaceForAsid asid
        NonDetE.whenE (vspace' ≠ vspace) <| NonDetE.throwError (.invalidCapability 1)
        let vmRights ← NonDetE.returnOk (maskVmRights R <| dataToRights rightsMask)
        checkVpAlignment pgsz vaddr
        let entries ← createMappingEntries (addrFromPPtr p) vaddr pgsz vmRights
          (attribsFromWord attr) vspace
        ensureSafeMapping entries
        NonDetE.returnOk <| .invokePage <| .pageMap
          (.archObjectCap <| .pageCap dev p R .vmVSpaceMap pgsz (some (asid, vaddr))) cte entries vspace
    else NonDetE.throwError .truncatedMessage
    else if invocationType label = .archInvocationLabel .x64PageUnmap then
      -- l4v (cancelled): case map_type of VMIOSpaceMap ⇒
      --   decode_io_unmap_invocation label args cte cap extra_caps | _ ⇒
      NonDetE.returnOk <| .invokePage <| .pageUnmap cap cte
    -- l4v (cancelled, FIXME x64-vtd): X64PageMapIO ⇒ decode_io_map_invocation
    else if invocationType label = .archInvocationLabel .x64PageGetAddress
    then NonDetE.returnOk <| .invokePage <| .pageGetAddr p
    else NonDetE.throwError .illegalOperation
  | _ => NonDetE.liftE NonDet.fail

end

/-- l4v: ArchDecode_A.X64_A.filter_vm_attributes. -/
def filterVmAttributes (attrs : VMAttributes) : TableAttrs :=
  {s | ∃ s' ∈ attrs, s' = .ptAttr s}

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.decode_page_table_invocation. -/
def decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  match cap with
  | .pageTableCap p mappedAddress =>
    if invocationType label = .archInvocationLabel .x64PageTableMap then
    if args.length > 1 ∧ extraCaps.length > 0
    then
      let vaddr := the args[0]?
      let attr := the args[1]?
      let pml4Cap := (the extraCaps[0]?).1
      do
        NonDetE.whenE (mappedAddress ≠ none) <| NonDetE.throwError (.invalidCapability 0)
        let vaddr' ← NonDetE.returnOk (vaddr &&& ~~~(mask pdShiftBits))
        let (pml4, asid) ← match pml4Cap with
          | .archObjectCap (.pml4Cap pml4 (some asid)) => NonDetE.returnOk (pml4, asid)
          | _ => NonDetE.throwError (.invalidCapability 1)
        NonDetE.whenE (userVtop < vaddr') <| NonDetE.throwError (.invalidArgument 0)
        let pml4' ← lookupErrorOnFailure false <| findVspaceForAsid asid
        NonDetE.whenE (pml4' ≠ pml4) <| NonDetE.throwError (.invalidCapability 1)
        let pdSlot ← lookupErrorOnFailure false <| lookupPdSlot pml4 vaddr'
        let oldPde ← NonDetE.liftE <| getPde pdSlot
        NonDetE.unlessE (oldPde = .invalidPDE) <| NonDetE.throwError .deleteFirst
        let pde ← NonDetE.returnOk (PDE.pageTablePDE (addrFromPPtr p)
          (filterVmAttributes <| attribsFromWord attr) vmReadWrite)
        let cap' ← NonDetE.returnOk <| Cap.archObjectCap <| .pageTableCap p <| some (asid, vaddr')
        NonDetE.returnOk <| .invokePageTable <| .pageTableMap cap' cte pde pdSlot pml4
    else NonDetE.throwError .truncatedMessage
    else if invocationType label = .archInvocationLabel .x64PageTableUnmap then do
      let final ← NonDetE.liftE <| isFinalCap (.archObjectCap cap)
      NonDetE.unlessE final <| NonDetE.throwError .revokeFirst
      NonDetE.returnOk <| .invokePageTable <| .pageTableUnmap (.archObjectCap cap) cte
    else NonDetE.throwError .illegalOperation
  | _ => NonDetE.liftE NonDet.fail

/-- l4v: ArchDecode_A.X64_A.decode_page_directory_invocation. -/
def decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr)
    (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  match cap with
  | .pageDirectoryCap p mappedAddress =>
    if invocationType label = .archInvocationLabel .x64PageDirectoryMap then
    if args.length > 1 ∧ extraCaps.length > 0
    then
      let vaddr := the args[0]?
      let attr := the args[1]?
      let pml4Cap := (the extraCaps[0]?).1
      do
        NonDetE.whenE (mappedAddress ≠ none) <| NonDetE.throwError (.invalidCapability 0)
        let vaddr' ← NonDetE.returnOk (vaddr &&& ~~~(mask pdptShiftBits))
        let (pml4, asid) ← match pml4Cap with
          | .archObjectCap (.pml4Cap pml4 (some asid)) => NonDetE.returnOk (pml4, asid)
          | _ => NonDetE.throwError (.invalidCapability 1)
        NonDetE.whenE (userVtop < vaddr') <| NonDetE.throwError (.invalidArgument 0)
        let pml4' ← lookupErrorOnFailure false <| findVspaceForAsid asid
        NonDetE.whenE (pml4' ≠ pml4) <| NonDetE.throwError (.invalidCapability 1)
        let pdptSlot ← lookupErrorOnFailure false <| lookupPdptSlot pml4 vaddr'
        let oldPdpte ← NonDetE.liftE <| getPdpte pdptSlot
        NonDetE.unlessE (oldPdpte = .invalidPDPTE) <| NonDetE.throwError .deleteFirst
        let pdpte ← NonDetE.returnOk (PDPTE.pageDirectoryPDPTE (addrFromPPtr p)
          (filterVmAttributes <| attribsFromWord attr) vmReadWrite)
        let cap' ← NonDetE.returnOk <| Cap.archObjectCap <| .pageDirectoryCap p <| some (asid, vaddr')
        NonDetE.returnOk <| .invokePageDirectory <| .pageDirectoryMap cap' cte pdpte pdptSlot pml4
    else NonDetE.throwError .truncatedMessage
    else if invocationType label = .archInvocationLabel .x64PageDirectoryUnmap then do
      let final ← NonDetE.liftE <| isFinalCap (.archObjectCap cap)
      NonDetE.unlessE final <| NonDetE.throwError .revokeFirst
      NonDetE.returnOk <| .invokePageDirectory <| .pageDirectoryUnmap (.archObjectCap cap) cte
    else NonDetE.throwError .illegalOperation
  | _ => NonDetE.liftE NonDet.fail

/-- l4v: ArchDecode_A.X64_A.decode_pdpt_invocation. -/
def decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  match cap with
  | .pdPointerTableCap p mappedAddress =>
    if invocationType label = .archInvocationLabel .x64PDPTMap then
    if args.length > 1 ∧ extraCaps.length > 0
    then
      let vaddr := the args[0]?
      let attr := the args[1]?
      let pml4Cap := (the extraCaps[0]?).1
      do
        NonDetE.whenE (mappedAddress ≠ none) <| NonDetE.throwError (.invalidCapability 0)
        let vaddr' ← NonDetE.returnOk (vaddr &&& ~~~(mask pml4ShiftBits))
        let (pml4, asid) ← match pml4Cap with
          | .archObjectCap (.pml4Cap pml4 (some asid)) => NonDetE.returnOk (pml4, asid)
          | _ => NonDetE.throwError (.invalidCapability 1)
        NonDetE.whenE (userVtop < vaddr') <| NonDetE.throwError (.invalidArgument 0)
        let pml4' ← lookupErrorOnFailure false <| findVspaceForAsid asid
        NonDetE.whenE (pml4' ≠ pml4) <| NonDetE.throwError (.invalidCapability 1)
        let pmlSlot ← NonDetE.returnOk (lookupPml4Slot pml4 vaddr')
        let oldPml4e ← NonDetE.liftE <| getPml4e pmlSlot
        NonDetE.unlessE (oldPml4e = .invalidPML4E) <| NonDetE.throwError .deleteFirst
        let pml4e ← NonDetE.returnOk (PML4E.pdPointerTablePML4E (addrFromPPtr p)
          (filterVmAttributes <| attribsFromWord attr) vmReadWrite)
        let cap' ← NonDetE.returnOk <| Cap.archObjectCap <| .pdPointerTableCap p <| some (asid, vaddr')
        NonDetE.returnOk <| .invokePDPT <| .pdptMap cap' cte pml4e pmlSlot pml4
    else NonDetE.throwError .truncatedMessage
    else if invocationType label = .archInvocationLabel .x64PDPTUnmap then do
      let final ← NonDetE.liftE <| isFinalCap (.archObjectCap cap)
      NonDetE.unlessE final <| NonDetE.throwError .revokeFirst
      NonDetE.returnOk <| .invokePDPT <| .pdptUnmap (.archObjectCap cap) cte
    else NonDetE.throwError .illegalOperation
  | _ => NonDetE.liftE NonDet.fail

/-- l4v: ArchDecode_A.X64_A.arch_decode_invocation. -/
def archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr)
    (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SEMonad Z ArchInvocation :=
  match cap with
  -- Virtualization decoder refinement is separate from the native x86 model.
  | .vcpuCap .. | .eptCap .. => NonDetE.liftE NonDet.fail
  | .pdPointerTableCap _ _ => decodePdptInvocation label args cte cap extraCaps
  | .pageDirectoryCap _ _ => decodePageDirectoryInvocation label args cte cap extraCaps
  | .pageTableCap _ _ => decodePageTableInvocation label args cte cap extraCaps
  | .pageCap _ _ _ _ _ _ => decodePageInvocation label args cte cap extraCaps
  | .asidControlCap =>
    if invocationType label = .archInvocationLabel .x64ASIDControlMakePool then
    if args.length > 1 ∧ extraCaps.length > 1
    then
      let index := the args[0]?
      let depth := the args[1]?
      let (untyped, parentSlot) := the extraCaps[0]?
      let root := (the extraCaps[1]?).1
      do
        let asidTable ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64AsidTable
        let freeSet ← NonDetE.returnOk (dom asidTable)ᶜ
        NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
        let free ← NonDetE.liftE <| selectExt (fun _ => freeAsidSelect asidTable) freeSet
        let base ← NonDetE.returnOk (ucast asidRepLen free <<< asidLowBits)
        let (p, n) ← match untyped with
          | .untypedCap false p n _f => NonDetE.returnOk (p, n)
          | _ => NonDetE.throwError (.invalidCapability 1)
        let frame ← (if n = pageBits
          then do
            ensureNoChildren parentSlot
            NonDetE.returnOk p
          else NonDetE.throwError (.invalidCapability 1) : SEMonad Z ObjRef)
        let destSlot ← lookupTargetSlot root (toBl index) (unat depth)
        ensureEmpty destSlot
        NonDetE.returnOk <| .invokeASIDControl <| .makePool frame destSlot parentSlot base
    else NonDetE.throwError .truncatedMessage
    else NonDetE.throwError .illegalOperation
  | .asidPoolCap p base =>
    if invocationType label = .archInvocationLabel .x64ASIDPoolAssign then
    if extraCaps.length > 0
    then
      let (pdCap, pdCapSlot) := the extraCaps[0]?
      match pdCap with
      | .archObjectCap (.pml4Cap _ none) => do
        let asidTable ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64AsidTable
        let poolPtr ← NonDetE.returnOk (asidTable (asidHighBitsOf base))
        NonDetE.whenE (poolPtr = none) <| NonDetE.throwError (.failedLookup false .invalidRoot)
        NonDetE.whenE (p ≠ the poolPtr) <| NonDetE.throwError (.invalidCapability 0)
        let pool ← NonDetE.liftE <| getAsidPool p
        let freeSet ← NonDetE.returnOk ((dom pool)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0})
        NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
        let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect pool base) freeSet
        NonDetE.returnOk <| .invokeASIDPool <| .assign (ucast asidRepLen offset + base) p pdCapSlot
      | _ => NonDetE.throwError (.invalidCapability 1)
    else NonDetE.throwError .truncatedMessage
    else NonDetE.throwError .illegalOperation
  | .ioPortCap f l => decodePortInvocation label args (.ioPortCap f l)
  | .ioPortControlCap => decodeIoportControlInvocation label args cte cap (extraCaps.map Prod.fst)
  | .pml4Cap _a _b => NonDetE.throwError .illegalOperation

end

/-- l4v: ArchDecode_A.X64_A.arch_data_to_obj_type. -/
def archDataToObjType (n : Nat) : Option AObjectType :=
  if n = 0 then some .pdptObj
  else if n = 1 then some .pml4Obj
  else if n = 2 then some .hugePageObj
  else if n = 3 then some .smallPageObj
  else if n = 4 then some .largePageObj
  else if n = 5 then some .pageTableObj
  else if n = 6 then some .pageDirectoryObj
  else if n = 7 then some .vcpuObj
  else if n = 8 then some .eptPml4Obj
  else if n = 9 then some .eptPdptObj
  else if n = 10 then some .eptPdObj
  else if n = 11 then some .eptPtObj
  else none

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.arch_check_irq: x86 has no generic
`IRQIssueIRQHandler`. -/
def archCheckIrq (_irq : Data) : SEMonad Z Unit := NonDetE.throwError .illegalOperation

/-! ## Decode_A: CNode -/

/-- l4v: Decode_A.decode_cnode_invocation. -/
def decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) :
    SEMonad Z CnodeInvocation := do
  NonDetE.unlessE (genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate) <|
    NonDetE.throwError .illegalOperation
  NonDetE.whenE (args.length < 2) (NonDetE.throwError .truncatedMessage)
  let index ← NonDetE.returnOk <| dataToCptr <| the args[0]?
  let bits ← NonDetE.returnOk <| dataToNat <| the args[1]?
  let args ← NonDetE.returnOk <| args.drop 2
  let destSlot ← lookupTargetSlot cap index bits
  if args.length ≥ 2 ∧ excaps.length > 0
        ∧ genInvocationType label ∈ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate then
  do
    let srcIndex ← NonDetE.returnOk <| dataToCptr <| the args[0]?
    let srcDepth ← NonDetE.returnOk <| dataToNat <| the args[1]?
    let args ← NonDetE.returnOk <| args.drop 2
    let srcRootCap ← NonDetE.returnOk <| the excaps[0]?
    ensureEmpty destSlot
    let srcSlot ←
      lookupSourceSlot srcRootCap srcIndex srcDepth
    let srcCap ← NonDetE.liftE <| getCap srcSlot
    NonDetE.whenE (srcCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup true <| .missingCapability srcDepth
    let (rights, capData, isMove) ← (match genInvocationType label, args with
      | .cnodeCopy, rightsWord :: _ => do
        let rights ← NonDetE.returnOk <| dataToRights <| rightsWord
        NonDetE.returnOk <| (rights, none, false)
      | .cnodeMint, rightsWord :: capData :: _ => do
        let rights ← NonDetE.returnOk <| dataToRights <| rightsWord
        NonDetE.returnOk <| (rights, some capData, false)
      | .cnodeMove, _ => NonDetE.returnOk (allRights, none, true)
      | .cnodeMutate, capData :: _ => NonDetE.returnOk (allRights, some capData, true)
      | _, _ => NonDetE.throwError .truncatedMessage : SEMonad Z (CapRights × Option Data × Bool))
    let srcCap ← NonDetE.returnOk <| maskCap rights srcCap
    let newCap ← (if isMove then NonDetE.returnOk else deriveCap srcSlot) (match capData with
      | some w => updateCapData isMove w srcCap
      | none => srcCap)
    NonDetE.whenE (newCap = .nullCap) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| (if isMove then CnodeInvocation.moveCall else .insertCall) newCap srcSlot destSlot
  else if genInvocationType label = .cnodeRevoke then NonDetE.returnOk <| .revokeCall destSlot
  else if genInvocationType label = .cnodeDelete then NonDetE.returnOk <| .deleteCall destSlot
  else if genInvocationType label = .cnodeCancelBadgedSends then do
    let cap ← NonDetE.liftE <| getCap destSlot
    NonDetE.unlessE (hasCancelSendRights cap) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .cancelBadgedSendsCall cap
  else if genInvocationType label = .cnodeRotate ∧ args.length > 5
          ∧ excaps.length > 1 then
  do
    let pivotNewData ← NonDetE.returnOk <| the args[0]?
    let pivotIndex ← NonDetE.returnOk <| dataToCptr <| the args[1]?
    let pivotDepth ← NonDetE.returnOk <| dataToNat <| the args[2]?
    let srcNewData ← NonDetE.returnOk <| the args[3]?
    let srcIndex ← NonDetE.returnOk <| dataToCptr <| the args[4]?
    let srcDepth ← NonDetE.returnOk <| dataToNat <| the args[5]?
    let pivotRootCap ← NonDetE.returnOk <| the excaps[0]?
    let srcRootCap ← NonDetE.returnOk <| the excaps[1]?

    let srcSlot ← lookupSourceSlot srcRootCap srcIndex srcDepth
    let pivotSlot ← lookupPivotSlot pivotRootCap pivotIndex pivotDepth

    NonDetE.whenE (pivotSlot = srcSlot ∨ pivotSlot = destSlot) <|
      NonDetE.throwError .illegalOperation

    NonDetE.unlessE (srcSlot = destSlot) <| ensureEmpty destSlot

    let srcCap ← NonDetE.liftE <| getCap srcSlot
    NonDetE.whenE (srcCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup true <| .missingCapability srcDepth

    let pivotCap ← NonDetE.liftE <| getCap pivotSlot
    NonDetE.whenE (pivotCap = .nullCap) <|
      NonDetE.throwError <| .failedLookup false <| .missingCapability pivotDepth

    let newSrcCap ← NonDetE.returnOk <| updateCapData true srcNewData srcCap
    let newPivotCap ← NonDetE.returnOk <| updateCapData true pivotNewData pivotCap

    NonDetE.whenE (newSrcCap = .nullCap) <| NonDetE.throwError .illegalOperation
    NonDetE.whenE (newPivotCap = .nullCap) <| NonDetE.throwError .illegalOperation

    NonDetE.returnOk <| .rotateCall newSrcCap newPivotCap srcSlot pivotSlot destSlot
  else
    NonDetE.throwError .truncatedMessage

/-! ## Decode_A: threads -/

/-- l4v: Decode_A.decode_read_registers. -/
def decodeReadRegisters (data : List Data) (cap : Cap) : SEMonad Z TcbInvocation :=
  match data with
  | flags :: n :: _ => do
    rangeCheck n 1 <| BitVec.ofNat 64 (frameRegisters.length + gpRegisters.length)
    let p ← match cap with
      | .threadCap p => NonDetE.returnOk p
      | _ => undefined
    let self ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.whenE (p = self) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .readRegisters p (testBit flags 0) n ArchDefaultExtraRegisters
  | _ => NonDetE.throwError .truncatedMessage

/-- l4v: Decode_A.decode_copy_registers. -/
def decodeCopyRegisters (data : List Data) (cap : Cap) (extraCaps : List Cap) :
    SEMonad Z TcbInvocation :=
  match data with
  | flags :: _ => do
    let suspendSource ← NonDetE.returnOk (testBit flags 0)
    let resumeTarget ← NonDetE.returnOk (testBit flags 1)
    let transferFrame ← NonDetE.returnOk (testBit flags 2)
    let transferInteger ← NonDetE.returnOk (testBit flags 3)
    NonDetE.whenE (extraCaps = []) <| NonDetE.throwError .truncatedMessage
    let srcTcb ← (match extraCaps with
      | .threadCap p :: _ => NonDetE.returnOk p
      | _ => NonDetE.throwError <| .invalidCapability 1)
    let p ← match cap with
      | .threadCap p => NonDetE.returnOk p
      | _ => undefined
    NonDetE.returnOk <| .copyRegisters p srcTcb
                             suspendSource resumeTarget
                             transferFrame transferInteger
                             ArchDefaultExtraRegisters
  | _ => NonDetE.throwError .truncatedMessage

/-- l4v: Decode_A.decode_write_registers. -/
def decodeWriteRegisters (data : List Data) (cap : Cap) : SEMonad Z TcbInvocation :=
  match data with
  | flags :: n :: values => do
    NonDetE.whenE (values.length < unat n) <| NonDetE.throwError .truncatedMessage
    let p ← match cap with
      | .threadCap p => NonDetE.returnOk p
      | _ => undefined
    let self ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.whenE (p = self) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .writeRegisters p (testBit flags 0)
               (values.take (unat n)) ArchDefaultExtraRegisters
  | _ => NonDetE.throwError .truncatedMessage

/-- l4v: Decode_A.check_prio: a new priority may not exceed the authorising
thread's maximum controlled priority. -/
def checkPrio (newPrio : Data) (authTcb : ObjRef) : SEMonad Z Unit := do
  let mcp ← NonDetE.liftE <| threadGet Tcb.tcbMcpriority authTcb
  NonDetE.whenE (newPrio > ucast 64 mcp) <| NonDetE.throwError (.rangeError 0 (ucast 64 mcp))

/-- l4v: Decode_A.decode_set_priority. -/
def decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length = 0 ∨ extraCaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let prio ← NonDetE.returnOk <| ucast 8 (the args[0]?)
  let authTcb ← match (the extraCaps[0]?).1 with
    | .threadCap tcbPtr => NonDetE.returnOk tcbPtr
    | _ => NonDetE.throwError (.invalidCapability 1)
  checkPrio (the args[0]?) authTcb
  NonDetE.returnOk (.threadControlSched (objRefOf cap) slot none none
                          (some (prio, authTcb)) none)

/-- l4v: Decode_A.decode_set_mcpriority. -/
def decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length = 0 ∨ extraCaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let newMcp ← NonDetE.returnOk <| ucast 8 <| the args[0]?
  let authTcb ← match (the extraCaps[0]?).1 with
    | .threadCap tcbPtr => NonDetE.returnOk tcbPtr
    | _ => NonDetE.throwError (.invalidCapability 1)
  checkPrio (the args[0]?) authTcb
  NonDetE.returnOk (.threadControlSched (objRefOf cap) slot none (some (newMcp, authTcb))
                          none none)

/-- l4v: Decode_A.decode_set_ipc_buffer. -/
def decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length = 0) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (excs.length = 0) <| NonDetE.throwError .truncatedMessage
  let buffer ← NonDetE.returnOk <| dataToVref <| the args[0]?
  let (bcap, bslot) ← NonDetE.returnOk <| the excs[0]?
  let newbuf ← (if buffer = 0 then NonDetE.returnOk none
           else do
      let bufferCap ← deriveCap bslot bcap
      checkValidIpcBuffer buffer bufferCap
      NonDetE.returnOk <| some (bufferCap, bslot) : SEMonad Z (Option (Cap × CslotPtr)))
  NonDetE.returnOk <|
    .threadControlCaps (objRefOf cap) slot none none none none (some (buffer, newbuf))

end

/-- l4v: Decode_A.has_handler_rights. -/
def hasHandlerRights (cap : Cap) : Prop :=
  AllowSend ∈ capRights cap ∧ {Rights.allowGrant, .allowGrantReply} ∩ capRights cap ≠ ∅

/-- l4v: Decode_A.valid_fault_handler (`is_ep_cap and has_handler_rights or
(=) NullCap`). -/
def validFaultHandler (cap : Cap) : Prop :=
  (isEpCap cap ∧ hasHandlerRights cap) ∨ Cap.nullCap = cap

section
variable {Z : Type} [StateExt Z]

/-- l4v: Decode_A.check_handler_ep. -/
def checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : SEMonad Z (Cap × CslotPtr) := do
  NonDetE.unlessE (validFaultHandler hCapHSlot.1) <| NonDetE.throwError <| .invalidCapability pos
  NonDetE.returnOk hCapHSlot

/-- l4v: Decode_A.decode_cv_space: the new CSpace and VSpace roots of a
thread. -/
def decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) :
    SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length < 2 ∨ excaps.length < 2) <| NonDetE.throwError .truncatedMessage
  let crootData ← NonDetE.returnOk <| the args[0]?
  let vrootData ← NonDetE.returnOk <| the args[1]?
  let crootArg ← NonDetE.returnOk <| the excaps[0]?
  let vrootArg ← NonDetE.returnOk <| the excaps[1]?
  let canChgCr ← NonDetE.liftE <| NonDet.liftM not <| slotCapLongRunningDelete
                    <| getTcbCtablePtr <| objRefOf cap
  let canChgVr ← NonDetE.liftE <| NonDet.liftM not <| slotCapLongRunningDelete
                    <| getTcbVtablePtr <| objRefOf cap
  NonDetE.unlessE (canChgCr ∧ canChgVr) <| NonDetE.throwError .illegalOperation

  let crootCap ← NonDetE.returnOk <| crootArg.1
  let crootSlot ← NonDetE.returnOk <| crootArg.2
  let crootCap' ← deriveCap crootSlot <|
                  (if crootData = 0 then id else updateCapData false crootData)
                  crootCap
  NonDetE.unlessE (isCnodeCap crootCap') <| NonDetE.throwError .illegalOperation
  let croot ← NonDetE.returnOk (crootCap', crootSlot)

  let vrootCap ← NonDetE.returnOk <| vrootArg.1
  let vrootSlot ← NonDetE.returnOk <| vrootArg.2
  let vrootCap' ← deriveCap vrootSlot <|
                  (if vrootData = 0 then id else updateCapData false vrootData)
                  vrootCap
  NonDetE.unlessE (isValidVtableRoot vrootCap') <| NonDetE.throwError .illegalOperation
  let vroot ← NonDetE.returnOk (vrootCap', vrootSlot)

  NonDetE.returnOk <| .threadControlCaps (objRefOf cap) slot none none
                           (some croot) (some vroot) none

/-- l4v: Decode_A.decode_set_space. -/
def decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) :
    SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length < 2 ∨ excaps.length < 3) <| NonDetE.throwError .truncatedMessage
  let space ← decodeCvSpace (args.take 2) cap slot ((excaps.drop 1).take 2)
  let fhArg ← NonDetE.returnOk <| the excaps[0]?
  let faultHandler ← checkHandlerEp 1 fhArg
  NonDetE.returnOk <| .threadControlCaps (objRefOf cap) slot (some faultHandler) none
                           space.tcNewCroot space.tcNewVroot none

/-- l4v: Decode_A.decode_update_sc: the scheduling context change of a
`SetSchedParams` (`none` if none). -/
def decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) :
    SEMonad Z (Option (Option ObjRef)) := do
  let tcbPtr ← NonDetE.returnOk <| objRefOf cap
  let tcbSc ← NonDetE.liftE <| getTcbObjRef Tcb.tcbSchedContext tcbPtr
  let scPtrOpt ←
    match scCap with
    | .nullCap => do
      let ctPtr ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
      NonDetE.whenE (tcbPtr = ctPtr) <| NonDetE.throwError .illegalOperation
      NonDetE.returnOk none
    | .schedContextCap _ _ => do
      let scPtr ← NonDetE.returnOk <| objRefOf scCap
      let scTcb ← NonDetE.liftE <| getScObjRef SchedContext.scTcb scPtr
      NonDetE.whenE (tcbSc ≠ some scPtr ∧ (tcbSc ≠ none ∨ scTcb ≠ none))
            (NonDetE.throwError .illegalOperation)
      let blocked ← NonDetE.liftE <| isBlocked tcbPtr
      let released ← NonDetE.liftE <| getScReleased scPtr
      NonDetE.whenE (blocked ∧ ¬released) <| NonDetE.throwError .illegalOperation
      NonDetE.returnOk (some scPtr)
    | _ => NonDetE.throwError (.invalidCapability 2)
  NonDetE.returnOk (if tcbSc ≠ scPtrOpt then some scPtrOpt else none)

/-- l4v: Decode_A.decode_tcb_configure. -/
def decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length < 3) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (extraCaps.length < 3) <| NonDetE.throwError .truncatedMessage
  let buffer ← NonDetE.returnOk <| the args[2]?
  let bufferCap ← NonDetE.returnOk <| the extraCaps[2]?
  let setParams ← decodeSetIpcBuffer [buffer] cap slot [bufferCap]
  let setSpace ← decodeCvSpace (args.take 2) cap slot (extraCaps.take 2)
  NonDetE.returnOk <| .threadControlCaps (objRefOf cap) slot
                           none none
                           setSpace.tcNewCroot setSpace.tcNewVroot
                           setParams.tcNewBuffer

/-- l4v: Decode_A.decode_set_timeout_ep. -/
def decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) :
    SEMonad Z TcbInvocation := do
  NonDetE.whenE (extraCaps.length < 1) <| NonDetE.throwError .truncatedMessage
  let thArg ← NonDetE.returnOk <| the extraCaps[0]?
  let handler ← checkHandlerEp 1 thArg
  NonDetE.returnOk <| .threadControlCaps (objRefOf cap) slot
                           none (some handler) none none none

/-- l4v: Decode_A.decode_bind_notification. -/
def decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) :
    SEMonad Z TcbInvocation :=
  match cap with
  | .threadCap tcb => do
    NonDetE.whenE (extraCaps.length = 0) <| NonDetE.throwError .truncatedMessage
    let nTFN ← NonDetE.liftE <| getTcbObjRef Tcb.tcbBoundNotification tcb
    match nTFN with
    | some _ => NonDetE.throwError .illegalOperation
    | none => NonDetE.returnOk ()
    let (ntfnptr, rights) ← match (the extraCaps.head?).1 with
      | .notificationCap ptr _ r => NonDetE.returnOk (ptr, r)
      | _ => NonDetE.throwError .illegalOperation
    NonDetE.whenE (AllowRecv ∉ rights) <| NonDetE.throwError .illegalOperation
    let ntfn ← NonDetE.liftE <| getNotification ntfnptr
    match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
    | .idleNtfn, none => NonDetE.returnOk ()
    | .activeNtfn _, none => NonDetE.returnOk ()
    | _, _ => NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .notificationControl tcb (some ntfnptr)
  | _ => NonDetE.throwError .illegalOperation

/-- l4v: Decode_A.decode_unbind_notification. -/
def decodeUnbindNotification (cap : Cap) : SEMonad Z TcbInvocation :=
  match cap with
  | .threadCap tcb => do
    let nTFN ← NonDetE.liftE <| getTcbObjRef Tcb.tcbBoundNotification tcb
    match nTFN with
    | none => NonDetE.throwError .illegalOperation
    | some _ => NonDetE.returnOk ()
    NonDetE.returnOk <| .notificationControl tcb none
  | _ => NonDetE.throwError .illegalOperation

/-- l4v: Decode_A.decode_set_tls_base. -/
def decodeSetTlsBase (args : List Data) (cap : Cap) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length = 0) <| NonDetE.throwError .truncatedMessage
  NonDetE.returnOk (.setTLSBase (objRefOf cap) (ucast 64 (the args[0]?)))

/-- l4v: Decode_A.decode_set_flags. -/
def decodeSetFlags (args : List Data) (cap : Cap) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length < 2) <| NonDetE.throwError .truncatedMessage
  NonDetE.returnOk (.setFlags (objRefOf cap) (wordToTcbFlags (the args[0]?))
    (wordToTcbFlags (the args[1]?)))

/-- l4v: Decode_A.decode_set_sched_params. -/
def decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation := do
  NonDetE.whenE (args.length < 2) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (extraCaps.length < 3) <| NonDetE.throwError .truncatedMessage
  let newMcp ← NonDetE.returnOk <| ucast 8 <| the args[0]?
  let newPrio ← NonDetE.returnOk <| ucast 8 <| the args[1]?
  let authCap ← NonDetE.returnOk <| (the extraCaps[0]?).1
  let scCap ← NonDetE.returnOk <| (the extraCaps[1]?).1
  let fhArg ← NonDetE.returnOk <| the extraCaps[2]?
  let authTcb ← match authCap with
    | .threadCap tcbPtr => NonDetE.returnOk tcbPtr
    | _ => NonDetE.throwError (.invalidCapability 1)
  checkPrio (the args[0]?) authTcb
  checkPrio (the args[1]?) authTcb
  let scPtrOptOpt ← decodeUpdateSc cap slot scCap
  let fh ← checkHandlerEp 3 fhArg
  NonDetE.returnOk <| .threadControlSched (objRefOf cap) slot (some fh)
                           (some (newMcp, authTcb)) (some (newPrio, authTcb))
                           scPtrOptOpt

/-- l4v: Decode_A.decode_tcb_invocation. -/
def decodeTcbInvocation (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SEMonad Z TcbInvocation :=
  match genInvocationType label with
  | .tcbReadRegisters => decodeReadRegisters args cap
  | .tcbWriteRegisters => decodeWriteRegisters args cap
  | .tcbCopyRegisters => decodeCopyRegisters args cap <| excs.map Prod.fst
  | .tcbSuspend => NonDetE.returnOk <| .suspend <| objRefOf cap
  | .tcbResume => NonDetE.returnOk <| .resume <| objRefOf cap
  | .tcbConfigure => decodeTcbConfigure args cap slot excs
  | .tcbSetPriority => decodeSetPriority args cap slot excs
  | .tcbSetMCPriority => decodeSetMcpriority args cap slot excs
  | .tcbSetSchedParams => decodeSetSchedParams args cap slot excs
  | .tcbSetTimeoutEndpoint => decodeSetTimeoutEp cap slot excs
  | .tcbSetIPCBuffer => decodeSetIpcBuffer args cap slot excs
  | .tcbSetSpace => decodeSetSpace args cap slot excs
  | .tcbBindNotification => decodeBindNotification cap excs
  | .tcbUnbindNotification => decodeUnbindNotification cap
  | .tcbSetTLSBase => decodeSetTlsBase args cap
  | .tcbSetFlags => decodeSetFlags args cap
  | _ => NonDetE.throwError .illegalOperation

/-! ## Decode_A: domains -/

/-- l4v: Decode_A.decode_domain_set. -/
def decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) :
    SEMonad Z DomainInvocation := do
  let domain ← (match args with
    | x :: _xs => do
      NonDetE.whenE (unat x ≥ numDomains) <| NonDetE.throwError <| .invalidArgument 0
      NonDetE.returnOk (ucast domainLen x)
    | _ => NonDetE.throwError .truncatedMessage : SEMonad Z Domain)
  NonDetE.whenE (excs.length = 0) <| NonDetE.throwError .truncatedMessage
  match (the excs.head?).1 with
  | .threadCap ptr => NonDetE.returnOk <| .invokeDomainSet ptr domain
  | _ => NonDetE.throwError <| .invalidArgument 1

/-- l4v: Decode_A.decode_domain_schedule_set_start. -/
def decodeDomainScheduleSetStart (args : List Data) : SEMonad Z DomainInvocation := do
  NonDetE.whenE (args.length = 0) <| NonDetE.throwError .truncatedMessage
  let index ← NonDetE.returnOk <| unat (the args[0]?)
  let sched ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.domainList
  NonDetE.whenE (index ≥ sched.length) <|
    NonDetE.throwError <| .rangeError 0 (BitVec.ofNat 64 (sched.length - 1))
  NonDetE.whenE (the sched[index]? = domainEndMarker) <| NonDetE.throwError <| .invalidArgument 0
  NonDetE.returnOk <| .invokeDomainScheduleSetStart index

/-- l4v: Decode_A.decode_domain_schedule_configure. -/
def decodeDomainScheduleConfigure (args : List Data) : SEMonad Z DomainInvocation := do
  NonDetE.whenE (args.length < 2 + timeArgLen) <| NonDetE.throwError .truncatedMessage
  let index ← NonDetE.returnOk <| unat (the args[0]?)
  let domain ← NonDetE.returnOk <| the args[1]?
  let duration ← NonDetE.returnOk <| parseTimeArg 2 args
  let sched ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.domainList
  -- Item at `length sched - 1` is reserved to always be an end marker
  NonDetE.whenE (index ≥ sched.length - 1) <|
    NonDetE.throwError <| .rangeError 0 (BitVec.ofNat 64 (sched.length - 2))
  NonDetE.whenE (unat domain ≥ numDomains) <|
    NonDetE.throwError <| .rangeError 0 (BitVec.ofNat 64 (numDomains - 1))
  NonDetE.whenE (duration > maxDomainDuration) <| NonDetE.throwError <| .invalidArgument 2
  NonDetE.whenE (duration = 0 ∧ domain ≠ 0) <| NonDetE.throwError <| .invalidArgument 1
  let start ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.domainStartIndex
  NonDetE.whenE (index = start ∧ duration = 0) <| NonDetE.throwError <| .invalidArgument 2
  NonDetE.returnOk <|
    .invokeDomainScheduleConfigure index (ucast domainLen domain) (ucast domainDurationLen duration)

/-- l4v: Decode_A.decode_domain_invocation. -/
def decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) :
    SEMonad Z DomainInvocation :=
  match genInvocationType label with
  | .domainSetSet => decodeDomainSet args excs
  | .domainScheduleConfigure => decodeDomainScheduleConfigure args
  | .domainScheduleSetStart => decodeDomainScheduleSetStart args
  | _ => NonDetE.throwError .illegalOperation

/-! ## Decode_A: scheduling contexts -/

/-- l4v: Decode_A.decode_sched_context_bind. -/
def decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) :
    SEMonad Z SchedContextInvocation := do
  NonDetE.whenE (excaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let cap ← NonDetE.returnOk <| the excaps.head?
  let sc ← NonDetE.liftE <| getSchedContext scPtr
  match cap with
  | .threadCap tcbPtr => do
    NonDetE.whenE (sc.scTcb ≠ none) <| NonDetE.throwError .illegalOperation
    let scPtrOpt ← NonDetE.liftE <| getTcbObjRef Tcb.tcbSchedContext tcbPtr
    NonDetE.whenE (scPtrOpt ≠ none) <| NonDetE.throwError .illegalOperation
    let st ← NonDetE.liftE <| getThreadState tcbPtr
    let released ← NonDetE.liftE <| getScReleased scPtr
    NonDetE.whenE (ipcQueuedThreadState st ∧ ¬released) <|
      NonDetE.throwError .illegalOperation
  | .notificationCap ntfnPtr _ _ => do
    NonDetE.whenE (sc.scNtfn ≠ none) <| NonDetE.throwError .illegalOperation
    let scPtrOpt ← NonDetE.liftE <| getNtfnObjRef Notification.ntfnSc ntfnPtr
    NonDetE.whenE (scPtrOpt ≠ none) <| NonDetE.throwError .illegalOperation
  | _ => NonDetE.throwError (.invalidCapability 1)
  NonDetE.returnOk <| .invokeSchedContextBind scPtr cap

/-- l4v: Decode_A.decode_sched_context_unbind_object. -/
def decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) :
    SEMonad Z SchedContextInvocation := do
  NonDetE.whenE (excaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let cap ← NonDetE.returnOk <| the excaps.head?
  match cap with
  | .threadCap tcbPtr => do
    let scTcbOpt ← NonDetE.liftE <| getScObjRef SchedContext.scTcb scPtr
    NonDetE.whenE (scTcbOpt ≠ some tcbPtr) <| NonDetE.throwError .illegalOperation
    let ctPtr ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.whenE (tcbPtr = ctPtr) <| NonDetE.throwError .illegalOperation
  | .notificationCap ntfnPtr _ _ => do
    let scNtfnOpt ← NonDetE.liftE <| getScObjRef SchedContext.scNtfn scPtr
    NonDetE.whenE (scNtfnOpt ≠ some ntfnPtr) <| NonDetE.throwError .illegalOperation
  | _ => NonDetE.throwError (.invalidCapability 1)
  NonDetE.returnOk <| .invokeSchedContextUnbindObject scPtr cap

/-- l4v: Decode_A.decode_sched_context_yield_to. -/
def decodeSchedContextYieldTo (scPtr : ObjRef) : SEMonad Z SchedContextInvocation := do
  let scTcbOpt ← NonDetE.liftE <| getScObjRef SchedContext.scTcb scPtr
  NonDetE.whenE (scTcbOpt = none) <| NonDetE.throwError .illegalOperation
  let ctPtr ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
  NonDetE.whenE (scTcbOpt = some ctPtr) <| NonDetE.throwError .illegalOperation
  let prios ← NonDetE.liftE <| threadGet Tcb.tcbPriority (the scTcbOpt)
  let ctMcp ← NonDetE.liftE <| threadGet Tcb.tcbMcpriority ctPtr
  NonDetE.whenE (prios > ctMcp) <| NonDetE.throwError .illegalOperation
  let ytPtr ← NonDetE.liftE <| threadGet Tcb.tcbYieldTo ctPtr
  NonDetE.whenE (ytPtr ≠ none) <| NonDetE.throwError .illegalOperation
  NonDetE.returnOk <| .invokeSchedContextYieldTo scPtr

/-- l4v: Decode_A.decode_sched_context_invocation. -/
def decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) :
    SEMonad Z SchedContextInvocation :=
  match genInvocationType label with
  | .schedContextConsumed => NonDetE.returnOk <| .invokeSchedContextConsumed scPtr
  | .schedContextBind => decodeSchedContextBind scPtr excaps
  | .schedContextUnbindObject => decodeSchedContextUnbindObject scPtr excaps
  | .schedContextUnbind => do
    let sc ← NonDetE.liftE <| getSchedContext scPtr
    let ctPtr ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.whenE (sc.scTcb = some ctPtr) <| NonDetE.throwError .illegalOperation
    NonDetE.returnOk <| .invokeSchedContextUnbind scPtr
  | .schedContextYieldTo => decodeSchedContextYieldTo scPtr
  | _ => NonDetE.throwError <| .illegalOperation

/-- l4v: Decode_A.decode_sched_control_invocation_flags: the budget, period,
extra refills, badge and flags of `SchedControlConfigureFlags`. -/
def decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) :
    SEMonad Z SchedControlInvocation := do
  NonDetE.unlessE (genInvocationType label = .schedControlConfigureFlags) <|
    NonDetE.throwError .illegalOperation
  NonDetE.whenE (excaps.length = 0) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (args.length < timeArgLen * 2 + 3) <| NonDetE.throwError .truncatedMessage
  let budgetUs ← NonDetE.returnOk <| parseTimeArgA 0 args
  NonDetE.whenE (budgetUs > MAX_PERIOD_US) <|
    NonDetE.throwError (.rangeError (ucast 64 MIN_BUDGET_US) (ucast 64 MAX_PERIOD_US))
  let periodUs ← NonDetE.returnOk <| parseTimeArgA timeArgLen args
  NonDetE.whenE (periodUs > MAX_PERIOD_US) <|
    NonDetE.throwError (.rangeError (ucast 64 MIN_BUDGET_US) (ucast 64 MAX_PERIOD_US))
  NonDetE.whenE (budgetUs < MIN_BUDGET_US) <|
    NonDetE.throwError (.rangeError (ucast 64 MIN_BUDGET_US) (ucast 64 MAX_PERIOD_US))
  NonDetE.whenE (periodUs < MIN_BUDGET_US) <|
    NonDetE.throwError (.rangeError (ucast 64 MIN_BUDGET_US) (ucast 64 MAX_PERIOD_US))
  NonDetE.whenE (periodUs < budgetUs) <|
    NonDetE.throwError (.rangeError (ucast 64 MIN_BUDGET_US) (ucast 64 periodUs))
  let targetCap ← NonDetE.returnOk <| the excaps.head?
  NonDetE.whenE (¬isSchedContextCap targetCap) <| NonDetE.throwError (.invalidCapability 1)
  let scPtr ← NonDetE.returnOk <| objRefOf targetCap
  NonDetE.assertE (MIN_REFILLS ≤ maxRefillsCap targetCap)
  let extraRefills ← NonDetE.returnOk <| the args[2 * timeArgLen]?
  NonDetE.whenE (unat extraRefills > maxRefillsCap targetCap - MIN_REFILLS) <|
    NonDetE.throwError (.rangeError 0 (BitVec.ofNat 64 (maxRefillsCap targetCap - MIN_REFILLS)))
  let badge ← NonDetE.returnOk <| the args[2 * timeArgLen + 1]?
  let flags ← NonDetE.returnOk <| the args[2 * timeArgLen + 2]?
  NonDetE.returnOk <| .invokeSchedControlConfigureFlags scPtr
     (usToTicks budgetUs) (usToTicks periodUs) (unat extraRefills + MIN_REFILLS)
     badge flags

/-! ## Decode_A: IRQ -/

/-- l4v: Decode_A.decode_irq_control_invocation. -/
def decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr)
    (cps : List Cap) : SEMonad Z IrqControlInvocation :=
  (if genInvocationType label = .irqIssueIRQHandler
    then if args.length ≥ 3 ∧ cps.length ≥ 1
      then
        let irqWord := the args[0]?
        let index := the args[1]?
        let depth := the args[2]?
        let cnode := the cps[0]?
        let irq : Irq := ucast 8 irqWord
        do
          archCheckIrq irqWord
          let irqActive ← NonDetE.liftE <| isIrqActive irq
          NonDetE.whenE irqActive <| NonDetE.throwError .revokeFirst

          let destSlot ← lookupTargetSlot
                 cnode (dataToCptr index) (unat depth)
          ensureEmpty destSlot

          NonDetE.returnOk <| .irqControl irq destSlot srcSlot
      else NonDetE.throwError .truncatedMessage
    else NonDetE.liftME IrqControlInvocation.archIRQControl <|
      archDecodeIrqControlInvocation label args srcSlot cps)

/-- l4v: Decode_A.decode_irq_handler_invocation. -/
def decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) :
    SEMonad Z IrqHandlerInvocation :=
  if genInvocationType label = .irqAckIRQ
    then NonDetE.returnOk <| .aCKIrq irq
  else if genInvocationType label = .irqSetIRQHandler
    then if cps ≠ []
      then let (cap, slot) := the cps.head?
      if isNtfnCap cap ∧ AllowSend ∈ capRights cap
      then NonDetE.returnOk <| .setIRQHandler irq cap slot
      else NonDetE.throwError <| .invalidCapability 0
    else NonDetE.throwError .truncatedMessage
  else if genInvocationType label = .irqClearIRQHandler
    then NonDetE.returnOk <| .clearIRQHandler irq
  else NonDetE.throwError .illegalOperation

/-! ## Decode_A: untyped -/

/-- l4v: Decode_A.data_to_obj_type. -/
def dataToObjType (type : Data) : SEMonad Z ApiObjectType := do
  let n ← NonDetE.returnOk <| dataToNat type
  if n = 0 then
    NonDetE.returnOk <| .untyped
  else if n = 1 then
    NonDetE.returnOk <| .tcbObject
  else if n = 2 then
    NonDetE.returnOk <| .endpointObject
  else if n = 3 then
    NonDetE.returnOk <| .notificationObject
  else if n = 4 then
    NonDetE.returnOk <| .capTableObject
  else if n = 5 then
    NonDetE.returnOk <| .schedContextObject
  else if n = 6 then
    NonDetE.returnOk <| .replyObject
  else (match archDataToObjType (n - 7) with
     | some tp => NonDetE.returnOk (.archObject tp)
     | none => NonDetE.throwError (.invalidArgument 0))

/-- l4v: Decode_A.decode_untyped_invocation: `Retype`. For SchedContext
objects the `user_obj_size` argument is the whole size. -/
def decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap)
    (excaps : List Cap) : SEMonad Z UntypedInvocation := do
  NonDetE.unlessE (genInvocationType label = .untypedRetype) <| NonDetE.throwError .illegalOperation
  NonDetE.whenE (args.length < 6) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (excaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let rootCap ← NonDetE.returnOk <| the excaps[0]?
  let newType ← dataToObjType (the args[0]?)

  let userObjSize ← NonDetE.returnOk <| dataToNat (the args[1]?)
  let objectSize ← NonDetE.returnOk (objBitsApi newType userObjSize)
  NonDetE.unlessE (userObjSize < wordBits ∧ objectSize ≤ untypedMaxBits) <|
    NonDetE.throwError (.rangeError 0 (BitVec.ofNat 64 untypedMaxBits))
  NonDetE.whenE (newType = .capTableObject ∧ userObjSize = 0) <|
    NonDetE.throwError (.invalidArgument 1)
  NonDetE.whenE (newType = .untyped ∧ userObjSize < untypedMinBits) <|
    NonDetE.throwError (.invalidArgument 1)
  NonDetE.whenE (newType = .schedContextObject ∧ userObjSize < minSchedContextBits) <|
    NonDetE.throwError (.invalidArgument 1)
  let nodeIndex ← NonDetE.returnOk <| dataToCptr (the args[2]?)
  let nodeDepth ← NonDetE.returnOk <| dataToNat (the args[3]?)

  let nodeCap ← (if nodeDepth = 0
        then NonDetE.returnOk rootCap
        else do
            let nodeSlot ← lookupTargetSlot
                rootCap nodeIndex nodeDepth
            NonDetE.liftE <| getCap nodeSlot : SEMonad Z Cap)

  if isCnodeCap nodeCap
        then NonDetE.returnOk ()
        else NonDetE.throwError <| .failedLookup false <| .missingCapability nodeDepth

  let nodeOffset ← NonDetE.returnOk <| dataToNat (the args[4]?)
  let nodeWindow ← NonDetE.returnOk <| dataToNat (the args[5]?)
  let radixBits ← NonDetE.returnOk <| bitsOf nodeCap
  let nodeSize ← NonDetE.returnOk (2 ^ radixBits)

  NonDetE.whenE (nodeOffset < 0 ∨ nodeOffset > nodeSize - 1) <|
    NonDetE.throwError <| .rangeError 0 (BitVec.ofNat 64 (nodeSize - 1))

  NonDetE.whenE (nodeWindow < 1 ∨ nodeWindow > unat retypeFanOutLimit) <|
    NonDetE.throwError <| .rangeError 1 retypeFanOutLimit

  NonDetE.whenE (nodeWindow < 1 ∨ nodeWindow > nodeSize - nodeOffset) <|
    NonDetE.throwError <| .rangeError 1 (BitVec.ofNat 64 (nodeSize - nodeOffset))

  let oref ← NonDetE.returnOk <| objRefOf nodeCap
  let offsets ← NonDetE.returnOk <| (List.range' nodeOffset
                           (nodeOffset + nodeWindow - nodeOffset)).map (natToCref radixBits)
  let slots ← NonDetE.returnOk <| offsets.map fun cref => (oref, cref)

  NonDetE.mapMEx ensureEmpty slots

  let reset ← NonDetE.liftE <| constOnFailure false <| (do
    ensureNoChildren slot
    NonDetE.returnOk true : SEMonad Z Bool)

  let freeIndex ← NonDetE.returnOk (if reset then 0 else freeIndexOf cap)
  let freeRef ← NonDetE.returnOk (getFreeRef (objRefOf cap) freeIndex)
  let alignedFreeRef ← NonDetE.returnOk (alignUp freeRef objectSize)
  let untypedFreeBytes ← NonDetE.returnOk (objSize cap - BitVec.ofNat 64 freeIndex)

  let maxCount ← NonDetE.returnOk (untypedFreeBytes >>> objectSize)
  NonDetE.whenE (unat maxCount < nodeWindow) <|
        NonDetE.throwError <| .notEnoughMemory <| untypedFreeBytes

  let notFrame ← NonDetE.returnOk (¬isFrameType newType)
  let (ptr, isDevice) ← match cap with
                        | .untypedCap dev p _n _f => NonDetE.returnOk (p, dev)
                        | _ => NonDetE.liftE NonDet.fail
  NonDetE.whenE (isDevice ∧ notFrame ∧ newType ≠ .untyped) <|
           NonDetE.throwError <| .invalidArgument 1
  NonDetE.returnOk <| .retype slot reset ptr alignedFreeRef newType userObjSize slots isDevice

/-! ## Decode_A: toplevel invocation decode -/

/-- l4v: Decode_A.decode_invocation: dispatch on the invoked cap. -/
def decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef)
    (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) :
    SEMonad Z Invocation :=
  match cap with
  | .endpointCap ptr badge rights =>
    if AllowSend ∈ rights then
      NonDetE.returnOk <| .invokeEndpoint ptr badge (decide (Rights.allowGrant ∈ rights))
        (decide (Rights.allowGrantReply ∈ rights))
    else NonDetE.throwError <| .invalidCapability 0
  | .notificationCap ptr badge rights =>
    if AllowSend ∈ rights then
      NonDetE.returnOk <| .invokeNotification ptr badge
    else NonDetE.throwError <| .invalidCapability 0
  | .replyCap reply rights =>
    NonDetE.returnOk <| .invokeReply reply (decide (Rights.allowGrant ∈ rights))
  | .irqControlCap =>
    NonDetE.liftME Invocation.invokeIRQControl
      <| decodeIrqControlInvocation label args slot (excaps.map Prod.fst)
  | .irqHandlerCap irq =>
    NonDetE.liftME Invocation.invokeIRQHandler
      <| decodeIrqHandlerInvocation label irq excaps
  | .threadCap _ptr =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Invocation.invokeTCB <| decodeTcbInvocation label args cap slot excaps
  | .domainCap =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Invocation.invokeDomain <| decodeDomainInvocation label args excaps
  | .schedContextCap sc _sz =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Invocation.invokeSchedContext <|
      decodeSchedContextInvocation label sc (excaps.map Prod.fst)
  | .schedControlCap =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Invocation.invokeSchedControl <|
      decodeSchedControlInvocationFlags label args (excaps.map Prod.fst)
  | .cnodeCap _ptr _bits _ =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Invocation.invokeCNode <|
      decodeCnodeInvocation label args cap (excaps.map Prod.fst)
  | .untypedCap _dev _ptr _sz _fi =>
    NonDetE.liftME Invocation.invokeUntyped <|
      decodeUntypedInvocation label args slot cap (excaps.map Prod.fst)
  | .archObjectCap archCap =>
    NonDetE.liftME Invocation.invokeArchObject <|
      archDecodeInvocation label args capIndex slot archCap excaps
  | _ =>
    NonDetE.throwError <| .invalidCapability 0

end

end

end Fl4Spec
