/-
x86-64 FPU ownership, virtual address spaces, and arch cap predicates (MCS).

Ports, in theory order:
- `spec/abstract/X64/FPU_A`;
- `spec/abstract/X64/ArchVSpace_A`;
- `spec/abstract/X64/ArchCSpace_A`.

Omitted (no IOMMU): the IOSpace and IO page table cases that l4v comments
out (`FIXME x64-vtd`) in `arch_derive_cap`, `arch_finalise_cap` and
`arch_same_region_as`. The `msg_align_bits` lemma is not ported.
-/
import Fl4Spec.Retype

namespace Fl4Spec

open Classical

noncomputable section

/-! ## FPU_A -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: FPU_A.X64_A.save_fpu_state. -/
def saveFpuState (t : ObjRef) : SMonad Z Unit := do
  let fpuState ← doMachineOp readFpuState
  asUser t (setFPUState fpuState)

/-- l4v: FPU_A.X64_A.load_fpu_state. -/
def loadFpuState (t : ObjRef) : SMonad Z Unit := do
  let fpuState ← asUser t getFPUState
  doMachineOp (writeFpuState fpuState)

/-- l4v: FPU_A.X64_A.set_x64_current_fpu_owner. -/
def setX64CurrentFpuOwner (newOwner : Option ObjRef) : SMonad Z Unit := do
  let curFpuOwner ← NonDet.gets fun s : State Z => s.archState.x64CurrentFpuOwner
  NonDet.maybeM (archThreadSet fun t => { t with tcbCurFpu := false }) curFpuOwner
  NonDet.modify fun s => { s with archState := { s.archState with x64CurrentFpuOwner := newOwner } }
  NonDet.maybeM (archThreadSet fun t => { t with tcbCurFpu := true }) newOwner

/-- l4v: FPU_A.X64_A.switch_local_fpu_owner. -/
def switchLocalFpuOwner (newOwner : Option ObjRef) : SMonad Z Unit := do
  let curFpuOwner ← NonDet.gets fun s : State Z => s.archState.x64CurrentFpuOwner
  doMachineOp enableFpu
  NonDet.maybeM saveFpuState curFpuOwner
  match newOwner with
  | none => doMachineOp disableFpu
  | some tcbPtr => loadFpuState tcbPtr
  setX64CurrentFpuOwner newOwner

/-- l4v: FPU_A.X64_A.fpu_release. -/
def fpuRelease (threadPtr : ObjRef) : SMonad Z Unit := do
  let curFpuOwner ← NonDet.gets fun s : State Z => s.archState.x64CurrentFpuOwner
  NonDet.when (curFpuOwner = some threadPtr) <| switchLocalFpuOwner none

/-- l4v: FPU_A.X64_A.lazy_fpu_restore. -/
def lazyFpuRestore (threadPtr : ObjRef) : SMonad Z Unit := do
  let flags ← threadGet Tcb.tcbFlags threadPtr
  if TcbFlag.fpuDisabled ∈ flags
  then doMachineOp disableFpu
  else do
    let curFpuOwner ← NonDet.gets fun s : State Z => s.archState.x64CurrentFpuOwner
    if curFpuOwner = some threadPtr
    then doMachineOp enableFpu
    else switchLocalFpuOwner (some threadPtr)

end

/-! ## ArchVSpace_A -/

/-- l4v: ArchVSpace_A.X64_A.attr_mask: attributes always cleared when pages
are mapped. -/
def attrMask : VMAttributes := {.global, .dirty, .ptAttr .accessed, .ptAttr .executeDisable}

/-- l4v: ArchVSpace_A.X64_A.attr_mask'. -/
def attrMask' : VMAttributes := attrMask ∪ {.pat}

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpace_A.X64_A.create_mapping_entries: the entry that would be
inserted to map a frame of the given size at a virtual address, and its
slot. -/
def createMappingEntries (base : Paddr) (vptr : VSpaceRef) :
    VMPageSize → VMRights → VMAttributes → ObjRef → SEMonad Z (VMPageEntry × ObjRef)
  | .x64SmallPage, vmRights, attrib, pd => do
      let p ← lookupErrorOnFailure false (lookupPtSlot pd vptr)
      NonDetE.returnOk (.vmPTE (.smallPagePTE base (attrib \ attrMask) vmRights), p)
  | .x64LargePage, vmRights, attrib, pdpt => do
      let p ← lookupErrorOnFailure false (lookupPdSlot pdpt vptr)
      NonDetE.returnOk (.vmPDE (.largePagePDE base (attrib \ attrMask) vmRights), p)
  | .x64HugePage, vmRights, attrib, pml4 => do
      let p ← lookupErrorOnFailure false (lookupPdptSlot pml4 vptr)
      NonDetE.returnOk (.vmPDPTE (.hugePagePDPTE base (attrib \ attrMask') vmRights), p)

/-- l4v: ArchVSpace_A.X64_A.ensure_safe_mapping: the entries are invalid
(unmapping) or replace invalid entries (mapping). -/
def ensureSafeMapping : VMPageEntry × ObjRef → SEMonad Z Unit
  | (.vmPTE .invalidPTE, _) => NonDetE.returnOk ()
  | (.vmPDE .invalidPDE, _) => NonDetE.returnOk ()
  | (.vmPDPTE .invalidPDPTE, _) => NonDetE.returnOk ()
  | (.vmPTE (.smallPagePTE _ _ _), _) => NonDetE.returnOk ()
  | (.vmPDE (.largePagePDE _ _ _), pdSlot) => do
      let pde ← NonDetE.liftE (getPde pdSlot)
      match pde with
      | .invalidPDE => NonDetE.returnOk ()
      | .largePagePDE _ _ _ => NonDetE.returnOk ()
      | _ => NonDetE.throwError .deleteFirst
  | (.vmPDPTE (.hugePagePDPTE _ _ _), pdptSlot) => do
      let pdpt ← NonDetE.liftE (getPdpte pdptSlot)
      match pdpt with
      | .invalidPDPTE => NonDetE.returnOk ()
      | .hugePagePDPTE _ _ _ => NonDetE.returnOk ()
      | _ => NonDetE.throwError .deleteFirst
  | (.vmPDE (.pageTablePDE _ _ _), _) => NonDetE.liftE NonDet.fail
  | (.vmPDPTE (.pageDirectoryPDPTE _ _ _), _) => NonDetE.liftE NonDet.fail

/-- l4v: ArchVSpace_A.X64_A.lookup_ipc_buffer: a thread's IPC buffer, if the
thread may read it (or, as receiver, write it). rt X64 gap: X64 `rt` reads
the non-MCS slot `tcb_cnode_index 4` (after `tcb_reply`, `tcb_caller`); in the
MCS TCB (`tcb_cnode_map`) the IPC frame cap is at `tcb_cnode_index 2` and slot
4 is the timeout handler, so this uses 2, as RISCV64 `rt` `lookup_ipc_buffer`
does. -/
def lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : SMonad Z (Option ObjRef) := do
  let bufferPtr ← threadGet Tcb.tcbIpcBuffer thread
  let bufferFrameSlot ← pure (thread, tcbCnodeIndex 2)
  let bufferCap ← getCap bufferFrameSlot
  match bufferCap with
  | .archObjectCap (.pageCap _ p R _ vms _) =>
      if vmReadWrite ⊆ R ∨ vmReadOnly ⊆ R ∧ ¬isReceiver
      then return (some (p + (bufferPtr &&& mask (pageBitsForSize vms))))
      else return none
  | _ => return none

/-- ASID pools retain nested-root tags so guest allocations occupy their
slots. Native address-space operations select only untagged entries. -/
def nativeAsidRoot : Option ObjRef → Option ObjRef
  | none => none
  | some ptr => if ptr &&& 1 = 0 then some ptr else none

/-- Root pointer carried by an occupied native or nested ASID entry. -/
def asidEntryRoot (entry : ObjRef) : ObjRef := entry &&& ~~~1

/-- l4v: ArchVSpace_A.X64_A.find_vspace_for_asid: the PML4 of a virtual
ASID. -/
def findVspaceForAsid (asid : Asid) : LFMonad Z ObjRef := do
  NonDetE.assertE (asid > 0)
  let asidTable ← NonDetE.liftE (NonDet.gets fun s : State Z => s.archState.x64AsidTable)
  let poolPtr ← NonDetE.returnOk (asidTable (asidHighBitsOf asid))
  let pool ← match poolPtr with
    | some ptr => NonDetE.liftE (getAsidPool ptr)
    | none => NonDetE.throwError .invalidRoot
  let pml4 ← NonDetE.returnOk (nativeAsidRoot (pool (asidLowBitsOf asid)))
  match pml4 with
  | some ptr => NonDetE.returnOk ptr
  | none => NonDetE.throwError .invalidRoot

/-- l4v: ArchVSpace_A.X64_A.find_vspace_for_asid_assert: as
`find_vspace_for_asid`, failing unless it returns a real PML4. -/
def findVspaceForAsidAssert (asid : Asid) : SMonad Z ObjRef := do
  let pml4 ← NonDetE.catch (findVspaceForAsid asid) fun _ => NonDet.fail
  let _ ← getPml4 pml4
  return pml4

/-- l4v: ArchVSpace_A.X64_A.handle_vm_fault: the VM fault message for a
thread's supervisor. -/
def handleVmFault (thread : ObjRef) (faultType : VMFaultType) : FMonad Z Unit := do
  let addr ← NonDetE.liftE (doMachineOp getFaultAddress)
  let fault ← NonDetE.liftE (asUser thread (getRegister .errorRegister))
  match faultType with
  | .x64DataFault => NonDetE.throwError (.archFault (.vmFault addr [0, fault &&& mask 5]))
  | .x64InstructionFault => NonDetE.throwError (.archFault (.vmFault addr [1, fault &&& mask 5]))

/-- l4v: ArchVSpace_A.X64_A.get_current_cr3. -/
def getCurrentCr3 : SMonad Z Cr3 := NonDet.gets fun s : State Z => s.archState.x64CurrentCr3

/-- l4v: ArchVSpace_A.X64_A.set_current_cr3. -/
def setCurrentCr3 (c : Cr3) : SMonad Z Unit :=
  NonDet.modify fun s => { s with archState := { s.archState with x64CurrentCr3 := c } }

/-- l4v: ArchVSpace_A.X64_A.invalidate_page_structure_cache_asid. -/
def invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SMonad Z Unit :=
  doMachineOp (invalidateLocalPageStructureCacheASID vspace (ucast 64 asid))

/-- l4v: ArchVSpace_A.X64_A.getCurrentVSpaceRoot. -/
def getCurrentVSpaceRoot : SMonad Z ObjRef := do
  let cur ← getCurrentCr3
  return cr3BaseAddress cur

end

/-- l4v: ArchVSpace_A.X64_A.cr3_addr_mask. Above the 12-bit PCID field:
l4v writes `asid_bits`, which is 12 there but 20 in FL4. -/
def cr3AddrMask : Word := mask pml4ShiftBits <<< 12

/-- l4v: ArchVSpace_A.X64_A.make_cr3. -/
def makeCr3 (vspace : ObjRef) (asid : Asid) : Cr3 := .cr3 (vspace &&& cr3AddrMask) asid

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpace_A.X64_A.set_current_vspace_root. -/
def setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : SMonad Z Unit :=
  setCurrentCr3 (makeCr3 vspace asid)

/-- l4v: ArchVSpace_A.X64_A.set_vm_root: switch to the address space of a
thread, or to the global one if it has none correctly configured. -/
def setVmRoot (tcb : ObjRef) : SMonad Z Unit := do
  let threadRootSlot ← pure (tcb, tcbCnodeIndex 1)
  let threadRoot ← getCap threadRootSlot
  NonDetE.catch
    (match threadRoot with
     | .archObjectCap (.pml4Cap pml4 (some asid)) => do
         let pml4' ← findVspaceForAsid asid
         NonDetE.whenE (pml4 ≠ pml4') <| NonDetE.throwError .invalidRoot
         let curCr3 ← NonDetE.liftE getCurrentCr3
         NonDetE.whenE (curCr3 ≠ makeCr3 (addrFromPPtr pml4) asid) <|
           NonDetE.liftE <| setCurrentCr3 <| makeCr3 (addrFromPPtr pml4) asid
     | _ => NonDetE.throwError .invalidRoot)
    (fun _ => do
      let globalPml4 ← NonDet.gets fun s : State Z => s.archState.x64GlobalPml4
      setCurrentVspaceRoot (addrFromKPPtr globalPml4) 0)

/-- l4v: ArchVSpace_A.X64_A.hw_asid_invalidate: remove the mappings of a
virtual ASID. -/
def hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : SMonad Z Unit :=
  doMachineOp (invalidateASID vspace (ucast 64 asid))

/-- l4v: ArchVSpace_A.X64_A.delete_asid_pool. -/
def deleteAsidPool (base : Asid) (ptr : ObjRef) : SMonad Z Unit := do
  NonDet.assert (asidLowBitsOf base = 0)
  let asidTable ← NonDet.gets fun s : State Z => s.archState.x64AsidTable
  NonDet.when (asidTable (asidHighBitsOf base) = some ptr) <| do
    let pool ← getAsidPool ptr
    let _ ← NonDet.mapM (fun offset : Asid =>
        NonDet.when (nativeAsidRoot (pool (ucast asidLowLen offset)) ≠ none) <|
          hwAsidInvalidate (base + offset) (the (nativeAsidRoot (pool (ucast asidLowLen offset)))))
      (uptoEnum 0 (((1 : Asid) <<< asidLowBits) - 1))
    let asidTable' ← pure (Function.update asidTable (asidHighBitsOf base) none)
    NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }
    let tcb ← NonDet.gets fun s : State Z => s.curThread
    setVmRoot tcb

/-- l4v: ArchVSpace_A.X64_A.delete_asid: deactivate a PML4 when it is
deleted from an ASID pool. -/
def deleteAsid (asid : Asid) (pml4 : ObjRef) : SMonad Z Unit := do
  let asidTable ← NonDet.gets fun s : State Z => s.archState.x64AsidTable
  match asidTable (asidHighBitsOf asid) with
  | none => return ()
  | some poolPtr => do
    let pool ← getAsidPool poolPtr
    match pool (asidLowBitsOf asid) with
    | none => return ()
    | some entry =>
      NonDet.when (asidEntryRoot entry = pml4) <| do
        if entry &&& 1 = 0 then hwAsidInvalidate asid pml4 else pure ()
        let pool' ← pure (Function.update pool (asidLowBitsOf asid) none)
        setAsidPool poolPtr pool'
        if entry &&& 1 = 0 then do
          let tcb ← NonDet.gets fun s : State Z => s.curThread
          setVmRoot tcb
        else pure ()


/-- l4v: ArchVSpace_A.X64_A.flush_all. -/
def flushAll (vspace : ObjRef) (asid : Asid) : SMonad Z Unit :=
  doMachineOp (invalidateASID vspace (ucast 64 asid))

/-- l4v: ArchVSpace_A.X64_A.flush_pdpt (`abbreviation`). -/
abbrev flushPdpt : ObjRef → Asid → SMonad Z Unit := flushAll

/-- l4v: ArchVSpace_A.X64_A.flush_pd (`abbreviation`). -/
abbrev flushPd : ObjRef → Asid → SMonad Z Unit := flushAll

/-- l4v: ArchVSpace_A.X64_A.flush_table: flush the mappings of a page
table. -/
def flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) :
    SMonad Z Unit := do
  NonDet.assert (vptr &&& mask (ptTranslationBits + pageBits) = 0)
  let pt ← getPt ptRef
  NonDet.forMx (uptoEnum (0 : BitVec 9) (-1)) fun index => do
    let pte ← pure (pt index)
    match pte with
    | .invalidPTE => return ()
    | _ => doMachineOp <|
        invalidateTranslationSingleASID (vptr + (ucast 64 index <<< pageBits)) (ucast 64 asid)

/-- l4v: ArchVSpace_A.X64_A.unmap_pdpt: unmap a PDPT from a PML4. -/
def unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SMonad Z Unit :=
  NonDetE.catch (do
    let vspace ← findVspaceForAsid asid
    let pmSlot ← NonDetE.returnOk (lookupPml4Slot vspace vaddr)
    let pml4e ← NonDetE.liftE (getPml4e pmSlot)
    match pml4e with
    | .pdPointerTablePML4E pt' _ _ =>
        if pt' = addrFromPPtr pdpt then NonDetE.returnOk () else NonDetE.throwError .invalidRoot
    | _ => NonDetE.throwError .invalidRoot
    NonDetE.liftE (do
      flushPdpt vspace asid
      storePml4e pmSlot .invalidPML4E))
    (fun _ => return ())

/-- l4v: ArchVSpace_A.X64_A.unmap_pd: unmap a page directory from a PDPT. -/
def unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SMonad Z Unit :=
  NonDetE.catch (do
    let vspace ← findVspaceForAsid asid
    let pdptSlot ← lookupPdptSlot vspace vaddr
    let pdpte ← NonDetE.liftE (getPdpte pdptSlot)
    match pdpte with
    | .pageDirectoryPDPTE pd' _ _ =>
        if pd' = addrFromPPtr pd then NonDetE.returnOk () else NonDetE.throwError .invalidRoot
    | _ => NonDetE.throwError .invalidRoot
    NonDetE.liftE (do
      flushPd vspace asid
      storePdpte pdptSlot .invalidPDPTE
      invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid))
    (fun _ => return ())

/-- l4v: ArchVSpace_A.X64_A.unmap_page_table: unmap a page table from its
page directory. -/
def unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SMonad Z Unit :=
  NonDetE.catch (do
    let vspace ← findVspaceForAsid asid
    let pdSlot ← lookupPdSlot vspace vaddr
    let pde ← NonDetE.liftE (getPde pdSlot)
    match pde with
    | .pageTablePDE addr _ _ =>
        if addrFromPPtr pt = addr then NonDetE.returnOk () else NonDetE.throwError .invalidRoot
    | _ => NonDetE.throwError .invalidRoot
    NonDetE.liftE (do
      flushTable vspace vaddr pt asid
      storePde pdSlot .invalidPDE
      invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid))
    (fun _ => return ())

end

/-- l4v: ArchVSpace_A.X64_A.check_mapping_pptr: whether a frame is mapped by
an entry. -/
def checkMappingPptr (pptr : Word) (entry : VMPageEntry) : Bool :=
  match entry with
  | .vmPTE (.smallPagePTE base _ _) => decide (base = addrFromPPtr pptr)
  | .vmPDE (.largePagePDE base _ _) => decide (base = addrFromPPtr pptr)
  | .vmPDPTE (.hugePagePDPTE base _ _) => decide (base = addrFromPPtr pptr)
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpace_A.X64_A.unmap_page: unmap a page if the mapping details
are still current. -/
def unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SMonad Z Unit :=
  NonDetE.catch (do
    let vspace ← findVspaceForAsid asid
    match pgsz with
    | .x64SmallPage => do
        let ptSlot ← lookupPtSlot vspace vptr
        let pte ← NonDetE.liftE (getPte ptSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPTE pte)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePte ptSlot .invalidPTE)
    | .x64LargePage => do
        let pdSlot ← lookupPdSlot vspace vptr
        let pde ← NonDetE.liftE (getPde pdSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPDE pde)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePde pdSlot .invalidPDE)
    | .x64HugePage => do
        let pdptSlot ← lookupPdptSlot vspace vptr
        let pdpte ← NonDetE.liftE (getPdpte pdptSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPDPTE pdpte)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePdpte pdptSlot .invalidPDPTE)
    NonDetE.liftE (doMachineOp (invalidateTranslationSingleASID vptr (ucast 64 asid))))
    (fun _ => return ())

/-- l4v: ArchVSpace_A.X64_A.arch_derive_cap: page table structure caps cannot
be copied until they have a virtual ASID and location. The IOSpace and IO
page table cases are commented out in l4v (no IOMMU). -/
def archDeriveCap (c : ArchCap) : SEMonad Z Cap :=
  match c with
  | .vcpuCap _ => NonDetE.returnOk (.archObjectCap c)
  | .eptCap _ _ (some _) => NonDetE.returnOk (.archObjectCap c)
  | .eptCap _ _ none => NonDetE.throwError .illegalOperation
  | .pageTableCap _ (some _) => NonDetE.returnOk (.archObjectCap c)
  | .pageTableCap _ none => NonDetE.throwError .illegalOperation
  | .pageDirectoryCap _ (some _) => NonDetE.returnOk (.archObjectCap c)
  | .pageDirectoryCap _ none => NonDetE.throwError .illegalOperation
  | .pdPointerTableCap _ (some _) => NonDetE.returnOk (.archObjectCap c)
  | .pdPointerTableCap _ none => NonDetE.throwError .illegalOperation
  | .pml4Cap _ (some _) => NonDetE.returnOk (.archObjectCap c)
  | .pml4Cap _ none => NonDetE.throwError .illegalOperation
  | .pageCap dev r R _ pgs _ => NonDetE.returnOk (.archObjectCap (.pageCap dev r R .vmNoMap pgs none))
  | .asidControlCap => NonDetE.returnOk (.archObjectCap c)
  | .asidPoolCap _ _ => NonDetE.returnOk (.archObjectCap c)
  | .ioPortCap _ _ => NonDetE.returnOk (.archObjectCap c)
  | .ioPortControlCap => NonDetE.returnOk .nullCap

end

/-- l4v: ArchVSpace_A.X64_A.arch_update_cap_data: x64 caps hold no
user-modifiable data. -/
def archUpdateCapData (_preserve : Bool) (_data : Data) (c : ArchCap) : Cap := .archObjectCap c

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpace_A.X64_A.arch_finalise_cap: actions on finalisation of
x64 caps. The IOSpace and IO page table cases are a `FIXME x64-vtd` in l4v
(no IOMMU). -/
def archFinaliseCap (c : ArchCap) (x : Bool) : SMonad Z (Cap × Cap) :=
  match c, x with
  | .asidPoolCap ptr b, true => do
      deleteAsidPool b ptr
      return (.nullCap, .nullCap)
  | .pml4Cap ptr (some a), true => do
      deleteAsid a ptr
      return (.nullCap, .nullCap)
  | .pdPointerTableCap ptr (some (a, v)), true => do
      unmapPdpt a v ptr
      return (.nullCap, .nullCap)
  | .pageDirectoryCap ptr (some (a, v)), true => do
      unmapPd a v ptr
      return (.nullCap, .nullCap)
  | .pageTableCap ptr (some (a, v)), true => do
      unmapPageTable a v ptr
      return (.nullCap, .nullCap)
  | .pageCap _ ptr _ _ s (some (a, v)), _ => do
      unmapPage s a v ptr
      return (.nullCap, .nullCap)
  | .ioPortCap f l, true => return (.nullCap, .archObjectCap (.ioPortCap f l))
  | _, _ => return (.nullCap, .nullCap)

end

/-- l4v: ArchVSpace_A.X64_A.is_valid_vtable_root: a thread's address space
cap must be to a mapped PML4. -/
def isValidVtableRoot (c : Cap) : Prop := ∃ r a, c = .archObjectCap (.pml4Cap r (some a))

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpace_A.X64_A.check_valid_ipc_buffer. -/
def checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : SEMonad Z Unit :=
  match c with
  | .archObjectCap (.pageCap false _ _ _ _ _) => do
      NonDetE.whenE (¬isAligned vptr msgAlignBits) <| NonDetE.throwError .alignmentError
      NonDetE.returnOk ()
  | _ => NonDetE.throwError .illegalOperation

end

/-- l4v: ArchVSpace_A.X64_A.update_map_data: update the mapping data of a
page or page table cap (`nonexhaustive` case). -/
def updateMapData (cap : ArchCap) (m : Option (Asid × VSpaceRef)) (mt : Option VMMapType) : ArchCap :=
  match cap with
  | .pageCap dev p R _ sz _ => .pageCap dev p R (the mt) sz m
  | .pageTableCap p _ => .pageTableCap p m
  | .pageDirectoryCap p _ => .pageDirectoryCap p m
  | .pdPointerTableCap p _ => .pdPointerTableCap p m
  | _ => undefined

/-- l4v: ArchVSpace_A.X64_A.in_user_frame: the top bits of a pointer point to
a `DataPage`. -/
def inUserFrame {Z : Type} (p : ObjRef) (s : State Z) : Prop :=
  ∃ sz, s.kheap (p &&& ~~~(mask (pageBitsForSize sz))) = some (.archObj (.dataPage false sz))

/-- l4v: ArchVSpace_A.X64_A.prepare_thread_delete. -/
def prepareThreadDelete {Z : Type} [StateExt Z] (threadPtr : ObjRef) : SMonad Z Unit :=
  fpuRelease threadPtr

/-! ## ArchCSpace_A -/

/-- l4v: ArchCSpace_A.X64_A.cnode_guard_size_bits. -/
def cnodeGuardSizeBits : Nat := 6

/-- l4v: ArchCSpace_A.X64_A.cnode_padding_bits. -/
def cnodePaddingBits : Nat := 0

/-- l4v: ArchCSpace_A.X64_A.update_cnode_cap_data: the new guard size and
guard of a user request to modify a cnode cap. -/
def updateCnodeCapData (w : Data) : Nat × Data :=
  let guardBits := 58
  let guardSize' := unat ((w >>> cnodePaddingBits) &&& mask cnodeGuardSizeBits)
  let guard'' := (w >>> (cnodePaddingBits + cnodeGuardSizeBits)) &&& mask guardBits
  (guardSize', guard'')

/-- l4v: ArchCSpace_A.X64_A.arch_is_physical: whether the cap is to a
physical object. -/
def archIsPhysical (cap : ArchCap) : Bool :=
  match cap with
  | .asidControlCap => false
  | .ioPortCap _ _ => false
  | .ioPortControlCap => false
  | _ => true

/-- l4v: ArchCSpace_A.X64_A.arch_same_region_as: whether the second cap is to
the same object as, or an object inside the region of, the first. The IO
page table and IOSpace cases are commented out in l4v (no IOMMU). -/
def archSameRegionAs : ArchCap → ArchCap → Prop
  | .vcpuCap r, c' => ∃ r', c' = .vcpuCap r' ∧ r = r'
  | .eptCap r level _, c' => ∃ r' m', c' = .eptCap r' level m' ∧ r = r'
  | .pageCap _ r _ _ s _, c' =>
      ∃ dev' r' R' t' s' m', c' = .pageCap dev' r' R' t' s' m' ∧
        (let topA := r + ((1 : Word) <<< pageBitsForSize s) - 1
         let topB := r' + ((1 : Word) <<< pageBitsForSize s') - 1
         r ≤ r' ∧ topA ≥ topB ∧ r' ≤ topB)
  | .pageTableCap r _, c' => ∃ r' d', c' = .pageTableCap r' d' ∧ r = r'
  | .pageDirectoryCap r _, c' => ∃ r' d', c' = .pageDirectoryCap r' d' ∧ r = r'
  | .pdPointerTableCap r _, c' => ∃ r' d', c' = .pdPointerTableCap r' d' ∧ r = r'
  | .pml4Cap r _, c' => ∃ r' d', c' = .pml4Cap r' d' ∧ r = r'
  | .asidControlCap, c' => c' = .asidControlCap
  | .asidPoolCap r _, c' => ∃ r' d', c' = .asidPoolCap r' d' ∧ r = r'
  | .ioPortCap frst lst, c' => ∃ frst' lst', c' = .ioPortCap frst' lst' ∧ frst' = frst ∧ lst' = lst
  | .ioPortControlCap, c' => c' = .ioPortControlCap ∨ ∃ f l, c' = .ioPortCap f l

/-- l4v: ArchCSpace_A.X64_A.is_irq_control_descendant. -/
def isIrqControlDescendant (_acap : ArchCap) : Bool := false

/-- l4v: ArchCSpace_A.X64_A.same_aobject_as: whether two arch caps are to the
same object. -/
def sameAobjectAs (cp cp' : ArchCap) : Prop :=
  match cp, cp' with
  | .pageCap dev ref _ _ pgsz _, .pageCap dev' ref' _ _ pgsz' _ =>
      (dev, ref, pgsz) = (dev', ref', pgsz') ∧ ref ≤ ref + 2 ^ pageBitsForSize pgsz - 1
  | .ioPortControlCap, .ioPortCap _ _ => False
  | _, _ => archSameRegionAs cp cp'

/-- l4v: ArchCSpace_A.X64_A.arch_is_cap_revocable. -/
def archIsCapRevocable (newCap srcCap : Cap) : Prop :=
  if ∃ f l, newCap = .archObjectCap (.ioPortCap f l)
  then srcCap = .archObjectCap .ioPortControlCap
  else False

/-- l4v: ArchCSpace_A.X64_A.should_be_arch_parent_of. -/
def shouldBeArchParentOf (_acap _acap' : ArchCap) (_original' : Bool) : Prop := True

end

end Fl4Spec
