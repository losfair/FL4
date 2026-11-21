theorem fg_archActivateIdleThread (_t : ObjRef) : FGK Fq Sq Cq (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archActivateIdleThread _)

theorem fg_archCheckIrq (_irq : Data) : FGKE Fq Sq Cq (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archCheckIrq _)

theorem fg_getCap (a0 : CslotPtr) : FGK Fq Sq Cq (getCap (Z := Unit) a0) := by
  unfold getCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getCap _)

theorem fg_ensureEmpty (slot : CslotPtr) : FGKE Fq Sq Cq (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ensureEmpty _)

theorem fg_isIoportRangeFree (f l : IoPort) : FGK Fq Sq Cq (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isIoportRangeFree _ _)

theorem fg_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : FGKE Fq Sq Cq m) : FGKE Fq Sq Cq (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_lookupErrorOnFailure _ _ ?_)

theorem fg_resolveAddressBits' (p : Cap × CapRef) : FGKE Fq Sq Cq (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by fg_auto)) fun nc => ?_
        split
        · exact fg_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_resolveAddressBits' _)

theorem fg_resolveAddressBits (a0 : Cap × CapRef) : FGKE Fq Sq Cq (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_resolveAddressBits _)

theorem fg_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : FGKE Fq Sq Cq (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupSlotForCnodeOp _ _ _ _)

theorem fg_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FGKE Fq Sq Cq (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupTargetSlot _ _ _)

theorem fg_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : FGKE Fq Sq Cq (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIoportControlInvocation _ _ _ _ _)

theorem fg_getAsidPool (ptr : ObjRef) : FGK Fq Sq Cq (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getAsidPool _)

theorem fg_findVspaceForAsid (asid : Asid) : FGKE Fq Sq Cq (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_findVspaceForAsid _)

theorem fg_getPdpt (ptr : ObjRef) : FGK Fq Sq Cq (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPdpt _)

theorem fg_getPdpte (ptr : ObjRef) : FGK Fq Sq Cq (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPdpte _)

theorem fg_isFinalCap (cap : Cap) : FGK Fq Sq Cq (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isFinalCap _)

theorem fg_getPml4 (ptr : ObjRef) : FGK Fq Sq Cq (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPml4 _)

theorem fg_getPml4e (ptr : ObjRef) : FGK Fq Sq Cq (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPml4e _)

theorem fg_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : FGKE Fq Sq Cq (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupPdptSlot _ _)

theorem fg_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePageDirectoryInvocation _ _ _ _ _)

theorem fg_checkVpAlignment (sz : VMPageSize) (vptr : Word) : FGKE Fq Sq Cq (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkVpAlignment _ _)

theorem fg_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : FGKE Fq Sq Cq (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupPdSlot _ _)

theorem fg_getPd (ptr : ObjRef) : FGK Fq Sq Cq (getPd (Z := Unit) ptr) := by
  unfold getPd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPd _)

theorem fg_getPde (ptr : ObjRef) : FGK Fq Sq Cq (getPde (Z := Unit) ptr) := by
  unfold getPde; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPde _)

theorem fg_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : FGKE Fq Sq Cq (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupPtSlot _ _)

theorem fg_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : FGKE Fq Sq Cq (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_createMappingEntries _ _ _ _ _ _)

theorem fg_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : FGKE Fq Sq Cq (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ensureSafeMapping _)

theorem fg_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePageInvocation _ _ _ _ _)

theorem fg_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePageTableInvocation _ _ _ _ _)

theorem fg_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePdptInvocation _ _ _ _ _)

theorem fg_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : FGKE Fq Sq Cq (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ensurePortOperationAllowed _ _ _)

theorem fg_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : FGKE Fq Sq Cq (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePortInvocation _ _ _)

theorem fg_ensureNoChildren (cslotPtr : CslotPtr) : FGKE Fq Sq Cq (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ensureNoChildren _)

theorem fg_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : FGK Fq Sq Cq (selectExt (Z := Unit) a S) := by
  unfold selectExt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_selectExt _ _)

theorem fg_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archDecodeInvocation _ _ _ _ _ _)

theorem fg_getIrqState (irq : Irq) : FGK Fq Sq Cq (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getIrqState _)

theorem fg_isIrqActive (irq : Irq) : FGK Fq Sq Cq (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isIrqActive _)

theorem fg_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archDecodeIrqControlInvocation _ _ _ _)

theorem fg_archDeriveCap (c : ArchCap) : FGKE Fq Sq Cq (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archDeriveCap _)

theorem fg_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : FGK Fq Sq Cq (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_hwAsidInvalidate _ _)

theorem fg_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : FGK Fq Sq Cq (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setAsidPool _ _)

theorem fg_getCurrentCr3  : FGK Fq Sq Cq (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getCurrentCr3)

theorem fg_setCurrentCr3 (c : Cr3) : FGK Fq Sq Cq (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setCurrentCr3 _)

theorem fg_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : FGK Fq Sq Cq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setCurrentVspaceRoot _ _)

theorem fg_setVmRoot (tcb : ObjRef) : FGK Fq Sq Cq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setVmRoot _)

theorem fg_deleteAsid (asid : Asid) (pml4 : ObjRef) : FGK Fq Sq Cq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deleteAsid _ _)

theorem fg_deleteAsidPool (base : Asid) (ptr : ObjRef) : FGK Fq Sq Cq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deleteAsidPool _ _)

theorem fg_getPt (ptr : ObjRef) : FGK Fq Sq Cq (getPt (Z := Unit) ptr) := by
  unfold getPt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPt _)

theorem fg_getPte (ptr : ObjRef) : FGK Fq Sq Cq (getPte (Z := Unit) ptr) := by
  unfold getPte; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getPte _)

theorem fg_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : FGK Fq Sq Cq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setPd _ _)

theorem fg_storePde (p : ObjRef) (pde : PDE) : FGK Fq Sq Cq (storePde (Z := Unit) p pde) := by
  unfold storePde; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storePde _ _)

theorem fg_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : FGK Fq Sq Cq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setPdpt _ _)

theorem fg_storePdpte (p : ObjRef) (pte : PDPTE) : FGK Fq Sq Cq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storePdpte _ _)

theorem fg_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : FGK Fq Sq Cq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setPt _ _)

theorem fg_storePte (p : ObjRef) (pte : PTE) : FGK Fq Sq Cq (storePte (Z := Unit) p pte) := by
  unfold storePte; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storePte _ _)

theorem fg_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : FGK Fq Sq Cq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPage _ _ _ _)

theorem fg_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : FGK Fq Sq Cq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_flushTable _ _ _ _)

theorem fg_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : FGK Fq Sq Cq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invalidatePageStructureCacheAsid _ _)

theorem fg_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : FGK Fq Sq Cq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPageTable _ _ _)

theorem fg_flushAll (vspace : ObjRef) (asid : Asid) : FGK Fq Sq Cq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_flushAll _ _)

theorem fg_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : FGK Fq Sq Cq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPd _ _ _)

theorem fg_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : FGK Fq Sq Cq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setPml4 _ _)

theorem fg_storePml4e (p : ObjRef) (pte : PML4E) : FGK Fq Sq Cq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storePml4e _ _)

theorem fg_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : FGK Fq Sq Cq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPdpt _ _ _)

theorem fg_archFinaliseCap (c : ArchCap) (x : Bool) : FGK Fq Sq Cq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archFinaliseCap _ _)

theorem fg_archGetSanitiseRegisterInfo (_t : ObjRef) : FGK Fq Sq Cq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archGetSanitiseRegisterInfo _)

theorem fg_setOriginal (slot : CslotPtr) (v : Bool) : FGK Fq Sq Cq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setOriginal _ _)

theorem fg_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : FGK Fq Sq Cq (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setUntypedCapAsFull _ _ _)

theorem fg_setCdt (t : Cdt) : FGK Fq Sq Cq (setCdt (Z := Unit) t) := by
  unfold setCdt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setCdt _)

theorem fg_updateCdt (f : Cdt → Cdt) : FGK Fq Sq Cq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateCdt _)

theorem fg_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : FGK Fq Sq Cq (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capInsert _ _ _)

theorem fg_setIrqState (state : IrqState) (irq : Irq) : FGK Fq Sq Cq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setIrqState _ _)

theorem fg_updateIrqState (irq : Irq) (irqState : X64IRQState) : FGK Fq Sq Cq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateIrqState _ _)

theorem fg_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : FGK Fq Sq Cq m) : FGKE Fq Sq Cq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_withoutPreemption _ ?_)

theorem fg_archInvokeIrqControl (aic : ArchIrqControlInvocation) : FGKE Fq Sq Cq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archInvokeIrqControl _)

theorem fg_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : FGK Fq Sq Cq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archInvokeIrqHandler _)

theorem fg_archMaskIrqSignal (irq : Irq) : FGK Fq Sq Cq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archMaskIrqSignal _)

theorem fg_performAsidControlInvocation (iv : AsidControlInvocation) : FGK Fq Sq Cq (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performAsidControlInvocation _)

theorem fg_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : FGK Fq Sq Cq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storeAsidPoolEntry _ _ _)

theorem fg_performAsidPoolInvocation (iv : AsidPoolInvocation) : FGK Fq Sq Cq (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performAsidPoolInvocation _)

theorem fg_portIn (f : MachineMonad Data) : FGK Fq Sq Cq (portIn (Z := Unit) f) := by
  unfold portIn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_portIn _)

theorem fg_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : FGK Fq Sq Cq (portOut (Z := Unit) f w) := by
  unfold portOut; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_portOut _ _)

theorem fg_performIoPortInvocation (i : IoPortInvocation) : FGK Fq Sq Cq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performIoPortInvocation _)

theorem fg_setIoportMask (f l : IoPort) (val : Bool) : FGK Fq Sq Cq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setIoportMask _ _ _)

theorem fg_performIoportControlInvocation (i : IoPortControlInvocation) : FGK Fq Sq Cq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performIoportControlInvocation _)

theorem fg_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : FGK Fq Sq Cq (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageDirectoryInvocation _)

theorem fg_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : FGK Fq Sq Cq (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageInvocationUnmap _ _)

theorem fg_performPageInvocation (iv : PageInvocation) : FGK Fq Sq Cq (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageInvocation _)

theorem fg_performPageTableInvocation (iv : PageTableInvocation) : FGK Fq Sq Cq (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageTableInvocation _)

theorem fg_performPdptInvocation (iv : PdptInvocation) : FGK Fq Sq Cq (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPdptInvocation _)

theorem fg_archPerformInvocation (i : ArchInvocation) : FGKE Fq Sq Cq (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPerformInvocation _)

theorem fg_freeIoportRange (f l : IoPort) : FGK Fq Sq Cq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_freeIoportRange _ _)

theorem fg_archPostCapDeletion (ac : ArchCap) : FGK Fq Sq Cq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostCapDeletion _)

theorem fg_archPostModifyRegisters (cur t : ObjRef) : FGK Fq Sq Cq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostModifyRegisters _ _)

theorem fg_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : FGK Fq Sq Cq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostResetUntyped _ _)

theorem fg_loadFpuState (t : ObjRef) : FGK Fq Sq Cq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadFpuState _)

theorem fg_saveFpuState (t : ObjRef) : FGK Fq Sq Cq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_saveFpuState _)

theorem fg_setX64CurrentFpuOwner (newOwner : Option ObjRef) : FGK Fq Sq Cq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setX64CurrentFpuOwner _)

theorem fg_switchLocalFpuOwner (newOwner : Option ObjRef) : FGK Fq Sq Cq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchLocalFpuOwner _)

theorem fg_fpuRelease (threadPtr : ObjRef) : FGK Fq Sq Cq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fpuRelease _)

theorem fg_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : FGK Fq Sq Cq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadGet _ _)

theorem fg_lazyFpuRestore (threadPtr : ObjRef) : FGK Fq Sq Cq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lazyFpuRestore _)

theorem fg_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : FGK Fq Sq Cq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostSetFlags _ _)

theorem fg_archPrepareNextDomain  : FGK Fq Sq Cq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPrepareNextDomain)

theorem fg_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : FGK Fq Sq Cq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPrepareSetDomain _ _)

theorem fg_archSwitchToIdleThread  : FGK Fq Sq Cq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archSwitchToIdleThread)

theorem fg_archSwitchToThread (t : ObjRef) : FGK Fq Sq Cq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archSwitchToThread _)

theorem fg_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getTcbObjRef _ _)

theorem fg_getScRefillReady (scPtr : ObjRef) : FGK Fq Sq Cq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScRefillReady _)

theorem fg_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScRefillSufficient _ _)

theorem fg_setSchedulerAction (action : SchedulerAction) : FGK Fq Sq Cq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setSchedulerAction _)

theorem fg_getTcbQueue (d : Domain) (prio : Priority) : FGK Fq Sq Cq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getTcbQueue _ _)

theorem fg_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : FGK Fq Sq Cq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setTcbQueue _ _ _)

theorem fg_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : FGK Fq Sq Cq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbSchedAction _ _)

theorem fg_rescheduleRequired  : FGK Fq Sq Cq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_rescheduleRequired)

theorem fg_possibleSwitchTo (target : ObjRef) : FGK Fq Sq Cq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_possibleSwitchTo _)

theorem fg_tcbReleaseRemove (tcbPtr : ObjRef) : FGK Fq Sq Cq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseRemove _)

theorem fg_tcbReleaseDequeue  : FGK Fq Sq Cq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseDequeue)

theorem fg_awaken  : FGK Fq Sq Cq (awaken (Z := Unit)) := by
  unfold awaken; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_awaken)

theorem fg_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : FGK Fq Sq Cq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSimpleKo _ _)

theorem fg_bindNotification (tcbptr ntfnptr : ObjRef) : FGK Fq Sq Cq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_bindNotification _ _)

theorem fg_getSchedContext (ptr : ObjRef) : FGK Fq Sq Cq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSchedContext _)

theorem fg_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : FGK Fq Sq Cq (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateSchedContext _ _)

theorem fg_bindScReply (scPtr replyPtr : ObjRef) : FGK Fq Sq Cq (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_bindScReply _ _)

theorem fg_getBlockingObject (state : ThreadState) : FGK Fq Sq Cq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getBlockingObject _)

theorem fg_getThreadState (ref : ObjRef) : FGK Fq Sq Cq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getThreadState _)

theorem fg_setThreadStateAct (tcbPtr : ObjRef) : FGK Fq Sq Cq (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setThreadStateAct _)

theorem fg_replyUnlinkTcb (t r : ObjRef) : FGK Fq Sq Cq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyUnlinkTcb _ _)

theorem fg_tcbEpDequeue (tptr epPtr : ObjRef) : FGK Fq Sq Cq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbEpDequeue _ _)

theorem fg_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : FGK Fq Sq Cq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_blockedCancelIpc _ _ _)

theorem fg_cancelSignal (threadptr ntfnptr : ObjRef) : FGK Fq Sq Cq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_cancelSignal _ _)

theorem fg_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSkObjRef _ _ _)

theorem fg_replyRemoveTcb (tptr rptr : ObjRef) : FGK Fq Sq Cq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyRemoveTcb _ _)

theorem fg_cancelIpc (tptr : ObjRef) : FGK Fq Sq Cq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_cancelIpc _)

theorem fg_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : FGKE Fq Sq Cq m) : FGKE Fq Sq Cq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_capFaultOnFailure _ _ _ ?_)

theorem fg_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : FGK Fq Sq Cq (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capMove _ _ _)

theorem fg_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : FGK Fq Sq Cq (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capSwap _ _ _ _)

theorem fg_capSwapForDelete (slot1 slot2 : CslotPtr) : FGK Fq Sq Cq (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capSwapForDelete _ _)

theorem fg_captransferFromWords (ptr : Word) : FGK Fq Sq Cq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_captransferFromWords _)

theorem fg_getRefillHead (scPtr : ObjRef) : FGK Fq Sq Cq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefillHead _)

theorem fg_refillPopHead (scPtr : ObjRef) : FGK Fq Sq Cq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillPopHead _)

theorem fg_getRefills (scPtr : ObjRef) : FGK Fq Sq Cq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefills _)

theorem fg_refillSize (scPtr : ObjRef) : FGK Fq Sq Cq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillSize _)

theorem fg_refillSingle (scPtr : ObjRef) : FGK Fq Sq Cq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillSingle _)

theorem fg_getRefillTail (scPtr : ObjRef) : FGK Fq Sq Cq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefillTail _)

theorem fg_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : FGK Fq Sq Cq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillAddTail _ _)

theorem fg_refillFull (scPtr : ObjRef) : FGK Fq Sq Cq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillFull _)

theorem fg_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : FGK Fq Sq Cq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRefillTl _ _)

theorem fg_scheduleUsed (scPtr : ObjRef) (new : Refill) : FGK Fq Sq Cq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scheduleUsed _ _)

theorem fg_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : FGK Fq Sq Cq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRefillHd _ _)

theorem fg_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_chargeEntireHeadRefill _ _)

theorem fg_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : FGK Fq Sq Cq m) : FGK Fq Sq Cq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_checkCapAt _ _ _ ?_)

theorem fg_checkDomainTime  : FGK Fq Sq Cq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkDomainTime)

theorem fg_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : FGKE Fq Sq Cq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkHandlerEp _ _)

theorem fg_checkPrio (newPrio : Data) (authTcb : ObjRef) : FGKE Fq Sq Cq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkPrio _ _)

theorem fg_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : FGKE Fq Sq Cq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkValidIpcBuffer _ _)

theorem fg_getScActive (scPtr : ObjRef) : FGK Fq Sq Cq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScActive _)

theorem fg_isRoundRobin (scPtr : ObjRef) : FGK Fq Sq Cq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isRoundRobin _)

theorem fg_handleOverrun (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleOverrun _ _)

theorem fg_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : FGK Fq Sq Cq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_mergeNonoverlappingHeadRefill _)

theorem fg_headInsufficientLoop (scPtr : ObjRef) : FGK Fq Sq Cq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_headInsufficientLoop _)

theorem fg_refillBudgetCheck (usage : Ticks) : FGK Fq Sq Cq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillBudgetCheck _)

theorem fg_refillBudgetCheckRoundRobin (usage : Ticks) : FGK Fq Sq Cq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillBudgetCheckRoundRobin _)

theorem fg_commitTime  : FGK Fq Sq Cq (commitTime (Z := Unit)) := by
  unfold commitTime; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_commitTime)

theorem fg_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScObjRef _ _)

theorem fg_testReschedule (fromTptr : ObjRef) : FGK Fq Sq Cq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_testReschedule _)

theorem fg_schedContextDonate (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextDonate _ _)

theorem fg_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : FGK Fq Sq Cq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_orderedInsert _ _ _ _)

theorem fg_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : FGK Fq Sq Cq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_readyTimesAppend _ _)

theorem fg_tcbReleaseEnqueue (tcbPtr : ObjRef) : FGK Fq Sq Cq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseEnqueue _)

theorem fg_postpone (scPtr : ObjRef) : FGK Fq Sq Cq (postpone (Z := Unit) scPtr) := by
  unfold postpone; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_postpone _)

theorem fg_schedContextResume (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextResume _)

theorem fg_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : FGK Fq Sq Cq (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeDonateSc _ _)

theorem fg_mergeOverlappingRefills (scPtr : ObjRef) : FGK Fq Sq Cq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_mergeOverlappingRefills _)

theorem fg_refillHeadOverlappingLoop (scPtr : ObjRef) : FGK Fq Sq Cq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillHeadOverlappingLoop _)

theorem fg_refillUnblockCheck (scPtr : ObjRef) : FGK Fq Sq Cq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillUnblockCheck _)

theorem fg_completeSignal (ntfnptr tptr : ObjRef) : FGK Fq Sq Cq (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_completeSignal _ _)

theorem fg_schedContextCancelYieldTo (thread : ObjRef) : FGK Fq Sq Cq (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextCancelYieldTo _)

theorem fg_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : FGK Fq Sq Cq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupIpcBuffer _ _)

theorem fg_setMessageInfo (thread : ObjRef) (info : MessageInfo) : FGK Fq Sq Cq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setMessageInfo _ _)

theorem fg_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : FGK Fq Sq Cq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storeWordOffs _ _ _)

theorem fg_replyFromKernel (thread : ObjRef) (x : Data × List Data) : FGK Fq Sq Cq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyFromKernel _ _)

theorem fg_schedContextUpdateConsumed (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUpdateConsumed _)

theorem fg_setConsumed (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setConsumed _ _)

theorem fg_completeYieldTo (tcbPtr : ObjRef) : FGK Fq Sq Cq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_completeYieldTo _)

theorem fg_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : FGKE Fq Sq Cq m) : FGK Fq Sq Cq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_constOnFailure _ _ ?_)

theorem fg_copyGlobalMappings (newPm : ObjRef) : FGK Fq Sq Cq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_copyGlobalMappings _)

theorem fg_loadWordOffs (ptr : ObjRef) (offs : Nat) : FGK Fq Sq Cq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadWordOffs _ _)

theorem fg_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : FGK Fq Sq Cq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_copyMrs _ _ _ _ _)

theorem fg_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : FGK Fq Sq Cq (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_createCap _ _ _ _ _)

theorem fg_dataToObjType (type : Data) : FGKE Fq Sq Cq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_dataToObjType _)

theorem fg_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeBindNotification _ _)

theorem fg_deriveCap (slot : CslotPtr) (cap : Cap) : FGKE Fq Sq Cq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deriveCap _ _)

theorem fg_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FGKE Fq Sq Cq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupPivotSlot _ _ _)

theorem fg_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FGKE Fq Sq Cq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupSourceSlot _ _ _)

theorem fg_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeCnodeInvocation _ _ _ _)

theorem fg_slotCapLongRunningDelete (slot : CslotPtr) : FGK Fq Sq Cq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_slotCapLongRunningDelete _)

theorem fg_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeCvSpace _ _ _ _)

theorem fg_subframeNode (nodeCap : Cap) (index depth : Data) : FGKE Fq Sq Cq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_subframeNode _ _ _)

theorem fg_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDeriveSubframe _ _ _ _)

theorem fg_decodeDomainScheduleConfigure (args : List Data) : FGKE Fq Sq Cq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainScheduleConfigure _)

theorem fg_decodeDomainScheduleSetStart (args : List Data) : FGKE Fq Sq Cq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainScheduleSetStart _)

theorem fg_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainSet _ _)

theorem fg_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainInvocation _ _ _)

theorem fg_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : FGK Fq Sq Cq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4GetMr _ _ _)

theorem fg_fl4Arg (buf : Option ObjRef) (i : Nat) : FGKE Fq Sq Cq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4Arg _ _)

theorem fg_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4ConfigureSingleStepping _ _)

theorem fg_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4FpuTransfer _ _ _ _)

theorem fg_fl4CheckBpNum (bp : Data) : FGKE Fq Sq Cq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4CheckBpNum _)

theorem fg_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4GetBreakpoint _ _)

theorem fg_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, FGKE Fq Sq Cq (check x0)) : FGKE Fq Sq Cq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; fg_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem fg_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqControlRemapped _ _ _)

theorem fg_fl4ArchCheckIrq (irq : Data) : FGKE Fq Sq Cq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchCheckIrq _)

theorem fg_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4IrqControl _ _ _ _ _)

theorem fg_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetBreakpoint _ _)

theorem fg_decodeFl4SetFlags (args : List Data) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetFlags _ _)

theorem fg_decodeFl4SetTimer (args : List Data) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetTimer _ _)

theorem fg_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4UnsetBreakpoint _ _)

theorem fg_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : FGKE Fq Sq Cq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4TcbExt _ _ _ _ _)

theorem fg_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqControlInvocation _ _ _ _)

theorem fg_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqHandlerInvocation _ _ _)

theorem fg_getScReleased (scPtr : ObjRef) : FGK Fq Sq Cq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScReleased _)

theorem fg_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextBind _ _)

theorem fg_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextUnbindObject _ _)

theorem fg_decodeSchedContextYieldTo (scPtr : ObjRef) : FGKE Fq Sq Cq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextYieldTo _)

theorem fg_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextInvocation _ _ _)

theorem fg_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedControlInvocationFlags _ _ _)

theorem fg_rangeCheck (v minV maxV : Word) : FGKE Fq Sq Cq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_rangeCheck _ _ _)

theorem fg_decodeSetFlags (args : List Data) (cap : Cap) : FGKE Fq Sq Cq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetFlags _ _)

theorem fg_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetIpcBuffer _ _ _ _)

theorem fg_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetMcpriority _ _ _ _)

theorem fg_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetPriority _ _ _ _)

theorem fg_isBlocked (thread : ObjRef) : FGK Fq Sq Cq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isBlocked _)

theorem fg_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : FGKE Fq Sq Cq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUpdateSc _ _ _)

theorem fg_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetSchedParams _ _ _ _)

theorem fg_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetSpace _ _ _ _)

theorem fg_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetTimeoutEp _ _ _)

theorem fg_decodeSetTlsBase (args : List Data) (cap : Cap) : FGKE Fq Sq Cq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetTlsBase _ _)

theorem fg_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTcbConfigure _ _ _ _)

theorem fg_decodeUnbindNotification (cap : Cap) : FGKE Fq Sq Cq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem fg_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTcbInvocation _ _ _ _ _)

theorem fg_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUntypedInvocation _ _ _ _ _)

theorem fg_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : FGKE Fq Sq Cq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeInvocation _ _ _ _ _ _ _ _)

theorem fg_decodePml4Flush (cap : ArchCap) : FGKE Fq Sq Cq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePml4Flush _)

theorem fg_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : FGKE Fq Sq Cq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_frameMappingSlot _ _ _ _)

theorem fg_decodeTestAndClearAccessed (cap : ArchCap) : FGKE Fq Sq Cq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTestAndClearAccessed _)

theorem fg_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem fg_deletedIrqHandler (irq : Irq) : FGK Fq Sq Cq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deletedIrqHandler _)

theorem fg_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : FGK Fq Sq Cq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_makeArchFaultMsg _ _)

theorem fg_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : FGK Fq Sq Cq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_makeFaultMsg _ _)

theorem fg_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : FGK Fq Sq Cq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doFaultTransfer _ _ _ _)

theorem fg_getMessageInfo (thread : ObjRef) : FGK Fq Sq Cq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getMessageInfo _)

theorem fg_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : FGK Fq Sq Cq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; fg_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getExtraCptrs _ _)

theorem fg_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : FGKE Fq Sq Cq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupSlotForThread _ _)

theorem fg_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : FGKE Fq Sq Cq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupCapAndSlot _ _)

theorem fg_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : FGKE Fq Sq Cq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupExtraCaps _ _ _)

theorem fg_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : FGKE Fq Sq Cq m) : FGK Fq Sq Cq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_emptyOnFailure _ ?_)

theorem fg_loadCapTransfer (buffer : ObjRef) : FGK Fq Sq Cq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadCapTransfer _)

theorem fg_lookupCap (thread : ObjRef) (ref : CapRef) : FGKE Fq Sq Cq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupCap _ _)

theorem fg_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : FGKE Fq Sq Cq m) : FGKE Fq Sq Cq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_unifyFailure _ ?_)

theorem fg_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : FGK Fq Sq Cq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getReceiveSlots _ _)

theorem fg_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : FGK Fq Sq Cq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setExtraBadge _ _ _)

theorem fg_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      FGK Fq Sq Cq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; fg_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => fg_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | fg_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_transferCapsLoop _ _ _ _ _ _)

theorem fg_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : FGK Fq Sq Cq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_transferCaps _ _ _ _ _)

theorem fg_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : FGK Fq Sq Cq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doNormalTransfer _ _ _ _ _ _ _)

theorem fg_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : FGK Fq Sq Cq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doIpcTransfer _ _ _ _ _)

theorem fg_doNbrecvFailedTransfer (thread : ObjRef) : FGK Fq Sq Cq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doNbrecvFailedTransfer _)

theorem fg_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : FGK Fq Sq Cq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_domainScheduleConfigure _ _ _)

theorem fg_setNextInterrupt  : FGK Fq Sq Cq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setNextInterrupt)

theorem fg_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : FGK Fq Sq Cq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ifCondRefillUnblockCheck _ _ _)

theorem fg_switchSchedContext  : FGK Fq Sq Cq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchSchedContext)

theorem fg_scAndTimer  : FGK Fq Sq Cq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scAndTimer)

theorem fg_nextDomain  : FGK Fq Sq Cq (nextDomain (Z := Unit)) := by
  unfold nextDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_nextDomain)

theorem fg_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : FGK Fq Sq Cq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scheduleSwitchThreadFastfail _ _ _ _)

theorem fg_domainSetStart (index : Nat) : FGK Fq Sq Cq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_domainSetStart _)

theorem fg_postCapDeletion (cap : Cap) : FGK Fq Sq Cq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_postCapDeletion _)

theorem fg_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : FGK Fq Sq Cq (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_emptySlot _ _)

theorem fg_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem fg_performDeriveSubframe (iv : Fl4SubframeInvocation) : FGK Fq Sq Cq (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performDeriveSubframe _)

theorem fg_performPml4Flush (a0 : Fl4Pml4Invocation) : FGK Fq Sq Cq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPml4Flush _)

theorem fg_performTestAndClearAccessed (_slot : ObjRef) : FGK Fq Sq Cq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performTestAndClearAccessed _)

theorem fg_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : FGKE Fq Sq Cq (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchPerformInvocation _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem fg_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    FGKE Fq Sq Cq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem fg_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : FGKE Fq Sq Cq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem fg_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : FGK Fq Sq Cq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ReplyFromKernelError _ _ _)

theorem fg_fl4SyscallFaultIP (thread : ObjRef) : FGK Fq Sq Cq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4SyscallFaultIP _)

theorem fg_getCapReg (reg : Register) : FGK Fq Sq Cq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getCapReg _)

theorem fg_getIrqSlot (irq : Irq) : FGK Fq Sq Cq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getIrqSlot _)

theorem fg_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : FGK Fq Sq Cq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getMrs _ _ _)

theorem fg_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : FGK Fq Sq Cq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleArchFaultReply _ _ _ _)

theorem fg_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : FGK Fq Sq Cq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleFaultReply _ _ _ _)

theorem fg_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : FGK Fq Sq Cq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleHypervisorFault _ _)

theorem fg_handleNoFault (tptr : ObjRef) : FGK Fq Sq Cq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleNoFault _)

theorem fg_handleReservedIrq (_irq : Irq) : FGK Fq Sq Cq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleReservedIrq _)

theorem fg_handleSpuriousIrq  : FGK Fq Sq Cq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleSpuriousIrq)

theorem fg_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : FGKE Fq Sq Cq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleVmFault _ _)

theorem fg_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : FGK Fq Sq Cq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_initArchObjects _ _ _ _ _ _)

theorem fg_threadSetDomain (tptr : ObjRef) (domain : Domain) : FGK Fq Sq Cq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadSetDomain _ _)

theorem fg_setDomain (tptr : ObjRef) (newDom : Domain) : FGK Fq Sq Cq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setDomain _ _)

theorem fg_invokeSetDomain (thread : ObjRef) (domain : Domain) : FGK Fq Sq Cq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSetDomain _ _)

theorem fg_invokeDomain (domInv : DomainInvocation) : FGK Fq Sq Cq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeDomain _)

theorem fg_invokeIrqControl (a0 : IrqControlInvocation) : FGKE Fq Sq Cq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeIrqControl _)

theorem fg_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : FGKE Fq Sq Cq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeFl4IrqControl _)

theorem fg_invokeFl4Tcb (a0 : Fl4TcbInvocation) : FGKE Fq Sq Cq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeFl4Tcb _)

theorem fg_returnConsumed (scPtr : ObjRef) : FGK Fq Sq Cq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_returnConsumed _)

theorem fg_schedContextBindNtfn (sc ntfn : ObjRef) : FGK Fq Sq Cq (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextBindNtfn _ _)

theorem fg_schedContextBindTcb (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextBindTcb _ _)

theorem fg_schedContextUnbindTcb (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindTcb _)

theorem fg_schedContextUnbindAllTcbs (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindAllTcbs _)

theorem fg_schedContextUnbindNtfn (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindNtfn _)

theorem fg_schedContextUnbindReply (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindReply _)

theorem fg_schedContextYieldTo (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextYieldTo _)

theorem fg_invokeSchedContext (iv : SchedContextInvocation) : FGK Fq Sq Cq (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSchedContext _)

theorem fg_maybeAddEmptyTail (scPtr : ObjRef) : FGK Fq Sq Cq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeAddEmptyTail _)

theorem fg_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : FGK Fq Sq Cq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillNew _ _ _ _)

theorem fg_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : FGK Fq Sq Cq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillUpdate _ _ _ _)

theorem fg_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : FGK Fq Sq Cq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSchedControlConfigureFlags _)

theorem fg_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : FGKE Fq Sq Cq f) (h_g : FGKE Fq Sq Cq g) : FGKE Fq Sq Cq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; fg_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_orChoiceE _ _ _ ?_ ?_)

theorem fg_updateTimeStamp  : FGK Fq Sq Cq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateTimeStamp)

theorem fg_preemptionPoint  : FGKE Fq Sq Cq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_preemptionPoint)

theorem fg_resetUntypedCap (srcSlot : CslotPtr) : FGKE Fq Sq Cq (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_resetUntypedCap _)

theorem fg_invokeUntyped (ui : UntypedInvocation) : FGKE Fq Sq Cq (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeUntyped _)

theorem fg_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : FGKE Fq Sq Cq (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeUntypedWith _ _)

theorem fg_isValidTimeoutHandler (tptr : ObjRef) : FGK Fq Sq Cq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isValidTimeoutHandler _)

theorem fg_lookupReply  : FGKE Fq Sq Cq (lookupReply (Z := Unit)) := by
  unfold lookupReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupReply)

theorem fg_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeReturnSc _ _)

theorem fg_prepareThreadDelete (threadPtr : ObjRef) : FGK Fq Sq Cq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_prepareThreadDelete _)

theorem fg_refillResetRr (cscPtr : ObjRef) : FGK Fq Sq Cq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillResetRr _)

theorem fg_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : FGK Fq Sq Cq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbAppend _ _)

theorem fg_reorderEp (epPtr tptr : ObjRef) : FGK Fq Sq Cq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_reorderEp _ _)

theorem fg_replyUnlinkSc (scPtr replyPtr : ObjRef) : FGK Fq Sq Cq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyUnlinkSc _ _)

theorem fg_replyRemove (caller r : ObjRef) : FGK Fq Sq Cq (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyRemove _ _)

theorem fg_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : FGK Fq Sq Cq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextMaybeUnbindNtfn _)

theorem fg_schedContextSetInactive (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextSetInactive _)

theorem fg_schedContextUnbindYieldFrom (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindYieldFrom _)

theorem fg_setFlags (ref : ObjRef) (flags : TcbFlags) : FGK Fq Sq Cq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setFlags _ _)

theorem fg_setMcpriority (ref : ObjRef) (mcp : Priority) : FGK Fq Sq Cq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setMcpriority _ _)

theorem fg_updateRestartPc (threadPtr : ObjRef) : FGK Fq Sq Cq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRestartPc _)

theorem fg_suspend (thread : ObjRef) : FGK Fq Sq Cq (suspend (Z := Unit) thread) := by
  unfold suspend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_suspend _)

theorem fg_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : FGKE Fq Sq Cq mFault) (h_hFault : ∀ x0, FGK Fq Sq Cq (hFault x0)) (h_mError : ∀ x0, FGKE Fq Sq Cq (mError x0)) (h_hError : ∀ x0, FGK Fq Sq Cq (hError x0)) (h_mFinalise : ∀ x0, FGKE Fq Sq Cq (mFinalise x0)) : FGKE Fq Sq Cq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; fg_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem fg_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : FGK Fq Sq Cq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbEpAppend _ _ _)

theorem fg_testPossibleSwitchTo (tcbPtr : ObjRef) : FGK Fq Sq Cq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_testPossibleSwitchTo _)

theorem fg_threadSetPriority (tptr : ObjRef) (prio : Priority) : FGK Fq Sq Cq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadSetPriority _ _)

theorem fg_unbindFromSc (tcbPtr : ObjRef) : FGK Fq Sq Cq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindFromSc _)

theorem fg_unbindMaybeNotification (ntfnptr : ObjRef) : FGK Fq Sq Cq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindMaybeNotification _)

theorem fg_unbindNotification (tcb : ObjRef) : FGK Fq Sq Cq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindNotification _)
