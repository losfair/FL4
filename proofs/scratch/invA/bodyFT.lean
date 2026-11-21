theorem ft_archActivateIdleThread (_t : ObjRef) : FTK L (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archActivateIdleThread _)

theorem ft_archCheckIrq (_irq : Data) : FTKE L (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archCheckIrq _)

theorem ft_getCap (a0 : CslotPtr) : FTK L (getCap (Z := Unit) a0) := by
  unfold getCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCap _)

theorem ft_ensureEmpty (slot : CslotPtr) : FTKE L (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureEmpty _)

theorem ft_isIoportRangeFree (f l : IoPort) : FTK L (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isIoportRangeFree _ _)

theorem ft_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : FTKE L m) : FTKE L (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_lookupErrorOnFailure _ _ ?_)

theorem ft_resolveAddressBits' (p : Cap × CapRef) : FTKE L (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ft_auto)) fun nc => ?_
        split
        · exact ft_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resolveAddressBits' _)

theorem ft_resolveAddressBits (a0 : Cap × CapRef) : FTKE L (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resolveAddressBits _)

theorem ft_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : FTKE L (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSlotForCnodeOp _ _ _ _)

theorem ft_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupTargetSlot _ _ _)

theorem ft_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : FTKE L (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIoportControlInvocation _ _ _ _ _)

theorem ft_getAsidPool (ptr : ObjRef) : FTK L (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getAsidPool _)

theorem ft_findVspaceForAsid (asid : Asid) : FTKE L (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_findVspaceForAsid _)

theorem ft_getPdpt (ptr : ObjRef) : FTK L (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPdpt _)

theorem ft_getPdpte (ptr : ObjRef) : FTK L (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPdpte _)

theorem ft_isFinalCap (cap : Cap) : FTK L (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isFinalCap _)

theorem ft_getPml4 (ptr : ObjRef) : FTK L (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPml4 _)

theorem ft_getPml4e (ptr : ObjRef) : FTK L (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPml4e _)

theorem ft_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPdptSlot _ _)

theorem ft_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageDirectoryInvocation _ _ _ _ _)

theorem ft_checkVpAlignment (sz : VMPageSize) (vptr : Word) : FTKE L (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkVpAlignment _ _)

theorem ft_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPdSlot _ _)

theorem ft_getPd (ptr : ObjRef) : FTK L (getPd (Z := Unit) ptr) := by
  unfold getPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPd _)

theorem ft_getPde (ptr : ObjRef) : FTK L (getPde (Z := Unit) ptr) := by
  unfold getPde; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPde _)

theorem ft_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPtSlot _ _)

theorem ft_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : FTKE L (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_createMappingEntries _ _ _ _ _ _)

theorem ft_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : FTKE L (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureSafeMapping _)

theorem ft_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageInvocation _ _ _ _ _)

theorem ft_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageTableInvocation _ _ _ _ _)

theorem ft_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePdptInvocation _ _ _ _ _)

theorem ft_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : FTKE L (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensurePortOperationAllowed _ _ _)

theorem ft_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : FTKE L (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePortInvocation _ _ _)

theorem ft_ensureNoChildren (cslotPtr : CslotPtr) : FTKE L (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureNoChildren _)

theorem ft_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : FTK L (selectExt (Z := Unit) a S) := by
  unfold selectExt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_selectExt _ _)

theorem ft_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDecodeInvocation _ _ _ _ _ _)

theorem ft_getIrqState (irq : Irq) : FTK L (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getIrqState _)

theorem ft_isIrqActive (irq : Irq) : FTK L (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isIrqActive _)

theorem ft_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDecodeIrqControlInvocation _ _ _ _)

theorem ft_archDeriveCap (c : ArchCap) : FTKE L (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDeriveCap _)

theorem ft_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : FTK L (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_hwAsidInvalidate _ _)

theorem ft_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : FTK L (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setAsidPool _ _)

theorem ft_getCurrentCr3  : FTK L (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCurrentCr3)

theorem ft_setCurrentCr3 (c : Cr3) : FTK L (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCurrentCr3 _)

theorem ft_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : FTK L (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCurrentVspaceRoot _ _)

theorem ft_setVmRoot (tcb : ObjRef) : FTK L (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setVmRoot _)

theorem ft_deleteAsid (asid : Asid) (pml4 : ObjRef) : FTK L (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deleteAsid _ _)

theorem ft_deleteAsidPool (base : Asid) (ptr : ObjRef) : FTK L (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deleteAsidPool _ _)

theorem ft_getPt (ptr : ObjRef) : FTK L (getPt (Z := Unit) ptr) := by
  unfold getPt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPt _)

theorem ft_getPte (ptr : ObjRef) : FTK L (getPte (Z := Unit) ptr) := by
  unfold getPte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPte _)

theorem ft_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : FTK L (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPd _ _)

theorem ft_storePde (p : ObjRef) (pde : PDE) : FTK L (storePde (Z := Unit) p pde) := by
  unfold storePde; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePde _ _)

theorem ft_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : FTK L (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPdpt _ _)

theorem ft_storePdpte (p : ObjRef) (pte : PDPTE) : FTK L (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePdpte _ _)

theorem ft_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : FTK L (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPt _ _)

theorem ft_storePte (p : ObjRef) (pte : PTE) : FTK L (storePte (Z := Unit) p pte) := by
  unfold storePte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePte _ _)

theorem ft_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : FTK L (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPage _ _ _ _)

theorem ft_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : FTK L (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_flushTable _ _ _ _)

theorem ft_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : FTK L (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invalidatePageStructureCacheAsid _ _)

theorem ft_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : FTK L (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPageTable _ _ _)

theorem ft_flushAll (vspace : ObjRef) (asid : Asid) : FTK L (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_flushAll _ _)

theorem ft_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : FTK L (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPd _ _ _)

theorem ft_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : FTK L (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPml4 _ _)

theorem ft_storePml4e (p : ObjRef) (pte : PML4E) : FTK L (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePml4e _ _)

theorem ft_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : FTK L (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPdpt _ _ _)

theorem ft_archFinaliseCap (c : ArchCap) (x : Bool) : FTK L (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archFinaliseCap _ _)

theorem ft_archGetSanitiseRegisterInfo (_t : ObjRef) : FTK L (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archGetSanitiseRegisterInfo _)

theorem ft_setOriginal (slot : CslotPtr) (v : Bool) : FTK L (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setOriginal _ _)

theorem ft_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : FTK L (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setUntypedCapAsFull _ _ _)

theorem ft_setCdt (t : Cdt) : FTK L (setCdt (Z := Unit) t) := by
  unfold setCdt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCdt _)

theorem ft_updateCdt (f : Cdt → Cdt) : FTK L (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateCdt _)

theorem ft_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : FTK L (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capInsert _ _ _)

theorem ft_setIrqState (state : IrqState) (irq : Irq) : FTK L (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setIrqState _ _)

theorem ft_updateIrqState (irq : Irq) (irqState : X64IRQState) : FTK L (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateIrqState _ _)

theorem ft_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : FTK L m) : FTKE L (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_withoutPreemption _ ?_)

theorem ft_archInvokeIrqControl (aic : ArchIrqControlInvocation) : FTKE L (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archInvokeIrqControl _)

theorem ft_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : FTK L (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archInvokeIrqHandler _)

theorem ft_archMaskIrqSignal (irq : Irq) : FTK L (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archMaskIrqSignal _)

theorem ft_performAsidControlInvocation (iv : AsidControlInvocation) : FTK L (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performAsidControlInvocation _)

theorem ft_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : FTK L (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storeAsidPoolEntry _ _ _)

theorem ft_performAsidPoolInvocation (iv : AsidPoolInvocation) : FTK L (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performAsidPoolInvocation _)

theorem ft_portIn (f : MachineMonad Data) : FTK L (portIn (Z := Unit) f) := by
  unfold portIn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_portIn _)

theorem ft_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : FTK L (portOut (Z := Unit) f w) := by
  unfold portOut; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_portOut _ _)

theorem ft_performIoPortInvocation (i : IoPortInvocation) : FTK L (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performIoPortInvocation _)

theorem ft_setIoportMask (f l : IoPort) (val : Bool) : FTK L (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setIoportMask _ _ _)

theorem ft_performIoportControlInvocation (i : IoPortControlInvocation) : FTK L (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performIoportControlInvocation _)

theorem ft_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : FTK L (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageDirectoryInvocation _)

theorem ft_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : FTK L (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageInvocationUnmap _ _)

theorem ft_performPageInvocation (iv : PageInvocation) : FTK L (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageInvocation _)

theorem ft_performPageTableInvocation (iv : PageTableInvocation) : FTK L (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageTableInvocation _)

theorem ft_performPdptInvocation (iv : PdptInvocation) : FTK L (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPdptInvocation _)

theorem ft_archPerformInvocation (i : ArchInvocation) : FTKE L (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPerformInvocation _)

theorem ft_freeIoportRange (f l : IoPort) : FTK L (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_freeIoportRange _ _)

theorem ft_archPostCapDeletion (ac : ArchCap) : FTK L (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostCapDeletion _)

theorem ft_archPostModifyRegisters (cur t : ObjRef) : FTK L (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostModifyRegisters _ _)

theorem ft_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : FTK L (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostResetUntyped _ _)

theorem ft_loadFpuState (t : ObjRef) : FTK L (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadFpuState _)

theorem ft_saveFpuState (t : ObjRef) : FTK L (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_saveFpuState _)

theorem ft_setX64CurrentFpuOwner (newOwner : Option ObjRef) : FTK L (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setX64CurrentFpuOwner _)

theorem ft_switchLocalFpuOwner (newOwner : Option ObjRef) : FTK L (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchLocalFpuOwner _)

theorem ft_fpuRelease (threadPtr : ObjRef) : FTK L (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fpuRelease _)

theorem ft_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : FTK L (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadGet _ _)

theorem ft_lazyFpuRestore (threadPtr : ObjRef) : FTK L (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lazyFpuRestore _)

theorem ft_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : FTK L (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostSetFlags _ _)

theorem ft_archPrepareNextDomain  : FTK L (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPrepareNextDomain)

theorem ft_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : FTK L (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPrepareSetDomain _ _)

theorem ft_archSwitchToIdleThread  : FTK L (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archSwitchToIdleThread)

theorem ft_archSwitchToThread (t : ObjRef) : FTK L (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archSwitchToThread _)

theorem ft_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : FTK L (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getTcbObjRef _ _)

theorem ft_getScRefillReady (scPtr : ObjRef) : FTK L (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScRefillReady _)

theorem ft_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : FTK L (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScRefillSufficient _ _)

theorem ft_setSchedulerAction (action : SchedulerAction) : FTK L (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setSchedulerAction _)

theorem ft_getTcbQueue (d : Domain) (prio : Priority) : FTK L (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getTcbQueue _ _)

theorem ft_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : FTK L (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setTcbQueue _ _ _)

theorem ft_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : FTK L (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbSchedAction _ _)

theorem ft_rescheduleRequired  : FTK L (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_rescheduleRequired)

theorem ft_possibleSwitchTo (target : ObjRef) : FTK L (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_possibleSwitchTo _)

theorem ft_tcbReleaseRemove (tcbPtr : ObjRef) : FTK L (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseRemove _)

theorem ft_tcbReleaseDequeue  : FTK L (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseDequeue)

theorem ft_awaken  : FTK L (awaken (Z := Unit)) := by
  unfold awaken; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_awaken)

theorem ft_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : FTK L (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSimpleKo _ _)

theorem ft_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : FTK L (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateSkObjRef _ _ _ _)

theorem ft_bindNotification (tcbptr ntfnptr : ObjRef) : FTK L (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_bindNotification _ _)

theorem ft_getSchedContext (ptr : ObjRef) : FTK L (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSchedContext _)

theorem ft_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : FTK L (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateSchedContext _ _)

theorem ft_bindScReply (scPtr replyPtr : ObjRef) : FTK L (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_bindScReply _ _)

theorem ft_getBlockingObject (state : ThreadState) : FTK L (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getBlockingObject _)

theorem ft_getThreadState (ref : ObjRef) : FTK L (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getThreadState _)

theorem ft_setThreadStateAct (tcbPtr : ObjRef) : FTK L (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setThreadStateAct _)

theorem ft_replyUnlinkTcb (t r : ObjRef) : FTK L (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyUnlinkTcb _ _)

theorem ft_tcbEpDequeue (tptr epPtr : ObjRef) : FTK L (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbEpDequeue _ _)

theorem ft_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : FTK L (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_blockedCancelIpc _ _ _)

theorem ft_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : FTK L (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbNtfnDequeue _ _)

theorem ft_cancelSignal (threadptr ntfnptr : ObjRef) : FTK L (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_cancelSignal _ _)

theorem ft_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : FTK L (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSkObjRef _ _ _)

theorem ft_replyRemoveTcb (tptr rptr : ObjRef) : FTK L (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyRemoveTcb _ _)

theorem ft_cancelIpc (tptr : ObjRef) : FTK L (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_cancelIpc _)

theorem ft_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : FTKE L m) : FTKE L (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_capFaultOnFailure _ _ _ ?_)

theorem ft_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : FTK L (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capMove _ _ _)

theorem ft_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : FTK L (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capSwap _ _ _ _)

theorem ft_capSwapForDelete (slot1 slot2 : CslotPtr) : FTK L (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capSwapForDelete _ _)

theorem ft_captransferFromWords (ptr : Word) : FTK L (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_captransferFromWords _)

theorem ft_getRefillHead (scPtr : ObjRef) : FTK L (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefillHead _)

theorem ft_refillPopHead (scPtr : ObjRef) : FTK L (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillPopHead _)

theorem ft_getRefills (scPtr : ObjRef) : FTK L (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefills _)

theorem ft_refillSize (scPtr : ObjRef) : FTK L (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillSize _)

theorem ft_refillSingle (scPtr : ObjRef) : FTK L (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillSingle _)

theorem ft_getRefillTail (scPtr : ObjRef) : FTK L (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefillTail _)

theorem ft_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : FTK L (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillAddTail _ _)

theorem ft_refillFull (scPtr : ObjRef) : FTK L (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillFull _)

theorem ft_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : FTK L (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRefillTl _ _)

theorem ft_scheduleUsed (scPtr : ObjRef) (new : Refill) : FTK L (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleUsed _ _)

theorem ft_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : FTK L (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRefillHd _ _)

theorem ft_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : FTK L (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_chargeEntireHeadRefill _ _)

theorem ft_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : FTK L m) : FTK L (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_checkCapAt _ _ _ ?_)

theorem ft_checkDomainTime  : FTK L (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkDomainTime)

theorem ft_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : FTKE L (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkHandlerEp _ _)

theorem ft_checkPrio (newPrio : Data) (authTcb : ObjRef) : FTKE L (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkPrio _ _)

theorem ft_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : FTKE L (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkValidIpcBuffer _ _)

theorem ft_nextDomain  : FTK L (nextDomain (Z := Unit)) := by
  unfold nextDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_nextDomain)

theorem ft_switchToThread (t : ObjRef) : FTK L (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchToThread _)

theorem ft_guardedSwitchTo (thread : ObjRef) : FTK L (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_guardedSwitchTo _)

theorem ft_switchToIdleThread  : FTK L (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchToIdleThread)

theorem ft_chooseThread  : FTK L (chooseThread (Z := Unit)) := by
  unfold chooseThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_chooseThread)

theorem ft_getScActive (scPtr : ObjRef) : FTK L (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScActive _)

theorem ft_isRoundRobin (scPtr : ObjRef) : FTK L (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isRoundRobin _)

theorem ft_handleOverrun (scPtr : ObjRef) (usage : Ticks) : FTK L (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleOverrun _ _)

theorem ft_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : FTK L (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_mergeNonoverlappingHeadRefill _)

theorem ft_headInsufficientLoop (scPtr : ObjRef) : FTK L (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_headInsufficientLoop _)

theorem ft_refillBudgetCheck (usage : Ticks) : FTK L (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillBudgetCheck _)

theorem ft_refillBudgetCheckRoundRobin (usage : Ticks) : FTK L (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillBudgetCheckRoundRobin _)

theorem ft_commitTime  : FTK L (commitTime (Z := Unit)) := by
  unfold commitTime; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_commitTime)

theorem ft_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : FTK L (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScObjRef _ _)

theorem ft_testReschedule (fromTptr : ObjRef) : FTK L (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_testReschedule _)

theorem ft_schedContextDonate (scPtr tcbPtr : ObjRef) : FTK L (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextDonate _ _)

theorem ft_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : FTK L (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_orderedInsert _ _ _ _)

theorem ft_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : FTK L (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_readyTimesAppend _ _)

theorem ft_tcbReleaseEnqueue (tcbPtr : ObjRef) : FTK L (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseEnqueue _)

theorem ft_postpone (scPtr : ObjRef) : FTK L (postpone (Z := Unit) scPtr) := by
  unfold postpone; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_postpone _)

theorem ft_schedContextResume (scPtr : ObjRef) : FTK L (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextResume _)

theorem ft_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : FTK L (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeDonateSc _ _)

theorem ft_mergeOverlappingRefills (scPtr : ObjRef) : FTK L (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_mergeOverlappingRefills _)

theorem ft_refillHeadOverlappingLoop (scPtr : ObjRef) : FTK L (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillHeadOverlappingLoop _)

theorem ft_refillUnblockCheck (scPtr : ObjRef) : FTK L (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillUnblockCheck _)

theorem ft_completeSignal (ntfnptr tptr : ObjRef) : FTK L (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_completeSignal _ _)

theorem ft_schedContextCancelYieldTo (thread : ObjRef) : FTK L (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextCancelYieldTo _)

theorem ft_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : FTK L (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupIpcBuffer _ _)

theorem ft_setMessageInfo (thread : ObjRef) (info : MessageInfo) : FTK L (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setMessageInfo _ _)

theorem ft_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : FTK L (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storeWordOffs _ _ _)

theorem ft_replyFromKernel (thread : ObjRef) (x : Data × List Data) : FTK L (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyFromKernel _ _)

theorem ft_schedContextUpdateConsumed (scPtr : ObjRef) : FTK L (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUpdateConsumed _)

theorem ft_setConsumed (scPtr tcbPtr : ObjRef) : FTK L (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setConsumed _ _)

theorem ft_completeYieldTo (tcbPtr : ObjRef) : FTK L (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_completeYieldTo _)

theorem ft_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : FTKE L m) : FTK L (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_constOnFailure _ _ ?_)

theorem ft_copyGlobalMappings (newPm : ObjRef) : FTK L (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_copyGlobalMappings _)

theorem ft_loadWordOffs (ptr : ObjRef) (offs : Nat) : FTK L (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadWordOffs _ _)

theorem ft_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : FTK L (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_copyMrs _ _ _ _ _)

theorem ft_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : FTK L (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_createCap _ _ _ _ _)

theorem ft_dataToObjType (type : Data) : FTKE L (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_dataToObjType _)

theorem ft_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeBindNotification _ _)

theorem ft_deriveCap (slot : CslotPtr) (cap : Cap) : FTKE L (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deriveCap _ _)

theorem ft_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPivotSlot _ _ _)

theorem ft_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSourceSlot _ _ _)

theorem ft_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : FTKE L (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeCnodeInvocation _ _ _ _)

theorem ft_slotCapLongRunningDelete (slot : CslotPtr) : FTK L (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_slotCapLongRunningDelete _)

theorem ft_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeCvSpace _ _ _ _)

theorem ft_subframeNode (nodeCap : Cap) (index depth : Data) : FTKE L (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_subframeNode _ _ _)

theorem ft_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDeriveSubframe _ _ _ _)

theorem ft_decodeDomainScheduleConfigure (args : List Data) : FTKE L (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainScheduleConfigure _)

theorem ft_decodeDomainScheduleSetStart (args : List Data) : FTKE L (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainScheduleSetStart _)

theorem ft_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : FTKE L (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainSet _ _)

theorem ft_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : FTKE L (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainInvocation _ _ _)

theorem ft_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : FTK L (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4GetMr _ _ _)

theorem ft_fl4Arg (buf : Option ObjRef) (i : Nat) : FTKE L (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4Arg _ _)

theorem ft_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4ConfigureSingleStepping _ _)

theorem ft_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4FpuTransfer _ _ _ _)

theorem ft_fl4CheckBpNum (bp : Data) : FTKE L (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4CheckBpNum _)

theorem ft_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4GetBreakpoint _ _)

theorem ft_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, FTKE L (check x0)) : FTKE L (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ft_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ft_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqControlRemapped _ _ _)

theorem ft_fl4ArchCheckIrq (irq : Data) : FTKE L (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchCheckIrq _)

theorem ft_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4IrqControl _ _ _ _ _)

theorem ft_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetBreakpoint _ _)

theorem ft_decodeFl4SetFlags (args : List Data) (t : ObjRef) : FTKE L (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetFlags _ _)

theorem ft_decodeFl4SetTimer (args : List Data) (t : ObjRef) : FTKE L (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetTimer _ _)

theorem ft_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4UnsetBreakpoint _ _)

theorem ft_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : FTKE L (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4TcbExt _ _ _ _ _)

theorem ft_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqControlInvocation _ _ _ _)

theorem ft_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : FTKE L (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqHandlerInvocation _ _ _)

theorem ft_getScReleased (scPtr : ObjRef) : FTK L (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScReleased _)

theorem ft_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextBind _ _)

theorem ft_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextUnbindObject _ _)

theorem ft_decodeSchedContextYieldTo (scPtr : ObjRef) : FTKE L (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextYieldTo _)

theorem ft_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextInvocation _ _ _)

theorem ft_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : FTKE L (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedControlInvocationFlags _ _ _)

theorem ft_rangeCheck (v minV maxV : Word) : FTKE L (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_rangeCheck _ _ _)

theorem ft_decodeSetFlags (args : List Data) (cap : Cap) : FTKE L (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetFlags _ _)

theorem ft_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : FTKE L (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetIpcBuffer _ _ _ _)

theorem ft_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetMcpriority _ _ _ _)

theorem ft_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetPriority _ _ _ _)

theorem ft_isBlocked (thread : ObjRef) : FTK L (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isBlocked _)

theorem ft_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : FTKE L (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUpdateSc _ _ _)

theorem ft_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetSchedParams _ _ _ _)

theorem ft_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetSpace _ _ _ _)

theorem ft_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetTimeoutEp _ _ _)

theorem ft_decodeSetTlsBase (args : List Data) (cap : Cap) : FTKE L (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetTlsBase _ _)

theorem ft_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTcbConfigure _ _ _ _)

theorem ft_decodeUnbindNotification (cap : Cap) : FTKE L (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ft_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : FTKE L (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTcbInvocation _ _ _ _ _)

theorem ft_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FTKE L (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUntypedInvocation _ _ _ _ _)

theorem ft_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : FTKE L (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeInvocation _ _ _ _ _ _ _ _)

theorem ft_decodePml4Flush (cap : ArchCap) : FTKE L (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePml4Flush _)

theorem ft_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : FTKE L (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_frameMappingSlot _ _ _ _)

theorem ft_decodeTestAndClearAccessed (cap : ArchCap) : FTKE L (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTestAndClearAccessed _)

theorem ft_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FTKE L (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ft_deletedIrqHandler (irq : Irq) : FTK L (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deletedIrqHandler _)

theorem ft_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : FTK L (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_makeArchFaultMsg _ _)

theorem ft_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : FTK L (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_makeFaultMsg _ _)

theorem ft_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : FTK L (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doFaultTransfer _ _ _ _)

theorem ft_getMessageInfo (thread : ObjRef) : FTK L (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getMessageInfo _)

theorem ft_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : FTK L (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ft_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getExtraCptrs _ _)

theorem ft_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : FTKE L (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSlotForThread _ _)

theorem ft_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : FTKE L (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupCapAndSlot _ _)

theorem ft_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : FTKE L (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupExtraCaps _ _ _)

theorem ft_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : FTKE L m) : FTK L (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_emptyOnFailure _ ?_)

theorem ft_loadCapTransfer (buffer : ObjRef) : FTK L (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadCapTransfer _)

theorem ft_lookupCap (thread : ObjRef) (ref : CapRef) : FTKE L (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupCap _ _)

theorem ft_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : FTKE L m) : FTKE L (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_unifyFailure _ ?_)

theorem ft_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : FTK L (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getReceiveSlots _ _)

theorem ft_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : FTK L (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setExtraBadge _ _ _)

theorem ft_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      FTK L (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ft_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ft_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ft_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_transferCapsLoop _ _ _ _ _ _)

theorem ft_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : FTK L (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_transferCaps _ _ _ _ _)

theorem ft_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : FTK L (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doNormalTransfer _ _ _ _ _ _ _)

theorem ft_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : FTK L (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doIpcTransfer _ _ _ _ _)

theorem ft_doNbrecvFailedTransfer (thread : ObjRef) : FTK L (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doNbrecvFailedTransfer _)

theorem ft_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : FTK L (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_domainScheduleConfigure _ _ _)

theorem ft_setNextInterrupt  : FTK L (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setNextInterrupt)

theorem ft_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : FTK L (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ifCondRefillUnblockCheck _ _ _)

theorem ft_switchSchedContext  : FTK L (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchSchedContext)

theorem ft_scAndTimer  : FTK L (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scAndTimer)

theorem ft_scheduleChooseNewThread  : FTK L (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleChooseNewThread)

theorem ft_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : FTK L (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleSwitchThreadFastfail _ _ _ _)

theorem ft_schedule  : FTK L (schedule (Z := Unit)) := by
  unfold schedule; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedule)

theorem ft_domainSetStart (index : Nat) : FTK L (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_domainSetStart _)

theorem ft_postCapDeletion (cap : Cap) : FTK L (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_postCapDeletion _)

theorem ft_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : FTK L (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_emptySlot _ _)

theorem ft_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ft_performDeriveSubframe (iv : Fl4SubframeInvocation) : FTK L (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performDeriveSubframe _)

theorem ft_performPml4Flush (a0 : Fl4Pml4Invocation) : FTK L (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPml4Flush _)

theorem ft_performTestAndClearAccessed (_slot : ObjRef) : FTK L (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performTestAndClearAccessed _)

theorem ft_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : FTKE L (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchPerformInvocation _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ft_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    FTKE L (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ft_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : FTKE L (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ft_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : FTK L (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ReplyFromKernelError _ _ _)

theorem ft_fl4SyscallFaultIP (thread : ObjRef) : FTK L (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4SyscallFaultIP _)

theorem ft_getCapReg (reg : Register) : FTK L (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCapReg _)

theorem ft_getIrqSlot (irq : Irq) : FTK L (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getIrqSlot _)

theorem ft_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : FTK L (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getMrs _ _ _)

theorem ft_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : FTK L (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleArchFaultReply _ _ _ _)

theorem ft_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : FTK L (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleFaultReply _ _ _ _)

theorem ft_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : FTK L (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleHypervisorFault _ _)

theorem ft_handleNoFault (tptr : ObjRef) : FTK L (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleNoFault _)

theorem ft_handleReservedIrq (_irq : Irq) : FTK L (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleReservedIrq _)

theorem ft_handleSpuriousIrq  : FTK L (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleSpuriousIrq)

theorem ft_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : FTKE L (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleVmFault _ _)

theorem ft_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : FTK L (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_initArchObjects _ _ _ _ _ _)

theorem ft_threadSetDomain (tptr : ObjRef) (domain : Domain) : FTK L (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadSetDomain _ _)

theorem ft_setDomain (tptr : ObjRef) (newDom : Domain) : FTK L (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setDomain _ _)

theorem ft_invokeSetDomain (thread : ObjRef) (domain : Domain) : FTK L (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSetDomain _ _)

theorem ft_invokeDomain (domInv : DomainInvocation) : FTK L (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeDomain _)

theorem ft_invokeIrqControl (a0 : IrqControlInvocation) : FTKE L (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeIrqControl _)

theorem ft_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : FTKE L (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeFl4IrqControl _)

theorem ft_invokeFl4Tcb (a0 : Fl4TcbInvocation) : FTKE L (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeFl4Tcb _)

theorem ft_returnConsumed (scPtr : ObjRef) : FTK L (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_returnConsumed _)

theorem ft_schedContextBindNtfn (sc ntfn : ObjRef) : FTK L (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextBindNtfn _ _)

theorem ft_schedContextBindTcb (scPtr tcbPtr : ObjRef) : FTK L (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextBindTcb _ _)

theorem ft_schedContextUnbindTcb (scPtr : ObjRef) : FTK L (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindTcb _)

theorem ft_schedContextUnbindAllTcbs (scPtr : ObjRef) : FTK L (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindAllTcbs _)

theorem ft_schedContextUnbindNtfn (scPtr : ObjRef) : FTK L (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindNtfn _)

theorem ft_schedContextUnbindReply (scPtr : ObjRef) : FTK L (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindReply _)

theorem ft_schedContextYieldTo (scPtr : ObjRef) : FTK L (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextYieldTo _)

theorem ft_invokeSchedContext (iv : SchedContextInvocation) : FTK L (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSchedContext _)

theorem ft_maybeAddEmptyTail (scPtr : ObjRef) : FTK L (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeAddEmptyTail _)

theorem ft_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : FTK L (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillNew _ _ _ _)

theorem ft_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : FTK L (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillUpdate _ _ _ _)

theorem ft_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : FTK L (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSchedControlConfigureFlags _)

theorem ft_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : FTKE L f) (h_g : FTKE L g) : FTKE L (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ft_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_orChoiceE _ _ _ ?_ ?_)

theorem ft_updateTimeStamp  : FTK L (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateTimeStamp)

theorem ft_preemptionPoint  : FTKE L (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_preemptionPoint)

theorem ft_resetUntypedCap (srcSlot : CslotPtr) : FTKE L (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resetUntypedCap _)

theorem ft_invokeUntyped (ui : UntypedInvocation) : FTKE L (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeUntyped _)

theorem ft_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : FTKE L (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeUntypedWith _ _)

theorem ft_isValidTimeoutHandler (tptr : ObjRef) : FTK L (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isValidTimeoutHandler _)

theorem ft_lookupReply  : FTKE L (lookupReply (Z := Unit)) := by
  unfold lookupReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupReply)

theorem ft_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : FTK L (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeReturnSc _ _)

theorem ft_prepareThreadDelete (threadPtr : ObjRef) : FTK L (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_prepareThreadDelete _)

theorem ft_refillResetRr (cscPtr : ObjRef) : FTK L (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillResetRr _)

theorem ft_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : FTK L (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbAppend _ _)

theorem ft_reorderEp (epPtr tptr : ObjRef) : FTK L (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_reorderEp _ _)

theorem ft_reorderNtfn (ntfnPtr tptr : ObjRef) : FTK L (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_reorderNtfn _ _)

theorem ft_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : FTK L (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyPush _ _ _ _)

theorem ft_replyUnlinkSc (scPtr replyPtr : ObjRef) : FTK L (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyUnlinkSc _ _)

theorem ft_replyRemove (caller r : ObjRef) : FTK L (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyRemove _ _)

theorem ft_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : FTK L (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextMaybeUnbindNtfn _)

theorem ft_schedContextSetInactive (scPtr : ObjRef) : FTK L (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextSetInactive _)

theorem ft_schedContextUnbindYieldFrom (scPtr : ObjRef) : FTK L (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindYieldFrom _)

theorem ft_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : FTK L (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbEpAppend _ _ _)

theorem ft_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : FTK L (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_sendIpcBlocked _ _ _ _ _ _)

theorem ft_setFlags (ref : ObjRef) (flags : TcbFlags) : FTK L (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setFlags _ _)

theorem ft_setMcpriority (ref : ObjRef) (mcp : Priority) : FTK L (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setMcpriority _ _)

theorem ft_threadSetPriority (tptr : ObjRef) (prio : Priority) : FTK L (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadSetPriority _ _)

theorem ft_setPriority (tptr : ObjRef) (prio : Priority) : FTK L (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPriority _ _)

theorem ft_updateRestartPc (threadPtr : ObjRef) : FTK L (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRestartPc _)

theorem ft_suspend (thread : ObjRef) : FTK L (suspend (Z := Unit) thread) := by
  unfold suspend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_suspend _)

theorem ft_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : FTKE L mFault) (h_hFault : ∀ x0, FTK L (hFault x0)) (h_mError : ∀ x0, FTKE L (mError x0)) (h_hError : ∀ x0, FTK L (hError x0)) (h_mFinalise : ∀ x0, FTKE L (mFinalise x0)) : FTKE L (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ft_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ft_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : FTK L (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbNtfnAppend _ _)

theorem ft_testPossibleSwitchTo (tcbPtr : ObjRef) : FTK L (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_testPossibleSwitchTo _)

theorem ft_unbindFromSc (tcbPtr : ObjRef) : FTK L (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindFromSc _)

theorem ft_unbindMaybeNotification (ntfnptr : ObjRef) : FTK L (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindMaybeNotification _)

theorem ft_unbindNotification (tcb : ObjRef) : FTK L (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindNotification _)
