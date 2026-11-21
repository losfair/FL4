theorem nb_archActivateIdleThread (_t : ObjRef) : NBK (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archActivateIdleThread _)

theorem nb_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : NBK (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadGet _ _)

theorem nb_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : NBK (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getTcbObjRef _ _)

theorem nb_schedContextCancelYieldTo (thread : ObjRef) : NBK (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextCancelYieldTo _)

theorem nb_getCap (a0 : CslotPtr) : NBK (getCap (Z := Unit) a0) := by
  unfold getCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getCap _)

theorem nb_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : NBK (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupIpcBuffer _ _)

theorem nb_setMessageInfo (thread : ObjRef) (info : MessageInfo) : NBK (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setMessageInfo _ _)

theorem nb_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : NBK (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storeWordOffs _ _ _)

theorem nb_replyFromKernel (thread : ObjRef) (x : Data × List Data) : NBK (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyFromKernel _ _)

theorem nb_getSchedContext (ptr : ObjRef) : NBK (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getSchedContext _)

theorem nb_schedContextUpdateConsumed (scPtr : ObjRef) : NBK (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUpdateConsumed _)

theorem nb_setConsumed (scPtr tcbPtr : ObjRef) : NBK (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setConsumed _ _)

theorem nb_completeYieldTo (tcbPtr : ObjRef) : NBK (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_completeYieldTo _)

theorem nb_getThreadState (ref : ObjRef) : NBK (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getThreadState _)

theorem nb_setSchedulerAction (action : SchedulerAction) : NBK (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setSchedulerAction _)

theorem nb_activateThread  : NBK (activateThread (Z := Unit)) := by
  unfold activateThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_activateThread)

theorem nb_archCheckIrq (_irq : Data) : NBKE (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archCheckIrq _)

theorem nb_ensureEmpty (slot : CslotPtr) : NBKE (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ensureEmpty _)

theorem nb_isIoportRangeFree (f l : IoPort) : NBK (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isIoportRangeFree _ _)

theorem nb_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : NBKE m) : NBKE (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_lookupErrorOnFailure _ _ ?_)

theorem nb_resolveAddressBits' (p : Cap × CapRef) : NBKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by nb_auto)) fun nc => ?_
        split
        · exact nb_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_resolveAddressBits' _)

theorem nb_resolveAddressBits (a0 : Cap × CapRef) : NBKE (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_resolveAddressBits _)

theorem nb_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : NBKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupSlotForCnodeOp _ _ _ _)

theorem nb_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NBKE (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupTargetSlot _ _ _)

theorem nb_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : NBKE (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIoportControlInvocation _ _ _ _ _)

theorem nb_getAsidPool (ptr : ObjRef) : NBK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getAsidPool _)

theorem nb_findVspaceForAsid (asid : Asid) : NBKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_findVspaceForAsid _)

theorem nb_getPdpt (ptr : ObjRef) : NBK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPdpt _)

theorem nb_getPdpte (ptr : ObjRef) : NBK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPdpte _)

theorem nb_isFinalCap (cap : Cap) : NBK (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isFinalCap _)

theorem nb_getPml4 (ptr : ObjRef) : NBK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPml4 _)

theorem nb_getPml4e (ptr : ObjRef) : NBK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPml4e _)

theorem nb_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : NBKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupPdptSlot _ _)

theorem nb_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePageDirectoryInvocation _ _ _ _ _)

theorem nb_checkVpAlignment (sz : VMPageSize) (vptr : Word) : NBKE (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkVpAlignment _ _)

theorem nb_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : NBKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupPdSlot _ _)

theorem nb_getPd (ptr : ObjRef) : NBK (getPd (Z := Unit) ptr) := by
  unfold getPd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPd _)

theorem nb_getPde (ptr : ObjRef) : NBK (getPde (Z := Unit) ptr) := by
  unfold getPde; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPde _)

theorem nb_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : NBKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupPtSlot _ _)

theorem nb_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : NBKE (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_createMappingEntries _ _ _ _ _ _)

theorem nb_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : NBKE (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ensureSafeMapping _)

theorem nb_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePageInvocation _ _ _ _ _)

theorem nb_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePageTableInvocation _ _ _ _ _)

theorem nb_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePdptInvocation _ _ _ _ _)

theorem nb_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : NBKE (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ensurePortOperationAllowed _ _ _)

theorem nb_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : NBKE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePortInvocation _ _ _)

theorem nb_ensureNoChildren (cslotPtr : CslotPtr) : NBKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ensureNoChildren _)

theorem nb_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : NBK (selectExt (Z := Unit) a S) := by
  unfold selectExt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_selectExt _ _)

theorem nb_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archDecodeInvocation _ _ _ _ _ _)

theorem nb_getIrqState (irq : Irq) : NBK (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getIrqState _)

theorem nb_isIrqActive (irq : Irq) : NBK (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isIrqActive _)

theorem nb_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archDecodeIrqControlInvocation _ _ _ _)

theorem nb_archDeriveCap (c : ArchCap) : NBKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archDeriveCap _)

theorem nb_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : NBK (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_hwAsidInvalidate _ _)

theorem nb_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : NBK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setAsidPool _ _)

theorem nb_getCurrentCr3  : NBK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getCurrentCr3)

theorem nb_setCurrentCr3 (c : Cr3) : NBK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setCurrentCr3 _)

theorem nb_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : NBK (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setCurrentVspaceRoot _ _)

theorem nb_setVmRoot (tcb : ObjRef) : NBK (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setVmRoot _)

theorem nb_deleteAsid (asid : Asid) (pml4 : ObjRef) : NBK (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deleteAsid _ _)

theorem nb_deleteAsidPool (base : Asid) (ptr : ObjRef) : NBK (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deleteAsidPool _ _)

theorem nb_getPt (ptr : ObjRef) : NBK (getPt (Z := Unit) ptr) := by
  unfold getPt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPt _)

theorem nb_getPte (ptr : ObjRef) : NBK (getPte (Z := Unit) ptr) := by
  unfold getPte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getPte _)

theorem nb_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : NBK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPd _ _)

theorem nb_storePde (p : ObjRef) (pde : PDE) : NBK (storePde (Z := Unit) p pde) := by
  unfold storePde; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePde _ _)

theorem nb_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : NBK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPdpt _ _)

theorem nb_storePdpte (p : ObjRef) (pte : PDPTE) : NBK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePdpte _ _)

theorem nb_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : NBK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPt _ _)

theorem nb_storePte (p : ObjRef) (pte : PTE) : NBK (storePte (Z := Unit) p pte) := by
  unfold storePte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePte _ _)

theorem nb_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : NBK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPage _ _ _ _)

theorem nb_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : NBK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_flushTable _ _ _ _)

theorem nb_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : NBK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invalidatePageStructureCacheAsid _ _)

theorem nb_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NBK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPageTable _ _ _)

theorem nb_flushAll (vspace : ObjRef) (asid : Asid) : NBK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_flushAll _ _)

theorem nb_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NBK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPd _ _ _)

theorem nb_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NBK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPml4 _ _)

theorem nb_storePml4e (p : ObjRef) (pte : PML4E) : NBK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePml4e _ _)

theorem nb_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NBK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPdpt _ _ _)

theorem nb_archFinaliseCap (c : ArchCap) (x : Bool) : NBK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archFinaliseCap _ _)

theorem nb_archGetSanitiseRegisterInfo (_t : ObjRef) : NBK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archGetSanitiseRegisterInfo _)

theorem nb_setOriginal (slot : CslotPtr) (v : Bool) : NBK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setOriginal _ _)

theorem nb_setCdt (t : Cdt) : NBK (setCdt (Z := Unit) t) := by
  unfold setCdt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setCdt _)

theorem nb_updateCdt (f : Cdt → Cdt) : NBK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateCdt _)

theorem nb_setIrqState (state : IrqState) (irq : Irq) : NBK (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setIrqState _ _)

theorem nb_updateIrqState (irq : Irq) (irqState : X64IRQState) : NBK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateIrqState _ _)

theorem nb_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NBK m) : NBKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_withoutPreemption _ ?_)

theorem nb_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NBKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archInvokeIrqControl _)

theorem nb_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NBK (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archInvokeIrqHandler _)

theorem nb_archMaskIrqSignal (irq : Irq) : NBK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archMaskIrqSignal _)

theorem nb_setIoportMask (f l : IoPort) (val : Bool) : NBK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setIoportMask _ _ _)

theorem nb_freeIoportRange (f l : IoPort) : NBK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_freeIoportRange _ _)

theorem nb_archPostCapDeletion (ac : ArchCap) : NBK (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostCapDeletion _)

theorem nb_archPostModifyRegisters (cur t : ObjRef) : NBK (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostModifyRegisters _ _)

theorem nb_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NBK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostResetUntyped _ _)

theorem nb_loadFpuState (t : ObjRef) : NBK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadFpuState _)

theorem nb_saveFpuState (t : ObjRef) : NBK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_saveFpuState _)

theorem nb_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NBK (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setX64CurrentFpuOwner _)

theorem nb_switchLocalFpuOwner (newOwner : Option ObjRef) : NBK (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchLocalFpuOwner _)

theorem nb_fpuRelease (threadPtr : ObjRef) : NBK (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fpuRelease _)

theorem nb_lazyFpuRestore (threadPtr : ObjRef) : NBK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lazyFpuRestore _)

theorem nb_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NBK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostSetFlags _ _)

theorem nb_archPrepareNextDomain  : NBK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPrepareNextDomain)

theorem nb_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NBK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPrepareSetDomain _ _)

theorem nb_archSwitchToIdleThread  : NBK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archSwitchToIdleThread)

theorem nb_archSwitchToThread (t : ObjRef) : NBK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archSwitchToThread _)

theorem nb_getScRefillReady (scPtr : ObjRef) : NBK (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScRefillReady _)

theorem nb_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NBK (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScRefillSufficient _ _)

theorem nb_getTcbQueue (d : Domain) (prio : Priority) : NBK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getTcbQueue _ _)

theorem nb_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NBK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setTcbQueue _ _ _)

theorem nb_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NBK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbSchedAction _ _)

theorem nb_rescheduleRequired  : NBK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_rescheduleRequired)

theorem nb_possibleSwitchTo (target : ObjRef) : NBK (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_possibleSwitchTo _)

theorem nb_tcbReleaseRemove (tcbPtr : ObjRef) : NBK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseRemove _)

theorem nb_tcbReleaseDequeue  : NBK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseDequeue)

theorem nb_awaken  : NBK (awaken (Z := Unit)) := by
  unfold awaken; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_awaken)

theorem nb_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NBK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getSimpleKo _ _)

theorem nb_bindNotification (tcbptr ntfnptr : ObjRef) : NBK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_bindNotification _ _)

theorem nb_bindScReply (scPtr replyPtr : ObjRef) : NBK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_bindScReply _ _)

theorem nb_getBlockingObject (state : ThreadState) : NBK (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getBlockingObject _)

theorem nb_replyUnlinkTcb (t r : ObjRef) : NBK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyUnlinkTcb _ _)

theorem nb_tcbEpDequeue (tptr epPtr : ObjRef) : NBK (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbEpDequeue _ _)

theorem nb_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : NBK (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_blockedCancelIpc _ _ _)

theorem nb_isRoundRobin (scPtr : ObjRef) : NBK (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isRoundRobin _)

theorem nb_getRefillHead (scPtr : ObjRef) : NBK (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefillHead _)

theorem nb_refillPopHead (scPtr : ObjRef) : NBK (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillPopHead _)

theorem nb_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NBK (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRefillHd _ _)

theorem nb_mergeOverlappingRefills (scPtr : ObjRef) : NBK (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_mergeOverlappingRefills _)

theorem nb_refillHeadOverlappingLoop (scPtr : ObjRef) : NBK (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillHeadOverlappingLoop _)

theorem nb_refillUnblockCheck (scPtr : ObjRef) : NBK (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillUnblockCheck _)

theorem nb_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NBK (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ifCondRefillUnblockCheck _ _ _)

theorem nb_restartThreadIfNoFault (t : ObjRef) : NBK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_restartThreadIfNoFault _)

theorem nb_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NBK (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartEpQueuedThread _ _)

theorem nb_cancelAllIpc (epptr : ObjRef) : NBK (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelAllIpc _)

theorem nb_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NBK (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartNtfnQueuedThread _ _)

theorem nb_cancelAllSignals (ntfnptr : ObjRef) : NBK (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelAllSignals _)

theorem nb_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NBK (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartBadgedThread _ _ _)

theorem nb_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NBK (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelBadgedSends _ _)

theorem nb_cancelSignal (threadptr ntfnptr : ObjRef) : NBK (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelSignal _ _)

theorem nb_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NBK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getSkObjRef _ _ _)

theorem nb_replyRemoveTcb (tptr rptr : ObjRef) : NBK (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyRemoveTcb _ _)

theorem nb_cancelIpc (tptr : ObjRef) : NBK (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelIpc _)

theorem nb_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NBK (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capSwap _ _ _ _)

theorem nb_capSwapForDelete (slot1 slot2 : CslotPtr) : NBK (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capSwapForDelete _ _)

theorem nb_deletedIrqHandler (irq : Irq) : NBK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deletedIrqHandler _)

theorem nb_postCapDeletion (cap : Cap) : NBK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_postCapDeletion _)

theorem nb_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NBK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_emptySlot _ _)

theorem nb_replyUnlinkSc (scPtr replyPtr : ObjRef) : NBK (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyUnlinkSc _ _)

theorem nb_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NBK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScObjRef _ _)

theorem nb_testReschedule (fromTptr : ObjRef) : NBK (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_testReschedule _)

theorem nb_schedContextDonate (scPtr tcbPtr : ObjRef) : NBK (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextDonate _ _)

theorem nb_replyRemove (caller r : ObjRef) : NBK (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyRemove _ _)

theorem nb_unbindMaybeNotification (ntfnptr : ObjRef) : NBK (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindMaybeNotification _)

theorem nb_fastFinalise (a0 : Cap) (a1 : Bool) : NBK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fastFinalise _ _)

theorem nb_capDeleteOne (slot : CslotPtr) : NBK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capDeleteOne _)

theorem nb_getIrqSlot (irq : Irq) : NBK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getIrqSlot _)

theorem nb_deletingIrqHandler (irq : Irq) : NBK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deletingIrqHandler _)

theorem nb_prepareThreadDelete (threadPtr : ObjRef) : NBK (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_prepareThreadDelete _)

theorem nb_schedContextSetInactive (scPtr : ObjRef) : NBK (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextSetInactive _)

theorem nb_schedContextUnbindTcb (scPtr : ObjRef) : NBK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindTcb _)

theorem nb_schedContextUnbindAllTcbs (scPtr : ObjRef) : NBK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindAllTcbs _)

theorem nb_schedContextUnbindReply (scPtr : ObjRef) : NBK (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindReply _)

theorem nb_schedContextUnbindYieldFrom (scPtr : ObjRef) : NBK (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindYieldFrom _)

theorem nb_updateRestartPc (threadPtr : ObjRef) : NBK (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRestartPc _)

theorem nb_suspend (thread : ObjRef) : NBK (suspend (Z := Unit) thread) := by
  unfold suspend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_suspend _)

theorem nb_unbindFromSc (tcbPtr : ObjRef) : NBK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindFromSc _)

theorem nb_unbindNotification (tcb : ObjRef) : NBK (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindNotification _)

theorem nb_finaliseCap (a0 : Cap) (a1 : Bool) : NBK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_finaliseCap _ _)

theorem nb_getScActive (scPtr : ObjRef) : NBK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScActive _)

theorem nb_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NBKE f) (h_g : NBKE g) : NBKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; nb_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_orChoiceE _ _ _ ?_ ?_)

theorem nb_updateTimeStamp  : NBK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateTimeStamp)

theorem nb_preemptionPoint  : NBKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem nb_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NBK (f k)) (k : RecDelCall) : NBKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NBKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; nb_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; nb_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> nb_auto
    all_goals exact hrec' _

theorem nb_recDel (c : RecDelCall) : NBKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => nb_recDelF hf k) c
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_recDel _)

theorem nb_capDelete (slot : CslotPtr) : NBKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capDelete _)

theorem nb_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NBKE m) : NBKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_capFaultOnFailure _ _ _ ?_)

theorem nb_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NBK (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem nb_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NBK (f k)) (sl : CslotPtr) : NBKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NBKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  nb_auto
  all_goals exact hrec' _

theorem nb_capRevoke (sl : CslotPtr) : NBKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => nb_capRevokeF hf k) sl
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capRevoke _)

theorem nb_captransferFromWords (ptr : Word) : NBK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_captransferFromWords _)

theorem nb_isValidTimeoutHandler (tptr : ObjRef) : NBK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isValidTimeoutHandler _)

theorem nb_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NBK (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_makeArchFaultMsg _ _)

theorem nb_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NBK (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_makeFaultMsg _ _)

theorem nb_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NBK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doFaultTransfer _ _ _ _)

theorem nb_loadWordOffs (ptr : ObjRef) (offs : Nat) : NBK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadWordOffs _ _)

theorem nb_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NBK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_copyMrs _ _ _ _ _)

theorem nb_getMessageInfo (thread : ObjRef) : NBK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getMessageInfo _)

theorem nb_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NBK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; nb_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getExtraCptrs _ _)

theorem nb_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NBKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupSlotForThread _ _)

theorem nb_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NBKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupCapAndSlot _ _)

theorem nb_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NBKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupExtraCaps _ _ _)

theorem nb_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NBKE m) : NBK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_emptyOnFailure _ ?_)

theorem nb_loadCapTransfer (buffer : ObjRef) : NBK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadCapTransfer _)

theorem nb_lookupCap (thread : ObjRef) (ref : CapRef) : NBKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupCap _ _)

theorem nb_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NBKE m) : NBKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_unifyFailure _ ?_)

theorem nb_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NBK (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getReceiveSlots _ _)

theorem nb_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NBKE m) : NBK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_constOnFailure _ _ ?_)

theorem nb_deriveCap (slot : CslotPtr) (cap : Cap) : NBKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deriveCap _ _)

theorem nb_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NBK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setExtraBadge _ _ _)

theorem nb_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NBK (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; nb_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => nb_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | nb_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_transferCapsLoop _ _ _ _ _ _)

theorem nb_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NBK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_transferCaps _ _ _ _ _)

theorem nb_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NBK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doNormalTransfer _ _ _ _ _ _ _)

theorem nb_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NBK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doIpcTransfer _ _ _ _ _)

theorem nb_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : NBK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyPush _ _ _ _)

theorem nb_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NBK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_orderedInsert _ _ _ _)

theorem nb_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NBK (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbAppend _ _)

theorem nb_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : NBK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbEpAppend _ _ _)

theorem nb_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : NBK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendIpcBlocked _ _ _ _ _ _)

theorem nb_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : NBK (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendIpc _ _ _ _ _ _ _ _)

theorem nb_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : NBK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendFaultIpc _ _ _ _)

theorem nb_handleTimeout (tptr : ObjRef) (ex : Fault) : NBK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleTimeout _ _)

theorem nb_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NBK (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_readyTimesAppend _ _)

theorem nb_tcbReleaseEnqueue (tcbPtr : ObjRef) : NBK (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseEnqueue _)

theorem nb_postpone (scPtr : ObjRef) : NBK (postpone (Z := Unit) scPtr) := by
  unfold postpone; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_postpone _)

theorem nb_endTimeslice (canTimeout : Bool) : NBK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_endTimeslice _)

theorem nb_getRefills (scPtr : ObjRef) : NBK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefills _)

theorem nb_refillSize (scPtr : ObjRef) : NBK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillSize _)

theorem nb_refillSingle (scPtr : ObjRef) : NBK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillSingle _)

theorem nb_getRefillTail (scPtr : ObjRef) : NBK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefillTail _)

theorem nb_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NBK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillAddTail _ _)

theorem nb_refillFull (scPtr : ObjRef) : NBK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillFull _)

theorem nb_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NBK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRefillTl _ _)

theorem nb_scheduleUsed (scPtr : ObjRef) (new : Refill) : NBK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleUsed _ _)

theorem nb_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NBK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chargeEntireHeadRefill _ _)

theorem nb_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NBK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleOverrun _ _)

theorem nb_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NBK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_mergeNonoverlappingHeadRefill _)

theorem nb_headInsufficientLoop (scPtr : ObjRef) : NBK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_headInsufficientLoop _)

theorem nb_refillBudgetCheck (usage : Ticks) : NBK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillBudgetCheck _)

theorem nb_refillResetRr (cscPtr : ObjRef) : NBK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillResetRr _)

theorem nb_chargeBudget (consumed : Ticks) (canTimeout : Bool) : NBK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chargeBudget _ _)

theorem nb_checkBudget  : NBK (checkBudget (Z := Unit)) := by
  unfold checkBudget; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkBudget)

theorem nb_checkBudgetRestart  : NBK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkBudgetRestart)

theorem nb_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NBK m) : NBK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_checkCapAt _ _ _ ?_)

theorem nb_checkDomainTime  : NBK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkDomainTime)

theorem nb_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NBKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkHandlerEp _ _)

theorem nb_checkPrio (newPrio : Data) (authTcb : ObjRef) : NBKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkPrio _ _)

theorem nb_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NBKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkValidIpcBuffer _ _)

theorem nb_nextDomain  : NBK (nextDomain (Z := Unit)) := by
  unfold nextDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_nextDomain)

theorem nb_switchToThread (t : ObjRef) : NBK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchToThread _)

theorem nb_guardedSwitchTo (thread : ObjRef) : NBK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_guardedSwitchTo _)

theorem nb_switchToIdleThread  : NBK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchToIdleThread)

theorem nb_chooseThread  : NBK (chooseThread (Z := Unit)) := by
  unfold chooseThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chooseThread)

theorem nb_refillBudgetCheckRoundRobin (usage : Ticks) : NBK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillBudgetCheckRoundRobin _)

theorem nb_commitTime  : NBK (commitTime (Z := Unit)) := by
  unfold commitTime; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_commitTime)

theorem nb_copyGlobalMappings (newPm : ObjRef) : NBK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_copyGlobalMappings _)

theorem nb_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NBK (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_createCap _ _ _ _ _)

theorem nb_dataToObjType (type : Data) : NBKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_dataToObjType _)

theorem nb_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeBindNotification _ _)

theorem nb_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NBKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupPivotSlot _ _ _)

theorem nb_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NBKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupSourceSlot _ _ _)

theorem nb_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NBKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeCnodeInvocation _ _ _ _)

theorem nb_slotCapLongRunningDelete (slot : CslotPtr) : NBK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_slotCapLongRunningDelete _)

theorem nb_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NBKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeCvSpace _ _ _ _)

theorem nb_subframeNode (nodeCap : Cap) (index depth : Data) : NBKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_subframeNode _ _ _)

theorem nb_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NBKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDeriveSubframe _ _ _ _)

theorem nb_decodeDomainScheduleConfigure (args : List Data) : NBKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainScheduleConfigure _)

theorem nb_decodeDomainScheduleSetStart (args : List Data) : NBKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainScheduleSetStart _)

theorem nb_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NBKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainSet _ _)

theorem nb_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NBKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainInvocation _ _ _)

theorem nb_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NBK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4GetMr _ _ _)

theorem nb_fl4Arg (buf : Option ObjRef) (i : Nat) : NBKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4Arg _ _)

theorem nb_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4ConfigureSingleStepping _ _)

theorem nb_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NBKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4FpuTransfer _ _ _ _)

theorem nb_fl4CheckBpNum (bp : Data) : NBKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4CheckBpNum _)

theorem nb_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4GetBreakpoint _ _)

theorem nb_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NBKE (check x0)) : NBKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; nb_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem nb_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqControlRemapped _ _ _)

theorem nb_fl4ArchCheckIrq (irq : Data) : NBKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ArchCheckIrq _)

theorem nb_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4IrqControl _ _ _ _ _)

theorem nb_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetBreakpoint _ _)

theorem nb_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NBKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetFlags _ _)

theorem nb_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NBKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetTimer _ _)

theorem nb_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4UnsetBreakpoint _ _)

theorem nb_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NBKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4TcbExt _ _ _ _ _)

theorem nb_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqControlInvocation _ _ _ _)

theorem nb_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NBKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqHandlerInvocation _ _ _)

theorem nb_getScReleased (scPtr : ObjRef) : NBK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScReleased _)

theorem nb_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextBind _ _)

theorem nb_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextUnbindObject _ _)

theorem nb_decodeSchedContextYieldTo (scPtr : ObjRef) : NBKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextYieldTo _)

theorem nb_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextInvocation _ _ _)

theorem nb_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NBKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedControlInvocationFlags _ _ _)

theorem nb_rangeCheck (v minV maxV : Word) : NBKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_rangeCheck _ _ _)

theorem nb_decodeSetFlags (args : List Data) (cap : Cap) : NBKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetFlags _ _)

theorem nb_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NBKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetIpcBuffer _ _ _ _)

theorem nb_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetMcpriority _ _ _ _)

theorem nb_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetPriority _ _ _ _)

theorem nb_isBlocked (thread : ObjRef) : NBK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isBlocked _)

theorem nb_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NBKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUpdateSc _ _ _)

theorem nb_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetSchedParams _ _ _ _)

theorem nb_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NBKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetSpace _ _ _ _)

theorem nb_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetTimeoutEp _ _ _)

theorem nb_decodeSetTlsBase (args : List Data) (cap : Cap) : NBKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetTlsBase _ _)

theorem nb_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTcbConfigure _ _ _ _)

theorem nb_decodeUnbindNotification (cap : Cap) : NBKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem nb_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NBKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTcbInvocation _ _ _ _ _)

theorem nb_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NBKE (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUntypedInvocation _ _ _ _ _)

theorem nb_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NBKE (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeInvocation _ _ _ _ _ _ _ _)

theorem nb_decodePml4Flush (cap : ArchCap) : NBKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePml4Flush _)

theorem nb_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NBKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_frameMappingSlot _ _ _ _)

theorem nb_decodeTestAndClearAccessed (cap : ArchCap) : NBKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTestAndClearAccessed _)

theorem nb_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NBKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem nb_doNbrecvFailedTransfer (thread : ObjRef) : NBK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doNbrecvFailedTransfer _)

theorem nb_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NBK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getMrs _ _ _)

theorem nb_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NBK (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleArchFaultReply _ _ _ _)

theorem nb_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NBK (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleFaultReply _ _ _ _)

theorem nb_schedContextResume (scPtr : ObjRef) : NBK (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextResume _)

theorem nb_testPossibleSwitchTo (tcbPtr : ObjRef) : NBK (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_testPossibleSwitchTo _)

theorem nb_restart (thread : ObjRef) : NBK (restart (Z := Unit) thread) := by
  unfold restart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_restart _)

theorem nb_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : NBK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doReplyTransfer _ _ _)

theorem nb_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NBK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_domainScheduleConfigure _ _ _)

theorem nb_setNextInterrupt  : NBK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setNextInterrupt)

theorem nb_switchSchedContext  : NBK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchSchedContext)

theorem nb_scAndTimer  : NBK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scAndTimer)

theorem nb_scheduleChooseNewThread  : NBK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleChooseNewThread)

theorem nb_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NBK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleSwitchThreadFastfail _ _ _ _)

theorem nb_schedule  : NBK (schedule (Z := Unit)) := by
  unfold schedule; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedule)

theorem nb_domainSetStart (index : Nat) : NBK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_domainSetStart _)

theorem nb_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem nb_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NBKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem nb_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NBKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem nb_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NBK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ReplyFromKernelError _ _ _)

theorem nb_fl4SyscallFaultIP (thread : ObjRef) : NBK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4SyscallFaultIP _)

theorem nb_getCapReg (reg : Register) : NBK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getCapReg _)

theorem nb_handleNoFault (tptr : ObjRef) : NBK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleNoFault _)

theorem nb_handleFault (thread : ObjRef) (ex : Fault) : NBK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleFault _ _)

theorem nb_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NBK (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleHypervisorFault _ _)

theorem nb_handleReservedIrq (_irq : Irq) : NBK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleReservedIrq _)

theorem nb_handleSpuriousIrq  : NBK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleSpuriousIrq)

theorem nb_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NBKE (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleVmFault _ _)

theorem nb_handleYield  : NBK (handleYield (Z := Unit)) := by
  unfold handleYield; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleYield)

theorem nb_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NBK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_initArchObjects _ _ _ _ _ _)

theorem nb_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NBKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_installTcbCap _ _ _ _)

theorem nb_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NBKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_installTcbFrameCap _ _ _)

theorem nb_invokeCnode (i : CnodeInvocation) : NBKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeCnode _)

theorem nb_threadSetDomain (tptr : ObjRef) (domain : Domain) : NBK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadSetDomain _ _)

theorem nb_setDomain (tptr : ObjRef) (newDom : Domain) : NBK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setDomain _ _)

theorem nb_invokeSetDomain (thread : ObjRef) (domain : Domain) : NBK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeSetDomain _ _)

theorem nb_invokeDomain (domInv : DomainInvocation) : NBK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeDomain _)

theorem nb_invokeIrqControl (a0 : IrqControlInvocation) : NBKE (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeIrqControl _)

theorem nb_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NBKE (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeFl4IrqControl _)

theorem nb_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NBKE (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeFl4Tcb _)

theorem nb_invokeIrqHandler (a0 : IrqHandlerInvocation) : NBK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeIrqHandler _)

theorem nb_maybeAddEmptyTail (scPtr : ObjRef) : NBK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeAddEmptyTail _)

theorem nb_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NBK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillNew _ _ _ _)

theorem nb_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NBK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillUpdate _ _ _ _)

theorem nb_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NBK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeSchedControlConfigureFlags _)

theorem nb_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NBK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextBindTcb _ _)

theorem nb_setFlags (ref : ObjRef) (flags : TcbFlags) : NBK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setFlags _ _)

theorem nb_setMcpriority (ref : ObjRef) (mcp : Priority) : NBK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setMcpriority _ _)

theorem nb_reorderEp (epPtr tptr : ObjRef) : NBK (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_reorderEp _ _)

theorem nb_threadSetPriority (tptr : ObjRef) (prio : Priority) : NBK (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadSetPriority _ _)

theorem nb_setPriority (tptr : ObjRef) (prio : Priority) : NBK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPriority _ _)

theorem nb_invokeTcb (a0 : TcbInvocation) : NBKE (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeTcb _)

theorem nb_lookupReply  : NBKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupReply)

theorem nb_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NBK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeDonateSc _ _)

theorem nb_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NBK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeReturnSc _ _)

theorem nb_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NBK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storeAsidPoolEntry _ _ _)

theorem nb_performAsidPoolInvocation (iv : AsidPoolInvocation) : NBK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performAsidPoolInvocation _)

theorem nb_performDeriveSubframe (iv : Fl4SubframeInvocation) : NBK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performDeriveSubframe _)

theorem nb_portIn (f : MachineMonad Data) : NBK (portIn (Z := Unit) f) := by
  unfold portIn; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_portIn _)

theorem nb_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NBK (portOut (Z := Unit) f w) := by
  unfold portOut; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_portOut _ _)

theorem nb_performIoPortInvocation (i : IoPortInvocation) : NBK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performIoPortInvocation _)

theorem nb_performIoportControlInvocation (i : IoPortControlInvocation) : NBK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performIoportControlInvocation _)

theorem nb_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NBK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageDirectoryInvocation _)

theorem nb_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NBK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageInvocationUnmap _ _)

theorem nb_performPageInvocation (iv : PageInvocation) : NBK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageInvocation _)

theorem nb_performPageTableInvocation (iv : PageTableInvocation) : NBK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageTableInvocation _)

theorem nb_performPdptInvocation (iv : PdptInvocation) : NBK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPdptInvocation _)

theorem nb_performPml4Flush (a0 : Fl4Pml4Invocation) : NBK (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPml4Flush _)

theorem nb_performTestAndClearAccessed (_slot : ObjRef) : NBK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performTestAndClearAccessed _)

theorem nb_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : NBK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_receiveIpcBlocked _ _ _ _)

theorem nb_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : NBK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_receiveSignalBlocked _ _ _)

theorem nb_returnConsumed (scPtr : ObjRef) : NBK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_returnConsumed _)

theorem nb_schedContextYieldTo (scPtr : ObjRef) : NBK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextYieldTo _)

theorem nb_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NBKE mFault) (h_hFault : ∀ x0, NBK (hFault x0)) (h_mError : ∀ x0, NBKE (mError x0)) (h_hError : ∀ x0, NBK (hError x0)) (h_mFinalise : ∀ x0, NBKE (mFinalise x0)) : NBKE (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; nb_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem nb_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NBK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateWaitingNtfn _ _ _)
