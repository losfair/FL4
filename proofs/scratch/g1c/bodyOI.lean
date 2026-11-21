theorem oi_archActivateIdleThread (_t : ObjRef) : OIK N (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archActivateIdleThread _)

theorem oi_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : OIK N (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadGet _ _)

theorem oi_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : OIK N (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getTcbObjRef _ _)

theorem oi_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : OIK N (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateSchedContext _ _)

theorem oi_schedContextCancelYieldTo (thread : ObjRef) : OIK N (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextCancelYieldTo _)

theorem oi_getCap (a0 : CslotPtr) : OIK N (getCap (Z := Unit) a0) := by
  unfold getCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getCap _)

theorem oi_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : OIK N (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupIpcBuffer _ _)

theorem oi_setMessageInfo (thread : ObjRef) (info : MessageInfo) : OIK N (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setMessageInfo _ _)

theorem oi_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : OIK N (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storeWordOffs _ _ _)

theorem oi_replyFromKernel (thread : ObjRef) (x : Data × List Data) : OIK N (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyFromKernel _ _)

theorem oi_getSchedContext (ptr : ObjRef) : OIK N (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSchedContext _)

theorem oi_schedContextUpdateConsumed (scPtr : ObjRef) : OIK N (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUpdateConsumed _)

theorem oi_setConsumed (scPtr tcbPtr : ObjRef) : OIK N (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setConsumed _ _)

theorem oi_completeYieldTo (tcbPtr : ObjRef) : OIK N (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_completeYieldTo _)

theorem oi_getThreadState (ref : ObjRef) : OIK N (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getThreadState _)

theorem oi_setSchedulerAction (action : SchedulerAction) : OIK N (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setSchedulerAction _)

theorem oi_setThreadStateAct (tcbPtr : ObjRef) : OIK N (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setThreadStateAct _)

theorem oi_activateThread  : OIK N (activateThread (Z := Unit)) := by
  unfold activateThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_activateThread)

theorem oi_archCheckIrq (_irq : Data) : OIKE N (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archCheckIrq _)

theorem oi_ensureEmpty (slot : CslotPtr) : OIKE N (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ensureEmpty _)

theorem oi_isIoportRangeFree (f l : IoPort) : OIK N (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isIoportRangeFree _ _)

theorem oi_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : OIKE N m) : OIKE N (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_lookupErrorOnFailure _ _ ?_)

theorem oi_resolveAddressBits' (p : Cap × CapRef) : OIKE N (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by oi_auto)) fun nc => ?_
        split
        · exact oi_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_resolveAddressBits' _)

theorem oi_resolveAddressBits (a0 : Cap × CapRef) : OIKE N (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_resolveAddressBits _)

theorem oi_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : OIKE N (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupSlotForCnodeOp _ _ _ _)

theorem oi_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OIKE N (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupTargetSlot _ _ _)

theorem oi_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : OIKE N (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIoportControlInvocation _ _ _ _ _)

theorem oi_getAsidPool (ptr : ObjRef) : OIK N (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getAsidPool _)

theorem oi_findVspaceForAsid (asid : Asid) : OIKE N (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_findVspaceForAsid _)

theorem oi_getPdpt (ptr : ObjRef) : OIK N (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPdpt _)

theorem oi_getPdpte (ptr : ObjRef) : OIK N (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPdpte _)

theorem oi_isFinalCap (cap : Cap) : OIK N (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isFinalCap _)

theorem oi_getPml4 (ptr : ObjRef) : OIK N (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPml4 _)

theorem oi_getPml4e (ptr : ObjRef) : OIK N (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPml4e _)

theorem oi_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : OIKE N (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupPdptSlot _ _)

theorem oi_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePageDirectoryInvocation _ _ _ _ _)

theorem oi_checkVpAlignment (sz : VMPageSize) (vptr : Word) : OIKE N (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkVpAlignment _ _)

theorem oi_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : OIKE N (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupPdSlot _ _)

theorem oi_getPd (ptr : ObjRef) : OIK N (getPd (Z := Unit) ptr) := by
  unfold getPd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPd _)

theorem oi_getPde (ptr : ObjRef) : OIK N (getPde (Z := Unit) ptr) := by
  unfold getPde; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPde _)

theorem oi_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : OIKE N (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupPtSlot _ _)

theorem oi_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : OIKE N (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_createMappingEntries _ _ _ _ _ _)

theorem oi_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : OIKE N (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ensureSafeMapping _)

theorem oi_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePageInvocation _ _ _ _ _)

theorem oi_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePageTableInvocation _ _ _ _ _)

theorem oi_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePdptInvocation _ _ _ _ _)

theorem oi_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : OIKE N (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ensurePortOperationAllowed _ _ _)

theorem oi_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : OIKE N (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePortInvocation _ _ _)

theorem oi_ensureNoChildren (cslotPtr : CslotPtr) : OIKE N (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ensureNoChildren _)

theorem oi_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : OIK N (selectExt (Z := Unit) a S) := by
  unfold selectExt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_selectExt _ _)

theorem oi_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archDecodeInvocation _ _ _ _ _ _)

theorem oi_getIrqState (irq : Irq) : OIK N (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getIrqState _)

theorem oi_isIrqActive (irq : Irq) : OIK N (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isIrqActive _)

theorem oi_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archDecodeIrqControlInvocation _ _ _ _)

theorem oi_archDeriveCap (c : ArchCap) : OIKE N (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archDeriveCap _)

theorem oi_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : OIK N (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_hwAsidInvalidate _ _)

theorem oi_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : OIK N (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setAsidPool _ _)

theorem oi_getCurrentCr3  : OIK N (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getCurrentCr3)

theorem oi_setCurrentCr3 (c : Cr3) : OIK N (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setCurrentCr3 _)

theorem oi_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : OIK N (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setCurrentVspaceRoot _ _)

theorem oi_setVmRoot (tcb : ObjRef) : OIK N (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setVmRoot _)

theorem oi_deleteAsid (asid : Asid) (pml4 : ObjRef) : OIK N (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deleteAsid _ _)

theorem oi_deleteAsidPool (base : Asid) (ptr : ObjRef) : OIK N (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deleteAsidPool _ _)

theorem oi_getPt (ptr : ObjRef) : OIK N (getPt (Z := Unit) ptr) := by
  unfold getPt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPt _)

theorem oi_getPte (ptr : ObjRef) : OIK N (getPte (Z := Unit) ptr) := by
  unfold getPte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getPte _)

theorem oi_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : OIK N (setPd (Z := Unit) ptr pd) := by
  unfold setPd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPd _ _)

theorem oi_storePde (p : ObjRef) (pde : PDE) : OIK N (storePde (Z := Unit) p pde) := by
  unfold storePde; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePde _ _)

theorem oi_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : OIK N (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPdpt _ _)

theorem oi_storePdpte (p : ObjRef) (pte : PDPTE) : OIK N (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePdpte _ _)

theorem oi_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : OIK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPt _ _)

theorem oi_storePte (p : ObjRef) (pte : PTE) : OIK N (storePte (Z := Unit) p pte) := by
  unfold storePte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePte _ _)

theorem oi_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : OIK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPage _ _ _ _)

theorem oi_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : OIK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushTable _ _ _ _)

theorem oi_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : OIK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invalidatePageStructureCacheAsid _ _)

theorem oi_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : OIK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPageTable _ _ _)

theorem oi_flushAll (vspace : ObjRef) (asid : Asid) : OIK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushAll _ _)

theorem oi_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : OIK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPd _ _ _)

theorem oi_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : OIK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPml4 _ _)

theorem oi_storePml4e (p : ObjRef) (pte : PML4E) : OIK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePml4e _ _)

theorem oi_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : OIK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPdpt _ _ _)

theorem oi_archFinaliseCap (c : ArchCap) (x : Bool) : OIK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archFinaliseCap _ _)

theorem oi_archGetSanitiseRegisterInfo (_t : ObjRef) : OIK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archGetSanitiseRegisterInfo _)

theorem oi_setOriginal (slot : CslotPtr) (v : Bool) : OIK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setOriginal _ _)

theorem oi_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : OIK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setUntypedCapAsFull _ _ _)

theorem oi_setCdt (t : Cdt) : OIK N (setCdt (Z := Unit) t) := by
  unfold setCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setCdt _)

theorem oi_updateCdt (f : Cdt → Cdt) : OIK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateCdt _)

theorem oi_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capInsert _ _ _)

theorem oi_setIrqState (state : IrqState) (irq : Irq) : OIK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIrqState _ _)

theorem oi_updateIrqState (irq : Irq) (irqState : X64IRQState) : OIK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateIrqState _ _)

theorem oi_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : OIK N m) : OIKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_withoutPreemption _ ?_)

theorem oi_archInvokeIrqControl (aic : ArchIrqControlInvocation) : OIKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqControl _)

theorem oi_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : OIK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqHandler _)

theorem oi_archMaskIrqSignal (irq : Irq) : OIK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archMaskIrqSignal _)

theorem oi_performAsidControlInvocation (iv : AsidControlInvocation) : OIK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performAsidControlInvocation _)

theorem oi_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : OIK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storeAsidPoolEntry _ _ _)

theorem oi_performAsidPoolInvocation (iv : AsidPoolInvocation) : OIK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performAsidPoolInvocation _)

theorem oi_portIn (f : MachineMonad Data) : OIK N (portIn (Z := Unit) f) := by
  unfold portIn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portIn _)

theorem oi_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : OIK N (portOut (Z := Unit) f w) := by
  unfold portOut; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portOut _ _)

theorem oi_performIoPortInvocation (i : IoPortInvocation) : OIK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoPortInvocation _)

theorem oi_setIoportMask (f l : IoPort) (val : Bool) : OIK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIoportMask _ _ _)

theorem oi_performIoportControlInvocation (i : IoPortControlInvocation) : OIK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoportControlInvocation _)

theorem oi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : OIK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageDirectoryInvocation _)

theorem oi_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : OIK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocationUnmap _ _)

theorem oi_performPageInvocation (iv : PageInvocation) : OIK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocation _)

theorem oi_performPageTableInvocation (iv : PageTableInvocation) : OIK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageTableInvocation _)

theorem oi_performPdptInvocation (iv : PdptInvocation) : OIK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPdptInvocation _)

theorem oi_archPerformInvocation (i : ArchInvocation) : OIKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPerformInvocation _)

theorem oi_freeIoportRange (f l : IoPort) : OIK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_freeIoportRange _ _)

theorem oi_archPostCapDeletion (ac : ArchCap) : OIK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostCapDeletion _)

theorem oi_archPostModifyRegisters (cur t : ObjRef) : OIK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostModifyRegisters _ _)

theorem oi_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : OIK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostResetUntyped _ _)

theorem oi_loadFpuState (t : ObjRef) : OIK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadFpuState _)

theorem oi_saveFpuState (t : ObjRef) : OIK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_saveFpuState _)

theorem oi_setX64CurrentFpuOwner (newOwner : Option ObjRef) : OIK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setX64CurrentFpuOwner _)

theorem oi_switchLocalFpuOwner (newOwner : Option ObjRef) : OIK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchLocalFpuOwner _)

theorem oi_fpuRelease (threadPtr : ObjRef) : OIK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fpuRelease _)

theorem oi_lazyFpuRestore (threadPtr : ObjRef) : OIK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lazyFpuRestore _)

theorem oi_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : OIK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostSetFlags _ _)

theorem oi_archPrepareNextDomain  : OIK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPrepareNextDomain)

theorem oi_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : OIK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPrepareSetDomain _ _)

theorem oi_archSwitchToIdleThread  : OIK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archSwitchToIdleThread)

theorem oi_archSwitchToThread (t : ObjRef) : OIK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archSwitchToThread _)

theorem oi_getScRefillReady (scPtr : ObjRef) : OIK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillReady _)

theorem oi_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : OIK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillSufficient _ _)

theorem oi_getTcbQueue (d : Domain) (prio : Priority) : OIK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getTcbQueue _ _)

theorem oi_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : OIK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setTcbQueue _ _ _)

theorem oi_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : OIK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbSchedAction _ _)

theorem oi_rescheduleRequired  : OIK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_rescheduleRequired)

theorem oi_possibleSwitchTo (target : ObjRef) : OIK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_possibleSwitchTo _)

theorem oi_tcbReleaseRemove (tcbPtr : ObjRef) : OIK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseRemove _)

theorem oi_tcbReleaseDequeue  : OIK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseDequeue)

theorem oi_awaken  : OIK N (awaken (Z := Unit)) := by
  unfold awaken; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_awaken)

theorem oi_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : OIK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSimpleKo _ _)

theorem oi_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : OIK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateSkObjRef _ _ _ _)

theorem oi_bindNotification (tcbptr ntfnptr : ObjRef) : OIK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindNotification _ _)

theorem oi_bindScReply (scPtr replyPtr : ObjRef) : OIK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindScReply _ _)

theorem oi_getBlockingObject (state : ThreadState) : OIK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getBlockingObject _)

theorem oi_replyUnlinkTcb (t r : ObjRef) : OIK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkTcb _ _)

theorem oi_tcbEpDequeue (tptr epPtr : ObjRef) : OIK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbEpDequeue _ _)

theorem oi_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : OIK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_blockedCancelIpc _ _ _)

theorem oi_isRoundRobin (scPtr : ObjRef) : OIK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isRoundRobin _)

theorem oi_getRefillHead (scPtr : ObjRef) : OIK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefillHead _)

theorem oi_refillPopHead (scPtr : ObjRef) : OIK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillPopHead _)

theorem oi_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : OIK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRefillHd _ _)

theorem oi_mergeOverlappingRefills (scPtr : ObjRef) : OIK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_mergeOverlappingRefills _)

theorem oi_refillHeadOverlappingLoop (scPtr : ObjRef) : OIK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillHeadOverlappingLoop _)

theorem oi_refillUnblockCheck (scPtr : ObjRef) : OIK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUnblockCheck _)

theorem oi_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : OIK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ifCondRefillUnblockCheck _ _ _)

theorem oi_restartThreadIfNoFault (t : ObjRef) : OIK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_restartThreadIfNoFault _)

theorem oi_removeAndRestartEpQueuedThread (t epptr : ObjRef) : OIK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartEpQueuedThread _ _)

theorem oi_cancelAllIpc (epptr : ObjRef) : OIK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllIpc _)

theorem oi_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : OIK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnDequeue _ _)

theorem oi_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : OIK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartNtfnQueuedThread _ _)

theorem oi_cancelAllSignals (ntfnptr : ObjRef) : OIK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllSignals _)

theorem oi_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : OIK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartBadgedThread _ _ _)

theorem oi_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : OIK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelBadgedSends _ _)

theorem oi_cancelSignal (threadptr ntfnptr : ObjRef) : OIK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelSignal _ _)

theorem oi_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : OIK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSkObjRef _ _ _)

theorem oi_replyRemoveTcb (tptr rptr : ObjRef) : OIK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemoveTcb _ _)

theorem oi_cancelIpc (tptr : ObjRef) : OIK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelIpc _)

theorem oi_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : OIK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwap _ _ _ _)

theorem oi_capSwapForDelete (slot1 slot2 : CslotPtr) : OIK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwapForDelete _ _)

theorem oi_deletedIrqHandler (irq : Irq) : OIK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletedIrqHandler _)

theorem oi_postCapDeletion (cap : Cap) : OIK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_postCapDeletion _)

theorem oi_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : OIK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_emptySlot _ _)

theorem oi_replyUnlinkSc (scPtr replyPtr : ObjRef) : OIK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkSc _ _)

theorem oi_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : OIK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScObjRef _ _)

theorem oi_testReschedule (fromTptr : ObjRef) : OIK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_testReschedule _)

theorem oi_schedContextDonate (scPtr tcbPtr : ObjRef) : OIK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextDonate _ _)

theorem oi_replyRemove (caller r : ObjRef) : OIK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemove _ _)

theorem oi_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : OIK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextMaybeUnbindNtfn _)

theorem oi_unbindMaybeNotification (ntfnptr : ObjRef) : OIK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindMaybeNotification _)

theorem oi_fastFinalise (a0 : Cap) (a1 : Bool) : OIK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fastFinalise _ _)

theorem oi_capDeleteOne (slot : CslotPtr) : OIK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capDeleteOne _)

theorem oi_getIrqSlot (irq : Irq) : OIK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getIrqSlot _)

theorem oi_deletingIrqHandler (irq : Irq) : OIK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletingIrqHandler _)

theorem oi_prepareThreadDelete (threadPtr : ObjRef) : OIK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_prepareThreadDelete _)

theorem oi_schedContextSetInactive (scPtr : ObjRef) : OIK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextSetInactive _)

theorem oi_schedContextUnbindTcb (scPtr : ObjRef) : OIK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindTcb _)

theorem oi_schedContextUnbindAllTcbs (scPtr : ObjRef) : OIK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindAllTcbs _)

theorem oi_schedContextUnbindNtfn (scPtr : ObjRef) : OIK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindNtfn _)

theorem oi_schedContextUnbindReply (scPtr : ObjRef) : OIK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindReply _)

theorem oi_schedContextUnbindYieldFrom (scPtr : ObjRef) : OIK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindYieldFrom _)

theorem oi_updateRestartPc (threadPtr : ObjRef) : OIK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRestartPc _)

theorem oi_suspend (thread : ObjRef) : OIK N (suspend (Z := Unit) thread) := by
  unfold suspend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_suspend _)

theorem oi_unbindFromSc (tcbPtr : ObjRef) : OIK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindFromSc _)

theorem oi_unbindNotification (tcb : ObjRef) : OIK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindNotification _)

theorem oi_finaliseCap (a0 : Cap) (a1 : Bool) : OIK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_finaliseCap _ _)

theorem oi_getScActive (scPtr : ObjRef) : OIK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScActive _)

theorem oi_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : OIKE N f) (h_g : OIKE N g) : OIKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; oi_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_orChoiceE _ _ _ ?_ ?_)

theorem oi_updateTimeStamp  : OIK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateTimeStamp)

theorem oi_preemptionPoint  : OIKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem oi_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, OIK N (f k)) (k : RecDelCall) : OIKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, OIKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; oi_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; oi_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> oi_auto
    all_goals exact hrec' _

theorem oi_recDel (c : RecDelCall) : OIKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => oi_recDelF hf k) c
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_recDel _)

theorem oi_capDelete (slot : CslotPtr) : OIKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capDelete _)

theorem oi_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : OIKE N m) : OIKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_capFaultOnFailure _ _ _ ?_)

theorem oi_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem oi_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, OIK N (f k)) (sl : CslotPtr) : OIKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, OIKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  oi_auto
  all_goals exact hrec' _

theorem oi_capRevoke (sl : CslotPtr) : OIKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => oi_capRevokeF hf k) sl
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capRevoke _)

theorem oi_captransferFromWords (ptr : Word) : OIK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_captransferFromWords _)

theorem oi_isValidTimeoutHandler (tptr : ObjRef) : OIK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isValidTimeoutHandler _)

theorem oi_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : OIK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeArchFaultMsg _ _)

theorem oi_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : OIK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeFaultMsg _ _)

theorem oi_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : OIK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doFaultTransfer _ _ _ _)

theorem oi_loadWordOffs (ptr : ObjRef) (offs : Nat) : OIK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadWordOffs _ _)

theorem oi_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : OIK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_copyMrs _ _ _ _ _)

theorem oi_getMessageInfo (thread : ObjRef) : OIK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getMessageInfo _)

theorem oi_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : OIK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; oi_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getExtraCptrs _ _)

theorem oi_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : OIKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupSlotForThread _ _)

theorem oi_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : OIKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupCapAndSlot _ _)

theorem oi_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : OIKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupExtraCaps _ _ _)

theorem oi_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : OIKE N m) : OIK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_emptyOnFailure _ ?_)

theorem oi_loadCapTransfer (buffer : ObjRef) : OIK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadCapTransfer _)

theorem oi_lookupCap (thread : ObjRef) (ref : CapRef) : OIKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupCap _ _)

theorem oi_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : OIKE N m) : OIKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_unifyFailure _ ?_)

theorem oi_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : OIK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getReceiveSlots _ _)

theorem oi_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : OIKE N m) : OIK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_constOnFailure _ _ ?_)

theorem oi_deriveCap (slot : CslotPtr) (cap : Cap) : OIKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deriveCap _ _)

theorem oi_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : OIK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setExtraBadge _ _ _)

theorem oi_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      OIK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; oi_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => oi_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | oi_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_transferCapsLoop _ _ _ _ _ _)

theorem oi_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : OIK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_transferCaps _ _ _ _ _)

theorem oi_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : OIK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doNormalTransfer _ _ _ _ _ _ _)

theorem oi_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : OIK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doIpcTransfer _ _ _ _ _)

theorem oi_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : OIK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyPush _ _ _ _)

theorem oi_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : OIK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_orderedInsert _ _ _ _)

theorem oi_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : OIK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbAppend _ _)

theorem oi_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : OIK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbEpAppend _ _ _)

theorem oi_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : OIK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendIpcBlocked _ _ _ _ _ _)

theorem oi_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : OIK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendIpc _ _ _ _ _ _ _ _)

theorem oi_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : OIK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendFaultIpc _ _ _ _)

theorem oi_handleTimeout (tptr : ObjRef) (ex : Fault) : OIK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleTimeout _ _)

theorem oi_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : OIK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_readyTimesAppend _ _)

theorem oi_tcbReleaseEnqueue (tcbPtr : ObjRef) : OIK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseEnqueue _)

theorem oi_postpone (scPtr : ObjRef) : OIK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_postpone _)

theorem oi_endTimeslice (canTimeout : Bool) : OIK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_endTimeslice _)

theorem oi_getRefills (scPtr : ObjRef) : OIK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefills _)

theorem oi_refillSize (scPtr : ObjRef) : OIK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillSize _)

theorem oi_refillSingle (scPtr : ObjRef) : OIK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillSingle _)

theorem oi_getRefillTail (scPtr : ObjRef) : OIK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefillTail _)

theorem oi_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : OIK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillAddTail _ _)

theorem oi_refillFull (scPtr : ObjRef) : OIK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillFull _)

theorem oi_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : OIK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRefillTl _ _)

theorem oi_scheduleUsed (scPtr : ObjRef) (new : Refill) : OIK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleUsed _ _)

theorem oi_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : OIK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_chargeEntireHeadRefill _ _)

theorem oi_handleOverrun (scPtr : ObjRef) (usage : Ticks) : OIK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleOverrun _ _)

theorem oi_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : OIK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_mergeNonoverlappingHeadRefill _)

theorem oi_headInsufficientLoop (scPtr : ObjRef) : OIK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_headInsufficientLoop _)

theorem oi_refillBudgetCheck (usage : Ticks) : OIK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillBudgetCheck _)

theorem oi_refillResetRr (cscPtr : ObjRef) : OIK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillResetRr _)

theorem oi_chargeBudget (consumed : Ticks) (canTimeout : Bool) : OIK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_chargeBudget _ _)

theorem oi_checkBudget  : OIK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkBudget)

theorem oi_checkBudgetRestart  : OIK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkBudgetRestart)

theorem oi_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : OIK N m) : OIK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_checkCapAt _ _ _ ?_)

theorem oi_checkDomainTime  : OIK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkDomainTime)

theorem oi_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : OIKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkHandlerEp _ _)

theorem oi_checkPrio (newPrio : Data) (authTcb : ObjRef) : OIKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkPrio _ _)

theorem oi_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : OIKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkValidIpcBuffer _ _)

theorem oi_nextDomain  : OIK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_nextDomain)

theorem oi_switchToThread (t : ObjRef) : OIK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchToThread _)

theorem oi_guardedSwitchTo (thread : ObjRef) : OIK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_guardedSwitchTo _)

theorem oi_switchToIdleThread  : OIK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchToIdleThread)

theorem oi_chooseThread  : OIK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_chooseThread)

theorem oi_refillBudgetCheckRoundRobin (usage : Ticks) : OIK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillBudgetCheckRoundRobin _)

theorem oi_commitTime  : OIK N (commitTime (Z := Unit)) := by
  unfold commitTime; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_commitTime)

theorem oi_schedContextResume (scPtr : ObjRef) : OIK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextResume _)

theorem oi_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : OIK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeDonateSc _ _)

theorem oi_completeSignal (ntfnptr tptr : ObjRef) : OIK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_completeSignal _ _)

theorem oi_copyGlobalMappings (newPm : ObjRef) : OIK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_copyGlobalMappings _)

theorem oi_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : OIK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_createCap _ _ _ _ _)

theorem oi_dataToObjType (type : Data) : OIKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_dataToObjType _)

theorem oi_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeBindNotification _ _)

theorem oi_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OIKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupPivotSlot _ _ _)

theorem oi_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OIKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupSourceSlot _ _ _)

theorem oi_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : OIKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeCnodeInvocation _ _ _ _)

theorem oi_slotCapLongRunningDelete (slot : CslotPtr) : OIK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_slotCapLongRunningDelete _)

theorem oi_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeCvSpace _ _ _ _)

theorem oi_subframeNode (nodeCap : Cap) (index depth : Data) : OIKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_subframeNode _ _ _)

theorem oi_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDeriveSubframe _ _ _ _)

theorem oi_decodeDomainScheduleConfigure (args : List Data) : OIKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainScheduleConfigure _)

theorem oi_decodeDomainScheduleSetStart (args : List Data) : OIKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainScheduleSetStart _)

theorem oi_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : OIKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainSet _ _)

theorem oi_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : OIKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainInvocation _ _ _)

theorem oi_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : OIK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4GetMr _ _ _)

theorem oi_fl4Arg (buf : Option ObjRef) (i : Nat) : OIKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4Arg _ _)

theorem oi_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4ConfigureSingleStepping _ _)

theorem oi_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4FpuTransfer _ _ _ _)

theorem oi_fl4CheckBpNum (bp : Data) : OIKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4CheckBpNum _)

theorem oi_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4GetBreakpoint _ _)

theorem oi_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, OIKE N (check x0)) : OIKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; oi_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem oi_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqControlRemapped _ _ _)

theorem oi_fl4ArchCheckIrq (irq : Data) : OIKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchCheckIrq _)

theorem oi_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4IrqControl _ _ _ _ _)

theorem oi_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetBreakpoint _ _)

theorem oi_decodeFl4SetFlags (args : List Data) (t : ObjRef) : OIKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetFlags _ _)

theorem oi_decodeFl4SetTimer (args : List Data) (t : ObjRef) : OIKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetTimer _ _)

theorem oi_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4UnsetBreakpoint _ _)

theorem oi_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : OIKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4TcbExt _ _ _ _ _)

theorem oi_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqControlInvocation _ _ _ _)

theorem oi_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : OIKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqHandlerInvocation _ _ _)

theorem oi_getScReleased (scPtr : ObjRef) : OIK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScReleased _)

theorem oi_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextBind _ _)

theorem oi_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextUnbindObject _ _)

theorem oi_decodeSchedContextYieldTo (scPtr : ObjRef) : OIKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextYieldTo _)

theorem oi_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextInvocation _ _ _)

theorem oi_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : OIKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedControlInvocationFlags _ _ _)

theorem oi_rangeCheck (v minV maxV : Word) : OIKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_rangeCheck _ _ _)

theorem oi_decodeSetFlags (args : List Data) (cap : Cap) : OIKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetFlags _ _)

theorem oi_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : OIKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetIpcBuffer _ _ _ _)

theorem oi_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetMcpriority _ _ _ _)

theorem oi_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetPriority _ _ _ _)

theorem oi_isBlocked (thread : ObjRef) : OIK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isBlocked _)

theorem oi_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : OIKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUpdateSc _ _ _)

theorem oi_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetSchedParams _ _ _ _)

theorem oi_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetSpace _ _ _ _)

theorem oi_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetTimeoutEp _ _ _)

theorem oi_decodeSetTlsBase (args : List Data) (cap : Cap) : OIKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetTlsBase _ _)

theorem oi_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTcbConfigure _ _ _ _)

theorem oi_decodeUnbindNotification (cap : Cap) : OIKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem oi_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : OIKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTcbInvocation _ _ _ _ _)

theorem oi_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OIKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUntypedInvocation _ _ _ _ _)

theorem oi_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : OIKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeInvocation _ _ _ _ _ _ _ _)

theorem oi_decodePml4Flush (cap : ArchCap) : OIKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePml4Flush _)

theorem oi_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : OIKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_frameMappingSlot _ _ _ _)

theorem oi_decodeTestAndClearAccessed (cap : ArchCap) : OIKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTestAndClearAccessed _)

theorem oi_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OIKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem oi_doNbrecvFailedTransfer (thread : ObjRef) : OIK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doNbrecvFailedTransfer _)

theorem oi_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : OIK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getMrs _ _ _)

theorem oi_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : OIK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleArchFaultReply _ _ _ _)

theorem oi_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : OIK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleFaultReply _ _ _ _)

theorem oi_testPossibleSwitchTo (tcbPtr : ObjRef) : OIK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_testPossibleSwitchTo _)

theorem oi_restart (thread : ObjRef) : OIK N (restart (Z := Unit) thread) := by
  unfold restart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_restart _)

theorem oi_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : OIK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doReplyTransfer _ _ _)

theorem oi_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : OIK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_domainScheduleConfigure _ _ _)

theorem oi_setNextInterrupt  : OIK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setNextInterrupt)

theorem oi_switchSchedContext  : OIK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchSchedContext)

theorem oi_scAndTimer  : OIK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scAndTimer)

theorem oi_scheduleChooseNewThread  : OIK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleChooseNewThread)

theorem oi_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : OIK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleSwitchThreadFastfail _ _ _ _)

theorem oi_schedule  : OIK N (schedule (Z := Unit)) := by
  unfold schedule; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedule)

theorem oi_domainSetStart (index : Nat) : OIK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_domainSetStart _)

theorem oi_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem oi_performDeriveSubframe (iv : Fl4SubframeInvocation) : OIK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performDeriveSubframe _)

theorem oi_performPml4Flush (a0 : Fl4Pml4Invocation) : OIK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPml4Flush _)

theorem oi_performTestAndClearAccessed (_slot : ObjRef) : OIK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performTestAndClearAccessed _)

theorem oi_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : OIKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchPerformInvocation _)

theorem oi_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : OIK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateWaitingNtfn _ _ _)

theorem oi_sendSignal (ntfnptr : ObjRef) (badge : Badge) : OIK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendSignal _ _)

theorem oi_fl4Awaken : OIK N (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact oi_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem oi_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OIKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem oi_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : OIKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem oi_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : OIK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_initArchObjects _ _ _ _ _ _)

theorem oi_resetUntypedCap (srcSlot : CslotPtr) : OIKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_resetUntypedCap _)

theorem oi_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : OIKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeUntypedWith _ _)

theorem oi_invokeCnode (i : CnodeInvocation) : OIKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeCnode _)

theorem oi_threadSetDomain (tptr : ObjRef) (domain : Domain) : OIK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetDomain _ _)

theorem oi_setDomain (tptr : ObjRef) (newDom : Domain) : OIK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setDomain _ _)

theorem oi_invokeSetDomain (thread : ObjRef) (domain : Domain) : OIK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSetDomain _ _)

theorem oi_invokeDomain (domInv : DomainInvocation) : OIK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeDomain _)

theorem oi_invokeIrqControl (a0 : IrqControlInvocation) : OIKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqControl _)

theorem oi_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : OIKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeFl4IrqControl _)

theorem oi_invokeFl4Tcb (a0 : Fl4TcbInvocation) : OIKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeFl4Tcb _)

theorem oi_invokeIrqHandler (a0 : IrqHandlerInvocation) : OIK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqHandler _)

theorem oi_returnConsumed (scPtr : ObjRef) : OIK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_returnConsumed _)

theorem oi_schedContextBindNtfn (sc ntfn : ObjRef) : OIK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindNtfn _ _)

theorem oi_schedContextBindTcb (scPtr tcbPtr : ObjRef) : OIK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindTcb _ _)

theorem oi_schedContextYieldTo (scPtr : ObjRef) : OIK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextYieldTo _)

theorem oi_invokeSchedContext (iv : SchedContextInvocation) : OIK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedContext _)

theorem oi_maybeAddEmptyTail (scPtr : ObjRef) : OIK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeAddEmptyTail _)

theorem oi_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : OIK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillNew _ _ _ _)

theorem oi_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : OIK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUpdate _ _ _ _)

theorem oi_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : OIK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedControlConfigureFlags _)

theorem oi_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : OIKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_installTcbCap _ _ _ _)

theorem oi_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : OIKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_installTcbFrameCap _ _ _)

theorem oi_setFlags (ref : ObjRef) (flags : TcbFlags) : OIK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setFlags _ _)

theorem oi_setMcpriority (ref : ObjRef) (mcp : Priority) : OIK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setMcpriority _ _)

theorem oi_reorderEp (epPtr tptr : ObjRef) : OIK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderEp _ _)

theorem oi_reorderNtfn (ntfnPtr tptr : ObjRef) : OIK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderNtfn _ _)

theorem oi_threadSetPriority (tptr : ObjRef) (prio : Priority) : OIK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetPriority _ _)

theorem oi_setPriority (tptr : ObjRef) (prio : Priority) : OIK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPriority _ _)

theorem oi_invokeTcb (a0 : TcbInvocation) : OIKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeTcb _)

theorem oi_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : OIKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4PerformInvocation _ _ _ _)

theorem oi_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : OIK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ReplyFromKernelError _ _ _)

theorem oi_handleNoFault (tptr : ObjRef) : OIK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleNoFault _)

theorem oi_handleFault (thread : ObjRef) (ex : Fault) : OIK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleFault _ _)

theorem oi_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : OIKE N mFault) (h_hFault : ∀ x0, OIK N (hFault x0)) (h_mError : ∀ x0, OIKE N (mError x0)) (h_hError : ∀ x0, OIK N (hError x0)) (h_mFinalise : ∀ x0, OIKE N (mFinalise x0)) : OIKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; oi_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem oi_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : OIKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleInvocationR _ _ _ _ _ _)

theorem oi_getCapReg (reg : Register) : OIK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getCapReg _)

theorem oi_lookupReply  : OIKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupReply)

theorem oi_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : OIK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeReturnSc _ _)

theorem oi_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : OIK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem oi_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    OIK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpc _ _ _ _)

theorem oi_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : OIK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnAppend _ _)

theorem oi_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : OIK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignalBlocked _ _ _)

theorem oi_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : OIK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignal _ _ _)

theorem oi_handleRecv (isBlocking canReply : Bool) : OIK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleRecv _ _)

theorem oi_handleYield  : OIK N (handleYield (Z := Unit)) := by
  unfold handleYield; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleYield)

theorem oi_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : OIKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleSyscall _ _)

theorem oi_invokeUntyped (ui : UntypedInvocation) : OIKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeUntyped _)

theorem oi_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : OIKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performInvocation _ _ _ _)

theorem oi_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : OIKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleInvocation _ _ _ _ _)

theorem oi_handleCall  : OIKE N (handleCall (Z := Unit)) := by
  unfold handleCall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleCall)

theorem oi_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : OIK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleHypervisorFault _ _)

theorem oi_handleSend (bl : Bool) : OIKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleSend _)

theorem oi_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : OIKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleVmFault _ _)

theorem oi_handleReservedIrq (_irq : Irq) : OIK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleReservedIrq _)

theorem oi_handleInterrupt (irq : Irq) : OIK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleInterrupt _)

theorem oi_handleSpuriousIrq  : OIK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleSpuriousIrq)

theorem oi_maybeHandleInterrupt (inKernel : Bool) : OIK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeHandleInterrupt _)

theorem oi_handleEvent (a0 : Event) : OIKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleEvent _)

theorem oi_fl4HandleEvent (rep : Bool) (a0 : Event) : OIKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleEvent _ _)

theorem oi_preemptionPath  : OIK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPath)

theorem oi_fl4CallKernel (rep : Bool) (ev : Event) : OIK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4CallKernel _ _)

theorem oi_fl4SyscallFaultIP (thread : ObjRef) : OIK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4SyscallFaultIP _)

theorem oi_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : OIK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4KernelEntrySyscall _ _)
