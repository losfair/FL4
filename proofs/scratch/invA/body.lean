theorem ns_archActivateIdleThread (_t : ObjRef) : NSK (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archActivateIdleThread _)

theorem ns_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : NSK (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_threadGet _ _)

theorem ns_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : NSK (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getTcbObjRef _ _)

theorem ns_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : NSK (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateSchedContext _ _)

theorem ns_schedContextCancelYieldTo (thread : ObjRef) : NSK (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextCancelYieldTo _)

theorem ns_getCap (a0 : CslotPtr) : NSK (getCap (Z := Unit) a0) := by
  unfold getCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getCap _)

theorem ns_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : NSK (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupIpcBuffer _ _)

theorem ns_setMessageInfo (thread : ObjRef) (info : MessageInfo) : NSK (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setMessageInfo _ _)

theorem ns_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : NSK (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storeWordOffs _ _ _)

theorem ns_replyFromKernel (thread : ObjRef) (x : Data × List Data) : NSK (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyFromKernel _ _)

theorem ns_getSchedContext (ptr : ObjRef) : NSK (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getSchedContext _)

theorem ns_schedContextUpdateConsumed (scPtr : ObjRef) : NSK (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUpdateConsumed _)

theorem ns_setConsumed (scPtr tcbPtr : ObjRef) : NSK (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setConsumed _ _)

theorem ns_completeYieldTo (tcbPtr : ObjRef) : NSK (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_completeYieldTo _)

theorem ns_getThreadState (ref : ObjRef) : NSK (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getThreadState _)

theorem ns_setSchedulerAction (action : SchedulerAction) : NSK (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setSchedulerAction _)

theorem ns_setThreadStateAct (tcbPtr : ObjRef) : NSK (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setThreadStateAct _)

theorem ns_activateThread  : NSK (activateThread (Z := Unit)) := by
  unfold activateThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_activateThread)

theorem ns_archCheckIrq (_irq : Data) : NSKE (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archCheckIrq _)

theorem ns_ensureEmpty (slot : CslotPtr) : NSKE (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ensureEmpty _)

theorem ns_isIoportRangeFree (f l : IoPort) : NSK (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isIoportRangeFree _ _)

theorem ns_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : NSKE m) : NSKE (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_lookupErrorOnFailure _ _ ?_)

theorem ns_resolveAddressBits' (p : Cap × CapRef) : NSKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ns_auto)) fun nc => ?_
        split
        · exact ns_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_resolveAddressBits' _)

theorem ns_resolveAddressBits (a0 : Cap × CapRef) : NSKE (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_resolveAddressBits _)

theorem ns_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : NSKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupSlotForCnodeOp _ _ _ _)

theorem ns_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NSKE (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupTargetSlot _ _ _)

theorem ns_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : NSKE (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIoportControlInvocation _ _ _ _ _)

theorem ns_getAsidPool (ptr : ObjRef) : NSK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getAsidPool _)

theorem ns_findVspaceForAsid (asid : Asid) : NSKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_findVspaceForAsid _)

theorem ns_getPdpt (ptr : ObjRef) : NSK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPdpt _)

theorem ns_getPdpte (ptr : ObjRef) : NSK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPdpte _)

theorem ns_isFinalCap (cap : Cap) : NSK (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isFinalCap _)

theorem ns_getPml4 (ptr : ObjRef) : NSK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPml4 _)

theorem ns_getPml4e (ptr : ObjRef) : NSK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPml4e _)

theorem ns_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : NSKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupPdptSlot _ _)

theorem ns_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePageDirectoryInvocation _ _ _ _ _)

theorem ns_checkVpAlignment (sz : VMPageSize) (vptr : Word) : NSKE (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkVpAlignment _ _)

theorem ns_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : NSKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupPdSlot _ _)

theorem ns_getPd (ptr : ObjRef) : NSK (getPd (Z := Unit) ptr) := by
  unfold getPd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPd _)

theorem ns_getPde (ptr : ObjRef) : NSK (getPde (Z := Unit) ptr) := by
  unfold getPde; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPde _)

theorem ns_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : NSKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupPtSlot _ _)

theorem ns_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : NSKE (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_createMappingEntries _ _ _ _ _ _)

theorem ns_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : NSKE (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ensureSafeMapping _)

theorem ns_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePageInvocation _ _ _ _ _)

theorem ns_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePageTableInvocation _ _ _ _ _)

theorem ns_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePdptInvocation _ _ _ _ _)

theorem ns_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : NSKE (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ensurePortOperationAllowed _ _ _)

theorem ns_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : NSKE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePortInvocation _ _ _)

theorem ns_ensureNoChildren (cslotPtr : CslotPtr) : NSKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ensureNoChildren _)

theorem ns_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : NSK (selectExt (Z := Unit) a S) := by
  unfold selectExt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_selectExt _ _)

theorem ns_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archDecodeInvocation _ _ _ _ _ _)

theorem ns_getIrqState (irq : Irq) : NSK (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getIrqState _)

theorem ns_isIrqActive (irq : Irq) : NSK (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isIrqActive _)

theorem ns_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archDecodeIrqControlInvocation _ _ _ _)

theorem ns_archDeriveCap (c : ArchCap) : NSKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archDeriveCap _)

theorem ns_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : NSK (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_hwAsidInvalidate _ _)

theorem ns_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : NSK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setAsidPool _ _)

theorem ns_getCurrentCr3  : NSK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getCurrentCr3)

theorem ns_setCurrentCr3 (c : Cr3) : NSK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setCurrentCr3 _)

theorem ns_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : NSK (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setCurrentVspaceRoot _ _)

theorem ns_setVmRoot (tcb : ObjRef) : NSK (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setVmRoot _)

theorem ns_deleteAsid (asid : Asid) (pml4 : ObjRef) : NSK (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deleteAsid _ _)

theorem ns_deleteAsidPool (base : Asid) (ptr : ObjRef) : NSK (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deleteAsidPool _ _)

theorem ns_getPt (ptr : ObjRef) : NSK (getPt (Z := Unit) ptr) := by
  unfold getPt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPt _)

theorem ns_getPte (ptr : ObjRef) : NSK (getPte (Z := Unit) ptr) := by
  unfold getPte; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getPte _)

theorem ns_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : NSK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPd _ _)

theorem ns_storePde (p : ObjRef) (pde : PDE) : NSK (storePde (Z := Unit) p pde) := by
  unfold storePde; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePde _ _)

theorem ns_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : NSK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPdpt _ _)

theorem ns_storePdpte (p : ObjRef) (pte : PDPTE) : NSK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePdpte _ _)

theorem ns_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : NSK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPt _ _)

theorem ns_storePte (p : ObjRef) (pte : PTE) : NSK (storePte (Z := Unit) p pte) := by
  unfold storePte; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePte _ _)

theorem ns_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : NSK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPage _ _ _ _)

theorem ns_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : NSK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_flushTable _ _ _ _)

theorem ns_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : NSK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invalidatePageStructureCacheAsid _ _)

theorem ns_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NSK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPageTable _ _ _)

theorem ns_flushAll (vspace : ObjRef) (asid : Asid) : NSK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_flushAll _ _)

theorem ns_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NSK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPd _ _ _)

theorem ns_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NSK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPml4 _ _)

theorem ns_storePml4e (p : ObjRef) (pte : PML4E) : NSK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePml4e _ _)

theorem ns_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NSK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPdpt _ _ _)

theorem ns_archFinaliseCap (c : ArchCap) (x : Bool) : NSK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archFinaliseCap _ _)

theorem ns_archGetSanitiseRegisterInfo (_t : ObjRef) : NSK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archGetSanitiseRegisterInfo _)

theorem ns_setOriginal (slot : CslotPtr) (v : Bool) : NSK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setOriginal _ _)

theorem ns_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : NSK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setUntypedCapAsFull _ _ _)

theorem ns_setCdt (t : Cdt) : NSK (setCdt (Z := Unit) t) := by
  unfold setCdt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setCdt _)

theorem ns_updateCdt (f : Cdt → Cdt) : NSK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateCdt _)

theorem ns_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : NSK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capInsert _ _ _)

theorem ns_setIrqState (state : IrqState) (irq : Irq) : NSK (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setIrqState _ _)

theorem ns_updateIrqState (irq : Irq) (irqState : X64IRQState) : NSK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateIrqState _ _)

theorem ns_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NSK m) : NSKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_withoutPreemption _ ?_)

theorem ns_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NSKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archInvokeIrqControl _)

theorem ns_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NSK (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archInvokeIrqHandler _)

theorem ns_archMaskIrqSignal (irq : Irq) : NSK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archMaskIrqSignal _)

theorem ns_performAsidControlInvocation (iv : AsidControlInvocation) : NSK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performAsidControlInvocation _)

theorem ns_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NSK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storeAsidPoolEntry _ _ _)

theorem ns_performAsidPoolInvocation (iv : AsidPoolInvocation) : NSK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performAsidPoolInvocation _)

theorem ns_portIn (f : MachineMonad Data) : NSK (portIn (Z := Unit) f) := by
  unfold portIn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_portIn _)

theorem ns_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NSK (portOut (Z := Unit) f w) := by
  unfold portOut; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_portOut _ _)

theorem ns_performIoPortInvocation (i : IoPortInvocation) : NSK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performIoPortInvocation _)

theorem ns_setIoportMask (f l : IoPort) (val : Bool) : NSK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setIoportMask _ _ _)

theorem ns_performIoportControlInvocation (i : IoPortControlInvocation) : NSK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performIoportControlInvocation _)

theorem ns_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NSK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageDirectoryInvocation _)

theorem ns_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NSK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageInvocationUnmap _ _)

theorem ns_performPageInvocation (iv : PageInvocation) : NSK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageInvocation _)

theorem ns_performPageTableInvocation (iv : PageTableInvocation) : NSK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageTableInvocation _)

theorem ns_performPdptInvocation (iv : PdptInvocation) : NSK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPdptInvocation _)

theorem ns_archPerformInvocation (i : ArchInvocation) : NSKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPerformInvocation _)

theorem ns_freeIoportRange (f l : IoPort) : NSK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_freeIoportRange _ _)

theorem ns_archPostCapDeletion (ac : ArchCap) : NSK (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostCapDeletion _)

theorem ns_archPostModifyRegisters (cur t : ObjRef) : NSK (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostModifyRegisters _ _)

theorem ns_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NSK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostResetUntyped _ _)

theorem ns_loadFpuState (t : ObjRef) : NSK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadFpuState _)

theorem ns_saveFpuState (t : ObjRef) : NSK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_saveFpuState _)

theorem ns_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NSK (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setX64CurrentFpuOwner _)

theorem ns_switchLocalFpuOwner (newOwner : Option ObjRef) : NSK (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchLocalFpuOwner _)

theorem ns_fpuRelease (threadPtr : ObjRef) : NSK (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fpuRelease _)

theorem ns_lazyFpuRestore (threadPtr : ObjRef) : NSK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lazyFpuRestore _)

theorem ns_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NSK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostSetFlags _ _)

theorem ns_archPrepareNextDomain  : NSK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPrepareNextDomain)

theorem ns_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NSK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPrepareSetDomain _ _)

theorem ns_archSwitchToIdleThread  : NSK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archSwitchToIdleThread)

theorem ns_archSwitchToThread (t : ObjRef) : NSK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archSwitchToThread _)

theorem ns_getScRefillReady (scPtr : ObjRef) : NSK (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScRefillReady _)

theorem ns_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NSK (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScRefillSufficient _ _)

theorem ns_getTcbQueue (d : Domain) (prio : Priority) : NSK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getTcbQueue _ _)

theorem ns_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NSK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setTcbQueue _ _ _)

theorem ns_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NSK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbSchedAction _ _)

theorem ns_rescheduleRequired  : NSK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_rescheduleRequired)

theorem ns_possibleSwitchTo (target : ObjRef) : NSK (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_possibleSwitchTo _)

theorem ns_tcbReleaseRemove (tcbPtr : ObjRef) : NSK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseRemove _)

theorem ns_tcbReleaseDequeue  : NSK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseDequeue)

theorem ns_awaken  : NSK (awaken (Z := Unit)) := by
  unfold awaken; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_awaken)

theorem ns_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NSK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getSimpleKo _ _)

theorem ns_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : NSK (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateSkObjRef _ _ _ _)

theorem ns_bindNotification (tcbptr ntfnptr : ObjRef) : NSK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_bindNotification _ _)

theorem ns_bindScReply (scPtr replyPtr : ObjRef) : NSK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_bindScReply _ _)

theorem ns_getBlockingObject (state : ThreadState) : NSK (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getBlockingObject _)

theorem ns_replyUnlinkTcb (t r : ObjRef) : NSK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyUnlinkTcb _ _)

theorem ns_tcbEpDequeue (tptr epPtr : ObjRef) : NSK (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbEpDequeue _ _)

theorem ns_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : NSK (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_blockedCancelIpc _ _ _)

theorem ns_isRoundRobin (scPtr : ObjRef) : NSK (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isRoundRobin _)

theorem ns_getRefillHead (scPtr : ObjRef) : NSK (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefillHead _)

theorem ns_refillPopHead (scPtr : ObjRef) : NSK (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillPopHead _)

theorem ns_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NSK (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRefillHd _ _)

theorem ns_mergeOverlappingRefills (scPtr : ObjRef) : NSK (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_mergeOverlappingRefills _)

theorem ns_refillHeadOverlappingLoop (scPtr : ObjRef) : NSK (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillHeadOverlappingLoop _)

theorem ns_refillUnblockCheck (scPtr : ObjRef) : NSK (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillUnblockCheck _)

theorem ns_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NSK (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ifCondRefillUnblockCheck _ _ _)

theorem ns_restartThreadIfNoFault (t : ObjRef) : NSK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_restartThreadIfNoFault _)

theorem ns_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NSK (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartEpQueuedThread _ _)

theorem ns_cancelAllIpc (epptr : ObjRef) : NSK (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelAllIpc _)

theorem ns_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : NSK (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbNtfnDequeue _ _)

theorem ns_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NSK (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartNtfnQueuedThread _ _)

theorem ns_cancelAllSignals (ntfnptr : ObjRef) : NSK (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelAllSignals _)

theorem ns_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NSK (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartBadgedThread _ _ _)

theorem ns_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NSK (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelBadgedSends _ _)

theorem ns_cancelSignal (threadptr ntfnptr : ObjRef) : NSK (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelSignal _ _)

theorem ns_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NSK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getSkObjRef _ _ _)

theorem ns_replyRemoveTcb (tptr rptr : ObjRef) : NSK (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyRemoveTcb _ _)

theorem ns_cancelIpc (tptr : ObjRef) : NSK (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelIpc _)

theorem ns_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NSK (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capSwap _ _ _ _)

theorem ns_capSwapForDelete (slot1 slot2 : CslotPtr) : NSK (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capSwapForDelete _ _)

theorem ns_deletedIrqHandler (irq : Irq) : NSK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deletedIrqHandler _)

theorem ns_postCapDeletion (cap : Cap) : NSK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_postCapDeletion _)

theorem ns_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NSK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_emptySlot _ _)

theorem ns_replyUnlinkSc (scPtr replyPtr : ObjRef) : NSK (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyUnlinkSc _ _)

theorem ns_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NSK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScObjRef _ _)

theorem ns_testReschedule (fromTptr : ObjRef) : NSK (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_testReschedule _)

theorem ns_schedContextDonate (scPtr tcbPtr : ObjRef) : NSK (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextDonate _ _)

theorem ns_replyRemove (caller r : ObjRef) : NSK (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyRemove _ _)

theorem ns_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : NSK (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextMaybeUnbindNtfn _)

theorem ns_unbindMaybeNotification (ntfnptr : ObjRef) : NSK (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindMaybeNotification _)

theorem ns_fastFinalise (a0 : Cap) (a1 : Bool) : NSK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fastFinalise _ _)

theorem ns_capDeleteOne (slot : CslotPtr) : NSK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capDeleteOne _)

theorem ns_getIrqSlot (irq : Irq) : NSK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getIrqSlot _)

theorem ns_deletingIrqHandler (irq : Irq) : NSK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deletingIrqHandler _)

theorem ns_prepareThreadDelete (threadPtr : ObjRef) : NSK (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_prepareThreadDelete _)

theorem ns_schedContextSetInactive (scPtr : ObjRef) : NSK (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextSetInactive _)

theorem ns_schedContextUnbindTcb (scPtr : ObjRef) : NSK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindTcb _)

theorem ns_schedContextUnbindAllTcbs (scPtr : ObjRef) : NSK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindAllTcbs _)

theorem ns_schedContextUnbindNtfn (scPtr : ObjRef) : NSK (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindNtfn _)

theorem ns_schedContextUnbindReply (scPtr : ObjRef) : NSK (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindReply _)

theorem ns_schedContextUnbindYieldFrom (scPtr : ObjRef) : NSK (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindYieldFrom _)

theorem ns_updateRestartPc (threadPtr : ObjRef) : NSK (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRestartPc _)

theorem ns_suspend (thread : ObjRef) : NSK (suspend (Z := Unit) thread) := by
  unfold suspend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_suspend _)

theorem ns_unbindFromSc (tcbPtr : ObjRef) : NSK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindFromSc _)

theorem ns_unbindNotification (tcb : ObjRef) : NSK (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindNotification _)

theorem ns_finaliseCap (a0 : Cap) (a1 : Bool) : NSK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_finaliseCap _ _)

theorem ns_getScActive (scPtr : ObjRef) : NSK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScActive _)

theorem ns_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NSKE f) (h_g : NSKE g) : NSKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ns_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_orChoiceE _ _ _ ?_ ?_)

theorem ns_updateTimeStamp  : NSK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateTimeStamp)

theorem ns_preemptionPoint  : NSKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem ns_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NSK (f k)) (k : RecDelCall) : NSKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ns_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ns_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ns_auto
    all_goals exact hrec' _

theorem ns_recDel (c : RecDelCall) : NSKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ns_recDelF hf k) c
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_recDel _)

theorem ns_capDelete (slot : CslotPtr) : NSKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capDelete _)

theorem ns_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NSKE m) : NSKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_capFaultOnFailure _ _ _ ?_)

theorem ns_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NSK (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem ns_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NSK (f k)) (sl : CslotPtr) : NSKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ns_auto
  all_goals exact hrec' _

theorem ns_capRevoke (sl : CslotPtr) : NSKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ns_capRevokeF hf k) sl
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capRevoke _)

theorem ns_captransferFromWords (ptr : Word) : NSK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_captransferFromWords _)

theorem ns_isValidTimeoutHandler (tptr : ObjRef) : NSK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isValidTimeoutHandler _)

theorem ns_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NSK (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_makeArchFaultMsg _ _)

theorem ns_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NSK (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_makeFaultMsg _ _)

theorem ns_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NSK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doFaultTransfer _ _ _ _)

theorem ns_loadWordOffs (ptr : ObjRef) (offs : Nat) : NSK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadWordOffs _ _)

theorem ns_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NSK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_copyMrs _ _ _ _ _)

theorem ns_getMessageInfo (thread : ObjRef) : NSK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getMessageInfo _)

theorem ns_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NSK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ns_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getExtraCptrs _ _)

theorem ns_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NSKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupSlotForThread _ _)

theorem ns_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NSKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupCapAndSlot _ _)

theorem ns_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NSKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupExtraCaps _ _ _)

theorem ns_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NSKE m) : NSK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_emptyOnFailure _ ?_)

theorem ns_loadCapTransfer (buffer : ObjRef) : NSK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadCapTransfer _)

theorem ns_lookupCap (thread : ObjRef) (ref : CapRef) : NSKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupCap _ _)

theorem ns_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NSKE m) : NSKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_unifyFailure _ ?_)

theorem ns_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NSK (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getReceiveSlots _ _)

theorem ns_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NSKE m) : NSK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_constOnFailure _ _ ?_)

theorem ns_deriveCap (slot : CslotPtr) (cap : Cap) : NSKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deriveCap _ _)

theorem ns_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NSK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setExtraBadge _ _ _)

theorem ns_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NSK (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ns_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ns_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ns_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_transferCapsLoop _ _ _ _ _ _)

theorem ns_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NSK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_transferCaps _ _ _ _ _)

theorem ns_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NSK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doNormalTransfer _ _ _ _ _ _ _)

theorem ns_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NSK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doIpcTransfer _ _ _ _ _)

theorem ns_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : NSK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyPush _ _ _ _)

theorem ns_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NSK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_orderedInsert _ _ _ _)

theorem ns_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NSK (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbAppend _ _)

theorem ns_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : NSK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbEpAppend _ _ _)

theorem ns_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : NSK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendIpcBlocked _ _ _ _ _ _)

theorem ns_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : NSK (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendIpc _ _ _ _ _ _ _ _)

theorem ns_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : NSK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendFaultIpc _ _ _ _)

theorem ns_handleTimeout (tptr : ObjRef) (ex : Fault) : NSK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleTimeout _ _)

theorem ns_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NSK (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_readyTimesAppend _ _)

theorem ns_tcbReleaseEnqueue (tcbPtr : ObjRef) : NSK (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseEnqueue _)

theorem ns_postpone (scPtr : ObjRef) : NSK (postpone (Z := Unit) scPtr) := by
  unfold postpone; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_postpone _)

theorem ns_endTimeslice (canTimeout : Bool) : NSK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_endTimeslice _)

theorem ns_getRefills (scPtr : ObjRef) : NSK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefills _)

theorem ns_refillSize (scPtr : ObjRef) : NSK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillSize _)

theorem ns_refillSingle (scPtr : ObjRef) : NSK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillSingle _)

theorem ns_getRefillTail (scPtr : ObjRef) : NSK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefillTail _)

theorem ns_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NSK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillAddTail _ _)

theorem ns_refillFull (scPtr : ObjRef) : NSK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillFull _)

theorem ns_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NSK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRefillTl _ _)

theorem ns_scheduleUsed (scPtr : ObjRef) (new : Refill) : NSK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleUsed _ _)

theorem ns_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NSK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chargeEntireHeadRefill _ _)

theorem ns_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NSK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleOverrun _ _)

theorem ns_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NSK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_mergeNonoverlappingHeadRefill _)

theorem ns_headInsufficientLoop (scPtr : ObjRef) : NSK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_headInsufficientLoop _)

theorem ns_refillBudgetCheck (usage : Ticks) : NSK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillBudgetCheck _)

theorem ns_refillResetRr (cscPtr : ObjRef) : NSK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillResetRr _)

theorem ns_chargeBudget (consumed : Ticks) (canTimeout : Bool) : NSK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chargeBudget _ _)

theorem ns_checkBudget  : NSK (checkBudget (Z := Unit)) := by
  unfold checkBudget; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkBudget)

theorem ns_checkBudgetRestart  : NSK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkBudgetRestart)

theorem ns_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NSK m) : NSK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_checkCapAt _ _ _ ?_)

theorem ns_checkDomainTime  : NSK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkDomainTime)

theorem ns_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NSKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkHandlerEp _ _)

theorem ns_checkPrio (newPrio : Data) (authTcb : ObjRef) : NSKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkPrio _ _)

theorem ns_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NSKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkValidIpcBuffer _ _)

theorem ns_nextDomain  : NSK (nextDomain (Z := Unit)) := by
  unfold nextDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_nextDomain)

theorem ns_switchToThread (t : ObjRef) : NSK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchToThread _)

theorem ns_guardedSwitchTo (thread : ObjRef) : NSK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_guardedSwitchTo _)

theorem ns_switchToIdleThread  : NSK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchToIdleThread)

theorem ns_chooseThread  : NSK (chooseThread (Z := Unit)) := by
  unfold chooseThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chooseThread)

theorem ns_refillBudgetCheckRoundRobin (usage : Ticks) : NSK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillBudgetCheckRoundRobin _)

theorem ns_commitTime  : NSK (commitTime (Z := Unit)) := by
  unfold commitTime; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_commitTime)

theorem ns_schedContextResume (scPtr : ObjRef) : NSK (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextResume _)

theorem ns_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NSK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeDonateSc _ _)

theorem ns_completeSignal (ntfnptr tptr : ObjRef) : NSK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_completeSignal _ _)

theorem ns_copyGlobalMappings (newPm : ObjRef) : NSK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_copyGlobalMappings _)

theorem ns_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NSK (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_createCap _ _ _ _ _)

theorem ns_dataToObjType (type : Data) : NSKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_dataToObjType _)

theorem ns_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeBindNotification _ _)

theorem ns_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NSKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupPivotSlot _ _ _)

theorem ns_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NSKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupSourceSlot _ _ _)

theorem ns_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NSKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeCnodeInvocation _ _ _ _)

theorem ns_slotCapLongRunningDelete (slot : CslotPtr) : NSK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_slotCapLongRunningDelete _)

theorem ns_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NSKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeCvSpace _ _ _ _)

theorem ns_subframeNode (nodeCap : Cap) (index depth : Data) : NSKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_subframeNode _ _ _)

theorem ns_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NSKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDeriveSubframe _ _ _ _)

theorem ns_decodeDomainScheduleConfigure (args : List Data) : NSKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainScheduleConfigure _)

theorem ns_decodeDomainScheduleSetStart (args : List Data) : NSKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainScheduleSetStart _)

theorem ns_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NSKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainSet _ _)

theorem ns_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NSKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainInvocation _ _ _)

theorem ns_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NSK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4GetMr _ _ _)

theorem ns_fl4Arg (buf : Option ObjRef) (i : Nat) : NSKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4Arg _ _)

theorem ns_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4ConfigureSingleStepping _ _)

theorem ns_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NSKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4FpuTransfer _ _ _ _)

theorem ns_fl4CheckBpNum (bp : Data) : NSKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4CheckBpNum _)

theorem ns_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4GetBreakpoint _ _)

theorem ns_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NSKE (check x0)) : NSKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ns_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ns_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqControlRemapped _ _ _)

theorem ns_fl4ArchCheckIrq (irq : Data) : NSKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchCheckIrq _)

theorem ns_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4IrqControl _ _ _ _ _)

theorem ns_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetBreakpoint _ _)

theorem ns_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NSKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetFlags _ _)

theorem ns_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NSKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetTimer _ _)

theorem ns_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4UnsetBreakpoint _ _)

theorem ns_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NSKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4TcbExt _ _ _ _ _)

theorem ns_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqControlInvocation _ _ _ _)

theorem ns_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NSKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqHandlerInvocation _ _ _)

theorem ns_getScReleased (scPtr : ObjRef) : NSK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScReleased _)

theorem ns_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextBind _ _)

theorem ns_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextUnbindObject _ _)

theorem ns_decodeSchedContextYieldTo (scPtr : ObjRef) : NSKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextYieldTo _)

theorem ns_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextInvocation _ _ _)

theorem ns_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NSKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedControlInvocationFlags _ _ _)

theorem ns_rangeCheck (v minV maxV : Word) : NSKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_rangeCheck _ _ _)

theorem ns_decodeSetFlags (args : List Data) (cap : Cap) : NSKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetFlags _ _)

theorem ns_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NSKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetIpcBuffer _ _ _ _)

theorem ns_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetMcpriority _ _ _ _)

theorem ns_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetPriority _ _ _ _)

theorem ns_isBlocked (thread : ObjRef) : NSK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isBlocked _)

theorem ns_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NSKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUpdateSc _ _ _)

theorem ns_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetSchedParams _ _ _ _)

theorem ns_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NSKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetSpace _ _ _ _)

theorem ns_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetTimeoutEp _ _ _)

theorem ns_decodeSetTlsBase (args : List Data) (cap : Cap) : NSKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetTlsBase _ _)

theorem ns_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTcbConfigure _ _ _ _)

theorem ns_decodeUnbindNotification (cap : Cap) : NSKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ns_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NSKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTcbInvocation _ _ _ _ _)

theorem ns_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NSKE (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUntypedInvocation _ _ _ _ _)

theorem ns_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NSKE (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeInvocation _ _ _ _ _ _ _ _)

theorem ns_decodePml4Flush (cap : ArchCap) : NSKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePml4Flush _)

theorem ns_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NSKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_frameMappingSlot _ _ _ _)

theorem ns_decodeTestAndClearAccessed (cap : ArchCap) : NSKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTestAndClearAccessed _)

theorem ns_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NSKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ns_doNbrecvFailedTransfer (thread : ObjRef) : NSK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doNbrecvFailedTransfer _)

theorem ns_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NSK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getMrs _ _ _)

theorem ns_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NSK (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleArchFaultReply _ _ _ _)

theorem ns_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NSK (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleFaultReply _ _ _ _)

theorem ns_testPossibleSwitchTo (tcbPtr : ObjRef) : NSK (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_testPossibleSwitchTo _)

theorem ns_restart (thread : ObjRef) : NSK (restart (Z := Unit) thread) := by
  unfold restart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_restart _)

theorem ns_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : NSK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doReplyTransfer _ _ _)

theorem ns_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NSK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_domainScheduleConfigure _ _ _)

theorem ns_setNextInterrupt  : NSK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setNextInterrupt)

theorem ns_switchSchedContext  : NSK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchSchedContext)

theorem ns_scAndTimer  : NSK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scAndTimer)

theorem ns_scheduleChooseNewThread  : NSK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleChooseNewThread)

theorem ns_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NSK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleSwitchThreadFastfail _ _ _ _)

theorem ns_schedule  : NSK (schedule (Z := Unit)) := by
  unfold schedule; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedule)

theorem ns_domainSetStart (index : Nat) : NSK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_domainSetStart _)

theorem ns_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ns_performDeriveSubframe (iv : Fl4SubframeInvocation) : NSK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performDeriveSubframe _)

theorem ns_performPml4Flush (a0 : Fl4Pml4Invocation) : NSK (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPml4Flush _)

theorem ns_performTestAndClearAccessed (_slot : ObjRef) : NSK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performTestAndClearAccessed _)

theorem ns_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : NSKE (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchPerformInvocation _)

theorem ns_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NSK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateWaitingNtfn _ _ _)

theorem ns_sendSignal (ntfnptr : ObjRef) (badge : Badge) : NSK (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendSignal _ _)

theorem ns_fl4Awaken : NSK (fl4Awaken (Z := Unit)) := by
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
    · exact ns_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ns_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NSKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ns_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NSKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ns_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NSK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_initArchObjects _ _ _ _ _ _)

theorem ns_resetUntypedCap (srcSlot : CslotPtr) : NSKE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_resetUntypedCap _)

theorem ns_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : NSKE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeUntypedWith _ _)

theorem ns_invokeCnode (i : CnodeInvocation) : NSKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeCnode _)

theorem ns_threadSetDomain (tptr : ObjRef) (domain : Domain) : NSK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_threadSetDomain _ _)

theorem ns_setDomain (tptr : ObjRef) (newDom : Domain) : NSK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setDomain _ _)

theorem ns_invokeSetDomain (thread : ObjRef) (domain : Domain) : NSK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSetDomain _ _)

theorem ns_invokeDomain (domInv : DomainInvocation) : NSK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeDomain _)

theorem ns_invokeIrqControl (a0 : IrqControlInvocation) : NSKE (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeIrqControl _)

theorem ns_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NSKE (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeFl4IrqControl _)

theorem ns_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NSKE (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeFl4Tcb _)

theorem ns_invokeIrqHandler (a0 : IrqHandlerInvocation) : NSK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeIrqHandler _)

theorem ns_returnConsumed (scPtr : ObjRef) : NSK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_returnConsumed _)

theorem ns_schedContextBindNtfn (sc ntfn : ObjRef) : NSK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextBindNtfn _ _)

theorem ns_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NSK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextBindTcb _ _)

theorem ns_schedContextYieldTo (scPtr : ObjRef) : NSK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextYieldTo _)

theorem ns_invokeSchedContext (iv : SchedContextInvocation) : NSK (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSchedContext _)

theorem ns_maybeAddEmptyTail (scPtr : ObjRef) : NSK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeAddEmptyTail _)

theorem ns_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NSK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillNew _ _ _ _)

theorem ns_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NSK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillUpdate _ _ _ _)

theorem ns_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NSK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSchedControlConfigureFlags _)

theorem ns_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NSKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbCap _ _ _ _)

theorem ns_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NSKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbFrameCap _ _ _)

theorem ns_setFlags (ref : ObjRef) (flags : TcbFlags) : NSK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setFlags _ _)

theorem ns_setMcpriority (ref : ObjRef) (mcp : Priority) : NSK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setMcpriority _ _)

theorem ns_reorderEp (epPtr tptr : ObjRef) : NSK (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_reorderEp _ _)

theorem ns_reorderNtfn (ntfnPtr tptr : ObjRef) : NSK (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_reorderNtfn _ _)

theorem ns_threadSetPriority (tptr : ObjRef) (prio : Priority) : NSK (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_threadSetPriority _ _)

theorem ns_setPriority (tptr : ObjRef) (prio : Priority) : NSK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPriority _ _)

theorem ns_invokeTcb (a0 : TcbInvocation) : NSKE (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeTcb _)

theorem ns_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : NSKE (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4PerformInvocation _ _ _ _)

theorem ns_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NSK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ReplyFromKernelError _ _ _)

theorem ns_handleNoFault (tptr : ObjRef) : NSK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleNoFault _)

theorem ns_handleFault (thread : ObjRef) (ex : Fault) : NSK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleFault _ _)

theorem ns_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NSKE mFault) (h_hFault : ∀ x0, NSK (hFault x0)) (h_mError : ∀ x0, NSKE (mError x0)) (h_hError : ∀ x0, NSK (hError x0)) (h_mFinalise : ∀ x0, NSKE (mFinalise x0)) : NSKE (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ns_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ns_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NSKE (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleInvocationR _ _ _ _ _ _)

theorem ns_getCapReg (reg : Register) : NSK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getCapReg _)

theorem ns_lookupReply  : NSKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupReply)

theorem ns_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NSK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeReturnSc _ _)

theorem ns_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : NSK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem ns_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    NSK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveIpc _ _ _ _)

theorem ns_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : NSK (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbNtfnAppend _ _)

theorem ns_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : NSK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveSignalBlocked _ _ _)

theorem ns_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : NSK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveSignal _ _ _)

theorem ns_handleRecv (isBlocking canReply : Bool) : NSK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleRecv _ _)

theorem ns_handleYield  : NSK (handleYield (Z := Unit)) := by
  unfold handleYield; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleYield)

theorem ns_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : NSKE (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleSyscall _ _)

theorem ns_invokeUntyped (ui : UntypedInvocation) : NSKE (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeUntyped _)

theorem ns_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : NSKE (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performInvocation _ _ _ _)

theorem ns_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NSKE (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleInvocation _ _ _ _ _)

theorem ns_handleCall  : NSKE (handleCall (Z := Unit)) := by
  unfold handleCall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleCall)

theorem ns_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NSK (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleHypervisorFault _ _)

theorem ns_handleSend (bl : Bool) : NSKE (handleSend (Z := Unit) bl) := by
  unfold handleSend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleSend _)

theorem ns_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NSKE (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleVmFault _ _)

theorem ns_handleReservedIrq (_irq : Irq) : NSK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleReservedIrq _)

theorem ns_handleInterrupt (irq : Irq) : NSK (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleInterrupt _)

theorem ns_handleSpuriousIrq  : NSK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleSpuriousIrq)

theorem ns_maybeHandleInterrupt (inKernel : Bool) : NSK (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeHandleInterrupt _)

theorem ns_handleEvent (a0 : Event) : NSKE (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleEvent _)

theorem ns_fl4HandleEvent (rep : Bool) (a0 : Event) : NSKE (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleEvent _ _)

theorem ns_preemptionPath  : NSK (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_preemptionPath)

theorem ns_fl4CallKernel (rep : Bool) (ev : Event) : NSK (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4CallKernel _ _)

theorem ns_fl4SyscallFaultIP (thread : ObjRef) : NSK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4SyscallFaultIP _)

theorem ns_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : NSK (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4KernelEntrySyscall _ _)
