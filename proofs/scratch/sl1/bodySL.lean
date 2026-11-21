theorem sl_archActivateIdleThread (_t : ObjRef) : SLK Iq Kq (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archActivateIdleThread _)

theorem sl_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : SLK Iq Kq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_threadGet _ _)

theorem sl_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : SLK Iq Kq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getTcbObjRef _ _)

theorem sl_schedContextCancelYieldTo (thread : ObjRef) : SLK Iq Kq (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextCancelYieldTo _)

theorem sl_getCap (a0 : CslotPtr) : SLK Iq Kq (getCap (Z := Unit) a0) := by
  unfold getCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getCap _)

theorem sl_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : SLK Iq Kq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupIpcBuffer _ _)

theorem sl_setMessageInfo (thread : ObjRef) (info : MessageInfo) : SLK Iq Kq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setMessageInfo _ _)

theorem sl_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : SLK Iq Kq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storeWordOffs _ _ _)

theorem sl_replyFromKernel (thread : ObjRef) (x : Data × List Data) : SLK Iq Kq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyFromKernel _ _)

theorem sl_getSchedContext (ptr : ObjRef) : SLK Iq Kq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getSchedContext _)

theorem sl_schedContextUpdateConsumed (scPtr : ObjRef) : SLK Iq Kq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUpdateConsumed _)

theorem sl_setConsumed (scPtr tcbPtr : ObjRef) : SLK Iq Kq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setConsumed _ _)

theorem sl_completeYieldTo (tcbPtr : ObjRef) : SLK Iq Kq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_completeYieldTo _)

theorem sl_getThreadState (ref : ObjRef) : SLK Iq Kq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getThreadState _)

theorem sl_setSchedulerAction (action : SchedulerAction) : SLK Iq Kq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setSchedulerAction _)

theorem sl_activateThread  : SLK Iq Kq (activateThread (Z := Unit)) := by
  unfold activateThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_activateThread)

theorem sl_archCheckIrq (_irq : Data) : SLKE Iq Kq (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archCheckIrq _)

theorem sl_ensureEmpty (slot : CslotPtr) : SLKE Iq Kq (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ensureEmpty _)

theorem sl_isIoportRangeFree (f l : IoPort) : SLK Iq Kq (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isIoportRangeFree _ _)

theorem sl_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : SLKE Iq Kq m) : SLKE Iq Kq (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_lookupErrorOnFailure _ _ ?_)

theorem sl_resolveAddressBits' (p : Cap × CapRef) : SLKE Iq Kq (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by sl_auto)) fun nc => ?_
        split
        · exact sl_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_resolveAddressBits' _)

theorem sl_resolveAddressBits (a0 : Cap × CapRef) : SLKE Iq Kq (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_resolveAddressBits _)

theorem sl_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : SLKE Iq Kq (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupSlotForCnodeOp _ _ _ _)

theorem sl_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SLKE Iq Kq (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupTargetSlot _ _ _)

theorem sl_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : SLKE Iq Kq (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIoportControlInvocation _ _ _ _ _)

theorem sl_getAsidPool (ptr : ObjRef) : SLK Iq Kq (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getAsidPool _)

theorem sl_findVspaceForAsid (asid : Asid) : SLKE Iq Kq (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_findVspaceForAsid _)

theorem sl_getPdpt (ptr : ObjRef) : SLK Iq Kq (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPdpt _)

theorem sl_getPdpte (ptr : ObjRef) : SLK Iq Kq (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPdpte _)

theorem sl_isFinalCap (cap : Cap) : SLK Iq Kq (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isFinalCap _)

theorem sl_getPml4 (ptr : ObjRef) : SLK Iq Kq (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPml4 _)

theorem sl_getPml4e (ptr : ObjRef) : SLK Iq Kq (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPml4e _)

theorem sl_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : SLKE Iq Kq (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupPdptSlot _ _)

theorem sl_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePageDirectoryInvocation _ _ _ _ _)

theorem sl_checkVpAlignment (sz : VMPageSize) (vptr : Word) : SLKE Iq Kq (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkVpAlignment _ _)

theorem sl_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : SLKE Iq Kq (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupPdSlot _ _)

theorem sl_getPd (ptr : ObjRef) : SLK Iq Kq (getPd (Z := Unit) ptr) := by
  unfold getPd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPd _)

theorem sl_getPde (ptr : ObjRef) : SLK Iq Kq (getPde (Z := Unit) ptr) := by
  unfold getPde; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPde _)

theorem sl_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : SLKE Iq Kq (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupPtSlot _ _)

theorem sl_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : SLKE Iq Kq (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_createMappingEntries _ _ _ _ _ _)

theorem sl_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : SLKE Iq Kq (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ensureSafeMapping _)

theorem sl_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePageInvocation _ _ _ _ _)

theorem sl_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePageTableInvocation _ _ _ _ _)

theorem sl_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePdptInvocation _ _ _ _ _)

theorem sl_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : SLKE Iq Kq (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ensurePortOperationAllowed _ _ _)

theorem sl_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : SLKE Iq Kq (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePortInvocation _ _ _)

theorem sl_ensureNoChildren (cslotPtr : CslotPtr) : SLKE Iq Kq (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ensureNoChildren _)

theorem sl_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : SLK Iq Kq (selectExt (Z := Unit) a S) := by
  unfold selectExt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_selectExt _ _)

theorem sl_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archDecodeInvocation _ _ _ _ _ _)

theorem sl_getIrqState (irq : Irq) : SLK Iq Kq (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getIrqState _)

theorem sl_isIrqActive (irq : Irq) : SLK Iq Kq (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isIrqActive _)

theorem sl_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archDecodeIrqControlInvocation _ _ _ _)

theorem sl_archDeriveCap (c : ArchCap) : SLKE Iq Kq (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archDeriveCap _)

theorem sl_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : SLK Iq Kq (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_hwAsidInvalidate _ _)

theorem sl_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SLK Iq Kq (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setAsidPool _ _)

theorem sl_getCurrentCr3  : SLK Iq Kq (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getCurrentCr3)

theorem sl_setCurrentCr3 (c : Cr3) : SLK Iq Kq (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setCurrentCr3 _)

theorem sl_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setCurrentVspaceRoot _ _)

theorem sl_setVmRoot (tcb : ObjRef) : SLK Iq Kq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setVmRoot _)

theorem sl_deleteAsid (asid : Asid) (pml4 : ObjRef) : SLK Iq Kq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deleteAsid _ _)

theorem sl_deleteAsidPool (base : Asid) (ptr : ObjRef) : SLK Iq Kq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deleteAsidPool _ _)

theorem sl_getPt (ptr : ObjRef) : SLK Iq Kq (getPt (Z := Unit) ptr) := by
  unfold getPt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPt _)

theorem sl_getPte (ptr : ObjRef) : SLK Iq Kq (getPte (Z := Unit) ptr) := by
  unfold getPte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPte _)

theorem sl_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SLK Iq Kq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPd _ _)

theorem sl_storePde (p : ObjRef) (pde : PDE) : SLK Iq Kq (storePde (Z := Unit) p pde) := by
  unfold storePde; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePde _ _)

theorem sl_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SLK Iq Kq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPdpt _ _)

theorem sl_storePdpte (p : ObjRef) (pte : PDPTE) : SLK Iq Kq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePdpte _ _)

theorem sl_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SLK Iq Kq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPt _ _)

theorem sl_storePte (p : ObjRef) (pte : PTE) : SLK Iq Kq (storePte (Z := Unit) p pte) := by
  unfold storePte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePte _ _)

theorem sl_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SLK Iq Kq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPage _ _ _ _)

theorem sl_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : SLK Iq Kq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_flushTable _ _ _ _)

theorem sl_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invalidatePageStructureCacheAsid _ _)

theorem sl_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SLK Iq Kq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPageTable _ _ _)

theorem sl_flushAll (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_flushAll _ _)

theorem sl_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SLK Iq Kq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPd _ _ _)

theorem sl_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SLK Iq Kq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPml4 _ _)

theorem sl_storePml4e (p : ObjRef) (pte : PML4E) : SLK Iq Kq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePml4e _ _)

theorem sl_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SLK Iq Kq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPdpt _ _ _)

theorem sl_archFinaliseCap (c : ArchCap) (x : Bool) : SLK Iq Kq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archFinaliseCap _ _)

theorem sl_archGetSanitiseRegisterInfo (_t : ObjRef) : SLK Iq Kq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archGetSanitiseRegisterInfo _)

theorem sl_setOriginal (slot : CslotPtr) (v : Bool) : SLK Iq Kq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setOriginal _ _)

theorem sl_setCdt (t : Cdt) : SLK Iq Kq (setCdt (Z := Unit) t) := by
  unfold setCdt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setCdt _)

theorem sl_updateCdt (f : Cdt → Cdt) : SLK Iq Kq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateCdt _)

theorem sl_setIrqState (state : IrqState) (irq : Irq) : SLK Iq Kq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setIrqState _ _)

theorem sl_updateIrqState (irq : Irq) (irqState : X64IRQState) : SLK Iq Kq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateIrqState _ _)

theorem sl_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : SLK Iq Kq m) : SLKE Iq Kq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_withoutPreemption _ ?_)

theorem sl_archInvokeIrqControl (aic : ArchIrqControlInvocation) : SLKE Iq Kq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archInvokeIrqControl _)

theorem sl_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : SLK Iq Kq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archInvokeIrqHandler _)

theorem sl_archMaskIrqSignal (irq : Irq) : SLK Iq Kq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archMaskIrqSignal _)

theorem sl_setIoportMask (f l : IoPort) (val : Bool) : SLK Iq Kq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setIoportMask _ _ _)

theorem sl_freeIoportRange (f l : IoPort) : SLK Iq Kq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_freeIoportRange _ _)

theorem sl_archPostCapDeletion (ac : ArchCap) : SLK Iq Kq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostCapDeletion _)

theorem sl_archPostModifyRegisters (cur t : ObjRef) : SLK Iq Kq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostModifyRegisters _ _)

theorem sl_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : SLK Iq Kq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostResetUntyped _ _)

theorem sl_loadFpuState (t : ObjRef) : SLK Iq Kq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadFpuState _)

theorem sl_saveFpuState (t : ObjRef) : SLK Iq Kq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_saveFpuState _)

theorem sl_setX64CurrentFpuOwner (newOwner : Option ObjRef) : SLK Iq Kq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setX64CurrentFpuOwner _)

theorem sl_switchLocalFpuOwner (newOwner : Option ObjRef) : SLK Iq Kq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchLocalFpuOwner _)

theorem sl_fpuRelease (threadPtr : ObjRef) : SLK Iq Kq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fpuRelease _)

theorem sl_lazyFpuRestore (threadPtr : ObjRef) : SLK Iq Kq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lazyFpuRestore _)

theorem sl_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : SLK Iq Kq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostSetFlags _ _)

theorem sl_archPrepareNextDomain  : SLK Iq Kq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPrepareNextDomain)

theorem sl_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : SLK Iq Kq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPrepareSetDomain _ _)

theorem sl_archSwitchToIdleThread  : SLK Iq Kq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archSwitchToIdleThread)

theorem sl_archSwitchToThread (t : ObjRef) : SLK Iq Kq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archSwitchToThread _)

theorem sl_getScRefillReady (scPtr : ObjRef) : SLK Iq Kq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScRefillReady _)

theorem sl_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScRefillSufficient _ _)

theorem sl_getTcbQueue (d : Domain) (prio : Priority) : SLK Iq Kq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getTcbQueue _ _)

theorem sl_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : SLK Iq Kq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setTcbQueue _ _ _)

theorem sl_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : SLK Iq Kq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbSchedAction _ _)

theorem sl_rescheduleRequired  : SLK Iq Kq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_rescheduleRequired)

theorem sl_possibleSwitchTo (target : ObjRef) : SLK Iq Kq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_possibleSwitchTo _)

theorem sl_tcbReleaseRemove (tcbPtr : ObjRef) : SLK Iq Kq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseRemove _)

theorem sl_tcbReleaseDequeue  : SLK Iq Kq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseDequeue)

theorem sl_awaken  : SLK Iq Kq (awaken (Z := Unit)) := by
  unfold awaken; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_awaken)

theorem sl_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : SLK Iq Kq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getSimpleKo _ _)

theorem sl_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : SLK Iq Kq (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateSkObjRef _ _ _ _)

theorem sl_bindNotification (tcbptr ntfnptr : ObjRef) : SLK Iq Kq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_bindNotification _ _)

theorem sl_getBlockingObject (state : ThreadState) : SLK Iq Kq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getBlockingObject _)

theorem sl_replyUnlinkTcb (t r : ObjRef) : SLK Iq Kq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyUnlinkTcb _ _)

theorem sl_tcbEpDequeue (tptr epPtr : ObjRef) : SLK Iq Kq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbEpDequeue _ _)

theorem sl_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : SLK Iq Kq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_blockedCancelIpc _ _ _)

theorem sl_isRoundRobin (scPtr : ObjRef) : SLK Iq Kq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isRoundRobin _)

theorem sl_getRefillHead (scPtr : ObjRef) : SLK Iq Kq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefillHead _)

theorem sl_refillPopHead (scPtr : ObjRef) : SLK Iq Kq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillPopHead _)

theorem sl_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : SLK Iq Kq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRefillHd _ _)

theorem sl_mergeOverlappingRefills (scPtr : ObjRef) : SLK Iq Kq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_mergeOverlappingRefills _)

theorem sl_refillHeadOverlappingLoop (scPtr : ObjRef) : SLK Iq Kq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillHeadOverlappingLoop _)

theorem sl_refillUnblockCheck (scPtr : ObjRef) : SLK Iq Kq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillUnblockCheck _)

theorem sl_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : SLK Iq Kq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ifCondRefillUnblockCheck _ _ _)

theorem sl_restartThreadIfNoFault (t : ObjRef) : SLK Iq Kq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_restartThreadIfNoFault _)

theorem sl_removeAndRestartEpQueuedThread (t epptr : ObjRef) : SLK Iq Kq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartEpQueuedThread _ _)

theorem sl_cancelAllIpc (epptr : ObjRef) : SLK Iq Kq (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelAllIpc _)

theorem sl_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : SLK Iq Kq (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbNtfnDequeue _ _)

theorem sl_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : SLK Iq Kq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartNtfnQueuedThread _ _)

theorem sl_cancelAllSignals (ntfnptr : ObjRef) : SLK Iq Kq (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelAllSignals _)

theorem sl_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : SLK Iq Kq (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartBadgedThread _ _ _)

theorem sl_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : SLK Iq Kq (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelBadgedSends _ _)

theorem sl_cancelSignal (threadptr ntfnptr : ObjRef) : SLK Iq Kq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelSignal _ _)

theorem sl_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : SLK Iq Kq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getSkObjRef _ _ _)

theorem sl_replyRemoveTcb (tptr rptr : ObjRef) : SLK Iq Kq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyRemoveTcb _ _)

theorem sl_cancelIpc (tptr : ObjRef) : SLK Iq Kq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelIpc _)

theorem sl_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : SLKE Iq Kq m) : SLKE Iq Kq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_capFaultOnFailure _ _ _ ?_)

theorem sl_captransferFromWords (ptr : Word) : SLK Iq Kq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_captransferFromWords _)

theorem sl_getRefills (scPtr : ObjRef) : SLK Iq Kq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefills _)

theorem sl_refillSize (scPtr : ObjRef) : SLK Iq Kq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillSize _)

theorem sl_refillSingle (scPtr : ObjRef) : SLK Iq Kq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillSingle _)

theorem sl_getRefillTail (scPtr : ObjRef) : SLK Iq Kq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefillTail _)

theorem sl_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : SLK Iq Kq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillAddTail _ _)

theorem sl_refillFull (scPtr : ObjRef) : SLK Iq Kq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillFull _)

theorem sl_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : SLK Iq Kq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRefillTl _ _)

theorem sl_scheduleUsed (scPtr : ObjRef) (new : Refill) : SLK Iq Kq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleUsed _ _)

theorem sl_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_chargeEntireHeadRefill _ _)

theorem sl_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : SLK Iq Kq m) : SLK Iq Kq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_checkCapAt _ _ _ ?_)

theorem sl_checkDomainTime  : SLK Iq Kq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkDomainTime)

theorem sl_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : SLKE Iq Kq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkHandlerEp _ _)

theorem sl_checkPrio (newPrio : Data) (authTcb : ObjRef) : SLKE Iq Kq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkPrio _ _)

theorem sl_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : SLKE Iq Kq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkValidIpcBuffer _ _)

theorem sl_nextDomain  : SLK Iq Kq (nextDomain (Z := Unit)) := by
  unfold nextDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_nextDomain)

theorem sl_switchToThread (t : ObjRef) : SLK Iq Kq (switchToThread (Z := Unit) t) := by
  unfold switchToThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchToThread _)

theorem sl_guardedSwitchTo (thread : ObjRef) : SLK Iq Kq (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_guardedSwitchTo _)

theorem sl_switchToIdleThread  : SLK Iq Kq (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchToIdleThread)

theorem sl_chooseThread  : SLK Iq Kq (chooseThread (Z := Unit)) := by
  unfold chooseThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_chooseThread)

theorem sl_getScActive (scPtr : ObjRef) : SLK Iq Kq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScActive _)

theorem sl_handleOverrun (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleOverrun _ _)

theorem sl_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : SLK Iq Kq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_mergeNonoverlappingHeadRefill _)

theorem sl_headInsufficientLoop (scPtr : ObjRef) : SLK Iq Kq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_headInsufficientLoop _)

theorem sl_refillBudgetCheck (usage : Ticks) : SLK Iq Kq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillBudgetCheck _)

theorem sl_refillBudgetCheckRoundRobin (usage : Ticks) : SLK Iq Kq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillBudgetCheckRoundRobin _)

theorem sl_commitTime  : SLK Iq Kq (commitTime (Z := Unit)) := by
  unfold commitTime; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_commitTime)

theorem sl_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : SLKE Iq Kq m) : SLK Iq Kq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_constOnFailure _ _ ?_)

theorem sl_copyGlobalMappings (newPm : ObjRef) : SLK Iq Kq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_copyGlobalMappings _)

theorem sl_loadWordOffs (ptr : ObjRef) (offs : Nat) : SLK Iq Kq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadWordOffs _ _)

theorem sl_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : SLK Iq Kq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_copyMrs _ _ _ _ _)

theorem sl_dataToObjType (type : Data) : SLKE Iq Kq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_dataToObjType _)

theorem sl_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeBindNotification _ _)

theorem sl_deriveCap (slot : CslotPtr) (cap : Cap) : SLKE Iq Kq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deriveCap _ _)

theorem sl_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SLKE Iq Kq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupPivotSlot _ _ _)

theorem sl_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SLKE Iq Kq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupSourceSlot _ _ _)

theorem sl_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeCnodeInvocation _ _ _ _)

theorem sl_slotCapLongRunningDelete (slot : CslotPtr) : SLK Iq Kq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_slotCapLongRunningDelete _)

theorem sl_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeCvSpace _ _ _ _)

theorem sl_subframeNode (nodeCap : Cap) (index depth : Data) : SLKE Iq Kq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_subframeNode _ _ _)

theorem sl_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDeriveSubframe _ _ _ _)

theorem sl_decodeDomainScheduleConfigure (args : List Data) : SLKE Iq Kq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainScheduleConfigure _)

theorem sl_decodeDomainScheduleSetStart (args : List Data) : SLKE Iq Kq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainScheduleSetStart _)

theorem sl_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainSet _ _)

theorem sl_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainInvocation _ _ _)

theorem sl_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : SLK Iq Kq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4GetMr _ _ _)

theorem sl_fl4Arg (buf : Option ObjRef) (i : Nat) : SLKE Iq Kq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4Arg _ _)

theorem sl_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4ConfigureSingleStepping _ _)

theorem sl_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4FpuTransfer _ _ _ _)

theorem sl_fl4CheckBpNum (bp : Data) : SLKE Iq Kq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4CheckBpNum _)

theorem sl_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4GetBreakpoint _ _)

theorem sl_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, SLKE Iq Kq (check x0)) : SLKE Iq Kq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; sl_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem sl_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqControlRemapped _ _ _)

theorem sl_fl4ArchCheckIrq (irq : Data) : SLKE Iq Kq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ArchCheckIrq _)

theorem sl_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4IrqControl _ _ _ _ _)

theorem sl_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetBreakpoint _ _)

theorem sl_decodeFl4SetFlags (args : List Data) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetFlags _ _)

theorem sl_decodeFl4SetTimer (args : List Data) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetTimer _ _)

theorem sl_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4UnsetBreakpoint _ _)

theorem sl_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : SLKE Iq Kq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4TcbExt _ _ _ _ _)

theorem sl_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqControlInvocation _ _ _ _)

theorem sl_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqHandlerInvocation _ _ _)

theorem sl_getScReleased (scPtr : ObjRef) : SLK Iq Kq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScReleased _)

theorem sl_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextBind _ _)

theorem sl_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : SLK Iq Kq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScObjRef _ _)

theorem sl_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextUnbindObject _ _)

theorem sl_decodeSchedContextYieldTo (scPtr : ObjRef) : SLKE Iq Kq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextYieldTo _)

theorem sl_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextInvocation _ _ _)

theorem sl_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : SLKE Iq Kq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedControlInvocationFlags _ _ _)

theorem sl_rangeCheck (v minV maxV : Word) : SLKE Iq Kq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_rangeCheck _ _ _)

theorem sl_decodeSetFlags (args : List Data) (cap : Cap) : SLKE Iq Kq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetFlags _ _)

theorem sl_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetIpcBuffer _ _ _ _)

theorem sl_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetMcpriority _ _ _ _)

theorem sl_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetPriority _ _ _ _)

theorem sl_isBlocked (thread : ObjRef) : SLK Iq Kq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isBlocked _)

theorem sl_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : SLKE Iq Kq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUpdateSc _ _ _)

theorem sl_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetSchedParams _ _ _ _)

theorem sl_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetSpace _ _ _ _)

theorem sl_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetTimeoutEp _ _ _)

theorem sl_decodeSetTlsBase (args : List Data) (cap : Cap) : SLKE Iq Kq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetTlsBase _ _)

theorem sl_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTcbConfigure _ _ _ _)

theorem sl_decodeUnbindNotification (cap : Cap) : SLKE Iq Kq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem sl_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTcbInvocation _ _ _ _ _)

theorem sl_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUntypedInvocation _ _ _ _ _)

theorem sl_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : SLKE Iq Kq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeInvocation _ _ _ _ _ _ _ _)

theorem sl_decodePml4Flush (cap : ArchCap) : SLKE Iq Kq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePml4Flush _)

theorem sl_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : SLKE Iq Kq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_frameMappingSlot _ _ _ _)

theorem sl_decodeTestAndClearAccessed (cap : ArchCap) : SLKE Iq Kq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTestAndClearAccessed _)

theorem sl_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem sl_deletedIrqHandler (irq : Irq) : SLK Iq Kq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deletedIrqHandler _)

theorem sl_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : SLK Iq Kq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_makeArchFaultMsg _ _)

theorem sl_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : SLK Iq Kq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_makeFaultMsg _ _)

theorem sl_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : SLK Iq Kq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doFaultTransfer _ _ _ _)

theorem sl_getMessageInfo (thread : ObjRef) : SLK Iq Kq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getMessageInfo _)

theorem sl_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : SLK Iq Kq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; sl_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getExtraCptrs _ _)

theorem sl_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : SLKE Iq Kq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupSlotForThread _ _)

theorem sl_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : SLKE Iq Kq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupCapAndSlot _ _)

theorem sl_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SLKE Iq Kq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupExtraCaps _ _ _)

theorem sl_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : SLKE Iq Kq m) : SLK Iq Kq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_emptyOnFailure _ ?_)

theorem sl_loadCapTransfer (buffer : ObjRef) : SLK Iq Kq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadCapTransfer _)

theorem sl_lookupCap (thread : ObjRef) (ref : CapRef) : SLKE Iq Kq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupCap _ _)

theorem sl_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : SLKE Iq Kq m) : SLKE Iq Kq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_unifyFailure _ ?_)

theorem sl_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : SLK Iq Kq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getReceiveSlots _ _)

theorem sl_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : SLK Iq Kq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setExtraBadge _ _ _)

theorem sl_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      SLK Iq Kq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; sl_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => sl_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | sl_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_transferCapsLoop _ _ _ _ _ _)

theorem sl_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : SLK Iq Kq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_transferCaps _ _ _ _ _)

theorem sl_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SLK Iq Kq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doNormalTransfer _ _ _ _ _ _ _)

theorem sl_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : SLK Iq Kq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doIpcTransfer _ _ _ _ _)

theorem sl_doNbrecvFailedTransfer (thread : ObjRef) : SLK Iq Kq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doNbrecvFailedTransfer _)

theorem sl_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : SLK Iq Kq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_domainScheduleConfigure _ _ _)

theorem sl_setNextInterrupt  : SLK Iq Kq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setNextInterrupt)

theorem sl_switchSchedContext  : SLK Iq Kq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchSchedContext)

theorem sl_scAndTimer  : SLK Iq Kq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scAndTimer)

theorem sl_scheduleChooseNewThread  : SLK Iq Kq (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleChooseNewThread)

theorem sl_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : SLK Iq Kq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleSwitchThreadFastfail _ _ _ _)

theorem sl_schedule  : SLK Iq Kq (schedule (Z := Unit)) := by
  unfold schedule; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedule)

theorem sl_domainSetStart (index : Nat) : SLK Iq Kq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_domainSetStart _)

theorem sl_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem sl_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SLKE Iq Kq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem sl_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : SLKE Iq Kq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sl_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : SLK Iq Kq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ReplyFromKernelError _ _ _)

theorem sl_fl4SyscallFaultIP (thread : ObjRef) : SLK Iq Kq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4SyscallFaultIP _)

theorem sl_getCapReg (reg : Register) : SLK Iq Kq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getCapReg _)

theorem sl_getIrqSlot (irq : Irq) : SLK Iq Kq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getIrqSlot _)

theorem sl_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SLK Iq Kq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getMrs _ _ _)

theorem sl_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : SLK Iq Kq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleArchFaultReply _ _ _ _)

theorem sl_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : SLK Iq Kq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleFaultReply _ _ _ _)

theorem sl_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : SLK Iq Kq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleHypervisorFault _ _)

theorem sl_handleNoFault (tptr : ObjRef) : SLK Iq Kq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleNoFault _)

theorem sl_handleReservedIrq (_irq : Irq) : SLK Iq Kq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleReservedIrq _)

theorem sl_handleSpuriousIrq  : SLK Iq Kq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleSpuriousIrq)

theorem sl_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : SLKE Iq Kq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleVmFault _ _)

theorem sl_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : SLK Iq Kq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_initArchObjects _ _ _ _ _ _)

theorem sl_threadSetDomain (tptr : ObjRef) (domain : Domain) : SLK Iq Kq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_threadSetDomain _ _)

theorem sl_setDomain (tptr : ObjRef) (newDom : Domain) : SLK Iq Kq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setDomain _ _)

theorem sl_invokeSetDomain (thread : ObjRef) (domain : Domain) : SLK Iq Kq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeSetDomain _ _)

theorem sl_invokeDomain (domInv : DomainInvocation) : SLK Iq Kq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeDomain _)

theorem sl_invokeIrqControl (a0 : IrqControlInvocation) : SLKE Iq Kq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeIrqControl _)

theorem sl_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : SLKE Iq Kq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeFl4IrqControl _)

theorem sl_invokeFl4Tcb (a0 : Fl4TcbInvocation) : SLKE Iq Kq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeFl4Tcb _)

theorem sl_maybeAddEmptyTail (scPtr : ObjRef) : SLK Iq Kq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_maybeAddEmptyTail _)

theorem sl_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : SLK Iq Kq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillNew _ _ _ _)

theorem sl_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : SLK Iq Kq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillUpdate _ _ _ _)

theorem sl_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : SLK Iq Kq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_orderedInsert _ _ _ _)

theorem sl_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : SLK Iq Kq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_readyTimesAppend _ _)

theorem sl_tcbReleaseEnqueue (tcbPtr : ObjRef) : SLK Iq Kq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseEnqueue _)

theorem sl_postpone (scPtr : ObjRef) : SLK Iq Kq (postpone (Z := Unit) scPtr) := by
  unfold postpone; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_postpone _)

theorem sl_schedContextResume (scPtr : ObjRef) : SLK Iq Kq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextResume _)

theorem sl_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : SLK Iq Kq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeSchedControlConfigureFlags _)

theorem sl_isValidTimeoutHandler (tptr : ObjRef) : SLK Iq Kq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isValidTimeoutHandler _)

theorem sl_lookupReply  : SLKE Iq Kq (lookupReply (Z := Unit)) := by
  unfold lookupReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupReply)

theorem sl_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : SLK Iq Kq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_maybeReturnSc _ _)

theorem sl_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : SLKE Iq Kq f) (h_g : SLKE Iq Kq g) : SLKE Iq Kq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; sl_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_orChoiceE _ _ _ ?_ ?_)

theorem sl_portIn (f : MachineMonad Data) : SLK Iq Kq (portIn (Z := Unit) f) := by
  unfold portIn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_portIn _)

theorem sl_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : SLK Iq Kq (portOut (Z := Unit) f w) := by
  unfold portOut; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_portOut _ _)

theorem sl_performIoPortInvocation (i : IoPortInvocation) : SLK Iq Kq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performIoPortInvocation _)

theorem sl_performIoportControlInvocation (i : IoPortControlInvocation) : SLK Iq Kq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performIoportControlInvocation _)

theorem sl_performPml4Flush (a0 : Fl4Pml4Invocation) : SLK Iq Kq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performPml4Flush _)

theorem sl_performTestAndClearAccessed (_slot : ObjRef) : SLK Iq Kq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performTestAndClearAccessed _)

theorem sl_postCapDeletion (cap : Cap) : SLK Iq Kq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_postCapDeletion _)

theorem sl_updateTimeStamp  : SLK Iq Kq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateTimeStamp)

theorem sl_preemptionPoint  : SLKE Iq Kq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_preemptionPoint)

theorem sl_prepareThreadDelete (threadPtr : ObjRef) : SLK Iq Kq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_prepareThreadDelete _)

theorem sl_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : SLK Iq Kq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbAppend _ _)

theorem sl_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : SLK Iq Kq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbEpAppend _ _ _)

theorem sl_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : SLK Iq Kq (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_receiveIpcBlocked _ _ _ _)

theorem sl_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : SLK Iq Kq (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbNtfnAppend _ _)

theorem sl_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : SLK Iq Kq (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_receiveSignalBlocked _ _ _)

theorem sl_refillResetRr (cscPtr : ObjRef) : SLK Iq Kq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillResetRr _)

theorem sl_reorderEp (epPtr tptr : ObjRef) : SLK Iq Kq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_reorderEp _ _)

theorem sl_reorderNtfn (ntfnPtr tptr : ObjRef) : SLK Iq Kq (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_reorderNtfn _ _)

theorem sl_replyUnlinkSc (scPtr replyPtr : ObjRef) : SLK Iq Kq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyUnlinkSc _ _)

theorem sl_testPossibleSwitchTo (tcbPtr : ObjRef) : SLK Iq Kq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_testPossibleSwitchTo _)

theorem sl_restart (thread : ObjRef) : SLK Iq Kq (restart (Z := Unit) thread) := by
  unfold restart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_restart _)

theorem sl_returnConsumed (scPtr : ObjRef) : SLK Iq Kq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_returnConsumed _)

theorem sl_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : SLK Iq Kq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextMaybeUnbindNtfn _)

theorem sl_schedContextSetInactive (scPtr : ObjRef) : SLK Iq Kq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextSetInactive _)

theorem sl_schedContextUnbindTcb (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindTcb _)

theorem sl_schedContextUnbindAllTcbs (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindAllTcbs _)

theorem sl_schedContextUnbindNtfn (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindNtfn _)

theorem sl_schedContextUnbindReply (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindReply _)

theorem sl_schedContextUnbindYieldFrom (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindYieldFrom _)

theorem sl_schedContextYieldTo (scPtr : ObjRef) : SLK Iq Kq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextYieldTo _)

theorem sl_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : SLK Iq Kq (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_sendIpcBlocked _ _ _ _ _ _)

theorem sl_setFlags (ref : ObjRef) (flags : TcbFlags) : SLK Iq Kq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setFlags _ _)

theorem sl_setMcpriority (ref : ObjRef) (mcp : Priority) : SLK Iq Kq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setMcpriority _ _)

theorem sl_threadSetPriority (tptr : ObjRef) (prio : Priority) : SLK Iq Kq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_threadSetPriority _ _)

theorem sl_setPriority (tptr : ObjRef) (prio : Priority) : SLK Iq Kq (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPriority _ _)

theorem sl_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : SLK Iq Kq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storeAsidPoolEntry _ _ _)

theorem sl_updateRestartPc (threadPtr : ObjRef) : SLK Iq Kq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRestartPc _)

theorem sl_suspend (thread : ObjRef) : SLK Iq Kq (suspend (Z := Unit) thread) := by
  unfold suspend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_suspend _)

theorem sl_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : SLKE Iq Kq mFault) (h_hFault : ∀ x0, SLK Iq Kq (hFault x0)) (h_mError : ∀ x0, SLKE Iq Kq (mError x0)) (h_hError : ∀ x0, SLK Iq Kq (hError x0)) (h_mFinalise : ∀ x0, SLKE Iq Kq (mFinalise x0)) : SLKE Iq Kq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; sl_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem sl_testReschedule (fromTptr : ObjRef) : SLK Iq Kq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_testReschedule _)

theorem sl_unbindFromSc (tcbPtr : ObjRef) : SLK Iq Kq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindFromSc _)

theorem sl_unbindMaybeNotification (ntfnptr : ObjRef) : SLK Iq Kq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindMaybeNotification _)

theorem sl_unbindNotification (tcb : ObjRef) : SLK Iq Kq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindNotification _)
