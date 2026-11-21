theorem sb_archActivateIdleThread (_t : ObjRef) : SBK h0 (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archActivateIdleThread _)

theorem sb_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : SBK h0 (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_threadGet _ _)

theorem sb_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : SBK h0 (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getTcbObjRef _ _)

theorem sb_schedContextCancelYieldTo (thread : ObjRef) : SBK h0 (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextCancelYieldTo _)

theorem sb_getCap (a0 : CslotPtr) : SBK h0 (getCap (Z := Unit) a0) := by
  unfold getCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getCap _)

theorem sb_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : SBK h0 (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupIpcBuffer _ _)

theorem sb_setMessageInfo (thread : ObjRef) (info : MessageInfo) : SBK h0 (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setMessageInfo _ _)

theorem sb_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : SBK h0 (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storeWordOffs _ _ _)

theorem sb_replyFromKernel (thread : ObjRef) (x : Data × List Data) : SBK h0 (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_replyFromKernel _ _)

theorem sb_getSchedContext (ptr : ObjRef) : SBK h0 (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getSchedContext _)

theorem sb_schedContextUpdateConsumed (scPtr : ObjRef) : SBK h0 (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextUpdateConsumed _)

theorem sb_setConsumed (scPtr tcbPtr : ObjRef) : SBK h0 (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setConsumed _ _)

theorem sb_completeYieldTo (tcbPtr : ObjRef) : SBK h0 (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_completeYieldTo _)

theorem sb_getThreadState (ref : ObjRef) : SBK h0 (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getThreadState _)

theorem sb_setSchedulerAction (action : SchedulerAction) : SBK h0 (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setSchedulerAction _)

theorem sb_setThreadStateAct (tcbPtr : ObjRef) : SBK h0 (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setThreadStateAct _)

theorem sb_activateThread  : SBK h0 (activateThread (Z := Unit)) := by
  unfold activateThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_activateThread)

theorem sb_archCheckIrq (_irq : Data) : SBKE h0 (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archCheckIrq _)

theorem sb_ensureEmpty (slot : CslotPtr) : SBKE h0 (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_ensureEmpty _)

theorem sb_isIoportRangeFree (f l : IoPort) : SBK h0 (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isIoportRangeFree _ _)

theorem sb_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : SBKE h0 m) : SBKE h0 (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_lookupErrorOnFailure _ _ ?_)

theorem sb_resolveAddressBits' (p : Cap × CapRef) : SBKE h0 (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by sb_auto)) fun nc => ?_
        split
        · exact sb_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_resolveAddressBits' _)

theorem sb_resolveAddressBits (a0 : Cap × CapRef) : SBKE h0 (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_resolveAddressBits _)

theorem sb_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : SBKE h0 (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupSlotForCnodeOp _ _ _ _)

theorem sb_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SBKE h0 (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupTargetSlot _ _ _)

theorem sb_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : SBKE h0 (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeIoportControlInvocation _ _ _ _ _)

theorem sb_getAsidPool (ptr : ObjRef) : SBK h0 (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getAsidPool _)

theorem sb_findVspaceForAsid (asid : Asid) : SBKE h0 (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_findVspaceForAsid _)

theorem sb_getPdpt (ptr : ObjRef) : SBK h0 (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPdpt _)

theorem sb_getPdpte (ptr : ObjRef) : SBK h0 (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPdpte _)

theorem sb_isFinalCap (cap : Cap) : SBK h0 (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isFinalCap _)

theorem sb_getPml4 (ptr : ObjRef) : SBK h0 (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPml4 _)

theorem sb_getPml4e (ptr : ObjRef) : SBK h0 (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPml4e _)

theorem sb_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : SBKE h0 (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupPdptSlot _ _)

theorem sb_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePageDirectoryInvocation _ _ _ _ _)

theorem sb_checkVpAlignment (sz : VMPageSize) (vptr : Word) : SBKE h0 (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_checkVpAlignment _ _)

theorem sb_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : SBKE h0 (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupPdSlot _ _)

theorem sb_getPd (ptr : ObjRef) : SBK h0 (getPd (Z := Unit) ptr) := by
  unfold getPd; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPd _)

theorem sb_getPde (ptr : ObjRef) : SBK h0 (getPde (Z := Unit) ptr) := by
  unfold getPde; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPde _)

theorem sb_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : SBKE h0 (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupPtSlot _ _)

theorem sb_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : SBKE h0 (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_createMappingEntries _ _ _ _ _ _)

theorem sb_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : SBKE h0 (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_ensureSafeMapping _)

theorem sb_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePageInvocation _ _ _ _ _)

theorem sb_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePageTableInvocation _ _ _ _ _)

theorem sb_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePdptInvocation _ _ _ _ _)

theorem sb_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : SBKE h0 (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_ensurePortOperationAllowed _ _ _)

theorem sb_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : SBKE h0 (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePortInvocation _ _ _)

theorem sb_ensureNoChildren (cslotPtr : CslotPtr) : SBKE h0 (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_ensureNoChildren _)

theorem sb_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : SBK h0 (selectExt (Z := Unit) a S) := by
  unfold selectExt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_selectExt _ _)

theorem sb_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archDecodeInvocation _ _ _ _ _ _)

theorem sb_getIrqState (irq : Irq) : SBK h0 (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getIrqState _)

theorem sb_isIrqActive (irq : Irq) : SBK h0 (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isIrqActive _)

theorem sb_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SBKE h0 (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archDecodeIrqControlInvocation _ _ _ _)

theorem sb_archDeriveCap (c : ArchCap) : SBKE h0 (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archDeriveCap _)

theorem sb_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : SBK h0 (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_hwAsidInvalidate _ _)

theorem sb_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SBK h0 (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setAsidPool _ _)

theorem sb_getCurrentCr3  : SBK h0 (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getCurrentCr3)

theorem sb_setCurrentCr3 (c : Cr3) : SBK h0 (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setCurrentCr3 _)

theorem sb_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : SBK h0 (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setCurrentVspaceRoot _ _)

theorem sb_setVmRoot (tcb : ObjRef) : SBK h0 (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setVmRoot _)

theorem sb_deleteAsid (asid : Asid) (pml4 : ObjRef) : SBK h0 (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_deleteAsid _ _)

theorem sb_deleteAsidPool (base : Asid) (ptr : ObjRef) : SBK h0 (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_deleteAsidPool _ _)

theorem sb_getPt (ptr : ObjRef) : SBK h0 (getPt (Z := Unit) ptr) := by
  unfold getPt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPt _)

theorem sb_getPte (ptr : ObjRef) : SBK h0 (getPte (Z := Unit) ptr) := by
  unfold getPte; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getPte _)

theorem sb_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SBK h0 (setPd (Z := Unit) ptr pd) := by
  unfold setPd; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setPd _ _)

theorem sb_storePde (p : ObjRef) (pde : PDE) : SBK h0 (storePde (Z := Unit) p pde) := by
  unfold storePde; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storePde _ _)

theorem sb_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SBK h0 (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setPdpt _ _)

theorem sb_storePdpte (p : ObjRef) (pte : PDPTE) : SBK h0 (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storePdpte _ _)

theorem sb_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SBK h0 (setPt (Z := Unit) ptr pt) := by
  unfold setPt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setPt _ _)

theorem sb_storePte (p : ObjRef) (pte : PTE) : SBK h0 (storePte (Z := Unit) p pte) := by
  unfold storePte; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storePte _ _)

theorem sb_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SBK h0 (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unmapPage _ _ _ _)

theorem sb_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : SBK h0 (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_flushTable _ _ _ _)

theorem sb_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SBK h0 (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invalidatePageStructureCacheAsid _ _)

theorem sb_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SBK h0 (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unmapPageTable _ _ _)

theorem sb_flushAll (vspace : ObjRef) (asid : Asid) : SBK h0 (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_flushAll _ _)

theorem sb_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SBK h0 (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unmapPd _ _ _)

theorem sb_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SBK h0 (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setPml4 _ _)

theorem sb_storePml4e (p : ObjRef) (pte : PML4E) : SBK h0 (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storePml4e _ _)

theorem sb_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SBK h0 (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unmapPdpt _ _ _)

theorem sb_archFinaliseCap (c : ArchCap) (x : Bool) : SBK h0 (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archFinaliseCap _ _)

theorem sb_archGetSanitiseRegisterInfo (_t : ObjRef) : SBK h0 (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archGetSanitiseRegisterInfo _)

theorem sb_setOriginal (slot : CslotPtr) (v : Bool) : SBK h0 (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setOriginal _ _)

theorem sb_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : SBK h0 (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setUntypedCapAsFull _ _ _)

theorem sb_setCdt (t : Cdt) : SBK h0 (setCdt (Z := Unit) t) := by
  unfold setCdt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setCdt _)

theorem sb_updateCdt (f : Cdt → Cdt) : SBK h0 (updateCdt (Z := Unit) f) := by
  unfold updateCdt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateCdt _)

theorem sb_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : SBK h0 (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_capInsert _ _ _)

theorem sb_setIrqState (state : IrqState) (irq : Irq) : SBK h0 (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setIrqState _ _)

theorem sb_updateIrqState (irq : Irq) (irqState : X64IRQState) : SBK h0 (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateIrqState _ _)

theorem sb_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : SBK h0 m) : SBKE h0 (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_withoutPreemption _ ?_)

theorem sb_archInvokeIrqControl (aic : ArchIrqControlInvocation) : SBKE h0 (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archInvokeIrqControl _)

theorem sb_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : SBK h0 (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archInvokeIrqHandler _)

theorem sb_archMaskIrqSignal (irq : Irq) : SBK h0 (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archMaskIrqSignal _)

theorem sb_setIoportMask (f l : IoPort) (val : Bool) : SBK h0 (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setIoportMask _ _ _)

theorem sb_freeIoportRange (f l : IoPort) : SBK h0 (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_freeIoportRange _ _)

theorem sb_archPostCapDeletion (ac : ArchCap) : SBK h0 (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPostCapDeletion _)

theorem sb_archPostModifyRegisters (cur t : ObjRef) : SBK h0 (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPostModifyRegisters _ _)

theorem sb_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : SBK h0 (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPostResetUntyped _ _)

theorem sb_loadFpuState (t : ObjRef) : SBK h0 (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_loadFpuState _)

theorem sb_saveFpuState (t : ObjRef) : SBK h0 (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_saveFpuState _)

theorem sb_setX64CurrentFpuOwner (newOwner : Option ObjRef) : SBK h0 (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setX64CurrentFpuOwner _)

theorem sb_switchLocalFpuOwner (newOwner : Option ObjRef) : SBK h0 (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_switchLocalFpuOwner _)

theorem sb_fpuRelease (threadPtr : ObjRef) : SBK h0 (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fpuRelease _)

theorem sb_lazyFpuRestore (threadPtr : ObjRef) : SBK h0 (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lazyFpuRestore _)

theorem sb_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : SBK h0 (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPostSetFlags _ _)

theorem sb_archPrepareNextDomain  : SBK h0 (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPrepareNextDomain)

theorem sb_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : SBK h0 (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archPrepareSetDomain _ _)

theorem sb_archSwitchToIdleThread  : SBK h0 (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archSwitchToIdleThread)

theorem sb_archSwitchToThread (t : ObjRef) : SBK h0 (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_archSwitchToThread _)

theorem sb_getScRefillReady (scPtr : ObjRef) : SBK h0 (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getScRefillReady _)

theorem sb_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : SBK h0 (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getScRefillSufficient _ _)

theorem sb_getTcbQueue (d : Domain) (prio : Priority) : SBK h0 (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getTcbQueue _ _)

theorem sb_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : SBK h0 (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setTcbQueue _ _ _)

theorem sb_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : SBK h0 (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbSchedAction _ _)

theorem sb_rescheduleRequired  : SBK h0 (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_rescheduleRequired)

theorem sb_possibleSwitchTo (target : ObjRef) : SBK h0 (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_possibleSwitchTo _)

theorem sb_tcbReleaseRemove (tcbPtr : ObjRef) : SBK h0 (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbReleaseRemove _)

theorem sb_tcbReleaseDequeue  : SBK h0 (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbReleaseDequeue)

theorem sb_awaken  : SBK h0 (awaken (Z := Unit)) := by
  unfold awaken; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_awaken)

theorem sb_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : SBK h0 (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getSimpleKo _ _)

theorem sb_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : SBK h0 (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateSkObjRef _ _ _ _)

theorem sb_bindNotification (tcbptr ntfnptr : ObjRef) : SBK h0 (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_bindNotification _ _)

theorem sb_bindScReply (scPtr replyPtr : ObjRef) : SBK h0 (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_bindScReply _ _)

theorem sb_getBlockingObject (state : ThreadState) : SBK h0 (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getBlockingObject _)

theorem sb_replyUnlinkTcb (t r : ObjRef) : SBK h0 (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_replyUnlinkTcb _ _)

theorem sb_tcbEpDequeue (tptr epPtr : ObjRef) : SBK h0 (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbEpDequeue _ _)

theorem sb_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : SBK h0 (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_blockedCancelIpc _ _ _)

theorem sb_isRoundRobin (scPtr : ObjRef) : SBK h0 (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isRoundRobin _)

theorem sb_getRefillHead (scPtr : ObjRef) : SBK h0 (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getRefillHead _)

theorem sb_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : SBK h0 (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateRefillHd _ _)

theorem sb_refillHeadOverlappingLoop (scPtr : ObjRef) : SBK h0 (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillHeadOverlappingLoop _)

theorem sb_refillUnblockCheck (scPtr : ObjRef) : SBK h0 (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillUnblockCheck _)

theorem sb_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : SBK h0 (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_ifCondRefillUnblockCheck _ _ _)

theorem sb_restartThreadIfNoFault (t : ObjRef) : SBK h0 (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_restartThreadIfNoFault _)

theorem sb_removeAndRestartEpQueuedThread (t epptr : ObjRef) : SBK h0 (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_removeAndRestartEpQueuedThread _ _)

theorem sb_cancelAllIpc (epptr : ObjRef) : SBK h0 (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_cancelAllIpc _)

theorem sb_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : SBK h0 (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbNtfnDequeue _ _)

theorem sb_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : SBK h0 (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_removeAndRestartNtfnQueuedThread _ _)

theorem sb_cancelAllSignals (ntfnptr : ObjRef) : SBK h0 (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_cancelAllSignals _)

theorem sb_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : SBK h0 (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_removeAndRestartBadgedThread _ _ _)

theorem sb_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : SBK h0 (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_cancelBadgedSends _ _)

theorem sb_cancelSignal (threadptr ntfnptr : ObjRef) : SBK h0 (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_cancelSignal _ _)

theorem sb_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : SBK h0 (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getSkObjRef _ _ _)

theorem sb_replyRemoveTcb (tptr rptr : ObjRef) : SBK h0 (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_replyRemoveTcb _ _)

theorem sb_cancelIpc (tptr : ObjRef) : SBK h0 (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_cancelIpc _)

theorem sb_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : SBKE h0 m) : SBKE h0 (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_capFaultOnFailure _ _ _ ?_)

theorem sb_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : SBK h0 (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_capMove _ _ _)

theorem sb_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : SBK h0 (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_capSwap _ _ _ _)

theorem sb_capSwapForDelete (slot1 slot2 : CslotPtr) : SBK h0 (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_capSwapForDelete _ _)

theorem sb_captransferFromWords (ptr : Word) : SBK h0 (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_captransferFromWords _)

theorem sb_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : SBK h0 m) : SBK h0 (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_checkCapAt _ _ _ ?_)

theorem sb_checkDomainTime  : SBK h0 (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_checkDomainTime)

theorem sb_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : SBKE h0 (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_checkHandlerEp _ _)

theorem sb_checkPrio (newPrio : Data) (authTcb : ObjRef) : SBKE h0 (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_checkPrio _ _)

theorem sb_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : SBKE h0 (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_checkValidIpcBuffer _ _)

theorem sb_nextDomain  : SBK h0 (nextDomain (Z := Unit)) := by
  unfold nextDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_nextDomain)

theorem sb_switchToThread (t : ObjRef) : SBK h0 (switchToThread (Z := Unit) t) := by
  unfold switchToThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_switchToThread _)

theorem sb_guardedSwitchTo (thread : ObjRef) : SBK h0 (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_guardedSwitchTo _)

theorem sb_switchToIdleThread  : SBK h0 (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_switchToIdleThread)

theorem sb_chooseThread  : SBK h0 (chooseThread (Z := Unit)) := by
  unfold chooseThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_chooseThread)

theorem sb_getScActive (scPtr : ObjRef) : SBK h0 (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getScActive _)

theorem sb_getRefills (scPtr : ObjRef) : SBK h0 (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getRefills _)

theorem sb_refillSize (scPtr : ObjRef) : SBK h0 (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillSize _)

theorem sb_refillSingle (scPtr : ObjRef) : SBK h0 (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillSingle _)

theorem sb_getRefillTail (scPtr : ObjRef) : SBK h0 (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getRefillTail _)

theorem sb_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : SBK h0 (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillAddTail _ _)

theorem sb_refillFull (scPtr : ObjRef) : SBK h0 (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillFull _)

theorem sb_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : SBK h0 (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateRefillTl _ _)

theorem sb_scheduleUsed (scPtr : ObjRef) (new : Refill) : SBK h0 (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_scheduleUsed _ _)

theorem sb_handleOverrun (scPtr : ObjRef) (usage : Ticks) : SBK h0 (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleOverrun _ _)

theorem sb_headInsufficientLoop (scPtr : ObjRef) : SBK h0 (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_headInsufficientLoop _)

theorem sb_refillBudgetCheck (usage : Ticks) : SBK h0 (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillBudgetCheck _)

theorem sb_refillBudgetCheckRoundRobin (usage : Ticks) : SBK h0 (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillBudgetCheckRoundRobin _)

theorem sb_commitTime  : SBK h0 (commitTime (Z := Unit)) := by
  unfold commitTime; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_commitTime)

theorem sb_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : SBKE h0 m) : SBK h0 (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_constOnFailure _ _ ?_)

theorem sb_copyGlobalMappings (newPm : ObjRef) : SBK h0 (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_copyGlobalMappings _)

theorem sb_loadWordOffs (ptr : ObjRef) (offs : Nat) : SBK h0 (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_loadWordOffs _ _)

theorem sb_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : SBK h0 (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_copyMrs _ _ _ _ _)

theorem sb_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : SBK h0 (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_createCap _ _ _ _ _)

theorem sb_dataToObjType (type : Data) : SBKE h0 (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_dataToObjType _)

theorem sb_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeBindNotification _ _)

theorem sb_deriveCap (slot : CslotPtr) (cap : Cap) : SBKE h0 (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_deriveCap _ _)

theorem sb_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SBKE h0 (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupPivotSlot _ _ _)

theorem sb_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SBKE h0 (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupSourceSlot _ _ _)

theorem sb_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : SBKE h0 (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeCnodeInvocation _ _ _ _)

theorem sb_slotCapLongRunningDelete (slot : CslotPtr) : SBK h0 (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_slotCapLongRunningDelete _)

theorem sb_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SBKE h0 (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeCvSpace _ _ _ _)

theorem sb_subframeNode (nodeCap : Cap) (index depth : Data) : SBKE h0 (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_subframeNode _ _ _)

theorem sb_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : SBKE h0 (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeDeriveSubframe _ _ _ _)

theorem sb_decodeDomainScheduleConfigure (args : List Data) : SBKE h0 (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeDomainScheduleConfigure _)

theorem sb_decodeDomainScheduleSetStart (args : List Data) : SBKE h0 (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeDomainScheduleSetStart _)

theorem sb_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : SBKE h0 (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeDomainSet _ _)

theorem sb_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : SBKE h0 (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeDomainInvocation _ _ _)

theorem sb_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : SBK h0 (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4GetMr _ _ _)

theorem sb_fl4Arg (buf : Option ObjRef) (i : Nat) : SBKE h0 (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4Arg _ _)

theorem sb_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : SBKE h0 (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4ConfigureSingleStepping _ _)

theorem sb_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : SBKE h0 (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4FpuTransfer _ _ _ _)

theorem sb_fl4CheckBpNum (bp : Data) : SBKE h0 (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4CheckBpNum _)

theorem sb_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SBKE h0 (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4GetBreakpoint _ _)

theorem sb_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, SBKE h0 (check x0)) : SBKE h0 (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; sb_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem sb_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SBKE h0 (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeIrqControlRemapped _ _ _)

theorem sb_fl4ArchCheckIrq (irq : Data) : SBKE h0 (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4ArchCheckIrq _)

theorem sb_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SBKE h0 (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4IrqControl _ _ _ _ _)

theorem sb_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SBKE h0 (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4SetBreakpoint _ _)

theorem sb_decodeFl4SetFlags (args : List Data) (t : ObjRef) : SBKE h0 (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4SetFlags _ _)

theorem sb_decodeFl4SetTimer (args : List Data) (t : ObjRef) : SBKE h0 (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4SetTimer _ _)

theorem sb_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SBKE h0 (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4UnsetBreakpoint _ _)

theorem sb_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : SBKE h0 (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeFl4TcbExt _ _ _ _ _)

theorem sb_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SBKE h0 (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeIrqControlInvocation _ _ _ _)

theorem sb_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : SBKE h0 (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeIrqHandlerInvocation _ _ _)

theorem sb_getScReleased (scPtr : ObjRef) : SBK h0 (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getScReleased _)

theorem sb_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : SBKE h0 (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSchedContextBind _ _)

theorem sb_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : SBK h0 (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getScObjRef _ _)

theorem sb_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : SBKE h0 (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSchedContextUnbindObject _ _)

theorem sb_decodeSchedContextYieldTo (scPtr : ObjRef) : SBKE h0 (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSchedContextYieldTo _)

theorem sb_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : SBKE h0 (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSchedContextInvocation _ _ _)

theorem sb_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : SBKE h0 (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSchedControlInvocationFlags _ _ _)

theorem sb_rangeCheck (v minV maxV : Word) : SBKE h0 (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_rangeCheck _ _ _)

theorem sb_decodeSetFlags (args : List Data) (cap : Cap) : SBKE h0 (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetFlags _ _)

theorem sb_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : SBKE h0 (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetIpcBuffer _ _ _ _)

theorem sb_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetMcpriority _ _ _ _)

theorem sb_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetPriority _ _ _ _)

theorem sb_isBlocked (thread : ObjRef) : SBK h0 (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isBlocked _)

theorem sb_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : SBKE h0 (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeUpdateSc _ _ _)

theorem sb_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetSchedParams _ _ _ _)

theorem sb_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SBKE h0 (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetSpace _ _ _ _)

theorem sb_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetTimeoutEp _ _ _)

theorem sb_decodeSetTlsBase (args : List Data) (cap : Cap) : SBKE h0 (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeSetTlsBase _ _)

theorem sb_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeTcbConfigure _ _ _ _)

theorem sb_decodeUnbindNotification (cap : Cap) : SBKE h0 (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem sb_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SBKE h0 (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeTcbInvocation _ _ _ _ _)

theorem sb_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SBKE h0 (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeUntypedInvocation _ _ _ _ _)

theorem sb_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : SBKE h0 (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeInvocation _ _ _ _ _ _ _ _)

theorem sb_decodePml4Flush (cap : ArchCap) : SBKE h0 (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodePml4Flush _)

theorem sb_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : SBKE h0 (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_frameMappingSlot _ _ _ _)

theorem sb_decodeTestAndClearAccessed (cap : ArchCap) : SBKE h0 (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeTestAndClearAccessed _)

theorem sb_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SBKE h0 (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem sb_deletedIrqHandler (irq : Irq) : SBK h0 (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_deletedIrqHandler _)

theorem sb_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : SBK h0 (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_makeArchFaultMsg _ _)

theorem sb_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : SBK h0 (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_makeFaultMsg _ _)

theorem sb_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : SBK h0 (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_doFaultTransfer _ _ _ _)

theorem sb_getMessageInfo (thread : ObjRef) : SBK h0 (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getMessageInfo _)

theorem sb_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : SBK h0 (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; sb_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getExtraCptrs _ _)

theorem sb_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : SBKE h0 (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupSlotForThread _ _)

theorem sb_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : SBKE h0 (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupCapAndSlot _ _)

theorem sb_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SBKE h0 (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupExtraCaps _ _ _)

theorem sb_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : SBKE h0 m) : SBK h0 (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_emptyOnFailure _ ?_)

theorem sb_loadCapTransfer (buffer : ObjRef) : SBK h0 (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_loadCapTransfer _)

theorem sb_lookupCap (thread : ObjRef) (ref : CapRef) : SBKE h0 (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupCap _ _)

theorem sb_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : SBKE h0 m) : SBKE h0 (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; sb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_unifyFailure _ ?_)

theorem sb_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : SBK h0 (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getReceiveSlots _ _)

theorem sb_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : SBK h0 (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setExtraBadge _ _ _)

theorem sb_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      SBK h0 (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; sb_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => sb_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | sb_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_transferCapsLoop _ _ _ _ _ _)

theorem sb_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : SBK h0 (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_transferCaps _ _ _ _ _)

theorem sb_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SBK h0 (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_doNormalTransfer _ _ _ _ _ _ _)

theorem sb_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : SBK h0 (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_doIpcTransfer _ _ _ _ _)

theorem sb_doNbrecvFailedTransfer (thread : ObjRef) : SBK h0 (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_doNbrecvFailedTransfer _)

theorem sb_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : SBK h0 (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_domainScheduleConfigure _ _ _)

theorem sb_setNextInterrupt  : SBK h0 (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setNextInterrupt)

theorem sb_switchSchedContext  : SBK h0 (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_switchSchedContext)

theorem sb_scAndTimer  : SBK h0 (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_scAndTimer)

theorem sb_scheduleChooseNewThread  : SBK h0 (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_scheduleChooseNewThread)

theorem sb_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : SBK h0 (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_scheduleSwitchThreadFastfail _ _ _ _)

theorem sb_schedule  : SBK h0 (schedule (Z := Unit)) := by
  unfold schedule; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedule)

theorem sb_domainSetStart (index : Nat) : SBK h0 (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_domainSetStart _)

theorem sb_postCapDeletion (cap : Cap) : SBK h0 (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_postCapDeletion _)

theorem sb_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : SBK h0 (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_emptySlot _ _)

theorem sb_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SBKE h0 (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem sb_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SBKE h0 (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem sb_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : SBKE h0 (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sb_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : SBK h0 (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4ReplyFromKernelError _ _ _)

theorem sb_fl4SyscallFaultIP (thread : ObjRef) : SBK h0 (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_fl4SyscallFaultIP _)

theorem sb_getCapReg (reg : Register) : SBK h0 (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getCapReg _)

theorem sb_getIrqSlot (irq : Irq) : SBK h0 (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getIrqSlot _)

theorem sb_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SBK h0 (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_getMrs _ _ _)

theorem sb_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : SBK h0 (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleArchFaultReply _ _ _ _)

theorem sb_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : SBK h0 (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleFaultReply _ _ _ _)

theorem sb_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : SBK h0 (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleHypervisorFault _ _)

theorem sb_handleNoFault (tptr : ObjRef) : SBK h0 (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleNoFault _)

theorem sb_handleReservedIrq (_irq : Irq) : SBK h0 (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleReservedIrq _)

theorem sb_handleSpuriousIrq  : SBK h0 (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleSpuriousIrq)

theorem sb_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : SBKE h0 (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_handleVmFault _ _)

theorem sb_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : SBK h0 (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_initArchObjects _ _ _ _ _ _)

theorem sb_threadSetDomain (tptr : ObjRef) (domain : Domain) : SBK h0 (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_threadSetDomain _ _)

theorem sb_setDomain (tptr : ObjRef) (newDom : Domain) : SBK h0 (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setDomain _ _)

theorem sb_invokeSetDomain (thread : ObjRef) (domain : Domain) : SBK h0 (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invokeSetDomain _ _)

theorem sb_invokeDomain (domInv : DomainInvocation) : SBK h0 (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invokeDomain _)

theorem sb_invokeIrqControl (a0 : IrqControlInvocation) : SBKE h0 (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invokeIrqControl _)

theorem sb_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : SBKE h0 (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invokeFl4IrqControl _)

theorem sb_invokeFl4Tcb (a0 : Fl4TcbInvocation) : SBKE h0 (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_invokeFl4Tcb _)

theorem sb_isValidTimeoutHandler (tptr : ObjRef) : SBK h0 (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_isValidTimeoutHandler _)

theorem sb_lookupReply  : SBKE h0 (lookupReply (Z := Unit)) := by
  unfold lookupReply; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_lookupReply)

theorem sb_maybeAddEmptyTail (scPtr : ObjRef) : SBK h0 (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_maybeAddEmptyTail _)

theorem sb_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : SBKE h0 f) (h_g : SBKE h0 g) : SBKE h0 (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; sb_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_orChoiceE _ _ _ ?_ ?_)

theorem sb_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : SBK h0 (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_orderedInsert _ _ _ _)

theorem sb_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : SBK h0 (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_storeAsidPoolEntry _ _ _)

theorem sb_performAsidPoolInvocation (iv : AsidPoolInvocation) : SBK h0 (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performAsidPoolInvocation _)

theorem sb_performDeriveSubframe (iv : Fl4SubframeInvocation) : SBK h0 (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performDeriveSubframe _)

theorem sb_portIn (f : MachineMonad Data) : SBK h0 (portIn (Z := Unit) f) := by
  unfold portIn; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_portIn _)

theorem sb_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : SBK h0 (portOut (Z := Unit) f w) := by
  unfold portOut; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_portOut _ _)

theorem sb_performIoPortInvocation (i : IoPortInvocation) : SBK h0 (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performIoPortInvocation _)

theorem sb_performIoportControlInvocation (i : IoPortControlInvocation) : SBK h0 (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performIoportControlInvocation _)

theorem sb_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : SBK h0 (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPageDirectoryInvocation _)

theorem sb_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : SBK h0 (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPageInvocationUnmap _ _)

theorem sb_performPageInvocation (iv : PageInvocation) : SBK h0 (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPageInvocation _)

theorem sb_performPageTableInvocation (iv : PageTableInvocation) : SBK h0 (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPageTableInvocation _)

theorem sb_performPdptInvocation (iv : PdptInvocation) : SBK h0 (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPdptInvocation _)

theorem sb_performPml4Flush (a0 : Fl4Pml4Invocation) : SBK h0 (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performPml4Flush _)

theorem sb_performTestAndClearAccessed (_slot : ObjRef) : SBK h0 (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_performTestAndClearAccessed _)

theorem sb_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : SBK h0 (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_readyTimesAppend _ _)

theorem sb_tcbReleaseEnqueue (tcbPtr : ObjRef) : SBK h0 (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbReleaseEnqueue _)

theorem sb_postpone (scPtr : ObjRef) : SBK h0 (postpone (Z := Unit) scPtr) := by
  unfold postpone; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_postpone _)

theorem sb_updateTimeStamp  : SBK h0 (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateTimeStamp)

theorem sb_preemptionPoint  : SBKE h0 (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_preemptionPoint)

theorem sb_prepareThreadDelete (threadPtr : ObjRef) : SBK h0 (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_prepareThreadDelete _)

theorem sb_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : SBK h0 (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbAppend _ _)

theorem sb_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : SBK h0 (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbEpAppend _ _ _)

theorem sb_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : SBK h0 (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_receiveIpcBlocked _ _ _ _)

theorem sb_refillResetRr (cscPtr : ObjRef) : SBK h0 (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillResetRr _)

theorem sb_reorderEp (epPtr tptr : ObjRef) : SBK h0 (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_reorderEp _ _)

theorem sb_reorderNtfn (ntfnPtr tptr : ObjRef) : SBK h0 (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_reorderNtfn _ _)

theorem sb_replyUnlinkSc (scPtr replyPtr : ObjRef) : SBK h0 (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_replyUnlinkSc _ _)

theorem sb_schedContextResume (scPtr : ObjRef) : SBK h0 (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextResume _)

theorem sb_testPossibleSwitchTo (tcbPtr : ObjRef) : SBK h0 (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_testPossibleSwitchTo _)

theorem sb_restart (thread : ObjRef) : SBK h0 (restart (Z := Unit) thread) := by
  unfold restart; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_restart _)

theorem sb_returnConsumed (scPtr : ObjRef) : SBK h0 (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_returnConsumed _)

theorem sb_schedContextBindNtfn (sc ntfn : ObjRef) : SBK h0 (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextBindNtfn _ _)

theorem sb_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : SBK h0 (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextMaybeUnbindNtfn _)

theorem sb_schedContextUnbindNtfn (scPtr : ObjRef) : SBK h0 (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextUnbindNtfn _)

theorem sb_schedContextUnbindReply (scPtr : ObjRef) : SBK h0 (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextUnbindReply _)

theorem sb_schedContextUnbindYieldFrom (scPtr : ObjRef) : SBK h0 (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextUnbindYieldFrom _)

theorem sb_schedContextYieldTo (scPtr : ObjRef) : SBK h0 (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_schedContextYieldTo _)

theorem sb_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : SBK h0 (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_sendIpcBlocked _ _ _ _ _ _)

theorem sb_setFlags (ref : ObjRef) (flags : TcbFlags) : SBK h0 (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setFlags _ _)

theorem sb_setMcpriority (ref : ObjRef) (mcp : Priority) : SBK h0 (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setMcpriority _ _)

theorem sb_threadSetPriority (tptr : ObjRef) (prio : Priority) : SBK h0 (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_threadSetPriority _ _)

theorem sb_setPriority (tptr : ObjRef) (prio : Priority) : SBK h0 (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_setPriority _ _)

theorem sb_updateRestartPc (threadPtr : ObjRef) : SBK h0 (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_updateRestartPc _)

theorem sb_suspend (thread : ObjRef) : SBK h0 (suspend (Z := Unit) thread) := by
  unfold suspend; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_suspend _)

theorem sb_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : SBKE h0 mFault) (h_hFault : ∀ x0, SBK h0 (hFault x0)) (h_mError : ∀ x0, SBKE h0 (mError x0)) (h_hError : ∀ x0, SBK h0 (hError x0)) (h_mFinalise : ∀ x0, SBKE h0 (mFinalise x0)) : SBKE h0 (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; sb_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible refine sb_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem sb_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : SBK h0 (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_tcbNtfnAppend _ _)

theorem sb_testReschedule (fromTptr : ObjRef) : SBK h0 (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_testReschedule _)

theorem sb_unbindMaybeNotification (ntfnptr : ObjRef) : SBK h0 (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unbindMaybeNotification _)

theorem sb_unbindNotification (tcb : ObjRef) : SBK h0 (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; sb_auto
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_unbindNotification _)
