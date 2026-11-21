/- nq1: the current-thread frame `CTK c` (the current thread stays `c`) for every spec function reachable from the syscall entry except the scheduler, part 1 (generated: proofs/scratch/nq1/mkck.sh). -/
import Fl4Proofs.P3.SpecInvNtfnQC
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {cq : ObjRef}

theorem ct_archActivateIdleThread (_t : ObjRef) : CTK cq (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archActivateIdleThread _)

theorem ct_getObject (ptr : ObjRef) : CTK cq (getObject (Z := Unit) ptr) := by
  unfold getObject; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getObject _)

theorem ct_setObject (ptr : ObjRef) (obj : KernelObject) : CTK cq (setObject (Z := Unit) ptr obj) := by
  unfold setObject; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setObject _ _)

theorem ct_asUser {α : Type} (tptr : ObjRef) (f : UserMonad α) : CTK cq (asUser (Z := Unit) tptr f) := by
  unfold asUser; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_asUser _ _)

theorem ct_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : CTK cq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_threadGet _ _)

theorem ct_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : CTK cq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getTcbObjRef _ _)

theorem ct_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : CTK cq (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateSchedContext _ _)

theorem ct_threadSet (f : Tcb → Tcb) (tptr : ObjRef) : CTK cq (threadSet (Z := Unit) f tptr) := by
  unfold threadSet; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_threadSet _ _)

theorem ct_schedContextCancelYieldTo (thread : ObjRef) : CTK cq (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextCancelYieldTo _)

theorem ct_getCap (a0 : CslotPtr) : CTK cq (getCap (Z := Unit) a0) := by
  unfold getCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getCap _)

theorem ct_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : CTK cq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupIpcBuffer _ _)

theorem ct_setMessageInfo (thread : ObjRef) (info : MessageInfo) : CTK cq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setMessageInfo _ _)

theorem ct_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : CTK cq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storeWordOffs _ _ _)

theorem ct_setMrs (thread : ObjRef) (buf : Option ObjRef) (msgs : List Message) : CTK cq (setMrs (Z := Unit) thread buf msgs) := by
  unfold setMrs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setMrs _ _ _)

theorem ct_replyFromKernel (thread : ObjRef) (x : Data × List Data) : CTK cq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyFromKernel _ _)

theorem ct_getSchedContext (ptr : ObjRef) : CTK cq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getSchedContext _)

theorem ct_schedContextUpdateConsumed (scPtr : ObjRef) : CTK cq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUpdateConsumed _)

theorem ct_setConsumed (scPtr tcbPtr : ObjRef) : CTK cq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setConsumed _ _)

theorem ct_completeYieldTo (tcbPtr : ObjRef) : CTK cq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_completeYieldTo _)

theorem ct_getThreadState (ref : ObjRef) : CTK cq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getThreadState _)

theorem ct_setSchedulerAction (action : SchedulerAction) : CTK cq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setSchedulerAction _)

theorem ct_setThreadStateAct (tcbPtr : ObjRef) : CTK cq (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setThreadStateAct _)

theorem ct_setThreadState (ref : ObjRef) (ts : ThreadState) : CTK cq (setThreadState (Z := Unit) ref ts) := by
  unfold setThreadState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setThreadState _ _)

theorem ct_activateThread  : CTK cq (activateThread (Z := Unit)) := by
  unfold activateThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_activateThread)

theorem ct_archCheckIrq (_irq : Data) : CTKE cq (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archCheckIrq _)

theorem ct_ensureEmpty (slot : CslotPtr) : CTKE cq (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_ensureEmpty _)

theorem ct_isIoportRangeFree (f l : IoPort) : CTK cq (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isIoportRangeFree _ _)

theorem ct_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : CTKE cq m) : CTKE cq (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_lookupErrorOnFailure _ _ ?_)

theorem ct_resolveAddressBits' (p : Cap × CapRef) : CTKE cq (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ct_auto)) fun nc => ?_
        split
        · exact ct_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_resolveAddressBits' _)

theorem ct_resolveAddressBits (a0 : Cap × CapRef) : CTKE cq (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_resolveAddressBits _)

theorem ct_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : CTKE cq (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupSlotForCnodeOp _ _ _ _)

theorem ct_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : CTKE cq (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupTargetSlot _ _ _)

theorem ct_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : CTKE cq (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeIoportControlInvocation _ _ _ _ _)

theorem ct_getAsidPool (ptr : ObjRef) : CTK cq (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getAsidPool _)

theorem ct_findVspaceForAsid (asid : Asid) : CTKE cq (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_findVspaceForAsid _)

theorem ct_getPdpt (ptr : ObjRef) : CTK cq (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPdpt _)

theorem ct_getPdpte (ptr : ObjRef) : CTK cq (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPdpte _)

theorem ct_isFinalCap (cap : Cap) : CTK cq (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isFinalCap _)

theorem ct_getPml4 (ptr : ObjRef) : CTK cq (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPml4 _)

theorem ct_getPml4e (ptr : ObjRef) : CTK cq (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPml4e _)

theorem ct_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : CTKE cq (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupPdptSlot _ _)

theorem ct_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePageDirectoryInvocation _ _ _ _ _)

theorem ct_checkVpAlignment (sz : VMPageSize) (vptr : Word) : CTKE cq (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkVpAlignment _ _)

theorem ct_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : CTKE cq (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupPdSlot _ _)

theorem ct_getPd (ptr : ObjRef) : CTK cq (getPd (Z := Unit) ptr) := by
  unfold getPd; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPd _)

theorem ct_getPde (ptr : ObjRef) : CTK cq (getPde (Z := Unit) ptr) := by
  unfold getPde; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPde _)

theorem ct_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : CTKE cq (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupPtSlot _ _)

theorem ct_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : CTKE cq (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_createMappingEntries _ _ _ _ _ _)

theorem ct_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : CTKE cq (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_ensureSafeMapping _)

theorem ct_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePageInvocation _ _ _ _ _)

theorem ct_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePageTableInvocation _ _ _ _ _)

theorem ct_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePdptInvocation _ _ _ _ _)

theorem ct_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : CTKE cq (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_ensurePortOperationAllowed _ _ _)

theorem ct_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : CTKE cq (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePortInvocation _ _ _)

theorem ct_ensureNoChildren (cslotPtr : CslotPtr) : CTKE cq (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_ensureNoChildren _)

theorem ct_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : CTK cq (selectExt (Z := Unit) a S) := by
  unfold selectExt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_selectExt _ _)

theorem ct_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archDecodeInvocation _ _ _ _ _ _)

theorem ct_getIrqState (irq : Irq) : CTK cq (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getIrqState _)

theorem ct_isIrqActive (irq : Irq) : CTK cq (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isIrqActive _)

theorem ct_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : CTKE cq (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archDecodeIrqControlInvocation _ _ _ _)

theorem ct_archDeriveCap (c : ArchCap) : CTKE cq (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archDeriveCap _)

theorem ct_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : CTK cq (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_hwAsidInvalidate _ _)

theorem ct_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : CTK cq (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setAsidPool _ _)

theorem ct_getCurrentCr3  : CTK cq (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getCurrentCr3)

theorem ct_setCurrentCr3 (c : Cr3) : CTK cq (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setCurrentCr3 _)

theorem ct_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : CTK cq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setCurrentVspaceRoot _ _)

theorem ct_setVmRoot (tcb : ObjRef) : CTK cq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setVmRoot _)

theorem ct_deleteAsid (asid : Asid) (pml4 : ObjRef) : CTK cq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deleteAsid _ _)

theorem ct_deleteAsidPool (base : Asid) (ptr : ObjRef) : CTK cq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deleteAsidPool _ _)

theorem ct_getPt (ptr : ObjRef) : CTK cq (getPt (Z := Unit) ptr) := by
  unfold getPt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPt _)

theorem ct_getPte (ptr : ObjRef) : CTK cq (getPte (Z := Unit) ptr) := by
  unfold getPte; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getPte _)

theorem ct_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : CTK cq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setPd _ _)

theorem ct_storePde (p : ObjRef) (pde : PDE) : CTK cq (storePde (Z := Unit) p pde) := by
  unfold storePde; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storePde _ _)

theorem ct_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : CTK cq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setPdpt _ _)

theorem ct_storePdpte (p : ObjRef) (pte : PDPTE) : CTK cq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storePdpte _ _)

theorem ct_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : CTK cq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setPt _ _)

theorem ct_storePte (p : ObjRef) (pte : PTE) : CTK cq (storePte (Z := Unit) p pte) := by
  unfold storePte; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storePte _ _)

theorem ct_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : CTK cq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unmapPage _ _ _ _)

theorem ct_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : CTK cq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_flushTable _ _ _ _)

theorem ct_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : CTK cq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invalidatePageStructureCacheAsid _ _)

theorem ct_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : CTK cq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unmapPageTable _ _ _)

theorem ct_flushAll (vspace : ObjRef) (asid : Asid) : CTK cq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_flushAll _ _)

theorem ct_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : CTK cq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unmapPd _ _ _)

theorem ct_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : CTK cq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setPml4 _ _)

theorem ct_storePml4e (p : ObjRef) (pte : PML4E) : CTK cq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storePml4e _ _)

theorem ct_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : CTK cq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unmapPdpt _ _ _)

theorem ct_archFinaliseCap (c : ArchCap) (x : Bool) : CTK cq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archFinaliseCap _ _)

theorem ct_archGetSanitiseRegisterInfo (_t : ObjRef) : CTK cq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archGetSanitiseRegisterInfo _)

theorem ct_setCap (cap : Cap) (a0 : CslotPtr) : CTK cq (setCap (Z := Unit) cap a0) := by
  unfold setCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setCap _ _)

theorem ct_setOriginal (slot : CslotPtr) (v : Bool) : CTK cq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setOriginal _ _)

theorem ct_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : CTK cq (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setUntypedCapAsFull _ _ _)

theorem ct_setCdt (t : Cdt) : CTK cq (setCdt (Z := Unit) t) := by
  unfold setCdt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setCdt _)

theorem ct_updateCdt (f : Cdt → Cdt) : CTK cq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateCdt _)

theorem ct_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : CTK cq (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capInsert _ _ _)

theorem ct_setIrqState (state : IrqState) (irq : Irq) : CTK cq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setIrqState _ _)

theorem ct_updateIrqState (irq : Irq) (irqState : X64IRQState) : CTK cq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateIrqState _ _)

theorem ct_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : CTK cq m) : CTKE cq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_withoutPreemption _ ?_)

theorem ct_archInvokeIrqControl (aic : ArchIrqControlInvocation) : CTKE cq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archInvokeIrqControl _)

theorem ct_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : CTK cq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archInvokeIrqHandler _)

theorem ct_archMaskIrqSignal (irq : Irq) : CTK cq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archMaskIrqSignal _)

theorem ct_deleteObjects (ptr : Word) (bits : Nat) : CTK cq (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deleteObjects _ _)

theorem ct_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : CTK cq (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_retypeRegion _ _ _ _ _)

theorem ct_performAsidControlInvocation (iv : AsidControlInvocation) : CTK cq (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performAsidControlInvocation _)

theorem ct_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : CTK cq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_storeAsidPoolEntry _ _ _)

theorem ct_performAsidPoolInvocation (iv : AsidPoolInvocation) : CTK cq (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performAsidPoolInvocation _)
end

end Fl4Proofs.P3.SInv
