/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi1): **`VI N S b` kept by every
spec function that writes no idle-relevant field** (no thread state, no TCB/SC binding,
no yield-to / bound-notification / reply-stack write, no endpoint / notification queue,
no retype / detype). Generated: sg1's idle-pointer frames SpecInvSgI1..I6 (themselves ut7's
NK family) renamed `vi_` → `vi_`, the leaves replaced by SpecInvViA's (`vi_setObject` …
with their side conditions, `vi_side`), and every function reaching an idle-relevant
writer removed (those are SpecInvViH*). Parts 2-6: SpecInvViG2..G6.
-/
import Fl4Proofs.P3.SpecInvViA
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}


theorem vi_archActivateIdleThread (_t : ObjRef) : IK (VIT N S T b) (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archActivateIdleThread _)

theorem vi_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : IK (VIT N S T b) (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_threadGet _ _)

theorem vi_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : IK (VIT N S T b) (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getTcbObjRef _ _)

theorem vi_getCap (a0 : CslotPtr) : IK (VIT N S T b) (getCap (Z := Unit) a0) := by
  unfold getCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getCap _)

theorem vi_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : IK (VIT N S T b) (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupIpcBuffer _ _)

theorem vi_setMessageInfo (thread : ObjRef) (info : MessageInfo) : IK (VIT N S T b) (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setMessageInfo _ _)

theorem vi_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : IK (VIT N S T b) (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storeWordOffs _ _ _)

theorem vi_replyFromKernel (thread : ObjRef) (x : Data × List Data) : IK (VIT N S T b) (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_replyFromKernel _ _)

theorem vi_getSchedContext (ptr : ObjRef) : IK (VIT N S T b) (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getSchedContext _)

theorem vi_schedContextUpdateConsumed (scPtr : ObjRef) : IK (VIT N S T b) (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextUpdateConsumed _)

theorem vi_setConsumed (scPtr tcbPtr : ObjRef) : IK (VIT N S T b) (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setConsumed _ _)

theorem vi_getThreadState (ref : ObjRef) : IK (VIT N S T b) (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getThreadState _)

theorem vi_setSchedulerAction (action : SchedulerAction) : IK (VIT N S T b) (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setSchedulerAction _)

theorem vi_setThreadStateAct (tcbPtr : ObjRef) : IK (VIT N S T b) (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setThreadStateAct _)

theorem vi_archCheckIrq (_irq : Data) : IKE (VIT N S T b) (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archCheckIrq _)

theorem vi_ensureEmpty (slot : CslotPtr) : IKE (VIT N S T b) (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_ensureEmpty _)

theorem vi_isIoportRangeFree (f l : IoPort) : IK (VIT N S T b) (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isIoportRangeFree _ _)

theorem vi_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : IKE (VIT N S T b) m) : IKE (VIT N S T b) (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_lookupErrorOnFailure _ _ ?_)

theorem vi_resolveAddressBits' (p : Cap × CapRef) : IKE (VIT N S T b) (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by vi_auto)) fun nc => ?_
        split
        · exact vi_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_resolveAddressBits' _)

theorem vi_resolveAddressBits (a0 : Cap × CapRef) : IKE (VIT N S T b) (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_resolveAddressBits _)

theorem vi_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : IKE (VIT N S T b) (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupSlotForCnodeOp _ _ _ _)

theorem vi_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IKE (VIT N S T b) (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupTargetSlot _ _ _)

theorem vi_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : IKE (VIT N S T b) (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeIoportControlInvocation _ _ _ _ _)

theorem vi_getAsidPool (ptr : ObjRef) : IK (VIT N S T b) (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getAsidPool _)

theorem vi_findVspaceForAsid (asid : Asid) : IKE (VIT N S T b) (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_findVspaceForAsid _)

theorem vi_getPdpt (ptr : ObjRef) : IK (VIT N S T b) (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPdpt _)

theorem vi_getPdpte (ptr : ObjRef) : IK (VIT N S T b) (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPdpte _)

theorem vi_isFinalCap (cap : Cap) : IK (VIT N S T b) (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isFinalCap _)

theorem vi_getPml4 (ptr : ObjRef) : IK (VIT N S T b) (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPml4 _)

theorem vi_getPml4e (ptr : ObjRef) : IK (VIT N S T b) (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPml4e _)

theorem vi_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : IKE (VIT N S T b) (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupPdptSlot _ _)

theorem vi_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePageDirectoryInvocation _ _ _ _ _)

theorem vi_checkVpAlignment (sz : VMPageSize) (vptr : Word) : IKE (VIT N S T b) (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkVpAlignment _ _)

theorem vi_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : IKE (VIT N S T b) (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupPdSlot _ _)

theorem vi_getPd (ptr : ObjRef) : IK (VIT N S T b) (getPd (Z := Unit) ptr) := by
  unfold getPd; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPd _)

theorem vi_getPde (ptr : ObjRef) : IK (VIT N S T b) (getPde (Z := Unit) ptr) := by
  unfold getPde; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPde _)

theorem vi_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : IKE (VIT N S T b) (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupPtSlot _ _)

theorem vi_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : IKE (VIT N S T b) (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_createMappingEntries _ _ _ _ _ _)

theorem vi_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : IKE (VIT N S T b) (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_ensureSafeMapping _)

theorem vi_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePageInvocation _ _ _ _ _)

theorem vi_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePageTableInvocation _ _ _ _ _)

theorem vi_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePdptInvocation _ _ _ _ _)

theorem vi_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : IKE (VIT N S T b) (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_ensurePortOperationAllowed _ _ _)

theorem vi_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : IKE (VIT N S T b) (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePortInvocation _ _ _)

theorem vi_ensureNoChildren (cslotPtr : CslotPtr) : IKE (VIT N S T b) (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_ensureNoChildren _)

theorem vi_selectExt {D : Type} (a : State DetExt → D) (S' : Set D) : IK (VIT N S T b) (selectExt (Z := Unit) a S') := by
  unfold selectExt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_selectExt _ _)

theorem vi_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archDecodeInvocation _ _ _ _ _ _)

theorem vi_getIrqState (irq : Irq) : IK (VIT N S T b) (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getIrqState _)

theorem vi_isIrqActive (irq : Irq) : IK (VIT N S T b) (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isIrqActive _)

theorem vi_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IKE (VIT N S T b) (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archDecodeIrqControlInvocation _ _ _ _)

theorem vi_archDeriveCap (c : ArchCap) : IKE (VIT N S T b) (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archDeriveCap _)

theorem vi_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : IK (VIT N S T b) (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_hwAsidInvalidate _ _)

theorem vi_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : IK (VIT N S T b) (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setAsidPool _ _)

theorem vi_getCurrentCr3  : IK (VIT N S T b) (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getCurrentCr3)

theorem vi_setCurrentCr3 (c : Cr3) : IK (VIT N S T b) (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setCurrentCr3 _)

theorem vi_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : IK (VIT N S T b) (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setCurrentVspaceRoot _ _)

theorem vi_setVmRoot (tcb : ObjRef) : IK (VIT N S T b) (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setVmRoot _)

theorem vi_deleteAsid (asid : Asid) (pml4 : ObjRef) : IK (VIT N S T b) (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_deleteAsid _ _)

theorem vi_deleteAsidPool (base : Asid) (ptr : ObjRef) : IK (VIT N S T b) (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_deleteAsidPool _ _)

theorem vi_getPt (ptr : ObjRef) : IK (VIT N S T b) (getPt (Z := Unit) ptr) := by
  unfold getPt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPt _)

theorem vi_getPte (ptr : ObjRef) : IK (VIT N S T b) (getPte (Z := Unit) ptr) := by
  unfold getPte; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getPte _)

theorem vi_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : IK (VIT N S T b) (setPd (Z := Unit) ptr pd) := by
  unfold setPd; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setPd _ _)

theorem vi_storePde (p : ObjRef) (pde : PDE) : IK (VIT N S T b) (storePde (Z := Unit) p pde) := by
  unfold storePde; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storePde _ _)

theorem vi_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : IK (VIT N S T b) (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setPdpt _ _)

theorem vi_storePdpte (p : ObjRef) (pte : PDPTE) : IK (VIT N S T b) (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storePdpte _ _)
end

end Fl4Proofs.P3.SInvI
