/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §2/§4, invA): **NativeScope,
spec part: no thread is in `runningVM`**, kept by every spec step (spec side
only; imports only Fl4Spec via SpecInvNativeScopeT, outside the JAtZ cone).

* `NativeScopeS σ := TI nsQ σ` with `nsQ x := x.tcbState ≠ .runningVM`: the
  same statement as IpcLeaves' `NativeScope` (consumed at the top by
  `kernel_entryJ26P`'s `hNS` / `hNSR` [S], KENTRY-PLAN fin1); l4v has no
  counterpart (FL4's VT-x state, out of the native scope).
* The spec never writes `runningVM` (it only reads it, Fl4Spec/Ipc.lean:515):
  every `setThreadState` has a literal state other than `runningVM`, every
  other TCB write keeps `tcbState`, and a new TCB is `defaultTcb` (Inactive).
  So the writers are leaves with a side condition closed by `ns_side`:
  `setObject` / `setSimpleKo` / `threadSet` / `archThreadSet` / `asUser` /
  `setMrs` / `setCap` / `retypeRegion(With)` / `deleteObjects`
  (SpecInvNativeScopeT), `setThreadState` (`ts ≠ runningVM`),
  `optionUpdateThread`.
* The rest: one lemma per spec function reachable from
  `fl4KernelEntrySyscall`, bottom-up (`ns_auto`: the leaves, `ik_step0`,
  else unfold the head spec function). Generated from the spec's call graph
  (invA scratch gen.py, untracked); the recursive ones by hand.
* `kentry_nativeScope`: every outcome of the syscall entry from a
  `NativeScopeS` state is `NativeScopeS`; `kcall_nativeScope`: the same for
  `fl4CallKernel rep ev` for every event (interrupts, faults, timer);
  `boot_nativeScope`: the initial state `initASt`.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A TCB not in `runningVM`. -/
def nsQ (x : Tcb) : Prop := x.tcbState ≠ .runningVM

/-- No thread is in `runningVM` (IpcLeaves' `NativeScope`). -/
abbrev NativeScopeS (σ : State Unit) : Prop := TI nsQ σ

abbrev NSK {α : Type} (m : NonDet (State Unit) α) : Prop := IK NativeScopeS m
abbrev NSKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE NativeScopeS m

/-- The side conditions of the TCB-writer leaves. -/
macro "ns_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; simp [nsQ]; done)
  | (intro _ hx; simpa [nsQ] using hx)
  | (intro _ _ _; simp [nsQ]; done)
  | (intro _ _ hx; simpa [nsQ] using hx)
  | (simp; done)
  | (split <;> simp <;> done)
  | (simp [nsQ, defaultTcb]; done)
  | decide)

syntax "ns_leaf" : tactic
macro_rules | `(tactic| ns_leaf) => `(tactic| fail "no ns_leaf")

macro "ns_auto" : tactic => `(tactic| repeat' (first | ns_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setObject _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ti_setSimpleKo _ _ _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_threadSet _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_archThreadSet _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_asUser _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setMrs _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_setCap _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_retypeRegionWith _ _ _ _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ti_retypeRegion _ _ _ _ _ ?_); ns_side))
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ti_deleteObjects _ _)

theorem ns_setThreadState (t : ObjRef) (ts : ThreadState) (h : ts ≠ .runningVM) :
    NSK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (ti_threadSet _ _ fun _ _ => h) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ns_setThreadState _ _ ?_); ns_side))

theorem ns_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, nsQ x → nsQ (fn v x)) : NSK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ti_threadSet _ _ (h _)
macro_rules | `(tactic| ns_leaf) => `(tactic| ((with_reducible refine ns_optionUpdateThread _ _ _ ?_); ns_side))

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
end

end Fl4Proofs.P3.SInv
