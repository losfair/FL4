/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, g1c): **OnlyIdle (l4v
`only_idle`): every TCB in `IdleThreadState` is the idle thread**, kept by every
spec step (spec side only; imports only Fl4Spec via SpecInvFaultTcbsT, outside
the JAtZ cone). g1b's handoff (KENTRY-PLAN g1b): the carried form of its [J]
premise `OnlyIdle`.

* `oiQ N p x := x.tcbState = .idleThreadState → p = N`, `OIS N := TP (oiQ N)`
  (SpecInvFaultTcbsT's pointer-dependent `TP`: the idle pointer `N` is exempt);
  `OnlyIdle σ ↔ OIS σ.idleThread σ` (SpecInvAllO, `onlyIdle_iff`).
* The spec writes `IdleThreadState` only in `initKheap` (grep Fl4Spec:
  Init.lean:97): every `setThreadState` has a literal state other than
  `IdleThreadState` (`oi_setThreadState`'s side condition `ts ≠ IdleThreadState`),
  every other TCB write keeps `tcbState`, and a new TCB is `defaultTcb`
  (Inactive). So every TCB writer is a `tp_*` leaf with a side condition closed
  by `oi_side`, as invA's NativeScope family (SpecInvNativeScopeF1).
* The rest: one lemma per spec function reachable from
  `fl4KernelEntrySyscall`, bottom-up (`oi_auto`), generated from the spec's
  call graph by invA's gen.py (scratch/g1c, untracked: `sh mkoi.sh`); the
  recursive ones by invA's manual.py texts. Parts 2-6: SpecInvAllO2..O6.
-/
import Fl4Proofs.P3.SpecInvFaultTcbsT
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A TCB in `IdleThreadState` sits at `N`. -/
def oiQ (N : ObjRef) (p : ObjRef) (x : Tcb) : Prop := x.tcbState = .idleThreadState → p = N

/-- Only the thread at `N` is in `IdleThreadState`. -/
abbrev OIS (N : ObjRef) (σ : State Unit) : Prop := TP (oiQ N) σ

variable {N : ObjRef}

abbrev OIK {α : Type} (N : ObjRef) (m : NonDet (State Unit) α) : Prop := IK (OIS N) m
abbrev OIKE {ε α : Type} (N : ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (OIS N) m

/-- The side conditions of the TCB-writer leaves. -/
macro "oi_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; simp [oiQ, defaultTcb]; done)
  | (left; decide)
  | (left; simp; done)
  | (left; split <;> simp <;> done)
  | (intro _ _ _; simp [oiQ]; done)
  | (intro _ hx; simpa [oiQ] using hx)
  | (intro _ _ hx; simpa [oiQ] using hx)
  | (simp; done)
  | (split <;> simp <;> done)
  | (simp [oiQ, defaultTcb]; done)
  | decide)

syntax "oi_leaf" : tactic
macro_rules | `(tactic| oi_leaf) => `(tactic| fail "no oi_leaf")

macro "oi_auto" : tactic => `(tactic| repeat' (first | oi_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); oi_side))
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- **`set_thread_state`** (hand lemma): any state but `IdleThreadState` (no spec
call site writes it: every site passes another literal), or the idle thread itself. -/
theorem oi_setThreadState (t : ObjRef) (ts : ThreadState) (h : ts ≠ .idleThreadState ∨ t = N) :
    OIK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun _ _ hs => h.resolve_left (not_not.2 hs)) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine oi_setThreadState _ _ ?_); oi_side))

theorem oi_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, oiQ N t x → oiQ N t (fn v x)) : OIK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| oi_leaf) => `(tactic| ((with_reducible refine oi_optionUpdateThread _ _ _ ?_); oi_side))

/-- **Retype** (hand lemma): a new TCB is `defaultTcb` (Inactive). -/
theorem oi_defaultTcb (p : ObjRef) (d : Domain) : oiQ N p (defaultTcb d) := by
  simp [oiQ, defaultTcb]

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
end

end Fl4Proofs.P3.SInvAll
