/-
P3 (DESIGN.md §9), invariant line G1 (sl1): **no spec step writes the idle SC
pointer** (`IdleScIs t σ := σ.idleSc = t`), part 1, spec side only. ScLive names
the state's idle SC (`IrqOutV (fun _ => σ.idleSc)`), so the entry theorems need it
constant. The family `IsK t m := IK (IdleScIs t) m` is sg1's idle-thread family
(SpecInvSgI1..I6) mechanically renamed (`IdleIs` → `IdleScIs`, `idleThread` →
`idleSc`, `idk_` → `isk_`): every leaf is a `get` / `modify` / `select` of other
fields (no spec function writes `idleSc`). Parts 2-6: SpecInvSlI2..I6.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The idle thread pointer is `N`. -/
def IdleScIs (N : ObjRef) (σ : State Unit) : Prop := σ.idleSc = N

abbrev IsK (N : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (IdleScIs N) m
abbrev IsKE (N : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (IdleScIs N) m

variable {N : ObjRef}

macro "isk_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "isk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); isk_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); isk_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem isk_setObject (p : ObjRef) (o : KernelObject) : IsK N (setObject (Z := Unit) p o) := by
  unfold setObject; isk0_auto

theorem isk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IsK N (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_threadSet (f : Tcb → Tcb) (t : ObjRef) : IsK N (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IsK N (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IsK N (asUser (Z := Unit) t u) := by
  unfold asUser; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IsK N (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_setCap (c : Cap) (sl : CslotPtr) : IsK N (setCap (Z := Unit) c sl) := by
  unfold setCap; repeat' (first | exact isk_setObject _ _ | isk0_auto)

theorem isk_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType)
    (dev : Bool) : IsK N (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith; isk0_auto

theorem isk_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    IsK N (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  unfold retypeRegion; repeat' (first | exact isk_retypeRegionWith _ _ _ _ _ _ | isk0_auto)

theorem isk_deleteObjects (ptr : Word) (bits : Nat) : IsK N (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; isk0_auto

theorem isk_setThreadState (t : ObjRef) (ts : ThreadState) : IsK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (isk_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; isk0_auto

theorem isk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    IsK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact isk_threadSet _ _

syntax "isk_leaf" : tactic
macro_rules | `(tactic| isk_leaf) => `(tactic| fail "no isk_leaf")

macro "isk_auto" : tactic => `(tactic| repeat' (first | isk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| isk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); isk_side))
macro_rules | `(tactic| isk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); isk_side))
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setObject _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setSimpleKo _ _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_threadSet _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archThreadSet _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_asUser _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setMrs _ _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setCap _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deleteObjects _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setThreadState _ _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_optionUpdateThread _ _ _)

theorem isk_archActivateIdleThread (_t : ObjRef) : IsK N (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archActivateIdleThread _)

theorem isk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : IsK N (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_threadGet _ _)

theorem isk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : IsK N (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getTcbObjRef _ _)

theorem isk_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : IsK N (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateSchedContext _ _)

theorem isk_schedContextCancelYieldTo (thread : ObjRef) : IsK N (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextCancelYieldTo _)

theorem isk_getCap (a0 : CslotPtr) : IsK N (getCap (Z := Unit) a0) := by
  unfold getCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getCap _)

theorem isk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : IsK N (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupIpcBuffer _ _)

theorem isk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : IsK N (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setMessageInfo _ _)

theorem isk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : IsK N (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storeWordOffs _ _ _)

theorem isk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : IsK N (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyFromKernel _ _)

theorem isk_getSchedContext (ptr : ObjRef) : IsK N (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getSchedContext _)

theorem isk_schedContextUpdateConsumed (scPtr : ObjRef) : IsK N (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUpdateConsumed _)

theorem isk_setConsumed (scPtr tcbPtr : ObjRef) : IsK N (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setConsumed _ _)

theorem isk_completeYieldTo (tcbPtr : ObjRef) : IsK N (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_completeYieldTo _)

theorem isk_getThreadState (ref : ObjRef) : IsK N (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getThreadState _)

theorem isk_setSchedulerAction (action : SchedulerAction) : IsK N (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setSchedulerAction _)

theorem isk_setThreadStateAct (tcbPtr : ObjRef) : IsK N (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setThreadStateAct _)

theorem isk_activateThread  : IsK N (activateThread (Z := Unit)) := by
  unfold activateThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_activateThread)

theorem isk_archCheckIrq (_irq : Data) : IsKE N (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archCheckIrq _)

theorem isk_ensureEmpty (slot : CslotPtr) : IsKE N (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_ensureEmpty _)

theorem isk_isIoportRangeFree (f l : IoPort) : IsK N (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isIoportRangeFree _ _)

theorem isk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : IsKE N m) : IsKE N (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_lookupErrorOnFailure _ _ ?_)

theorem isk_resolveAddressBits' (p : Cap × CapRef) : IsKE N (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by isk_auto)) fun nc => ?_
        split
        · exact isk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_resolveAddressBits' _)

theorem isk_resolveAddressBits (a0 : Cap × CapRef) : IsKE N (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_resolveAddressBits _)

theorem isk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : IsKE N (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupSlotForCnodeOp _ _ _ _)

theorem isk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IsKE N (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupTargetSlot _ _ _)

theorem isk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : IsKE N (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeIoportControlInvocation _ _ _ _ _)

theorem isk_getAsidPool (ptr : ObjRef) : IsK N (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getAsidPool _)

theorem isk_findVspaceForAsid (asid : Asid) : IsKE N (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_findVspaceForAsid _)

theorem isk_getPdpt (ptr : ObjRef) : IsK N (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPdpt _)

theorem isk_getPdpte (ptr : ObjRef) : IsK N (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPdpte _)

theorem isk_isFinalCap (cap : Cap) : IsK N (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isFinalCap _)

theorem isk_getPml4 (ptr : ObjRef) : IsK N (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPml4 _)

theorem isk_getPml4e (ptr : ObjRef) : IsK N (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPml4e _)

theorem isk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : IsKE N (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupPdptSlot _ _)

theorem isk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePageDirectoryInvocation _ _ _ _ _)

theorem isk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : IsKE N (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkVpAlignment _ _)

theorem isk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : IsKE N (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupPdSlot _ _)

theorem isk_getPd (ptr : ObjRef) : IsK N (getPd (Z := Unit) ptr) := by
  unfold getPd; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPd _)

theorem isk_getPde (ptr : ObjRef) : IsK N (getPde (Z := Unit) ptr) := by
  unfold getPde; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPde _)

theorem isk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : IsKE N (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupPtSlot _ _)

theorem isk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : IsKE N (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_createMappingEntries _ _ _ _ _ _)

theorem isk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : IsKE N (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_ensureSafeMapping _)

theorem isk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePageInvocation _ _ _ _ _)

theorem isk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePageTableInvocation _ _ _ _ _)

theorem isk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePdptInvocation _ _ _ _ _)

theorem isk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : IsKE N (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_ensurePortOperationAllowed _ _ _)

theorem isk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : IsKE N (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePortInvocation _ _ _)

theorem isk_ensureNoChildren (cslotPtr : CslotPtr) : IsKE N (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_ensureNoChildren _)

theorem isk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : IsK N (selectExt (Z := Unit) a S) := by
  unfold selectExt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_selectExt _ _)

theorem isk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archDecodeInvocation _ _ _ _ _ _)

theorem isk_getIrqState (irq : Irq) : IsK N (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getIrqState _)

theorem isk_isIrqActive (irq : Irq) : IsK N (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isIrqActive _)

theorem isk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IsKE N (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archDecodeIrqControlInvocation _ _ _ _)

theorem isk_archDeriveCap (c : ArchCap) : IsKE N (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archDeriveCap _)

theorem isk_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : IsK N (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_hwAsidInvalidate _ _)

theorem isk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : IsK N (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setAsidPool _ _)

theorem isk_getCurrentCr3  : IsK N (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getCurrentCr3)

theorem isk_setCurrentCr3 (c : Cr3) : IsK N (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setCurrentCr3 _)

theorem isk_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : IsK N (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setCurrentVspaceRoot _ _)

theorem isk_setVmRoot (tcb : ObjRef) : IsK N (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setVmRoot _)

theorem isk_deleteAsid (asid : Asid) (pml4 : ObjRef) : IsK N (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deleteAsid _ _)

theorem isk_deleteAsidPool (base : Asid) (ptr : ObjRef) : IsK N (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deleteAsidPool _ _)

theorem isk_getPt (ptr : ObjRef) : IsK N (getPt (Z := Unit) ptr) := by
  unfold getPt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPt _)

theorem isk_getPte (ptr : ObjRef) : IsK N (getPte (Z := Unit) ptr) := by
  unfold getPte; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getPte _)

theorem isk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : IsK N (setPd (Z := Unit) ptr pd) := by
  unfold setPd; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setPd _ _)

theorem isk_storePde (p : ObjRef) (pde : PDE) : IsK N (storePde (Z := Unit) p pde) := by
  unfold storePde; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storePde _ _)

theorem isk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : IsK N (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setPdpt _ _)

theorem isk_storePdpte (p : ObjRef) (pte : PDPTE) : IsK N (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storePdpte _ _)
end

end Fl4Proofs.P3.SInvL
