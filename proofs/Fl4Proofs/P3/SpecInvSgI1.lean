/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **no spec step writes
the idle thread pointer** (`IdleIs t σ := σ.idleThread = t`), part 1, spec side
only. SpecGlob (`valid_global_refs`) names the state's idle thread, so the entry
theorems need it constant. The family `IdK t m := IK (IdleIs t) m` is ut7's
IRQ-node family (SpecInvUtNK1..NK6) mechanically renamed (`NodeIs` → `IdleIs`,
`interruptIrqNode` → `idleThread`, `nk_` → `idk_`): every leaf is a `get` /
`modify` / `select` of other fields (`idk0_auto`). Parts 2-6: SpecInvSgI2..I6.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The idle thread pointer is `N`. -/
def IdleIs (N : ObjRef) (σ : State Unit) : Prop := σ.idleThread = N

abbrev IdK (N : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (IdleIs N) m
abbrev IdKE (N : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (IdleIs N) m

variable {N : ObjRef}

macro "idk_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "idk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); idk_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); idk_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem idk_setObject (p : ObjRef) (o : KernelObject) : IdK N (setObject (Z := Unit) p o) := by
  unfold setObject; idk0_auto

theorem idk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IdK N (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_threadSet (f : Tcb → Tcb) (t : ObjRef) : IdK N (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IdK N (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IdK N (asUser (Z := Unit) t u) := by
  unfold asUser; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IdK N (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_setCap (c : Cap) (sl : CslotPtr) : IdK N (setCap (Z := Unit) c sl) := by
  unfold setCap; repeat' (first | exact idk_setObject _ _ | idk0_auto)

theorem idk_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType)
    (dev : Bool) : IdK N (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith; idk0_auto

theorem idk_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    IdK N (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  unfold retypeRegion; repeat' (first | exact idk_retypeRegionWith _ _ _ _ _ _ | idk0_auto)

theorem idk_deleteObjects (ptr : Word) (bits : Nat) : IdK N (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; idk0_auto

theorem idk_setThreadState (t : ObjRef) (ts : ThreadState) : IdK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (idk_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; idk0_auto

theorem idk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    IdK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact idk_threadSet _ _

syntax "idk_leaf" : tactic
macro_rules | `(tactic| idk_leaf) => `(tactic| fail "no idk_leaf")

macro "idk_auto" : tactic => `(tactic| repeat' (first | idk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| idk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); idk_side))
macro_rules | `(tactic| idk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); idk_side))
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setObject _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setSimpleKo _ _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_threadSet _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archThreadSet _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_asUser _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setMrs _ _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setCap _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deleteObjects _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setThreadState _ _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_optionUpdateThread _ _ _)

theorem idk_archActivateIdleThread (_t : ObjRef) : IdK N (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archActivateIdleThread _)

theorem idk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : IdK N (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_threadGet _ _)

theorem idk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : IdK N (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getTcbObjRef _ _)

theorem idk_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : IdK N (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateSchedContext _ _)

theorem idk_schedContextCancelYieldTo (thread : ObjRef) : IdK N (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextCancelYieldTo _)

theorem idk_getCap (a0 : CslotPtr) : IdK N (getCap (Z := Unit) a0) := by
  unfold getCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getCap _)

theorem idk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : IdK N (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupIpcBuffer _ _)

theorem idk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : IdK N (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setMessageInfo _ _)

theorem idk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : IdK N (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storeWordOffs _ _ _)

theorem idk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : IdK N (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyFromKernel _ _)

theorem idk_getSchedContext (ptr : ObjRef) : IdK N (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getSchedContext _)

theorem idk_schedContextUpdateConsumed (scPtr : ObjRef) : IdK N (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUpdateConsumed _)

theorem idk_setConsumed (scPtr tcbPtr : ObjRef) : IdK N (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setConsumed _ _)

theorem idk_completeYieldTo (tcbPtr : ObjRef) : IdK N (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_completeYieldTo _)

theorem idk_getThreadState (ref : ObjRef) : IdK N (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getThreadState _)

theorem idk_setSchedulerAction (action : SchedulerAction) : IdK N (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setSchedulerAction _)

theorem idk_setThreadStateAct (tcbPtr : ObjRef) : IdK N (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setThreadStateAct _)

theorem idk_activateThread  : IdK N (activateThread (Z := Unit)) := by
  unfold activateThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_activateThread)

theorem idk_archCheckIrq (_irq : Data) : IdKE N (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archCheckIrq _)

theorem idk_ensureEmpty (slot : CslotPtr) : IdKE N (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_ensureEmpty _)

theorem idk_isIoportRangeFree (f l : IoPort) : IdK N (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isIoportRangeFree _ _)

theorem idk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : IdKE N m) : IdKE N (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_lookupErrorOnFailure _ _ ?_)

theorem idk_resolveAddressBits' (p : Cap × CapRef) : IdKE N (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by idk_auto)) fun nc => ?_
        split
        · exact idk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_resolveAddressBits' _)

theorem idk_resolveAddressBits (a0 : Cap × CapRef) : IdKE N (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_resolveAddressBits _)

theorem idk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : IdKE N (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupSlotForCnodeOp _ _ _ _)

theorem idk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IdKE N (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupTargetSlot _ _ _)

theorem idk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : IdKE N (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeIoportControlInvocation _ _ _ _ _)

theorem idk_getAsidPool (ptr : ObjRef) : IdK N (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getAsidPool _)

theorem idk_findVspaceForAsid (asid : Asid) : IdKE N (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_findVspaceForAsid _)

theorem idk_getPdpt (ptr : ObjRef) : IdK N (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPdpt _)

theorem idk_getPdpte (ptr : ObjRef) : IdK N (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPdpte _)

theorem idk_isFinalCap (cap : Cap) : IdK N (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isFinalCap _)

theorem idk_getPml4 (ptr : ObjRef) : IdK N (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPml4 _)

theorem idk_getPml4e (ptr : ObjRef) : IdK N (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPml4e _)

theorem idk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : IdKE N (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupPdptSlot _ _)

theorem idk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePageDirectoryInvocation _ _ _ _ _)

theorem idk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : IdKE N (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkVpAlignment _ _)

theorem idk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : IdKE N (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupPdSlot _ _)

theorem idk_getPd (ptr : ObjRef) : IdK N (getPd (Z := Unit) ptr) := by
  unfold getPd; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPd _)

theorem idk_getPde (ptr : ObjRef) : IdK N (getPde (Z := Unit) ptr) := by
  unfold getPde; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPde _)

theorem idk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : IdKE N (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupPtSlot _ _)

theorem idk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : IdKE N (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_createMappingEntries _ _ _ _ _ _)

theorem idk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : IdKE N (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_ensureSafeMapping _)

theorem idk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePageInvocation _ _ _ _ _)

theorem idk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePageTableInvocation _ _ _ _ _)

theorem idk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePdptInvocation _ _ _ _ _)

theorem idk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : IdKE N (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_ensurePortOperationAllowed _ _ _)

theorem idk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : IdKE N (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePortInvocation _ _ _)

theorem idk_ensureNoChildren (cslotPtr : CslotPtr) : IdKE N (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_ensureNoChildren _)

theorem idk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : IdK N (selectExt (Z := Unit) a S) := by
  unfold selectExt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_selectExt _ _)

theorem idk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archDecodeInvocation _ _ _ _ _ _)

theorem idk_getIrqState (irq : Irq) : IdK N (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getIrqState _)

theorem idk_isIrqActive (irq : Irq) : IdK N (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isIrqActive _)

theorem idk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IdKE N (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archDecodeIrqControlInvocation _ _ _ _)

theorem idk_archDeriveCap (c : ArchCap) : IdKE N (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archDeriveCap _)

theorem idk_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : IdK N (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_hwAsidInvalidate _ _)

theorem idk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : IdK N (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setAsidPool _ _)

theorem idk_getCurrentCr3  : IdK N (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getCurrentCr3)

theorem idk_setCurrentCr3 (c : Cr3) : IdK N (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setCurrentCr3 _)

theorem idk_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : IdK N (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setCurrentVspaceRoot _ _)

theorem idk_setVmRoot (tcb : ObjRef) : IdK N (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setVmRoot _)

theorem idk_deleteAsid (asid : Asid) (pml4 : ObjRef) : IdK N (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deleteAsid _ _)

theorem idk_deleteAsidPool (base : Asid) (ptr : ObjRef) : IdK N (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deleteAsidPool _ _)

theorem idk_getPt (ptr : ObjRef) : IdK N (getPt (Z := Unit) ptr) := by
  unfold getPt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPt _)

theorem idk_getPte (ptr : ObjRef) : IdK N (getPte (Z := Unit) ptr) := by
  unfold getPte; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getPte _)

theorem idk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : IdK N (setPd (Z := Unit) ptr pd) := by
  unfold setPd; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setPd _ _)

theorem idk_storePde (p : ObjRef) (pde : PDE) : IdK N (storePde (Z := Unit) p pde) := by
  unfold storePde; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storePde _ _)

theorem idk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : IdK N (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setPdpt _ _)

theorem idk_storePdpte (p : ObjRef) (pte : PDPTE) : IdK N (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storePdpte _ _)
end

end Fl4Proofs.P3.SInvG
