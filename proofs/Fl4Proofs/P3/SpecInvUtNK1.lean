/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **no spec step writes
the IRQ node** (`NodeIs N σ := σ.interruptIrqNode = N`), part 1, spec side only.
The IRQ node map is set at boot and never written; `UtInv3` (ut6) reads it
outside the view `uV`, so the entry theorems need it constant. The family
`NK N m := IK (NodeIs N) m` is proved for every spec function reachable from
`fl4KernelEntrySyscall` by the same scripts as invA's NativeScope family
(SpecInvNativeScopeF1..F6, mechanically renamed `ns_` → `nk_`): every leaf is a
`get` / `modify` / `select` of other fields (`nk0_auto`). Parts 2-6:
SpecInvUtNK2..NK6.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The IRQ node map is `N`. -/
def NodeIs (N : Irq → ObjRef) (σ : State Unit) : Prop := σ.interruptIrqNode = N

abbrev NK (N : Irq → ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (NodeIs N) m
abbrev NKE (N : Irq → ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (NodeIs N) m

variable {N : Irq → ObjRef}

macro "nk_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "nk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); nk_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); nk_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem nk_setObject (p : ObjRef) (o : KernelObject) : NK N (setObject (Z := Unit) p o) := by
  unfold setObject; nk0_auto

theorem nk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    NK N (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_threadSet (f : Tcb → Tcb) (t : ObjRef) : NK N (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : NK N (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : NK N (asUser (Z := Unit) t u) := by
  unfold asUser; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : NK N (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_setCap (c : Cap) (sl : CslotPtr) : NK N (setCap (Z := Unit) c sl) := by
  unfold setCap; repeat' (first | exact nk_setObject _ _ | nk0_auto)

theorem nk_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType)
    (dev : Bool) : NK N (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith; nk0_auto

theorem nk_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    NK N (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  unfold retypeRegion; repeat' (first | exact nk_retypeRegionWith _ _ _ _ _ _ | nk0_auto)

theorem nk_deleteObjects (ptr : Word) (bits : Nat) : NK N (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; nk0_auto

theorem nk_setThreadState (t : ObjRef) (ts : ThreadState) : NK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (nk_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; nk0_auto

theorem nk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    NK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact nk_threadSet _ _

syntax "nk_leaf" : tactic
macro_rules | `(tactic| nk_leaf) => `(tactic| fail "no nk_leaf")

macro "nk_auto" : tactic => `(tactic| repeat' (first | nk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| nk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); nk_side))
macro_rules | `(tactic| nk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); nk_side))
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setObject _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setSimpleKo _ _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_threadSet _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archThreadSet _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_asUser _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setMrs _ _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setCap _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deleteObjects _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setThreadState _ _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_optionUpdateThread _ _ _)

theorem nk_archActivateIdleThread (_t : ObjRef) : NK N (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archActivateIdleThread _)

theorem nk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : NK N (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_threadGet _ _)

theorem nk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : NK N (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getTcbObjRef _ _)

theorem nk_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : NK N (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateSchedContext _ _)

theorem nk_schedContextCancelYieldTo (thread : ObjRef) : NK N (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextCancelYieldTo _)

theorem nk_getCap (a0 : CslotPtr) : NK N (getCap (Z := Unit) a0) := by
  unfold getCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getCap _)

theorem nk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : NK N (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupIpcBuffer _ _)

theorem nk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : NK N (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setMessageInfo _ _)

theorem nk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : NK N (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storeWordOffs _ _ _)

theorem nk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : NK N (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyFromKernel _ _)

theorem nk_getSchedContext (ptr : ObjRef) : NK N (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getSchedContext _)

theorem nk_schedContextUpdateConsumed (scPtr : ObjRef) : NK N (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUpdateConsumed _)

theorem nk_setConsumed (scPtr tcbPtr : ObjRef) : NK N (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setConsumed _ _)

theorem nk_completeYieldTo (tcbPtr : ObjRef) : NK N (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_completeYieldTo _)

theorem nk_getThreadState (ref : ObjRef) : NK N (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getThreadState _)

theorem nk_setSchedulerAction (action : SchedulerAction) : NK N (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setSchedulerAction _)

theorem nk_setThreadStateAct (tcbPtr : ObjRef) : NK N (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setThreadStateAct _)

theorem nk_activateThread  : NK N (activateThread (Z := Unit)) := by
  unfold activateThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_activateThread)

theorem nk_archCheckIrq (_irq : Data) : NKE N (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archCheckIrq _)

theorem nk_ensureEmpty (slot : CslotPtr) : NKE N (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_ensureEmpty _)

theorem nk_isIoportRangeFree (f l : IoPort) : NK N (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isIoportRangeFree _ _)

theorem nk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : NKE N m) : NKE N (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_lookupErrorOnFailure _ _ ?_)

theorem nk_resolveAddressBits' (p : Cap × CapRef) : NKE N (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by nk_auto)) fun nc => ?_
        split
        · exact nk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_resolveAddressBits' _)

theorem nk_resolveAddressBits (a0 : Cap × CapRef) : NKE N (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_resolveAddressBits _)

theorem nk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : NKE N (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupSlotForCnodeOp _ _ _ _)

theorem nk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NKE N (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupTargetSlot _ _ _)

theorem nk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : NKE N (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeIoportControlInvocation _ _ _ _ _)

theorem nk_getAsidPool (ptr : ObjRef) : NK N (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getAsidPool _)

theorem nk_findVspaceForAsid (asid : Asid) : NKE N (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_findVspaceForAsid _)

theorem nk_getPdpt (ptr : ObjRef) : NK N (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPdpt _)

theorem nk_getPdpte (ptr : ObjRef) : NK N (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPdpte _)

theorem nk_isFinalCap (cap : Cap) : NK N (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isFinalCap _)

theorem nk_getPml4 (ptr : ObjRef) : NK N (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPml4 _)

theorem nk_getPml4e (ptr : ObjRef) : NK N (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPml4e _)

theorem nk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : NKE N (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupPdptSlot _ _)

theorem nk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePageDirectoryInvocation _ _ _ _ _)

theorem nk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : NKE N (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkVpAlignment _ _)

theorem nk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : NKE N (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupPdSlot _ _)

theorem nk_getPd (ptr : ObjRef) : NK N (getPd (Z := Unit) ptr) := by
  unfold getPd; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPd _)

theorem nk_getPde (ptr : ObjRef) : NK N (getPde (Z := Unit) ptr) := by
  unfold getPde; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPde _)

theorem nk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : NKE N (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupPtSlot _ _)

theorem nk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : NKE N (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_createMappingEntries _ _ _ _ _ _)

theorem nk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : NKE N (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_ensureSafeMapping _)

theorem nk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePageInvocation _ _ _ _ _)

theorem nk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePageTableInvocation _ _ _ _ _)

theorem nk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePdptInvocation _ _ _ _ _)

theorem nk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : NKE N (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_ensurePortOperationAllowed _ _ _)

theorem nk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : NKE N (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePortInvocation _ _ _)

theorem nk_ensureNoChildren (cslotPtr : CslotPtr) : NKE N (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_ensureNoChildren _)

theorem nk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : NK N (selectExt (Z := Unit) a S) := by
  unfold selectExt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_selectExt _ _)

theorem nk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archDecodeInvocation _ _ _ _ _ _)

theorem nk_getIrqState (irq : Irq) : NK N (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getIrqState _)

theorem nk_isIrqActive (irq : Irq) : NK N (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isIrqActive _)

theorem nk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NKE N (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archDecodeIrqControlInvocation _ _ _ _)

theorem nk_archDeriveCap (c : ArchCap) : NKE N (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archDeriveCap _)

theorem nk_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : NK N (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_hwAsidInvalidate _ _)

theorem nk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : NK N (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setAsidPool _ _)

theorem nk_getCurrentCr3  : NK N (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getCurrentCr3)

theorem nk_setCurrentCr3 (c : Cr3) : NK N (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setCurrentCr3 _)

theorem nk_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : NK N (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setCurrentVspaceRoot _ _)

theorem nk_setVmRoot (tcb : ObjRef) : NK N (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setVmRoot _)

theorem nk_deleteAsid (asid : Asid) (pml4 : ObjRef) : NK N (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deleteAsid _ _)

theorem nk_deleteAsidPool (base : Asid) (ptr : ObjRef) : NK N (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deleteAsidPool _ _)

theorem nk_getPt (ptr : ObjRef) : NK N (getPt (Z := Unit) ptr) := by
  unfold getPt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPt _)

theorem nk_getPte (ptr : ObjRef) : NK N (getPte (Z := Unit) ptr) := by
  unfold getPte; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getPte _)

theorem nk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : NK N (setPd (Z := Unit) ptr pd) := by
  unfold setPd; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setPd _ _)

theorem nk_storePde (p : ObjRef) (pde : PDE) : NK N (storePde (Z := Unit) p pde) := by
  unfold storePde; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storePde _ _)

theorem nk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : NK N (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setPdpt _ _)

theorem nk_storePdpte (p : ObjRef) (pte : PDPTE) : NK N (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storePdpte _ _)
end

end Fl4Proofs.P3.SInvU
