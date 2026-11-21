/-
P3 (DESIGN.md §9), invariant line G1 (rd8n): **the lookups and the decode
keep the ready queues and the release queue** (spec side only, outside the
`JAtZ` cone).

`QVv σ := (readyQueues, releaseQueue)`; `QVK V m := IK (QVq V) m`. It carries
the queue part of `VB` (rd8n C, l4v `valid_blocked`) from the shell start to
the perform. The lemmas are epq1's SpecInvEqV (the `vz_` family over the
lookups and `fl4DecodeInvocation`, itself sg1's SpecInvSgI1..I6 restricted)
with the view swapped (proofs/scratch/rd8n/genq.py, untracked); leaves: every
heap / TCB / scheduler-action writer keeps the queues by `ik_modify`.
-/
import Fl4Proofs.P3.SpecInvEqB
open Classical

namespace Fl4Proofs.P3.SInvR.B8n
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

abbrev QVw := (Domain → Priority → List ObjRef) × List ObjRef

/-- The queue view. -/
def QVv (σ : State Unit) : QVw := (σ.readyQueues, σ.releaseQueue)

def QVq (V : QVw) (σ : State Unit) : Prop := QVv σ = V

abbrev QVK (V : QVw) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (QVq V) m
abbrev QVKE (V : QVw) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (QVq V) m

variable {V : QVw}

macro "qv_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

macro "qv0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); qv_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); qv_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem qv_setObject (p : ObjRef) (o : KernelObject) : QVK V (setObject (Z := Unit) p o) := by
  unfold setObject; qv0_auto

theorem qv_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    QVK V (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; qv0_auto

theorem qv_threadSet (f : Tcb → Tcb) (t : ObjRef) : QVK V (threadSet (Z := Unit) f t) := by
  unfold threadSet; qv0_auto

theorem qv_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : QVK V (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; qv0_auto

theorem qv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : QVK V (asUser (Z := Unit) t u) := by
  unfold asUser; qv0_auto

theorem qv_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : QVK V (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; qv0_auto

theorem qv_setThreadState (t : ObjRef) (ts : ThreadState) : QVK V (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (qv_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; qv0_auto

theorem qv_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    QVK V (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact qv_threadSet _ _

syntax "qv_leaf" : tactic
macro_rules | `(tactic| qv_leaf) => `(tactic| fail "no qv_leaf")

macro "qv_auto" : tactic => `(tactic| repeat' (first | qv_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| qv_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); qv_side))
macro_rules | `(tactic| qv_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); qv_side))
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setObject _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setSimpleKo _ _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_threadSet _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_archThreadSet _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_asUser _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setMrs _ _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setThreadState _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_optionUpdateThread _ _ _)


theorem qv_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : QVK V (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_threadGet _ _)

theorem qv_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : QVK V (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getTcbObjRef _ _)

theorem qv_getCap (a0 : CslotPtr) : QVK V (getCap (Z := Unit) a0) := by
  unfold getCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getCap _)

theorem qv_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : QVK V (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupIpcBuffer _ _)

theorem qv_setMessageInfo (thread : ObjRef) (info : MessageInfo) : QVK V (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setMessageInfo _ _)

theorem qv_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : QVK V (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storeWordOffs _ _ _)

theorem qv_replyFromKernel (thread : ObjRef) (x : Data × List Data) : QVK V (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_replyFromKernel _ _)

theorem qv_getSchedContext (ptr : ObjRef) : QVK V (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getSchedContext _)

theorem qv_getThreadState (ref : ObjRef) : QVK V (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getThreadState _)

theorem qv_ensureEmpty (slot : CslotPtr) : QVKE V (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_ensureEmpty _)

theorem qv_isIoportRangeFree (f l : IoPort) : QVK V (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_isIoportRangeFree _ _)

theorem qv_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : QVKE V m) : QVKE V (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; qv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_lookupErrorOnFailure _ _ ?_)

theorem qv_resolveAddressBits' (p : Cap × CapRef) : QVKE V (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by qv_auto)) fun nc => ?_
        split
        · exact qv_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_resolveAddressBits' _)

theorem qv_resolveAddressBits (a0 : Cap × CapRef) : QVKE V (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_resolveAddressBits _)

theorem qv_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : QVKE V (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupSlotForCnodeOp _ _ _ _)

theorem qv_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : QVKE V (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupTargetSlot _ _ _)

theorem qv_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : QVKE V (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeIoportControlInvocation _ _ _ _ _)

theorem qv_getAsidPool (ptr : ObjRef) : QVK V (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getAsidPool _)

theorem qv_findVspaceForAsid (asid : Asid) : QVKE V (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_findVspaceForAsid _)

theorem qv_getPdpt (ptr : ObjRef) : QVK V (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPdpt _)

theorem qv_getPdpte (ptr : ObjRef) : QVK V (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPdpte _)

theorem qv_isFinalCap (cap : Cap) : QVK V (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_isFinalCap _)

theorem qv_getPml4 (ptr : ObjRef) : QVK V (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPml4 _)

theorem qv_getPml4e (ptr : ObjRef) : QVK V (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPml4e _)

theorem qv_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : QVKE V (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPdptSlot _ _)

theorem qv_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePageDirectoryInvocation _ _ _ _ _)

theorem qv_checkVpAlignment (sz : VMPageSize) (vptr : Word) : QVKE V (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_checkVpAlignment _ _)

theorem qv_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : QVKE V (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPdSlot _ _)

theorem qv_getPd (ptr : ObjRef) : QVK V (getPd (Z := Unit) ptr) := by
  unfold getPd; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPd _)

theorem qv_getPde (ptr : ObjRef) : QVK V (getPde (Z := Unit) ptr) := by
  unfold getPde; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPde _)

theorem qv_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : QVKE V (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPtSlot _ _)

theorem qv_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : QVKE V (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_createMappingEntries _ _ _ _ _ _)

theorem qv_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : QVKE V (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_ensureSafeMapping _)

theorem qv_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePageInvocation _ _ _ _ _)

theorem qv_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePageTableInvocation _ _ _ _ _)

theorem qv_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePdptInvocation _ _ _ _ _)

theorem qv_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : QVKE V (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_ensurePortOperationAllowed _ _ _)

theorem qv_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : QVKE V (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePortInvocation _ _ _)

theorem qv_ensureNoChildren (cslotPtr : CslotPtr) : QVKE V (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_ensureNoChildren _)

theorem qv_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : QVK V (selectExt (Z := Unit) a S) := by
  unfold selectExt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_selectExt _ _)

theorem qv_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_archDecodeInvocation _ _ _ _ _ _)

theorem qv_getIrqState (irq : Irq) : QVK V (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getIrqState _)

theorem qv_isIrqActive (irq : Irq) : QVK V (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_isIrqActive _)

theorem qv_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : QVKE V (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_archDecodeIrqControlInvocation _ _ _ _)

theorem qv_archDeriveCap (c : ArchCap) : QVKE V (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_archDeriveCap _)

theorem qv_getPt (ptr : ObjRef) : QVK V (getPt (Z := Unit) ptr) := by
  unfold getPt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPt _)

theorem qv_getPte (ptr : ObjRef) : QVK V (getPte (Z := Unit) ptr) := by
  unfold getPte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPte _)

theorem qv_getTcbQueue (d : Domain) (prio : Priority) : QVK V (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getTcbQueue _ _)




theorem qv_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : QVK V (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getSimpleKo _ _)

theorem qv_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : QVK V (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getSkObjRef _ _ _)

theorem qv_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : QVK V (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getScObjRef _ _)

theorem qv_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : QVKE V m) : QVKE V (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; qv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_capFaultOnFailure _ _ _ ?_)

theorem qv_loadWordOffs (ptr : ObjRef) (offs : Nat) : QVK V (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_loadWordOffs _ _)

theorem qv_getMessageInfo (thread : ObjRef) : QVK V (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getMessageInfo _)
theorem qv_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : QVK V (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; qv_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getExtraCptrs _ _)

theorem qv_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : QVKE V (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupSlotForThread _ _)

theorem qv_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : QVKE V (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupCapAndSlot _ _)

theorem qv_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : QVKE V (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupExtraCaps _ _ _)

theorem qv_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : QVKE V m) : QVK V (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; qv_auto
  all_goals first | exact h_m
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_constOnFailure _ _ ?_)

theorem qv_deriveCap (slot : CslotPtr) (cap : Cap) : QVKE V (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_deriveCap _ _)

theorem qv_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : QVKE V (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_checkHandlerEp _ _)

theorem qv_checkPrio (newPrio : Data) (authTcb : ObjRef) : QVKE V (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_checkPrio _ _)

theorem qv_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : QVKE V (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_checkValidIpcBuffer _ _)

theorem qv_dataToObjType (type : Data) : QVKE V (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_dataToObjType _)

theorem qv_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeBindNotification _ _)

theorem qv_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : QVKE V (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPivotSlot _ _ _)

theorem qv_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : QVKE V (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupSourceSlot _ _ _)

theorem qv_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : QVKE V (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeCnodeInvocation _ _ _ _)

theorem qv_slotCapLongRunningDelete (slot : CslotPtr) : QVK V (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_slotCapLongRunningDelete _)

theorem qv_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : QVKE V (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeCvSpace _ _ _ _)
theorem qv_subframeNode (nodeCap : Cap) (index depth : Data) : QVKE V (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_subframeNode _ _ _)

theorem qv_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : QVKE V (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeDeriveSubframe _ _ _ _)

theorem qv_decodeDomainScheduleConfigure (args : List Data) : QVKE V (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeDomainScheduleConfigure _)

theorem qv_decodeDomainScheduleSetStart (args : List Data) : QVKE V (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeDomainScheduleSetStart _)

theorem qv_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : QVKE V (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeDomainSet _ _)

theorem qv_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : QVKE V (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeDomainInvocation _ _ _)

theorem qv_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : QVK V (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4GetMr _ _ _)

theorem qv_fl4Arg (buf : Option ObjRef) (i : Nat) : QVKE V (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4Arg _ _)

theorem qv_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : QVKE V (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4ConfigureSingleStepping _ _)

theorem qv_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : QVKE V (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4FpuTransfer _ _ _ _)

theorem qv_fl4CheckBpNum (bp : Data) : QVKE V (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4CheckBpNum _)

theorem qv_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : QVKE V (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4GetBreakpoint _ _)

theorem qv_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, QVKE V (check x0)) : QVKE V (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; qv_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem qv_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : QVKE V (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeIrqControlRemapped _ _ _)

theorem qv_fl4ArchCheckIrq (irq : Data) : QVKE V (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4ArchCheckIrq _)

theorem qv_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : QVKE V (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4IrqControl _ _ _ _ _)

theorem qv_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : QVKE V (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4SetBreakpoint _ _)

theorem qv_decodeFl4SetFlags (args : List Data) (t : ObjRef) : QVKE V (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4SetFlags _ _)

theorem qv_decodeFl4SetTimer (args : List Data) (t : ObjRef) : QVKE V (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4SetTimer _ _)

theorem qv_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : QVKE V (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4UnsetBreakpoint _ _)

theorem qv_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : QVKE V (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeFl4TcbExt _ _ _ _ _)

theorem qv_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : QVKE V (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeIrqHandlerInvocation _ _ _)

theorem qv_getScReleased (scPtr : ObjRef) : QVK V (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getScReleased _)

theorem qv_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : QVKE V (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSchedContextBind _ _)

theorem qv_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : QVKE V (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSchedContextUnbindObject _ _)

theorem qv_decodeSchedContextYieldTo (scPtr : ObjRef) : QVKE V (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSchedContextYieldTo _)

theorem qv_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : QVKE V (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSchedContextInvocation _ _ _)

theorem qv_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : QVKE V (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSchedControlInvocationFlags _ _ _)

theorem qv_rangeCheck (v minV maxV : Word) : QVKE V (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_rangeCheck _ _ _)

theorem qv_decodeSetFlags (args : List Data) (cap : Cap) : QVKE V (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetFlags _ _)

theorem qv_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : QVKE V (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetIpcBuffer _ _ _ _)

theorem qv_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetMcpriority _ _ _ _)

theorem qv_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetPriority _ _ _ _)

theorem qv_isBlocked (thread : ObjRef) : QVK V (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_isBlocked _)

theorem qv_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : QVKE V (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeUpdateSc _ _ _)

theorem qv_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetSchedParams _ _ _ _)

theorem qv_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : QVKE V (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetSpace _ _ _ _)

theorem qv_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetTimeoutEp _ _ _)

theorem qv_decodeSetTlsBase (args : List Data) (cap : Cap) : QVKE V (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeSetTlsBase _ _)

theorem qv_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : QVKE V (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeTcbConfigure _ _ _ _)

theorem qv_decodeUnbindNotification (cap : Cap) : QVKE V (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem qv_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : QVKE V (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeTcbInvocation _ _ _ _ _)

theorem qv_decodePml4Flush (cap : ArchCap) : QVKE V (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodePml4Flush _)

theorem qv_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : QVKE V (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_frameMappingSlot _ _ _ _)

theorem qv_decodeTestAndClearAccessed (cap : ArchCap) : QVKE V (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeTestAndClearAccessed _)

theorem qv_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : QVKE V (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem qv_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : QVK V (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getMrs _ _ _)

theorem qv_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : QVKE V (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem qv_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    QVKE V (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem qv_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : QVKE V (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem qv_getCapReg (reg : Register) : QVK V (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getCapReg _)

end

end Fl4Proofs.P3.SInvR.B8n
