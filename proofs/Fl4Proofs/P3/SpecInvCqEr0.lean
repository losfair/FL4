/-
P3 (DESIGN.md §9), invariant line G1 (ctq18): **the invocation front keeps
`Simple`** (no switch pending; spec side only, outside the JAtZ cone).

`SMK m := IK Simple m`. The lemmas are epq1's `VZ` family (SpecInvEqV, the
functions below the lookups and `fl4DecodeInvocation`) with the view replaced
(sed of SpecInvEqV, proofs/scratch/er/mksm.sh, untracked, as rd8c's
SpecInvRd8cV); hand leaves: every object / TCB / register write keeps the
scheduler action, and `set_thread_state`'s action write sets
`choose_new_thread` (`sm_setCn`).
-/
import Fl4Proofs.P3.SpecInvEqV
import Fl4Proofs.P3.SpecInvCqX
open Classical

namespace Fl4Proofs.P3.SInvQ.R18
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The family -/

abbrev SMK {α : Type} (m : NonDet (State Unit) α) : Prop := IK Simple m
abbrev SMKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE Simple m

theorem sm_setCn : SMK (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ _ _ e => by cases e

macro "sm_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

macro "sm0_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact sm_setCn
  | ((with_reducible refine ik_doMachineOp ?_ _); sm_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); sm_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem sm_setObject (p : ObjRef) (o : KernelObject) : SMK (setObject (Z := Unit) p o) := by
  unfold setObject; sm0_auto

theorem sm_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    SMK (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  refine ik_bind (ik_getObject _) fun _ => ?_
  sm0_auto
  all_goals exact sm_setObject _ _

theorem sm_threadSet (f : Tcb → Tcb) (t : ObjRef) : SMK (threadSet (Z := Unit) f t) := by
  unfold threadSet; sm0_auto

theorem sm_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : SMK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; sm0_auto

theorem sm_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : SMK (asUser (Z := Unit) t u) := by
  unfold asUser; sm0_auto

theorem sm_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : SMK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; sm0_auto

theorem sm_setThreadState (t : ObjRef) (ts : ThreadState) : SMK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (sm_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct; sm0_auto

theorem sm_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    SMK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact sm_threadSet _ _

syntax "sm_leaf" : tactic
macro_rules | `(tactic| sm_leaf) => `(tactic| fail "no sm_leaf")

macro "sm_auto" : tactic => `(tactic| repeat' (first | sm_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| sm_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); sm_side))
macro_rules | `(tactic| sm_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); sm_side))
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setObject _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setSimpleKo _ _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_threadSet _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_archThreadSet _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_asUser _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setMrs _ _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setThreadState _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_optionUpdateThread _ _ _)
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setCn)

/-! ## Generated (epq1's VZ family, view replaced) -/

theorem sm_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : SMK (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_threadGet _ _)

theorem sm_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : SMK (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getTcbObjRef _ _)

theorem sm_getCap (a0 : CslotPtr) : SMK (getCap (Z := Unit) a0) := by
  unfold getCap; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getCap _)

theorem sm_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : SMK (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupIpcBuffer _ _)

theorem sm_setMessageInfo (thread : ObjRef) (info : MessageInfo) : SMK (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setMessageInfo _ _)

theorem sm_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : SMK (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_storeWordOffs _ _ _)

theorem sm_replyFromKernel (thread : ObjRef) (x : Data × List Data) : SMK (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_replyFromKernel _ _)

theorem sm_getSchedContext (ptr : ObjRef) : SMK (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getSchedContext _)

theorem sm_getThreadState (ref : ObjRef) : SMK (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getThreadState _)

theorem sm_ensureEmpty (slot : CslotPtr) : SMKE (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_ensureEmpty _)

theorem sm_isIoportRangeFree (f l : IoPort) : SMK (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_isIoportRangeFree _ _)

theorem sm_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : SMKE m) : SMKE (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; sm_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible refine sm_lookupErrorOnFailure _ _ ?_)

theorem sm_resolveAddressBits' (p : Cap × CapRef) : SMKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by sm_auto)) fun nc => ?_
        split
        · exact sm_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_resolveAddressBits' _)

theorem sm_resolveAddressBits (a0 : Cap × CapRef) : SMKE (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_resolveAddressBits _)

theorem sm_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : SMKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupSlotForCnodeOp _ _ _ _)

theorem sm_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SMKE (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupTargetSlot _ _ _)

theorem sm_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : SMKE (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeIoportControlInvocation _ _ _ _ _)

theorem sm_getAsidPool (ptr : ObjRef) : SMK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getAsidPool _)

theorem sm_findVspaceForAsid (asid : Asid) : SMKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_findVspaceForAsid _)

theorem sm_getPdpt (ptr : ObjRef) : SMK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPdpt _)

theorem sm_getPdpte (ptr : ObjRef) : SMK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPdpte _)

theorem sm_isFinalCap (cap : Cap) : SMK (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_isFinalCap _)

theorem sm_getPml4 (ptr : ObjRef) : SMK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPml4 _)

theorem sm_getPml4e (ptr : ObjRef) : SMK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPml4e _)

theorem sm_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : SMKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupPdptSlot _ _)

theorem sm_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePageDirectoryInvocation _ _ _ _ _)

theorem sm_checkVpAlignment (sz : VMPageSize) (vptr : Word) : SMKE (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_checkVpAlignment _ _)

theorem sm_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : SMKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupPdSlot _ _)

theorem sm_getPd (ptr : ObjRef) : SMK (getPd (Z := Unit) ptr) := by
  unfold getPd; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPd _)

theorem sm_getPde (ptr : ObjRef) : SMK (getPde (Z := Unit) ptr) := by
  unfold getPde; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPde _)

theorem sm_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : SMKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupPtSlot _ _)

theorem sm_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : SMKE (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_createMappingEntries _ _ _ _ _ _)

theorem sm_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : SMKE (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_ensureSafeMapping _)

theorem sm_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePageInvocation _ _ _ _ _)

theorem sm_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePageTableInvocation _ _ _ _ _)

theorem sm_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePdptInvocation _ _ _ _ _)

theorem sm_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : SMKE (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_ensurePortOperationAllowed _ _ _)

theorem sm_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : SMKE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePortInvocation _ _ _)

theorem sm_ensureNoChildren (cslotPtr : CslotPtr) : SMKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_ensureNoChildren _)

theorem sm_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : SMK (selectExt (Z := Unit) a S) := by
  unfold selectExt; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_selectExt _ _)

theorem sm_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_archDecodeInvocation _ _ _ _ _ _)

theorem sm_getIrqState (irq : Irq) : SMK (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getIrqState _)

theorem sm_isIrqActive (irq : Irq) : SMK (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_isIrqActive _)

theorem sm_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SMKE (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_archDecodeIrqControlInvocation _ _ _ _)

theorem sm_archDeriveCap (c : ArchCap) : SMKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_archDeriveCap _)

theorem sm_getPt (ptr : ObjRef) : SMK (getPt (Z := Unit) ptr) := by
  unfold getPt; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPt _)

theorem sm_getPte (ptr : ObjRef) : SMK (getPte (Z := Unit) ptr) := by
  unfold getPte; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getPte _)

theorem sm_getTcbQueue (d : Domain) (prio : Priority) : SMK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getTcbQueue _ _)

theorem sm_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : SMK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_setTcbQueue _ _ _)

theorem sm_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : SMK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_tcbSchedAction _ _)

theorem sm_tcbReleaseRemove (tcbPtr : ObjRef) : SMK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_tcbReleaseRemove _)

theorem sm_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : SMK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getSimpleKo _ _)

theorem sm_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : SMK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getSkObjRef _ _ _)

theorem sm_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : SMK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getScObjRef _ _)

theorem sm_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : SMKE m) : SMKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; sm_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible refine sm_capFaultOnFailure _ _ _ ?_)

theorem sm_loadWordOffs (ptr : ObjRef) (offs : Nat) : SMK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_loadWordOffs _ _)

theorem sm_getMessageInfo (thread : ObjRef) : SMK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getMessageInfo _)
theorem sm_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : SMK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; sm_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getExtraCptrs _ _)

theorem sm_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : SMKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupSlotForThread _ _)

theorem sm_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : SMKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupCapAndSlot _ _)

theorem sm_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SMKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupExtraCaps _ _ _)

theorem sm_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : SMKE m) : SMK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; sm_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible refine sm_constOnFailure _ _ ?_)

theorem sm_deriveCap (slot : CslotPtr) (cap : Cap) : SMKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_deriveCap _ _)

theorem sm_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : SMKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_checkHandlerEp _ _)

theorem sm_checkPrio (newPrio : Data) (authTcb : ObjRef) : SMKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_checkPrio _ _)

theorem sm_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : SMKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_checkValidIpcBuffer _ _)

theorem sm_dataToObjType (type : Data) : SMKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_dataToObjType _)

theorem sm_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeBindNotification _ _)

theorem sm_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SMKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupPivotSlot _ _ _)

theorem sm_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SMKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_lookupSourceSlot _ _ _)

theorem sm_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : SMKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeCnodeInvocation _ _ _ _)

theorem sm_slotCapLongRunningDelete (slot : CslotPtr) : SMK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_slotCapLongRunningDelete _)

theorem sm_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SMKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeCvSpace _ _ _ _)
theorem sm_subframeNode (nodeCap : Cap) (index depth : Data) : SMKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_subframeNode _ _ _)

theorem sm_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : SMKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeDeriveSubframe _ _ _ _)

theorem sm_decodeDomainScheduleConfigure (args : List Data) : SMKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeDomainScheduleConfigure _)

theorem sm_decodeDomainScheduleSetStart (args : List Data) : SMKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeDomainScheduleSetStart _)

theorem sm_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : SMKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeDomainSet _ _)

theorem sm_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : SMKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeDomainInvocation _ _ _)

theorem sm_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : SMK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4GetMr _ _ _)

theorem sm_fl4Arg (buf : Option ObjRef) (i : Nat) : SMKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4Arg _ _)

theorem sm_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : SMKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4ConfigureSingleStepping _ _)

theorem sm_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : SMKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4FpuTransfer _ _ _ _)

theorem sm_fl4CheckBpNum (bp : Data) : SMKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4CheckBpNum _)

theorem sm_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SMKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4GetBreakpoint _ _)

theorem sm_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, SMKE (check x0)) : SMKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; sm_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible refine sm_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem sm_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SMKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeIrqControlRemapped _ _ _)

theorem sm_fl4ArchCheckIrq (irq : Data) : SMKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4ArchCheckIrq _)

theorem sm_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SMKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4IrqControl _ _ _ _ _)

theorem sm_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SMKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4SetBreakpoint _ _)

theorem sm_decodeFl4SetFlags (args : List Data) (t : ObjRef) : SMKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4SetFlags _ _)

theorem sm_decodeFl4SetTimer (args : List Data) (t : ObjRef) : SMKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4SetTimer _ _)

theorem sm_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SMKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4UnsetBreakpoint _ _)

theorem sm_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : SMKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeFl4TcbExt _ _ _ _ _)

theorem sm_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : SMKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeIrqHandlerInvocation _ _ _)

theorem sm_getScReleased (scPtr : ObjRef) : SMK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getScReleased _)

theorem sm_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : SMKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSchedContextBind _ _)

theorem sm_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : SMKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSchedContextUnbindObject _ _)

theorem sm_decodeSchedContextYieldTo (scPtr : ObjRef) : SMKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSchedContextYieldTo _)

theorem sm_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : SMKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSchedContextInvocation _ _ _)

theorem sm_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : SMKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSchedControlInvocationFlags _ _ _)

theorem sm_rangeCheck (v minV maxV : Word) : SMKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_rangeCheck _ _ _)

theorem sm_decodeSetFlags (args : List Data) (cap : Cap) : SMKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetFlags _ _)

theorem sm_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : SMKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetIpcBuffer _ _ _ _)

theorem sm_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetMcpriority _ _ _ _)

theorem sm_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetPriority _ _ _ _)

theorem sm_isBlocked (thread : ObjRef) : SMK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_isBlocked _)

theorem sm_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : SMKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeUpdateSc _ _ _)

theorem sm_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetSchedParams _ _ _ _)

theorem sm_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SMKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetSpace _ _ _ _)

theorem sm_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetTimeoutEp _ _ _)

theorem sm_decodeSetTlsBase (args : List Data) (cap : Cap) : SMKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeSetTlsBase _ _)

theorem sm_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SMKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeTcbConfigure _ _ _ _)

theorem sm_decodeUnbindNotification (cap : Cap) : SMKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem sm_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SMKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeTcbInvocation _ _ _ _ _)

theorem sm_decodePml4Flush (cap : ArchCap) : SMKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodePml4Flush _)

theorem sm_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : SMKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_frameMappingSlot _ _ _ _)

theorem sm_decodeTestAndClearAccessed (cap : ArchCap) : SMKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeTestAndClearAccessed _)

theorem sm_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SMKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem sm_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SMK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getMrs _ _ _)

theorem sm_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SMKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem sm_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SMKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem sm_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : SMKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sm_getCapReg (reg : Register) : SMK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; sm_auto
macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_getCapReg _)

end

end Fl4Proofs.P3.SInvQ.R18
