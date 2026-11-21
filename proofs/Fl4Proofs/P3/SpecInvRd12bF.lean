/-
P3 (DESIGN.md §9), invariant line G1 (rd12b, KENTRY-PLAN rd11a goal 2): **the
invocation front keeps the scheduler view, `cfS` and the scheduler action**
(spec side only, outside the JAtZ cone), so it keeps rd11a's pinned body frame
`KP` (SpecInvRd12bA's `kp_of_kz`).

`KZ V σ`: σ has V's rd8c view `BKv` (every TCB's state / fault / SC, every SC
object, the time), V's `cfS` (consumed time, cur_sc, ct, idle thread / SC, the
time) and V's scheduler action. `KZK V m := IK (KZ V) m`. The lemmas are rd8c's
BK family (SpecInvRd8cV, the functions below the lookups and
`fl4DecodeInvocation`, from `bk_threadGet`) with the view replaced (sed,
proofs/scratch/rd12b/mkkz.sh + head.lean, untracked); hand leaves: each BK
leaf (`setObject` of a non-TCB / non-SC / non-CNode, the TCB writers keeping
state / fault / SC, `set_simple_ko`) with its `CA` half (`cfS` and the action:
these writers touch only the heap).
-/
import Fl4Proofs.P3.SpecInvRd8cV
import Fl4Proofs.P3.SpecInvRdP
open Classical

namespace Fl4Proofs.P3.SInvR.A12b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvE Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The view -/

/-- `cfS` and the scheduler action. -/
def CAv (σ : State Unit) := (cfS σ, σ.schedulerAction)

def CA (V σ : State Unit) : Prop := CAv σ = CAv V

/-- The view: rd8c's `BKv`, `cfS`, the action. -/
def KZv (σ : State Unit) := (B8c.BKv σ, CAv σ)

/-- σ has V's view. -/
def KZ (V σ : State Unit) : Prop := KZv σ = KZv V

abbrev KZK (V : State Unit) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (KZ V) m
abbrev KZKE (V : State Unit) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (KZ V) m

variable {V : State Unit}

theorem kz_of {α : Type} {m : NonDet (State Unit) α} (h1 : ∀ W, B8c.BKK W m) (h2 : ∀ W, IK (CA W) m) :
    KZK V m := by
  intro σ hσ y hy
  have a := h1 (B8c.BKv σ) σ rfl y hy
  have b := h2 σ σ rfl y hy
  unfold B8c.BK at a
  unfold CA at b
  unfold KZ KZv at hσ ⊢
  rw [a, b]; exact hσ

macro "ca_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

theorem ca_setObject (W : State Unit) (p : ObjRef) (o : KernelObject) : IK (CA W) (setObject (Z := Unit) p o) := by
  unfold setObject; repeat' (first | ik_step0 | ik_unfold)

macro "ca0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); ca_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); ca_side)
  | with_reducible exact ik_getObject _
  | with_reducible exact ca_setObject _ _ _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem ca_threadSet (W : State Unit) (f : Tcb → Tcb) (t : ObjRef) : IK (CA W) (threadSet (Z := Unit) f t) := by
  unfold threadSet; ca0_auto

theorem ca_archThreadSet (W : State Unit) (f : ArchTcb → ArchTcb) (t : ObjRef) :
    IK (CA W) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ca0_auto

theorem ca_asUser (W : State Unit) {α : Type} (t : ObjRef) (u : UserMonad α) : IK (CA W) (asUser (Z := Unit) t u) := by
  unfold asUser; ca0_auto

theorem ca_setMrs (W : State Unit) (t : ObjRef) (b : Option ObjRef) (ms : List Message) :
    IK (CA W) (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; ca0_auto

theorem ca_setSimpleKo (W : State Unit) {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK (CA W) (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; ca0_auto

/-! ## The leaves -/

theorem kz_setObject (p : ObjRef) (o : KernelObject) (ho : NSC o) (hot : ∀ x, o ≠ .tcb x) :
    KZK V (setObject (Z := Unit) p o) :=
  kz_of (fun _ => B8c.bk_setObject p o ho hot) (fun W => ca_setObject W p o)

theorem kz_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault ∧ (f x).tcbSchedContext = x.tcbSchedContext) :
    KZK V (threadSet (Z := Unit) f t) :=
  kz_of (fun _ => B8c.bk_threadSet f t hf) (fun W => ca_threadSet W f t)

theorem kz_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : KZK V (archThreadSet (Z := Unit) f t) :=
  kz_of (fun _ => B8c.bk_archThreadSet f t) (fun W => ca_archThreadSet W f t)

theorem kz_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : KZK V (asUser (Z := Unit) t u) :=
  kz_of (fun _ => B8c.bk_asUser t u) (fun W => ca_asUser W t u)

theorem kz_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : KZK V (setMrs (Z := Unit) t b ms) :=
  kz_of (fun _ => B8c.bk_setMrs t b ms) (fun W => ca_setMrs W t b ms)

theorem kz_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    KZK V (setSimpleKo (Z := Unit) f p e) :=
  kz_of (fun _ => B8c.bk_setSimpleKo f p e) (fun W => ca_setSimpleKo W f p e)

macro "kz_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

syntax "kz_leaf" : tactic
macro_rules | `(tactic| kz_leaf) => `(tactic| fail "no kz_leaf")

macro "kz_auto" : tactic => `(tactic| repeat' (first | kz_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| kz_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); kz_side))
macro_rules | `(tactic| kz_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); kz_side))
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| kz_leaf) => `(tactic| ((with_reducible refine kz_setObject _ _ ?_ ?_); first | trivial | (intro _ h; cases h)))
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_setSimpleKo _ _ _)
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_archThreadSet _ _)
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_asUser _ _)
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_setMrs _ _ _)

theorem kz_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : KZK V (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_threadGet _ _)

theorem kz_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : KZK V (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getTcbObjRef _ _)

theorem kz_getCap (a0 : CslotPtr) : KZK V (getCap (Z := Unit) a0) := by
  unfold getCap; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getCap _)

theorem kz_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : KZK V (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupIpcBuffer _ _)

theorem kz_setMessageInfo (thread : ObjRef) (info : MessageInfo) : KZK V (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_setMessageInfo _ _)

theorem kz_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : KZK V (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_storeWordOffs _ _ _)

theorem kz_replyFromKernel (thread : ObjRef) (x : Data × List Data) : KZK V (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_replyFromKernel _ _)

theorem kz_getSchedContext (ptr : ObjRef) : KZK V (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getSchedContext _)

theorem kz_getThreadState (ref : ObjRef) : KZK V (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getThreadState _)

theorem kz_ensureEmpty (slot : CslotPtr) : KZKE V (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_ensureEmpty _)

theorem kz_isIoportRangeFree (f l : IoPort) : KZK V (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_isIoportRangeFree _ _)

theorem kz_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : KZKE V m) : KZKE V (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; kz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible refine kz_lookupErrorOnFailure _ _ ?_)

theorem kz_resolveAddressBits' (p : Cap × CapRef) : KZKE V (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by kz_auto)) fun nc => ?_
        split
        · exact kz_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_resolveAddressBits' _)

theorem kz_resolveAddressBits (a0 : Cap × CapRef) : KZKE V (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_resolveAddressBits _)

theorem kz_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : KZKE V (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupSlotForCnodeOp _ _ _ _)

theorem kz_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : KZKE V (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupTargetSlot _ _ _)

theorem kz_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : KZKE V (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeIoportControlInvocation _ _ _ _ _)

theorem kz_getAsidPool (ptr : ObjRef) : KZK V (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getAsidPool _)

theorem kz_findVspaceForAsid (asid : Asid) : KZKE V (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_findVspaceForAsid _)

theorem kz_getPdpt (ptr : ObjRef) : KZK V (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPdpt _)

theorem kz_getPdpte (ptr : ObjRef) : KZK V (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPdpte _)

theorem kz_isFinalCap (cap : Cap) : KZK V (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_isFinalCap _)

theorem kz_getPml4 (ptr : ObjRef) : KZK V (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPml4 _)

theorem kz_getPml4e (ptr : ObjRef) : KZK V (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPml4e _)

theorem kz_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : KZKE V (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupPdptSlot _ _)

theorem kz_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePageDirectoryInvocation _ _ _ _ _)

theorem kz_checkVpAlignment (sz : VMPageSize) (vptr : Word) : KZKE V (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_checkVpAlignment _ _)

theorem kz_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : KZKE V (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupPdSlot _ _)

theorem kz_getPd (ptr : ObjRef) : KZK V (getPd (Z := Unit) ptr) := by
  unfold getPd; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPd _)

theorem kz_getPde (ptr : ObjRef) : KZK V (getPde (Z := Unit) ptr) := by
  unfold getPde; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPde _)

theorem kz_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : KZKE V (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupPtSlot _ _)

theorem kz_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : KZKE V (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_createMappingEntries _ _ _ _ _ _)

theorem kz_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : KZKE V (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_ensureSafeMapping _)

theorem kz_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePageInvocation _ _ _ _ _)

theorem kz_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePageTableInvocation _ _ _ _ _)

theorem kz_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePdptInvocation _ _ _ _ _)

theorem kz_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : KZKE V (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_ensurePortOperationAllowed _ _ _)

theorem kz_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : KZKE V (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePortInvocation _ _ _)

theorem kz_ensureNoChildren (cslotPtr : CslotPtr) : KZKE V (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_ensureNoChildren _)

theorem kz_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : KZK V (selectExt (Z := Unit) a S) := by
  unfold selectExt; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_selectExt _ _)

theorem kz_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_archDecodeInvocation _ _ _ _ _ _)

theorem kz_getIrqState (irq : Irq) : KZK V (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getIrqState _)

theorem kz_isIrqActive (irq : Irq) : KZK V (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_isIrqActive _)

theorem kz_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : KZKE V (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_archDecodeIrqControlInvocation _ _ _ _)

theorem kz_archDeriveCap (c : ArchCap) : KZKE V (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_archDeriveCap _)

theorem kz_getPt (ptr : ObjRef) : KZK V (getPt (Z := Unit) ptr) := by
  unfold getPt; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPt _)

theorem kz_getPte (ptr : ObjRef) : KZK V (getPte (Z := Unit) ptr) := by
  unfold getPte; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getPte _)

theorem kz_getTcbQueue (d : Domain) (prio : Priority) : KZK V (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getTcbQueue _ _)

theorem kz_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : KZK V (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_setTcbQueue _ _ _)

theorem kz_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : KZK V (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_tcbSchedAction _ _)

theorem kz_tcbReleaseRemove (tcbPtr : ObjRef) : KZK V (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_tcbReleaseRemove _)

theorem kz_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : KZK V (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getSimpleKo _ _)

theorem kz_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : KZK V (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getSkObjRef _ _ _)

theorem kz_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : KZK V (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getScObjRef _ _)

theorem kz_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : KZKE V m) : KZKE V (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; kz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible refine kz_capFaultOnFailure _ _ _ ?_)

theorem kz_loadWordOffs (ptr : ObjRef) (offs : Nat) : KZK V (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_loadWordOffs _ _)

theorem kz_getMessageInfo (thread : ObjRef) : KZK V (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getMessageInfo _)
theorem kz_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : KZK V (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; kz_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getExtraCptrs _ _)

theorem kz_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : KZKE V (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupSlotForThread _ _)

theorem kz_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : KZKE V (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupCapAndSlot _ _)

theorem kz_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : KZKE V (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupExtraCaps _ _ _)

theorem kz_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : KZKE V m) : KZK V (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; kz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible refine kz_constOnFailure _ _ ?_)

theorem kz_deriveCap (slot : CslotPtr) (cap : Cap) : KZKE V (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_deriveCap _ _)

theorem kz_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : KZKE V (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_checkHandlerEp _ _)

theorem kz_checkPrio (newPrio : Data) (authTcb : ObjRef) : KZKE V (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_checkPrio _ _)

theorem kz_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : KZKE V (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_checkValidIpcBuffer _ _)

theorem kz_dataToObjType (type : Data) : KZKE V (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_dataToObjType _)

theorem kz_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeBindNotification _ _)

theorem kz_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : KZKE V (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupPivotSlot _ _ _)

theorem kz_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : KZKE V (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_lookupSourceSlot _ _ _)

theorem kz_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : KZKE V (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeCnodeInvocation _ _ _ _)

theorem kz_slotCapLongRunningDelete (slot : CslotPtr) : KZK V (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_slotCapLongRunningDelete _)

theorem kz_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : KZKE V (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeCvSpace _ _ _ _)
theorem kz_subframeNode (nodeCap : Cap) (index depth : Data) : KZKE V (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_subframeNode _ _ _)

theorem kz_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : KZKE V (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeDeriveSubframe _ _ _ _)

theorem kz_decodeDomainScheduleConfigure (args : List Data) : KZKE V (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeDomainScheduleConfigure _)

theorem kz_decodeDomainScheduleSetStart (args : List Data) : KZKE V (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeDomainScheduleSetStart _)

theorem kz_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : KZKE V (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeDomainSet _ _)

theorem kz_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : KZKE V (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeDomainInvocation _ _ _)

theorem kz_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : KZK V (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4GetMr _ _ _)

theorem kz_fl4Arg (buf : Option ObjRef) (i : Nat) : KZKE V (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4Arg _ _)

theorem kz_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : KZKE V (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4ConfigureSingleStepping _ _)

theorem kz_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : KZKE V (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4FpuTransfer _ _ _ _)

theorem kz_fl4CheckBpNum (bp : Data) : KZKE V (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4CheckBpNum _)

theorem kz_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : KZKE V (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4GetBreakpoint _ _)

theorem kz_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, KZKE V (check x0)) : KZKE V (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; kz_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible refine kz_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem kz_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : KZKE V (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeIrqControlRemapped _ _ _)

theorem kz_fl4ArchCheckIrq (irq : Data) : KZKE V (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4ArchCheckIrq _)

theorem kz_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : KZKE V (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4IrqControl _ _ _ _ _)

theorem kz_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : KZKE V (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4SetBreakpoint _ _)

theorem kz_decodeFl4SetFlags (args : List Data) (t : ObjRef) : KZKE V (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4SetFlags _ _)

theorem kz_decodeFl4SetTimer (args : List Data) (t : ObjRef) : KZKE V (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4SetTimer _ _)

theorem kz_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : KZKE V (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4UnsetBreakpoint _ _)

theorem kz_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : KZKE V (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeFl4TcbExt _ _ _ _ _)

theorem kz_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : KZKE V (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeIrqHandlerInvocation _ _ _)

theorem kz_getScReleased (scPtr : ObjRef) : KZK V (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getScReleased _)

theorem kz_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : KZKE V (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSchedContextBind _ _)

theorem kz_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : KZKE V (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSchedContextUnbindObject _ _)

theorem kz_decodeSchedContextYieldTo (scPtr : ObjRef) : KZKE V (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSchedContextYieldTo _)

theorem kz_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : KZKE V (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSchedContextInvocation _ _ _)

theorem kz_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : KZKE V (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSchedControlInvocationFlags _ _ _)

theorem kz_rangeCheck (v minV maxV : Word) : KZKE V (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_rangeCheck _ _ _)

theorem kz_decodeSetFlags (args : List Data) (cap : Cap) : KZKE V (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetFlags _ _)

theorem kz_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : KZKE V (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetIpcBuffer _ _ _ _)

theorem kz_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetMcpriority _ _ _ _)

theorem kz_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetPriority _ _ _ _)

theorem kz_isBlocked (thread : ObjRef) : KZK V (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_isBlocked _)

theorem kz_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : KZKE V (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeUpdateSc _ _ _)

theorem kz_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetSchedParams _ _ _ _)

theorem kz_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : KZKE V (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetSpace _ _ _ _)

theorem kz_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetTimeoutEp _ _ _)

theorem kz_decodeSetTlsBase (args : List Data) (cap : Cap) : KZKE V (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeSetTlsBase _ _)

theorem kz_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : KZKE V (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeTcbConfigure _ _ _ _)

theorem kz_decodeUnbindNotification (cap : Cap) : KZKE V (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem kz_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : KZKE V (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeTcbInvocation _ _ _ _ _)

theorem kz_decodePml4Flush (cap : ArchCap) : KZKE V (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodePml4Flush _)

theorem kz_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : KZKE V (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_frameMappingSlot _ _ _ _)

theorem kz_decodeTestAndClearAccessed (cap : ArchCap) : KZKE V (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeTestAndClearAccessed _)

theorem kz_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : KZKE V (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem kz_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : KZK V (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getMrs _ _ _)

theorem kz_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : KZKE V (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem kz_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    KZKE V (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem kz_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : KZKE V (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem kz_getCapReg (reg : Register) : KZK V (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; kz_auto
macro_rules | `(tactic| kz_leaf) => `(tactic| with_reducible exact kz_getCapReg _)

end

end Fl4Proofs.P3.SInvR.A12b
