/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq1): **the lookups and
the decode keep every SC, the current and idle SC and the consumed time**
(spec side only, outside the `JAtZ` cone).

`VZv σ` is that view (`scAt σ p`: the SC object at `p`, with its size);
`VZK V m := IK (VZ V) m`. It carries the configure perform's entry facts
(`CfgOK`, SpecInvEqC) from the front's `check_budget_restart` to the perform.
The lemmas are sg1's SpecInvSgI1..I6 restricted to the functions below the
lookups and `fl4DecodeInvocation` (proofs/scratch/epq1/tr2.py, untracked);
leaves: `vz_setObject` (an object that is neither an SC nor a CNode: by
`a_type` the old one is no SC either), the TCB writers, `set_simple_ko`.
-/
import Fl4Proofs.P3.SpecInvEqB
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The SC object at `p`. -/
def scAt (σ : State Unit) (p : ObjRef) : Option (SchedContext × Nat) :=
  match σ.kheap p with
  | some (.schedContext y n) => some (y, n)
  | _ => none

abbrev VZw := (ObjRef → Option (SchedContext × Nat)) × ObjRef × ObjRef × Ticks

/-- The view. -/
def VZv (σ : State Unit) : VZw := (scAt σ, σ.curSc, σ.idleSc, σ.consumedTime)

def VZ (V : VZw) (σ : State Unit) : Prop := VZv σ = V

abbrev VZK (V : VZw) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (VZ V) m
abbrev VZKE (V : VZw) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (VZ V) m

variable {V : VZw}

theorem mem_setObjectV {p : ObjRef} {o : KernelObject} {σ : State Unit} {y : Unit × State Unit}
    (h : y ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧
      y.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at h
  obtain ⟨⟨y1, y2⟩, hy, hx⟩ := h
  obtain ⟨e1, e2⟩ := mem_getObject hy
  simp only at e1 e2; subst e2
  obtain ⟨z, ⟨hz, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  exact ⟨y1, e1, hz, by rw [Set.mem_singleton_iff.1 hx]⟩

/-- Neither an SC nor a CNode (an SC's or a CNode's `a_type` may be garbage). -/
def NSC : KernelObject → Prop
  | .schedContext _ _ => False
  | .cnode _ _ => False
  | _ => True

theorem nsc_old {k o : KernelObject} (h : aType k = aType o) (ho : NSC o) : ∀ y n, k ≠ .schedContext y n := by
  intro y n e
  subst e
  cases o <;> simp only [NSC] at ho <;> simp only [aType] at h <;> split_ifs at h <;> cases h

theorem scAt_put {σ : State Unit} {p : ObjRef} {k o : KernelObject} (hk : σ.kheap p = some k)
    (hko : ∀ y n, k ≠ .schedContext y n) (ho : ∀ y n, o ≠ .schedContext y n) :
    scAt { σ with kheap := Function.update σ.kheap p (some o) } = scAt σ := by
  funext q
  unfold scAt
  dsimp only
  rw [Function.update_apply]
  split_ifs with e
  · subst e; rw [hk]
    cases o <;> (try exact absurd rfl (ho _ _)) <;> cases k <;> (try exact absurd rfl (hko _ _)) <;> rfl
  · rfl

theorem vz_setObject (p : ObjRef) (o : KernelObject) (ho : NSC o) : VZK V (setObject (Z := Unit) p o) := by
  intro σ hσ y hy
  obtain ⟨k, hk, ht, e⟩ := mem_setObjectV hy
  rw [e]
  have ho' : ∀ y n, o ≠ .schedContext y n := fun y n e => by subst e; exact ho
  unfold VZ VZv at hσ ⊢
  rw [scAt_put hk (nsc_old ht ho) ho']
  exact hσ

theorem vz_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    VZK V (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have hn : ∀ o : KernelObject, (aType o = .aEndpoint ∨ aType o = .aNTFN ∨ aType o = .aReply) →
      ∀ y n, o ≠ .schedContext y n := by
    intro o h y n e; subst e; simp only [aType] at h; split_ifs at h <;> simp at h
  simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
  have h1 := hn obj hsimp
  have h2 := hn (f e) (by rw [← hty]; exact hsimp)
  unfold VZ VZv at hσ ⊢
  rw [scAt_put hk h1 h2]; exact hσ

macro "vz_side" : tactic => `(tactic| first
  | trivial
  | (intro _ _ h; exact h)
  | (intro _ h; exact h))

macro "vz0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); vz_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); vz_side)
  | with_reducible exact ik_getObject _
  | ((with_reducible refine vz_setObject _ _ ?_); vz_side)
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem vz_threadSet (f : Tcb → Tcb) (t : ObjRef) : VZK V (threadSet (Z := Unit) f t) := by
  unfold threadSet; vz0_auto

theorem vz_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : VZK V (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; vz0_auto

theorem vz_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : VZK V (asUser (Z := Unit) t u) := by
  unfold asUser; vz0_auto

theorem vz_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : VZK V (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; vz0_auto

theorem vz_setThreadState (t : ObjRef) (ts : ThreadState) : VZK V (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (vz_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; vz0_auto

theorem vz_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    VZK V (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact vz_threadSet _ _

syntax "vz_leaf" : tactic
macro_rules | `(tactic| vz_leaf) => `(tactic| fail "no vz_leaf")

macro "vz_auto" : tactic => `(tactic| repeat' (first | vz_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| vz_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); vz_side))
macro_rules | `(tactic| vz_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); vz_side))
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| vz_leaf) => `(tactic| ((with_reducible refine vz_setObject _ _ ?_); vz_side))
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_setSimpleKo _ _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_threadSet _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_archThreadSet _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_asUser _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_setMrs _ _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_setThreadState _ _)
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_optionUpdateThread _ _ _)

theorem vz_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : VZK V (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_threadGet _ _)

theorem vz_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : VZK V (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getTcbObjRef _ _)

theorem vz_getCap (a0 : CslotPtr) : VZK V (getCap (Z := Unit) a0) := by
  unfold getCap; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getCap _)

theorem vz_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : VZK V (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupIpcBuffer _ _)

theorem vz_setMessageInfo (thread : ObjRef) (info : MessageInfo) : VZK V (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_setMessageInfo _ _)

theorem vz_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : VZK V (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_storeWordOffs _ _ _)

theorem vz_replyFromKernel (thread : ObjRef) (x : Data × List Data) : VZK V (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_replyFromKernel _ _)

theorem vz_getSchedContext (ptr : ObjRef) : VZK V (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getSchedContext _)

theorem vz_getThreadState (ref : ObjRef) : VZK V (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getThreadState _)

theorem vz_ensureEmpty (slot : CslotPtr) : VZKE V (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_ensureEmpty _)

theorem vz_isIoportRangeFree (f l : IoPort) : VZK V (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_isIoportRangeFree _ _)

theorem vz_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : VZKE V m) : VZKE V (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; vz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible refine vz_lookupErrorOnFailure _ _ ?_)

theorem vz_resolveAddressBits' (p : Cap × CapRef) : VZKE V (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by vz_auto)) fun nc => ?_
        split
        · exact vz_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_resolveAddressBits' _)

theorem vz_resolveAddressBits (a0 : Cap × CapRef) : VZKE V (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_resolveAddressBits _)

theorem vz_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : VZKE V (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupSlotForCnodeOp _ _ _ _)

theorem vz_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : VZKE V (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupTargetSlot _ _ _)

theorem vz_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : VZKE V (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeIoportControlInvocation _ _ _ _ _)

theorem vz_getAsidPool (ptr : ObjRef) : VZK V (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getAsidPool _)

theorem vz_findVspaceForAsid (asid : Asid) : VZKE V (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_findVspaceForAsid _)

theorem vz_getPdpt (ptr : ObjRef) : VZK V (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPdpt _)

theorem vz_getPdpte (ptr : ObjRef) : VZK V (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPdpte _)

theorem vz_isFinalCap (cap : Cap) : VZK V (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_isFinalCap _)

theorem vz_getPml4 (ptr : ObjRef) : VZK V (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPml4 _)

theorem vz_getPml4e (ptr : ObjRef) : VZK V (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPml4e _)

theorem vz_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : VZKE V (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupPdptSlot _ _)

theorem vz_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePageDirectoryInvocation _ _ _ _ _)

theorem vz_checkVpAlignment (sz : VMPageSize) (vptr : Word) : VZKE V (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_checkVpAlignment _ _)

theorem vz_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : VZKE V (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupPdSlot _ _)

theorem vz_getPd (ptr : ObjRef) : VZK V (getPd (Z := Unit) ptr) := by
  unfold getPd; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPd _)

theorem vz_getPde (ptr : ObjRef) : VZK V (getPde (Z := Unit) ptr) := by
  unfold getPde; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPde _)

theorem vz_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : VZKE V (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupPtSlot _ _)

theorem vz_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : VZKE V (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_createMappingEntries _ _ _ _ _ _)

theorem vz_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : VZKE V (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_ensureSafeMapping _)

theorem vz_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePageInvocation _ _ _ _ _)

theorem vz_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePageTableInvocation _ _ _ _ _)

theorem vz_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePdptInvocation _ _ _ _ _)

theorem vz_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : VZKE V (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_ensurePortOperationAllowed _ _ _)

theorem vz_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : VZKE V (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePortInvocation _ _ _)

theorem vz_ensureNoChildren (cslotPtr : CslotPtr) : VZKE V (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_ensureNoChildren _)

theorem vz_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : VZK V (selectExt (Z := Unit) a S) := by
  unfold selectExt; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_selectExt _ _)

theorem vz_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_archDecodeInvocation _ _ _ _ _ _)

theorem vz_getIrqState (irq : Irq) : VZK V (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getIrqState _)

theorem vz_isIrqActive (irq : Irq) : VZK V (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_isIrqActive _)

theorem vz_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : VZKE V (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_archDecodeIrqControlInvocation _ _ _ _)

theorem vz_archDeriveCap (c : ArchCap) : VZKE V (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_archDeriveCap _)

theorem vz_getPt (ptr : ObjRef) : VZK V (getPt (Z := Unit) ptr) := by
  unfold getPt; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPt _)

theorem vz_getPte (ptr : ObjRef) : VZK V (getPte (Z := Unit) ptr) := by
  unfold getPte; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getPte _)

theorem vz_getTcbQueue (d : Domain) (prio : Priority) : VZK V (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getTcbQueue _ _)

theorem vz_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : VZK V (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_setTcbQueue _ _ _)

theorem vz_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : VZK V (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_tcbSchedAction _ _)

theorem vz_tcbReleaseRemove (tcbPtr : ObjRef) : VZK V (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_tcbReleaseRemove _)

theorem vz_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : VZK V (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getSimpleKo _ _)

theorem vz_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : VZK V (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getSkObjRef _ _ _)

theorem vz_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : VZK V (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getScObjRef _ _)

theorem vz_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : VZKE V m) : VZKE V (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; vz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible refine vz_capFaultOnFailure _ _ _ ?_)

theorem vz_loadWordOffs (ptr : ObjRef) (offs : Nat) : VZK V (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_loadWordOffs _ _)

theorem vz_getMessageInfo (thread : ObjRef) : VZK V (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getMessageInfo _)
theorem vz_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : VZK V (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; vz_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getExtraCptrs _ _)

theorem vz_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : VZKE V (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupSlotForThread _ _)

theorem vz_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : VZKE V (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupCapAndSlot _ _)

theorem vz_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : VZKE V (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupExtraCaps _ _ _)

theorem vz_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : VZKE V m) : VZK V (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; vz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible refine vz_constOnFailure _ _ ?_)

theorem vz_deriveCap (slot : CslotPtr) (cap : Cap) : VZKE V (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_deriveCap _ _)

theorem vz_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : VZKE V (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_checkHandlerEp _ _)

theorem vz_checkPrio (newPrio : Data) (authTcb : ObjRef) : VZKE V (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_checkPrio _ _)

theorem vz_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : VZKE V (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_checkValidIpcBuffer _ _)

theorem vz_dataToObjType (type : Data) : VZKE V (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_dataToObjType _)

theorem vz_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeBindNotification _ _)

theorem vz_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : VZKE V (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupPivotSlot _ _ _)

theorem vz_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : VZKE V (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_lookupSourceSlot _ _ _)

theorem vz_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : VZKE V (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeCnodeInvocation _ _ _ _)

theorem vz_slotCapLongRunningDelete (slot : CslotPtr) : VZK V (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_slotCapLongRunningDelete _)

theorem vz_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : VZKE V (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeCvSpace _ _ _ _)
theorem vz_subframeNode (nodeCap : Cap) (index depth : Data) : VZKE V (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_subframeNode _ _ _)

theorem vz_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : VZKE V (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeDeriveSubframe _ _ _ _)

theorem vz_decodeDomainScheduleConfigure (args : List Data) : VZKE V (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeDomainScheduleConfigure _)

theorem vz_decodeDomainScheduleSetStart (args : List Data) : VZKE V (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeDomainScheduleSetStart _)

theorem vz_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : VZKE V (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeDomainSet _ _)

theorem vz_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : VZKE V (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeDomainInvocation _ _ _)

theorem vz_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : VZK V (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4GetMr _ _ _)

theorem vz_fl4Arg (buf : Option ObjRef) (i : Nat) : VZKE V (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4Arg _ _)

theorem vz_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : VZKE V (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4ConfigureSingleStepping _ _)

theorem vz_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : VZKE V (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4FpuTransfer _ _ _ _)

theorem vz_fl4CheckBpNum (bp : Data) : VZKE V (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4CheckBpNum _)

theorem vz_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : VZKE V (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4GetBreakpoint _ _)

theorem vz_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, VZKE V (check x0)) : VZKE V (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; vz_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible refine vz_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem vz_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : VZKE V (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeIrqControlRemapped _ _ _)

theorem vz_fl4ArchCheckIrq (irq : Data) : VZKE V (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4ArchCheckIrq _)

theorem vz_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : VZKE V (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4IrqControl _ _ _ _ _)

theorem vz_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : VZKE V (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4SetBreakpoint _ _)

theorem vz_decodeFl4SetFlags (args : List Data) (t : ObjRef) : VZKE V (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4SetFlags _ _)

theorem vz_decodeFl4SetTimer (args : List Data) (t : ObjRef) : VZKE V (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4SetTimer _ _)

theorem vz_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : VZKE V (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4UnsetBreakpoint _ _)

theorem vz_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : VZKE V (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeFl4TcbExt _ _ _ _ _)

theorem vz_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : VZKE V (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeIrqHandlerInvocation _ _ _)

theorem vz_getScReleased (scPtr : ObjRef) : VZK V (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getScReleased _)

theorem vz_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : VZKE V (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSchedContextBind _ _)

theorem vz_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : VZKE V (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSchedContextUnbindObject _ _)

theorem vz_decodeSchedContextYieldTo (scPtr : ObjRef) : VZKE V (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSchedContextYieldTo _)

theorem vz_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : VZKE V (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSchedContextInvocation _ _ _)

theorem vz_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : VZKE V (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSchedControlInvocationFlags _ _ _)

theorem vz_rangeCheck (v minV maxV : Word) : VZKE V (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_rangeCheck _ _ _)

theorem vz_decodeSetFlags (args : List Data) (cap : Cap) : VZKE V (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetFlags _ _)

theorem vz_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : VZKE V (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetIpcBuffer _ _ _ _)

theorem vz_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetMcpriority _ _ _ _)

theorem vz_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetPriority _ _ _ _)

theorem vz_isBlocked (thread : ObjRef) : VZK V (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_isBlocked _)

theorem vz_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : VZKE V (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeUpdateSc _ _ _)

theorem vz_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetSchedParams _ _ _ _)

theorem vz_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : VZKE V (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetSpace _ _ _ _)

theorem vz_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetTimeoutEp _ _ _)

theorem vz_decodeSetTlsBase (args : List Data) (cap : Cap) : VZKE V (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeSetTlsBase _ _)

theorem vz_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : VZKE V (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeTcbConfigure _ _ _ _)

theorem vz_decodeUnbindNotification (cap : Cap) : VZKE V (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem vz_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : VZKE V (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeTcbInvocation _ _ _ _ _)

theorem vz_decodePml4Flush (cap : ArchCap) : VZKE V (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodePml4Flush _)

theorem vz_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : VZKE V (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_frameMappingSlot _ _ _ _)

theorem vz_decodeTestAndClearAccessed (cap : ArchCap) : VZKE V (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeTestAndClearAccessed _)

theorem vz_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : VZKE V (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem vz_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : VZK V (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getMrs _ _ _)

theorem vz_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : VZKE V (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem vz_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    VZKE V (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem vz_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : VZKE V (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem vz_getCapReg (reg : Register) : VZK V (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; vz_auto
macro_rules | `(tactic| vz_leaf) => `(tactic| with_reducible exact vz_getCapReg _)

end

end Fl4Proofs.P3.SInvE
