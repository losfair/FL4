/-
P3 (DESIGN.md §9), invariant line G1 (ctq14, item 5 (a)): **`CKN`, ctq11's
`CK` with "ct is not BlockedOnReply", across the deletion cone: the leaves**
(spec side only, outside the JAtZ cone).

* **`CKN s`**: if the current thread is a TCB, its SC is none or `cur_sc`
  (ctq11's `CK`, l4v `cur_sc_tcb` / `ct_schedulable`'s SC half) and it is not
  BlockedOnReply. The second half is what `reply_remove`'s donation needs:
  its caller is read BlockedOnReply, hence `≠ ct` (`fast_finalise` /
  `finalise_cap`'s reply arm). At the perform ct is Restart.
* In the deletion cone `cur_sc` and `cur_thread` are never written (their
  only writers are `switch_sched_context` / `switch_to_thread`, in
  `schedule`), and a TCB's SC field only by `sched_context_unbind_tcb` /
  `maybe_return_sc` (to none) and `sched_context_donate` (here only from
  `reply_remove`, to a thread `≠ ct`).
* Leaves (after ctq11's SpecInvCqG): `set_object` of a non-TCB, TCB writes
  keeping `CKT` (`ck_threadSet`: SC kept or none, state kept or non-reply),
  a TCB write at a thread `≠ ct` (`ck_threadSet_ne`), `set_thread_state` to a
  non-reply state (`ck_setThreadState`), set_cap, as_user, set_mrs; the
  `ck_auto` driver of the generated family SpecInvCqHF*.
-/
import Fl4Proofs.P3.SpecInvCqH1
import Fl4Proofs.P3.SpecInvCqGB
open Classical

namespace Fl4Proofs.P3.SInvQ.R14
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- The TCB part of `CKN` for SC `c`. -/
abbrev CKT (c : ObjRef) (y : Tcb) : Prop :=
  (y.tcbSchedContext = none ∨ y.tcbSchedContext = some c) ∧ ∀ r, y.tcbState ≠ .blockedOnReply r

/-- **CKN**: ctq11's `CK` and ct not BlockedOnReply. -/
abbrev CKN (s : State Unit) : Prop := ∀ x, s.kheap s.curThread = some (.tcb x) → CKT s.curSc x

abbrev CKK {α : Type} (m : NonDet (State Unit) α) : Prop := IK CKN m
abbrev CKKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE CKN m

theorem ckn_ck {s : State Unit} (h : CKN s) : R11.CK s := fun x hx => (h x hx).1

/-! ## The heap update of `set_object` -/

theorem ck_upd {σ : State Unit} (h : CKN σ) (p : ObjRef) (o : KernelObject)
    (hty : ∀ y, o = .tcb y → ∃ x, σ.kheap p = some (.tcb x))
    (ho : ∀ x, p = σ.curThread → σ.kheap p = some (.tcb x) → CKT σ.curSc x → ∀ y, o = .tcb y → CKT σ.curSc y) :
    CKN { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro y hy
  show CKT σ.curSc y
  change Function.update σ.kheap p (some o) σ.curThread = some (.tcb y) at hy
  by_cases e : σ.curThread = p
  · rw [e, Function.update_self] at hy
    have ho' : o = .tcb y := by injection hy
    obtain ⟨x, hx⟩ := hty y ho'
    exact ho x e.symm hx (h x (by rw [e]; exact hx)) y ho'
  · rw [Function.update_of_ne e] at hy
    exact h y hy

theorem ck_aType {a o : KernelObject} (h : aType a = aType o) (y : Tcb) (hy : o = .tcb y) : ∃ x, a = .tcb x := by
  subst hy; exact q1_aType_tcb h

theorem ck_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x, p = σ.curThread → σ.kheap p = some (.tcb x) → CKT σ.curSc x → ∀ y, o = .tcb y → CKT σ.curSc y) :
    IKp CKN σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ck_upd hσ p o (fun y0 hy0 => ?_) ho
  obtain ⟨x0, e⟩ := ck_aType hty y0 hy0
  exact ⟨x0, hk.trans (congrArg some e)⟩

theorem ck_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    CKK (setObject (Z := Unit) p o) :=
  fun σ => ck_setObject_p p o σ fun _ _ _ _ y e => (ho y e).elim

theorem ck_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h : ∀ c, CKT c x → CKT c y) : IKp CKN σ (setObject (Z := Unit) p (.tcb y)) :=
  ck_setObject_p _ _ σ fun x0 _ hk hc y0 e => by
    rw [hx] at hk; cases hk; cases e; exact h _ hc

theorem ck_setTcb_ne (p : ObjRef) (σ : State Unit) (hp : p ≠ σ.curThread) (y : Tcb) :
    IKp CKN σ (setObject (Z := Unit) p (.tcb y)) :=
  ck_setObject_p _ _ σ fun _ e _ _ _ _ => absurd e hp

theorem ck_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    CKK (setSimpleKo (Z := Unit) f p e) := by
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
  refine ck_upd hσ _ _ (fun y0 hy0 => ?_) (fun x0 _ hx0 _ _ _ => ?_)
  · obtain ⟨x0, e⟩ := ck_aType hty y0 hy0
    exfalso
    dsimp only at e; subst e
    simp [isSimpleType, aType] at hsimp
  · exfalso
    rw [hk] at hx0; cases hx0
    simp [isSimpleType, aType] at hsimp

/-- A TCB update keeping `CKT` (SC kept or none, state kept or not a reply wait). -/
theorem ck_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext ∨ (f x).tcbSchedContext = none)
    (hs : ∀ x, (f x).tcbState = x.tcbState ∨ ∀ r, (f x).tcbState ≠ .blockedOnReply r) :
    CKK (threadSet (Z := Unit) f t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ck_setTcb_keep _ x σ (getTcb_kheap hx) _ fun c hc => ⟨?_, ?_⟩
  · rcases hf x with e | e
    · rw [e]; exact hc.1
    · exact Or.inl e
  · rcases hs x with e | e
    · rw [e]; exact hc.2
    · exact e

/-- A TCB update of a thread `≠ ct` (any update). -/
theorem ck_threadSet_ne (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit) (ht : t ≠ σ.curThread) :
    IKp CKN σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact ck_setTcb_ne t σ ht _ hσ y hy

theorem ck_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : CKK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => ck_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ h => h

theorem ck_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : CKK (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (ck_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ h => h) fun _ => ik_pure _

theorem ck_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : CKK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (ck_setTcb_keep _ x σ (getTcb_kheap hx) _ fun _ h => h) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem ck_setCap (c : Cap) (sl : CslotPtr) : CKK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (ck_setObject_p _ _ σ fun _ _ _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    split
    · exact ikp_pure_bind (ck_setTcb_keep _ tcb σ hk _ fun _ h => h)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem ck_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbSchedContext = x.tcbSchedContext) (h2 : ∀ v x, (fn v x).tcbState = x.tcbState) :
    CKK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ck_threadSet _ _ (fun x => Or.inl (h _ x)) (fun x => Or.inl (h2 _ x))

/-! ## `ck_auto` -/

syntax "ck_leaf" : tactic
macro_rules | `(tactic| ck_leaf) => `(tactic| fail "no ck_leaf")

macro "ck_side" : tactic => `(tactic| first
  | (intro _; exact Or.inl rfl)
  | (intro _; exact Or.inr rfl)
  | (intro _; right; intro _ h; cases h)
  | (intro t ht; cases ht; done)
  | (intro _ _; rfl))

macro "ck_auto" : tactic => `(tactic| repeat' (first | ck_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- `set_thread_state` to a state that is not a reply wait. -/
theorem ck_setThreadState (t : ObjRef) (ts : ThreadState) (h : ∀ r, ts ≠ .blockedOnReply r) :
    CKK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (ck_threadSet _ _ (fun _ => Or.inl rfl) (fun _ => Or.inr h)) fun _ => ?_
  unfold setThreadStateAct
  repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless))

macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ck_setObject _ _ ?_); intro _ h; cases h))
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ck_setSimpleKo _ _ _)
macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ck_threadSet _ _ ?_ ?_) <;> ck_side))
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ck_archThreadSet _ _)
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ck_asUser _ _)
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ck_setMrs _ _ _)
macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact ck_setCap _ _)
macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ck_optionUpdateThread _ _ _ ?_ ?_) <;> (intro _ _; rfl)))
macro_rules | `(tactic| ck_leaf) => `(tactic| ((with_reducible refine ck_setThreadState _ _ ?_); intro _ h; cases h))

end

end Fl4Proofs.P3.SInvQ.R14
