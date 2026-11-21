/-
P3 (DESIGN.md §9), invariant line G1 (ctq11): **`RT`: under
`resume_cur_thread` the current thread is a TCB with an SC** (spec side
only, outside the JAtZ cone; KENTRY-PLAN ctq10 handoff 1).

`RT s := action = resume_cur_thread → ∃ x, kheap ct = tcb x ∧ x's SC ≠ none`
is ctq10's `ResSc` with "ct is a TCB" (`resSc_of_rt`, SpecInvCqGB). It is a
stepwise invariant of the event with no local hypothesis besides the untyped
performs' (SpecInvCqGU):

* only `schedule` sets `resume_cur_thread` (Schedule.lean:186/222) and only
  `switch_to(_idle)_thread` writes `cur_thread` (both in the exit's cone, not
  in the event's); every other `set_scheduler_action` writes another action
  (`rt_setSchedulerAction`);
* `set_object` keeps the object's type (`aType` assert), so ct stays a TCB;
  a TCB write either keeps `tcb_sched_context` or sets it to `some`;
* the writers of `None` into a TCB's SC field all reschedule when that TCB is
  current: `sched_context_unbind_tcb` (before the write),
  `sched_context_donate` (`test_reschedule` after it), `maybe_return_sc`
  (after it): hand lemmas in the generated family (scratch/rt/manual.py);
* the untyped performs' detype / retype (SpecInvCqGU): ct's TCB has an SC,
  so it is live (`liveO`) and not in a childless untyped's region (sl4's
  `noLive_reg`), and retyped addresses hold no object (UtInv3 freshness).

This module: the leaves and the driver `rt_auto` of the generated family
SpecInvCqGF1..F5.
-/
import Fl4Proofs.P3.SpecInvCqY
open Classical

namespace Fl4Proofs.P3.SInvQ.R11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- **RT**: under `resume_cur_thread` the current thread is a TCB with an SC. -/
abbrev RT (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread → ∃ x, s.kheap s.curThread = some (.tcb x) ∧ x.tcbSchedContext ≠ none

abbrev RTK {α : Type} (m : NonDet (State Unit) α) : Prop := IK RT m
abbrev RTKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE RT m

/-- The scheduler action and the current thread are `A` and `C`. -/
abbrev KC (A : SchedulerAction) (C : ObjRef) (s : State Unit) : Prop :=
  s.schedulerAction = A ∧ s.curThread = C

/-- Under `resume_cur_thread` the current thread is not `t`. -/
abbrev AC (t : ObjRef) (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread → s.curThread ≠ t

theorem ac_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : ∀ A C, IK (KC A C) m) : IK (AC t) m := by
  intro σ hσ y hy
  obtain ⟨e1, e2⟩ := h σ.schedulerAction σ.curThread σ ⟨rfl, rfl⟩ y hy
  intro hs; rw [e2]; exact hσ (by rw [← e1]; exact hs)

theorem r11_ikAnd {P Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h1 : IK P m) (h2 : IK Q m) :
    IK (fun s => P s ∧ Q s) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

/-! ## The heap update of `set_object` -/

theorem rt_upd {σ : State Unit} (h : RT σ) (p : ObjRef) (o : KernelObject)
    (hty : ∀ x, σ.kheap p = some (.tcb x) → ∃ y, o = .tcb y)
    (ho : ∀ x, σ.schedulerAction = .resumeCurThread → p = σ.curThread → σ.kheap p = some (.tcb x) →
      x.tcbSchedContext ≠ none → ∀ y, o = .tcb y → y.tcbSchedContext ≠ none) :
    RT { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro hs
  obtain ⟨x0, hx0, hn⟩ := h hs
  show ∃ x, Function.update σ.kheap p (some o) σ.curThread = some (.tcb x) ∧ x.tcbSchedContext ≠ none
  by_cases e : σ.curThread = p
  · rw [e] at hx0 ⊢
    obtain ⟨y, rfl⟩ := hty x0 hx0
    exact ⟨y, by simp, ho x0 hs e.symm hx0 hn y rfl⟩
  · exact ⟨x0, by rw [Function.update_of_ne e]; exact hx0, hn⟩

theorem rt_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x, σ.schedulerAction = .resumeCurThread → p = σ.curThread → σ.kheap p = some (.tcb x) →
      x.tcbSchedContext ≠ none → ∀ y, o = .tcb y → y.tcbSchedContext ≠ none) :
    IKp RT σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst y2
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine rt_upd hσ p o (fun x0 hx0 => ?_) ho
  rw [hk] at hx0; cases hx0
  exact q1_aType_tcb hty.symm

theorem rt_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    RTK (setObject (Z := Unit) p o) :=
  fun σ => rt_setObject_p p o σ fun _ _ _ _ _ y e => (ho y e).elim

theorem rt_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h : x.tcbSchedContext ≠ none → y.tcbSchedContext ≠ none) : IKp RT σ (setObject (Z := Unit) p (.tcb y)) :=
  rt_setObject_p _ _ σ fun x0 _ _ hk hn y0 e => by
    rw [hx] at hk; cases hk; cases e; exact h hn

/-- A TCB write at a thread that is not current under `resume_cur_thread`. -/
theorem rt_setTcb_ac (p : ObjRef) (σ : State Unit) (hA : AC p σ) (y : Tcb) :
    IKp RT σ (setObject (Z := Unit) p (.tcb y)) :=
  rt_setObject_p _ _ σ fun _ hs e _ _ _ _ => absurd e.symm (hA hs)

theorem rt_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    RTK (setSimpleKo (Z := Unit) f p e) := by
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
  refine rt_upd hσ _ _ (fun x0 hx0 => ?_) (fun x0 _ _ hx0 _ _ _ => ?_)
  all_goals
    exfalso
    rw [hk] at hx0; cases hx0
    simp [isSimpleType, aType] at hsimp

theorem rt_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, x.tcbSchedContext ≠ none → (f x).tcbSchedContext ≠ none) :
    RTK (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => rt_setTcb_keep _ x σ (getTcb_kheap hx) _ (hf x)

/-- `thread_set` of a thread that is not current under `resume_cur_thread` (any update). -/
theorem rt_threadSet_ac (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit) (hA : AC t σ) :
    IKp RT σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact rt_setTcb_ac t σ hA _ hσ y hy

theorem rt_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : RTK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => rt_setTcb_keep _ x σ (getTcb_kheap hx) _ id

theorem rt_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : RTK (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (rt_setTcb_keep _ x σ (getTcb_kheap hx) _ id) fun _ => ik_pure _

theorem rt_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : RTK (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (rt_setTcb_keep _ x σ (getTcb_kheap hx) _ id) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem rt_setCap (c : Cap) (sl : CslotPtr) : RTK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (rt_setObject_p _ _ σ fun _ _ _ _ _ _ e => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    split
    · exact ikp_pure_bind (rt_setTcb_keep _ tcb σ hk _ id)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem rt_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbSchedContext = x.tcbSchedContext) : RTK (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact rt_threadSet _ _ fun x hx => by rw [h]; exact hx

/-- Every action but `resume_cur_thread`. -/
theorem rt_setSchedulerAction (a : SchedulerAction) (ha : a ≠ .resumeCurThread) :
    RTK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction
  intro σ _ y hy
  rw [Set.mem_singleton_iff.1 hy]
  intro hs; exact absurd hs ha

/-! ## `KC` frames and the reschedule's post -/

theorem kc_setObject (A : SchedulerAction) (C : ObjRef) (p : ObjRef) (o : KernelObject) :
    IK (KC A C) (setObject (Z := Unit) p o) := by
  unfold setObject; repeat' (first | ik_step0 | ik_unfold)

theorem kc_threadSet (A : SchedulerAction) (C : ObjRef) (f : Tcb → Tcb) (t : ObjRef) :
    IK (KC A C) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun _ σ _ => ikp_of_ik (kc_setObject A C _ _) σ

theorem post_cn : PostK (fun s => s.schedulerAction = .chooseNewThread)
    (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  intro σ y hy
  rw [Set.mem_singleton_iff.1 hy]

/-- `reschedule_required` ends at `choose_new_thread`. -/
theorem cn_rescheduleRequired : PostK (fun s => s.schedulerAction = .chooseNewThread)
    (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine post_bind fun _ => ?_
  try dsimp only
  split <;> repeat' (first | exact post_cn | refine post_bind fun _ => ?_)

/-- `test_reschedule` of the current thread ends at `choose_new_thread`. -/
theorem cn_testReschedule (t : ObjRef) (σ : State Unit) (he : t = σ.curThread) :
    ∀ y ∈ (testReschedule (Z := Unit) t σ).1, y.2.schedulerAction = .chooseNewThread := by
  unfold testReschedule
  intro y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨v, hv, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hv] at hy
  try dsimp only at hy
  unfold NonDet.when at hy
  rw [if_pos (Or.inl he)] at hy
  exact cn_rescheduleRequired _ y hy

/-- `RT ∧ AC t` from an `RT` frame keeping the action and the current thread. -/
theorem r11_ra {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : RTK m) (h2 : ∀ A C, IK (KC A C) m) :
    IK (fun s => RT s ∧ AC t s) m :=
  r11_ikAnd h1 (ac_of h2)

/-! ## `rt_auto` -/

syntax "rt_leaf" : tactic
macro_rules | `(tactic| rt_leaf) => `(tactic| fail "no rt_leaf")

macro "rt_side" : tactic => `(tactic| first
  | (intro _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ _; exact Option.some_ne_none _)
  | (intro _ _; simp [tcbSchedContextUpdate])
  | (intro _ _; rfl)
  | (intro h; cases h)
  | (intro _ _ h; exact h))

macro "rt_auto" : tactic => `(tactic| repeat' (first | rt_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h))
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine rt_setObject _ _ ?_); intro _ h; cases h))
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact rt_setSimpleKo _ _ _)
macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine rt_threadSet _ _ ?_); rt_side))
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact rt_archThreadSet _ _)
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact rt_asUser _ _)
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact rt_setMrs _ _ _)
macro_rules | `(tactic| rt_leaf) => `(tactic| with_reducible exact rt_setCap _ _)
macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine rt_optionUpdateThread _ _ _ ?_); (intro _ _; rfl)))
macro_rules | `(tactic| rt_leaf) => `(tactic| ((with_reducible refine rt_setSchedulerAction _ ?_); (intro h; cases h)))

end

end Fl4Proofs.P3.SInvQ.R11
