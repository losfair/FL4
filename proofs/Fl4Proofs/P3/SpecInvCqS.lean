/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq4): **the scheduler
slices carried with TQ** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq3 (a)-(c)).

* `RA σ`: the switch target is a runnable TCB (l4v `weak_valid_sched_action`,
  its `st_tcb_at runnable` half).
* `RR σ`: every thread of the release queue is a runnable TCB (l4v
  `valid_release_q`, its `st_tcb_at runnable` half).
* `CtNQR σ` (invB, l4v `ct_not_in_q`): under `resume_cur_thread` the current
  thread is in no ready queue.
* `SA σ := RA σ ∧ RR σ ∧ CtNQR σ` and **`SchedQ σ := TQ σ ∧ SA σ`**.

`SA` reads the heap only through "is a runnable TCB", so a heap write keeps
it when it keeps every runnable TCB runnable (`sa_setObject_p`), or writes a
thread that is neither the switch target nor released (`NP`, `sa_upd_np`);
a thread that is not runnable is neither (`np_of_nr`), so `set_thread_state`
of a blocked thread to any state keeps `SA`. Ready-queue writes keep `RA` /
`RR`; an enqueue keeps `CtNQR` unless it adds the current thread under
`resume_cur_thread` (`sa_tsa_p`).

Leaves and the `sa_auto` driver of the generated family SpecInvCqSF1..F5;
the scheduler writers by hand: `set_scheduler_action choose_new_thread`,
`reschedule_required` (`hk1` form: it ends at `choose_new_thread`),
`possible_switch_to` (target runnable; its other-domain enqueue needs the
target's domain = `cur_domain` or target ≠ ct), `tcb_release_remove`.
-/
import Fl4Proofs.P3.SpecInvCqR
import Fl4Proofs.P3.SpecInvCtNQR
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv
open Fl4Proofs.P3.SInvV (CtNQR boot_ctNQR)

noncomputable section

set_option maxHeartbeats 1000000

/-- **RA [J]** (l4v `weak_valid_sched_action`, runnable half). -/
abbrev RA (σ : State Unit) : Prop := ∀ t, σ.schedulerAction = .switchThread t → RnH t σ.kheap

/-- **RR [J]** (l4v `valid_release_q`, runnable half). -/
abbrev RR (σ : State Unit) : Prop := ∀ t ∈ σ.releaseQueue, RnH t σ.kheap

/-- **The scheduler slices.** -/
abbrev SA (σ : State Unit) : Prop := RA σ ∧ RR σ ∧ CtNQR σ

/-- **SchedQ [J]**: TQ and the scheduler slices (the carried bundle). -/
abbrev SchedQ (σ : State Unit) : Prop := TQ σ ∧ SA σ

abbrev SAK {α : Type} (m : NonDet (State Unit) α) : Prop := IK SA m
abbrev SAKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE SA m

theorem boot_sa : SA (initASt (Z := Unit)) :=
  ⟨fun _ h => by simp [initASt] at h, fun _ h => by simp [initASt] at h, boot_ctNQR⟩

theorem boot_schedQ : SchedQ (initASt (Z := Unit)) := ⟨boot_tq, boot_sa⟩

/-- `t` is neither the switch target nor released. -/
abbrev NP (t : ObjRef) (σ : State Unit) : Prop :=
  σ.schedulerAction ≠ .switchThread t ∧ t ∉ σ.releaseQueue

/-- A thread that is not a runnable TCB is neither the switch target nor released. -/
theorem np_of_nr {σ : State Unit} (h : SA σ) {t : ObjRef} (hn : ¬ RnH t σ.kheap) : NP t σ :=
  ⟨fun e => hn (h.1 t e), fun m => hn (h.2.1 t m)⟩

theorem np_of_tcb_nr {σ : State Unit} (h : SA σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = false) : NP t σ :=
  np_of_nr h fun ⟨y, hy, hy'⟩ => by rw [hx] at hy; cases hy; rw [hr] at hy'; cases hy'

/-! ## Frames -/

theorem sa_of_keep {σ σ' : State Unit} (h : SA σ) (hk : ∀ t, RnH t σ.kheap → RnH t σ'.kheap)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hq : σ'.readyQueues = σ.readyQueues) (hc : σ'.curThread = σ.curThread) : SA σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t ht => hk t (h1 t (ha.symm.trans ht)), fun t ht => hk t (h2 t (hr ▸ ht)), fun hs d p => ?_⟩
  rw [hq, hc]; exact h3 (ha.symm.trans hs) d p

theorem rnH_upd {kh : ObjRef → Option KernelObject} {p : ObjRef} {o : KernelObject}
    (ho : ∀ x, kh p = some (.tcb x) → runnable x.tcbState = true → ∃ y, o = .tcb y ∧ runnable y.tcbState = true)
    {t : ObjRef} (h : RnH t kh) : RnH t (Function.update kh p (some o)) := by
  obtain ⟨x, hx, hr⟩ := h
  by_cases e : t = p
  · subst e
    obtain ⟨y, rfl, hy⟩ := ho x hx hr
    exact ⟨y, by simp, hy⟩
  · exact ⟨x, by rw [Function.update_of_ne e]; exact hx, hr⟩

/-- A heap write at a thread that is neither the switch target nor released. -/
theorem sa_upd_np {σ : State Unit} (h : SA σ) (p : ObjRef) (o : KernelObject) (hp : NP p σ) :
    SA { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_, h3⟩
  · have e : t ≠ p := by rintro rfl; exact hp.1 ht
    obtain ⟨x, hx, hr⟩ := h1 t ht
    exact ⟨x, by show Function.update σ.kheap p (some o) t = _; rw [Function.update_of_ne e]; exact hx, hr⟩
  · have e : t ≠ p := by rintro rfl; exact hp.2 ht
    obtain ⟨x, hx, hr⟩ := h2 t ht
    exact ⟨x, by show Function.update σ.kheap p (some o) t = _; rw [Function.update_of_ne e]; exact hx, hr⟩

/-! ## Heap writes -/

/-- `setObject`: a TCB write keeps a runnable TCB runnable. -/
theorem sa_setObject_p (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x y, σ.kheap p = some (.tcb x) → o = .tcb y → runnable x.tcbState = true →
      runnable y.tcbState = true) :
    IKp SA σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine sa_of_keep hσ (fun t ht => rnH_upd (fun x0 hx0 hr => ?_) ht) rfl rfl rfl rfl
  rw [hk] at hx0; cases hx0
  obtain ⟨y, rfl⟩ := q1_aType_tcb hty.symm
  exact ⟨y, rfl, ho x0 y hk rfl hr⟩

/-- `setObject` at a thread that is neither the switch target nor released. -/
theorem sa_setObject_np (p : ObjRef) (o : KernelObject) (σ : State Unit) (hp : NP p σ) :
    IKp SA σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact sa_upd_np hσ p o hp

theorem sa_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    IK SA (setObject (Z := Unit) p o) :=
  fun σ => sa_setObject_p p o σ fun _ y _ e _ => (ho y e).elim

theorem sa_setTcb_keep (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h3 : y.tcbState = x.tcbState) : IKp SA σ (setObject (Z := Unit) p (.tcb y)) :=
  sa_setObject_p _ _ σ fun x0 y0 hk e hr => by
    rw [hx] at hk; cases hk; cases e; rw [h3]; exact hr

theorem sa_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK SA (setSimpleKo (Z := Unit) f p e) := by
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
  refine sa_of_keep hσ (fun t ht => rnH_upd (fun x0 hx0 _ => ?_) ht) rfl rfl rfl rfl
  exfalso
  rw [hk] at hx0; cases hx0
  simp [isSimpleType, aType] at hsimp

theorem sa_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, runnable x.tcbState = true → runnable (f x).tcbState = true) :
    IK SA (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => sa_setObject_p _ _ σ fun x' y hk e hr => by
    rw [getTcb_kheap hx] at hk; cases hk; cases e; exact hf x hr

theorem sa_threadSet_np (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit) (hp : NP t σ) :
    IKp SA σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    exact sa_setObject_np _ _ σ hp hσ y hy

theorem sa_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IK SA (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => sa_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl

theorem sa_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : IK SA (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (sa_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ik_pure _

theorem sa_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : IK SA (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (sa_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem sa_setCap (c : Cap) (sl : CslotPtr) : IK SA (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (sa_setObject_p _ _ σ fun _ _ _ e _ => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (sa_setTcb_keep _ tcb σ hk _ rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem sa_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState) : IK SA (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact sa_threadSet _ _ fun x hr => by rw [h]; exact hr

/-! ## Ready queues -/

/-- **`tcb_sched_action`**: an action adding only the thread, and that only
off `resume_cur_thread` or when the thread is not current. -/
theorem sa_tsa_p (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (σ : State Unit)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨
      (u = t ∧ (σ.schedulerAction ≠ .resumeCurThread ∨ t ≠ σ.curThread))) :
    IKp SA σ (tcbSchedAction (Z := Unit) act t) := by
  intro hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  obtain ⟨h1, h2, h3⟩ := hσ
  refine ⟨h1, h2, fun hs d p hm => ?_⟩
  dsimp only at hs hm
  split at hm
  · rcases hact _ _ hm with hm | ⟨e', hn⟩
    · exact h3 hs _ _ hm
    · rcases hn with hn | hn
      · exact hn hs
      · exact hn e'.symm
  · exact h3 hs d p hm

theorem sa_dequeue (t : ObjRef) : SAK (tcbSchedAction (Z := Unit) tcbSchedDequeue t) :=
  fun σ => sa_tsa_p _ t σ fun _ _ hu => Or.inl (List.mem_filter.1 hu).1

/-- An enqueue / append off `resume_cur_thread` or of a thread that is not current. -/
theorem sa_enq_p (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) (σ : State Unit)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t)
    (h : σ.schedulerAction ≠ .resumeCurThread ∨ t ≠ σ.curThread) :
    IKp SA σ (tcbSchedAction (Z := Unit) act t) :=
  sa_tsa_p act t σ fun q u hu => (hact q u hu).imp id fun e => ⟨e, h⟩

/-- `SA` and the scheduler action is `choose_new_thread`. -/
abbrev SAc (σ : State Unit) : Prop := SA σ ∧ σ.schedulerAction = .chooseNewThread

theorem sac_enq (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) : IK SAc (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  refine ⟨sa_enq_p act t σ hact (Or.inl (by rw [hσ.2]; exact fun h => by cases h)) hσ.1 y hy, ?_⟩
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact hσ.2

/-! ## Scheduler action and release queue -/

theorem sa_setSchedulerAction_cn : HK1 SA SAc (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  intro σ hσ x hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨⟨fun t ht => ?_, hσ.2.1, fun hs => ?_⟩, rfl⟩
  · exact absurd ht (by simp)
  · exact absurd hs (by simp)

theorem sa_setSchedulerAction_cn' : SAK (setSchedulerAction (Z := Unit) .chooseNewThread) :=
  fun σ hσ x hx => (sa_setSchedulerAction_cn σ hσ x hx).1

theorem sa_setThreadStateAct (t : ObjRef) : SAK (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | (with_reducible exact sa_setSchedulerAction_cn') | ik_step0 | ik_unfold)

/-- **`set_thread_state`**: a runnable state, or a thread that is neither the
switch target nor released. -/
theorem sa_setThreadState_p (t : ObjRef) (ts : ThreadState) (σ : State Unit)
    (h : runnable ts = true ∨ NP t σ) : IKp SA σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ikp_bind ?_ fun _ => sa_setThreadStateAct t
  rcases h with h | h
  · exact ikp_of_ik (sa_threadSet _ t fun _ _ => h) σ
  · exact sa_threadSet_np _ t σ h

theorem sa_setThreadState_r (t : ObjRef) (ts : ThreadState) (h : runnable ts = true) :
    SAK (setThreadState (Z := Unit) t ts) :=
  fun σ => sa_setThreadState_p t ts σ (Or.inl h)

/-- A thread that is not runnable at this state may get any state. -/
theorem sa_setThreadState_nr (t : ObjRef) (ts : ThreadState) (σ : State Unit) (x : Tcb)
    (hx : σ.kheap t = some (.tcb x)) (hr : runnable x.tcbState = false) :
    IKp SA σ (setThreadState (Z := Unit) t ts) :=
  fun hσ => sa_setThreadState_p t ts σ (Or.inr (np_of_tcb_nr hσ hx hr)) hσ

theorem sa_tcbReleaseRemove (t : ObjRef) : SAK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z, hz, hy⟩
  have hz' : SA z.2 ∧ z.2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨hσ, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨hσ, rfl⟩
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  rw [Set.mem_singleton_iff.1 hy]
  obtain ⟨⟨h1, h2, h3⟩, e⟩ := hz'
  refine ⟨h1, fun u hu => h2 u ?_, h3⟩
  rw [e]; exact (List.mem_filter.1 hu).1

/-! ## `sa_auto` -/

syntax "sa_leaf" : tactic
macro_rules | `(tactic| sa_leaf) => `(tactic| fail "no sa_leaf")

macro "sa_auto" : tactic => `(tactic| repeat' (first | sa_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); tq_side))
macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); tq_side))
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine sa_setObject _ _ ?_); tq_side))
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_setSimpleKo _ _ _)
macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine sa_threadSet _ _ ?_); tq_side))
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_archThreadSet _ _)
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_asUser _ _)
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_setMrs _ _ _)
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_setCap _ _)
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_dequeue _)
macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine sa_setThreadState_r _ _ ?_); tq_side))
macro_rules | `(tactic| sa_leaf) => `(tactic| ((with_reducible refine sa_optionUpdateThread _ _ _ ?_); (intro _ _; rfl)))
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_setThreadStateAct _)
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_setSchedulerAction_cn')
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_tcbReleaseRemove _)

/-! ## `reschedule_required`, `possible_switch_to` -/

theorem ikp_threadGet_bind {P : State Unit → Prop} {β γ : Type} {f : Tcb → β} {t : ObjRef}
    {k : β → NonDet (State Unit) γ} {σ : State Unit}
    (h : ∀ x, σ.kheap t = some (.tcb x) → IKp P σ (k (f x))) : IKp P σ (threadGet (Z := Unit) f t >>= k) := by
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  exact h x hx hσ y hy

theorem ikp_when {P : State Unit → Prop} {σ : State Unit} (c : Prop) [Decidable c] {m : NonDet (State Unit) Unit}
    (h : c → IKp P σ m) : IKp P σ (NonDet.when c m) := by
  unfold NonDet.when
  split
  · exact h ‹c›
  · exact ikp_of_ik (ik_pure' _) σ

/-- `SA` off `resume_cur_thread`. -/
abbrev SAn (σ : State Unit) : Prop := SA σ ∧ σ.schedulerAction ≠ .resumeCurThread

/-- An enqueue off `resume_cur_thread`, the action kept. -/
theorem sa_enq_nr (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) :
    IK SAn (tcbSchedAction (Z := Unit) act t) := by
  intro s hs y hy
  refine ⟨sa_enq_p act t s hact (Or.inl hs.2) hs.1 y hy, ?_⟩
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact hs.2

theorem san_setSchedulerAction_cn : IK SAn (setSchedulerAction (Z := Unit) .chooseNewThread) :=
  fun σ hσ x hx => ⟨(sa_setSchedulerAction_cn σ hσ.1 x hx).1, by
    rw [(sa_setSchedulerAction_cn σ hσ.1 x hx).2]; exact fun e => absurd e (by simp)⟩

/-- **`reschedule_required`** (by cases on the action; its `do` has a join
point, so no generator `auto` over it): the switch target is enqueued while
the action is still `switch_thread`. -/
theorem sa_rescheduleRequired' : SAK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine ik_gets_bind fun σ => ?_
  try dsimp only
  split
  · rename_i t ht
    refine ikp_strengthen (P' := SAn) (fun h => ⟨h, by rw [ht]; exact fun e => absurd e (by simp)⟩) ?_
      fun _ h => h.1
    repeat' (first | (with_reducible exact sa_enq_nr _ _ (q1_enq _)) | (with_reducible exact san_setSchedulerAction_cn) | ik_step0 | ik_unfold)
  · exact ikp_of_ik sa_setSchedulerAction_cn' σ
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_rescheduleRequired')

/-- Every outcome satisfies `Q`. -/
def PostK (Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ s y, y ∈ (m s).1 → Q y.2

theorem post_bind {Q : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hg : ∀ a, PostK Q (g a)) : PostK Q (m >>= g) := by
  intro s y hy
  obtain ⟨z, -, hy⟩ := hy
  exact hg z.1 z.2 y hy

theorem post_set (a : SchedulerAction) : PostK (fun s => s.schedulerAction = a) (setSchedulerAction (Z := Unit) a) := by
  intro s y hy; unfold setSchedulerAction at hy; rw [Set.mem_singleton_iff.1 hy]

theorem rescheduleRequired_cn : PostK (fun s => s.schedulerAction = .chooseNewThread) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine post_bind fun a => ?_
  try dsimp only
  split <;> repeat' (first | exact post_set _ | refine post_bind fun _ => ?_)

/-- `reschedule_required` ends at `choose_new_thread`. -/
theorem sa_rescheduleRequired : HK1 SA SAc (rescheduleRequired (Z := Unit)) :=
  fun σ hσ y hy => ⟨sa_rescheduleRequired' σ hσ y hy, rescheduleRequired_cn σ y hy⟩

/-- **`reply_unlink_tcb`** (it asserts the thread blocked before making it
Inactive: a blocked thread is neither the switch target nor released). -/
theorem sa_replyUnlinkTcb (t r : ObjRef) : SAK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb
  refine ik_bind (by sa_auto) fun reply => ?_
  refine ik_bind (ik_assert _) fun _ => ?_
  unfold getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hP, rfl⟩ := hz
  have hr : runnable x.tcbState = false := by
    rcases hP with h | ⟨ep, d, h⟩ <;> rw [h] <;> rfl
  have hA : SAK (setReplyObjRef (Z := Unit) replyTcbUpdate r none) := by sa_auto
  have hB : IK (NP t) (setReplyObjRef (Z := Unit) replyTcbUpdate r none) := by
    repeat' (first | ik_step0 | ik_unfold)
  obtain ⟨w, hw, hy⟩ := hy
  exact sa_setThreadState_p t _ w.2 (Or.inr (hB σ (np_of_tcb_nr hσ hx hr) w hw)) (hA σ hσ w hw) y hy
macro_rules | `(tactic| sa_leaf) => `(tactic| with_reducible exact sa_replyUnlinkTcb _ _)

/-- The target's domain is the current domain, or the target is not current. -/
abbrev DomOK (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ x, σ.kheap t = some (.tcb x) → x.tcbDomain = σ.curDomain ∨ t ≠ σ.curThread

/-- **`possible_switch_to`** of a thread runnable at this state (`DomOK`: its
other-domain enqueue does not add the current thread). -/
theorem sa_possibleSwitchTo_p (t : ObjRef) (σ : State Unit) (hr : RnH t σ.kheap) (hd : DomOK t σ) :
    IKp SA σ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_gets_bind ?_
  refine ikp_when _ fun _ => ?_
  refine ikp_gets_bind ?_
  refine ikp_threadGet_bind fun x' hx' => ?_
  obtain rfl : x = x' := by rw [hx] at hx'; cases hx'; rfl
  refine ikp_gets_bind ?_
  try dsimp only
  split
  · rename_i hne
    exact sa_enq_p _ t σ (q1_enq t) (Or.inr ((hd x hx).resolve_left hne))
  · split
    · intro hσ y ⟨z, hz, hy⟩
      exact (sac_enq _ t (q1_enq t)) z.2 (sa_rescheduleRequired σ hσ z hz) y hy |>.1
    · unfold setSchedulerAction
      intro hσ y hy
      rw [Set.mem_singleton_iff.1 hy]
      refine ⟨fun u hu => ?_, hσ.2.1, fun hs => by cases hs⟩
      cases hu; exact hr

/-- `possible_switch_to` in the pre/post form, both slices. -/
theorem sq_possibleSwitchTo_p (t : ObjRef) (σ : State Unit) (hr : RnH t σ.kheap) (hd : DomOK t σ) :
    IKp SchedQ σ (possibleSwitchTo (Z := Unit) t) :=
  fun hσ y hy => ⟨tq_possibleSwitchTo_p t σ hr hσ.1 y hy, sa_possibleSwitchTo_p t σ hr hd hσ.2 y hy⟩

end

end Fl4Proofs.P3.SInvQ
