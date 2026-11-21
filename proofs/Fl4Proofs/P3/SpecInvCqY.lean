/-
P3 (DESIGN.md §9), invariant line G1 (ctq6): **RD and the current-thread
facts carried with SchedQ** (spec side only, outside the JAtZ cone;
KENTRY-PLAN ctq5 handoff 1-2).

* **`RDq σ`** (ctq5's RD; l4v `valid_ready_qs`' "not in release queue" half
  and `weak_valid_sched_action`'s `not_in_release_q`): no ready-queued thread
  and not the switch target is in the release queue.
* **`CB σ`**: under `resume_cur_thread` the current thread is a runnable TCB
  or the idle thread (l4v `ct_in_state activatable` at `resume_cur_thread`:
  every write making the current thread blocked runs `set_thread_state_act`,
  which leaves `resume_cur_thread`).
* **`RBk k σ := HB k σ ∧ CB σ`**, `HB k σ := RDq σ ∧ (k → CtQ σ ∧ NP ct σ) ∧
  (resume_cur_thread → ct not released)`. `RB := RBk true` is ctq5's event
  bundle `EB` without SchedQ (`EB = SQ4 ∧ RB`): its conditional part `RnH ct
  → CtQ ∧ NP ct` is unconditional given SchedQ (`cn_of_cond`: a non-runnable
  ct is in no queue, not the switch target and not released). `RBk false` is
  what the kernel exit needs from the event's end (after a ct enqueue, or
  across FL4's timer step, which may wake and postpone ct). `RBk` reads the
  heap only through `CB`'s "ct is a runnable TCB"; every lemma is stated for
  both values of `k`.

Leaves, the `rb_auto` driver of the generated family SpecInvCqYF1..F5, and
the scheduler writers by hand: `set_thread_state` (any state: its
`set_thread_state_act` leaves `resume_cur_thread` when ct stops being
schedulable), `reschedule_required` (the switch target is enqueued after
`schedulable` read it: not released; ≠ ct by `NP ct`), `possible_switch_to`
of a thread ≠ ct (it checks `¬ in_release_queue`), `tcb_release_enqueue` /
`postpone` of a thread ≠ ct, not the switch target, in no ready queue after
the dequeue (TQ).
-/
import Fl4Proofs.P3.SpecInvCqX
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **RD** (KENTRY-PLAN ctq5): no ready-queued thread and not the switch
target is in the release queue. -/
abbrev RDq (s : State Unit) : Prop :=
  (∀ d p t, t ∈ s.readyQueues d p → t ∉ s.releaseQueue) ∧
  (∀ t, s.schedulerAction = .switchThread t → t ∉ s.releaseQueue)

/-- Under `resume_cur_thread` the current thread is a runnable TCB or idle. -/
abbrev CB (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread → RnH s.curThread s.kheap ∨ s.curThread = s.idleThread

/-- The heap-blind part. -/
abbrev HB (k : Bool) (s : State Unit) : Prop :=
  RDq s ∧ (k = true → CtQ s ∧ NP s.curThread s) ∧
  (s.schedulerAction = .resumeCurThread → s.curThread ∉ s.releaseQueue)

/-- **The bundle beside SchedQ** (`k = true`: the event's; `k = false`: the exit's need). -/
abbrev RBk (k : Bool) (s : State Unit) : Prop := HB k s ∧ CB s

/-- **The event bundle beside SchedQ** (ctq5's EB = SQ4 ∧ RB). -/
abbrev RB (s : State Unit) : Prop := RBk true s

abbrev RBK (k : Bool) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (RBk k) m
abbrev RBKE (k : Bool) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (RBk k) m

theorem boot_rb (k : Bool) : RBk k (initASt (Z := Unit)) := by
  refine ⟨⟨⟨fun _ _ _ h => by simp [initASt] at h, fun _ h => by simp [initASt] at h⟩,
    fun _ => ⟨fun _ _ h => by simp [initASt] at h, ⟨fun h => by simp [initASt] at h,
      fun h => by simp [initASt] at h⟩⟩, fun _ h => by simp [initASt] at h⟩, fun _ => Or.inr ?_⟩
  simp [initASt]

theorem rbk_weak {k : Bool} {s : State Unit} (h : RBk k s) : RBk false s :=
  ⟨⟨h.1.1, (fun e => by cases e), h.1.2.2⟩, h.2⟩

/-- With SchedQ, ctq5's conditional form gives the unconditional one. -/
theorem cn_of_cond {s : State Unit} (h : SchedQ s)
    (hc : RnH s.curThread s.kheap → CtQ s ∧ NP s.curThread s) : CtQ s ∧ NP s.curThread s := by
  by_cases hr : RnH s.curThread s.kheap
  · exact hc hr
  · refine ⟨fun d p hm => hr ?_, np_of_nr h.2 hr⟩
    obtain ⟨x, hx, -, -, h3⟩ := h.1.1 d p _ hm
    exact ⟨x, hx, h3⟩

/-! ## Frames -/

theorem hb_of_keep {k : Bool} {σ σ' : State Unit} (h : HB k σ)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hq : σ'.readyQueues = σ.readyQueues) (hc : σ'.curThread = σ.curThread) : HB k σ' := by
  obtain ⟨⟨h1, h2⟩, h3, h7⟩ := h
  refine ⟨⟨fun d p t ht => ?_, fun t ht => ?_⟩, fun hk => ?_, fun hs => ?_⟩
  · rw [hr]; rw [hq] at ht; exact h1 d p t ht
  · rw [hr]; rw [ha] at ht; exact h2 t ht
  · obtain ⟨h3, h4, h5⟩ := h3 hk
    refine ⟨fun d p => ?_, ?_, ?_⟩
    · rw [hq, hc]; exact h3 d p
    · rw [ha, hc]; exact h4
    · rw [hr, hc]; exact h5
  · rw [ha] at hs; rw [hr, hc]; exact h7 hs

theorem rb_of_keep {k : Bool} {σ σ' : State Unit} (h : RBk k σ) (hk : ∀ t, RnH t σ.kheap → RnH t σ'.kheap)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hq : σ'.readyQueues = σ.readyQueues) (hc : σ'.curThread = σ.curThread)
    (hi : σ'.idleThread = σ.idleThread) : RBk k σ' := by
  refine ⟨hb_of_keep h.1 ha hr hq hc, fun hs => ?_⟩
  rw [ha] at hs
  rw [hc, hi]
  exact (h.2 hs).imp (hk _) id

/-- `setObject`: a TCB write keeps a runnable TCB runnable. -/
theorem rb_setObject_p {k : Bool} (p : ObjRef) (o : KernelObject) (σ : State Unit)
    (ho : ∀ x y, σ.kheap p = some (.tcb x) → o = .tcb y → runnable x.tcbState = true →
      runnable y.tcbState = true) :
    IKp (RBk k) σ (setObject (Z := Unit) p o) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine rb_of_keep hσ (fun t ht => rnH_upd (fun x0 hx0 hr => ?_) ht) rfl rfl rfl rfl rfl
  rw [hk] at hx0; cases hx0
  obtain ⟨y, rfl⟩ := q1_aType_tcb hty.symm
  exact ⟨y, rfl, ho x0 y hk rfl hr⟩

theorem rb_setObject {k : Bool} (p : ObjRef) (o : KernelObject) (ho : ∀ t, o = .tcb t → False) :
    RBK k (setObject (Z := Unit) p o) :=
  fun σ => rb_setObject_p p o σ fun _ y _ e _ => (ho y e).elim

theorem rb_setTcb_keep {k : Bool} (p : ObjRef) (x : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x)) (y : Tcb)
    (h3 : y.tcbState = x.tcbState) : IKp (RBk k) σ (setObject (Z := Unit) p (.tcb y)) :=
  rb_setObject_p _ _ σ fun x0 y0 hk e hr => by
    rw [hx] at hk; cases hk; cases e; rw [h3]; exact hr

theorem rb_setSimpleKo {k : Bool} {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    RBK k (setSimpleKo (Z := Unit) f p e) := by
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
  refine rb_of_keep hσ (fun t ht => rnH_upd (fun x0 hx0 _ => ?_) ht) rfl rfl rfl rfl rfl
  exfalso
  rw [hk] at hx0; cases hx0
  simp [isSimpleType, aType] at hsimp

theorem rb_threadSet {k : Bool} (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, runnable x.tcbState = true → runnable (f x).tcbState = true) :
    RBK k (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ hx => rb_setObject_p _ _ σ fun x' y hk e hr => by
    rw [getTcb_kheap hx] at hk; cases hk; cases e; exact hf x hr

theorem rb_archThreadSet {k : Bool} (f : ArchTcb → ArchTcb) (t : ObjRef) : RBK k (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => rb_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl

theorem rb_asUser {k : Bool} {α : Type} (t : ObjRef) (u : UserMonad α) : RBK k (asUser (Z := Unit) t u) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (rb_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ik_pure _

theorem rb_setMrs {k : Bool} (t : ObjRef) (b : Option ObjRef) (ms : List Message) : RBK k (setMrs (Z := Unit) t b ms) := by
  unfold setMrs
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_pure_bind ?_
  refine ikp_pure_bind ?_
  refine ikp_bind (rb_setTcb_keep _ x σ (getTcb_kheap hx) _ rfl) fun _ => ?_
  repeat' (first | ik_step0 | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_unfold)

theorem rb_setCap {k : Bool} (c : Cap) (sl : CslotPtr) : RBK k (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  unfold setCap getObject
  refine ik_getsThe_bind fun obj σ hobj => ?_
  have hk : σ.kheap o = some obj := hobj
  split
  · split
    · exact ikp_pure_bind (rb_setObject_p _ _ σ fun _ _ _ e _ => by cases e)
    · exact ikp_fail_bind
  · rename_i tcb
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    split
    · exact ikp_pure_bind (rb_setTcb_keep _ tcb σ hk _ rfl)
    · exact ikp_fail_bind
  · exact ikp_fail_bind

theorem rb_optionUpdateThread {k : Bool} {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState) : RBK k (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact rb_threadSet _ _ fun x hr => by rw [h]; exact hr

/-! ## Ready queues, release queue, action -/

/-- An action removing only (the dequeue). -/
theorem rb_tsa_sub {k : Bool} (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q) : RBK k (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  obtain ⟨⟨⟨h1, h2⟩, h3, h7⟩, h6⟩ := hσ
  refine ⟨⟨⟨fun d p u hu => ?_, h2⟩, fun hk => ⟨fun d p hm => ?_, (h3 hk).2⟩, h7⟩, h6⟩
  · dsimp only at hu
    split at hu
    · exact h1 _ _ u (hact _ _ hu)
    · exact h1 d p u hu
  · dsimp only at hm
    split at hm
    · exact (h3 hk).1 _ _ (hact _ _ hm)
    · exact (h3 hk).1 d p hm

theorem rb_dequeue {k : Bool} (t : ObjRef) : RBK k (tcbSchedAction (Z := Unit) tcbSchedDequeue t) :=
  rb_tsa_sub _ t fun _ _ hu => (List.mem_filter.1 hu).1

/-- `HB k` and a thread that is not released, and not current if `k`. -/
abbrev HBe (k : Bool) (t : ObjRef) (s : State Unit) : Prop :=
  HB k s ∧ t ∉ s.releaseQueue ∧ (k = true → t ≠ s.curThread)

/-- An enqueue / append of such a thread (the heap-blind part). -/
theorem hbe_enq {k : Bool} (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) : IK (HBe k t) (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  obtain ⟨⟨⟨h1, h2⟩, h3, h7⟩, hr, hc⟩ := hσ
  refine ⟨⟨⟨fun d p u hu => ?_, h2⟩, fun hk => ⟨fun d p hm => ?_, (h3 hk).2⟩, h7⟩, hr, hc⟩
  · dsimp only at hu
    split at hu
    · rcases hact _ _ hu with hu | rfl
      · exact h1 _ _ u hu
      · exact hr
    · exact h1 d p u hu
  · dsimp only at hm
    split at hm
    · rcases hact _ _ hm with hm | e'
      · exact (h3 hk).1 _ _ hm
      · exact hc hk e'.symm
    · exact (h3 hk).1 d p hm

/-- `RBk k` and such a thread. -/
abbrev RBe (k : Bool) (t : ObjRef) (s : State Unit) : Prop := HBe k t s ∧ CB s

theorem rbe_enq {k : Bool} (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) : IK (RBe k t) (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  refine ⟨hbe_enq act t hact σ hσ.1 y hy, ?_⟩
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact hσ.2

/-- `choose_new_thread` from the heap-blind part. -/
theorem hb_setCn {k : Bool} : HK1 (HB k) (RBk k) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  intro σ h y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨⟨⟨h.1.1, (fun t ht => by cases ht)⟩, fun hk => ⟨(h.2.1 hk).1, (fun e => by cases e), (h.2.1 hk).2.2⟩,
    (fun e => by cases e)⟩, (fun e => by cases e)⟩

theorem rb_setCn {k : Bool} : RBK k (setSchedulerAction (Z := Unit) .chooseNewThread) :=
  fun σ h => hb_setCn σ h.1

theorem rb_tcbReleaseRemove {k : Bool} (t : ObjRef) : RBK k (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z, hz, hy⟩
  have hz' : RBk k z.2 ∧ z.2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨hσ, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨hσ, rfl⟩
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  rw [Set.mem_singleton_iff.1 hy]
  obtain ⟨⟨⟨⟨h1, h2⟩, h3, h7⟩, h6⟩, e⟩ := hz'
  have hsub : ∀ u, u ∈ tcbSchedDequeue t σ.releaseQueue → u ∈ z.2.releaseQueue := fun u hu => by
    rw [e]; exact (List.mem_filter.1 hu).1
  exact ⟨⟨⟨fun d p u hu hm => h1 d p u hu (hsub u hm), fun u hu hm => h2 u hu (hsub u hm)⟩,
    fun hk => ⟨(h3 hk).1, (h3 hk).2.1, fun hm => (h3 hk).2.2 (hsub _ hm)⟩,
    fun hs hm => h7 hs (hsub _ hm)⟩, h6⟩

/-- **`reschedule_required`** from the heap-blind part: the switch target is
enqueued after `schedulable` read it at the same state (not released), and
it is not current when `k` (`NP ct`); it ends at `choose_new_thread`, so
`CB` holds after. -/
theorem hb_rescheduleRequired {k : Bool} : HK1 (HB k) (RBk k) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  intro σ
  show HKp (HB k) (RBk k) σ _
  refine hkp_gets_bind ?_
  dsimp only
  split
  · rename_i t ht
    refine hkp_gets_bind ?_
    refine hkp_bind (R := HB k) ?_ fun _ => hb_setCn
    show IKp (HB k) σ _
    unfold NonDet.when
    split
    · rename_i hs
      refine ikp_strengthen (P' := HBe k t) (fun h => ⟨h, ?_, ?_⟩) ?_ fun _ h => h.1
      · unfold schedulable at hs
        exact (of_decide_eq_true hs).2.2
      · intro hk e; exact (h.2.1 hk).2.1 (by rw [← e]; exact ht)
      repeat' (first | (with_reducible exact hbe_enq _ _ (q1_enq _)) | ik_step0 | ik_unfold)
    · exact fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h
  · first
      | exact hb_setCn σ
      | exact hkp_bind (R := HB k) (fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h) fun _ => hb_setCn

theorem rb_rescheduleRequired {k : Bool} : RBK k (rescheduleRequired (Z := Unit)) :=
  fun σ h => hb_rescheduleRequired σ h.1

/-! ## Thread states -/

theorem rb_setThreadStateAct {k : Bool} (t : ObjRef) : RBK k (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | (with_reducible exact rb_setCn) | ik_step0 | ik_unfold)

/-- **`set_thread_state`, any state**: when ct stops being schedulable under
`resume_cur_thread`, `set_thread_state_act` leaves `resume_cur_thread`. -/
theorem rb_setThreadState {k : Bool} (t : ObjRef) (ts : ThreadState) : RBK k (setThreadState (Z := Unit) t ts) := by
  intro σ hσ y hy
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  -- the thread write keeps every field `RBk` reads but the heap
  have hf : IK (fun s => s.schedulerAction = σ.schedulerAction ∧ s.releaseQueue = σ.releaseQueue ∧
      s.readyQueues = σ.readyQueues ∧ s.curThread = σ.curThread ∧ s.idleThread = σ.idleThread ∧
      ∀ u, u ≠ t → s.kheap u = σ.kheap u)
      (threadSet (Z := Unit) (fun tcb => { tcb with tcbState := ts }) t) := by
    intro s hs w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    unfold threadSet at hw
    obtain ⟨v, hv, hw⟩ := hw
    unfold NonDet.getsThe at hv
    cases e : getTcb t s with
    | none => rw [e] at hv; exact hv.elim
    | some a =>
      rw [e] at hv
      obtain rfl := Set.mem_singleton_iff.1 hv
      unfold setObject at hw
      obtain ⟨w1, hw1, hw⟩ := hw
      obtain ⟨-, hs1⟩ := mem_getObject hw1
      obtain ⟨w11, w12⟩ := w1
      simp only at hs1; subst hs1
      obtain ⟨z, ⟨-, rfl⟩, hw⟩ := hw
      obtain ⟨v2, hv2, hw⟩ := hw
      rw [Set.mem_singleton_iff.1 hv2] at hw
      rw [Set.mem_singleton_iff.1 hw]
      exact ⟨h1, h2, h3, h4, h5, fun u hu => by
        show Function.update _ t _ u = _; rw [Function.update_of_ne hu]; exact h6 u hu⟩
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hf σ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ z hz
  have hz1 : HB k z.2 := hb_of_keep hσ.1 e1 e2 e3 e4
  unfold setThreadStateAct at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · exact hb_setCn z.2 hz1 y hy
  · rename_i hc
    rw [Set.mem_singleton_iff.1 hy]
    refine ⟨hz1, fun hs => ?_⟩
    by_cases ht : t = z.2.curThread
    · by_cases hsch : schedulable t z.2 = true
      · exact Or.inl (ht ▸ schedulable_rn hsch)
      · exact absurd ⟨ht, hs, hsch⟩ hc
    · rw [e1] at hs
      rcases hσ.2 hs with h | h
      · left
        obtain ⟨x0, hx0, hr0⟩ := h
        refine ⟨x0, ?_, hr0⟩
        rw [e4] at ht ⊢
        rw [e6 _ (Ne.symm ht)]; exact hx0
      · right; rw [e4, e5]; exact h

/-! ## `possible_switch_to`, the release queue -/

theorem rf_rescheduleRequired (R : List ObjRef) (C : ObjRef) :
    IK (fun s => s.releaseQueue = R ∧ s.curThread = C) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold)

/-- **`possible_switch_to`** of a thread that is not current when `k` (it
checks `¬ in_release_queue`; its switch arm runs only under
`resume_cur_thread`). -/
theorem rb_possibleSwitchTo_p {k : Bool} (t : ObjRef) (σ : State Unit) (hc : k = true → t ≠ σ.curThread) :
    IKp (RBk k) σ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_gets_bind ?_
  refine ikp_when _ fun hq => ?_
  have hr : t ∉ σ.releaseQueue := by
    have := hq.2; unfold inReleaseQueue at this; simpa using this
  refine ikp_strengthen (P' := RBe k t) (fun h => ⟨⟨h.1, hr, hc⟩, h.2⟩) ?_ fun _ h => ⟨h.1.1, h.2⟩
  refine ik_gets_bind fun s => ?_
  refine ikp_threadGet_bind fun x' hx' => ?_
  refine ikp_gets_bind ?_
  try dsimp only
  split
  · exact ikp_of_ik (rbe_enq _ t (q1_enq t)) s
  · split
    · refine ikp_of_ik (ik_bind ?_ fun _ => rbe_enq _ t (q1_enq t)) s
      intro s0 h0 y hy
      have e := rf_rescheduleRequired s0.releaseQueue s0.curThread s0 ⟨rfl, rfl⟩ y hy
      have h1 := rb_rescheduleRequired s0 ⟨h0.1.1, h0.2⟩ y hy
      exact ⟨⟨h1.1, by rw [e.1]; exact h0.1.2.1, by rw [e.2]; exact h0.1.2.2⟩, h1.2⟩
    · unfold setSchedulerAction
      intro h y hy
      rw [Set.mem_singleton_iff.1 hy]
      obtain ⟨⟨⟨⟨h1, -⟩, h3, h7⟩, hr', hc'⟩, -⟩ := h
      refine ⟨⟨⟨⟨h1, fun u hu => ?_⟩, fun hk => ⟨(h3 hk).1, fun e => ?_, (h3 hk).2.2⟩,
        (fun e => by cases e)⟩, hr', hc'⟩, (fun e => by cases e)⟩
      · have hu' : SchedulerAction.switchThread t = .switchThread u := hu
        cases hu'; exact hr'
      · have e' : SchedulerAction.switchThread t = .switchThread s.curThread := e
        injection e' with e''; exact hc' hk e''

/-- **`tcb_release_enqueue`** of a thread that is in no ready queue, not the
switch target, and not current when `k` or under `resume_cur_thread`. -/
theorem rb_tcbReleaseEnqueue_p {k : Bool} (t : ObjRef) (σ : State Unit) (hq : NoQ t σ.readyQueues)
    (ha : σ.schedulerAction ≠ .switchThread t)
    (hc : (k = true ∨ σ.schedulerAction = .resumeCurThread) → t ≠ σ.curThread) :
    IKp (RBk k) σ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine ikp_gets_bind ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, hm⟩ := cq5_mem_orderedInsert hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hm; subst z2
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨⟨⟨h1, h2⟩, h3, h7⟩, h6⟩ := hσ
  have hS : RBk k { σ with releaseQueue := z1 } := by
    refine ⟨⟨⟨fun d p u hu hu' => ?_, fun u hu hu' => ?_⟩, fun hk => ⟨(h3 hk).1, (h3 hk).2.1, fun hm' => ?_⟩,
      fun hs hm' => ?_⟩, h6⟩
    · rcases hm u hu' with rfl | hu'
      · exact hq d p hu
      · exact h1 d p u hu hu'
    · rcases hm u hu' with rfl | hu'
      · exact ha hu
      · exact h2 u hu hu'
    · rcases hm _ hm' with e' | hu'
      · exact hc (Or.inl hk) e'.symm
      · exact (h3 hk).2.2 hu'
    · rcases hm _ hm' with e' | hu'
      · exact hc (Or.inr hs) e'.symm
      · exact h7 hs hu'
  exact (ik_when _ (ik_modify (P := RBk k) (g := fun s => { s with reprogramTimer := true }) fun _ h => h)) _ hS y hy

/-- **`postpone`** of an SC whose bound thread is not the switch target, and
not current when `k` or under `resume_cur_thread` (with TQ: after the
dequeue it is in no ready queue). -/
theorem rb_postpone_p {k : Bool} (sc : ObjRef) (σ : State Unit) (hT : TQ σ)
    (h : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t →
      ((k = true ∨ σ.schedulerAction = .resumeCurThread) → t ≠ σ.curThread) ∧
      σ.schedulerAction ≠ .switchThread t) :
    IKp (RBk k) σ (postpone (Z := Unit) sc) := by
  unfold postpone
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, scv, n, hk, hv⟩ := cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  obtain ⟨w, hw, hy⟩ := hy
  have hw1 := rb_dequeue t σ hσ w hw
  have hnq := (tq_dequeue_noQ t σ hT w hw).2
  obtain ⟨x, -, ew⟩ := q1_tsa_out hw
  obtain ⟨hc, hn⟩ := h scv n t hk (hv.symm.trans ha1)
  obtain ⟨v, hv', hy⟩ := hy
  have hv1 := rb_tcbReleaseEnqueue_p t w.2 hnq (by rw [ew]; exact hn) (by rw [ew]; exact hc) hw1 v hv'
  exact (ik_modify (P := RBk k) (g := fun s => { s with reprogramTimer := true }) fun _ h => h) v.2 hv1 y hy

/-! ## `rb_auto` -/

syntax "rb_leaf" : tactic
macro_rules | `(tactic| rb_leaf) => `(tactic| fail "no rb_leaf")

macro "rb_auto" : tactic => `(tactic| repeat' (first | rb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| rb_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); tq_side))
macro_rules | `(tactic| rb_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); tq_side))
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| rb_leaf) => `(tactic| ((with_reducible refine rb_setObject _ _ ?_); tq_side))
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setSimpleKo _ _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| ((with_reducible refine rb_threadSet _ _ ?_); tq_side))
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_archThreadSet _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_asUser _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setMrs _ _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setCap _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_dequeue _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setThreadState _ _)
macro_rules | `(tactic| rb_leaf) => `(tactic| ((with_reducible refine rb_optionUpdateThread _ _ _ ?_); (intro _ _; rfl)))
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setThreadStateAct _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_setCn)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_tcbReleaseRemove _)
macro_rules | `(tactic| rb_leaf) => `(tactic| with_reducible exact rb_rescheduleRequired)

end

end Fl4Proofs.P3.SInvQ
