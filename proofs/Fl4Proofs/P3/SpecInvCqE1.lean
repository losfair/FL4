/-
P3 (DESIGN.md §9), invariant line G1 (ctq7): **the event bundle
`EB k := SQ4 ∧ RBk k`** (KENTRY-PLAN ctq6 handoff 1) and its scheduler
leaves (spec side only, outside the JAtZ cone).

* `eb_of`: a function with a TQ, SA, T4 and `RBk k` lemma keeps `EB k`
  (`eb_auto` for the generated families of ctq3 / ctq4 / q4 / ctq6).
* `set_thread_state` of a thread that is neither switch target nor
  released and in no ready queue (`NPQ t`), any state: `eb_setThreadState_p`;
  of the current thread under `EB true` (`NP ct`, `CtQ`):
  **`eb_setThreadState_ct`**; of a thread read non-runnable:
  `eb_setThreadState_nr`.
* `possible_switch_to` of a thread runnable at that state, not current when
  `k`: `eb_possibleSwitchTo_p`, `eb_pst_p` (the `schedulable`-guarded form).
* **`rq_rescheduleRequired : HK1 RDq (RBk false) rescheduleRequired`** (the
  switch target is enqueued after `schedulable` read it; afterwards the
  action is `choose_new_thread`, so `CB` and the resume clause are vacuous),
  `rr_rescheduleRequired : HK1 RR SAc` (the heap and the release queue are
  kept, the action becomes `choose_new_thread`), hence
  **`et_rescheduleRequired : HK1 ET (EB false)`** with `ET := TQ ∧ RR ∧ T4 ∧
  RDq`: what `end_timeslice`'s append / postpone of the current thread
  leaves for `charge_budget`'s following `reschedule_required`.
* `postpone` / `tcb_release_enqueue` for `RDq` alone (`rdq_postpone_p`), and
  `eb_postpone_p` (SA: the bound thread runnable; RB: ctq6's `rb_postpone_p`).
* The blocking leaves: `send_ipc_blocked`, `receive_ipc_blocked`,
  `receive_signal_blocked`, `reply_push` of a thread with `NPQ`.
-/
import Fl4Proofs.P3.SpecInvCqZA
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The bundle -/

/-- **The event bundle** (`k = true`: before any enqueue of the current
thread; `k = false`: what the tail needs). -/
abbrev EB (k : Bool) (s : State Unit) : Prop := SQ4 s ∧ RBk k s

abbrev EBK (k : Bool) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (EB k) m
abbrev EBKE (k : Bool) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (EB k) m

theorem eb_of {k : Bool} {α : Type} {m : NonDet (State Unit) α} (h1 : TQK m) (h2 : SAK m) (h3 : Q4K m)
    (h4 : RBK k m) : EBK k m :=
  fun σ h y hy => ⟨sq4_of h1 h2 h3 σ h.1 y hy, h4 σ h.2 y hy⟩

theorem eb_weak {k : Bool} {s : State Unit} (h : EB k s) : EB false s := ⟨h.1, rbk_weak h.2⟩

macro "eb_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine eb_of ?_ ?_ ?_ ?_); tq_leaf; sa_leaf; q4_leaf; rb_leaf; done)
  | ik_step0 | ik_unfold))

/-- Neither switch target nor released, and in no ready queue. -/
abbrev NPQ (t : ObjRef) (s : State Unit) : Prop := NP t s ∧ NoQ t s.readyQueues

/-- Under `EB true` the current thread has `NPQ`. -/
theorem npq_ct {s : State Unit} (h : EB true s) : NPQ s.curThread s :=
  ⟨(h.2.1.2.1 rfl).2, (h.2.1.2.1 rfl).1⟩

/-- A thread that is not runnable has `NPQ` (SchedQ). -/
theorem npq_nr {s : State Unit} (h : SQ4 s) {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = false) : NPQ t s :=
  ⟨np_of_tcb_nr h.1.2 hx hr, rqd_noQ h.1.1.1 hx hr⟩

/-! ## Thread states -/

theorem eb_setThreadState_p {k : Bool} (t : ObjRef) (ts : ThreadState) (σ : State Unit)
    (h : runnable ts = true ∨ NPQ t σ) : IKp (EB k) σ (setThreadState (Z := Unit) t ts) := by
  intro hσ y hy
  refine ⟨⟨⟨tqx_setThreadState_p t ts σ (h.imp id (·.2)) hσ.1.1.1 y hy,
    sa_setThreadState_p t ts σ (h.imp id (·.1)) hσ.1.1.2 y hy⟩, q4_setThreadState t ts σ hσ.1.2 y hy⟩,
    rb_setThreadState t ts σ hσ.2 y hy⟩

theorem eb_setThreadState_r {k : Bool} (t : ObjRef) (ts : ThreadState) (h : runnable ts = true) :
    EBK k (setThreadState (Z := Unit) t ts) :=
  fun σ => eb_setThreadState_p t ts σ (Or.inl h)

/-- **`set_thread_state` of the current thread, any state**, under `EB true`. -/
theorem eb_setThreadState_ct (ts : ThreadState) (σ : State Unit) :
    IKp (EB true) σ (setThreadState (Z := Unit) σ.curThread ts) :=
  fun hσ => eb_setThreadState_p _ ts σ (Or.inr (npq_ct hσ)) hσ

theorem eb_setThreadState_nr {k : Bool} (t : ObjRef) (ts : ThreadState) (σ : State Unit) (x : Tcb)
    (hx : σ.kheap t = some (.tcb x)) (hr : runnable x.tcbState = false) :
    IKp (EB k) σ (setThreadState (Z := Unit) t ts) :=
  fun hσ => eb_setThreadState_p t ts σ (Or.inr (npq_nr hσ.1 hx hr)) hσ

/-! ## `possible_switch_to` -/

theorem eb_possibleSwitchTo_p {k : Bool} (t : ObjRef) (σ : State Unit) (hr : RnH t σ.kheap)
    (hc : k = true → t ≠ σ.curThread) : IKp (EB k) σ (possibleSwitchTo (Z := Unit) t) :=
  fun hσ y hy => ⟨⟨sq_possibleSwitchTo_p t σ hr (domOK_of_t4 hσ.1.2 t) hσ.1.1 y hy,
    q4_possibleSwitchTo t σ hσ.1.2 y hy⟩, rb_possibleSwitchTo_p t σ hc hσ.2 y hy⟩

/-- `possible_switch_to` of a thread `schedulable` just read. -/
theorem eb_pst_p {k : Bool} {β : Type} (t : ObjRef) (g : Unit → NonDet (State Unit) β) (σ : State Unit)
    (hc : k = true → t ≠ σ.curThread) (hg : ∀ u, EBK k (g u)) :
    IKp (EB k) σ (NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= g) := by
  refine ikp_gets_bind ?_
  refine ikp_bind ?_ hg
  exact ikp_when _ fun hs => eb_possibleSwitchTo_p t σ (schedulable_rn hs) hc

/-! ## `reschedule_required` -/

theorem eb_rescheduleRequired {k : Bool} : EBK k (rescheduleRequired (Z := Unit)) :=
  eb_of tq_rescheduleRequired sa_rescheduleRequired' q4_rescheduleRequired rb_rescheduleRequired

/-- RD and a thread that is not released. -/
abbrev RDe (t : ObjRef) (s : State Unit) : Prop := RDq s ∧ t ∉ s.releaseQueue

theorem rde_enq (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef)
    (hact : ∀ q u, u ∈ act t q → u ∈ q ∨ u = t) : IK (RDe t) (tcbSchedAction (Z := Unit) act t) := by
  intro σ hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  obtain ⟨⟨h1, h2⟩, hr⟩ := hσ
  refine ⟨⟨fun d p u hu => ?_, h2⟩, hr⟩
  dsimp only at hu
  split at hu
  · rcases hact _ _ hu with hu | rfl
    · exact h1 _ _ u hu
    · exact hr
  · exact h1 d p u hu

theorem rq_setCn : HK1 RDq (RBk false) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  intro σ h y hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨⟨⟨h.1, (fun t ht => by cases ht)⟩, (fun hk => by cases hk), (fun e => by cases e)⟩,
    (fun e => by cases e)⟩

/-- **`reschedule_required` from RD alone** (KENTRY-PLAN ctq6 handoff 1(c)):
the switch target is enqueued after `schedulable` read it, so it is not
released; the action ends at `choose_new_thread`. -/
theorem rq_rescheduleRequired : HK1 RDq (RBk false) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  intro σ
  show HKp RDq (RBk false) σ _
  refine hkp_gets_bind ?_
  dsimp only
  split
  · rename_i t ht
    refine hkp_gets_bind ?_
    refine hkp_bind (R := RDq) ?_ fun _ => rq_setCn
    show IKp RDq σ _
    unfold NonDet.when
    split
    · rename_i hs
      refine ikp_strengthen (P' := RDe t) (fun h => ⟨h, ?_⟩) ?_ fun _ h => h.1
      · unfold schedulable at hs
        exact (of_decide_eq_true hs).2.2
      repeat' (first | (with_reducible exact rde_enq _ _ (q1_enq _)) | ik_step0 | ik_unfold)
    · exact fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h
  · first
      | exact rq_setCn σ
      | exact hkp_bind (R := RDq) (fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h) fun _ => rq_setCn

theorem kr_rescheduleRequired (H : ObjRef → Option KernelObject) (R : List ObjRef) :
    IK (fun s => s.kheap = H ∧ s.releaseQueue = R) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction
  repeat' (first | ik_step0 | ik_unfold)

/-- `reschedule_required` from RR alone gives SA (the action ends at
`choose_new_thread`, so RA and CtNQR are vacuous). -/
theorem rr_rescheduleRequired : HK1 RR SAc (rescheduleRequired (Z := Unit)) := by
  intro σ h y hy
  have hc := rescheduleRequired_cn σ y hy
  obtain ⟨e1, e2⟩ := kr_rescheduleRequired σ.kheap σ.releaseQueue σ ⟨rfl, rfl⟩ y hy
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun hr => ?_⟩, hc⟩
  · rw [hc] at ht; cases ht
  · rw [e1]; rw [e2] at ht; exact h t ht
  · rw [hc] at hr; cases hr

/-- What `end_timeslice` (append / postpone of the current thread) leaves. -/
abbrev ET (s : State Unit) : Prop := TQ s ∧ RR s ∧ T4 s ∧ RDq s

theorem et_of_eb {k : Bool} {s : State Unit} (h : EB k s) : ET s :=
  ⟨h.1.1.1, h.1.1.2.2.1, h.1.2, h.2.1.1⟩

/-- **`reschedule_required` after `end_timeslice`** restores the bundle
(weak form). -/
theorem et_rescheduleRequired : HK1 ET (EB false) (rescheduleRequired (Z := Unit)) :=
  fun σ h y hy => ⟨⟨⟨tq_rescheduleRequired σ h.1 y hy, (rr_rescheduleRequired σ h.2.1 y hy).1⟩,
    q4_rescheduleRequired σ h.2.2.1 y hy⟩, rq_rescheduleRequired σ h.2.2.2 y hy⟩

/-! ## The release queue -/

theorem rdq_tcbReleaseEnqueue_p (t : ObjRef) (σ : State Unit) (hq : NoQ t σ.readyQueues)
    (ha : σ.schedulerAction ≠ .switchThread t) : IKp RDq σ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine ikp_gets_bind ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, hm⟩ := cq5_mem_orderedInsert hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hm; subst z2
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨h1, h2⟩ := hσ
  have hS : RDq { σ with releaseQueue := z1 } := by
    refine ⟨fun d p u hu hu' => ?_, fun u hu hu' => ?_⟩
    · rcases hm u hu' with rfl | hu'
      · exact hq d p hu
      · exact h1 d p u hu hu'
    · rcases hm u hu' with rfl | hu'
      · exact ha hu
      · exact h2 u hu hu'
  exact (ik_when _ (ik_modify (P := RDq) (g := fun s => { s with reprogramTimer := true }) fun _ h => h)) _ hS y hy

theorem rdq_dequeue (t : ObjRef) : IK RDq (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  intro σ hσ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]
  obtain ⟨h1, h2⟩ := hσ
  refine ⟨fun d p u hu => ?_, h2⟩
  dsimp only at hu
  split at hu
  · exact h1 _ _ u (List.mem_filter.1 hu).1
  · exact h1 d p u hu

/-- **`postpone`** for RD alone: the bound thread is not the switch target
(TQ: in no ready queue after the dequeue). -/
theorem rdq_postpone_p (sc : ObjRef) (σ : State Unit) (hT : TQ σ)
    (h : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → σ.schedulerAction ≠ .switchThread t) :
    IKp RDq σ (postpone (Z := Unit) sc) := by
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
  have hw1 := rdq_dequeue t σ hσ w hw
  have hnq := (tq_dequeue_noQ t σ hT w hw).2
  obtain ⟨x, -, ew⟩ := q1_tsa_out hw
  have hn := h scv n t hk (hv.symm.trans ha1)
  obtain ⟨v, hv', hy⟩ := hy
  have hv1 := rdq_tcbReleaseEnqueue_p t w.2 hnq (by rw [ew]; exact hn) hw1 v hv'
  exact (ik_modify (P := RDq) (g := fun s => { s with reprogramTimer := true }) fun _ h => h) v.2 hv1 y hy

/-- **`postpone`** for the bundle: the bound thread is runnable (SA), not the
switch target, and not current when `k` or under `resume_cur_thread`. -/
theorem eb_postpone_p {k : Bool} (sc : ObjRef) (σ : State Unit)
    (h : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → RnH t σ.kheap ∧
      ((k = true ∨ σ.schedulerAction = .resumeCurThread) → t ≠ σ.curThread) ∧
      σ.schedulerAction ≠ .switchThread t) :
    IKp (EB k) σ (postpone (Z := Unit) sc) :=
  fun hσ y hy => ⟨⟨⟨tq_postpone sc σ hσ.1.1.1 y hy,
      sa_postpone_p sc σ (fun y' n t hk ht => (h y' n t hk ht).1) hσ.1.1.2 y hy⟩, q4_postpone sc σ hσ.1.2 y hy⟩,
    rb_postpone_p sc σ hσ.1.1.1 (fun y' n t hk ht => (h y' n t hk ht).2) hσ.2 y hy⟩

/-! ## The blocking leaves -/

theorem npq_frame {α : Type} {m : NonDet (State Unit) α} (t : ObjRef)
    (h : ∀ A R Q, IK (fun s => s.schedulerAction = A ∧ s.releaseQueue = R ∧ s.readyQueues = Q) m) :
    IK (NPQ t) m := by
  intro σ hσ y hy
  obtain ⟨e1, e2, e3⟩ := h σ.schedulerAction σ.releaseQueue σ.readyQueues σ ⟨rfl, rfl, rfl⟩ y hy
  exact ⟨⟨by rw [e1]; exact hσ.1.1, by rw [e2]; exact hσ.1.2⟩, by rw [e3]; exact hσ.2⟩

theorem eb_sendIpcBlocked_p {k : Bool} (thread epptr : ObjRef) (badge : Badge) (cg cgr call : Bool)
    (σ : State Unit) (h : NPQ thread σ) :
    IKp (EB k) σ (sendIpcBlocked (Z := Unit) thread epptr badge cg cgr call) := by
  unfold sendIpcBlocked
  refine ikp_bind (eb_setThreadState_p _ _ σ (Or.inr h)) fun _ => ?_
  eb_auto

theorem eb_receiveIpcBlocked_p {k : Bool} (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef)
    (σ : State Unit) (h : NPQ thread σ) :
    IKp (EB k) σ (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked
  split
  · refine ikp_bind (eb_setThreadState_p _ _ σ (Or.inr h)) fun _ => ?_
    eb_auto
  · exact ikp_of_ik (by unfold doNbrecvFailedTransfer; eb_auto) σ

theorem eb_receiveSignalBlocked_p {k : Bool} (thread ntfnptr : ObjRef) (isBlocking : Bool)
    (σ : State Unit) (h : NPQ thread σ) :
    IKp (EB k) σ (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked
  split
  · refine ikp_bind (eb_setThreadState_p _ _ σ (Or.inr h)) fun _ => ?_
    eb_auto
  · exact ikp_of_ik (by unfold doNbrecvFailedTransfer; eb_auto) σ

/-- A bind whose first step keeps `P` and establishes a side fact `Q`. -/
theorem ikp_bind_q {P Q : State Unit → Prop} {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : P σ → ∀ y ∈ (m σ).1, P y.2 ∧ Q y.2)
    (hg : ∀ a s, Q s → IKp P s (g a)) : IKp P σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨h1, h2⟩ := hm hσ y hy
  exact hg y.1 y.2 h2 h1 x hx

theorem eb_replyPush_p {k : Bool} (caller callee replyPtr : ObjRef) (canDonate : Bool)
    (σ : State Unit) (h : NPQ caller σ) :
    IKp (EB k) σ (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_bind_q (Q := NPQ caller) (fun hσ z hz => ⟨?_, ?_⟩) fun _ s hs => ?_
  · exact (show EBK k (setReplyObjRef (Z := Unit) replyTcbUpdate replyPtr (some caller)) by eb_auto) σ hσ z hz
  · exact npq_frame caller (fun A R Q => by repeat' (first | ik_step0 | ik_unfold)) σ h z hz
  refine ikp_bind (eb_setThreadState_p caller _ s (Or.inr hs)) fun _ => ?_
  eb_auto

end

end Fl4Proofs.P3.SInvQ
