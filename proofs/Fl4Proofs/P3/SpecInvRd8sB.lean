/-
P3 (DESIGN.md §9), invariant line G1 (rd8s): **`VE` across `schedule`** (KENTRY-PLAN rd8q
handoff 1(b); spec side only, outside the JAtZ cone).

`switch_to_thread` drops the old current thread `C` from `VB`'s ct exemption. `schedule`
enqueues `C` first when it is schedulable, so before the switch `C`'s clause holds without the
exemption: **`CQ C s`** (schedulable `C` ⇒ queued). It is carried over the domain step and the
arch switch by rdY's heap view `FK` (TCB arch fields erased: schedulability unchanged,
**`sched_hv`**) and the queue / release-queue / action frame **`QRA`**:

* **`PS E C A`** := `VE E ∧ ct = C ∧ CQ C ∧ action = A`, `ht_ps` (any step keeping the four).
* **`ht_switchToThread_cq`** / **`ht_switchToIdleThread_cq`** / **`ht_guardedSwitchTo_cq`** /
  **`ht_chooseThread_cq`**: `PS E C A → VE E` (no ct exemption lost).
* **`ht_scheduleChooseNewThread`** (`PS E C chooseNewThread → VE E`),
  **`ht_scheduleSwitchThreadBranch`** (candidate exempt as the switch target until it is
  enqueued / appended or switched to), **`ve_schedule`**.
-/
import Fl4Proofs.P3.SpecInvRd8sA
open Classical

namespace Fl4Proofs.P3.SInvR.B8s
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

/-! ## The old current thread's clause -/

/-- `C`'s `VB` clause without the ct / switch-target exemptions. -/
def CQ (C : ObjRef) (s : State Unit) : Prop := schedulable C s = true → ∃ d p, C ∈ s.readyQueues d p

/-- Ready queues, release queue and scheduler action fixed. -/
abbrev QRA (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue) (A : SchedulerAction) (s : State Unit) : Prop :=
  s.readyQueues = Q ∧ s.releaseQueue = R ∧ s.schedulerAction = A

theorem qra_archSwitchToThread (t : ObjRef) (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue)
    (A : SchedulerAction) : IK (QRA Q R A) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; repeat' (first | ik_step0 | ik_unfold)

theorem qra_archSwitchToIdleThread (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue)
    (A : SchedulerAction) : IK (QRA Q R A) (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; repeat' (first | ik_step0 | ik_unfold)

theorem qra_archPrepareNextDomain (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue)
    (A : SchedulerAction) : IK (QRA Q R A) (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; repeat' (first | ik_step0 | ik_unfold)

theorem qra_nextDomain (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue)
    (A : SchedulerAction) : IK (QRA Q R A) (nextDomain (Z := Unit)) := by
  unfold nextDomain; repeat' (first | ik_step0 | ik_unfold)

/-- Schedulability through equal heap views and release queues. -/
theorem sched_hv {s s' : State Unit} (hv : ∀ q, HV (s'.kheap q) = HV (s.kheap q))
    (hr : s'.releaseQueue = s.releaseQueue) {u : ObjRef} (h : schedulable u s' = true) :
    schedulable u s = true := by
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv h
  have h1 := hv u
  rw [hx] at h1
  obtain ⟨x', hx', e⟩ := hv_tcb h1.symm
  exact Sched.schedulable_of hx' (by rw [hvT_sc e]; exact hsc) (by rw [hvT_st e]; exact hrn)
    ((hv_sc (hv scp)).1 hy) ha (by rw [← hr]; exact hq)

theorem cq_fr {C : ObjRef} {s s' : State Unit} (h : CQ C s) (hv : ∀ q, HV (s'.kheap q) = HV (s.kheap q))
    (hr : s'.releaseQueue = s.releaseQueue) (hq : s'.readyQueues = s.readyQueues) : CQ C s' := by
  intro hs; rw [hq]; exact h (sched_hv hv hr hs)

/-- `VE`, ct `C`, `C`'s clause, action `A`. -/
def PS (E : ObjRef → Prop) (C : ObjRef) (A : SchedulerAction) (s : State Unit) : Prop :=
  VE E s ∧ s.curThread = C ∧ CQ C s ∧ s.schedulerAction = A

theorem ht_ps {α : Type} {m : NonDet (State Unit) α} (C : ObjRef) (A : SchedulerAction)
    (hv : VEK E m) (hc : SInv.CTK C m) (hf : ∀ K c u T I S, IK (FK K c u T I S) m)
    (hq : ∀ Q R A', IK (QRA Q R A') m) : HT (PS E C A) (PS E C A) m := by
  intro σ ⟨h1, h2, h3, h4⟩ x hx
  have hk := hf σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc σ (fk_self σ) x hx
  have hq' := hq σ.readyQueues σ.releaseQueue σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ x hx
  exact ⟨hv σ h1 x hx, hc σ h2 x hx, cq_fr h3 hk.1 hq'.2.1 hq'.1, hq'.2.2.trans h4⟩

/-! ## The switch -/

/-- **`switch_to_thread t`** from `PS E C A`: `VE E` (the target is ct; `C` queued or not schedulable). -/
theorem ht_switchToThread_cq (t C : ObjRef) (A : SchedulerAction) :
    HT (PS E C A) (fun s => VE E s ∧ s.curThread = t ∧ s.schedulerAction = A) (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  refine ht_bind (ht_ps C A (by ve_auto) (by ct_auto) (fun K c u T I S => fk_archSwitchToThread K c u T I S t)
    (fun Q R A' => qra_archSwitchToThread t Q R A')) fun _ => ?_
  refine ht_bind (R := fun s => VE (Ins E t) s ∧ s.curThread = C ∧ (t = C ∨ CQ C s) ∧ s.schedulerAction = A)
    ?_ fun _ => ?_
  · intro σ ⟨h1, h2, h3, h4⟩ x hx
    refine ⟨ht_dequeue t σ h1 x hx, ?_⟩
    obtain ⟨d, p, e⟩ := tsa_out hx
    rw [e]
    refine ⟨h2, ?_, h4⟩
    by_cases et : t = C
    · exact Or.inl et
    · refine Or.inr fun hs => ?_
      obtain ⟨d', p', hm⟩ := h3 hs
      refine ⟨d', p', ?_⟩
      try dsimp only
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        unfold tcbSchedDequeue
        exact List.mem_filter.2 ⟨hm, decide_eq_true et⟩
      · exact hm
  · intro σ ⟨h1, h2, h3, h4⟩ x hx
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨?_, rfl, h4⟩
    have h5 := ve_setCt h1 h2
    rcases h3 with e | h3
    · subst e; exact ve_drop_ct h5 rfl
    · exact ve_drop h5 fun hs _ _ => h3 hs

theorem ht_switchToIdleThread_cq (C : ObjRef) (A : SchedulerAction) :
    HT (PS E C A) (fun s => VE E s ∧ s.schedulerAction = A) (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  refine ht_bind (ht_ik (by ro_auto)) fun i => ?_
  refine ht_bind (ht_ps C A (by ve_auto) (by ct_auto) (fun K c u T I S => fk_archSwitchToIdleThread K c u T I S)
    (fun Q R A' => qra_archSwitchToIdleThread Q R A')) fun _ => ?_
  intro σ ⟨h1, h2, h3, h4⟩ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨ve_drop (ve_setCt (ve_ins i h1) h2) fun hs _ _ => h3 hs, h4⟩

theorem ht_guardedSwitchTo_cq (t C : ObjRef) (A : SchedulerAction) :
    HT (PS E C A) (fun s => VE E s ∧ s.curThread = t ∧ s.schedulerAction = A) (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  exact ht_switchToThread_cq t C A

theorem ht_chooseThread_cq (C : ObjRef) (A : SchedulerAction) :
    HT (PS E C A) (fun s => VE E s ∧ s.schedulerAction = A) (chooseThread (Z := Unit)) := by
  unfold chooseThread
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  split
  · exact ht_switchToIdleThread_cq C A
  · exact ht_conseq (fun _ h => h) (fun _ h => ⟨h.1, h.2.2⟩) (ht_guardedSwitchTo_cq _ C A)

/-- **`schedule_choose_new_thread`** from `PS E C chooseNewThread`. -/
theorem ht_scheduleChooseNewThread (C : ObjRef) :
    HT (PS E C .chooseNewThread) (VE E) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  refine ht_bind (R := PS E C .chooseNewThread) ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · exact ht_bind (ht_ps C _ (by ve_auto) (by ct_auto)
        (fun K c u T I S => fk_archPrepareNextDomain K c u T I S) (fun Q R A' => qra_archPrepareNextDomain Q R A'))
        fun _ => ht_ps C _ (by ve_auto) (by ct_auto) (fun K c u T I S => fk_nextDomain K c u T I S)
          (fun Q R A' => qra_nextDomain Q R A')
    · exact ht_ik (ik_pure _)
  refine ht_bind (ht_chooseThread_cq C _) fun _ => ?_
  intro σ ⟨h1, h2⟩ x hx
  exact ht_setSchedulerAction _ σ (vea_nsw h1 fun u e => by rw [h2] at e; cases e) x hx

/-! ## The switch-thread branch -/

theorem app_self (t : ObjRef) (q : List ObjRef) : t ∈ tcbSchedAppend t q := by
  by_cases e : t ∈ q <;> simp [tcbSchedAppend, e]

/-- A queue action keeping every queued thread and adding `t`. -/
theorem ht_enq_ps (f : ObjRef → List ObjRef → List ObjRef) (t C : ObjRef) (A : SchedulerAction)
    (hf : ∀ q u, u ∈ q → u ∈ f t q) (hself : ∀ q, t ∈ f t q) :
    HT (PS E C A) (fun s => PS E C A s ∧ ∃ d p, t ∈ s.readyQueues d p) (tcbSchedAction (Z := Unit) f t) := by
  intro σ ⟨h1, h2, h3, h4⟩ x hx
  have hv := ve_tcbSchedAction f t hf σ h1 x hx
  obtain ⟨d, p, e⟩ := tsa_out hx
  rw [e] at hv ⊢
  refine ⟨⟨hv, h2, fun hs => ?_, h4⟩, d, p, ?_⟩
  · obtain ⟨d', p', hm⟩ := h3 hs
    refine ⟨d', p', ?_⟩
    try dsimp only
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hf _ _ hm
    · exact hm
  · try dsimp only
    rw [if_pos ⟨rfl, rfl⟩]; exact hself _

/-- The candidate queued: the action may be reset to `chooseNewThread`. -/
theorem ht_setAction_q (C cand : ObjRef) :
    HT (fun s => PS E C (.switchThread cand) s ∧ ∃ d p, cand ∈ s.readyQueues d p) (PS E C .chooseNewThread)
      (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  intro σ ⟨⟨h1, h2, h3, h4⟩, d, p, hm⟩ x hx
  unfold setSchedulerAction at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨ve_setAction (vea_of h1 fun u e _ _ _ => ?_) _, h2, h3, rfl⟩
  rw [h4] at e
  injection e with e
  subst e
  exact ⟨d, p, hm⟩

/-- **`schedule`'s switch-thread branch** (`b` = the old ct's schedulability). -/
theorem ht_scheduleSwitchThreadBranch (cand C : ObjRef) (b : Bool) :
    HT (fun s => VE E s ∧ s.curThread = C ∧ s.schedulerAction = .switchThread cand ∧
        (b = true ∨ schedulable C s = false))
      (VE E) (scheduleSwitchThreadBranch (Z := Unit) cand C b) := by
  unfold scheduleSwitchThreadBranch
  refine ht_bind (R := PS E C (.switchThread cand)) ?_ fun _ => ?_
  · intro σ ⟨h1, h2, h3, hb⟩ w hw
    unfold NonDet.when at hw
    split at hw
    · obtain ⟨⟨k1, k2, k3⟩, d, p, hm⟩ := ht_enqueue C
        (fun s => VE E s ∧ s.curThread = C ∧ s.schedulerAction = .switchThread cand)
        (fun s r hs hr => ⟨ve_of hs.1 rfl rfl (fun d p u _ h => hr d p u h) (fun _ _ h => h), hs.2.1, hs.2.2⟩)
        σ ⟨h1, h2, h3⟩ w hw
      exact ⟨k1, k2, fun _ => ⟨d, p, hm⟩, k3⟩
    · rename_i hn
      rw [Set.mem_singleton_iff.1 hw]
      refine ⟨h1, h2, fun hs => ?_, h3⟩
      rcases hb with hb | hb
      · exact absurd hb hn
      · rw [hb] at hs; cases hs
  try dsimp only [letFun]
  repeat (refine ht_bind (ht_ik (by ro_auto; done)) fun _ => ?_)
  split <;>
  · repeat (refine ht_bind (ht_ik (by ro_auto; done)) fun _ => ?_)
    try dsimp only
    split
    · refine ht_bind (ht_enq_ps _ cand C _ (enq_mem cand) (enq_self cand)) fun _ => ?_
      exact ht_bind (ht_setAction_q C cand) fun _ => ht_scheduleChooseNewThread C
    · split
      · refine ht_bind (ht_enq_ps _ cand C _ (app_mem cand) (app_self cand)) fun _ => ?_
        exact ht_bind (ht_setAction_q C cand) fun _ => ht_scheduleChooseNewThread C
      · refine ht_bind (ht_guardedSwitchTo_cq cand C _) fun _ => ?_
        intro σ ⟨h1, h2, h3⟩ x hx
        refine ht_setSchedulerAction _ σ (vea_of h1 fun u e _ _ hc => ?_) x hx
        rw [h3] at e
        injection e with e
        subst e
        exact absurd h2.symm hc

/-! ## `schedule` -/

/-- **`schedule` keeps `VE E`.** -/
theorem ve_schedule : VEK E (schedule (Z := Unit)) := by
  unfold schedule
  refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  try dsimp only at hx
  have hsc : VEK E (scAndTimer (Z := Unit)) := by ve_auto
  rcases ha : σ.schedulerAction with _ | cand | _
  · rw [ha] at hx
    try dsimp only at hx
    exact hsc σ hσ x hx
  · rw [ha] at hx
    try dsimp only at hx
    obtain ⟨z, hz, hx⟩ := hx
    exact hsc z.2 (ht_scheduleSwitchThreadBranch cand σ.curThread _ σ
      ⟨hσ, rfl, ha, Bool.eq_false_or_eq_true _⟩ z hz) x hx
  · rw [ha] at hx
    try dsimp only at hx
    obtain ⟨w, hw, hx⟩ := hx
    obtain ⟨z, hz, hx⟩ := hx
    have hP : PS E σ.curThread .chooseNewThread w.2 := by
      unfold NonDet.when at hw
      split at hw
      · obtain ⟨⟨k1, k2, k3⟩, d, p, hm⟩ := ht_enqueue σ.curThread
          (fun s => VE E s ∧ s.curThread = σ.curThread ∧ s.schedulerAction = .chooseNewThread)
          (fun s r hs hr => ⟨ve_of hs.1 rfl rfl (fun d p u _ h => hr d p u h) (fun _ _ h => h), hs.2.1, hs.2.2⟩)
          σ ⟨hσ, rfl, ha⟩ w hw
        exact ⟨k1, k2, fun _ => ⟨d, p, hm⟩, k3⟩
      · rename_i hn
        rw [Set.mem_singleton_iff.1 hw]
        exact ⟨hσ, rfl, fun hs => absurd hs hn, ha⟩
    exact hsc z.2 (ht_scheduleChooseNewThread σ.curThread w.2 hP z hz) x hx

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedule)

end

end Fl4Proofs.P3.SInvR.B8s
