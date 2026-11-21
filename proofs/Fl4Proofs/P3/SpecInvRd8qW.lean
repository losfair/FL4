/-
P3 (DESIGN.md §9), invariant line G1 (rd8q): **`VE` / `VB` across the scheduler-local writers**
(hand lemmas over SpecInvRd8qA's kit and the generated family SpecInvRd8qF1..F4).

* Release queue: **`ve_tcbReleaseEnqueue`** (the release queue only grows, so nothing becomes
  schedulable), **`ht_tcbReleaseEnqueue_x`** (`t` released, so it leaves the exception set),
  **`ve_tcbReleaseDequeue`** (remove the head, then `possible_switch_to` it), **`ve_postpone`**.
* Thread switch: **`ht_switchToThread`** / **`ht_switchToIdleThread`** (from `VE E` with ct `C`:
  `VE (E ∪ {C})`; the caller — `schedule` — enqueues the old ct when it is schedulable).
* **`ve_setDomain`**, **`ve_setPriority`** (dequeue, write, enqueue when schedulable / runnable).
-/
import Fl4Proofs.P3.SpecInvRd8qF4
open Classical

namespace Fl4Proofs.P3.SInvR.B8q
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

theorem ik_of_ht {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HT P P m) : IK P m := h

/-! ## Release queue -/

/-- `tcb_release_enqueue` writes only the release queue (and `reprogramTimer`). -/
theorem kq_tcbReleaseEnqueue (t : ObjRef) (K : ObjRef → Option KernelObject) (C : ObjRef) (A : SchedulerAction)
    (Q : Domain → Priority → ReadyQueue) :
    IK (fun s : State Unit => s.kheap = K ∧ s.curThread = C ∧ s.schedulerAction = A ∧ s.readyQueues = Q)
      (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend orderedInsert
  repeat' (first | ik_step0 | ik_unfold)

/-- `ordered_insert t` inserts `t`. -/
theorem oi_self {α β : Type} [Nonempty β] {t : α} {ts : List α} {f : α → RMonad Unit β}
    {R : β → β → Prop} {σ : State Unit} {y : List α × State Unit}
    (hy : y ∈ (orderedInsert (Z := Unit) t ts f R σ).1) : t ∈ y.1 := by
  unfold orderedInsert at hy
  obtain ⟨y1, -, hy⟩ := hy
  obtain ⟨y2, -, hy⟩ := hy
  obtain ⟨y3, hy3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy3] at hy
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy4] at hy
  rw [Set.mem_singleton_iff.1 hy]
  simp

theorem relq_self (t : ObjRef) (σ : State Unit) (y : Unit × State Unit)
    (hy : y ∈ (tcbReleaseEnqueue (Z := Unit) t σ).1) : t ∈ y.2.releaseQueue := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz0
  obtain ⟨z, hz, hy⟩ := hy
  have hm := oi_self hz
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  unfold NonDet.when at hy
  split_ifs at hy <;> rw [Set.mem_singleton_iff.1 hy] <;> exact hm

theorem ve_tcbReleaseEnqueue (t : ObjRef) : VEK E (tcbReleaseEnqueue (Z := Unit) t) := by
  intro σ hσ y hy
  obtain ⟨ek, ec, ea, eq⟩ := kq_tcbReleaseEnqueue t σ.kheap σ.curThread σ.schedulerAction σ.readyQueues σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  have hr := A9.rqs_tcbReleaseEnqueue t σ.releaseQueue σ (fun _ h => h) y hy
  exact ve_of hσ ec ea (fun d p u _ hu => by rw [eq]; exact hu) (fun u _ hs => sched_relq ek (hr u) hs)

/-- Releasing `t` takes it out of the exception set (it is no longer schedulable). -/
theorem ht_tcbReleaseEnqueue_x (t : ObjRef) : HT (VE (Ins E t)) (VE E) (tcbReleaseEnqueue (Z := Unit) t) := by
  intro σ hσ y hy
  obtain ⟨ek, ec, ea, eq⟩ := kq_tcbReleaseEnqueue t σ.kheap σ.curThread σ.schedulerAction σ.readyQueues σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  have hr := A9.rqs_tcbReleaseEnqueue t σ.releaseQueue σ (fun _ h => h) y hy
  have ht := relq_self t σ y hy
  refine ve_drop (ve_of hσ ec ea (fun d p u _ hu => by rw [eq]; exact hu) (fun u _ hs => sched_relq ek (hr u) hs))
    fun hs => ?_
  obtain ⟨-, -, -, -, -, -, -, -, -, hq⟩ := Sched.schedulable_inv hs
  exact absurd ht hq

theorem ve_tcbReleaseDequeue : VEK E (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue
  refine ik_bind (by ve_auto) fun rq => ik_bind (by ve_auto) fun _ => ik_of_ht ?_
  exact ht_bind (ht_tcbReleaseRemove _) fun _ => ht_possibleSwitchTo _

theorem ve_postpone (p : ObjRef) : VEK E (postpone (Z := Unit) p) := by
  unfold postpone
  refine ik_bind (by ve_auto) fun o => ik_bind (by ve_auto) fun t => ik_of_ht ?_
  refine ht_bind (ht_dequeue t) fun _ => ht_bind (ht_tcbReleaseEnqueue_x t) fun _ => ht_ik ?_
  ve_auto

/-! ## Thread switch -/

theorem ct_archSwitchToThread (t C : ObjRef) :
    IK (fun s : State Unit => s.curThread = C) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; repeat' (first | ik_step0 | ik_unfold)

theorem ct_archSwitchToIdleThread (C : ObjRef) :
    IK (fun s : State Unit => s.curThread = C) (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; repeat' (first | ik_step0 | ik_unfold)

/-- The final `cur_thread := t` of a switch: the old ct `C` joins the exception set. -/
theorem ve_setCt {σ : State Unit} {C t : ObjRef} (h : VE (Ins E t) σ) (hc : σ.curThread = C) :
    VE (Ins E C) { σ with curThread := t } := by
  intro u hu hs hct ha
  exact h u (fun e => e.elim (fun e => hu (Or.inl e)) (fun e => hct e)) hs
    (fun e => hu (Or.inr (e.trans hc))) ha

theorem ht_dequeue_c (t C : ObjRef) :
    HT (fun s => VE E s ∧ s.curThread = C) (fun s => VE (Ins E t) s ∧ s.curThread = C)
      (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  intro σ ⟨h, hc⟩ x hx
  refine ⟨ht_dequeue t σ h x hx, ?_⟩
  obtain ⟨d, p, e⟩ := tsa_out hx
  rw [e]; exact hc

/-- **`switch_to_thread t`** from `VE E` with ct `C`: `VE (E ∪ {C})` (`t` is ct afterwards). -/
theorem ht_switchToThread (t C : ObjRef) :
    HT (fun s => VE E s ∧ s.curThread = C) (VE (Ins E C)) (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  refine ht_bind (ht_ik (by ik_step0)) fun _ => ht_bind (ht_ik (by ik_step0)) fun _ => ?_
  refine ht_bind (ht_ik (ik_and (by ve_auto) (ct_archSwitchToThread t C))) fun _ => ?_
  refine ht_bind (ht_dequeue_c t C) fun _ => ?_
  intro σ ⟨h, hc⟩ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_setCt h hc

/-- **`switch_to_idle_thread`** from `VE E` with ct `C`: `VE (E ∪ {C})`. -/
theorem ht_switchToIdleThread (C : ObjRef) :
    HT (fun s => VE E s ∧ s.curThread = C) (VE (Ins E C)) (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  refine ht_bind (ht_ik (by ik_step0)) fun i => ?_
  refine ht_bind (ht_ik (ik_and (by ve_auto) (ct_archSwitchToIdleThread C))) fun _ => ?_
  intro σ ⟨h, hc⟩ x hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ve_setCt (ve_ins i h) hc

/-! ## Domain and priority -/

theorem ve_when_rr (c : Prop) {_ : Decidable c} : VEK E (NonDet.when c (rescheduleRequired (Z := Unit))) := by
  unfold NonDet.when
  split
  · exact ve_rescheduleRequired
  · exact ik_pure _

theorem ve_setDomain (t : ObjRef) (d : Domain) : VEK E (setDomain (Z := Unit) t d) := by
  unfold setDomain threadSetDomain
  refine ik_bind (by ve_auto) fun cur => ik_of_ht ?_
  refine ht_bind (ht_dequeue t) fun _ => ?_
  refine ht_bind (ht_ik (ve_threadSet _ t fun x => ⟨rfl, Or.inl rfl⟩)) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  obtain ⟨z, hz, hx⟩ := hx
  have hz' : VE E z.2 := by
    unfold NonDet.when at hz
    split at hz
    · exact ht_enqueue_x t σ hσ z hz
    · rename_i hn
      rw [Set.mem_singleton_iff.1 hz]
      exact ve_drop hσ fun hs => absurd hs hn
  exact ve_when_rr _ z.2 hz' x hx

theorem ve_setPriority (t : ObjRef) (p : Priority) : VEK E (setPriority (Z := Unit) t p) := by
  unfold setPriority threadSetPriority
  refine ik_bind (by ve_auto) fun ts => ?_
  split
  · refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ =>
      ik_bind (by ve_auto) fun _ => ?_
    split
    · exact ik_of_ht (ht_bind (ht_dequeue t) fun _ =>
        ht_bind (ht_ik (ve_threadSet _ t fun x => ⟨rfl, Or.inl rfl⟩)) fun _ =>
        ht_bind (ht_enqueue_x t) fun _ => ht_ik ve_rescheduleRequired)
    · exact ve_threadSet _ t fun x => ⟨rfl, Or.inl rfl⟩
  · ve_auto

end

end Fl4Proofs.P3.SInvR.B8q
