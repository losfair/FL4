/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd3): **`Rdy` across the
release queue and `awaken`** (spec side only, outside the `JAtZ` cone;
KENTRY-PLAN rd2 handoff 1, lead decision (b) of rd3).

* `R4` (l4v `valid_release_q`, `active_sc_tcb_at` half) is `Rdy`'s fifth
  conjunct (SpecInvRdA). Its writers: the release enqueue (`postpone`) and the
  binding / activity writers (unbind, `sched_context_set_inactive`), which
  dequeue first.
* **`rd_tcbReleaseEnqueue_p`** (the enqueued thread `ActB` at that state),
  **`rd_postpone_p`** (the SC's thread `ActB`; `actB_of_fwd` from sb2's
  `ScFwd` and an active SC), **`rd_schedContextResume`** (no premise: it
  postpones only a thread it read `schedulable`, which is `ActB`).
* **`rd_tcbReleaseDequeue_p`** / **`rd_awaken`**: the loop guard reads the
  head's SC ready; `R4` gives that SC active (and sb2's `RNE` its refills
  non-empty, so the read is defined): the released head is `RdyT`, so
  `possible_switch_to` keeps `Rdy`. Premise of `rd_awaken`: `RNE` at its
  start (sb2's carried `ScInv`; `awaken` writes no object).
* `CtR σ` (ct `ActB` and not released ⇒ `RdyT`): kept by `awaken` (a released
  ct is `RdyT` at its release) and `check_domain_time`; with it, `schedule`'s
  ct enqueue (`schedulable ct`) adds an `RdyT` thread.
-/
import Fl4Proofs.P3.SpecInvRdD
import Fl4Proofs.P3.SpecInvCqV
import Fl4Proofs.P3.ScAwaken
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Small frames -/

theorem actB_congr {σ σ' : State Unit} {t : ObjRef} (hk : σ'.kheap = σ.kheap) (h : ActB σ t) : ActB σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha⟩ := h
  exact ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, ha⟩

theorem actB_of_fwd {σ : State Unit} (hF : SInvB.ScFwd σ) {p : ObjRef} {y : SchedContext} {n : Nat} {t : ObjRef}
    (hk : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true) (ht : y.scTcb = some t) : ActB σ t := by
  obtain ⟨x, hx, hc⟩ := hF p y n t hk ht
  exact ⟨x, p, y, n, hx, hc, hk, ha⟩

theorem actB_of_schedulable {σ : State Unit} {t : ObjRef} (h : schedulable t σ = true) : ActB σ t := by
  obtain ⟨x, scp, y, n, hx, hsc, -, hy, ha, -⟩ := Sched.schedulable_inv h
  exact ⟨x, scp, y, n, hx, hsc, hy, ha⟩

/-- A new release queue whose members were released or are `ActB`. -/
theorem rdy_relq {σ : State Unit} (h : Rdy σ) (L : List ObjRef)
    (hL : ∀ u, u ∈ L → u ∈ σ.releaseQueue ∨ ActB σ u) : Rdy { σ with releaseQueue := L } :=
  rdy_of_view h (fun t x hx => ⟨x, hx, rfl⟩) (fun t x hx hb _ => ⟨x, hx, rfl, hb⟩) (fun _ => rfl) rfl rfl
    (fun d p t hm => Or.inl hm) (fun t e => Or.inl e) hL

theorem rdy_rpt {σ : State Unit} (h : Rdy σ) (b : Bool) : Rdy { σ with reprogramTimer := b } :=
  rdy_congr h rfl rfl rfl rfl rfl fun _ h => h

/-! ## The release enqueue -/

/-- **`tcb_release_enqueue`** of a thread `ActB` at this state. -/
theorem rd_tcbReleaseEnqueue_p (t : ObjRef) (σ : State Unit) (hA : ActB σ t) :
    IKp Rdy σ (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine ikp_gets_bind ?_
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, hm⟩ := cq5_mem_orderedInsert hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hm; subst z2
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  have hS : Rdy { σ with releaseQueue := z1 } :=
    rdy_relq hσ z1 fun u hu => (hm u hu).elim (fun h => Or.inr (h ▸ hA)) Or.inl
  exact (ik_when _ (ik_modify (P := Rdy) (g := fun s => { s with reprogramTimer := true })
    fun _ h => rdy_rpt h true)) _ hS y hy

/-- **`postpone`** of an SC whose thread is `ActB` at this state. -/
theorem rd_postpone_p (sc : ObjRef) (σ : State Unit)
    (h : ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t → ActB σ t) :
    IKp Rdy σ (postpone (Z := Unit) sc) := by
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
  have hw1 := rd_dequeue t σ hσ w hw
  obtain ⟨x, -, ew⟩ := q1_tsa_out hw
  obtain ⟨v, hv', hy⟩ := hy
  have hA : ActB w.2 t := actB_congr (by rw [ew]) (h scv n t hk (hv.symm.trans ha1))
  have hv1 := rd_tcbReleaseEnqueue_p t w.2 hA hw1 v hv'
  exact (ik_modify (P := Rdy) (g := fun s => { s with reprogramTimer := true }) fun _ h => rdy_rpt h true)
    v.2 hv1 y hy

/-- **`postpone`** of an active SC (sb2's `ScFwd`: its thread is bound to it). -/
theorem rd_postpone_fwd (sc : ObjRef) (σ : State Unit) (hF : SInvB.ScFwd σ)
    (ha : ∀ y n, σ.kheap sc = some (.schedContext y n) → scActive y = true) :
    IKp Rdy σ (postpone (Z := Unit) sc) :=
  rd_postpone_p sc σ fun y n t hk ht => actB_of_fwd hF hk (ha y n hk) ht

/-- **`sched_context_resume`**: it postpones only a thread it read
`schedulable` at the same state (no premise). -/
theorem rd_schedContextResume (sc : ObjRef) : RdK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  revert hy
  refine ikp_gets_bind ?_ hσ y
  refine ikp_when _ fun hsch => ?_
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_when _ fun hc => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  refine rd_postpone_p sc σ fun y n' t' hk' ht' => ?_
  rw [hk] at hk'; cases hk'
  rw [ha1] at ht'; cases ht'
  exact actB_of_schedulable hsch
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_schedContextResume _)

/-! ## `awaken` -/

theorem kt_tcbReleaseRemove (K : ObjRef → Option KernelObject) (T : Time) (t : ObjRef) :
    IK (KT K T) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove
  repeat' (first | ik_step0 | ik_unfold)

theorem kt_possibleSwitchTo (K : ObjRef → Option KernelObject) (T : Time) (t : ObjRef) :
    IK (KT K T) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo
  repeat' (first | (with_reducible exact kt_rescheduleRequired _ _) | ik_step0 | ik_unfold)

theorem kt_tcbReleaseDequeue (K : ObjRef → Option KernelObject) (T : Time) :
    IK (KT K T) (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue
  repeat' (first | (with_reducible exact kt_tcbReleaseRemove _ _ _) | (with_reducible exact kt_possibleSwitchTo _ _ _) | ik_step0 | ik_unfold)

/-- The release queue's head, when the loop guard reads it ready, is `RdyT`. -/
theorem rdyT_relHead {σ : State Unit} (hσ : Rdy σ) (hR : SInvB.RNE σ)
    (hc : the (readReleaseQNonEmptyAndReady (Z := Unit) σ) = true) :
    ∃ h rest, σ.releaseQueue = h :: rest ∧ RdyT σ h := by
  cases hq : σ.releaseQueue with
  | nil => rw [Sched.readRQ_nil hq, Sched.the_some] at hc; cases hc
  | cons h rest =>
    obtain ⟨x, c, y, n, hx, hcs, hy, ha⟩ := hσ.2.2.2.2.1 h (by rw [hq]; exact List.mem_cons_self ..)
    have hne : y.scRefills ≠ [] := hR c y n hy (Or.inr ha)
    rw [Sched.readRQ_cons hq hx hcs hy hne, Sched.the_some] at hc
    exact ⟨h, rest, rfl, x, c, y, n, hx, hcs, hy, ha, hc⟩

/-- **One round of `awaken`** (module docstring). -/
theorem rd_tcbReleaseDequeue_p (σ : State Unit) (hR : SInvB.RNE σ)
    (hc : the (readReleaseQNonEmptyAndReady (Z := Unit) σ) = true) :
    IKp Rdy σ (tcbReleaseDequeue (Z := Unit)) := by
  intro hσ
  obtain ⟨h, rest, hq, hT⟩ := rdyT_relHead hσ hR hc
  revert hσ
  unfold tcbReleaseDequeue
  refine ikp_gets_bind ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  intro hσ r ⟨z, hz, hr⟩
  rw [hq] at hz hr
  simp only [List.head?_cons, Sched.the_some] at hz hr
  have hz1 := rd_tcbReleaseRemove h σ hσ z hz
  obtain ⟨e1, e2⟩ := kt_tcbReleaseRemove σ.kheap σ.curTime h σ ⟨rfl, rfl⟩ z hz
  exact rd_possibleSwitchTo_p h z.2 (rdyT_kt hT e1 e2) hz1 r hr

/-- **`awaken`** keeps `Rdy` (sb2's `RNE` at its start; `awaken` writes no object). -/
theorem rd_awaken (σ : State Unit) (hR : SInvB.RNE σ) : IKp Rdy σ (awaken (Z := Unit)) := by
  intro hσ r hr
  unfold awaken at hr
  refine (wl_inv (fun s => Rdy s ∧ SInvB.RNE s) (fun a s hs hc y hy => ?_) ⟨hσ, hR⟩ hr).1
  have hk := (kt_tcbReleaseDequeue s.kheap s.curTime s ⟨rfl, rfl⟩ y hy).1
  exact ⟨rd_tcbReleaseDequeue_p s hs.2 hc hs.1 y hy, fun p z n hz => hs.2 p z n (hk ▸ hz)⟩

end

end Fl4Proofs.P3.SInvR
