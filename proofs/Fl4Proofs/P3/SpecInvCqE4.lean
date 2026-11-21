/-
P3 (DESIGN.md §9), invariant line G1 (ctq7): **`end_timeslice` and
`charge_budget`'s tail** (spec side only, outside the JAtZ cone;
KENTRY-PLAN ctq6 handoff 1(c), ctq7).

* **`et_endTimeslice_p : HKp (EB true) ET σ (end_timeslice cto)`** at a
  state where the current thread is a runnable TCB (`charge_budget` read
  `schedulable ct`), the current SC is bound to the current thread only
  (`hB`: CurScT + sb2's ScSym) and nq3's `NQ K` holds with the current
  thread in `K`. Arms: the timeout fault of the current thread
  (`eb_handleTimeout_p`, it may block), the append of the current thread
  (TQ: runnable; RD: not released, `NP ct`; CtNQR is broken under
  `resume_cur_thread` until the reschedule), `postpone cur_sc` (SA: the bound
  thread is the current, runnable one; RD: `rdq_postpone_p`, not the switch
  target by `NP ct`).
* **`eb_chargeTail_p`**: `charge_budget`'s `when (schedulable ct)` tail
  (`end_timeslice`, `reschedule_required`, the reprogram flag) takes `EB
  true` to `EB false` (`et_rescheduleRequired`).
-/
import Fl4Proofs.P3.SpecInvCqE3
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem hkp_keep {P Q : State Unit → Prop} {α β : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : ∀ y, y ∈ (m σ).1 → y.2 = σ) (hg : ∀ a, HKp P Q σ (g a)) :
    HKp P Q σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  have e := hm y hy
  obtain ⟨y1, y2⟩ := y
  simp only at e; subst e
  exact hg y1 hσ x hx

/-- **`end_timeslice`** from `EB true` (see the module docstring). -/
theorem et_endTimeslice_p {K : List ObjRef} (cto : Bool) (σ : State Unit) (hR : RnH σ.curThread σ.kheap)
    (hB : ∀ y n t, σ.kheap σ.curSc = some (.schedContext y n) → y.scTcb = some t → t = σ.curThread)
    (hN : NQ K σ) (hc : σ.curThread ∈ K) :
    HKp (EB true) ET σ (endTimeslice (Z := Unit) cto) := by
  unfold endTimeslice
  refine hkp_gets_bind ?_
  refine hkp_keep (fun y hy => cq5_ro (fun _ => by unfold isRoundRobin; repeat' (first | ik_step0 | ik_unfold)) hy) fun rr => ?_
  refine hkp_gets_bind ?_
  refine hkp_keep (fun y hy => by obtain ⟨_, -, rfl⟩ := q1_mem_threadGet hy; rfl) fun ts => ?_
  dsimp only
  split
  all_goals refine hkp_keep (fun y hy => ?_) fun valid => ?_
  all_goals first
    | (rw [Set.mem_singleton_iff.1 hy]; done)
    | (exact cq5_ro (fun _ => by unfold isValidTimeoutHandler; repeat' (first | ik_step0 | ik_unfold)) hy)
    | skip
  all_goals
    split
    · refine hkp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun sc => ?_
      intro h y hy
      exact et_of_eb (eb_handleTimeout_p _ _ σ (npq_ct h) hN hc h y hy)
    · refine hkp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
      refine hkp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
      split
      · intro h y hy
        obtain ⟨x, -, e⟩ := q1_tsa_out hy
        refine ⟨tq_enq_p _ _ σ (q1_app _) hR h.1.1.1 y hy, ?_, q4_tcbSchedAction _ _ σ h.1.2 y hy,
          (rde_enq _ _ (q1_app _) σ ⟨h.2.1.1, (npq_ct h).1.2⟩ y hy).1⟩
        rw [e]; exact h.1.1.2.2.1
      · intro h y hy
        refine ⟨tq_postpone _ σ h.1.1.1 y hy,
          (sa_postpone_p _ σ (fun y' n t hk ht => by rw [hB y' n t hk ht]; exact hR) h.1.1.2 y hy).2.1,
          q4_postpone _ σ h.1.2 y hy,
          rdq_postpone_p _ σ h.1.1.1 (fun y' n t hk ht => by rw [hB y' n t hk ht]; exact (npq_ct h).1.1) h.2.1.1 y hy⟩

/-- **`charge_budget`'s tail** (`when (schedulable ct)`): `EB true` to `EB false`. -/
theorem eb_chargeTail_p {K : List ObjRef} (cto : Bool) (σ : State Unit)
    (hB : ∀ y n t, σ.kheap σ.curSc = some (.schedContext y n) → y.scTcb = some t → t = σ.curThread)
    (hN : NQ K σ) (hc : σ.curThread ∈ K) :
    HKp (EB true) (EB false) σ (NonDet.when (schedulable (Z := Unit) σ.curThread σ = true) (do
      endTimeslice (Z := Unit) cto
      rescheduleRequired (Z := Unit)
      NonDet.modify fun s : State Unit => { s with reprogramTimer := true })) := by
  refine hkp_when _ (fun hs => ?_) fun _ h => eb_weak h
  intro h y ⟨z, hz, hy⟩
  have h1 := et_endTimeslice_p cto σ (schedulable_rn hs) hB hN hc h z hz
  obtain ⟨w, hw, hy⟩ := hy
  have h2 := et_rescheduleRequired z.2 h1 w hw
  rw [Set.mem_singleton_iff.1 hy]
  exact h2

end

end Fl4Proofs.P3.SInvQ
