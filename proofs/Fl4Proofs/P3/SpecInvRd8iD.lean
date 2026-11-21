/-
P3 (DESIGN.md §9), invariant line G1 (rd8i): **`Sched.BlockedScActive`
across the budget checks** (spec side only, outside the JAtZ cone): every
caller of `charge_budget` reads the state only before it, so sb2's `ScInv` at
its start is all `ba_chargeBudget_p` needs.

* **`ba_checkBudget_p`**, **`ba_checkBudgetRestart_p`**,
  **`ba_handleYield_p`**, **`ba_preemptionPath_p`** (each `hI : ScInv σ`).
-/
import Fl4Proofs.P3.SpecInvRd8iG
open Classical

namespace Fl4Proofs.P3.SInvR.B8i
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8g

noncomputable section

set_option maxHeartbeats 1000000

theorem ba_checkBudget_p (σ : State Unit) (hI : SInvB.ScInv σ) : IKp BSA σ (checkBudget (Z := Unit)) := by
  unfold checkBudget
  refine ikp_gets_bind ?_
  refine ikp_gets_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun suff => ?_
  split
  · exact ikp_of_ik (by ba_auto) σ
  · refine ikp_gets_bind ?_
    exact ikp_bind (ba_chargeBudget_p _ _ σ hI) fun _ => ik_pure _

theorem ba_checkBudgetRestart_p (σ : State Unit) (hI : SInvB.ScInv σ) :
    IKp BSA σ (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  exact ikp_bind (ba_checkBudget_p σ hI) fun _ => by ba_auto

theorem ba_handleYield_p (σ : State Unit) (hI : SInvB.ScInv σ) : IKp BSA σ (handleYield (Z := Unit)) := by
  unfold handleYield
  refine ikp_gets_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun sc => ?_
  refine ikp_gets_bind ?_
  refine ikp_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) fun head => ?_
  exact ikp_bind (ba_chargeBudget_p _ _ σ hI) fun _ => by ba_auto

theorem ba_preemptionPath_p (σ : State Unit) (hI : SInvB.ScInv σ) : IKp BSA σ (preemptionPath (Z := Unit)) := by
  unfold preemptionPath
  refine ikp_gets_bind ?_
  refine ikp_gets_bind ?_
  intro hσ y hy
  dsimp only at hy
  split at hy
  · obtain ⟨z1, h1, hy⟩ := hy
    have b1 := ba_checkBudget_p σ hI hσ z1 h1
    exact (by (try dsimp only); ba_auto : BAK _) z1.2 b1 y hy
  · obtain ⟨⟨csc, s1⟩, h1, hy⟩ := hy
    have e1 : s1 = σ := (Prod.mk.inj (Set.mem_singleton_iff.1 h1)).2
    subst s1
    obtain ⟨⟨act, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
    subst s2
    dsimp only at hy
    split at hy
    · obtain ⟨⟨c, s3⟩, h3, hy⟩ := hy
      have e3 : s3 = σ := (Prod.mk.inj (Set.mem_singleton_iff.1 h3)).2
      subst s3
      obtain ⟨z4, h4, hy⟩ := hy
      have b4 := ba_chargeBudget_p _ _ σ hI hσ z4 h4
      exact (by (try dsimp only); ba_auto : BAK _) z4.2 b4 y hy
    · obtain ⟨z4, h4, hy⟩ := hy
      have b4 : BSA z4.2 := by rw [Set.mem_singleton_iff.1 h4]; exact bsa_kh hσ rfl
      exact (by (try dsimp only); ba_auto : BAK _) z4.2 b4 y hy

end

end Fl4Proofs.P3.SInvR.B8i
