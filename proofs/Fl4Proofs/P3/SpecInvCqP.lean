/-
P3 (DESIGN.md §9), invariant line G1 (ctq3): **T1 across `perform_invocation`
for every invocation** (spec side only, outside the JAtZ cone).

From `PQ i`: `NQ [] ∧ TQ` (nq2's EpQB / NtfnQB and TQ = T1 + "queued ⇒
runnable"), nq3's decode facts `NqDec` (proved at the perform by nq3's
`nqDecW`), ut4's `UtInv''` and `IfLiveTN` (nq3's IfLiveT statement):
* ThreadControlSched with a priority: `install_tcb_cap` keeps `NQ [] ∧ TQ`
  (SpecInvCqJ), `set_mcpriority` too, and `set_priority` keeps TQ
  (`tq_setPriority`: no premise once "queued ⇒ runnable" is carried); the SC
  part keeps T1 (ctq2's family).
* Untyped (no reset / reset) and MakePool: `tq_invokeUntyped` / `tq_makePool`
  with `rqDet_of_live` (SpecInvCqU).
* Every other invocation: ctq2's T1 family.
-/
import Fl4Proofs.P3.SpecInvCqU
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The perform's precondition. -/
def PQ (i : Fl4Invocation) (σ : State Unit) : Prop :=
  JQ [] σ ∧ NqDec σ i ∧ SInvU.UtInv'' σ ∧ IfLiveTN σ

theorem pq_t1 {i : Fl4Invocation} {σ : State Unit} (h : PQ i σ) : T1 σ := tq_t1 h.1.2.1

set_option maxHeartbeats 4000000 in
/-- **T1 across `perform_invocation`, every invocation.** -/
theorem q3_fl4PerformInvocation (bl call don : Bool) (i : Fl4Invocation) :
    HKE (PQ i) T1 (fl4PerformInvocation (Z := Unit) bl call don i) := by
  cases i
  case invokeUntyped ui =>
    intro σ hσ y hy
    simp only [fl4PerformInvocation] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := tq_invokeUntyped ui σ hσ.2.2.1.1.1 (hσ.2.1.1 ui rfl)
      (fun _ _ _ _ _ hc hk => rqDet_of_live hσ.2.2.1 hσ.2.2.2 hσ.1.2.1 hc hk) hσ.1.2 z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact tq_t1 hbz.1)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact tq_t1 hbz.1)
    | ok u =>
      try dsimp only at hy
      obtain rfl := Set.mem_singleton_iff.1 hy; exact tq_t1 hbz.1
  case invokeTCB ti =>
    cases ti
    case threadControlSched target slot fh mcp prio sc =>
      cases prio with
      | none =>
        refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
        simp only [fl4PerformInvocation, invokeTcb, NonDet.maybeM]
        q1_auto
      | some p =>
        obtain ⟨p1, p2⟩ := p
        simp only [fl4PerformInvocation, invokeTcb, NonDet.maybeM]
        refine hke_bind (R := JQ []) (hk_pre (hk_of_ik (jq_installTcbCap _ _ _ _)) fun _ h => h.1)
          (fun _ => ?_) fun _ h => tq_t1 h.2.1
        refine hke_bind (R := JQ []) (hk_liftE (hk_of_ik (by jq_auto))) (fun _ => ?_) fun _ h => tq_t1 h.2.1
        refine hke_bind (R := T1) (hk_liftE fun σ hσ y hy => tq_t1 (tq_setPriority _ _ σ hσ.2 y hy).1)
          (fun _ => ?_) fun _ h => h
        exact hk_of_ik (by q1_auto)
    case notificationControl t n =>
      cases n <;>
      · refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
        simp only [fl4PerformInvocation, invokeTcb]
        q1_auto
    all_goals
      refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
      simp only [fl4PerformInvocation, invokeTcb]
      q1_auto
  case invokeArchObject a =>
    cases a
    case spec a =>
      cases a
      case invokeASIDControl oper =>
        cases oper with
        | makePool frame slot parent base =>
          intro σ hσ y hy
          simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
          obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
          obtain ⟨x1, hx1, hx⟩ := hx
          obtain ⟨dev, fi, hc, hk⟩ := hσ.2.1.2 frame slot parent base rfl
          obtain ⟨hD, hf⟩ := rqMp_of hσ.2.2.1 hσ.2.2.2 hσ.1.2.1 hc hk
          have hb1 := tq_makePool frame slot parent base σ hD hf hσ.1.2 x1 hx1
          rw [Set.mem_singleton_iff.1 hx]; exact tq_t1 hb1.1
      all_goals
        refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
        q1_auto
    all_goals
      refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
      q1_auto
  all_goals
    refine fun σ hσ y hy => (?_ : Q1KE _) σ (pq_t1 hσ) y hy
    simp only [fl4PerformInvocation, withoutPreemption]
    q1_auto

end

end Fl4Proofs.P3.SInvQ
