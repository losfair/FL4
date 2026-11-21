/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **ScLive across the budget charge**
(sl1 handoff 1; spec side only): `end_timeslice` may raise a timeout fault
(`handle_timeout`, never a donation: SpecInvSlM), reached from
`charge_budget`, `check_budget`, `check_budget_restart`.
-/
import Fl4Proofs.P3.SpecInvSlR
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

section B
variable {I : ObjRef × ObjRef} {K L : List ObjRef} {t : ObjRef}

theorem sl_endTimeslice (cto : Bool) : HK (SAP I K L False t) (SL I K) (endTimeslice (Z := Unit) cto) := by
  unfold endTimeslice
  sapf_step
  sapf_step
  sapf_step
  refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun ts => ?_
  have htail : ∀ (m : NonDet (State Unit) Bool), IK (SAP I K L False t) m →
      ∀ (k : Bool → NonDet (State Unit) Unit), (∀ v, HK (SAP I K L False t) (SL I K) (k v)) →
      HK (SAP I K L False t) (SL I K) (m >>= k) :=
    fun m hm k hk => shk_ikbind hm hk
  dsimp only
  split
  all_goals refine htail _ ?_ _ fun valid => ?_
  any_goals exact ik_pure _
  any_goals exact sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)
  all_goals
    split
    · sapf_step
      exact sl_handleTimeout _ _
    · exact shk_ik (by sl_auto) fun s h => h.1.1

theorem sl_chargeBudget (n : Ticks) (cto : Bool) :
    HK (SAP I K L False t) (SL I K) (chargeBudget (Z := Unit) n cto) := by
  unfold chargeBudget
  sapf_step
  sapf_step
  sapf_step
  sapf_step
  sapf_step
  sapf_step
  unfold NonDet.when
  split
  · exact shk_bind (sl_endTimeslice _) fun _ => shk_ik (by sl_auto) fun s h => h
  · exact shk_pure _ fun s h => h.1.1

theorem sl_checkBudget : HK (SAP I K L False t) (SL I K) (checkBudget (Z := Unit)) := by
  unfold checkBudget
  sapf_step
  sapf_step
  sapf_step
  split
  · exact shk_ik (by sl_auto) fun s h => h.1.1
  · sapf_step
    exact shk_bind (sl_chargeBudget _ _) fun _ => shk_pure _ fun s h => h

theorem sl_checkBudgetRestart : HK (SAP I K L False t) (SL I K) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  exact shk_bind sl_checkBudget fun _ => shk_ik (by sl_auto) fun s h => h

end B

end

end Fl4Proofs.P3.SInvL
