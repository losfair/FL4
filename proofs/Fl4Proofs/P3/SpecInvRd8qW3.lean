/-
P3 (DESIGN.md §9), invariant line G1 (rd8q): **`VE` across the wake-up writers** (l4v's
`set_thread_state t Running; …; possible_switch_to t` discipline).

* **`ht_tpst`** (`when (schedulable t) (possible_switch_to t)`, any continuation: `t` leaves the
  exception set), **`ht_testPossibleSwitchTo`**.
* **`ve_updateWaitingNtfn`**, **`ve_sendSignal`** (the woken thread is exempt from its
  `set_thread_state Running` to its `possible_switch_to`), **`ve_restart`**.
* FL4's TCB timers: **`ve_fl4TimerSignal`**, **`ve_fl4TimerFire`**, **`ve_fl4TimerFires`**,
  **`ve_fl4Awaken`** (every `fl4TimerFires` step is a `send_signal`).
-/
import Fl4Proofs.P3.SpecInvRd8qW2
open Classical

namespace Fl4Proofs.P3.SInvR.B8q
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_awaken)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedContextBindTcb _ _)

/-- `when (schedulable t) (possible_switch_to t)` then `k`: `t` leaves the exception set. -/
theorem ht_tpst (t : ObjRef) {β : Type} (inst : ∀ b : Bool, Decidable (b = true)) (k : NonDet (State Unit) β)
    (hk : VEK E k) :
    HT (VE (Ins E t)) (VE E) (NonDet.gets (schedulable t) >>= fun sched =>
      @NonDet.when _ (sched = true) (inst sched) (possibleSwitchTo (Z := Unit) t) >>= fun _ => k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  obtain ⟨z, hz, hx⟩ := hx
  have hz' : VE E z.2 := by
    unfold NonDet.when at hz
    split at hz
    · exact ht_possibleSwitchTo t σ hσ z hz
    · rename_i hn
      rw [Set.mem_singleton_iff.1 hz]
      exact ve_drop hσ fun hs => absurd hs hn
  exact hk z.2 hz' x hx

/-- `test_possible_switch_to t`: `t` leaves the exception set. -/
theorem ht_testPossibleSwitchTo (t : ObjRef) : HT (VE (Ins E t)) (VE E) (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · exact ht_possibleSwitchTo t σ hσ x hx
  · rename_i hn
    rw [Set.mem_singleton_iff.1 hx]
    exact ve_drop hσ fun hs => absurd hs hn

/-- The woken thread `t`: running, badge, donation, then `possible_switch_to`. -/
theorem ht_wake (t n : ObjRef) (b : Badge) {β : Type} (inst : ∀ b : Bool, Decidable (b = true))
    (k : NonDet (State Unit) β) (hk : VEK E k) :
    HT (VE E) (VE E) (setThreadState (Z := Unit) t .running >>= fun _ =>
      asUser (Z := Unit) t (setRegister badge_register b) >>= fun _ => maybeDonateSc (Z := Unit) t n >>= fun _ =>
      NonDet.gets (schedulable t) >>= fun sched =>
      @NonDet.when _ (sched = true) (inst sched) (possibleSwitchTo (Z := Unit) t) >>= fun _ => k) := by
  refine ht_bind (ht_setThreadState_x t _) fun _ => ?_
  refine ht_bind (ht_ik (ve_asUser t _)) fun _ => ?_
  refine ht_bind (ht_ik (ve_maybeDonateSc t n (Or.inr rfl))) fun _ => ?_
  exact ht_tpst t inst k hk

theorem ve_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (b : Badge) :
    VEK E (updateWaitingNtfn (Z := Unit) n q b) := by
  unfold updateWaitingNtfn
  refine ik_bind (by ve_auto) fun _ => ?_
  refine ik_pure_bind ?_
  refine ik_bind (by ve_auto) fun _ => ik_of_ht ?_
  exact ht_wake _ n b _ _ (by ve_auto)

theorem ve_sendSignal (n : ObjRef) (b : Badge) : VEK E (sendSignal (Z := Unit) n b) := by
  unfold sendSignal
  refine ik_bind (by ve_auto) fun ntfn => ?_
  split
  · refine ik_bind (by ve_auto) fun st => ?_
    split
    · refine ik_bind (by ve_auto) fun _ => ik_of_ht ?_
      exact ht_wake _ n b _ _ (by ve_auto)
    · ve_auto
  · ve_auto
  · exact ve_updateWaitingNtfn _ _ _
  · ve_auto

theorem ve_restart (t : ObjRef) : VEK E (restart (Z := Unit) t) := by
  unfold restart
  refine ik_bind (by ve_auto) fun st => ik_bind (by ve_auto) fun sc => ?_
  unfold NonDet.when
  split
  · refine ik_bind (by ve_auto) fun _ => ik_of_ht ?_
    refine ht_bind (ht_setThreadState_x t _) fun _ => ?_
    exact ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ht_testPossibleSwitchTo t
  · exact ik_pure _

/-! ## FL4's TCB timers -/

theorem ve_fl4TimerSignal {σ σ' : State Unit} (h : VE E σ) (hs : fl4TimerSignal σ σ') : VE E σ' := by
  obtain ⟨n, b, e⟩ := hs
  exact ve_sendSignal n b σ h ((), σ') (by rw [e]; exact Set.mem_singleton _)

theorem ve_fl4TimerFire {σ σ' : State Unit} (h : VE E σ) (hs : fl4TimerFire σ σ') : VE E σ' := by
  obtain ⟨σ1, h1, rfl⟩ := hs
  have h1' : VE E σ1 := by
    rcases h1 with rfl | h1
    · exact h
    · exact ve_fl4TimerSignal h h1
  exact ve_kh h1' rfl rfl rfl rfl rfl

theorem ve_fl4TimerFires {σ σ' : State Unit} (h : VE E σ) (hs : fl4TimerFires σ σ') : VE E σ' := by
  induction hs with
  | refl => exact h
  | tail _ h2 ih => exact ve_fl4TimerFire ih h2

theorem ve_fl4Awaken : VEK E (fl4Awaken (Z := Unit)) := by
  intro σ h x hx
  exact ve_fl4TimerFires h hx

end

end Fl4Proofs.P3.SInvR.B8q
