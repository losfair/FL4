/-
P3 (DESIGN.md §9), invariant line G1 (rd8p, KENTRY-PLAN rd8m handoff 2):
**`Rdy` after `preemption_path`** from facts at the preempted state (spec
side only, outside the JAtZ cone).

* **`rq_maybeHandleInterrupt`**: `Rdy ∧ NQ []` (rd8f's `RQ`) across
  `maybe_handle_interrupt` (rd10's AW9 walk with RdL's `rd_sendSignal`, which
  needs only `Rdy` and `NtfnQB`).
* **`CurHold s`**: every TCB bound to `cur_sc` is not `BlkR` and is either the
  current thread or not runnable. This is the fact the charge of an active,
  sporadic `cur_sc` needs (`Excl`, read by `refill_budget_check`) when ct is
  not schedulable. Its l4v counterpart is the `cur_sc` side of
  `cur_sc_chargeable`. It holds at the reachable preemption points: at the
  perform `cur_sc`'s holder is ct (CurScT / ScSym), ct is Restart and the
  deletion cone never blocks a thread. The only rebinding of `cur_sc` there is
  `reply_remove`'s donation to a BlockedOnReply caller, which is not ct
  (ctq14's CKN). That caller is then unlinked (Inactive) and is never
  restarted inside the cone, since `restart_thread_if_no_fault` only reaches
  endpoint / notification queued threads.
* **`excl_of_hold`**: `Excl s cur_sc` from `CurHold`, ctq's `TQ` (a queued
  thread is runnable), `RA` (the switch target is runnable), `CtQ` and
  `NP ct` (all inside `EB true`).
* **`rd_preemptionPath`**: from `Rdy ∧ NQ [] ∧ ScInv ∧ CKN ∧ EB true ∧
  CurHold` at the preempted state, `Rdy ∧ NQ []` at every outcome of
  `preemption_path`. The three branches are (1) ct schedulable: check_budget,
  with ct bound to `cur_sc` by CKN and RdJ's `rd_chargeBudget`; (2) ct not
  schedulable with `cur_sc` active: RdH's charge `rd_chargeBudget_head`
  without the tail, since ct stays unschedulable by ctq's `sched_of_bf`;
  (3) `cur_sc` inactive: only `consumed_time := 0`. Then
  `maybe_handle_interrupt`.
-/
import Fl4Proofs.P3.SpecInvRd10A3
import Fl4Proofs.P3.SpecInvRd8fA
import Fl4Proofs.P3.SpecInvCqHS
import Fl4Proofs.P3.SpecInvEqD
open Classical

namespace Fl4Proofs.P3.SInvR.B8p
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `maybe_handle_interrupt` -/

theorem rq_sendSignal (n : ObjRef) (bd : Badge) : IK B8f.RQ (sendSignal (Z := Unit) n bd) :=
  fun b0 hb y hy => ⟨rd_sendSignal n bd b0 hb.1 (ntfnQB_of_nq hb.2) y hy, nq_sendSignal n bd b0 hb.2 y hy⟩

theorem rq_doMachineOp {α : Type} (mop : NonDet MachineState α) : IK B8f.RQ (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem rq_handleInterrupt (irq : Irq) : IK B8f.RQ (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt
  split
  · exact rq_doMachineOp _
  · refine ik_bind ?_ fun st => ?_
    · unfold getIrqState; repeat' (first | ik_step0 | ik_unfold)
    · dsimp only
      split
      · refine ik_bind ?_ fun sl => ?_
        · unfold getIrqSlot; repeat' (first | ik_step0 | ik_unfold)
        refine ik_bind ?_ fun cap => ?_
        · intro σ0 hσ y hy
          have e1 : y.2 = σ0 := SInvQ.cq5_ro (fun _ => by
            obtain ⟨o, r⟩ := sl; unfold getCap; repeat' (first | ik_step0 | ik_unfold | split)) hy
          rw [e1]; exact hσ
        refine ik_bind ?_ fun _ => ?_
        · unfold NonDet.when
          split
          · exact rq_sendSignal _ _
          · exact ik_pure _
        refine ik_bind ?_ fun _ => rq_doMachineOp _
        unfold archMaskIrqSignal; exact rq_doMachineOp _
      · refine ik_bind (rq_doMachineOp _) fun _ => ?_
        refine ik_bind (ik_modify (fun _ h => h)) fun _ => rq_doMachineOp _
      · exact ik_bind ik_fail fun _ => rq_doMachineOp _
      · refine ik_bind ?_ fun _ => rq_doMachineOp _
        unfold handleReservedIrq; exact ik_pure _

/-- **`Rdy ∧ NQ []` across `maybe_handle_interrupt`.** -/
theorem rq_maybeHandleInterrupt (b : Bool) : IK B8f.RQ (maybeHandleInterrupt (Z := Unit) b) := by
  unfold maybeHandleInterrupt
  refine ik_bind (rq_doMachineOp _) fun o => ?_
  cases o with
  | none => unfold handleSpuriousIrq; exact ik_pure _
  | some irq => exact rq_handleInterrupt irq

/-! ## The holder of `cur_sc` -/

/-- **`CurHold`** (module docstring): every TCB bound to `cur_sc` is not
`BlkR`, and is the current thread or not runnable. -/
def CurHold (s : State Unit) : Prop :=
  ∀ t x, s.kheap t = some (.tcb x) → x.tcbSchedContext = some s.curSc →
    ¬ BlkR x.tcbState x.tcbFault ∧ (t = s.curThread ∨ runnable x.tcbState = false)

/-- **`Excl` of `cur_sc`** from `CurHold` and the scheduler slices of `EB true`. -/
theorem excl_of_hold {s : State Unit} (hH : CurHold s) (hEB : EB true s) : Excl s s.curSc := by
  have hQd : RQd s := hEB.1.1.1.1
  have hRA : SInvQ.RA s := hEB.1.1.2.1
  obtain ⟨hCQ, hNP⟩ := hEB.2.1.2.1 rfl
  intro t x hx hc
  obtain ⟨hB, ht⟩ := hH t x hx hc
  rcases ht with rfl | hnr
  · exact ⟨hCQ, hNP.1, hB⟩
  · refine ⟨fun d q hq => ?_, fun e => ?_, hB⟩
    · obtain ⟨x', hx', -, -, hr⟩ := hQd d q t hq
      rw [hx] at hx'; cases hx'; rw [hnr] at hr; cases hr
    · obtain ⟨x', hx', hr⟩ := hRA t e
      rw [hx] at hx'; cases hx'; rw [hnr] at hr; cases hr

/-- The charge's frame for ctq's `sched_of_bf`. -/
theorem bf_chargeOut {σ : State Unit} {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) {s1 : State Unit} (hO : ChargeOut σ x n s1) :
    BF σ.kheap σ.curThread σ.curSc σ.releaseQueue s1 := by
  obtain ⟨z, rfl, e1, e2, -, -, -, -⟩ := hO
  refine ⟨rfl, rfl, rfl, fun q => ?_⟩
  by_cases hq : q = σ.curSc
  · subst hq
    right
    exact ⟨x, z, n, hk, kh_upd _ _ _ _, e1, by simp only [scActive, e2]⟩
  · left
    show (updSc σ σ.curSc z n).kheap q = σ.kheap q
    simp [Notif.updK, hq]

/-! ## `preemption_path` -/

/-- **`Rdy ∧ NQ []` after `preemption_path`** (module docstring, three branches). -/
theorem rd_preemptionPath {σ : State Unit} (hR : Rdy σ) (hN : NQ [] σ) (hS : SInvB.ScInv σ)
    (hK : R14.CKN σ) (hEB : EB true σ) (hH : CurHold σ) :
    ∀ y ∈ (preemptionPath (Z := Unit) σ).1, Rdy y.2 ∧ NQ [] y.2 := by
  have hX : Excl σ σ.curSc := excl_of_hold hH hEB
  intro y hy
  unfold preemptionPath at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  try dsimp only at hy
  split at hy
  · -- (1) ct schedulable: check_budget
    rename_i hs
    obtain ⟨w, hw, hy⟩ := hy
    refine rq_maybeHandleInterrupt true w.2 ⟨?_, nq_checkBudget (K := []) σ hN w hw⟩ y hy
    rcases checkBudget_cases hw with ⟨e, -⟩ | ⟨-, hc⟩
    · rw [e]; exact hR
    · obtain ⟨xt, c, z, m, hct, hc0, hz, ha⟩ := actB_of_schedulable hs
      have hb : xt.tcbSchedContext = some σ.curSc := by
        rcases (hK xt hct).1 with h | h
        · rw [h] at hc0; cases hc0
        · exact h
      rw [hb] at hc0; cases hc0
      obtain ⟨y0, k0, hy0, -, hne⟩ := hS.back σ.curThread xt σ.curSc hct hb
      rw [hz] at hy0; cases hy0
      exact (rd_chargeBudget hR hz ha (hne (Or.inr ha)) (fun _ _ => hX) hct hb hS.fwd _ true hc).1
  · -- ct not schedulable
    rename_i hs
    obtain ⟨w1, hw1, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hw1] at hy
    obtain ⟨w2, hw2, hy⟩ := hy
    obtain ⟨x, n, hk, rfl⟩ := SInvE.mem_getScActive hw2
    try dsimp only at hy
    split at hy
    · -- (2) cur_sc active: the charge, no tail
      rename_i ha
      obtain ⟨w3, hw3, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hw3] at hy
      obtain ⟨z, hz, hy⟩ := hy
      refine rq_maybeHandleInterrupt true z.2 ⟨?_, nq_chargeBudget (K := []) _ _ σ hN z hz⟩ y hy
      have hne : x.scRefills ≠ [] := hS.2 σ.curSc x n hk (Or.inr ha)
      obtain ⟨s1, hR1, hO, hz1⟩ := rd_chargeBudget_head hR hk (fun _ => ⟨ha, hne, fun _ => hX⟩) _ false hz
      have hs1 : schedulable s1.curThread s1 = false := by
        rw [sched_of_bf (bf_chargeOut hk hO)]
        cases h : schedulable σ.curThread σ
        · rfl
        · exact absurd h hs
      rw [(cbTail_cf hz1).2 hs1]; exact hR1
    · -- (3) cur_sc inactive: consumed_time := 0
      obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hz] at hy
      try dsimp only at hy
      exact rq_maybeHandleInterrupt true { σ with consumedTime := 0 } ⟨rdy_consumed0 hR, hN⟩ y hy

end

end Fl4Proofs.P3.SInvR.B8p
