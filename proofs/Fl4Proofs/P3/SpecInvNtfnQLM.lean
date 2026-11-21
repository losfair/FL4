/-
P3 (DESIGN.md §9), invariant line G1 (il1): **IfLiveT across the sends, the
faults and the budget charge** (spec side only; after the generated family
SpecInvNtfnQL1..L6).

* `il_sendIpc` (the sender a thread of `K`; the woken receiver is read
  BlockedOnReceive, so it joins `K`), `il_sendFaultIpc`, `il_handleTimeout`,
  `il_handleFault`, `il_receiveIpc` (the woken sender is read BlockedOnSend).
* The budget: `il_endTimeslice_p` (the current thread runnable, so it joins
  `K` before a timeout fault blocks it), `il_chargeBudget` (`schedulable` ⇒
  runnable), `il_checkBudget`, `il_checkBudgetRestart`.
Unlike `NQ K`, `IL K` survives blocking (no cap is removed), so every post
keeps `K`.
-/
import Fl4Proofs.P3.SpecInvNtfnQL6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem runnable_live {s : ThreadState} (h : runnable s = true) : liveSt s := by
  cases s <;> simp_all [runnable, liveSt]

/-! ## Sends and faults -/

/-- `send_ipc` of a thread of `K`. -/
theorem il_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool)
    (thread epptr : ObjRef) (ht : thread ∈ Kq) :
    ILK Kq (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc
  refine ik_bind (by il_auto) fun ep => ?_
  split
  all_goals first
    | (exact il_sendIpcBlocked _ _ _ _ _ _ ht)
    | (exact ik_pure _)
    | (exact ik_fail)
    | skip
  refine ik_bind (il_tcbEpDequeue _ _) fun _ => ?_
  unfold getThreadState
  refine ik_threadGet_bind fun σ x hx => ?_
  (try dsimp only)
  cases hs : x.tcbState with
  | blockedOnReceive e r d =>
    refine ikp_ilcons hx (liveSt_eq hs True.intro) ?_
    (try dsimp only)
    il2_auto
  | _ => exact ikp_of_ik (by (try dsimp only); il2_auto) σ
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_sendIpc _ _ _ _ _ _ _ _ ?_) <;> nq_mem))

theorem il_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) (ht : tptr ∈ Kq) :
    ILK Kq (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_sendFaultIpc _ _ _ _ ?_) <;> nq_mem))

theorem il_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ∈ Kq) :
    ILK Kq (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_handleTimeout _ _ ?_) <;> nq_mem))

theorem il_handleFault (thread : ObjRef) (ex : Fault) (ht : thread ∈ Kq) :
    ILK Kq (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_handleFault _ _ ?_) <;> nq_mem))

set_option maxHeartbeats 4000000 in
/-- `receive_ipc` of a thread of `K`; the woken sender is read BlockedOnSend. -/
theorem il_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (ht : thread ∈ Kq) :
    ILK Kq (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; il2_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_receiveIpc _ _ _ _ ?_) <;> nq_mem))

/-! ## The budget charge -/

theorem ik_eq_isRoundRobin' (p : ObjRef) (σ : State Unit) :
    IK (fun s => s = σ) (isRoundRobin (Z := Unit) p) := by
  unfold isRoundRobin; repeat' (first | ik_step0 | ik_unfold)

/-- `end_timeslice` from a state whose current thread is runnable. -/
theorem il_endTimeslice_p (cto : Bool) (σ : State Unit)
    (hct : ∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = true) :
    IKp (IL Kq) σ (endTimeslice (Z := Unit) cto) := by
  intro hσ y hy
  unfold endTimeslice at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = σ := ik_eq_isRoundRobin' _ σ σ rfl y2 h2
  obtain ⟨r2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  rw [mem_gets h3] at hy
  obtain ⟨y4, h4, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet h4
  refine il_tail ((?_ : ILK (σ.curThread :: Kq) _) σ (il_consR hσ hx (runnable_live (hct x hx))) y hy)
  have htail : ∀ valid : Bool, ILK (σ.curThread :: Kq)
      (if cto = true ∧ ¬r2 = true ∧ valid = true then do
        let sc ← getSchedContext (Z := Unit) σ.curSc
        handleTimeout σ.curThread (.timeout sc.scBadge)
      else do
        let ready ← getScRefillReady σ.curSc
        let sufficient ← getScRefillSufficient σ.curSc 0
        if ready = true ∧ sufficient = true
        then tcbSchedAction tcbSchedAppend σ.curThread
        else postpone σ.curSc) := by
    intro valid
    split
    · exact ik_bind (by il_auto) fun sc => il_handleTimeout _ _ (List.mem_cons_self ..)
    · il_auto
  (try dsimp only)
  by_cases hv : x.tcbState = .runningVM
  · rw [if_pos hv]; exact ik_bind (ik_pure _) fun v => htail v
  · rw [if_neg hv]; exact ik_bind (by il_auto) fun v => htail v

theorem il_chargeBudget (n : Ticks) (cto : Bool) : ILK Kq (chargeBudget (Z := Unit) n cto) := by
  intro σ hσ y hy
  unfold chargeBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : IL Kq y3.2 := (?_ : ILK Kq _) _ hσ y3 h3
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 h4] at hy
    have hb4 : IL Kq { y3.2 with consumedTime := 0 } := hb3
    obtain ⟨y5, h5, hy⟩ := hy
    rw [mem_gets h5] at hy
    obtain ⟨y6, h6, hy⟩ := hy
    rw [mem_gets h6] at hy
    (try dsimp only at hy)
    unfold NonDet.when at hy
    split at hy
    · rename_i hs
      have hrun := sched_runnable hs
      obtain ⟨y7, h7, hy⟩ := hy
      have hb7 := il_endTimeslice_p (Kq := Kq) cto _ hrun hb4 y7 h7
      refine (?_ : ILK Kq _) _ hb7 y hy
      il_auto
    · rw [Set.mem_singleton_iff.1 hy]; exact hb4
  · il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_chargeBudget _ _)

theorem il_checkBudget : ILK Kq (checkBudget (Z := Unit)) := by
  unfold checkBudget
  refine ik_bind (by il_auto) fun csc => ?_
  refine ik_bind (by il_auto) fun consumed => ?_
  refine ik_bind (by il_auto) fun suff => ?_
  split
  · il_auto
  · refine ik_bind (by il_auto) fun c => ?_
    exact ik_bind (il_chargeBudget _ _) fun _ => ik_pure _
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkBudget)

/-- `check_budget_restart`: the current thread is written only when read runnable. -/
theorem il_checkBudgetRestart : ILK Kq (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  refine ik_bind il_checkBudget fun r => ?_
  refine ik_bind (by il_auto) fun cur => ?_
  unfold getThreadState
  refine ik_threadGet_bind fun σ x hx => ?_
  (try dsimp only)
  by_cases hr : runnable x.tcbState = true
  · refine ikp_ilcons hx (runnable_live hr) ?_
    il2_auto
  · refine ikp_of_ik ?_ σ
    unfold NonDet.when
    split
    · rename_i h; exact absurd h.2 hr
    · il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkBudgetRestart)

end

end Fl4Proofs.P3.SInv
