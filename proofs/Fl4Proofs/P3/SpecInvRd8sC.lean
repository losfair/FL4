/-
P3 (DESIGN.md §9), invariant line G1 (rd8s): **`VE` across the IPC, fault and budget writers**
(KENTRY-PLAN rd8q handoff 1(a), 1(c) budget part; spec side only, outside the JAtZ cone).

* **`ht_replyUnlinkTcb`** (the caller is left Inactive: it leaves the exception set), hence
  **`ve_replyRemoveV`** for every `E` (the donation receiver is the caller, exempt until it is
  unlinked).
* **`ve_receiveIpc t`** / **`ve_sendIpc … t …`** / `ve_sendFaultIpc` / `ve_handleTimeout` /
  `ve_handleFault` keep their thread argument exempt (`VEK (E ∪ {t})`); the woken partner
  (sender / destination) is exempt from its wake-up to its `possible_switch_to` (`ve_run_pst`,
  the destination's donation inside `ve_sendIpc`).
* On ct (`ht_ct`): **`ve_handleRecv`**, **`ve_endTimeslice`**, **`ve_checkBudgetRestart`**;
  `ve_chargeBudget`, `ve_checkBudget`, `ve_handleYield`, `ve_maybeHandleInterrupt`,
  `ve_preemptionPath`.
* Cancel cone: `ve_fastFinalise`, `ve_capDeleteOne`, `ve_deletingIrqHandler`, `ve_finaliseCap`
  (the invocation leaves follow in SpecInvRd8sD).
-/
import Fl4Proofs.P3.SpecInvRd8sB
open Classical

namespace Fl4Proofs.P3.SInvR.B8s
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}


/-- The woken partner: running, then `possible_switch_to`. -/
theorem ve_run_pst (t : ObjRef) :
    VEK E (setThreadState (Z := Unit) t .running >>= fun _ => possibleSwitchTo (Z := Unit) t) :=
  ik_of_ht (ht_bind (ht_setThreadState_x t _) fun _ => ht_possibleSwitchTo t)

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_run_pst _)

/-! ## Reply removal -/

theorem ht_replyUnlinkTcb (t r : ObjRef) : HT (VE (Ins E t)) (VE E) (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  exact ht_setThreadState_nr t _ rfl

/-- **`reply_remove caller r`** keeps `VE E` (the caller receives the donation and is left Inactive). -/
theorem ve_replyRemoveV (caller r : ObjRef) : VEK E (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove
  refine ik_of_ht (ht_conseq (fun _ h => ve_ins caller h) (fun _ h => h) ?_)
  try dsimp only [letFun]
  repeat (first | exact ht_replyUnlinkTcb caller r | refine ht_bind (ht_ik (by ve_auto; done)) fun _ => ?_ | split)

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_replyRemoveV _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_replyPush _ _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_completeSignal _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_receiveSignal _ _ _)

/-! ## IPC -/

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc t`** keeps `t` exempt; the sender woken by a non-call send leaves the set. -/
theorem ve_receiveIpc (t : ObjRef) (cap : Cap) (b : Bool) (rc : Cap) :
    VEK (Ins E t) (receiveIpc (Z := Unit) t cap b rc) := by
  unfold receiveIpc; ve_auto

/-- The destination arm of `send_ipc`: the destination is exempt from its dequeue (it may receive
the donation) to its `possible_switch_to`. -/
theorem ve_sendIpc (block call : Bool) (badge : Badge) (g gr d : Bool) (t ep : ObjRef) :
    VEK (Ins E t) (sendIpc (Z := Unit) block call badge g gr d t ep) := by
  unfold sendIpc
  refine ik_bind (by ve_auto) fun epv => ?_
  rcases epv with _ | q | q
  · cases block <;> (try dsimp only) <;> ve_auto
  · cases block <;> (try dsimp only) <;> ve_auto
  · rcases q with _ | ⟨dest, q⟩
    · cases block <;> (try dsimp only) <;> ve_auto
    · cases block <;> (try dsimp only) <;>
      · refine ik_of_ht (ht_conseq (fun _ h => ve_ins dest h) (fun _ h => h) ?_)
        repeat (first | exact ht_possibleSwitchTo dest | refine ht_bind (ht_ik (by ve_auto; done)) fun _ => ?_ | split)

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_receiveIpc _ _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_sendIpc _ _ _ _ _ _ _ _)

theorem ve_sendFaultIpc (t : ObjRef) (h : Cap) (f : Fault) (d : Bool) :
    VEK (Ins E t) (sendFaultIpc (Z := Unit) t h f d) := by
  unfold sendFaultIpc; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_sendFaultIpc _ _ _ _)

theorem ve_handleTimeout (t : ObjRef) (f : Fault) : VEK (Ins E t) (handleTimeout (Z := Unit) t f) := by
  unfold handleTimeout; ve_auto

theorem ve_handleFault (t : ObjRef) (f : Fault) : VEK (Ins E t) (handleFault (Z := Unit) t f) := by
  unfold handleFault; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_handleTimeout _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_handleFault _ _)

/-- **`handle_recv`**: every write of a runnable state is to ct or to a woken sender. -/
theorem ve_handleRecv (b r : Bool) : VEK E (handleRecv (Z := Unit) b r) := by
  unfold handleRecv
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  exact ht_ct (E := E) σ.curThread (by ve_auto) (by ct_auto) σ ⟨hσ, rfl⟩ x hx

/-! ## Budget -/

/-- **`end_timeslice`**: ct is timed out (fault IPC of ct), appended, or postponed. -/
theorem ve_endTimeslice (c : Bool) : VEK E (endTimeslice (Z := Unit) c) := by
  unfold endTimeslice
  refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  exact ht_ct (E := E) σ.curThread (by ve_auto) (by ct_auto) σ ⟨hσ, rfl⟩ x hx

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_endTimeslice _)

theorem ve_chargeBudget (u : Ticks) (c : Bool) : VEK E (chargeBudget (Z := Unit) u c) := by
  unfold chargeBudget; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_chargeBudget _ _)

theorem ve_checkBudget : VEK E (checkBudget (Z := Unit)) := by
  unfold checkBudget; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_checkBudget)

/-- **`check_budget_restart`**: the Restart write is to ct. -/
theorem ve_checkBudgetRestart : VEK E (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart
  refine ik_bind (by ve_auto) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  exact ht_ct (E := E) σ.curThread (by ve_auto) (by ct_auto) σ ⟨hσ, rfl⟩ x hx

theorem ve_handleYield : VEK E (handleYield (Z := Unit)) := by
  unfold handleYield; ve_auto

theorem ve_maybeHandleInterrupt (b : Bool) : VEK E (maybeHandleInterrupt (Z := Unit) b) := by
  unfold maybeHandleInterrupt; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_checkBudgetRestart)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_handleYield)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_maybeHandleInterrupt _)

theorem ve_preemptionPath : VEK E (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_preemptionPath)

/-! ## Cancel / finalise cone -/

theorem ve_fastFinalise (c : Cap) (f : Bool) : VEK E (fastFinalise (Z := Unit) c f) := by
  unfold fastFinalise; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_fastFinalise _ _)

theorem ve_capDeleteOne (sl : CslotPtr) : VEK E (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_capDeleteOne _)

theorem ve_deletingIrqHandler (irq : Irq) : VEK E (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_deletingIrqHandler _)

theorem ve_finaliseCap (c : Cap) (f : Bool) : VEK E (finaliseCap (Z := Unit) c f) := by
  unfold finaliseCap; ve_auto

end

end Fl4Proofs.P3.SInvR.B8s
