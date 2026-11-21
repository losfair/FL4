/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi2): `VI N S b`, part F: **receive,
reply, budget, scheduler-side and TCB writers** (vi1's handoff steps 2 and 3).

* `receive_ipc` (the receiver `thread ≠ N`; the sender is taken from the queue, so it is
  not `N`), `do_reply_transfer` (the receiver read `BlockedOnReply` is not `N`),
  `handle_recv` (the current thread, `b = true`).
* Budget: `end_timeslice` at `b = true` (it times out / requeues the current thread);
  `charge_budget` calls it only after reading `schedulable ct`, and a schedulable thread is
  not `N`, so `vi_ct_when_sched` runs it at `b = true` from any `b`; check_budget(_restart)
  (a runnable thread is not `N`), the preemption path, `handle_yield`.
* `activate_thread` (the idle thread is left to `arch_activate_idle_thread`; a `Restart`
  thread is not `N`), `restart` (`¬idle` guard), `suspend` / `set_priority` /
  `bind_notification` (target `≠ N`), `sched_context_yield_to` (`b = true`: it writes the
  current thread's yield-to), FL4's timer step `fl4Awaken` (signals only), interrupts.
-/
import Fl4Proofs.P3.SpecInvViR
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Current-thread facts -/

theorem vit_true {σ : State Unit} (h : VIT N S T b σ) (hc : σ.curThread ≠ N) : VIT N S T true σ :=
  ⟨h.1, h.2.1, fun _ => hc, h.2.2.2⟩

theorem vit_any {σ : State Unit} (b' : Bool) (h : VIT N S T true σ) : VIT N S T b' σ :=
  ⟨h.1, h.2.1, fun _ => h.2.2.1 rfl, h.2.2.2⟩

theorem vi_weakB {α : Type} {m : NonDet (State Unit) α} (h : IK (VIT N S T true) m) (hc : ∀ σ, VIT N S T b σ → σ.curThread ≠ N) :
    IK (VIT N S T b) m :=
  fun σ hσ y hy => vit_any b (h σ (vit_true hσ (hc σ hσ)) y hy)

/-- `ct ← gets cur_thread; sched ← gets (schedulable ct); when sched (m ct)`: `m` runs with a
current thread that is not idle. -/
theorem vi_ct_when_sched {m : ObjRef → NonDet (State Unit) Unit} (hm : ∀ ct, IK (VIT N S T true) (m ct)) :
    IK (VIT N S T b) (NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct =>
      NonDet.gets (schedulable (Z := Unit) ct) >>= fun sched => NonDet.when sched (m ct)) := by
  intro σ hσ y ⟨z, hz, hy⟩
  rw [mem_gets_vi hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [mem_gets_vi hw] at hy
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hs
    exact vit_any b (hm σ.curThread σ (vit_true hσ (vi_ne_of_schedulable hσ hs)) y hy)
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ

/-! ## Receiving and replying -/

set_option maxHeartbeats 4000000 in
theorem vi_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    IK (VI N S b) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine ik_bind (by vi_auto) fun recvOpt => ?_
  refine vi_maybeM _ fun receiver _ => ?_
  refine vi_gts_bind receiver fun st hst => ?_
  cases st with
  | blockedOnReply r =>
    have hr : receiver ≠ N := fun e => by cases hst e
    dsimp only
    vi_auto
  | _ => exact ik_pure _
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_doReplyTransfer _ _ _)

set_option maxHeartbeats 4000000 in
theorem vi_handleRecv (blk cr : Bool) : IK (VI N S true) (handleRecv (Z := Unit) blk cr) := by
  unfold handleRecv; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleRecv _ _)

/-! ## Budget -/

theorem vi_endTimeslice (c : Bool) : IK (VI N S true) (endTimeslice (Z := Unit) c) := by
  unfold endTimeslice; vi_auto

theorem vi_chargeBudget (consumed : Ticks) (c : Bool) : IK (VI N S b) (chargeBudget (Z := Unit) consumed c) := by
  unfold chargeBudget
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (by vi_auto) fun _ => ?_
  refine ik_bind (by vi_auto) fun _ => ?_
  exact vi_ct_when_sched fun _ => by
    refine ik_bind (vi_endTimeslice _) fun _ => ?_
    vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_chargeBudget _ _)

theorem vi_checkBudget : IK (VI N S b) (checkBudget (Z := Unit)) := by
  unfold checkBudget; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkBudget)

theorem vi_checkBudgetRestart : IK (VI N S b) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkBudgetRestart)

theorem vi_preemptionPath : IK (VI N S b) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_preemptionPath)

theorem vi_handleYield : IK (VI N S b) (handleYield (Z := Unit)) := by
  unfold handleYield; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleYield)

/-! ## Scheduler side and TCB operations -/

theorem vi_activateThread : IK (VI N S b) (activateThread (Z := Unit)) := by
  unfold activateThread
  refine ik_bind (ik_gets _) fun thread => ik_bind (by vi_auto) fun _ => ik_bind (by vi_auto) fun _ => ?_
  refine vi_gts_bind thread fun st hst => ?_
  cases st with
  | restart =>
    have hr : thread ≠ N := fun e => by cases hst e
    dsimp only
    vi_auto
  | _ => dsimp only; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_activateThread)

theorem vi_restart (t : ObjRef) : IK (VI N S b) (restart (Z := Unit) t) := by
  unfold restart; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_restart _)

theorem vi_suspend (t : ObjRef) (ht : t ≠ N) : IK (VI N S b) (suspend (Z := Unit) t) := by
  unfold suspend; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_suspend _ ?_; vi_side2))

theorem vi_setPriority (t : ObjRef) (p : Priority) (ht : t ≠ N) : IK (VI N S b) (setPriority (Z := Unit) t p) := by
  unfold setPriority; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_setPriority _ _ ?_; vi_side2))

theorem vi_bindNotification (t n : ObjRef) (ht : t ≠ N) : IK (VI N S b) (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_bindNotification _ _ ?_; vi_side2))

theorem vi_schedContextYieldTo (p : ObjRef) : IK (VI N S true) (schedContextYieldTo (Z := Unit) p) := by
  unfold schedContextYieldTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextYieldTo _)

theorem vi_fl4Awaken : IK (VI N S b) (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact vi_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4Awaken)

theorem vi_handleInterrupt (irq : Irq) : IK (VI N S b) (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleInterrupt _)

theorem vi_maybeHandleInterrupt (k : Bool) : IK (VI N S b) (maybeHandleInterrupt (Z := Unit) k) := by
  unfold maybeHandleInterrupt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_maybeHandleInterrupt _)

end

end Fl4Proofs.P3.SInvI
