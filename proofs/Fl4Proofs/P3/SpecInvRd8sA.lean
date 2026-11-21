/-
P3 (DESIGN.md §9), invariant line G1 (rd8s): **`VE` across the wake-up / cancel writers**
(KENTRY-PLAN rd8q handoff 1(a); spec side only, outside the JAtZ cone).

* Drops: **`ht_threadSet_nr`** / **`ht_setThreadState_nr`** (a write of `t`'s TCB in a state that
  is not runnable takes `t` out of the exception set), **`ve_drop_ct`** / **`ht_ct`** (the current
  thread is exempt anyway: `VE (E ∪ {t})` with `ct = t` is `VE E`).
* Writers keeping their thread argument exempt (`VEK (E ∪ {t})`; the callers run them on ct or
  make `t` leave the set afterwards): **`ve_completeSignal`**, **`ve_receiveSignal`**,
  **`ve_replyPush`** (the callee receives the donation), **`ve_replyRemove`** (the caller
  receives the donation).
* Writers keeping `VE E`: **`ve_removeAndRestartNtfnQueuedThread`**, **`ve_restartThreadIfNoFault`**,
  `ve_removeAndRestartEpQueuedThread`, `ve_removeAndRestartBadgedThread`, `ve_cancelAllSignals`,
  `ve_cancelAllIpc`, `ve_cancelBadgedSends`, **`ve_suspend`**, `ve_schedContextUnbindAllTcbs`,
  `ve_unbindFromSc`, **`ve_schedContextYieldTo`**, `ve_handleInterrupt`, `ve_invokeSetDomain`,
  **`ve_activateThread`** (ct), **`ht_guardedSwitchTo`** (`switch_to_thread`'s form).
-/
import Fl4Proofs.P3.SpecInvRd8qW3
open Classical

namespace Fl4Proofs.P3.SInvR.B8s
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact B8q.ve_sendSignal _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact B8q.ve_updateWaitingNtfn _ _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact B8q.ve_restart _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact B8q.ve_fl4Awaken)
macro_rules | `(tactic| ve_leaf) => `(tactic|
  ((with_reducible refine B8q.ve_maybeDonateSc _ _ ?_); first | exact Or.inr rfl | assumption))
macro_rules | `(tactic| ve_leaf) => `(tactic|
  ((with_reducible refine B8q.ve_schedContextDonate _ _ ?_); first | exact Or.inr rfl | assumption))

/-! ## Drops -/

theorem threadSet_out {f : Tcb → Tcb} {t : ObjRef} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ a, getTcb t σ = some a ∧ x.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f a))) } := by
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  unfold NonDet.getsThe at hy
  cases e : getTcb t σ with
  | none => rw [e] at hy; exact hy.elim
  | some a =>
    rw [e] at hy
    rw [Set.mem_singleton_iff.1 hy] at hx
    exact ⟨a, rfl, B8q.setObject_out hx⟩

/-- A TCB write of `t` in a state that is not runnable: `t` leaves the exception set. -/
theorem ht_threadSet_nr (t : ObjRef) (f : Tcb → Tcb) (hf : ∀ x, runnable (f x).tcbState = false) :
    HT (VE (Ins E t)) (VE E) (threadSet (Z := Unit) f t) := by
  intro σ hσ x hx
  obtain ⟨a, -, e⟩ := threadSet_out hx
  rw [e]
  refine ve_drop (ve_mono (fun u h => h.elim id Or.inr) (ve_upd_tcb hσ t (f a))) fun hs => False.elim ?_
  obtain ⟨x0, -, -, -, hx0, -, hrn, -⟩ := Sched.schedulable_inv hs
  dsimp only at hx0
  rw [Function.update_apply, if_pos rfl] at hx0
  injection Option.some.inj hx0 with e0
  subst e0
  rw [hf a] at hrn; cases hrn

theorem ht_setThreadState_nr (t : ObjRef) (ts : ThreadState) (h : runnable ts = false) :
    HT (VE (Ins E t)) (VE E) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ht_bind (ht_threadSet_nr t _ fun _ => h) fun _ => ht_ik (ve_setThreadStateAct t)

/-- Any `set_thread_state` of an exempt thread keeps it exempt. -/
theorem ve_setThreadState_in (t : ObjRef) (ts : ThreadState) : VEK (Ins E t) (setThreadState (Z := Unit) t ts) :=
  fun σ hσ x hx => ve_mono (fun u h => h.elim id Or.inr) (ht_setThreadState_x (E := Ins E t) t ts σ hσ x hx)

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setThreadState_in _ _)

/-- The current thread is exempt anyway. -/
theorem ve_drop_ct {σ : State Unit} {t : ObjRef} (h : VE (Ins E t) σ) (hc : σ.curThread = t) : VE E σ :=
  ve_drop h fun _ hne => absurd hc.symm hne

theorem ht_ct {α : Type} (t : ObjRef) {m : NonDet (State Unit) α} (h : VEK (Ins E t) m)
    (hc : SInv.CTK t m) : HT (fun s => VE E s ∧ s.curThread = t) (VE E) m :=
  fun σ hσ x hx => ve_drop_ct (h σ (ve_ins t hσ.1) x hx) (hc σ hσ.2 x hx)

/-- `VE` and the current thread together. -/
theorem htc {α : Type} (C : ObjRef) {m : NonDet (State Unit) α} (h : VEK E m) (hc : SInv.CTK C m) :
    HT (fun s => VE E s ∧ s.curThread = C) (fun s => VE E s ∧ s.curThread = C) m :=
  ik_and h hc

/-! ## Writers keeping their thread exempt -/

theorem ve_completeSignal (n t : ObjRef) : VEK (Ins E t) (completeSignal (Z := Unit) n t) := by
  unfold completeSignal; ve_auto

theorem ve_receiveSignal (t : ObjRef) (cap : Cap) (b : Bool) : VEK (Ins E t) (receiveSignal (Z := Unit) t cap b) := by
  unfold receiveSignal; ve_auto

theorem ve_replyPush (caller callee r : ObjRef) (d : Bool) :
    VEK (Ins E callee) (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush; ve_auto

theorem ve_replyRemove (caller r : ObjRef) : VEK (Ins E caller) (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ve_auto

/-! ## Restart / cancel -/

theorem ve_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    VEK E (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread
  refine ik_bind (by ve_auto) fun _ => ik_of_ht ?_
  refine ht_bind (ht_setThreadState_x t _) fun _ => ?_
  exact ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ht_possibleSwitchTo t

theorem ve_restartThreadIfNoFault (t : ObjRef) : VEK E (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault
  refine ik_bind (by ve_auto) fun _ => ?_
  split
  · exact ik_of_ht (ht_bind (ht_setThreadState_x t _) fun _ =>
      ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ht_possibleSwitchTo t)
  · ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_removeAndRestartNtfnQueuedThread _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_restartThreadIfNoFault _)

theorem ve_removeAndRestartEpQueuedThread (t ep : ObjRef) : VEK E (removeAndRestartEpQueuedThread (Z := Unit) t ep) := by
  unfold removeAndRestartEpQueuedThread; ve_auto

theorem ve_removeAndRestartBadgedThread (t ep : ObjRef) (b : Badge) :
    VEK E (removeAndRestartBadgedThread (Z := Unit) t ep b) := by
  unfold removeAndRestartBadgedThread; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_removeAndRestartEpQueuedThread _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_removeAndRestartBadgedThread _ _ _)

theorem ve_cancelAllSignals (n : ObjRef) : VEK E (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; ve_auto

theorem ve_cancelAllIpc (ep : ObjRef) : VEK E (cancelAllIpc (Z := Unit) ep) := by
  unfold cancelAllIpc; ve_auto

theorem ve_cancelBadgedSends (ep : ObjRef) (b : Badge) : VEK E (cancelBadgedSends (Z := Unit) ep b) := by
  unfold cancelBadgedSends; ve_auto

theorem ve_suspend (t : ObjRef) : VEK E (suspend (Z := Unit) t) := by
  unfold suspend
  refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_of_ht ?_
  refine ht_bind (ht_dequeue t) fun _ => ?_
  refine ht_bind (ht_conseq (fun _ h => h) (fun _ h => ve_mono (fun u h => h.elim id Or.inr) h)
    (ht_tcbReleaseRemove (E := Ins E t) t)) fun _ => ?_
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  exact ht_setThreadState_nr t _ rfl

theorem ve_schedContextUnbindAllTcbs (p : ObjRef) : VEK E (schedContextUnbindAllTcbs (Z := Unit) p) := by
  unfold schedContextUnbindAllTcbs; ve_auto

theorem ve_unbindFromSc (t : ObjRef) : VEK E (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_cancelAllSignals _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_cancelAllIpc _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_cancelBadgedSends _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_suspend _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedContextUnbindAllTcbs _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_unbindFromSc _)

/-- **`sched_context_yield_to`**: the target is dequeued and re-enqueued. -/
theorem ve_schedContextYieldTo (p : ObjRef) : VEK E (schedContextYieldTo (Z := Unit) p) := by
  unfold schedContextYieldTo
  refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
  refine ik_bind ?_ fun _ => by ve_auto
  refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun tp => ik_bind (by ve_auto) fun _ => ?_
  split
  · refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ?_
    split
    · exact ik_of_ht (ht_bind (ht_dequeue tp) fun _ => ht_bind (ht_enqueue_x tp) fun _ => ht_ik (ik_pure _))
    · refine ik_bind (by ve_auto) fun _ => ik_bind (by ve_auto) fun _ => ik_of_ht ?_
      exact ht_bind (ht_dequeue tp) fun _ => ht_bind (ht_ik (ve_tcbSchedEnqueue _)) fun _ =>
        ht_bind (ht_enqueue_x tp) fun _ => ht_ik (by ve_auto)
  · exact ik_pure _

theorem ve_handleInterrupt (irq : Irq) : VEK E (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ve_auto

theorem ve_invokeSetDomain (t : ObjRef) (d : Domain) : VEK E (invokeSetDomain (Z := Unit) t d) := by
  unfold invokeSetDomain; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedContextYieldTo _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_handleInterrupt _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeSetDomain _ _)

/-- **`activate_thread`**: the only write of a runnable state is to ct. -/
theorem ve_activateThread : VEK E (activateThread (Z := Unit)) := by
  unfold activateThread
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  exact ht_ct (E := E) σ.curThread (by ve_auto) (by ct_auto) σ ⟨hσ, rfl⟩ x hx

/-- **`guarded_switch_to t`** (`switch_to_thread`'s form): the old ct `C` joins the exception set. -/
theorem ht_guardedSwitchTo (t C : ObjRef) :
    HT (fun s => VE E s ∧ s.curThread = C) (VE (Ins E C)) (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  refine ht_bind (htc C (by ve_auto) (by ct_auto)) fun _ => ?_
  exact ht_switchToThread t C

end

end Fl4Proofs.P3.SInvR.B8s
