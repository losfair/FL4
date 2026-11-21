/-
P3 (DESIGN.md §9), invariant line G1 (rd8q): **`VE` across the SC-binding writers.**

* **`UB t s`** (`t` holds no TCB or an unbound one: not schedulable), `ub_nsched`, `ve_drop_ub`,
  `setObject_out`, `ub_upd`, frames `ub_threadSet` (binding kept-or-cleared, clear-only),
  `ub_updateSchedContext`, `ub_kh`.
* **`ve_schedContextUnbindTcb`** (dequeue, release-remove, clear the binding: the unbound thread
  leaves the exception set), **`ve_schedContextDonate`** (`t ∈ E`: the donor is unbound, the
  receiver stays exempt; l4v: the callers make the receiver runnable and then
  `possible_switch_to` it), **`ve_schedContextResume`**, **`ve_schedContextBindTcb`** (the
  bound thread is enqueued when schedulable), **`ve_maybeDonateSc`** (`t ∈ E`), **`ve_awaken`**.
-/
import Fl4Proofs.P3.SpecInvRd8qW
open Classical

namespace Fl4Proofs.P3.SInvR.B8q
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_tcbReleaseEnqueue _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_tcbReleaseDequeue)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_postpone _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setDomain _ _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_setPriority _ _)

/-! ## Unbound threads -/

/-- `t` holds no TCB or an unbound one. -/
def UB (t : ObjRef) (s : State Unit) : Prop := ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = none

theorem ub_nsched {t : ObjRef} {s : State Unit} (h : UB t s) : schedulable t s = false := by
  cases e : schedulable t s
  · rfl
  · obtain ⟨x, scp, -, -, hx, hsc, -⟩ := Sched.schedulable_inv e
    rw [h x hx] at hsc; cases hsc

theorem ve_drop_ub {t : ObjRef} {s : State Unit} (h : VE (Ins E t) s) (hu : UB t s) : VE E s :=
  ve_drop h fun hs => by rw [ub_nsched hu] at hs; cases hs

theorem ub_kh {t : ObjRef} {s s' : State Unit} (h : UB t s) (hk : s'.kheap = s.kheap) : UB t s' :=
  fun x hx => h x (by rw [← hk]; exact hx)

theorem setObject_out {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) : x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at hx
  obtain ⟨w, hw, hx⟩ := hx
  obtain ⟨hk, hs⟩ := mem_getObject hw
  obtain ⟨y1, y2⟩ := w
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]

theorem ub_upd {t p : ObjRef} {o : KernelObject} {σ : State Unit} (h : UB t σ)
    (hp : p = t → ∀ y, o = .tcb y → y.tcbSchedContext = none) :
    UB t { σ with kheap := Function.update σ.kheap p (some o) } := by
  intro x hx
  dsimp only at hx
  rw [Function.update_apply] at hx
  split_ifs at hx with e
  · exact hp e.symm x (Option.some.inj hx)
  · exact h x hx

/-- A TCB write keeping an absent binding absent. -/
theorem ub_threadSet (t : ObjRef) (f : Tcb → Tcb) (u : ObjRef)
    (hf : ∀ x, x.tcbSchedContext = none → (f x).tcbSchedContext = none) : IK (UB t) (threadSet (Z := Unit) f u) := by
  unfold threadSet
  refine ik_getsThe_bind fun a σ ha => ?_
  intro hσ x hx
  rw [setObject_out hx]
  refine ub_upd hσ fun e y hy => ?_
  cases hy
  subst e
  exact hf a (hσ a (getTcb_kheap ha))

/-- A TCB write clearing the binding of `u`. -/
theorem ub_threadSet_clr (f : Tcb → Tcb) (u : ObjRef) (hf : ∀ x, (f x).tcbSchedContext = none)
    (σ : State Unit) : ∀ x, x ∈ (threadSet (Z := Unit) f u σ).1 → UB u x.2 := by
  unfold threadSet
  intro x ⟨y, hy, hx⟩
  unfold NonDet.getsThe at hy
  cases e : getTcb u σ with
  | none => rw [e] at hy; exact hy.elim
  | some a =>
    rw [e] at hy
    rw [Set.mem_singleton_iff.1 hy] at hx
    rw [setObject_out hx]
    intro x' hx'
    dsimp only at hx'
    rw [Function.update_apply, if_pos rfl] at hx'
    cases Option.some.inj hx'
    exact hf a

theorem ub_updateSchedContext (t p : ObjRef) (f : SchedContext → SchedContext) :
    IK (UB t) (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rw [setObject_out hx]
    exact ub_upd hσ fun _ y e => by cases e
  · exact hx.elim

theorem kh_testReschedule (u : ObjRef) (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) :
    IK (SInvQ.KH K D I) (testReschedule (Z := Unit) u) := by
  unfold testReschedule
  repeat' (first | (with_reducible exact SInvQ.kh_rescheduleRequired _ _ _) | ik_step0 | ik_unfold)

/-! ## Unbind / donate / resume / bind -/

/-- `t` dequeued, released-removed and unbound: it leaves the exception set (the tail of
`sched_context_unbind_tcb` and of the donor half of `sched_context_donate`). -/
theorem ht_unbindTail (t : ObjRef) {β : Type} (k : NonDet (State Unit) β) (hk : IK (VE (Ins E t)) k)
    (hku : IK (UB t) k) :
    HT (VE E) (VE E) (tcbSchedAction (Z := Unit) tcbSchedDequeue t >>= fun _ => tcbReleaseRemove (Z := Unit) t >>=
      fun _ => setTcbObjRef (Z := Unit) tcbSchedContextUpdate t none >>= fun _ => k) := by
  refine ht_bind (ht_dequeue t) fun _ => ?_
  refine ht_bind (ht_conseq (fun _ h => h) (fun _ h => ve_mono (fun u h => h.elim id Or.inr) h)
    (ht_tcbReleaseRemove (E := Ins E t) t)) fun _ => ?_
  refine ht_bind (R := fun s => VE (Ins E t) s ∧ UB t s) ?_ fun _ => ?_
  · intro σ hσ x hx
    exact ⟨ve_threadSet (E := Ins E t) (tcbSchedContextUpdate fun _ => none) t (fun _ => ⟨rfl, Or.inr rfl⟩) σ hσ x hx,
      ub_threadSet_clr (tcbSchedContextUpdate fun _ => none) t (fun _ => rfl) σ x hx⟩
  · intro σ ⟨hσ, hu⟩ x hx
    exact ve_drop_ub (hk σ hσ x hx) (hku σ hu x hx)

theorem ve_schedContextUnbindTcb (p : ObjRef) : VEK E (schedContextUnbindTcb (Z := Unit) p) := by
  unfold schedContextUnbindTcb
  refine ik_bind (by ve_auto) fun sc => ik_bind (by ve_auto) fun t => ik_bind (by ve_auto) fun cur => ?_
  refine ik_bind (ve_when_rr _) fun _ => ik_of_ht ?_
  exact ht_unbindTail t _ (ve_updateSchedContext _ _ fun _ h => h) (ub_updateSchedContext t _ _)

/-- **`sched_context_donate p t`** keeps `VE E` when the receiver `t` is exempt. -/
theorem ve_schedContextDonate (p t : ObjRef) (hE : E t) : VEK E (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate
  refine ik_bind (by ve_auto) fun fo => ik_bind ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · refine ik_bind (by ve_auto) fun f => ik_of_ht ?_
      exact ht_unbindTail f _ (by ve_auto) (fun σ hu x hx =>
        ub_kh hu (kh_testReschedule f σ.kheap σ.curDomain σ.idleThread σ ⟨rfl, rfl, rfl⟩ x hx).1)
    · exact ik_pure _
  · refine ik_bind (ve_updateSchedContext _ _ fun _ h => h) fun _ => ?_
    intro σ hσ x hx
    exact ve_mono (fun u h => h.elim id fun e => e ▸ hE) (ht_threadSet_x _ t σ hσ x hx)

theorem ve_schedContextResume (p : ObjRef) : VEK E (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedContextUnbindTcb _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_schedContextResume _)

/-- **`sched_context_bind_tcb p t`**: `t` is bound, then enqueued when schedulable. -/
theorem ve_schedContextBindTcb (p t : ObjRef) : VEK E (schedContextBindTcb (Z := Unit) p t) := by
  unfold schedContextBindTcb
  refine ik_of_ht (ht_bind (ht_threadSet_x _ t) fun _ => ?_)
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  refine ht_bind (ht_ik (by ve_auto)) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  try dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · obtain ⟨z, hz, hx⟩ := hx
    exact ve_rescheduleRequired z.2 (ht_enqueue_x t σ hσ z hz) x hx
  · rename_i hn
    rw [Set.mem_singleton_iff.1 hx]
    exact ve_drop hσ fun hs => absurd hs hn

/-- **`maybe_donate_sc t n`** keeps `VE E` when `t` is exempt. -/
theorem ve_maybeDonateSc (t n : ObjRef) (hE : E t) : VEK E (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  refine ik_bind (by ve_auto) fun o => ?_
  unfold NonDet.when
  split
  · refine ik_bind (by ve_auto) fun so => ?_
    rcases so with _ | p
    · try dsimp only [NonDet.maybeM]
      exact ik_pure _
    · try dsimp only [NonDet.maybeM]
      refine ik_bind (by ve_auto) fun st => ?_
      try unfold NonDet.when
      split
      · exact ik_bind (ve_schedContextDonate _ t hE) fun _ => ve_schedContextResume _
      · exact ik_pure _
  · exact ik_pure _

theorem ve_awaken : VEK E (awaken (Z := Unit)) := by
  unfold awaken; ve_auto

end

end Fl4Proofs.P3.SInvR.B8q
