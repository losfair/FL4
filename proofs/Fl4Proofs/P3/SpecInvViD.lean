/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi1): `VI N S b`, part D: **IPC**
(signals, blocking, reply stacks, `send_ipc` / `receive_ipc` / `do_reply_transfer`, faults
and timeouts). Every written thread is either read in a blocked state, taken from a queue,
or a caller-given thread shown not idle (`ht`). `send_ipc`'s non-call donation
`sched_context_donate (the sender_sc) dest` needs the sender bound to an SC: the pinned
thread of `VIT N S thread b` (`vi_sendIpc` is a pre/post lemma `HK (VIT N S T0 b) (VI N S b)`).
-/
import Fl4Proofs.P3.SpecInvViC
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Generic pinned combinators -/

theorem vi_of_vit {σ : State Unit} (h : VIT N S T b σ) : VI N S b σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun p o hp => ?_⟩
  have := h6 p o hp
  cases o with
  | tcb x =>
    simp only [ObjOK] at this ⊢
    refine ⟨this.1, this.2.1, fun e => ?_⟩
    subst e; rw [(this.1 rfl).2.2.1]; simp
  | _ => exact this

theorem vit_of_vi {σ : State Unit} (h : VI N S b σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ none) : VIT N S t b σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun p o hp => ?_⟩
  have := h6 p o hp
  cases o with
  | tcb x =>
    simp only [ObjOK] at this ⊢
    exact ⟨this.1, this.2.1, fun e => by subst e; exact ht x hp⟩
  | _ => exact this

/-! ## Blocking and signals -/

/-- `set_notification p (ntfn_obj_update (K o) n)`: the new queue state holds no `N`. -/
theorem vi_setNtfnObj (p : ObjRef) (n : Notification) (o : Ntfn) (h : N ∉ o.ntfnQueue) :
    IK (VIT N S T b) (setNotification (Z := Unit) p (ntfnObjUpdate (fun _ => o) n)) :=
  vi_setSimpleKo _ _ _ (by simp only [ObjOK, ntfnObjUpdate]; exact h)
macro_rules | `(tactic| vi_leaf) => `(tactic| ((with_reducible refine vi_setNtfnObj _ _ _ ?_); simp [Ntfn.ntfnQueue]))


theorem vi_sendIpcBlocked (t ep : ObjRef) (bd : Badge) (g gr c : Bool) (ht : t ≠ N) :
    IK (VIT N S T b) (sendIpcBlocked (Z := Unit) t ep bd g gr c) := by
  unfold sendIpcBlocked; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_sendIpcBlocked _ _ _ _ _ _ ?_; vi_side2))

theorem vi_receiveIpcBlocked (blk : Bool) (t ep : ObjRef) (r : Option ObjRef) (ht : t ≠ N) :
    IK (VIT N S T b) (receiveIpcBlocked (Z := Unit) blk t ep r) := by
  unfold receiveIpcBlocked; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_receiveIpcBlocked _ _ _ _ ?_; vi_side2))

theorem vi_receiveSignalBlocked (t n : ObjRef) (blk : Bool) (ht : t ≠ N) :
    IK (VI N S b) (receiveSignalBlocked (Z := Unit) t n blk) := by
  unfold receiveSignalBlocked; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_receiveSignalBlocked _ _ _ ?_; vi_side2))

theorem vi_completeSignal (n t : ObjRef) (ht : t ≠ N) : IK (VI N S b) (completeSignal (Z := Unit) n t) := by
  unfold completeSignal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_completeSignal _ _ ?_; vi_side2))

theorem vi_receiveSignal (t : ObjRef) (c : Cap) (blk : Bool) (ht : t ≠ N) :
    IK (VI N S b) (receiveSignal (Z := Unit) t c blk) := by
  unfold receiveSignal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_receiveSignal _ _ _ ?_; vi_side2))

theorem vi_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (bd : Badge) :
    IK (VI N S b) (updateWaitingNtfn (Z := Unit) n q bd) := by
  unfold updateWaitingNtfn; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateWaitingNtfn _ _ _)

theorem vi_sendSignal (n : ObjRef) (bd : Badge) : IK (VI N S b) (sendSignal (Z := Unit) n bd) := by
  unfold sendSignal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_sendSignal _ _)

/-! ## Reply stacks -/

theorem vi_bindScReply (p r : ObjRef) (hp : p ≠ S) : IK (VIT N S T b) (bindScReply (Z := Unit) p r) := by
  unfold bindScReply; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_bindScReply _ _ ?_; vi_side2))

theorem vi_replyPush (c e r : ObjRef) (d : Bool) (hc : c ≠ N) (he : e ≠ N) :
    IK (VI N S b) (replyPush (Z := Unit) c e r d) := by
  unfold replyPush
  refine vi_tsc_bind' _ fun sc1 _ h1 _ => vi_tsc_bind' _ fun sc2 _ _ _ => ?_
  cases sc1 with
  | none => vi_auto
  | some p =>
    have hp : p ≠ S := fun e' => h1 hc (by rw [e'])
    vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_replyPush _ _ _ _ ?_ ?_ <;> vi_side2))

theorem vi_replyUnlinkSc (p r : ObjRef) : IK (VIT N S T b) (replyUnlinkSc (Z := Unit) p r) := by
  unfold replyUnlinkSc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_replyUnlinkSc _ _)

theorem vi_replyRemove (c r : ObjRef) (hc : c ≠ N) : IK (VI N S b) (replyRemove (Z := Unit) c r) := by
  unfold replyRemove; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_replyRemove _ _ ?_; vi_side2))

end

end Fl4Proofs.P3.SInvI
