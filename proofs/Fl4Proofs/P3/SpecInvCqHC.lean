/-
P3 (DESIGN.md §9), invariant line G1 (ctq14, item 5 (a)): **`CKN` across the
deletion cone**: the hand lemmas above the generated family SpecInvCqHF1/2
(spec side only, outside the JAtZ cone).

`CKC C := CKN ∧ ct = C`. `sched_context_donate sc t` / `reply_remove t r`
keep it for `t ≠ C` (the donation writes `t`'s SC only); `fast_finalise` /
`finalise_cap`'s reply arm reads `t` BlockedOnReply, so `t ≠ C` by `CKN`.
Then `cap_delete_one`, `finalise_cap`, `rec_del` (`ik_lfp`), `cap_delete`,
`cap_revoke`: **every outcome** (errors from a preemption point included) has
`CKC C` (`ck_capDelete`, `ck_capRevoke`, `ck_capDeleteOne`), hence ctq11's
`CK` there (`ckn_ck`).
-/
import Fl4Proofs.P3.SpecInvCqHF2
open Classical

namespace Fl4Proofs.P3.SInvQ.R14
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- `CKN` with the current thread fixed. -/
abbrev CKC (C : ObjRef) (s : State Unit) : Prop := CKN s ∧ CTh C s

theorem ckc_of {α : Type} {C : ObjRef} {m : NonDet (State Unit) α} (h1 : CKK m) (h2 : CTK C m) : IK (CKC C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

/-- One generated callee, both halves. -/
macro "ckc_leaf" : tactic => `(tactic| ((with_reducible refine ckc_of ?_ ?_); ck_leaf; (first | ct_leaf | (ct_auto; done))))

macro "ckc_auto" : tactic => `(tactic| repeat' (first | ckc_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- **`sched_context_donate sc t`, `t ≠ C`.** -/
theorem ck_schedContextDonate_p (C sc t : ObjRef) (hne : t ≠ C) :
    IK (CKC C) (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate
  refine ik_bind (by ckc_auto) fun fromOpt => ?_
  refine ik_bind (by ckc_auto) fun _ => ?_
  refine ik_bind (by ckc_auto) fun _ => ?_
  intro s h y hy
  exact ⟨ck_threadSet_ne _ _ s (by rw [h.2]; exact hne) h.1 y hy,
    (show CTK C (threadSet (Z := Unit) (tcbSchedContextUpdate fun _ => some sc) t) by ct_auto) s h.2 y hy⟩

/-- **`reply_remove t r`, `t ≠ C`.** -/
theorem ck_replyRemove_p (C t r : ObjRef) (hne : t ≠ C) : IK (CKC C) (replyRemove (Z := Unit) t r) := by
  unfold replyRemove
  repeat' (first | (with_reducible exact ck_schedContextDonate_p C _ _ hne) | ckc_leaf | ik_step0 | (unfold NonDet.when) | (unfold NonDet.unless))

/-- `reply_remove` of a thread read BlockedOnReply: it is not `C` (`CKN`). -/
theorem ck_replyRemove_r (C t r r' : ObjRef) (σ : State Unit) (x : Tcb) (hx : σ.kheap t = some (.tcb x))
    (hs : x.tcbState = .blockedOnReply r') : IKp (CKC C) σ (replyRemove (Z := Unit) t r) := by
  intro h
  have hne : t ≠ C := by
    rintro rfl
    exact (h.1 x (by rw [h.2]; exact hx)).2 r' hs
  exact ck_replyRemove_p C t r hne σ h

/-- The reply arm of `fast_finalise` / `finalise_cap` after the TCB read. -/
macro "ck_reply_arm" : tactic => `(tactic| (
  unfold getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState <;> dsimp only
  all_goals first
    | exact ck_replyRemove_r _ _ _ _ σ x hx hs
    | exact ikp_of_ik (by ckc_leaf) σ))

theorem ck_fastFinalise (C : ObjRef) (c : Cap) (final : Bool) : IK (CKC C) (fastFinalise (Z := Unit) c final) := by
  cases c
  case nullCap => exact ik_pure _
  case replyCap r _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    refine ik_bind (by ckc_auto) fun tp => ?_
    split
    · exact ik_pure _
    · ck_reply_arm
  case endpointCap r _ _ =>
    simp only [fastFinalise]
    exact ik_when _ (by ckc_leaf)
  case notificationCap r _ _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    exact ik_bind (by ckc_leaf) fun _ => ik_bind (by ckc_leaf) fun _ => by ckc_leaf
  all_goals (simp only [fastFinalise]; exact ik_fail)

/-- **`cap_delete_one` keeps `CKC C`.** -/
theorem ck_capDeleteOne (C : ObjRef) (slot : CslotPtr) : IK (CKC C) (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  refine ik_bind (by ckc_leaf) fun cap => ?_
  refine ik_unless _ ?_
  exact ik_bind (by ckc_leaf) fun fin => ik_bind (ck_fastFinalise C cap fin) fun _ => by ckc_leaf

theorem ck_deletingIrqHandler (C : ObjRef) (irq : Irq) : IK (CKC C) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact ik_bind (ik_gets _) fun sl => ck_capDeleteOne C sl

theorem ck_finaliseCap (C : ObjRef) (c : Cap) (final : Bool) : IK (CKC C) (finaliseCap (Z := Unit) c final) := by
  cases c
  case replyCap r _ =>
    simp only [finaliseCap]
    refine ik_liftM _ ?_
    refine ik_when _ ?_
    refine ik_bind (by ckc_auto) fun tp => ?_
    split
    · exact ik_pure _
    · ck_reply_arm
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · exact ik_bind (ck_deletingIrqHandler C irq) fun _ => ik_pure _
    · exact ik_pure _
  all_goals (simp only [finaliseCap]; ckc_auto)

syntax "ckh_leaf" : tactic
macro_rules | `(tactic| ckh_leaf) => `(tactic| with_reducible exact ck_finaliseCap _ _ _)
macro_rules | `(tactic| ckh_leaf) => `(tactic| ckc_leaf)

macro "ckh_auto" : tactic => `(tactic| repeat' (first | ckh_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem ck_recDelF (C : ObjRef) {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IK (CKC C) (f k)) (k : RecDelCall) : IKE (CKC C) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (CKC C) (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ckh_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ckh_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ckh_auto
    all_goals exact hrec' _

theorem ck_recDel (C : ObjRef) (c : RecDelCall) : IKE (CKC C) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ck_recDelF C hf k) c

/-- **`cap_delete`: every outcome has `CKC C`.** -/
theorem ck_capDelete (C : ObjRef) (sl : CslotPtr) : IKE (CKC C) (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (ck_recDel C _) fun _ => ike_returnOk _

theorem ck_capRevokeF (C : ObjRef) {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (CKC C) (f k)) (sl : CslotPtr) : IKE (CKC C) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (CKC C) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first | (with_reducible exact ck_capDelete _ _) | ckh_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless))
  all_goals exact hrec' _

/-- **`cap_revoke`: every outcome has `CKC C`.** -/
theorem ck_capRevoke (C : ObjRef) (sl : CslotPtr) : IKE (CKC C) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ck_capRevokeF C hf k) sl

end

end Fl4Proofs.P3.SInvQ.R14
