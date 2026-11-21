/- nq3: do_reply_transfer (see SpecInvNtfnQG2). -/
import Fl4Proofs.P3.SpecInvNtfnQG2a
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}
/-! ## `do_reply_transfer` -/

/-- The timeout tail of `do_reply_transfer`: only the receiver may block. -/
theorem nq_replyTail (receiver : ObjRef) (fault : Option Fault) (hr : receiver ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ receiver))) (do
        let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
        let state ← getThreadState receiver
        NonDet.when (scOpt ≠ none ∧ runnable state) <| do
          let scPtr ← NonDet.assertOpt scOpt
          let sc ← getSchedContext scPtr
          let curtime ← NonDet.gets fun s : State Unit => s.curTime
          if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
          then possibleSwitchTo receiver
          else do
            let tcb ← NonDet.getsThe (getTcb receiver)
            if isEpCap tcb.tcbTimeoutHandler ∧ ¬(fault.elim false isTimeoutFault = true)
            then handleTimeout receiver (.timeout sc.scBadge)
            else postpone scPtr) := by
  refine hk_bind (hk_of_ik (by nq2_auto)) fun scOpt => ?_
  refine hk_bind (hk_of_ik (by nq2_auto)) fun st => ?_
  unfold NonDet.when
  split
  · refine hk_bind (hk_of_ik (by nq2_auto)) fun scPtr => hk_bind (hk_of_ik (by nq2_auto)) fun sc =>
      hk_bind (hk_of_ik (by nq2_auto)) fun ct => ?_
    split
    · exact hk_post (hk_of_ik (by nq2_auto)) nq_filter_post
    · refine hk_bind (hk_of_ik (by nq2_auto)) fun tcb => ?_
      split
      · exact nq_handleTimeout receiver _ hr
      · exact hk_post (hk_of_ik (by nq2_auto)) nq_filter_post
  · exact hk_post (hk_of_ik (ik_pure _)) nq_filter_post

theorem nq_filter_cons_sub {J : List ObjRef} {r : ObjRef} (hJ : ∀ u ∈ J, u ∈ Kq) (hn : ∀ u ∈ J, u ≠ r) :
    ∀ u ∈ J, u ∈ (r :: Kq).filter (· ≠ r) := by
  intro u hu
  simp only [List.mem_filter, List.mem_cons, decide_eq_true_eq]
  exact ⟨Or.inr (hJ u hu), hn u hu⟩

set_option maxHeartbeats 4000000 in
/-- `do_reply_transfer`: the receiver is read BlockedOnReply (so joins `K`; it is
no thread of `J`, none of which is BlockedOnReply); its timeout fault may block
it, so the post keeps `J ⊆ K` only. -/
theorem nq_doReplyTransfer (J : List ObjRef) (hJ : ∀ u ∈ J, u ∈ Kq) (sender reply : ObjRef) (grant : Bool) :
    HK (fun σ => NQ Kq σ ∧ NoRpl J σ) (NQ J) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine hk_bind (hk_of_ik (by repeat' (first | ik_step0 | ik_unfold))) fun ro => ?_
  cases ro with
  | none => exact fun σ h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact nq_mono h.1 hJ
  | some receiver =>
    show HK _ _ (getThreadState (Z := Unit) receiver >>= _)
    unfold getThreadState
    refine hk_threadGet_bind fun σ x hx => ?_
    cases hs : x.tcbState
    case blockedOnReply r' =>
      dsimp only
      intro ⟨hσ, hR⟩
      have hnJ : ∀ u ∈ J, u ≠ receiver := by
        intro u hu e
        subst e
        exact hR u hu x hx (by rw [hs]; trivial)
      have hσK : NQ (receiver :: Kq) σ := nq_consR hσ hx (by rw [hs]; exact fun h => h) (by rw [hs]; rfl)
      have hrK : receiver ∈ receiver :: Kq := List.mem_cons_self ..
      refine fun y hy => nq_mono ((?_ : HK (NQ (receiver :: Kq))
        (NQ ((receiver :: Kq).filter (· ≠ receiver))) _) σ hσK y hy) (nq_filter_cons_sub hJ hnJ)
      refine hk_bind (hk_of_ik (ik_assert _)) fun _ => hk_bind (hk_of_ik (nq_replyRemove _ _ hrK)) fun _ =>
        hk_bind (hk_of_ik (by nq2_auto)) fun _ => hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
      refine hk_threadGet_bind fun σ1 x1 hx1 => ?_
      (try dsimp only)
      refine hkp_of_hk ?_ σ1
      cases hf : x1.tcbFault with
      | none =>
        refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => ?_
        refine hk_bind (hk_of_ik (nq_setThreadState receiver .running hrK (fun h => h))) fun _ => ?_
        exact nq_replyTail receiver none hrK
      | some f =>
        refine hk_bind (hk_of_ik (by nq2_auto)) fun _ => hk_bind (hk_of_ik (by nq2_auto)) fun _ =>
          hk_bind (hk_of_ik (by nq2_auto)) fun _ => hk_bind (hk_of_ik (by nq2_auto)) fun rs => ?_
        refine hk_bind (hk_of_ik (nq_threadSet (fun tcb => { tcb with tcbFault := none }) receiver (fun _ => rfl)))
          fun _ => ?_
        refine hk_bind (hk_of_ik (nq_setThreadState receiver (if rs then .restart else .inactive) hrK
          (by cases rs <;> exact fun h => h))) fun _ => ?_
        exact nq_replyTail receiver (some f) hrK
    all_goals
      dsimp only
      exact fun h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact nq_mono h.1 hJ


end

end Fl4Proofs.P3.SInv
