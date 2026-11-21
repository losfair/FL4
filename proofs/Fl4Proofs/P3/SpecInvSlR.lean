/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **ScLive across `receive_ipc`**
(sl1 handoff 1; spec side only). Cases first (vi2's ViR / sb2's G5 shape):

* the reply-cap prefix (`cancel_ipc` of the reply's old thread: the SL family);
* a pending bound notification: `complete_signal` to the receiver (SpecInvSlS:
  the receiver in `K`, the notification's SC named by `NtfnScB`);
* a waiting sender: read BlockedOnSend, so live, so named (IfLiveT at that
  state): it joins `K`; `reply_push sender receiver` donates the sender's SC to
  the receiver (in `K`), sl1's `sl_replyPush` with `ScBackS`;
* otherwise the receiver blocks (`receive_ipc_blocked`: the SL family).
-/
import Fl4Proofs.P3.SpecInvSlS
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

section R
variable {I : ObjRef × ObjRef} {K L : List ObjRef} {t : ObjRef}

/-- A step kept by the SL, IL, ScInv and NtfnScB families (no pin). -/
theorem sapF_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h2 : ILK L m) (h3 : SInvB.SIK m)
    (h4 : NBK m) : IK (SAP I K L False t) m :=
  fun σ h x hx => ⟨⟨h1 σ h.1.1 x hx, h3 σ h.1.2.1 x hx, fun hf => hf.elim⟩, h2 σ h.2.1 x hx, h4 σ h.2.2 x hx⟩

/-- The sender arm. -/
theorem sl_recvSender (thread epptr : ObjRef) (reply : Option ObjRef) (q : List ObjRef) (ht : thread ∈ K) :
    HK (SAP I K L False t) (SL I K) (do
      NonDet.assert (q ≠ [])
      let sender ← pure (the q.head?)
      tcbEpDequeue (Z := Unit) sender epptr
      let senderState ← getThreadState sender
      let data ← match senderState with
        | .blockedOnSend _ref data => pure data
        | _ => NonDet.fail
      doIpcTransfer sender (some epptr)
        data.senderBadge data.senderCanGrant
        thread
      let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck scPtr
      let fault ← threadGet Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush sender thread (the reply) donate
        else setThreadState sender .inactive
      else do
        setThreadState sender .running
        possibleSwitchTo sender) := by
  refine shk_ikbind (sap_ik (ik_assert _) (ik_assert _) (fun _ => ik_assert _) (ik_assert _)) fun _ => ?_
  refine shk_pure_bind ?_
  refine shk_ikbind (sap_ik (sl_tcbEpDequeue _ _) (il_tcbEpDequeue _ _) (fun _ => SInvB.sb_tcbEpDequeue _ _)
    (nb_tcbEpDequeue _ _)) fun _ => ?_
  intro σ hσ x ⟨y, hy, hx⟩
  unfold getThreadState at hy
  obtain ⟨xs, hxs, rfl⟩ := mem_threadGet hy
  dsimp only at hx
  cases hs : xs.tcbState with
  | blockedOnSend r data =>
    rw [hs] at hx
    dsimp only at hx
    have h1 : SBP I (the q.head? :: K) False t σ := sbp_of_live hσ hxs (liveSt_eq hs True.intro)
    have ht' : thread ∈ the q.head? :: K := List.mem_cons_of_mem _ ht
    refine sl_tail ((?_ : HK (SBP I (the q.head? :: K) False t) (SL I (the q.head? :: K)) _) σ h1 x hx)
    refine shk_pure_bind ?_
    refine shk_ikbind (sbp_ik (sl_doIpcTransfer _ _ _ _ _) fun _ => SInvB.sb_doIpcTransfer _ _ _ _ _) fun _ => ?_
    refine shk_ikbind (sbp_ik (sl_getTcbObjRef _ _) fun _ => SInvB.sb_getTcbObjRef _ _) fun _ => ?_
    refine shk_ikbind (sbp_ik (by sl_auto) fun _ => by sb_auto) fun _ => ?_
    refine shk_ikbind (sbp_ik (sl_threadGet _ _) fun _ => SInvB.sb_threadGet _ _) fun fault => ?_
    split
    · split
      · refine shk_ikbind (sbp_ik (sl_getTcbObjRef _ _) fun _ => SInvB.sb_getTcbObjRef _ _) fun _ => ?_
        refine shk_pure_bind ?_
        exact shk_pre (sl_replyPush _ _ _ _ ht') fun s h => ⟨h.1, h.2.1.back⟩
      · exact sbp_sl (sl_setThreadState _ _)
    · exact shk_bind (sbp_sl (sl_setThreadState _ _)) fun _ => sl_possibleSwitchTo _
  | _ => rw [hs] at hx; dsimp only at hx; obtain ⟨z, hz, -⟩ := hx; exact hz.elim

/-- The `if` after the endpoint and notification reads. -/
theorem sl_recvTail (thread epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef) (ntfn : Notification)
    (ep : Endpoint) (ht : thread ∈ K) :
    HK (SAP I K L False t) (SL I K) (
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (Z := Unit) (the ntfnptr) thread
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) thread
        match ep with
        | .sendEP q => do
          NonDet.assert (q ≠ [])
          let sender ← pure (the q.head?)
          tcbEpDequeue sender epptr
          let senderState ← getThreadState sender
          let data ← match senderState with
            | .blockedOnSend _ref data => pure data
            | _ => NonDet.fail
          doIpcTransfer sender (some epptr)
            data.senderBadge data.senderCanGrant
            thread
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender thread (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking thread epptr reply) := by
  split
  · exact fun σ h x hx => (sln_completeSignal _ _ ht σ ⟨h.1.1, h.2.2⟩ x hx).1
  · refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun _ => ?_
    split
    · exact sl_recvSender _ _ _ _ ht
    · exact sap_sl (sl_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc`** of a receiver of `K`. -/
theorem sl_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (ht : thread ∈ K) :
    HK (SAP I K L False t) (SL I K) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  have hrest : ∀ (epptr : ObjRef) (reply : Option ObjRef), HK (SAP I K L False t) (SL I K) (do
      let ep ← getEndpoint (Z := Unit) epptr
      let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification thread
      let ntfn ← match ntfnptr with
        | none => pure defaultNotification
        | some p => getNotification p
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (the ntfnptr) thread
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) thread
        match ep with
        | .sendEP q => do
          NonDet.assert (q ≠ [])
          let sender ← pure (the q.head?)
          tcbEpDequeue sender epptr
          let senderState ← getThreadState sender
          let data ← match senderState with
            | .blockedOnSend _ref data => pure data
            | _ => NonDet.fail
          doIpcTransfer sender (some epptr)
            data.senderBadge data.senderCanGrant
            thread
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender thread (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking thread epptr reply) := by
    intro epptr reply
    refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun ep => ?_
    refine shk_ikbind (sap_ik (sl_getTcbObjRef _ _) (by il_auto) (fun _ => SInvB.sb_getTcbObjRef _ _)
      (nb_getTcbObjRef _ _)) fun ntfnptr => ?_
    cases ntfnptr with
    | none =>
      refine shk_ikbind (ik_pure _) fun ntfn => ?_
      exact sl_recvTail thread epptr isBlocking reply none ntfn ep ht
    | some p =>
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun ntfn => ?_
      exact sl_recvTail thread epptr isBlocking reply (some p) ntfn ep ht
  unfold receiveIpc
  cases cap
  case endpointCap epptr bd rights =>
    refine shk_ikbind (ik_pure _) fun p => ?_
    obtain ⟨epptr', rights'⟩ := p
    cases replyCap
    case replyCap r bb =>
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun tptr => ?_
      refine shk_ikbind (sap_ik (by sl_auto) (by il_auto) (fun _ => by sb_auto) (by nb_auto)) fun _ => ?_
      first
        | exact hrest epptr' (some r)
        | exact shk_pure_bind (hrest epptr' (some r))
        | exact shk_ikbind (ik_pure _) fun reply => hrest epptr' reply
    case nullCap =>
      exact shk_ikbind (ik_pure _) fun reply => hrest epptr' reply
    all_goals exact shk_fail_bind
  all_goals exact shk_fail_bind

/-! ## `do_reply_transfer` -/

/-- One step kept by the four families (no pin). -/
macro "sapf_step" : tactic => `(tactic| refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun _ => ?_)

/-- `do_reply_transfer`'s tail after the fault reply: a timeout fault of the receiver may follow. -/
theorem sl_drtTail (receiver : ObjRef) (fault : Option Fault) :
    HK (SAP I K L False t) (SL I K) (do
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
          if isEpCap tcb.tcbTimeoutHandler ∧
             ¬(fault.elim false isTimeoutFault = true)
          then handleTimeout receiver (.timeout sc.scBadge)
          else postpone scPtr) := by
  sapf_step
  sapf_step
  unfold NonDet.when
  split
  · sapf_step
    sapf_step
    sapf_step
    split
    · exact shk_ik (sl_possibleSwitchTo _) fun s h => h.1.1
    · sapf_step
      split
      · exact sl_handleTimeout _ _
      · exact shk_ik (sl_postpone _) fun s h => h.1.1
  · exact shk_pure _ fun s h => h.1.1

/-- **`do_reply_transfer`**: the receiver read BlockedOnReply is live, so named:
it joins `K` before `reply_remove` donates the reply's SC to it. -/
theorem sl_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    HK (SAP I K L False t) (SL I K) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun recvOpt => ?_
  cases recvOpt with
  | none => exact shk_pure _ fun s h => h.1.1
  | some receiver =>
    unfold NonDet.maybeM
    dsimp only
    intro σ hσ x ⟨y, hy, hx⟩
    unfold getThreadState at hy
    obtain ⟨xr, hxr, rfl⟩ := mem_threadGet hy
    dsimp only at hx
    cases hs : xr.tcbState with
    | blockedOnReply r =>
      rw [hs] at hx
      dsimp only at hx
      have h1 : SAP I (receiver :: K) (receiver :: L) False t σ := sap_of_live hσ hxr (liveSt_eq hs True.intro)
      have hm : receiver ∈ receiver :: K := List.mem_cons.2 (Or.inl rfl)
      refine sl_tail ((?_ : HK (SAP I (receiver :: K) (receiver :: L) False t) (SL I (receiver :: K)) _) σ h1 x hx)
      refine shk_ikbind (sapF_ik (ik_assert _) (ik_assert _) (ik_assert _) (ik_assert _)) fun _ => ?_
      refine shk_ikbind (sapF_ik (sl_replyRemove _ _ hm) (il_replyRemove _ _) (SInvB.sik_replyRemove _ _)
        (nb_replyRemove _ _)) fun _ => ?_
      sapf_step
      sapf_step
      refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun fault => ?_
      cases fault with
      | none =>
        dsimp only
        refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun _ => ?_
        refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun _ => ?_
        exact sl_drtTail receiver none
      | some f =>
        dsimp only
        sapf_step
        sapf_step
        sapf_step
        sapf_step
        sapf_step
        refine shk_ikbind (sapF_ik (by sl_auto) (by il_auto) (by si_auto) (by nb_auto)) fun _ => ?_
        exact sl_drtTail receiver (some f)
    | _ => rw [hs] at hx; dsimp only at hx; exact (shk_pure _ fun s h => h.1.1 : HK (SAP I K L False t) (SL I K) _) σ hσ x hx

end R

end

end Fl4Proofs.P3.SInvL
