/- nq3: receive_ipc (see SpecInvNtfnQG2). -/
import Fl4Proofs.P3.SpecInvNtfnQG2a
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}
/-! ## `receive_ipc`, one arm at a time -/

/-- The sender arm: the dequeued sender joins `K` (its state writes). -/
theorem nq_recvSender (thread epptr : ObjRef) (reply : Option ObjRef) (q : List ObjRef) :
    NQK Kq (do
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
  refine ik_bind (ik_assert _) fun _ => ?_
  refine ik_pure_bind ?_
  refine ik_nqhk_bind (nq_tcbEpDequeue_post _ _) fun _ => ?_
  have hs : the q.head? ∈ the q.head? :: Kq := List.mem_cons_self ..
  refine ik_bind (nq_getThreadState _) fun st => ?_
  cases st
  case blockedOnSend r data =>
    refine ik_pure_bind ?_
    refine ik_bind (nq_doIpcTransfer _ _ _ _ _) fun _ => ?_
    refine ik_bind (nq_getTcbObjRef _ _) fun scPtr => ?_
    refine ik_bind (by nq2_auto) fun _ => ?_
    refine ik_bind (nq_threadGet _ _) fun fault => ?_
    split
    · split
      · exact ik_bind (nq_getTcbObjRef _ _) fun _ => ik_pure_bind (nq_replyPush _ _ _ _ hs)
      · exact nq_setThreadState _ _ hs (fun h => h)
    · exact ik_bind (nq_setThreadState _ _ hs (fun h => h)) fun _ => nq_possibleSwitchTo _
  all_goals exact ik_fail_bind

/-- The reply-cap prefix of `receive_ipc`. -/
theorem nq_recvReply (thread : ObjRef) (replyCap : Cap) :
    NQK Kq (match replyCap with
      | .replyCap r _ => do
        let tptr ← getReplyTcb (Z := Unit) r
        NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) <| cancelIpc (the tptr)
        pure (some r)
      | .nullCap => pure none
      | _ => NonDet.fail) := by
  split
  · refine ik_bind (by nq2_auto) fun tptr => ik_bind ?_ fun _ => ik_pure _
    unfold NonDet.when
    split
    · exact nq_cancelIpc _
    · exact ik_pure _
  · exact ik_pure _
  · exact ik_fail

/-- The `if` of `receive_ipc` (after the endpoint and notification reads). -/
theorem nq_recvTail (thread epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef) (ntfn : Notification)
    (ep : Endpoint) (ht : thread ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ thread))) (
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
  · exact hk_post (hk_of_ik (nq_completeSignal _ _)) nq_filter_post
  · refine hk_bind (hk_of_ik ?_) fun _ => ?_
    · unfold NonDet.when
      split
      · exact nq_maybeReturnSc _ _
      · exact ik_pure _
    split
    · exact hk_post (hk_of_ik (nq_recvSender _ _ _ _)) nq_filter_post
    · exact nq_receiveIpcBlocked _ _ _ _ ht

theorem hk_nil_of_fail {P Q : State Unit → Prop} {α β : Type} {g : α → NonDet (State Unit) β} :
    HK P Q ((NonDet.fail : NonDet (State Unit) α) >>= g) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

theorem hk_fail' {P Q : State Unit → Prop} {α : Type} : HK P Q (NonDet.fail : NonDet (State Unit) α) :=
  fun _ _ _ hy => hy.elim

/-- `receive_ipc` of a thread of `K`: it may block on the endpoint, so it leaves `K`.
(Each `let x ← match …` of its `do` block is a join point: split on the
discriminant first, then the bind unifies arm by arm.) -/
theorem nq_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (ht : thread ∈ Kq) :
    HK (NQ Kq) (NQ (Kq.filter (· ≠ thread))) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  have hrest : ∀ (epptr : ObjRef) (reply : Option ObjRef), HK (NQ Kq) (NQ (Kq.filter (· ≠ thread))) (do
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
    refine hk_bind (hk_of_ik (by nq2_auto)) fun ep => ?_
    refine hk_bind (hk_of_ik (nq_getTcbObjRef _ _)) fun ntfnptr => ?_
    cases ntfnptr with
    | none =>
      refine hk_bind (hk_of_ik (ik_pure _)) fun ntfn => ?_
      exact nq_recvTail thread epptr isBlocking reply none ntfn ep ht
    | some p =>
      refine hk_bind (hk_of_ik ?_) fun ntfn => ?_
      · nq2_auto
      exact nq_recvTail thread epptr isBlocking reply (some p) ntfn ep ht
  unfold receiveIpc
  cases cap
  case endpointCap epptr bd rights =>
    refine hk_bind (hk_of_ik (ik_pure _)) fun p => ?_
    obtain ⟨epptr', rights'⟩ := p
    cases replyCap
    case replyCap r b =>
      refine hk_bind (hk_of_ik (by nq2_auto)) fun tptr => ?_
      refine hk_bind (hk_of_ik ?_) fun _ => ?_
      · unfold NonDet.when
        split
        · exact nq_cancelIpc _
        · exact ik_pure _
      first
        | exact hrest epptr' (some r)
        | exact hk_pure_bind (hrest epptr' (some r))
        | exact hk_bind (hk_of_ik (ik_pure _)) fun reply => hrest epptr' reply
    case nullCap =>
      exact hk_bind (hk_of_ik (ik_pure _)) fun reply => hrest epptr' reply
    all_goals exact hk_nil_of_fail
  all_goals exact hk_nil_of_fail

end

end Fl4Proofs.P3.SInv
