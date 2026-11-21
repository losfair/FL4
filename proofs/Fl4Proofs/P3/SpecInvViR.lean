/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi2): `VI N S b`, part R: **receive_ipc**,
one arm at a time (nq3's recipe: every `let x ← match …` of its `do` block is a join point,
so the cap / reply cap / bound notification are split first and the shared continuation is
stated once on its literal term). The receiver `thread ≠ N` (`ht`); the sender is taken from
the endpoint queue, so it is not `N` (`vi_epDeq_bind`).
-/
import Fl4Proofs.P3.SpecInvViE
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-- The sender arm. -/
theorem vi_recvSender (thread epptr : ObjRef) (reply : Option ObjRef) (q : List ObjRef) (ht : thread ≠ N) :
    IK (VI N S b) (do
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
  refine vi_epDeq_bind _ _ fun hs => ?_
  refine ik_bind (vi_getThreadState _) fun st => ?_
  cases st
  case blockedOnSend r data =>
    refine ik_pure_bind ?_
    refine ik_bind (vi_doIpcTransfer _ _ _ _ _) fun _ => ?_
    refine ik_bind (vi_getTcbObjRef _ _) fun scPtr => ?_
    refine ik_bind (by vi_auto) fun _ => ?_
    refine ik_bind (vi_threadGet _ _) fun fault => ?_
    split
    · split
      · exact ik_bind (vi_getTcbObjRef _ _) fun _ => ik_pure_bind (vi_replyPush _ _ _ _ hs ht)
      · exact vi_setThreadState _ _ fun e => absurd e hs
    · exact ik_bind (vi_setThreadState _ _ fun e => absurd e hs) fun _ => vi_possibleSwitchTo _
  all_goals exact vi_fail_bind

/-- The reply-cap prefix. -/
theorem vi_recvReply (thread : ObjRef) (replyCap : Cap) :
    IK (VI N S b) (match replyCap with
      | .replyCap r _ => do
        let tptr ← getReplyTcb (Z := Unit) r
        NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) <| cancelIpc (the tptr)
        pure (some r)
      | .nullCap => pure none
      | _ => NonDet.fail) := by
  split
  · refine ik_bind (by vi_auto) fun tptr => ik_bind ?_ fun _ => ik_pure _
    unfold NonDet.when
    split
    · exact vi_cancelIpc _
    · exact ik_pure _
  · exact ik_pure _
  · exact ik_fail

/-- The `if` after the endpoint and notification reads. -/
theorem vi_recvTail (thread epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef) (ntfn : Notification)
    (ep : Endpoint) (ht : thread ≠ N) :
    IK (VI N S b) (
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
  · exact vi_completeSignal _ _ ht
  · refine ik_bind ?_ fun _ => ?_
    · unfold NonDet.when
      split
      · exact vi_maybeReturnSc _ _ ht
      · exact ik_pure _
    split
    · exact vi_recvSender _ _ _ _ ht
    · exact vi_receiveIpcBlocked _ _ _ _ ht

/-- **`receive_ipc`** of a receiver that is not `N`. -/
theorem vi_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (ht : thread ≠ N) :
    IK (VI N S b) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  have hrest : ∀ (epptr : ObjRef) (reply : Option ObjRef), IK (VI N S b) (do
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
    refine ik_bind (by vi_auto) fun ep => ?_
    refine ik_bind (vi_getTcbObjRef _ _) fun ntfnptr => ?_
    cases ntfnptr with
    | none =>
      refine ik_bind (ik_pure _) fun ntfn => ?_
      exact vi_recvTail thread epptr isBlocking reply none ntfn ep ht
    | some p =>
      refine ik_bind ?_ fun ntfn => ?_
      · vi_auto
      exact vi_recvTail thread epptr isBlocking reply (some p) ntfn ep ht
  unfold receiveIpc
  cases cap
  case endpointCap epptr bd rights =>
    refine ik_bind (ik_pure _) fun p => ?_
    obtain ⟨epptr', rights'⟩ := p
    cases replyCap
    case replyCap r bb =>
      refine ik_bind (by vi_auto) fun tptr => ?_
      refine ik_bind ?_ fun _ => ?_
      · unfold NonDet.when
        split
        · exact vi_cancelIpc _
        · exact ik_pure _
      first
        | exact hrest epptr' (some r)
        | exact ik_pure_bind (hrest epptr' (some r))
        | exact ik_bind (ik_pure _) fun reply => hrest epptr' reply
    case nullCap =>
      exact ik_bind (ik_pure _) fun reply => hrest epptr' reply
    all_goals exact vi_fail_bind
  all_goals exact vi_fail_bind
macro_rules | `(tactic| vi_leaf) => `(tactic| (with_reducible refine vi_receiveIpc _ _ _ _ ?_; vi_side2))

end

end Fl4Proofs.P3.SInvI
