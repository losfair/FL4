
/- fo1: generated frames `OIK Qo` (sg1's SpecInvSgI4 renamed, the owner / retype / detype writers removed; see SpecInvFoG1). -/
import Fl4Proofs.P3.SpecInvFoG3
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Qo : Option ObjRef}

theorem oi_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : OIK Qo (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; oi_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getExtraCptrs _ _)

theorem oi_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : OIKE Qo (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupSlotForThread _ _)

theorem oi_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : OIKE Qo (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupCapAndSlot _ _)

theorem oi_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : OIKE Qo (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupExtraCaps _ _ _)

theorem oi_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : OIKE Qo m) : OIK Qo (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_emptyOnFailure _ ?_)

theorem oi_loadCapTransfer (buffer : ObjRef) : OIK Qo (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadCapTransfer _)

theorem oi_lookupCap (thread : ObjRef) (ref : CapRef) : OIKE Qo (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupCap _ _)

theorem oi_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : OIKE Qo m) : OIKE Qo (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_unifyFailure _ ?_)

theorem oi_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : OIK Qo (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getReceiveSlots _ _)

theorem oi_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : OIKE Qo m) : OIK Qo (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_constOnFailure _ _ ?_)

theorem oi_deriveCap (slot : CslotPtr) (cap : Cap) : OIKE Qo (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deriveCap _ _)

theorem oi_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : OIK Qo (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setExtraBadge _ _ _)

theorem oi_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      OIK Qo (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; oi_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => oi_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | oi_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_transferCapsLoop _ _ _ _ _ _)

theorem oi_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : OIK Qo (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_transferCaps _ _ _ _ _)

theorem oi_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : OIK Qo (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doNormalTransfer _ _ _ _ _ _ _)

theorem oi_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : OIK Qo (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doIpcTransfer _ _ _ _ _)

theorem oi_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : OIK Qo (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyPush _ _ _ _)

theorem oi_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : OIK Qo (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_orderedInsert _ _ _ _)

theorem oi_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : OIK Qo (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbAppend _ _)

theorem oi_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : OIK Qo (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbEpAppend _ _ _)

theorem oi_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : OIK Qo (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendIpcBlocked _ _ _ _ _ _)

theorem oi_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : OIK Qo (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendIpc _ _ _ _ _ _ _ _)

theorem oi_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : OIK Qo (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendFaultIpc _ _ _ _)

theorem oi_handleTimeout (tptr : ObjRef) (ex : Fault) : OIK Qo (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleTimeout _ _)

theorem oi_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : OIK Qo (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_readyTimesAppend _ _)

theorem oi_tcbReleaseEnqueue (tcbPtr : ObjRef) : OIK Qo (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseEnqueue _)

theorem oi_postpone (scPtr : ObjRef) : OIK Qo (postpone (Z := Unit) scPtr) := by
  unfold postpone; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_postpone _)

theorem oi_endTimeslice (canTimeout : Bool) : OIK Qo (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_endTimeslice _)

theorem oi_getRefills (scPtr : ObjRef) : OIK Qo (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefills _)

theorem oi_refillSize (scPtr : ObjRef) : OIK Qo (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillSize _)

theorem oi_refillSingle (scPtr : ObjRef) : OIK Qo (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillSingle _)

theorem oi_getRefillTail (scPtr : ObjRef) : OIK Qo (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefillTail _)

theorem oi_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : OIK Qo (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillAddTail _ _)

theorem oi_refillFull (scPtr : ObjRef) : OIK Qo (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillFull _)

theorem oi_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : OIK Qo (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRefillTl _ _)

theorem oi_scheduleUsed (scPtr : ObjRef) (new : Refill) : OIK Qo (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleUsed _ _)

theorem oi_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : OIK Qo (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_chargeEntireHeadRefill _ _)

theorem oi_handleOverrun (scPtr : ObjRef) (usage : Ticks) : OIK Qo (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleOverrun _ _)

theorem oi_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : OIK Qo (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_mergeNonoverlappingHeadRefill _)

theorem oi_headInsufficientLoop (scPtr : ObjRef) : OIK Qo (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_headInsufficientLoop _)

theorem oi_refillBudgetCheck (usage : Ticks) : OIK Qo (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillBudgetCheck _)

theorem oi_refillResetRr (cscPtr : ObjRef) : OIK Qo (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillResetRr _)

theorem oi_chargeBudget (consumed : Ticks) (canTimeout : Bool) : OIK Qo (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_chargeBudget _ _)

theorem oi_checkBudget  : OIK Qo (checkBudget (Z := Unit)) := by
  unfold checkBudget; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkBudget)

theorem oi_checkBudgetRestart  : OIK Qo (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkBudgetRestart)

theorem oi_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : OIK Qo m) : OIK Qo (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_checkCapAt _ _ _ ?_)

theorem oi_checkDomainTime  : OIK Qo (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkDomainTime)

theorem oi_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : OIKE Qo (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkHandlerEp _ _)

theorem oi_checkPrio (newPrio : Data) (authTcb : ObjRef) : OIKE Qo (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkPrio _ _)

theorem oi_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : OIKE Qo (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_checkValidIpcBuffer _ _)

theorem oi_nextDomain  : OIK Qo (nextDomain (Z := Unit)) := by
  unfold nextDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_nextDomain)

theorem oi_switchToIdleThread  : OIK Qo (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchToIdleThread)

theorem oi_refillBudgetCheckRoundRobin (usage : Ticks) : OIK Qo (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillBudgetCheckRoundRobin _)

theorem oi_commitTime  : OIK Qo (commitTime (Z := Unit)) := by
  unfold commitTime; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_commitTime)

theorem oi_schedContextResume (scPtr : ObjRef) : OIK Qo (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextResume _)

theorem oi_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : OIK Qo (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeDonateSc _ _)

theorem oi_completeSignal (ntfnptr tptr : ObjRef) : OIK Qo (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_completeSignal _ _)

theorem oi_copyGlobalMappings (newPm : ObjRef) : OIK Qo (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_copyGlobalMappings _)

theorem oi_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : OIK Qo (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_createCap _ _ _ _ _)

theorem oi_dataToObjType (type : Data) : OIKE Qo (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_dataToObjType _)

theorem oi_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : OIKE Qo (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeBindNotification _ _)

theorem oi_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OIKE Qo (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupPivotSlot _ _ _)

theorem oi_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OIKE Qo (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupSourceSlot _ _ _)

theorem oi_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : OIKE Qo (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeCnodeInvocation _ _ _ _)

theorem oi_slotCapLongRunningDelete (slot : CslotPtr) : OIK Qo (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_slotCapLongRunningDelete _)

theorem oi_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OIKE Qo (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvF
