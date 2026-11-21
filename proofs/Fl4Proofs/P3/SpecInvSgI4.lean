/- sg1: idle-thread frame lemmas `IdK t` (ut7's SpecInvUtNK4 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvSgI3
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem idk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : IdK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; idk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getExtraCptrs _ _)

theorem idk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : IdKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupSlotForThread _ _)

theorem idk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : IdKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupCapAndSlot _ _)

theorem idk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : IdKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupExtraCaps _ _ _)

theorem idk_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IdKE N m) : IdK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_emptyOnFailure _ ?_)

theorem idk_loadCapTransfer (buffer : ObjRef) : IdK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_loadCapTransfer _)

theorem idk_lookupCap (thread : ObjRef) (ref : CapRef) : IdKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupCap _ _)

theorem idk_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IdKE N m) : IdKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_unifyFailure _ ?_)

theorem idk_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : IdK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getReceiveSlots _ _)

theorem idk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IdKE N m) : IdK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_constOnFailure _ _ ?_)

theorem idk_deriveCap (slot : CslotPtr) (cap : Cap) : IdKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deriveCap _ _)

theorem idk_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : IdK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setExtraBadge _ _ _)

theorem idk_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      IdK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; idk_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => idk_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | idk_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_transferCapsLoop _ _ _ _ _ _)

theorem idk_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : IdK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_transferCaps _ _ _ _ _)

theorem idk_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : IdK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_doNormalTransfer _ _ _ _ _ _ _)

theorem idk_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IdK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_doIpcTransfer _ _ _ _ _)

theorem idk_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : IdK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyPush _ _ _ _)

theorem idk_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : IdK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_orderedInsert _ _ _ _)

theorem idk_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : IdK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbAppend _ _)

theorem idk_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : IdK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbEpAppend _ _ _)

theorem idk_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : IdK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_sendIpcBlocked _ _ _ _ _ _)

theorem idk_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IdK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_sendIpc _ _ _ _ _ _ _ _)

theorem idk_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IdK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_sendFaultIpc _ _ _ _)

theorem idk_handleTimeout (tptr : ObjRef) (ex : Fault) : IdK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleTimeout _ _)

theorem idk_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : IdK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_readyTimesAppend _ _)

theorem idk_tcbReleaseEnqueue (tcbPtr : ObjRef) : IdK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbReleaseEnqueue _)

theorem idk_postpone (scPtr : ObjRef) : IdK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_postpone _)

theorem idk_endTimeslice (canTimeout : Bool) : IdK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_endTimeslice _)

theorem idk_getRefills (scPtr : ObjRef) : IdK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getRefills _)

theorem idk_refillSize (scPtr : ObjRef) : IdK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillSize _)

theorem idk_refillSingle (scPtr : ObjRef) : IdK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillSingle _)

theorem idk_getRefillTail (scPtr : ObjRef) : IdK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getRefillTail _)

theorem idk_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : IdK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillAddTail _ _)

theorem idk_refillFull (scPtr : ObjRef) : IdK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillFull _)

theorem idk_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : IdK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateRefillTl _ _)

theorem idk_scheduleUsed (scPtr : ObjRef) (new : Refill) : IdK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_scheduleUsed _ _)

theorem idk_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : IdK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_chargeEntireHeadRefill _ _)

theorem idk_handleOverrun (scPtr : ObjRef) (usage : Ticks) : IdK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleOverrun _ _)

theorem idk_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : IdK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_mergeNonoverlappingHeadRefill _)

theorem idk_headInsufficientLoop (scPtr : ObjRef) : IdK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_headInsufficientLoop _)

theorem idk_refillBudgetCheck (usage : Ticks) : IdK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillBudgetCheck _)

theorem idk_refillResetRr (cscPtr : ObjRef) : IdK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillResetRr _)

theorem idk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IdK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_chargeBudget _ _)

theorem idk_checkBudget  : IdK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkBudget)

theorem idk_checkBudgetRestart  : IdK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkBudgetRestart)

theorem idk_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : IdK N m) : IdK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_checkCapAt _ _ _ ?_)

theorem idk_checkDomainTime  : IdK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkDomainTime)

theorem idk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : IdKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkHandlerEp _ _)

theorem idk_checkPrio (newPrio : Data) (authTcb : ObjRef) : IdKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkPrio _ _)

theorem idk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : IdKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_checkValidIpcBuffer _ _)

theorem idk_nextDomain  : IdK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_nextDomain)

theorem idk_switchToThread (t : ObjRef) : IdK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_switchToThread _)

theorem idk_guardedSwitchTo (thread : ObjRef) : IdK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_guardedSwitchTo _)

theorem idk_switchToIdleThread  : IdK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_switchToIdleThread)

theorem idk_chooseThread  : IdK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_chooseThread)

theorem idk_refillBudgetCheckRoundRobin (usage : Ticks) : IdK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillBudgetCheckRoundRobin _)

theorem idk_commitTime  : IdK N (commitTime (Z := Unit)) := by
  unfold commitTime; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_commitTime)

theorem idk_schedContextResume (scPtr : ObjRef) : IdK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextResume _)

theorem idk_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : IdK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_maybeDonateSc _ _)

theorem idk_completeSignal (ntfnptr tptr : ObjRef) : IdK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_completeSignal _ _)

theorem idk_copyGlobalMappings (newPm : ObjRef) : IdK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_copyGlobalMappings _)

theorem idk_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : IdK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_createCap _ _ _ _ _)

theorem idk_dataToObjType (type : Data) : IdKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_dataToObjType _)

theorem idk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeBindNotification _ _)

theorem idk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IdKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupPivotSlot _ _ _)

theorem idk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IdKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupSourceSlot _ _ _)

theorem idk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : IdKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeCnodeInvocation _ _ _ _)

theorem idk_slotCapLongRunningDelete (slot : CslotPtr) : IdK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_slotCapLongRunningDelete _)

theorem idk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IdKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvG
