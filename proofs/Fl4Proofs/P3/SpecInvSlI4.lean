/- sl1: idle-SC frame lemmas `IsK t` (sg1 SpecInvSgI4 renamed; see SpecInvSlI1). -/
import Fl4Proofs.P3.SpecInvSlI3
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem isk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : IsK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; isk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getExtraCptrs _ _)

theorem isk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : IsKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupSlotForThread _ _)

theorem isk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : IsKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupCapAndSlot _ _)

theorem isk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : IsKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupExtraCaps _ _ _)

theorem isk_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IsKE N m) : IsK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_emptyOnFailure _ ?_)

theorem isk_loadCapTransfer (buffer : ObjRef) : IsK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_loadCapTransfer _)

theorem isk_lookupCap (thread : ObjRef) (ref : CapRef) : IsKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupCap _ _)

theorem isk_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IsKE N m) : IsKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_unifyFailure _ ?_)

theorem isk_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : IsK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getReceiveSlots _ _)

theorem isk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IsKE N m) : IsK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_constOnFailure _ _ ?_)

theorem isk_deriveCap (slot : CslotPtr) (cap : Cap) : IsKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deriveCap _ _)

theorem isk_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : IsK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setExtraBadge _ _ _)

theorem isk_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      IsK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; isk_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => isk_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | isk_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_transferCapsLoop _ _ _ _ _ _)

theorem isk_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : IsK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_transferCaps _ _ _ _ _)

theorem isk_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : IsK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_doNormalTransfer _ _ _ _ _ _ _)

theorem isk_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IsK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_doIpcTransfer _ _ _ _ _)

theorem isk_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : IsK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyPush _ _ _ _)

theorem isk_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : IsK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_orderedInsert _ _ _ _)

theorem isk_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : IsK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbAppend _ _)

theorem isk_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : IsK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbEpAppend _ _ _)

theorem isk_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : IsK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_sendIpcBlocked _ _ _ _ _ _)

theorem isk_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IsK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_sendIpc _ _ _ _ _ _ _ _)

theorem isk_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IsK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_sendFaultIpc _ _ _ _)

theorem isk_handleTimeout (tptr : ObjRef) (ex : Fault) : IsK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleTimeout _ _)

theorem isk_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : IsK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_readyTimesAppend _ _)

theorem isk_tcbReleaseEnqueue (tcbPtr : ObjRef) : IsK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbReleaseEnqueue _)

theorem isk_postpone (scPtr : ObjRef) : IsK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_postpone _)

theorem isk_endTimeslice (canTimeout : Bool) : IsK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_endTimeslice _)

theorem isk_getRefills (scPtr : ObjRef) : IsK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getRefills _)

theorem isk_refillSize (scPtr : ObjRef) : IsK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillSize _)

theorem isk_refillSingle (scPtr : ObjRef) : IsK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillSingle _)

theorem isk_getRefillTail (scPtr : ObjRef) : IsK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getRefillTail _)

theorem isk_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : IsK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillAddTail _ _)

theorem isk_refillFull (scPtr : ObjRef) : IsK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillFull _)

theorem isk_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : IsK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateRefillTl _ _)

theorem isk_scheduleUsed (scPtr : ObjRef) (new : Refill) : IsK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_scheduleUsed _ _)

theorem isk_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : IsK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_chargeEntireHeadRefill _ _)

theorem isk_handleOverrun (scPtr : ObjRef) (usage : Ticks) : IsK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleOverrun _ _)

theorem isk_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : IsK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_mergeNonoverlappingHeadRefill _)

theorem isk_headInsufficientLoop (scPtr : ObjRef) : IsK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_headInsufficientLoop _)

theorem isk_refillBudgetCheck (usage : Ticks) : IsK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillBudgetCheck _)

theorem isk_refillResetRr (cscPtr : ObjRef) : IsK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillResetRr _)

theorem isk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IsK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_chargeBudget _ _)

theorem isk_checkBudget  : IsK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkBudget)

theorem isk_checkBudgetRestart  : IsK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkBudgetRestart)

theorem isk_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : IsK N m) : IsK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_checkCapAt _ _ _ ?_)

theorem isk_checkDomainTime  : IsK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkDomainTime)

theorem isk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : IsKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkHandlerEp _ _)

theorem isk_checkPrio (newPrio : Data) (authTcb : ObjRef) : IsKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkPrio _ _)

theorem isk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : IsKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_checkValidIpcBuffer _ _)

theorem isk_nextDomain  : IsK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_nextDomain)

theorem isk_switchToThread (t : ObjRef) : IsK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_switchToThread _)

theorem isk_guardedSwitchTo (thread : ObjRef) : IsK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_guardedSwitchTo _)

theorem isk_switchToIdleThread  : IsK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_switchToIdleThread)

theorem isk_chooseThread  : IsK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_chooseThread)

theorem isk_refillBudgetCheckRoundRobin (usage : Ticks) : IsK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillBudgetCheckRoundRobin _)

theorem isk_commitTime  : IsK N (commitTime (Z := Unit)) := by
  unfold commitTime; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_commitTime)

theorem isk_schedContextResume (scPtr : ObjRef) : IsK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextResume _)

theorem isk_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : IsK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_maybeDonateSc _ _)

theorem isk_completeSignal (ntfnptr tptr : ObjRef) : IsK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_completeSignal _ _)

theorem isk_copyGlobalMappings (newPm : ObjRef) : IsK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_copyGlobalMappings _)

theorem isk_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : IsK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_createCap _ _ _ _ _)

theorem isk_dataToObjType (type : Data) : IsKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_dataToObjType _)

theorem isk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeBindNotification _ _)

theorem isk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IsKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupPivotSlot _ _ _)

theorem isk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IsKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupSourceSlot _ _ _)

theorem isk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : IsKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeCnodeInvocation _ _ _ _)

theorem isk_slotCapLongRunningDelete (slot : CslotPtr) : IsK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_slotCapLongRunningDelete _)

theorem isk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IsKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvL
