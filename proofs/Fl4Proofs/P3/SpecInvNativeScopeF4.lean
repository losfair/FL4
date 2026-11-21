/- invA: NativeScope frame lemmas, part 4 (generated; see SpecInvNativeScopeF1). -/
import Fl4Proofs.P3.SpecInvNativeScopeF3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem ns_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NSK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ns_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getExtraCptrs _ _)

theorem ns_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NSKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupSlotForThread _ _)

theorem ns_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NSKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupCapAndSlot _ _)

theorem ns_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NSKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupExtraCaps _ _ _)

theorem ns_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NSKE m) : NSK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_emptyOnFailure _ ?_)

theorem ns_loadCapTransfer (buffer : ObjRef) : NSK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadCapTransfer _)

theorem ns_lookupCap (thread : ObjRef) (ref : CapRef) : NSKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupCap _ _)

theorem ns_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NSKE m) : NSKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_unifyFailure _ ?_)

theorem ns_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NSK (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getReceiveSlots _ _)

theorem ns_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NSKE m) : NSK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_constOnFailure _ _ ?_)

theorem ns_deriveCap (slot : CslotPtr) (cap : Cap) : NSKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deriveCap _ _)

theorem ns_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NSK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setExtraBadge _ _ _)

theorem ns_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NSK (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ns_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ns_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ns_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_transferCapsLoop _ _ _ _ _ _)

theorem ns_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NSK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_transferCaps _ _ _ _ _)

theorem ns_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NSK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doNormalTransfer _ _ _ _ _ _ _)

theorem ns_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NSK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doIpcTransfer _ _ _ _ _)

theorem ns_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : NSK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyPush _ _ _ _)

theorem ns_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NSK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_orderedInsert _ _ _ _)

theorem ns_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NSK (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbAppend _ _)

theorem ns_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : NSK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbEpAppend _ _ _)

theorem ns_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : NSK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendIpcBlocked _ _ _ _ _ _)

theorem ns_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : NSK (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendIpc _ _ _ _ _ _ _ _)

theorem ns_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : NSK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendFaultIpc _ _ _ _)

theorem ns_handleTimeout (tptr : ObjRef) (ex : Fault) : NSK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleTimeout _ _)

theorem ns_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NSK (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_readyTimesAppend _ _)

theorem ns_tcbReleaseEnqueue (tcbPtr : ObjRef) : NSK (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseEnqueue _)

theorem ns_postpone (scPtr : ObjRef) : NSK (postpone (Z := Unit) scPtr) := by
  unfold postpone; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_postpone _)

theorem ns_endTimeslice (canTimeout : Bool) : NSK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_endTimeslice _)

theorem ns_getRefills (scPtr : ObjRef) : NSK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefills _)

theorem ns_refillSize (scPtr : ObjRef) : NSK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillSize _)

theorem ns_refillSingle (scPtr : ObjRef) : NSK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillSingle _)

theorem ns_getRefillTail (scPtr : ObjRef) : NSK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefillTail _)

theorem ns_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NSK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillAddTail _ _)

theorem ns_refillFull (scPtr : ObjRef) : NSK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillFull _)

theorem ns_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NSK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRefillTl _ _)

theorem ns_scheduleUsed (scPtr : ObjRef) (new : Refill) : NSK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleUsed _ _)

theorem ns_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NSK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chargeEntireHeadRefill _ _)

theorem ns_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NSK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleOverrun _ _)

theorem ns_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NSK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_mergeNonoverlappingHeadRefill _)

theorem ns_headInsufficientLoop (scPtr : ObjRef) : NSK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_headInsufficientLoop _)

theorem ns_refillBudgetCheck (usage : Ticks) : NSK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillBudgetCheck _)

theorem ns_refillResetRr (cscPtr : ObjRef) : NSK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillResetRr _)

theorem ns_chargeBudget (consumed : Ticks) (canTimeout : Bool) : NSK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chargeBudget _ _)

theorem ns_checkBudget  : NSK (checkBudget (Z := Unit)) := by
  unfold checkBudget; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkBudget)

theorem ns_checkBudgetRestart  : NSK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkBudgetRestart)

theorem ns_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NSK m) : NSK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_checkCapAt _ _ _ ?_)

theorem ns_checkDomainTime  : NSK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkDomainTime)

theorem ns_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NSKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkHandlerEp _ _)

theorem ns_checkPrio (newPrio : Data) (authTcb : ObjRef) : NSKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkPrio _ _)

theorem ns_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NSKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_checkValidIpcBuffer _ _)

theorem ns_nextDomain  : NSK (nextDomain (Z := Unit)) := by
  unfold nextDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_nextDomain)

theorem ns_switchToThread (t : ObjRef) : NSK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchToThread _)

theorem ns_guardedSwitchTo (thread : ObjRef) : NSK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_guardedSwitchTo _)

theorem ns_switchToIdleThread  : NSK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchToIdleThread)

theorem ns_chooseThread  : NSK (chooseThread (Z := Unit)) := by
  unfold chooseThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_chooseThread)

theorem ns_refillBudgetCheckRoundRobin (usage : Ticks) : NSK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillBudgetCheckRoundRobin _)

theorem ns_commitTime  : NSK (commitTime (Z := Unit)) := by
  unfold commitTime; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_commitTime)

theorem ns_schedContextResume (scPtr : ObjRef) : NSK (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextResume _)

theorem ns_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NSK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeDonateSc _ _)

theorem ns_completeSignal (ntfnptr tptr : ObjRef) : NSK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_completeSignal _ _)

theorem ns_copyGlobalMappings (newPm : ObjRef) : NSK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_copyGlobalMappings _)

theorem ns_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NSK (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_createCap _ _ _ _ _)

theorem ns_dataToObjType (type : Data) : NSKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_dataToObjType _)

theorem ns_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeBindNotification _ _)

theorem ns_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NSKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupPivotSlot _ _ _)

theorem ns_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NSKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupSourceSlot _ _ _)

theorem ns_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NSKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeCnodeInvocation _ _ _ _)

theorem ns_slotCapLongRunningDelete (slot : CslotPtr) : NSK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_slotCapLongRunningDelete _)

theorem ns_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NSKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInv
