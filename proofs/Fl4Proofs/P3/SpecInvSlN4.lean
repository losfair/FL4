/- sl2: NtfnScB family lemmas, part 4 (generated; see SpecInvSlN1). -/
import Fl4Proofs.P3.SpecInvSlN3
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem nb_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NBKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupExtraCaps _ _ _)

theorem nb_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NBKE m) : NBK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_emptyOnFailure _ ?_)

theorem nb_loadCapTransfer (buffer : ObjRef) : NBK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadCapTransfer _)

theorem nb_lookupCap (thread : ObjRef) (ref : CapRef) : NBKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupCap _ _)

theorem nb_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NBKE m) : NBKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_unifyFailure _ ?_)

theorem nb_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NBK (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getReceiveSlots _ _)

theorem nb_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NBKE m) : NBK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_constOnFailure _ _ ?_)

theorem nb_deriveCap (slot : CslotPtr) (cap : Cap) : NBKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deriveCap _ _)

theorem nb_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NBK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setExtraBadge _ _ _)

theorem nb_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NBK (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; nb_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => nb_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | nb_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_transferCapsLoop _ _ _ _ _ _)

theorem nb_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NBK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_transferCaps _ _ _ _ _)

theorem nb_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NBK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doNormalTransfer _ _ _ _ _ _ _)

theorem nb_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NBK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doIpcTransfer _ _ _ _ _)

theorem nb_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : NBK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyPush _ _ _ _)

theorem nb_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NBK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_orderedInsert _ _ _ _)

theorem nb_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NBK (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbAppend _ _)

theorem nb_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : NBK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbEpAppend _ _ _)

theorem nb_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : NBK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendIpcBlocked _ _ _ _ _ _)

theorem nb_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : NBK (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendIpc _ _ _ _ _ _ _ _)

theorem nb_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : NBK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_sendFaultIpc _ _ _ _)

theorem nb_handleTimeout (tptr : ObjRef) (ex : Fault) : NBK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleTimeout _ _)

theorem nb_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NBK (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_readyTimesAppend _ _)

theorem nb_tcbReleaseEnqueue (tcbPtr : ObjRef) : NBK (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseEnqueue _)

theorem nb_postpone (scPtr : ObjRef) : NBK (postpone (Z := Unit) scPtr) := by
  unfold postpone; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_postpone _)

theorem nb_endTimeslice (canTimeout : Bool) : NBK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_endTimeslice _)

theorem nb_getRefills (scPtr : ObjRef) : NBK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefills _)

theorem nb_refillSize (scPtr : ObjRef) : NBK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillSize _)

theorem nb_refillSingle (scPtr : ObjRef) : NBK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillSingle _)

theorem nb_getRefillTail (scPtr : ObjRef) : NBK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefillTail _)

theorem nb_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NBK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillAddTail _ _)

theorem nb_refillFull (scPtr : ObjRef) : NBK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillFull _)

theorem nb_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NBK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRefillTl _ _)

theorem nb_scheduleUsed (scPtr : ObjRef) (new : Refill) : NBK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleUsed _ _)

theorem nb_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NBK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chargeEntireHeadRefill _ _)

theorem nb_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NBK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleOverrun _ _)

theorem nb_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NBK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_mergeNonoverlappingHeadRefill _)

theorem nb_headInsufficientLoop (scPtr : ObjRef) : NBK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_headInsufficientLoop _)

theorem nb_refillBudgetCheck (usage : Ticks) : NBK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillBudgetCheck _)

theorem nb_refillResetRr (cscPtr : ObjRef) : NBK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillResetRr _)

theorem nb_chargeBudget (consumed : Ticks) (canTimeout : Bool) : NBK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chargeBudget _ _)

theorem nb_checkBudget  : NBK (checkBudget (Z := Unit)) := by
  unfold checkBudget; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkBudget)

theorem nb_checkBudgetRestart  : NBK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkBudgetRestart)

theorem nb_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NBK m) : NBK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_checkCapAt _ _ _ ?_)

theorem nb_checkDomainTime  : NBK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkDomainTime)

theorem nb_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NBKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkHandlerEp _ _)

theorem nb_checkPrio (newPrio : Data) (authTcb : ObjRef) : NBKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkPrio _ _)

theorem nb_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NBKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_checkValidIpcBuffer _ _)

theorem nb_nextDomain  : NBK (nextDomain (Z := Unit)) := by
  unfold nextDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_nextDomain)

theorem nb_switchToThread (t : ObjRef) : NBK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchToThread _)

theorem nb_guardedSwitchTo (thread : ObjRef) : NBK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_guardedSwitchTo _)

theorem nb_switchToIdleThread  : NBK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchToIdleThread)

theorem nb_chooseThread  : NBK (chooseThread (Z := Unit)) := by
  unfold chooseThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_chooseThread)

theorem nb_refillBudgetCheckRoundRobin (usage : Ticks) : NBK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillBudgetCheckRoundRobin _)

theorem nb_commitTime  : NBK (commitTime (Z := Unit)) := by
  unfold commitTime; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_commitTime)

theorem nb_copyGlobalMappings (newPm : ObjRef) : NBK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_copyGlobalMappings _)

theorem nb_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NBK (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_createCap _ _ _ _ _)

theorem nb_dataToObjType (type : Data) : NBKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_dataToObjType _)

theorem nb_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeBindNotification _ _)

theorem nb_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NBKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupPivotSlot _ _ _)

theorem nb_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NBKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupSourceSlot _ _ _)

theorem nb_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NBKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeCnodeInvocation _ _ _ _)

theorem nb_slotCapLongRunningDelete (slot : CslotPtr) : NBK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_slotCapLongRunningDelete _)

theorem nb_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NBKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvL
