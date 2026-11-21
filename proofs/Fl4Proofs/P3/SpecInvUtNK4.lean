/- ut7: IRQ-node frame lemmas `NK N`, part 4 (invA's NativeScope scripts renamed; see SpecInvUtNK1). -/
import Fl4Proofs.P3.SpecInvUtNK3
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef}

theorem nk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; nk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getExtraCptrs _ _)

theorem nk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupSlotForThread _ _)

theorem nk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupCapAndSlot _ _)

theorem nk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupExtraCaps _ _ _)

theorem nk_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NKE N m) : NK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_emptyOnFailure _ ?_)

theorem nk_loadCapTransfer (buffer : ObjRef) : NK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_loadCapTransfer _)

theorem nk_lookupCap (thread : ObjRef) (ref : CapRef) : NKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupCap _ _)

theorem nk_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NKE N m) : NKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_unifyFailure _ ?_)

theorem nk_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getReceiveSlots _ _)

theorem nk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NKE N m) : NK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_constOnFailure _ _ ?_)

theorem nk_deriveCap (slot : CslotPtr) (cap : Cap) : NKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deriveCap _ _)

theorem nk_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setExtraBadge _ _ _)

theorem nk_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; nk_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => nk_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | nk_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_transferCapsLoop _ _ _ _ _ _)

theorem nk_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_transferCaps _ _ _ _ _)

theorem nk_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_doNormalTransfer _ _ _ _ _ _ _)

theorem nk_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_doIpcTransfer _ _ _ _ _)

theorem nk_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : NK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyPush _ _ _ _)

theorem nk_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_orderedInsert _ _ _ _)

theorem nk_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbAppend _ _)

theorem nk_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : NK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbEpAppend _ _ _)

theorem nk_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : NK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_sendIpcBlocked _ _ _ _ _ _)

theorem nk_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : NK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_sendIpc _ _ _ _ _ _ _ _)

theorem nk_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : NK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_sendFaultIpc _ _ _ _)

theorem nk_handleTimeout (tptr : ObjRef) (ex : Fault) : NK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleTimeout _ _)

theorem nk_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_readyTimesAppend _ _)

theorem nk_tcbReleaseEnqueue (tcbPtr : ObjRef) : NK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbReleaseEnqueue _)

theorem nk_postpone (scPtr : ObjRef) : NK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_postpone _)

theorem nk_endTimeslice (canTimeout : Bool) : NK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_endTimeslice _)

theorem nk_getRefills (scPtr : ObjRef) : NK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getRefills _)

theorem nk_refillSize (scPtr : ObjRef) : NK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillSize _)

theorem nk_refillSingle (scPtr : ObjRef) : NK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillSingle _)

theorem nk_getRefillTail (scPtr : ObjRef) : NK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getRefillTail _)

theorem nk_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillAddTail _ _)

theorem nk_refillFull (scPtr : ObjRef) : NK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillFull _)

theorem nk_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateRefillTl _ _)

theorem nk_scheduleUsed (scPtr : ObjRef) (new : Refill) : NK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_scheduleUsed _ _)

theorem nk_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_chargeEntireHeadRefill _ _)

theorem nk_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleOverrun _ _)

theorem nk_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_mergeNonoverlappingHeadRefill _)

theorem nk_headInsufficientLoop (scPtr : ObjRef) : NK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_headInsufficientLoop _)

theorem nk_refillBudgetCheck (usage : Ticks) : NK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillBudgetCheck _)

theorem nk_refillResetRr (cscPtr : ObjRef) : NK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillResetRr _)

theorem nk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : NK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_chargeBudget _ _)

theorem nk_checkBudget  : NK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkBudget)

theorem nk_checkBudgetRestart  : NK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkBudgetRestart)

theorem nk_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NK N m) : NK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_checkCapAt _ _ _ ?_)

theorem nk_checkDomainTime  : NK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkDomainTime)

theorem nk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkHandlerEp _ _)

theorem nk_checkPrio (newPrio : Data) (authTcb : ObjRef) : NKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkPrio _ _)

theorem nk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_checkValidIpcBuffer _ _)

theorem nk_nextDomain  : NK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_nextDomain)

theorem nk_switchToThread (t : ObjRef) : NK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_switchToThread _)

theorem nk_guardedSwitchTo (thread : ObjRef) : NK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_guardedSwitchTo _)

theorem nk_switchToIdleThread  : NK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_switchToIdleThread)

theorem nk_chooseThread  : NK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_chooseThread)

theorem nk_refillBudgetCheckRoundRobin (usage : Ticks) : NK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillBudgetCheckRoundRobin _)

theorem nk_commitTime  : NK N (commitTime (Z := Unit)) := by
  unfold commitTime; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_commitTime)

theorem nk_schedContextResume (scPtr : ObjRef) : NK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextResume _)

theorem nk_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_maybeDonateSc _ _)

theorem nk_completeSignal (ntfnptr tptr : ObjRef) : NK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_completeSignal _ _)

theorem nk_copyGlobalMappings (newPm : ObjRef) : NK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_copyGlobalMappings _)

theorem nk_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_createCap _ _ _ _ _)

theorem nk_dataToObjType (type : Data) : NKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_dataToObjType _)

theorem nk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeBindNotification _ _)

theorem nk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupPivotSlot _ _ _)

theorem nk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupSourceSlot _ _ _)

theorem nk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeCnodeInvocation _ _ _ _)

theorem nk_slotCapLongRunningDelete (slot : CslotPtr) : NK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_slotCapLongRunningDelete _)

theorem nk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvU
