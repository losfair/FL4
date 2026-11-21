
/- epq1: generated frames `PZK` (sg1's SpecInvSgI4 renamed, the refill writers and the configure path removed; see SpecInvEqG1). -/
import Fl4Proofs.P3.SpecInvEqG3
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000


theorem pz_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : PZK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; pz_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getExtraCptrs _ _)

theorem pz_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : PZKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupSlotForThread _ _)

theorem pz_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : PZKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupCapAndSlot _ _)

theorem pz_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : PZKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupExtraCaps _ _ _)

theorem pz_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : PZKE m) : PZK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_emptyOnFailure _ ?_)

theorem pz_loadCapTransfer (buffer : ObjRef) : PZK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_loadCapTransfer _)

theorem pz_lookupCap (thread : ObjRef) (ref : CapRef) : PZKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupCap _ _)

theorem pz_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : PZKE m) : PZKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_unifyFailure _ ?_)

theorem pz_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : PZK (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getReceiveSlots _ _)

theorem pz_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : PZKE m) : PZK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_constOnFailure _ _ ?_)

theorem pz_deriveCap (slot : CslotPtr) (cap : Cap) : PZKE (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_deriveCap _ _)

theorem pz_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : PZK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setExtraBadge _ _ _)

theorem pz_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      PZK (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; pz_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => pz_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | pz_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_transferCapsLoop _ _ _ _ _ _)

theorem pz_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : PZK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_transferCaps _ _ _ _ _)

theorem pz_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : PZK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_doNormalTransfer _ _ _ _ _ _ _)

theorem pz_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : PZK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_doIpcTransfer _ _ _ _ _)

theorem pz_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : PZK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_replyPush _ _ _ _)

theorem pz_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : PZK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_orderedInsert _ _ _ _)

theorem pz_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : PZK (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbAppend _ _)

theorem pz_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : PZK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbEpAppend _ _ _)

theorem pz_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : PZK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_sendIpcBlocked _ _ _ _ _ _)

theorem pz_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : PZK (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_sendIpc _ _ _ _ _ _ _ _)

theorem pz_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : PZK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_sendFaultIpc _ _ _ _)

theorem pz_handleTimeout (tptr : ObjRef) (ex : Fault) : PZK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleTimeout _ _)

theorem pz_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : PZK (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_readyTimesAppend _ _)

theorem pz_tcbReleaseEnqueue (tcbPtr : ObjRef) : PZK (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbReleaseEnqueue _)

theorem pz_postpone (scPtr : ObjRef) : PZK (postpone (Z := Unit) scPtr) := by
  unfold postpone; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_postpone _)

theorem pz_endTimeslice (canTimeout : Bool) : PZK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_endTimeslice _)

theorem pz_getRefills (scPtr : ObjRef) : PZK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getRefills _)

theorem pz_refillSize (scPtr : ObjRef) : PZK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_refillSize _)

theorem pz_refillSingle (scPtr : ObjRef) : PZK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_refillSingle _)

theorem pz_getRefillTail (scPtr : ObjRef) : PZK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getRefillTail _)

theorem pz_refillFull (scPtr : ObjRef) : PZK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_refillFull _)

theorem pz_chargeBudget (consumed : Ticks) (canTimeout : Bool) : PZK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget
  refine ik_gets_bind fun σ => ikp_gets_bind (ikp_bind ?_ fun _ => by pz_auto)
  unfold NonDet.when
  split
  · refine ikp_isRoundRobin fun y n hy => ?_
    dsimp only
    by_cases hp : y.scPeriod = 0
    · rw [if_pos (decide_eq_true hp)]
      exact ikp_bind (pz_refillResetRr_p _ σ hy hp) fun _ => pz_updateSchedContext _ _ fun _ => ⟨rfl, rfl, rfl⟩
    · rw [if_neg (by simpa using hp)]
      exact ikp_bind (ikp_of_ik (pz_refillBudgetCheck _) σ) fun _ => pz_updateSchedContext _ _ fun _ => ⟨rfl, rfl, rfl⟩
  · exact ikp_of_ik (ik_pure' _) σ
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_chargeBudget _ _)

theorem pz_checkBudget  : PZK (checkBudget (Z := Unit)) := by
  unfold checkBudget; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkBudget)

theorem pz_checkBudgetRestart  : PZK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkBudgetRestart)

theorem pz_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : PZK m) : PZK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_checkCapAt _ _ _ ?_)

theorem pz_checkDomainTime  : PZK (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkDomainTime)

theorem pz_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : PZKE (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkHandlerEp _ _)

theorem pz_checkPrio (newPrio : Data) (authTcb : ObjRef) : PZKE (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkPrio _ _)

theorem pz_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : PZKE (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_checkValidIpcBuffer _ _)

theorem pz_nextDomain  : PZK (nextDomain (Z := Unit)) := by
  unfold nextDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_nextDomain)

theorem pz_switchToThread (t : ObjRef) : PZK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_switchToThread _)

theorem pz_guardedSwitchTo (thread : ObjRef) : PZK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_guardedSwitchTo _)

theorem pz_switchToIdleThread  : PZK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_switchToIdleThread)

theorem pz_chooseThread  : PZK (chooseThread (Z := Unit)) := by
  unfold chooseThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ?_
  split
  · exact pz_switchToIdleThread
  · exact pz_guardedSwitchTo _
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_chooseThread)

theorem pz_schedContextResume (scPtr : ObjRef) : PZK (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextResume _)

theorem pz_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : PZK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_maybeDonateSc _ _)

theorem pz_completeSignal (ntfnptr tptr : ObjRef) : PZK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_completeSignal _ _)

theorem pz_copyGlobalMappings (newPm : ObjRef) : PZK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_copyGlobalMappings _)

theorem pz_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : PZK (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_createCap _ _ _ _ _)

theorem pz_dataToObjType (type : Data) : PZKE (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_dataToObjType _)

theorem pz_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeBindNotification _ _)

theorem pz_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : PZKE (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupPivotSlot _ _ _)

theorem pz_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : PZKE (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupSourceSlot _ _ _)

theorem pz_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : PZKE (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeCnodeInvocation _ _ _ _)

theorem pz_slotCapLongRunningDelete (slot : CslotPtr) : PZK (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_slotCapLongRunningDelete _)

theorem pz_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : PZKE (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvE
