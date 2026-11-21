
/- vi1: generated frames `IK (VIT N S T b)` (sg1's SpecInvSgI4 renamed, the idle-relevant writers removed; see SpecInvViG1). -/
import Fl4Proofs.P3.SpecInvViG3
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}

theorem vi_getExtraCptrs (bf : Option ObjRef) (mi : MessageInfo) : IK (VIT N S T b) (getExtraCptrs (Z := Unit) bf mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; vi_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getExtraCptrs _ _)

theorem vi_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : IKE (VIT N S T b) (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupSlotForThread _ _)

theorem vi_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : IKE (VIT N S T b) (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupCapAndSlot _ _)

theorem vi_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : IKE (VIT N S T b) (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupExtraCaps _ _ _)

theorem vi_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IKE (VIT N S T b) m) : IK (VIT N S T b) (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_emptyOnFailure _ ?_)

theorem vi_loadCapTransfer (buffer : ObjRef) : IK (VIT N S T b) (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_loadCapTransfer _)

theorem vi_lookupCap (thread : ObjRef) (ref : CapRef) : IKE (VIT N S T b) (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupCap _ _)

theorem vi_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IKE (VIT N S T b) m) : IKE (VIT N S T b) (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_unifyFailure _ ?_)

theorem vi_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : IK (VIT N S T b) (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getReceiveSlots _ _)

theorem vi_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IKE (VIT N S T b) m) : IK (VIT N S T b) (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_constOnFailure _ _ ?_)

theorem vi_deriveCap (slot : CslotPtr) (cap : Cap) : IKE (VIT N S T b) (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_deriveCap _ _)

theorem vi_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : IK (VIT N S T b) (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setExtraBadge _ _ _)

theorem vi_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      IK (VIT N S T b) (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; vi_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => vi_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | vi_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_transferCapsLoop _ _ _ _ _ _)

theorem vi_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : IK (VIT N S T b) (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_transferCaps _ _ _ _ _)

theorem vi_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : IK (VIT N S T b) (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_doNormalTransfer _ _ _ _ _ _ _)

theorem vi_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IK (VIT N S T b) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_doIpcTransfer _ _ _ _ _)

theorem vi_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : IK (VIT N S T b) (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_orderedInsert _ _ _ _)

theorem vi_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : IK (VIT N S T b) (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbAppend _ _)

theorem vi_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : IK (VIT N S T b) (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_readyTimesAppend _ _)

theorem vi_tcbReleaseEnqueue (tcbPtr : ObjRef) : IK (VIT N S T b) (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbReleaseEnqueue _)

theorem vi_postpone (scPtr : ObjRef) : IK (VIT N S T b) (postpone (Z := Unit) scPtr) := by
  unfold postpone; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_postpone _)

theorem vi_getRefills (scPtr : ObjRef) : IK (VIT N S T b) (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getRefills _)

theorem vi_refillSize (scPtr : ObjRef) : IK (VIT N S T b) (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillSize _)

theorem vi_refillSingle (scPtr : ObjRef) : IK (VIT N S T b) (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillSingle _)

theorem vi_getRefillTail (scPtr : ObjRef) : IK (VIT N S T b) (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getRefillTail _)

theorem vi_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : IK (VIT N S T b) (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillAddTail _ _)

theorem vi_refillFull (scPtr : ObjRef) : IK (VIT N S T b) (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillFull _)

theorem vi_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : IK (VIT N S T b) (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateRefillTl _ _)

theorem vi_scheduleUsed (scPtr : ObjRef) (new : Refill) : IK (VIT N S T b) (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_scheduleUsed _ _)

theorem vi_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : IK (VIT N S T b) (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_chargeEntireHeadRefill _ _)

theorem vi_handleOverrun (scPtr : ObjRef) (usage : Ticks) : IK (VIT N S T b) (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleOverrun _ _)

theorem vi_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : IK (VIT N S T b) (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_mergeNonoverlappingHeadRefill _)

theorem vi_headInsufficientLoop (scPtr : ObjRef) : IK (VIT N S T b) (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_headInsufficientLoop _)

theorem vi_refillBudgetCheck (usage : Ticks) : IK (VIT N S T b) (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillBudgetCheck _)

theorem vi_refillResetRr (cscPtr : ObjRef) : IK (VIT N S T b) (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillResetRr _)

theorem vi_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : IK (VIT N S T b) m) : IK (VIT N S T b) (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_checkCapAt _ _ _ ?_)

theorem vi_checkDomainTime  : IK (VIT N S T b) (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkDomainTime)

theorem vi_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : IKE (VIT N S T b) (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkHandlerEp _ _)

theorem vi_checkPrio (newPrio : Data) (authTcb : ObjRef) : IKE (VIT N S T b) (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkPrio _ _)

theorem vi_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : IKE (VIT N S T b) (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_checkValidIpcBuffer _ _)

theorem vi_nextDomain  : IK (VIT N S T b) (nextDomain (Z := Unit)) := by
  unfold nextDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_nextDomain)

/-- Writing the current thread keeps `VIT _ _ _ false` (the scheduler runs at `b = false`). -/
theorem vi_setCurThread (t : ObjRef) :
    IK (VIT N S T false) (NonDet.modify fun s : State Unit => { s with curThread := t }) :=
  ik_modify fun _ h => by
    obtain ⟨h1, h2, -, h4, h5, h6⟩ := h
    exact ⟨h1, h2, fun e => absurd e (by decide), h4, h5, h6⟩
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setCurThread _)


theorem vi_switchToThread (t : ObjRef) : IK (VIT N S T false) (switchToThread (Z := Unit) t) := by
  unfold switchToThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_switchToThread _)

theorem vi_guardedSwitchTo (thread : ObjRef) : IK (VIT N S T false) (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_guardedSwitchTo _)

theorem vi_switchToIdleThread  : IK (VIT N S T false) (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_switchToIdleThread)

theorem vi_chooseThread  : IK (VIT N S T false) (chooseThread (Z := Unit)) := by
  unfold chooseThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_chooseThread)

theorem vi_refillBudgetCheckRoundRobin (usage : Ticks) : IK (VIT N S T b) (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillBudgetCheckRoundRobin _)

theorem vi_commitTime  : IK (VIT N S T b) (commitTime (Z := Unit)) := by
  unfold commitTime; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_commitTime)

theorem vi_schedContextResume (scPtr : ObjRef) : IK (VIT N S T b) (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextResume _)

theorem vi_copyGlobalMappings (newPm : ObjRef) : IK (VIT N S T b) (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_copyGlobalMappings _)

theorem vi_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : IK (VIT N S T b) (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_createCap _ _ _ _ _)

theorem vi_dataToObjType (type : Data) : IKE (VIT N S T b) (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_dataToObjType _)

theorem vi_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeBindNotification _ _)

theorem vi_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IKE (VIT N S T b) (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupPivotSlot _ _ _)

theorem vi_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IKE (VIT N S T b) (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupSourceSlot _ _ _)

theorem vi_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : IKE (VIT N S T b) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeCnodeInvocation _ _ _ _)

theorem vi_slotCapLongRunningDelete (slot : CslotPtr) : IK (VIT N S T b) (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_slotCapLongRunningDelete _)

theorem vi_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvI
