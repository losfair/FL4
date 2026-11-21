/- il1: IfLiveT family lemmas, part 3 (generated; see SpecInvNtfnQL1). -/
import Fl4Proofs.P3.SpecInvNtfnQL2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem il_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : ILK Kq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getSimpleKo _ _)

theorem il_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : ILK Kq (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateSkObjRef _ _ _ _)

theorem il_bindNotification (tcbptr ntfnptr : ObjRef) : ILK Kq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_bindNotification _ _)

theorem il_bindScReply (scPtr replyPtr : ObjRef) : ILK Kq (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_bindScReply _ _)

theorem il_getBlockingObject (state : ThreadState) : ILK Kq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getBlockingObject _)

theorem il_replyUnlinkTcb (t r : ObjRef) : ILK Kq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_replyUnlinkTcb _ _)

theorem il_tcbEpDequeue (tptr epPtr : ObjRef) : ILK Kq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbEpDequeue _ _)

theorem il_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : ILK Kq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_blockedCancelIpc _ _ _)

theorem il_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : ILK Kq (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbNtfnDequeue _ _)

theorem il_cancelSignal (threadptr ntfnptr : ObjRef) : ILK Kq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_cancelSignal _ _)

theorem il_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : ILK Kq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getSkObjRef _ _ _)

theorem il_replyRemoveTcb (tptr rptr : ObjRef) : ILK Kq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_replyRemoveTcb _ _)

theorem il_cancelIpc (tptr : ObjRef) : ILK Kq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_cancelIpc _)

theorem il_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : ILKE Kq m) : ILKE Kq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_capFaultOnFailure _ _ _ ?_)

theorem il_captransferFromWords (ptr : Word) : ILK Kq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_captransferFromWords _)

theorem il_getRefillHead (scPtr : ObjRef) : ILK Kq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getRefillHead _)

theorem il_refillPopHead (scPtr : ObjRef) : ILK Kq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillPopHead _)

theorem il_getRefills (scPtr : ObjRef) : ILK Kq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getRefills _)

theorem il_refillSize (scPtr : ObjRef) : ILK Kq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillSize _)

theorem il_refillSingle (scPtr : ObjRef) : ILK Kq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillSingle _)

theorem il_getRefillTail (scPtr : ObjRef) : ILK Kq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getRefillTail _)

theorem il_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : ILK Kq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillAddTail _ _)

theorem il_refillFull (scPtr : ObjRef) : ILK Kq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillFull _)

theorem il_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : ILK Kq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateRefillTl _ _)

theorem il_scheduleUsed (scPtr : ObjRef) (new : Refill) : ILK Kq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_scheduleUsed _ _)

theorem il_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : ILK Kq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateRefillHd _ _)

theorem il_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : ILK Kq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_chargeEntireHeadRefill _ _)

theorem il_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : ILK Kq m) : ILK Kq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_checkCapAt _ _ _ ?_)

theorem il_checkDomainTime  : ILK Kq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkDomainTime)

theorem il_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : ILKE Kq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkHandlerEp _ _)

theorem il_checkPrio (newPrio : Data) (authTcb : ObjRef) : ILKE Kq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkPrio _ _)

theorem il_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : ILKE Kq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_checkValidIpcBuffer _ _)

theorem il_nextDomain  : ILK Kq (nextDomain (Z := Unit)) := by
  unfold nextDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_nextDomain)

theorem il_switchToThread (t : ObjRef) : ILK Kq (switchToThread (Z := Unit) t) := by
  unfold switchToThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_switchToThread _)

theorem il_guardedSwitchTo (thread : ObjRef) : ILK Kq (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_guardedSwitchTo _)

theorem il_switchToIdleThread  : ILK Kq (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_switchToIdleThread)

theorem il_chooseThread  : ILK Kq (chooseThread (Z := Unit)) := by
  unfold chooseThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_chooseThread)

theorem il_getScActive (scPtr : ObjRef) : ILK Kq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getScActive _)

theorem il_isRoundRobin (scPtr : ObjRef) : ILK Kq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_isRoundRobin _)

theorem il_handleOverrun (scPtr : ObjRef) (usage : Ticks) : ILK Kq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleOverrun _ _)

theorem il_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : ILK Kq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_mergeNonoverlappingHeadRefill _)

theorem il_headInsufficientLoop (scPtr : ObjRef) : ILK Kq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_headInsufficientLoop _)

theorem il_refillBudgetCheck (usage : Ticks) : ILK Kq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillBudgetCheck _)

theorem il_refillBudgetCheckRoundRobin (usage : Ticks) : ILK Kq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillBudgetCheckRoundRobin _)

theorem il_commitTime  : ILK Kq (commitTime (Z := Unit)) := by
  unfold commitTime; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_commitTime)

theorem il_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : ILK Kq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getScObjRef _ _)

theorem il_testReschedule (fromTptr : ObjRef) : ILK Kq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_testReschedule _)

theorem il_schedContextDonate (scPtr tcbPtr : ObjRef) : ILK Kq (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextDonate _ _)

theorem il_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : ILK Kq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_orderedInsert _ _ _ _)

theorem il_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : ILK Kq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_readyTimesAppend _ _)

theorem il_tcbReleaseEnqueue (tcbPtr : ObjRef) : ILK Kq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbReleaseEnqueue _)

theorem il_postpone (scPtr : ObjRef) : ILK Kq (postpone (Z := Unit) scPtr) := by
  unfold postpone; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_postpone _)

theorem il_schedContextResume (scPtr : ObjRef) : ILK Kq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextResume _)

theorem il_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : ILK Kq (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_maybeDonateSc _ _)

theorem il_mergeOverlappingRefills (scPtr : ObjRef) : ILK Kq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_mergeOverlappingRefills _)

theorem il_refillHeadOverlappingLoop (scPtr : ObjRef) : ILK Kq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillHeadOverlappingLoop _)

theorem il_refillUnblockCheck (scPtr : ObjRef) : ILK Kq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillUnblockCheck _)

theorem il_completeSignal (ntfnptr tptr : ObjRef) : ILK Kq (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_completeSignal _ _)
end

end Fl4Proofs.P3.SInv
