/- ft2: generic frame lemmas, part 3 (generated; see SpecInvFaultTcbsG1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsG2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Fq : FQ} {Sq : Set ObjRef} {Cq : ObjRef → Prop}

theorem fg_tcbReleaseRemove (tcbPtr : ObjRef) : FGK Fq Sq Cq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseRemove _)

theorem fg_tcbReleaseDequeue  : FGK Fq Sq Cq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseDequeue)

theorem fg_awaken  : FGK Fq Sq Cq (awaken (Z := Unit)) := by
  unfold awaken; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_awaken)

theorem fg_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : FGK Fq Sq Cq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSimpleKo _ _)

theorem fg_bindNotification (tcbptr ntfnptr : ObjRef) : FGK Fq Sq Cq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_bindNotification _ _)

theorem fg_getSchedContext (ptr : ObjRef) : FGK Fq Sq Cq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSchedContext _)

theorem fg_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : FGK Fq Sq Cq (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateSchedContext _ _)

theorem fg_bindScReply (scPtr replyPtr : ObjRef) : FGK Fq Sq Cq (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_bindScReply _ _)

theorem fg_getBlockingObject (state : ThreadState) : FGK Fq Sq Cq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getBlockingObject _)

theorem fg_getThreadState (ref : ObjRef) : FGK Fq Sq Cq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getThreadState _)

theorem fg_setThreadStateAct (tcbPtr : ObjRef) : FGK Fq Sq Cq (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setThreadStateAct _)

theorem fg_replyUnlinkTcb (t r : ObjRef) : FGK Fq Sq Cq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyUnlinkTcb _ _)

theorem fg_tcbEpDequeue (tptr epPtr : ObjRef) : FGK Fq Sq Cq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbEpDequeue _ _)

theorem fg_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : FGK Fq Sq Cq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_blockedCancelIpc _ _ _)

theorem fg_cancelSignal (threadptr ntfnptr : ObjRef) : FGK Fq Sq Cq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_cancelSignal _ _)

theorem fg_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getSkObjRef _ _ _)

theorem fg_replyRemoveTcb (tptr rptr : ObjRef) : FGK Fq Sq Cq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyRemoveTcb _ _)

theorem fg_cancelIpc (tptr : ObjRef) : FGK Fq Sq Cq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_cancelIpc _)

theorem fg_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : FGKE Fq Sq Cq m) : FGKE Fq Sq Cq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_capFaultOnFailure _ _ _ ?_)

theorem fg_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : FGK Fq Sq Cq (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capMove _ _ _)

theorem fg_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : FGK Fq Sq Cq (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capSwap _ _ _ _)

theorem fg_capSwapForDelete (slot1 slot2 : CslotPtr) : FGK Fq Sq Cq (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capSwapForDelete _ _)

theorem fg_captransferFromWords (ptr : Word) : FGK Fq Sq Cq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_captransferFromWords _)

theorem fg_getRefillHead (scPtr : ObjRef) : FGK Fq Sq Cq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefillHead _)

theorem fg_refillPopHead (scPtr : ObjRef) : FGK Fq Sq Cq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillPopHead _)

theorem fg_getRefills (scPtr : ObjRef) : FGK Fq Sq Cq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefills _)

theorem fg_refillSize (scPtr : ObjRef) : FGK Fq Sq Cq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillSize _)

theorem fg_refillSingle (scPtr : ObjRef) : FGK Fq Sq Cq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillSingle _)

theorem fg_getRefillTail (scPtr : ObjRef) : FGK Fq Sq Cq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getRefillTail _)

theorem fg_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : FGK Fq Sq Cq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillAddTail _ _)

theorem fg_refillFull (scPtr : ObjRef) : FGK Fq Sq Cq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillFull _)

theorem fg_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : FGK Fq Sq Cq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRefillTl _ _)

theorem fg_scheduleUsed (scPtr : ObjRef) (new : Refill) : FGK Fq Sq Cq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scheduleUsed _ _)

theorem fg_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : FGK Fq Sq Cq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRefillHd _ _)

theorem fg_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_chargeEntireHeadRefill _ _)

theorem fg_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : FGK Fq Sq Cq m) : FGK Fq Sq Cq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_checkCapAt _ _ _ ?_)

theorem fg_checkDomainTime  : FGK Fq Sq Cq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkDomainTime)

theorem fg_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : FGKE Fq Sq Cq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkHandlerEp _ _)

theorem fg_checkPrio (newPrio : Data) (authTcb : ObjRef) : FGKE Fq Sq Cq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkPrio _ _)

theorem fg_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : FGKE Fq Sq Cq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_checkValidIpcBuffer _ _)

theorem fg_getScActive (scPtr : ObjRef) : FGK Fq Sq Cq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScActive _)

theorem fg_isRoundRobin (scPtr : ObjRef) : FGK Fq Sq Cq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isRoundRobin _)

theorem fg_handleOverrun (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleOverrun _ _)

theorem fg_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : FGK Fq Sq Cq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_mergeNonoverlappingHeadRefill _)

theorem fg_headInsufficientLoop (scPtr : ObjRef) : FGK Fq Sq Cq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_headInsufficientLoop _)

theorem fg_refillBudgetCheck (usage : Ticks) : FGK Fq Sq Cq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillBudgetCheck _)

theorem fg_refillBudgetCheckRoundRobin (usage : Ticks) : FGK Fq Sq Cq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillBudgetCheckRoundRobin _)

theorem fg_commitTime  : FGK Fq Sq Cq (commitTime (Z := Unit)) := by
  unfold commitTime; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_commitTime)

theorem fg_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScObjRef _ _)

theorem fg_testReschedule (fromTptr : ObjRef) : FGK Fq Sq Cq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_testReschedule _)

theorem fg_schedContextDonate (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextDonate _ _)

theorem fg_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : FGK Fq Sq Cq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_orderedInsert _ _ _ _)

theorem fg_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : FGK Fq Sq Cq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_readyTimesAppend _ _)

theorem fg_tcbReleaseEnqueue (tcbPtr : ObjRef) : FGK Fq Sq Cq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbReleaseEnqueue _)

theorem fg_postpone (scPtr : ObjRef) : FGK Fq Sq Cq (postpone (Z := Unit) scPtr) := by
  unfold postpone; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_postpone _)

theorem fg_schedContextResume (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextResume _)

theorem fg_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : FGK Fq Sq Cq (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeDonateSc _ _)

theorem fg_mergeOverlappingRefills (scPtr : ObjRef) : FGK Fq Sq Cq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_mergeOverlappingRefills _)
end

end Fl4Proofs.P3.SInv
