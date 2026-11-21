/- invA2: FaultTcbsS frame lemmas, part 3 (generated; see SpecInvFaultTcbsF1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsF2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem ft_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : FTK L (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateSkObjRef _ _ _ _)

theorem ft_bindNotification (tcbptr ntfnptr : ObjRef) : FTK L (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_bindNotification _ _)

theorem ft_getSchedContext (ptr : ObjRef) : FTK L (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSchedContext _)

theorem ft_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : FTK L (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateSchedContext _ _)

theorem ft_bindScReply (scPtr replyPtr : ObjRef) : FTK L (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_bindScReply _ _)

theorem ft_getBlockingObject (state : ThreadState) : FTK L (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getBlockingObject _)

theorem ft_getThreadState (ref : ObjRef) : FTK L (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getThreadState _)

theorem ft_setThreadStateAct (tcbPtr : ObjRef) : FTK L (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setThreadStateAct _)

theorem ft_replyUnlinkTcb (t r : ObjRef) : FTK L (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyUnlinkTcb _ _)

theorem ft_tcbEpDequeue (tptr epPtr : ObjRef) : FTK L (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbEpDequeue _ _)

theorem ft_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : FTK L (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_blockedCancelIpc _ _ _)

theorem ft_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : FTK L (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbNtfnDequeue _ _)

theorem ft_cancelSignal (threadptr ntfnptr : ObjRef) : FTK L (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_cancelSignal _ _)

theorem ft_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : FTK L (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSkObjRef _ _ _)

theorem ft_replyRemoveTcb (tptr rptr : ObjRef) : FTK L (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyRemoveTcb _ _)

theorem ft_cancelIpc (tptr : ObjRef) : FTK L (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_cancelIpc _)

theorem ft_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : FTKE L m) : FTKE L (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_capFaultOnFailure _ _ _ ?_)

theorem ft_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : FTK L (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capMove _ _ _)

theorem ft_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : FTK L (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capSwap _ _ _ _)

theorem ft_capSwapForDelete (slot1 slot2 : CslotPtr) : FTK L (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capSwapForDelete _ _)

theorem ft_captransferFromWords (ptr : Word) : FTK L (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_captransferFromWords _)

theorem ft_getRefillHead (scPtr : ObjRef) : FTK L (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefillHead _)

theorem ft_refillPopHead (scPtr : ObjRef) : FTK L (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillPopHead _)

theorem ft_getRefills (scPtr : ObjRef) : FTK L (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefills _)

theorem ft_refillSize (scPtr : ObjRef) : FTK L (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillSize _)

theorem ft_refillSingle (scPtr : ObjRef) : FTK L (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillSingle _)

theorem ft_getRefillTail (scPtr : ObjRef) : FTK L (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getRefillTail _)

theorem ft_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : FTK L (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillAddTail _ _)

theorem ft_refillFull (scPtr : ObjRef) : FTK L (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillFull _)

theorem ft_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : FTK L (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRefillTl _ _)

theorem ft_scheduleUsed (scPtr : ObjRef) (new : Refill) : FTK L (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleUsed _ _)

theorem ft_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : FTK L (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRefillHd _ _)

theorem ft_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : FTK L (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_chargeEntireHeadRefill _ _)

theorem ft_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : FTK L m) : FTK L (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_checkCapAt _ _ _ ?_)

theorem ft_checkDomainTime  : FTK L (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkDomainTime)

theorem ft_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : FTKE L (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkHandlerEp _ _)

theorem ft_checkPrio (newPrio : Data) (authTcb : ObjRef) : FTKE L (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkPrio _ _)

theorem ft_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : FTKE L (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkValidIpcBuffer _ _)

theorem ft_nextDomain  : FTK L (nextDomain (Z := Unit)) := by
  unfold nextDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_nextDomain)

theorem ft_switchToThread (t : ObjRef) : FTK L (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchToThread _)

theorem ft_guardedSwitchTo (thread : ObjRef) : FTK L (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_guardedSwitchTo _)

theorem ft_switchToIdleThread  : FTK L (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchToIdleThread)

theorem ft_chooseThread  : FTK L (chooseThread (Z := Unit)) := by
  unfold chooseThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_chooseThread)

theorem ft_getScActive (scPtr : ObjRef) : FTK L (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScActive _)

theorem ft_isRoundRobin (scPtr : ObjRef) : FTK L (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isRoundRobin _)

theorem ft_handleOverrun (scPtr : ObjRef) (usage : Ticks) : FTK L (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleOverrun _ _)

theorem ft_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : FTK L (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_mergeNonoverlappingHeadRefill _)

theorem ft_headInsufficientLoop (scPtr : ObjRef) : FTK L (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_headInsufficientLoop _)

theorem ft_refillBudgetCheck (usage : Ticks) : FTK L (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillBudgetCheck _)

theorem ft_refillBudgetCheckRoundRobin (usage : Ticks) : FTK L (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillBudgetCheckRoundRobin _)

theorem ft_commitTime  : FTK L (commitTime (Z := Unit)) := by
  unfold commitTime; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_commitTime)

theorem ft_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : FTK L (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScObjRef _ _)

theorem ft_testReschedule (fromTptr : ObjRef) : FTK L (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_testReschedule _)

theorem ft_schedContextDonate (scPtr tcbPtr : ObjRef) : FTK L (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextDonate _ _)

theorem ft_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : FTK L (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_orderedInsert _ _ _ _)

theorem ft_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : FTK L (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_readyTimesAppend _ _)

theorem ft_tcbReleaseEnqueue (tcbPtr : ObjRef) : FTK L (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseEnqueue _)

theorem ft_postpone (scPtr : ObjRef) : FTK L (postpone (Z := Unit) scPtr) := by
  unfold postpone; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_postpone _)

theorem ft_schedContextResume (scPtr : ObjRef) : FTK L (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextResume _)

theorem ft_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : FTK L (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeDonateSc _ _)
end

end Fl4Proofs.P3.SInv
