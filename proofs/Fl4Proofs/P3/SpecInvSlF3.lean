/- sl1: ScLive family lemmas, part 3 (generated; see SpecInvSlF1). -/
import Fl4Proofs.P3.SpecInvSlF2
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Iq : ObjRef × ObjRef} {Kq : List ObjRef}

theorem sl_awaken  : SLK Iq Kq (awaken (Z := Unit)) := by
  unfold awaken; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_awaken)

theorem sl_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : SLK Iq Kq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getSimpleKo _ _)

theorem sl_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : SLK Iq Kq (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateSkObjRef _ _ _ _)

theorem sl_bindNotification (tcbptr ntfnptr : ObjRef) : SLK Iq Kq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_bindNotification _ _)

theorem sl_getBlockingObject (state : ThreadState) : SLK Iq Kq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getBlockingObject _)

theorem sl_replyUnlinkTcb (t r : ObjRef) : SLK Iq Kq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyUnlinkTcb _ _)

theorem sl_tcbEpDequeue (tptr epPtr : ObjRef) : SLK Iq Kq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbEpDequeue _ _)

theorem sl_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : SLK Iq Kq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_blockedCancelIpc _ _ _)

theorem sl_isRoundRobin (scPtr : ObjRef) : SLK Iq Kq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isRoundRobin _)

theorem sl_getRefillHead (scPtr : ObjRef) : SLK Iq Kq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefillHead _)

theorem sl_refillPopHead (scPtr : ObjRef) : SLK Iq Kq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillPopHead _)

theorem sl_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : SLK Iq Kq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRefillHd _ _)

theorem sl_mergeOverlappingRefills (scPtr : ObjRef) : SLK Iq Kq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_mergeOverlappingRefills _)

theorem sl_refillHeadOverlappingLoop (scPtr : ObjRef) : SLK Iq Kq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillHeadOverlappingLoop _)

theorem sl_refillUnblockCheck (scPtr : ObjRef) : SLK Iq Kq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillUnblockCheck _)

theorem sl_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : SLK Iq Kq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_ifCondRefillUnblockCheck _ _ _)

theorem sl_restartThreadIfNoFault (t : ObjRef) : SLK Iq Kq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_restartThreadIfNoFault _)

theorem sl_removeAndRestartEpQueuedThread (t epptr : ObjRef) : SLK Iq Kq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartEpQueuedThread _ _)

theorem sl_cancelAllIpc (epptr : ObjRef) : SLK Iq Kq (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelAllIpc _)

theorem sl_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : SLK Iq Kq (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbNtfnDequeue _ _)

theorem sl_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : SLK Iq Kq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartNtfnQueuedThread _ _)

theorem sl_cancelAllSignals (ntfnptr : ObjRef) : SLK Iq Kq (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelAllSignals _)

theorem sl_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : SLK Iq Kq (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_removeAndRestartBadgedThread _ _ _)

theorem sl_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : SLK Iq Kq (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelBadgedSends _ _)

theorem sl_cancelSignal (threadptr ntfnptr : ObjRef) : SLK Iq Kq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelSignal _ _)

theorem sl_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : SLK Iq Kq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getSkObjRef _ _ _)

theorem sl_replyRemoveTcb (tptr rptr : ObjRef) : SLK Iq Kq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyRemoveTcb _ _)

theorem sl_cancelIpc (tptr : ObjRef) : SLK Iq Kq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_cancelIpc _)

theorem sl_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : SLKE Iq Kq m) : SLKE Iq Kq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_capFaultOnFailure _ _ _ ?_)

theorem sl_captransferFromWords (ptr : Word) : SLK Iq Kq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_captransferFromWords _)

theorem sl_getRefills (scPtr : ObjRef) : SLK Iq Kq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefills _)

theorem sl_refillSize (scPtr : ObjRef) : SLK Iq Kq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillSize _)

theorem sl_refillSingle (scPtr : ObjRef) : SLK Iq Kq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillSingle _)

theorem sl_getRefillTail (scPtr : ObjRef) : SLK Iq Kq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getRefillTail _)

theorem sl_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : SLK Iq Kq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillAddTail _ _)

theorem sl_refillFull (scPtr : ObjRef) : SLK Iq Kq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillFull _)

theorem sl_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : SLK Iq Kq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRefillTl _ _)

theorem sl_scheduleUsed (scPtr : ObjRef) (new : Refill) : SLK Iq Kq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleUsed _ _)

theorem sl_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_chargeEntireHeadRefill _ _)

theorem sl_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : SLK Iq Kq m) : SLK Iq Kq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_checkCapAt _ _ _ ?_)

theorem sl_checkDomainTime  : SLK Iq Kq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkDomainTime)

theorem sl_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : SLKE Iq Kq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkHandlerEp _ _)

theorem sl_checkPrio (newPrio : Data) (authTcb : ObjRef) : SLKE Iq Kq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkPrio _ _)

theorem sl_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : SLKE Iq Kq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_checkValidIpcBuffer _ _)

theorem sl_nextDomain  : SLK Iq Kq (nextDomain (Z := Unit)) := by
  unfold nextDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_nextDomain)

theorem sl_switchToThread (t : ObjRef) : SLK Iq Kq (switchToThread (Z := Unit) t) := by
  unfold switchToThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchToThread _)

theorem sl_guardedSwitchTo (thread : ObjRef) : SLK Iq Kq (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_guardedSwitchTo _)

theorem sl_switchToIdleThread  : SLK Iq Kq (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchToIdleThread)

theorem sl_chooseThread  : SLK Iq Kq (chooseThread (Z := Unit)) := by
  unfold chooseThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_chooseThread)

theorem sl_getScActive (scPtr : ObjRef) : SLK Iq Kq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScActive _)

theorem sl_handleOverrun (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleOverrun _ _)

theorem sl_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : SLK Iq Kq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_mergeNonoverlappingHeadRefill _)

theorem sl_headInsufficientLoop (scPtr : ObjRef) : SLK Iq Kq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_headInsufficientLoop _)

theorem sl_refillBudgetCheck (usage : Ticks) : SLK Iq Kq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillBudgetCheck _)

theorem sl_refillBudgetCheckRoundRobin (usage : Ticks) : SLK Iq Kq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillBudgetCheckRoundRobin _)

theorem sl_commitTime  : SLK Iq Kq (commitTime (Z := Unit)) := by
  unfold commitTime; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_commitTime)

theorem sl_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : SLKE Iq Kq m) : SLK Iq Kq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_constOnFailure _ _ ?_)
end

end Fl4Proofs.P3.SInvL
