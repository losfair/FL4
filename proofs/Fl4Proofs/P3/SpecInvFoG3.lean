
/- fo1: generated frames `OIK Qo` (sg1's SpecInvSgI3 renamed, the owner / retype / detype writers removed; see SpecInvFoG1). -/
import Fl4Proofs.P3.SpecInvFoG2
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Qo : Option ObjRef}

theorem oi_tcbEpDequeue (tptr epPtr : ObjRef) : OIK Qo (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbEpDequeue _ _)

theorem oi_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : OIK Qo (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_blockedCancelIpc _ _ _)

theorem oi_isRoundRobin (scPtr : ObjRef) : OIK Qo (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isRoundRobin _)

theorem oi_getRefillHead (scPtr : ObjRef) : OIK Qo (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefillHead _)

theorem oi_refillPopHead (scPtr : ObjRef) : OIK Qo (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillPopHead _)

theorem oi_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : OIK Qo (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRefillHd _ _)

theorem oi_mergeOverlappingRefills (scPtr : ObjRef) : OIK Qo (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_mergeOverlappingRefills _)

theorem oi_refillHeadOverlappingLoop (scPtr : ObjRef) : OIK Qo (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillHeadOverlappingLoop _)

theorem oi_refillUnblockCheck (scPtr : ObjRef) : OIK Qo (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUnblockCheck _)

theorem oi_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : OIK Qo (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ifCondRefillUnblockCheck _ _ _)

theorem oi_restartThreadIfNoFault (t : ObjRef) : OIK Qo (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_restartThreadIfNoFault _)

theorem oi_removeAndRestartEpQueuedThread (t epptr : ObjRef) : OIK Qo (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartEpQueuedThread _ _)

theorem oi_cancelAllIpc (epptr : ObjRef) : OIK Qo (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllIpc _)

theorem oi_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : OIK Qo (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnDequeue _ _)

theorem oi_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : OIK Qo (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartNtfnQueuedThread _ _)

theorem oi_cancelAllSignals (ntfnptr : ObjRef) : OIK Qo (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllSignals _)

theorem oi_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : OIK Qo (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartBadgedThread _ _ _)

theorem oi_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : OIK Qo (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelBadgedSends _ _)

theorem oi_cancelSignal (threadptr ntfnptr : ObjRef) : OIK Qo (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelSignal _ _)

theorem oi_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : OIK Qo (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSkObjRef _ _ _)

theorem oi_replyRemoveTcb (tptr rptr : ObjRef) : OIK Qo (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemoveTcb _ _)

theorem oi_cancelIpc (tptr : ObjRef) : OIK Qo (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelIpc _)

theorem oi_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : OIK Qo (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwap _ _ _ _)

theorem oi_capSwapForDelete (slot1 slot2 : CslotPtr) : OIK Qo (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwapForDelete _ _)

theorem oi_deletedIrqHandler (irq : Irq) : OIK Qo (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletedIrqHandler _)

theorem oi_postCapDeletion (cap : Cap) : OIK Qo (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_postCapDeletion _)

theorem oi_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : OIK Qo (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_emptySlot _ _)

theorem oi_replyUnlinkSc (scPtr replyPtr : ObjRef) : OIK Qo (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkSc _ _)

theorem oi_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : OIK Qo (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScObjRef _ _)

theorem oi_testReschedule (fromTptr : ObjRef) : OIK Qo (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_testReschedule _)

theorem oi_schedContextDonate (scPtr tcbPtr : ObjRef) : OIK Qo (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextDonate _ _)

theorem oi_replyRemove (caller r : ObjRef) : OIK Qo (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemove _ _)

theorem oi_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : OIK Qo (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextMaybeUnbindNtfn _)

theorem oi_unbindMaybeNotification (ntfnptr : ObjRef) : OIK Qo (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindMaybeNotification _)

theorem oi_fastFinalise (a0 : Cap) (a1 : Bool) : OIK Qo (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fastFinalise _ _)

theorem oi_capDeleteOne (slot : CslotPtr) : OIK Qo (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capDeleteOne _)

theorem oi_getIrqSlot (irq : Irq) : OIK Qo (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getIrqSlot _)

theorem oi_deletingIrqHandler (irq : Irq) : OIK Qo (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletingIrqHandler _)

theorem oi_schedContextSetInactive (scPtr : ObjRef) : OIK Qo (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextSetInactive _)

theorem oi_schedContextUnbindTcb (scPtr : ObjRef) : OIK Qo (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindTcb _)

theorem oi_schedContextUnbindAllTcbs (scPtr : ObjRef) : OIK Qo (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindAllTcbs _)

theorem oi_schedContextUnbindNtfn (scPtr : ObjRef) : OIK Qo (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindNtfn _)

theorem oi_schedContextUnbindReply (scPtr : ObjRef) : OIK Qo (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindReply _)

theorem oi_schedContextUnbindYieldFrom (scPtr : ObjRef) : OIK Qo (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindYieldFrom _)

theorem oi_updateRestartPc (threadPtr : ObjRef) : OIK Qo (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRestartPc _)

theorem oi_suspend (thread : ObjRef) : OIK Qo (suspend (Z := Unit) thread) := by
  unfold suspend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_suspend _)

theorem oi_unbindFromSc (tcbPtr : ObjRef) : OIK Qo (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindFromSc _)

theorem oi_unbindNotification (tcb : ObjRef) : OIK Qo (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindNotification _)

theorem oi_getScActive (scPtr : ObjRef) : OIK Qo (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScActive _)

theorem oi_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : OIKE Qo f) (h_g : OIKE Qo g) : OIKE Qo (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; oi_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_orChoiceE _ _ _ ?_ ?_)

theorem oi_updateTimeStamp  : OIK Qo (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateTimeStamp)

theorem oi_preemptionPoint  : OIKE Qo (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPoint)


theorem oi_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : OIKE Qo m) : OIKE Qo (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_capFaultOnFailure _ _ _ ?_)

theorem oi_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK Qo (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capMove _ _ _)


theorem oi_captransferFromWords (ptr : Word) : OIK Qo (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_captransferFromWords _)

theorem oi_isValidTimeoutHandler (tptr : ObjRef) : OIK Qo (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isValidTimeoutHandler _)

theorem oi_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : OIK Qo (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeArchFaultMsg _ _)

theorem oi_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : OIK Qo (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeFaultMsg _ _)

theorem oi_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : OIK Qo (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doFaultTransfer _ _ _ _)

theorem oi_loadWordOffs (ptr : ObjRef) (offs : Nat) : OIK Qo (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadWordOffs _ _)

theorem oi_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : OIK Qo (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_copyMrs _ _ _ _ _)

theorem oi_getMessageInfo (thread : ObjRef) : OIK Qo (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getMessageInfo _)
end

end Fl4Proofs.P3.SInvF
