/- sl1: idle-SC frame lemmas `IsK t` (sg1 SpecInvSgI3 renamed; see SpecInvSlI1). -/
import Fl4Proofs.P3.SpecInvSlI2
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem isk_tcbEpDequeue (tptr epPtr : ObjRef) : IsK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbEpDequeue _ _)

theorem isk_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : IsK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_blockedCancelIpc _ _ _)

theorem isk_isRoundRobin (scPtr : ObjRef) : IsK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isRoundRobin _)

theorem isk_getRefillHead (scPtr : ObjRef) : IsK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getRefillHead _)

theorem isk_refillPopHead (scPtr : ObjRef) : IsK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillPopHead _)

theorem isk_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : IsK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateRefillHd _ _)

theorem isk_mergeOverlappingRefills (scPtr : ObjRef) : IsK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_mergeOverlappingRefills _)

theorem isk_refillHeadOverlappingLoop (scPtr : ObjRef) : IsK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillHeadOverlappingLoop _)

theorem isk_refillUnblockCheck (scPtr : ObjRef) : IsK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillUnblockCheck _)

theorem isk_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : IsK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_ifCondRefillUnblockCheck _ _ _)

theorem isk_restartThreadIfNoFault (t : ObjRef) : IsK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_restartThreadIfNoFault _)

theorem isk_removeAndRestartEpQueuedThread (t epptr : ObjRef) : IsK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_removeAndRestartEpQueuedThread _ _)

theorem isk_cancelAllIpc (epptr : ObjRef) : IsK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_cancelAllIpc _)

theorem isk_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : IsK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbNtfnDequeue _ _)

theorem isk_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : IsK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_removeAndRestartNtfnQueuedThread _ _)

theorem isk_cancelAllSignals (ntfnptr : ObjRef) : IsK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_cancelAllSignals _)

theorem isk_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : IsK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_removeAndRestartBadgedThread _ _ _)

theorem isk_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : IsK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_cancelBadgedSends _ _)

theorem isk_cancelSignal (threadptr ntfnptr : ObjRef) : IsK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_cancelSignal _ _)

theorem isk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : IsK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getSkObjRef _ _ _)

theorem isk_replyRemoveTcb (tptr rptr : ObjRef) : IsK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyRemoveTcb _ _)

theorem isk_cancelIpc (tptr : ObjRef) : IsK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_cancelIpc _)

theorem isk_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : IsK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capSwap _ _ _ _)

theorem isk_capSwapForDelete (slot1 slot2 : CslotPtr) : IsK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capSwapForDelete _ _)

theorem isk_deletedIrqHandler (irq : Irq) : IsK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deletedIrqHandler _)

theorem isk_postCapDeletion (cap : Cap) : IsK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_postCapDeletion _)

theorem isk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : IsK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_emptySlot _ _)

theorem isk_replyUnlinkSc (scPtr replyPtr : ObjRef) : IsK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyUnlinkSc _ _)

theorem isk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : IsK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getScObjRef _ _)

theorem isk_testReschedule (fromTptr : ObjRef) : IsK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_testReschedule _)

theorem isk_schedContextDonate (scPtr tcbPtr : ObjRef) : IsK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextDonate _ _)

theorem isk_replyRemove (caller r : ObjRef) : IsK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyRemove _ _)

theorem isk_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : IsK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextMaybeUnbindNtfn _)

theorem isk_unbindMaybeNotification (ntfnptr : ObjRef) : IsK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unbindMaybeNotification _)

theorem isk_fastFinalise (a0 : Cap) (a1 : Bool) : IsK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fastFinalise _ _)

theorem isk_capDeleteOne (slot : CslotPtr) : IsK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capDeleteOne _)

theorem isk_getIrqSlot (irq : Irq) : IsK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getIrqSlot _)

theorem isk_deletingIrqHandler (irq : Irq) : IsK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_deletingIrqHandler _)

theorem isk_prepareThreadDelete (threadPtr : ObjRef) : IsK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_prepareThreadDelete _)

theorem isk_schedContextSetInactive (scPtr : ObjRef) : IsK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextSetInactive _)

theorem isk_schedContextUnbindTcb (scPtr : ObjRef) : IsK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUnbindTcb _)

theorem isk_schedContextUnbindAllTcbs (scPtr : ObjRef) : IsK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUnbindAllTcbs _)

theorem isk_schedContextUnbindNtfn (scPtr : ObjRef) : IsK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUnbindNtfn _)

theorem isk_schedContextUnbindReply (scPtr : ObjRef) : IsK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUnbindReply _)

theorem isk_schedContextUnbindYieldFrom (scPtr : ObjRef) : IsK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextUnbindYieldFrom _)

theorem isk_updateRestartPc (threadPtr : ObjRef) : IsK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateRestartPc _)

theorem isk_suspend (thread : ObjRef) : IsK N (suspend (Z := Unit) thread) := by
  unfold suspend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_suspend _)

theorem isk_unbindFromSc (tcbPtr : ObjRef) : IsK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unbindFromSc _)

theorem isk_unbindNotification (tcb : ObjRef) : IsK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unbindNotification _)

theorem isk_finaliseCap (a0 : Cap) (a1 : Bool) : IsK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_finaliseCap _ _)

theorem isk_getScActive (scPtr : ObjRef) : IsK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getScActive _)

theorem isk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IsKE N f) (h_g : IsKE N g) : IsKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; isk_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_orChoiceE _ _ _ ?_ ?_)

theorem isk_updateTimeStamp  : IsK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateTimeStamp)

theorem isk_preemptionPoint  : IsKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem isk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IsK N (f k)) (k : RecDelCall) : IsKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IsKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; isk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; isk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> isk_auto
    all_goals exact hrec' _

theorem isk_recDel (c : RecDelCall) : IsKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => isk_recDelF hf k) c
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_recDel _)

theorem isk_capDelete (slot : CslotPtr) : IsKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capDelete _)

theorem isk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IsKE N m) : IsKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_capFaultOnFailure _ _ _ ?_)

theorem isk_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : IsK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem isk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IsK N (f k)) (sl : CslotPtr) : IsKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IsKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  isk_auto
  all_goals exact hrec' _

theorem isk_capRevoke (sl : CslotPtr) : IsKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => isk_capRevokeF hf k) sl
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capRevoke _)

theorem isk_captransferFromWords (ptr : Word) : IsK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_captransferFromWords _)

theorem isk_isValidTimeoutHandler (tptr : ObjRef) : IsK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isValidTimeoutHandler _)

theorem isk_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : IsK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_makeArchFaultMsg _ _)

theorem isk_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : IsK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_makeFaultMsg _ _)

theorem isk_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : IsK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_doFaultTransfer _ _ _ _)

theorem isk_loadWordOffs (ptr : ObjRef) (offs : Nat) : IsK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_loadWordOffs _ _)

theorem isk_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : IsK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_copyMrs _ _ _ _ _)

theorem isk_getMessageInfo (thread : ObjRef) : IsK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getMessageInfo _)
end

end Fl4Proofs.P3.SInvL
