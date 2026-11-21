/- g1c: OnlyIdle frame lemmas, part 3 (generated; see SpecInvAllO1). -/
import Fl4Proofs.P3.SpecInvAllO2
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem oi_tcbEpDequeue (tptr epPtr : ObjRef) : OIK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbEpDequeue _ _)

theorem oi_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : OIK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_blockedCancelIpc _ _ _)

theorem oi_isRoundRobin (scPtr : ObjRef) : OIK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isRoundRobin _)

theorem oi_getRefillHead (scPtr : ObjRef) : OIK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getRefillHead _)

theorem oi_refillPopHead (scPtr : ObjRef) : OIK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillPopHead _)

theorem oi_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : OIK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRefillHd _ _)

theorem oi_mergeOverlappingRefills (scPtr : ObjRef) : OIK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_mergeOverlappingRefills _)

theorem oi_refillHeadOverlappingLoop (scPtr : ObjRef) : OIK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillHeadOverlappingLoop _)

theorem oi_refillUnblockCheck (scPtr : ObjRef) : OIK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUnblockCheck _)

theorem oi_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : OIK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_ifCondRefillUnblockCheck _ _ _)

theorem oi_restartThreadIfNoFault (t : ObjRef) : OIK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_restartThreadIfNoFault _)

theorem oi_removeAndRestartEpQueuedThread (t epptr : ObjRef) : OIK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartEpQueuedThread _ _)

theorem oi_cancelAllIpc (epptr : ObjRef) : OIK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllIpc _)

theorem oi_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : OIK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnDequeue _ _)

theorem oi_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : OIK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartNtfnQueuedThread _ _)

theorem oi_cancelAllSignals (ntfnptr : ObjRef) : OIK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelAllSignals _)

theorem oi_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : OIK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_removeAndRestartBadgedThread _ _ _)

theorem oi_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : OIK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelBadgedSends _ _)

theorem oi_cancelSignal (threadptr ntfnptr : ObjRef) : OIK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelSignal _ _)

theorem oi_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : OIK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSkObjRef _ _ _)

theorem oi_replyRemoveTcb (tptr rptr : ObjRef) : OIK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemoveTcb _ _)

theorem oi_cancelIpc (tptr : ObjRef) : OIK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_cancelIpc _)

theorem oi_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : OIK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwap _ _ _ _)

theorem oi_capSwapForDelete (slot1 slot2 : CslotPtr) : OIK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capSwapForDelete _ _)

theorem oi_deletedIrqHandler (irq : Irq) : OIK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletedIrqHandler _)

theorem oi_postCapDeletion (cap : Cap) : OIK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_postCapDeletion _)

theorem oi_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : OIK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_emptySlot _ _)

theorem oi_replyUnlinkSc (scPtr replyPtr : ObjRef) : OIK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkSc _ _)

theorem oi_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : OIK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScObjRef _ _)

theorem oi_testReschedule (fromTptr : ObjRef) : OIK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_testReschedule _)

theorem oi_schedContextDonate (scPtr tcbPtr : ObjRef) : OIK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextDonate _ _)

theorem oi_replyRemove (caller r : ObjRef) : OIK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyRemove _ _)

theorem oi_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : OIK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextMaybeUnbindNtfn _)

theorem oi_unbindMaybeNotification (ntfnptr : ObjRef) : OIK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindMaybeNotification _)

theorem oi_fastFinalise (a0 : Cap) (a1 : Bool) : OIK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fastFinalise _ _)

theorem oi_capDeleteOne (slot : CslotPtr) : OIK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capDeleteOne _)

theorem oi_getIrqSlot (irq : Irq) : OIK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getIrqSlot _)

theorem oi_deletingIrqHandler (irq : Irq) : OIK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_deletingIrqHandler _)

theorem oi_prepareThreadDelete (threadPtr : ObjRef) : OIK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_prepareThreadDelete _)

theorem oi_schedContextSetInactive (scPtr : ObjRef) : OIK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextSetInactive _)

theorem oi_schedContextUnbindTcb (scPtr : ObjRef) : OIK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindTcb _)

theorem oi_schedContextUnbindAllTcbs (scPtr : ObjRef) : OIK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindAllTcbs _)

theorem oi_schedContextUnbindNtfn (scPtr : ObjRef) : OIK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindNtfn _)

theorem oi_schedContextUnbindReply (scPtr : ObjRef) : OIK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindReply _)

theorem oi_schedContextUnbindYieldFrom (scPtr : ObjRef) : OIK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextUnbindYieldFrom _)

theorem oi_updateRestartPc (threadPtr : ObjRef) : OIK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateRestartPc _)

theorem oi_suspend (thread : ObjRef) : OIK N (suspend (Z := Unit) thread) := by
  unfold suspend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_suspend _)

theorem oi_unbindFromSc (tcbPtr : ObjRef) : OIK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindFromSc _)

theorem oi_unbindNotification (tcb : ObjRef) : OIK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unbindNotification _)

theorem oi_finaliseCap (a0 : Cap) (a1 : Bool) : OIK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_finaliseCap _ _)

theorem oi_getScActive (scPtr : ObjRef) : OIK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScActive _)

theorem oi_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : OIKE N f) (h_g : OIKE N g) : OIKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; oi_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_orChoiceE _ _ _ ?_ ?_)

theorem oi_updateTimeStamp  : OIK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateTimeStamp)

theorem oi_preemptionPoint  : OIKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem oi_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, OIK N (f k)) (k : RecDelCall) : OIKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, OIKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; oi_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; oi_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> oi_auto
    all_goals exact hrec' _

theorem oi_recDel (c : RecDelCall) : OIKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => oi_recDelF hf k) c
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_recDel _)

theorem oi_capDelete (slot : CslotPtr) : OIKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capDelete _)

theorem oi_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : OIKE N m) : OIKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_capFaultOnFailure _ _ _ ?_)

theorem oi_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem oi_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, OIK N (f k)) (sl : CslotPtr) : OIKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, OIKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  oi_auto
  all_goals exact hrec' _

theorem oi_capRevoke (sl : CslotPtr) : OIKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => oi_capRevokeF hf k) sl
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capRevoke _)

theorem oi_captransferFromWords (ptr : Word) : OIK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_captransferFromWords _)

theorem oi_isValidTimeoutHandler (tptr : ObjRef) : OIK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isValidTimeoutHandler _)

theorem oi_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : OIK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeArchFaultMsg _ _)

theorem oi_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : OIK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_makeFaultMsg _ _)

theorem oi_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : OIK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doFaultTransfer _ _ _ _)

theorem oi_loadWordOffs (ptr : ObjRef) (offs : Nat) : OIK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadWordOffs _ _)

theorem oi_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : OIK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_copyMrs _ _ _ _ _)

theorem oi_getMessageInfo (thread : ObjRef) : OIK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getMessageInfo _)
end

end Fl4Proofs.P3.SInvAll
