/- sg1: idle-thread frame lemmas `IdK t` (ut7's SpecInvUtNK3 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvSgI2
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem idk_tcbEpDequeue (tptr epPtr : ObjRef) : IdK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbEpDequeue _ _)

theorem idk_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : IdK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_blockedCancelIpc _ _ _)

theorem idk_isRoundRobin (scPtr : ObjRef) : IdK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isRoundRobin _)

theorem idk_getRefillHead (scPtr : ObjRef) : IdK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getRefillHead _)

theorem idk_refillPopHead (scPtr : ObjRef) : IdK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillPopHead _)

theorem idk_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : IdK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateRefillHd _ _)

theorem idk_mergeOverlappingRefills (scPtr : ObjRef) : IdK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_mergeOverlappingRefills _)

theorem idk_refillHeadOverlappingLoop (scPtr : ObjRef) : IdK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillHeadOverlappingLoop _)

theorem idk_refillUnblockCheck (scPtr : ObjRef) : IdK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillUnblockCheck _)

theorem idk_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : IdK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_ifCondRefillUnblockCheck _ _ _)

theorem idk_restartThreadIfNoFault (t : ObjRef) : IdK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_restartThreadIfNoFault _)

theorem idk_removeAndRestartEpQueuedThread (t epptr : ObjRef) : IdK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_removeAndRestartEpQueuedThread _ _)

theorem idk_cancelAllIpc (epptr : ObjRef) : IdK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_cancelAllIpc _)

theorem idk_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : IdK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbNtfnDequeue _ _)

theorem idk_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : IdK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_removeAndRestartNtfnQueuedThread _ _)

theorem idk_cancelAllSignals (ntfnptr : ObjRef) : IdK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_cancelAllSignals _)

theorem idk_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : IdK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_removeAndRestartBadgedThread _ _ _)

theorem idk_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : IdK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_cancelBadgedSends _ _)

theorem idk_cancelSignal (threadptr ntfnptr : ObjRef) : IdK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_cancelSignal _ _)

theorem idk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : IdK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getSkObjRef _ _ _)

theorem idk_replyRemoveTcb (tptr rptr : ObjRef) : IdK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyRemoveTcb _ _)

theorem idk_cancelIpc (tptr : ObjRef) : IdK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_cancelIpc _)

theorem idk_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : IdK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capSwap _ _ _ _)

theorem idk_capSwapForDelete (slot1 slot2 : CslotPtr) : IdK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capSwapForDelete _ _)

theorem idk_deletedIrqHandler (irq : Irq) : IdK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deletedIrqHandler _)

theorem idk_postCapDeletion (cap : Cap) : IdK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_postCapDeletion _)

theorem idk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : IdK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_emptySlot _ _)

theorem idk_replyUnlinkSc (scPtr replyPtr : ObjRef) : IdK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyUnlinkSc _ _)

theorem idk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : IdK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getScObjRef _ _)

theorem idk_testReschedule (fromTptr : ObjRef) : IdK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_testReschedule _)

theorem idk_schedContextDonate (scPtr tcbPtr : ObjRef) : IdK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextDonate _ _)

theorem idk_replyRemove (caller r : ObjRef) : IdK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyRemove _ _)

theorem idk_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : IdK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextMaybeUnbindNtfn _)

theorem idk_unbindMaybeNotification (ntfnptr : ObjRef) : IdK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unbindMaybeNotification _)

theorem idk_fastFinalise (a0 : Cap) (a1 : Bool) : IdK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fastFinalise _ _)

theorem idk_capDeleteOne (slot : CslotPtr) : IdK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capDeleteOne _)

theorem idk_getIrqSlot (irq : Irq) : IdK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getIrqSlot _)

theorem idk_deletingIrqHandler (irq : Irq) : IdK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_deletingIrqHandler _)

theorem idk_prepareThreadDelete (threadPtr : ObjRef) : IdK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_prepareThreadDelete _)

theorem idk_schedContextSetInactive (scPtr : ObjRef) : IdK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextSetInactive _)

theorem idk_schedContextUnbindTcb (scPtr : ObjRef) : IdK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUnbindTcb _)

theorem idk_schedContextUnbindAllTcbs (scPtr : ObjRef) : IdK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUnbindAllTcbs _)

theorem idk_schedContextUnbindNtfn (scPtr : ObjRef) : IdK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUnbindNtfn _)

theorem idk_schedContextUnbindReply (scPtr : ObjRef) : IdK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUnbindReply _)

theorem idk_schedContextUnbindYieldFrom (scPtr : ObjRef) : IdK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextUnbindYieldFrom _)

theorem idk_updateRestartPc (threadPtr : ObjRef) : IdK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateRestartPc _)

theorem idk_suspend (thread : ObjRef) : IdK N (suspend (Z := Unit) thread) := by
  unfold suspend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_suspend _)

theorem idk_unbindFromSc (tcbPtr : ObjRef) : IdK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unbindFromSc _)

theorem idk_unbindNotification (tcb : ObjRef) : IdK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unbindNotification _)

theorem idk_finaliseCap (a0 : Cap) (a1 : Bool) : IdK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_finaliseCap _ _)

theorem idk_getScActive (scPtr : ObjRef) : IdK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getScActive _)

theorem idk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IdKE N f) (h_g : IdKE N g) : IdKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; idk_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_orChoiceE _ _ _ ?_ ?_)

theorem idk_updateTimeStamp  : IdK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateTimeStamp)

theorem idk_preemptionPoint  : IdKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem idk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IdK N (f k)) (k : RecDelCall) : IdKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IdKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; idk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; idk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> idk_auto
    all_goals exact hrec' _

theorem idk_recDel (c : RecDelCall) : IdKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => idk_recDelF hf k) c
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_recDel _)

theorem idk_capDelete (slot : CslotPtr) : IdKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capDelete _)

theorem idk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IdKE N m) : IdKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_capFaultOnFailure _ _ _ ?_)

theorem idk_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : IdK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem idk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IdK N (f k)) (sl : CslotPtr) : IdKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IdKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  idk_auto
  all_goals exact hrec' _

theorem idk_capRevoke (sl : CslotPtr) : IdKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => idk_capRevokeF hf k) sl
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capRevoke _)

theorem idk_captransferFromWords (ptr : Word) : IdK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_captransferFromWords _)

theorem idk_isValidTimeoutHandler (tptr : ObjRef) : IdK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isValidTimeoutHandler _)

theorem idk_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : IdK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_makeArchFaultMsg _ _)

theorem idk_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : IdK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_makeFaultMsg _ _)

theorem idk_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : IdK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_doFaultTransfer _ _ _ _)

theorem idk_loadWordOffs (ptr : ObjRef) (offs : Nat) : IdK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_loadWordOffs _ _)

theorem idk_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : IdK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_copyMrs _ _ _ _ _)

theorem idk_getMessageInfo (thread : ObjRef) : IdK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getMessageInfo _)
end

end Fl4Proofs.P3.SInvG
