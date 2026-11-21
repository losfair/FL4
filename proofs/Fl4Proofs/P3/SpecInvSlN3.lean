/- sl2: NtfnScB family lemmas, part 3 (generated; see SpecInvSlN1). -/
import Fl4Proofs.P3.SpecInvSlN2
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem nb_mergeOverlappingRefills (scPtr : ObjRef) : NBK (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_mergeOverlappingRefills _)

theorem nb_refillHeadOverlappingLoop (scPtr : ObjRef) : NBK (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillHeadOverlappingLoop _)

theorem nb_refillUnblockCheck (scPtr : ObjRef) : NBK (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillUnblockCheck _)

theorem nb_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NBK (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_ifCondRefillUnblockCheck _ _ _)

theorem nb_restartThreadIfNoFault (t : ObjRef) : NBK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_restartThreadIfNoFault _)

theorem nb_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NBK (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartEpQueuedThread _ _)

theorem nb_cancelAllIpc (epptr : ObjRef) : NBK (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelAllIpc _)

theorem nb_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NBK (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartNtfnQueuedThread _ _)

theorem nb_cancelAllSignals (ntfnptr : ObjRef) : NBK (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelAllSignals _)

theorem nb_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NBK (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_removeAndRestartBadgedThread _ _ _)

theorem nb_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NBK (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelBadgedSends _ _)

theorem nb_cancelSignal (threadptr ntfnptr : ObjRef) : NBK (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelSignal _ _)

theorem nb_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NBK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getSkObjRef _ _ _)

theorem nb_replyRemoveTcb (tptr rptr : ObjRef) : NBK (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyRemoveTcb _ _)

theorem nb_cancelIpc (tptr : ObjRef) : NBK (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_cancelIpc _)

theorem nb_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NBK (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capSwap _ _ _ _)

theorem nb_capSwapForDelete (slot1 slot2 : CslotPtr) : NBK (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capSwapForDelete _ _)

theorem nb_deletedIrqHandler (irq : Irq) : NBK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deletedIrqHandler _)

theorem nb_postCapDeletion (cap : Cap) : NBK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_postCapDeletion _)

theorem nb_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NBK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_emptySlot _ _)

theorem nb_replyUnlinkSc (scPtr replyPtr : ObjRef) : NBK (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyUnlinkSc _ _)

theorem nb_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NBK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScObjRef _ _)

theorem nb_testReschedule (fromTptr : ObjRef) : NBK (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_testReschedule _)

theorem nb_schedContextDonate (scPtr tcbPtr : ObjRef) : NBK (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextDonate _ _)

theorem nb_replyRemove (caller r : ObjRef) : NBK (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyRemove _ _)

theorem nb_unbindMaybeNotification (ntfnptr : ObjRef) : NBK (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindMaybeNotification _)

theorem nb_fastFinalise (a0 : Cap) (a1 : Bool) : NBK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fastFinalise _ _)

theorem nb_capDeleteOne (slot : CslotPtr) : NBK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capDeleteOne _)

theorem nb_getIrqSlot (irq : Irq) : NBK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getIrqSlot _)

theorem nb_deletingIrqHandler (irq : Irq) : NBK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_deletingIrqHandler _)

theorem nb_prepareThreadDelete (threadPtr : ObjRef) : NBK (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_prepareThreadDelete _)

theorem nb_schedContextSetInactive (scPtr : ObjRef) : NBK (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextSetInactive _)

theorem nb_schedContextUnbindTcb (scPtr : ObjRef) : NBK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindTcb _)

theorem nb_schedContextUnbindAllTcbs (scPtr : ObjRef) : NBK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindAllTcbs _)

theorem nb_schedContextUnbindReply (scPtr : ObjRef) : NBK (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindReply _)

theorem nb_schedContextUnbindYieldFrom (scPtr : ObjRef) : NBK (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextUnbindYieldFrom _)

theorem nb_updateRestartPc (threadPtr : ObjRef) : NBK (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRestartPc _)

theorem nb_suspend (thread : ObjRef) : NBK (suspend (Z := Unit) thread) := by
  unfold suspend; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_suspend _)

theorem nb_unbindFromSc (tcbPtr : ObjRef) : NBK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindFromSc _)

theorem nb_unbindNotification (tcb : ObjRef) : NBK (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unbindNotification _)

theorem nb_finaliseCap (a0 : Cap) (a1 : Bool) : NBK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_finaliseCap _ _)

theorem nb_getScActive (scPtr : ObjRef) : NBK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScActive _)

theorem nb_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NBKE f) (h_g : NBKE g) : NBKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; nb_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_orChoiceE _ _ _ ?_ ?_)

theorem nb_updateTimeStamp  : NBK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateTimeStamp)

theorem nb_preemptionPoint  : NBKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem nb_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NBK (f k)) (k : RecDelCall) : NBKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NBKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; nb_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; nb_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> nb_auto
    all_goals exact hrec' _

theorem nb_recDel (c : RecDelCall) : NBKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => nb_recDelF hf k) c
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_recDel _)

theorem nb_capDelete (slot : CslotPtr) : NBKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capDelete _)

theorem nb_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NBKE m) : NBKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_capFaultOnFailure _ _ _ ?_)

theorem nb_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NBK (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem nb_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NBK (f k)) (sl : CslotPtr) : NBKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NBKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  nb_auto
  all_goals exact hrec' _

theorem nb_capRevoke (sl : CslotPtr) : NBKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => nb_capRevokeF hf k) sl
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_capRevoke _)

theorem nb_captransferFromWords (ptr : Word) : NBK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_captransferFromWords _)

theorem nb_isValidTimeoutHandler (tptr : ObjRef) : NBK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isValidTimeoutHandler _)

theorem nb_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NBK (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_makeArchFaultMsg _ _)

theorem nb_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NBK (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_makeFaultMsg _ _)

theorem nb_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NBK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doFaultTransfer _ _ _ _)

theorem nb_loadWordOffs (ptr : ObjRef) (offs : Nat) : NBK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadWordOffs _ _)

theorem nb_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NBK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_copyMrs _ _ _ _ _)

theorem nb_getMessageInfo (thread : ObjRef) : NBK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getMessageInfo _)

theorem nb_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NBK (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; nb_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getExtraCptrs _ _)

theorem nb_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NBKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupSlotForThread _ _)

theorem nb_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NBKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupCapAndSlot _ _)
end

end Fl4Proofs.P3.SInvL
