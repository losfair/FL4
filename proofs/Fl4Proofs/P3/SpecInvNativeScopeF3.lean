/- invA: NativeScope frame lemmas, part 3 (generated; see SpecInvNativeScopeF1). -/
import Fl4Proofs.P3.SpecInvNativeScopeF2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem ns_tcbEpDequeue (tptr epPtr : ObjRef) : NSK (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbEpDequeue _ _)

theorem ns_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : NSK (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_blockedCancelIpc _ _ _)

theorem ns_isRoundRobin (scPtr : ObjRef) : NSK (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isRoundRobin _)

theorem ns_getRefillHead (scPtr : ObjRef) : NSK (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getRefillHead _)

theorem ns_refillPopHead (scPtr : ObjRef) : NSK (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillPopHead _)

theorem ns_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NSK (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRefillHd _ _)

theorem ns_mergeOverlappingRefills (scPtr : ObjRef) : NSK (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_mergeOverlappingRefills _)

theorem ns_refillHeadOverlappingLoop (scPtr : ObjRef) : NSK (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillHeadOverlappingLoop _)

theorem ns_refillUnblockCheck (scPtr : ObjRef) : NSK (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillUnblockCheck _)

theorem ns_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NSK (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_ifCondRefillUnblockCheck _ _ _)

theorem ns_restartThreadIfNoFault (t : ObjRef) : NSK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_restartThreadIfNoFault _)

theorem ns_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NSK (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartEpQueuedThread _ _)

theorem ns_cancelAllIpc (epptr : ObjRef) : NSK (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelAllIpc _)

theorem ns_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : NSK (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbNtfnDequeue _ _)

theorem ns_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NSK (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartNtfnQueuedThread _ _)

theorem ns_cancelAllSignals (ntfnptr : ObjRef) : NSK (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelAllSignals _)

theorem ns_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NSK (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_removeAndRestartBadgedThread _ _ _)

theorem ns_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NSK (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelBadgedSends _ _)

theorem ns_cancelSignal (threadptr ntfnptr : ObjRef) : NSK (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelSignal _ _)

theorem ns_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NSK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getSkObjRef _ _ _)

theorem ns_replyRemoveTcb (tptr rptr : ObjRef) : NSK (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyRemoveTcb _ _)

theorem ns_cancelIpc (tptr : ObjRef) : NSK (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_cancelIpc _)

theorem ns_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NSK (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capSwap _ _ _ _)

theorem ns_capSwapForDelete (slot1 slot2 : CslotPtr) : NSK (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capSwapForDelete _ _)

theorem ns_deletedIrqHandler (irq : Irq) : NSK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deletedIrqHandler _)

theorem ns_postCapDeletion (cap : Cap) : NSK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_postCapDeletion _)

theorem ns_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NSK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_emptySlot _ _)

theorem ns_replyUnlinkSc (scPtr replyPtr : ObjRef) : NSK (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyUnlinkSc _ _)

theorem ns_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NSK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScObjRef _ _)

theorem ns_testReschedule (fromTptr : ObjRef) : NSK (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_testReschedule _)

theorem ns_schedContextDonate (scPtr tcbPtr : ObjRef) : NSK (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextDonate _ _)

theorem ns_replyRemove (caller r : ObjRef) : NSK (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyRemove _ _)

theorem ns_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : NSK (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextMaybeUnbindNtfn _)

theorem ns_unbindMaybeNotification (ntfnptr : ObjRef) : NSK (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindMaybeNotification _)

theorem ns_fastFinalise (a0 : Cap) (a1 : Bool) : NSK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fastFinalise _ _)

theorem ns_capDeleteOne (slot : CslotPtr) : NSK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capDeleteOne _)

theorem ns_getIrqSlot (irq : Irq) : NSK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getIrqSlot _)

theorem ns_deletingIrqHandler (irq : Irq) : NSK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_deletingIrqHandler _)

theorem ns_prepareThreadDelete (threadPtr : ObjRef) : NSK (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_prepareThreadDelete _)

theorem ns_schedContextSetInactive (scPtr : ObjRef) : NSK (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextSetInactive _)

theorem ns_schedContextUnbindTcb (scPtr : ObjRef) : NSK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindTcb _)

theorem ns_schedContextUnbindAllTcbs (scPtr : ObjRef) : NSK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindAllTcbs _)

theorem ns_schedContextUnbindNtfn (scPtr : ObjRef) : NSK (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindNtfn _)

theorem ns_schedContextUnbindReply (scPtr : ObjRef) : NSK (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindReply _)

theorem ns_schedContextUnbindYieldFrom (scPtr : ObjRef) : NSK (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextUnbindYieldFrom _)

theorem ns_updateRestartPc (threadPtr : ObjRef) : NSK (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateRestartPc _)

theorem ns_suspend (thread : ObjRef) : NSK (suspend (Z := Unit) thread) := by
  unfold suspend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_suspend _)

theorem ns_unbindFromSc (tcbPtr : ObjRef) : NSK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindFromSc _)

theorem ns_unbindNotification (tcb : ObjRef) : NSK (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unbindNotification _)

theorem ns_finaliseCap (a0 : Cap) (a1 : Bool) : NSK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_finaliseCap _ _)

theorem ns_getScActive (scPtr : ObjRef) : NSK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScActive _)

theorem ns_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NSKE f) (h_g : NSKE g) : NSKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ns_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_orChoiceE _ _ _ ?_ ?_)

theorem ns_updateTimeStamp  : NSK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateTimeStamp)

theorem ns_preemptionPoint  : NSKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem ns_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NSK (f k)) (k : RecDelCall) : NSKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ns_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ns_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ns_auto
    all_goals exact hrec' _

theorem ns_recDel (c : RecDelCall) : NSKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ns_recDelF hf k) c
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_recDel _)

theorem ns_capDelete (slot : CslotPtr) : NSKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capDelete _)

theorem ns_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NSKE m) : NSKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_capFaultOnFailure _ _ _ ?_)

theorem ns_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NSK (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem ns_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NSK (f k)) (sl : CslotPtr) : NSKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NSKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ns_auto
  all_goals exact hrec' _

theorem ns_capRevoke (sl : CslotPtr) : NSKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ns_capRevokeF hf k) sl
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capRevoke _)

theorem ns_captransferFromWords (ptr : Word) : NSK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_captransferFromWords _)

theorem ns_isValidTimeoutHandler (tptr : ObjRef) : NSK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isValidTimeoutHandler _)

theorem ns_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NSK (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_makeArchFaultMsg _ _)

theorem ns_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NSK (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_makeFaultMsg _ _)

theorem ns_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NSK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doFaultTransfer _ _ _ _)

theorem ns_loadWordOffs (ptr : ObjRef) (offs : Nat) : NSK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadWordOffs _ _)

theorem ns_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NSK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_copyMrs _ _ _ _ _)

theorem ns_getMessageInfo (thread : ObjRef) : NSK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getMessageInfo _)
end

end Fl4Proofs.P3.SInv
