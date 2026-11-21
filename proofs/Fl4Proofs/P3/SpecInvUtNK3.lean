/- ut7: IRQ-node frame lemmas `NK N`, part 3 (invA's NativeScope scripts renamed; see SpecInvUtNK1). -/
import Fl4Proofs.P3.SpecInvUtNK2
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef}

theorem nk_tcbEpDequeue (tptr epPtr : ObjRef) : NK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbEpDequeue _ _)

theorem nk_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : NK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_blockedCancelIpc _ _ _)

theorem nk_isRoundRobin (scPtr : ObjRef) : NK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isRoundRobin _)

theorem nk_getRefillHead (scPtr : ObjRef) : NK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getRefillHead _)

theorem nk_refillPopHead (scPtr : ObjRef) : NK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillPopHead _)

theorem nk_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateRefillHd _ _)

theorem nk_mergeOverlappingRefills (scPtr : ObjRef) : NK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_mergeOverlappingRefills _)

theorem nk_refillHeadOverlappingLoop (scPtr : ObjRef) : NK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillHeadOverlappingLoop _)

theorem nk_refillUnblockCheck (scPtr : ObjRef) : NK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillUnblockCheck _)

theorem nk_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_ifCondRefillUnblockCheck _ _ _)

theorem nk_restartThreadIfNoFault (t : ObjRef) : NK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_restartThreadIfNoFault _)

theorem nk_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_removeAndRestartEpQueuedThread _ _)

theorem nk_cancelAllIpc (epptr : ObjRef) : NK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_cancelAllIpc _)

theorem nk_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : NK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbNtfnDequeue _ _)

theorem nk_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_removeAndRestartNtfnQueuedThread _ _)

theorem nk_cancelAllSignals (ntfnptr : ObjRef) : NK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_cancelAllSignals _)

theorem nk_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_removeAndRestartBadgedThread _ _ _)

theorem nk_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_cancelBadgedSends _ _)

theorem nk_cancelSignal (threadptr ntfnptr : ObjRef) : NK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_cancelSignal _ _)

theorem nk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getSkObjRef _ _ _)

theorem nk_replyRemoveTcb (tptr rptr : ObjRef) : NK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyRemoveTcb _ _)

theorem nk_cancelIpc (tptr : ObjRef) : NK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_cancelIpc _)

theorem nk_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capSwap _ _ _ _)

theorem nk_capSwapForDelete (slot1 slot2 : CslotPtr) : NK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capSwapForDelete _ _)

theorem nk_deletedIrqHandler (irq : Irq) : NK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deletedIrqHandler _)

theorem nk_postCapDeletion (cap : Cap) : NK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_postCapDeletion _)

theorem nk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_emptySlot _ _)

theorem nk_replyUnlinkSc (scPtr replyPtr : ObjRef) : NK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyUnlinkSc _ _)

theorem nk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getScObjRef _ _)

theorem nk_testReschedule (fromTptr : ObjRef) : NK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_testReschedule _)

theorem nk_schedContextDonate (scPtr tcbPtr : ObjRef) : NK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextDonate _ _)

theorem nk_replyRemove (caller r : ObjRef) : NK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyRemove _ _)

theorem nk_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : NK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextMaybeUnbindNtfn _)

theorem nk_unbindMaybeNotification (ntfnptr : ObjRef) : NK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unbindMaybeNotification _)

theorem nk_fastFinalise (a0 : Cap) (a1 : Bool) : NK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fastFinalise _ _)

theorem nk_capDeleteOne (slot : CslotPtr) : NK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capDeleteOne _)

theorem nk_getIrqSlot (irq : Irq) : NK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getIrqSlot _)

theorem nk_deletingIrqHandler (irq : Irq) : NK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_deletingIrqHandler _)

theorem nk_prepareThreadDelete (threadPtr : ObjRef) : NK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_prepareThreadDelete _)

theorem nk_schedContextSetInactive (scPtr : ObjRef) : NK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextSetInactive _)

theorem nk_schedContextUnbindTcb (scPtr : ObjRef) : NK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUnbindTcb _)

theorem nk_schedContextUnbindAllTcbs (scPtr : ObjRef) : NK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUnbindAllTcbs _)

theorem nk_schedContextUnbindNtfn (scPtr : ObjRef) : NK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUnbindNtfn _)

theorem nk_schedContextUnbindReply (scPtr : ObjRef) : NK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUnbindReply _)

theorem nk_schedContextUnbindYieldFrom (scPtr : ObjRef) : NK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextUnbindYieldFrom _)

theorem nk_updateRestartPc (threadPtr : ObjRef) : NK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateRestartPc _)

theorem nk_suspend (thread : ObjRef) : NK N (suspend (Z := Unit) thread) := by
  unfold suspend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_suspend _)

theorem nk_unbindFromSc (tcbPtr : ObjRef) : NK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unbindFromSc _)

theorem nk_unbindNotification (tcb : ObjRef) : NK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unbindNotification _)

theorem nk_finaliseCap (a0 : Cap) (a1 : Bool) : NK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_finaliseCap _ _)

theorem nk_getScActive (scPtr : ObjRef) : NK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getScActive _)

theorem nk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NKE N f) (h_g : NKE N g) : NKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; nk_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_orChoiceE _ _ _ ?_ ?_)

theorem nk_updateTimeStamp  : NK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateTimeStamp)

theorem nk_preemptionPoint  : NKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem nk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NK N (f k)) (k : RecDelCall) : NKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; nk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; nk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> nk_auto
    all_goals exact hrec' _

theorem nk_recDel (c : RecDelCall) : NKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => nk_recDelF hf k) c
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_recDel _)

theorem nk_capDelete (slot : CslotPtr) : NKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capDelete _)

theorem nk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NKE N m) : NKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_capFaultOnFailure _ _ _ ?_)

theorem nk_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem nk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NK N (f k)) (sl : CslotPtr) : NKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  nk_auto
  all_goals exact hrec' _

theorem nk_capRevoke (sl : CslotPtr) : NKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => nk_capRevokeF hf k) sl
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capRevoke _)

theorem nk_captransferFromWords (ptr : Word) : NK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_captransferFromWords _)

theorem nk_isValidTimeoutHandler (tptr : ObjRef) : NK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isValidTimeoutHandler _)

theorem nk_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_makeArchFaultMsg _ _)

theorem nk_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_makeFaultMsg _ _)

theorem nk_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_doFaultTransfer _ _ _ _)

theorem nk_loadWordOffs (ptr : ObjRef) (offs : Nat) : NK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_loadWordOffs _ _)

theorem nk_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_copyMrs _ _ _ _ _)

theorem nk_getMessageInfo (thread : ObjRef) : NK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getMessageInfo _)
end

end Fl4Proofs.P3.SInvU
