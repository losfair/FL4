
/- epq1: generated frames `PZK` (sg1's SpecInvSgI3 renamed, the refill writers and the configure path removed; see SpecInvEqG1). -/
import Fl4Proofs.P3.SpecInvEqG2
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000


theorem pz_tcbEpDequeue (tptr epPtr : ObjRef) : PZK (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbEpDequeue _ _)

theorem pz_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : PZK (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_blockedCancelIpc _ _ _)

theorem pz_isRoundRobin (scPtr : ObjRef) : PZK (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_isRoundRobin _)

theorem pz_getRefillHead (scPtr : ObjRef) : PZK (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getRefillHead _)

theorem pz_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : PZK (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_ifCondRefillUnblockCheck _ _ _)

theorem pz_restartThreadIfNoFault (t : ObjRef) : PZK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_restartThreadIfNoFault _)

theorem pz_removeAndRestartEpQueuedThread (t epptr : ObjRef) : PZK (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_removeAndRestartEpQueuedThread _ _)

theorem pz_cancelAllIpc (epptr : ObjRef) : PZK (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_cancelAllIpc _)

theorem pz_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : PZK (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbNtfnDequeue _ _)

theorem pz_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : PZK (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_removeAndRestartNtfnQueuedThread _ _)

theorem pz_cancelAllSignals (ntfnptr : ObjRef) : PZK (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_cancelAllSignals _)

theorem pz_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : PZK (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_removeAndRestartBadgedThread _ _ _)

theorem pz_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : PZK (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_cancelBadgedSends _ _)

theorem pz_cancelSignal (threadptr ntfnptr : ObjRef) : PZK (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_cancelSignal _ _)

theorem pz_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : PZK (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getSkObjRef _ _ _)

theorem pz_replyRemoveTcb (tptr rptr : ObjRef) : PZK (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_replyRemoveTcb _ _)

theorem pz_cancelIpc (tptr : ObjRef) : PZK (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_cancelIpc _)

theorem pz_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : PZK (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capSwap _ _ _ _)

theorem pz_capSwapForDelete (slot1 slot2 : CslotPtr) : PZK (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capSwapForDelete _ _)

theorem pz_deletedIrqHandler (irq : Irq) : PZK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_deletedIrqHandler _)

theorem pz_postCapDeletion (cap : Cap) : PZK (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_postCapDeletion _)

theorem pz_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : PZK (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_emptySlot _ _)

theorem pz_replyUnlinkSc (scPtr replyPtr : ObjRef) : PZK (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_replyUnlinkSc _ _)

theorem pz_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : PZK (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getScObjRef _ _)

theorem pz_testReschedule (fromTptr : ObjRef) : PZK (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_testReschedule _)

theorem pz_schedContextDonate (scPtr tcbPtr : ObjRef) : PZK (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextDonate _ _)

theorem pz_replyRemove (caller r : ObjRef) : PZK (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_replyRemove _ _)

theorem pz_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : PZK (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextMaybeUnbindNtfn _)

theorem pz_unbindMaybeNotification (ntfnptr : ObjRef) : PZK (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unbindMaybeNotification _)

theorem pz_fastFinalise (a0 : Cap) (a1 : Bool) : PZK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fastFinalise _ _)

theorem pz_capDeleteOne (slot : CslotPtr) : PZK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capDeleteOne _)

theorem pz_getIrqSlot (irq : Irq) : PZK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getIrqSlot _)

theorem pz_deletingIrqHandler (irq : Irq) : PZK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_deletingIrqHandler _)

theorem pz_prepareThreadDelete (threadPtr : ObjRef) : PZK (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_prepareThreadDelete _)

theorem pz_schedContextUnbindTcb (scPtr : ObjRef) : PZK (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextUnbindTcb _)

theorem pz_schedContextUnbindAllTcbs (scPtr : ObjRef) : PZK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextUnbindAllTcbs _)

theorem pz_schedContextUnbindNtfn (scPtr : ObjRef) : PZK (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextUnbindNtfn _)

theorem pz_schedContextUnbindReply (scPtr : ObjRef) : PZK (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextUnbindReply _)

theorem pz_schedContextUnbindYieldFrom (scPtr : ObjRef) : PZK (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextUnbindYieldFrom _)

theorem pz_updateRestartPc (threadPtr : ObjRef) : PZK (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateRestartPc _)

theorem pz_suspend (thread : ObjRef) : PZK (suspend (Z := Unit) thread) := by
  unfold suspend; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_suspend _)

theorem pz_unbindFromSc (tcbPtr : ObjRef) : PZK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unbindFromSc _)

theorem pz_unbindNotification (tcb : ObjRef) : PZK (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unbindNotification _)

theorem pz_finaliseCap (a0 : Cap) (a1 : Bool) : PZK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_finaliseCap _ _)

theorem pz_getScActive (scPtr : ObjRef) : PZK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getScActive _)

theorem pz_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : PZKE f) (h_g : PZKE g) : PZKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; pz_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_orChoiceE _ _ _ ?_ ?_)

theorem pz_updateTimeStamp  : PZK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateTimeStamp)

theorem pz_preemptionPoint  : PZKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem pz_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, PZK (f k)) (k : RecDelCall) : PZKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, PZKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; pz_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; pz_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> pz_auto
    all_goals exact hrec' _

theorem pz_recDel (c : RecDelCall) : PZKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => pz_recDelF hf k) c
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_recDel _)

theorem pz_capDelete (slot : CslotPtr) : PZKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capDelete _)

theorem pz_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : PZKE m) : PZKE (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_capFaultOnFailure _ _ _ ?_)

theorem pz_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : PZK (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem pz_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, PZK (f k)) (sl : CslotPtr) : PZKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, PZKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  pz_auto
  all_goals exact hrec' _

theorem pz_capRevoke (sl : CslotPtr) : PZKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => pz_capRevokeF hf k) sl
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capRevoke _)

theorem pz_captransferFromWords (ptr : Word) : PZK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_captransferFromWords _)

theorem pz_isValidTimeoutHandler (tptr : ObjRef) : PZK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_isValidTimeoutHandler _)

theorem pz_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : PZK (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_makeArchFaultMsg _ _)

theorem pz_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : PZK (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_makeFaultMsg _ _)

theorem pz_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : PZK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_doFaultTransfer _ _ _ _)

theorem pz_loadWordOffs (ptr : ObjRef) (offs : Nat) : PZK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_loadWordOffs _ _)

theorem pz_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : PZK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_copyMrs _ _ _ _ _)

theorem pz_getMessageInfo (thread : ObjRef) : PZK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getMessageInfo _)
end

end Fl4Proofs.P3.SInvE
