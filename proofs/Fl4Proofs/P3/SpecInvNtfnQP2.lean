/- nq3: the PJ frame family, part 2 (generated: proofs/scratch/nq3/mkpj.sh; see SpecInvNtfnQP). -/
import Fl4Proofs.P3.SpecInvNtfnQP1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Lp : List ObjRef}

theorem pj_removeAndRestartEpQueuedThread (t epptr : ObjRef) : PJK Lp (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_removeAndRestartEpQueuedThread _ _)

theorem pj_cancelAllIpc (epptr : ObjRef) : PJK Lp (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_cancelAllIpc _)

theorem pj_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : PJK Lp (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_tcbNtfnDequeue _ _)

theorem pj_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : PJK Lp (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_removeAndRestartNtfnQueuedThread _ _)

theorem pj_cancelAllSignals (ntfnptr : ObjRef) : PJK Lp (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_cancelAllSignals _)

theorem pj_cancelSignal (threadptr ntfnptr : ObjRef) : PJK Lp (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_cancelSignal _ _)

theorem pj_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : PJK Lp (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getSkObjRef _ _ _)

theorem pj_replyRemoveTcb (tptr rptr : ObjRef) : PJK Lp (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_replyRemoveTcb _ _)

theorem pj_cancelIpc (tptr : ObjRef) : PJK Lp (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_cancelIpc _)

theorem pj_setCdt (t : Cdt) : PJK Lp (setCdt (Z := Unit) t) := by
  unfold setCdt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setCdt _)

theorem pj_setOriginal (slot : CslotPtr) (v : Bool) : PJK Lp (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setOriginal _ _)

theorem pj_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : PJK Lp (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_capSwap _ _ _ _)

theorem pj_capSwapForDelete (slot1 slot2 : CslotPtr) : PJK Lp (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_capSwapForDelete _ _)

theorem pj_setIrqState (state : IrqState) (irq : Irq) : PJK Lp (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setIrqState _ _)

theorem pj_deletedIrqHandler (irq : Irq) : PJK Lp (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_deletedIrqHandler _)

theorem pj_postCapDeletion (cap : Cap) : PJK Lp (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_postCapDeletion _)

theorem pj_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : PJK Lp (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_emptySlot _ _)

theorem pj_replyUnlinkSc (scPtr replyPtr : ObjRef) : PJK Lp (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_replyUnlinkSc _ _)

theorem pj_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : PJK Lp (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getScObjRef _ _)

theorem pj_tcbReleaseRemove (tcbPtr : ObjRef) : PJK Lp (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_tcbReleaseRemove _)

theorem pj_testReschedule (fromTptr : ObjRef) : PJK Lp (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_testReschedule _)

theorem pj_schedContextDonate (scPtr tcbPtr : ObjRef) : PJK Lp (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextDonate _ _)

theorem pj_replyRemove (caller r : ObjRef) : PJK Lp (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_replyRemove _ _)

theorem pj_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : PJK Lp (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextMaybeUnbindNtfn _)

theorem pj_unbindMaybeNotification (ntfnptr : ObjRef) : PJK Lp (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unbindMaybeNotification _)

theorem pj_fastFinalise (a0 : Cap) (a1 : Bool) : PJK Lp (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_fastFinalise _ _)

theorem pj_isFinalCap (cap : Cap) : PJK Lp (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_isFinalCap _)

theorem pj_capDeleteOne (slot : CslotPtr) : PJK Lp (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_capDeleteOne _)

theorem pj_getIrqSlot (irq : Irq) : PJK Lp (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getIrqSlot _)

theorem pj_deletingIrqHandler (irq : Irq) : PJK Lp (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_deletingIrqHandler _)

theorem pj_loadFpuState (t : ObjRef) : PJK Lp (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_loadFpuState _)

theorem pj_saveFpuState (t : ObjRef) : PJK Lp (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_saveFpuState _)

theorem pj_setX64CurrentFpuOwner (newOwner : Option ObjRef) : PJK Lp (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setX64CurrentFpuOwner _)

theorem pj_switchLocalFpuOwner (newOwner : Option ObjRef) : PJK Lp (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_switchLocalFpuOwner _)

theorem pj_fpuRelease (threadPtr : ObjRef) : PJK Lp (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_fpuRelease _)

theorem pj_prepareThreadDelete (threadPtr : ObjRef) : PJK Lp (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_prepareThreadDelete _)

theorem pj_schedContextSetInactive (scPtr : ObjRef) : PJK Lp (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextSetInactive _)

theorem pj_schedContextUnbindTcb (scPtr : ObjRef) : PJK Lp (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUnbindTcb _)

theorem pj_schedContextUnbindAllTcbs (scPtr : ObjRef) : PJK Lp (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUnbindAllTcbs _)

theorem pj_schedContextUnbindNtfn (scPtr : ObjRef) : PJK Lp (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUnbindNtfn _)

theorem pj_schedContextUnbindReply (scPtr : ObjRef) : PJK Lp (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUnbindReply _)

theorem pj_schedContextCancelYieldTo (thread : ObjRef) : PJK Lp (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextCancelYieldTo _)

theorem pj_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : PJK Lp (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_lookupIpcBuffer _ _)

theorem pj_setMessageInfo (thread : ObjRef) (info : MessageInfo) : PJK Lp (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setMessageInfo _ _)

theorem pj_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : PJK Lp (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_storeWordOffs _ _ _)

theorem pj_replyFromKernel (thread : ObjRef) (x : Data × List Data) : PJK Lp (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_replyFromKernel _ _)

theorem pj_schedContextUpdateConsumed (scPtr : ObjRef) : PJK Lp (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUpdateConsumed _)

theorem pj_setConsumed (scPtr tcbPtr : ObjRef) : PJK Lp (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setConsumed _ _)

theorem pj_completeYieldTo (tcbPtr : ObjRef) : PJK Lp (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_completeYieldTo _)

theorem pj_schedContextUnbindYieldFrom (scPtr : ObjRef) : PJK Lp (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_schedContextUnbindYieldFrom _)

theorem pj_updateRestartPc (threadPtr : ObjRef) : PJK Lp (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateRestartPc _)

theorem pj_suspend (thread : ObjRef) : PJK Lp (suspend (Z := Unit) thread) := by
  unfold suspend; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_suspend _)

theorem pj_unbindFromSc (tcbPtr : ObjRef) : PJK Lp (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unbindFromSc _)

theorem pj_unbindNotification (tcb : ObjRef) : PJK Lp (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unbindNotification _)

theorem pj_finaliseCap (a0 : Cap) (a1 : Bool) : PJK Lp (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_finaliseCap _ _)

theorem pj_getScActive (scPtr : ObjRef) : PJK Lp (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getScActive _)

theorem pj_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : PJKE Lp f) (h_g : PJKE Lp g) : PJKE Lp (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; pj_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible refine pj_orChoiceE _ _ _ ?_ ?_)

theorem pj_updateTimeStamp  : PJK Lp (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateTimeStamp)

theorem pj_preemptionPoint  : PJKE Lp (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_preemptionPoint)

theorem pj_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : PJK Lp m) : PJKE Lp (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; pj_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible refine pj_withoutPreemption _ ?_)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem pj_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, PJK Lp (f k)) (k : RecDelCall) : PJKE Lp (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, PJKE Lp (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; pj_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; pj_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> pj_auto
    all_goals exact hrec' _

theorem pj_recDel (c : RecDelCall) : PJKE Lp (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => pj_recDelF hf k) c
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_recDel _)

theorem pj_capDelete (slot : CslotPtr) : PJKE Lp (capDelete (Z := Unit) slot) := by
  unfold capDelete; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_capDelete _)

theorem pj_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : PJK Lp (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setUntypedCapAsFull _ _ _)

theorem pj_updateCdt (f : Cdt → Cdt) : PJK Lp (updateCdt (Z := Unit) f) := by
  unfold updateCdt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateCdt _)

theorem pj_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : PJK Lp (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_capInsert _ _ _)

theorem pj_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : PJK Lp m) : PJK Lp (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; pj_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible refine pj_checkCapAt _ _ _ ?_)

theorem pj_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : PJKE Lp (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_installTcbCap _ _ _ _)

theorem pj_setMcpriority (ref : ObjRef) (mcp : Priority) : PJK Lp (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setMcpriority _ _)

end

end Fl4Proofs.P3.SInv
