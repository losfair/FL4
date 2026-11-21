/- rd14h: the QT frame family, part 2 (generated: proofs/scratch/rd14h/mkqt.sh; see SpecInvRd14hQ). -/
import Fl4Proofs.P3.SpecInvRd14hQ1
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Tq : ObjRef}

theorem qth_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : QTK Tq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getSkObjRef _ _ _)

theorem qth_replyRemoveTcb (tptr rptr : ObjRef) : QTK Tq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_replyRemoveTcb _ _)

theorem qth_replyUnlinkSc (scPtr replyPtr : ObjRef) : QTK Tq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_replyUnlinkSc _ _)

theorem qth_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : QTK Tq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getScObjRef _ _)

theorem qth_tcbReleaseRemove (tcbPtr : ObjRef) : QTK Tq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbReleaseRemove _)

theorem qth_testReschedule (fromTptr : ObjRef) : QTK Tq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_testReschedule _)

theorem qth_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : QTK Tq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextMaybeUnbindNtfn _)

theorem qth_unbindMaybeNotification (ntfnptr : ObjRef) : QTK Tq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unbindMaybeNotification _)

theorem qth_isFinalCap (cap : Cap) : QTK Tq (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_isFinalCap _)

theorem qth_getIrqSlot (irq : Irq) : QTK Tq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getIrqSlot _)

theorem qth_deletingIrqHandler (irq : Irq) : QTK Tq (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_deletingIrqHandler _)

theorem qth_loadFpuState (t : ObjRef) : QTK Tq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_loadFpuState _)

theorem qth_saveFpuState (t : ObjRef) : QTK Tq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_saveFpuState _)

theorem qth_setX64CurrentFpuOwner (newOwner : Option ObjRef) : QTK Tq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setX64CurrentFpuOwner _)

theorem qth_switchLocalFpuOwner (newOwner : Option ObjRef) : QTK Tq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_switchLocalFpuOwner _)

theorem qth_fpuRelease (threadPtr : ObjRef) : QTK Tq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_fpuRelease _)

theorem qth_prepareThreadDelete (threadPtr : ObjRef) : QTK Tq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_prepareThreadDelete _)

theorem qth_schedContextSetInactive (scPtr : ObjRef) : QTK Tq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextSetInactive _)

theorem qth_schedContextUnbindTcb (scPtr : ObjRef) : QTK Tq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUnbindTcb _)

theorem qth_schedContextUnbindAllTcbs (scPtr : ObjRef) : QTK Tq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUnbindAllTcbs _)

theorem qth_schedContextUnbindNtfn (scPtr : ObjRef) : QTK Tq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUnbindNtfn _)

theorem qth_schedContextUnbindReply (scPtr : ObjRef) : QTK Tq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUnbindReply _)

theorem qth_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : QTK Tq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_lookupIpcBuffer _ _)

theorem qth_setMessageInfo (thread : ObjRef) (info : MessageInfo) : QTK Tq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setMessageInfo _ _)

theorem qth_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : QTK Tq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_storeWordOffs _ _ _)

theorem qth_replyFromKernel (thread : ObjRef) (x : Data × List Data) : QTK Tq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_replyFromKernel _ _)

theorem qth_schedContextUpdateConsumed (scPtr : ObjRef) : QTK Tq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUpdateConsumed _)

theorem qth_setConsumed (scPtr tcbPtr : ObjRef) : QTK Tq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setConsumed _ _)

theorem qth_completeYieldTo (tcbPtr : ObjRef) : QTK Tq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_completeYieldTo _)

theorem qth_schedContextUnbindYieldFrom (scPtr : ObjRef) : QTK Tq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextUnbindYieldFrom _)

theorem qth_updateRestartPc (threadPtr : ObjRef) : QTK Tq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateRestartPc _)

theorem qth_unbindFromSc (tcbPtr : ObjRef) : QTK Tq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unbindFromSc _)

theorem qth_unbindNotification (tcb : ObjRef) : QTK Tq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unbindNotification _)

theorem qth_finaliseCap (a0 : Cap) (a1 : Bool) : QTK Tq (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_finaliseCap _ _)

theorem qth_getScActive (scPtr : ObjRef) : QTK Tq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getScActive _)

theorem qth_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : QTKE Tq f) (h_g : QTKE Tq g) : QTKE Tq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; qth_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible refine qth_orChoiceE _ _ _ ?_ ?_)

theorem qth_updateTimeStamp  : QTK Tq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateTimeStamp)

theorem qth_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : QTK Tq m) : QTKE Tq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; qth_auto
  all_goals first | exact h_m
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible refine qth_withoutPreemption _ ?_)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem qth_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, QTK Tq (f k)) (k : RecDelCall) : QTKE Tq (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, QTKE Tq (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; qth_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; qth_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> qth_auto
    all_goals exact hrec' _

theorem qth_recDel (c : RecDelCall) : QTKE Tq (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => qth_recDelF hf k) c
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_recDel _)

theorem qth_capDelete (slot : CslotPtr) : QTKE Tq (capDelete (Z := Unit) slot) := by
  unfold capDelete; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_capDelete _)

theorem qth_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : QTK Tq (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setUntypedCapAsFull _ _ _)

theorem qth_updateCdt (f : Cdt → Cdt) : QTK Tq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateCdt _)

theorem qth_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : QTK Tq (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_capInsert _ _ _)

theorem qth_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : QTK Tq (selectExt (Z := Unit) a S) := by
  unfold selectExt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_selectExt _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem qth_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, QTK Tq (f k)) (sl : CslotPtr) : QTKE Tq (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, QTKE Tq (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  qth_auto
  all_goals exact hrec' _

theorem qth_capRevoke (sl : CslotPtr) : QTKE Tq (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => qth_capRevokeF hf k) sl
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_capRevoke _)

theorem qth_getRefills (scPtr : ObjRef) : QTK Tq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getRefills _)

theorem qth_refillSize (scPtr : ObjRef) : QTK Tq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillSize _)

theorem qth_refillSingle (scPtr : ObjRef) : QTK Tq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillSingle _)

theorem qth_getRefillTail (scPtr : ObjRef) : QTK Tq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getRefillTail _)

theorem qth_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : QTK Tq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillAddTail _ _)

theorem qth_refillFull (scPtr : ObjRef) : QTK Tq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillFull _)

theorem qth_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : QTK Tq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateRefillTl _ _)

theorem qth_scheduleUsed (scPtr : ObjRef) (new : Refill) : QTK Tq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_scheduleUsed _ _)

theorem qth_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : QTK Tq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_chargeEntireHeadRefill _ _)

theorem qth_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : QTK Tq m) : QTK Tq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; qth_auto
  all_goals first | exact h_m
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible refine qth_checkCapAt _ _ _ ?_)

theorem qth_handleOverrun (scPtr : ObjRef) (usage : Ticks) : QTK Tq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_handleOverrun _ _)

theorem qth_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : QTK Tq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_mergeNonoverlappingHeadRefill _)

theorem qth_headInsufficientLoop (scPtr : ObjRef) : QTK Tq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_headInsufficientLoop _)

theorem qth_refillBudgetCheck (usage : Ticks) : QTK Tq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillBudgetCheck _)

theorem qth_refillBudgetCheckRoundRobin (usage : Ticks) : QTK Tq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillBudgetCheckRoundRobin _)

theorem qth_commitTime  : QTK Tq (commitTime (Z := Unit)) := by
  unfold commitTime; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_commitTime)

theorem qth_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : QTKE Tq (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_installTcbCap _ _ _ _)

theorem qth_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : QTKE Tq (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_installTcbFrameCap _ _ _)

theorem qth_maybeAddEmptyTail (scPtr : ObjRef) : QTK Tq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_maybeAddEmptyTail _)

theorem qth_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : QTK Tq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillNew _ _ _ _)

theorem qth_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : QTK Tq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillUpdate _ _ _ _)

theorem qth_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : QTK Tq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_orderedInsert _ _ _ _)

theorem qth_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : QTK Tq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_readyTimesAppend _ _)

theorem qth_tcbReleaseEnqueue (tcbPtr : ObjRef) : QTK Tq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbReleaseEnqueue _)

theorem qth_postpone (scPtr : ObjRef) : QTK Tq (postpone (Z := Unit) scPtr) := by
  unfold postpone; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_postpone _)

theorem qth_schedContextResume (scPtr : ObjRef) : QTK Tq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextResume _)

theorem qth_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : QTK Tq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_invokeSchedControlConfigureFlags _)

theorem qth_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : QTK Tq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbAppend _ _)

theorem qth_reorderEp (epPtr tptr : ObjRef) : QTK Tq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_reorderEp _ _)

theorem qth_reorderNtfn (ntfnPtr tptr : ObjRef) : QTK Tq (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_reorderNtfn _ _)

theorem qth_schedContextBindTcb (scPtr tcbPtr : ObjRef) : QTK Tq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_schedContextBindTcb _ _)

theorem qth_setMcpriority (ref : ObjRef) (mcp : Priority) : QTK Tq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setMcpriority _ _)

theorem qth_threadSetPriority (tptr : ObjRef) (prio : Priority) : QTK Tq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_threadSetPriority _ _)

theorem qth_setPriority (tptr : ObjRef) (prio : Priority) : QTK Tq (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setPriority _ _)

end

end Fl4Proofs.P3.SInvR.A14h
