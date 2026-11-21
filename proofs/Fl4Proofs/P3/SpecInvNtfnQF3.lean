/- nq1: NtfnQB family lemmas, part 3 (generated; see SpecInvNtfnQF1). -/
import Fl4Proofs.P3.SpecInvNtfnQF2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_blockedCancelIpc (st : ThreadState) (t : ObjRef) (r : Option ObjRef) :
    NQK Kq (blockedCancelIpc (Z := Unit) st t r) :=
  fun σ hσ y hy => nq_tail (nq_blockedCancelIpc_post st t r σ hσ y hy)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_blockedCancelIpc _ _ _)

/-- `cancel_signal`: the dequeued thread is in no queue when it becomes Inactive. -/
theorem nq_cancelSignal_post (t n : ObjRef) : HK (NQ Kq) (NQ (t :: Kq)) (cancelSignal (Z := Unit) t n) := by
  unfold cancelSignal
  exact hk_bind (nq_tcbNtfnDequeue_post t n) fun _ => nq_setThreadState_q t _ (fun h => h)

theorem nq_cancelSignal (t n : ObjRef) : NQK Kq (cancelSignal (Z := Unit) t n) :=
  fun σ hσ y hy => nq_tail (nq_cancelSignal_post t n σ hσ y hy)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_cancelSignal _ _)

theorem nq_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : NQK Kq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getSkObjRef _ _ _)

theorem nq_replyRemoveTcb (tptr rptr : ObjRef) (hk_tptr : tptr ∈ Kq) : NQK Kq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_replyRemoveTcb _ _ ?_) <;> nq_mem))

/-- `cancel_ipc`: afterwards the thread is in no queue. -/
theorem nq_cancelIpc_post (t : ObjRef) : HK (NQ Kq) (NQ (t :: Kq)) (cancelIpc (Z := Unit) t) := by
  intro σ hσ y hy
  unfold cancelIpc getThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hz
  dsimp only at hy
  cases hs : x.tcbState <;> rw [hs] at hy <;> (try dsimp only at hy)
  case blockedOnNotification n =>
    obtain ⟨w, hw, hy⟩ := hy
    have h1 : NQ Kq w.2 := nq_threadSet (fun tcb => { tcb with tcbFault := none }) t (fun _ => rfl) σ hσ w hw
    exact nq_cancelSignal_post t n w.2 h1 y hy
  case blockedOnSend ep d =>
    obtain ⟨w, hw, hy⟩ := hy
    exact nq_blockedCancelIpc_post _ t none w.2 (nq_threadSet (fun tcb => { tcb with tcbFault := none }) t (fun _ => rfl) σ hσ w hw) y hy
  case blockedOnReceive ep r d =>
    obtain ⟨w, hw, hy⟩ := hy
    exact nq_blockedCancelIpc_post _ t r w.2 (nq_threadSet (fun tcb => { tcb with tcbFault := none }) t (fun _ => rfl) σ hσ w hw) y hy
  all_goals
    have hb : ¬ isBoN x.tcbState := by rw [hs]; exact fun h => h
    have he : epBlocked x.tcbState = none := by rw [hs]; rfl
    refine (?_ : NQK (t :: Kq) _) σ (nq_consR hσ hx hb he) y hy
    nq_auto

theorem nq_cancelIpc (t : ObjRef) : NQK Kq (cancelIpc (Z := Unit) t) :=
  fun σ hσ y hy => nq_tail (nq_cancelIpc_post t σ hσ y hy)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_cancelIpc _)
macro_rules | `(tactic| nq_leaf) => `(tactic| (refine ik_nqhk_bind (nq_cancelIpc_post _) fun _ => ?_))

theorem nq_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : NQKE Kq m) : NQKE Kq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_capFaultOnFailure _ _ _ ?_)

theorem nq_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : NQK Kq (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capMove _ _ _)

theorem nq_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : NQK Kq (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capSwap _ _ _ _)

theorem nq_capSwapForDelete (slot1 slot2 : CslotPtr) : NQK Kq (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capSwapForDelete _ _)

theorem nq_captransferFromWords (ptr : Word) : NQK Kq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_captransferFromWords _)

theorem nq_getRefillHead (scPtr : ObjRef) : NQK Kq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getRefillHead _)

theorem nq_refillPopHead (scPtr : ObjRef) : NQK Kq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillPopHead _)

theorem nq_getRefills (scPtr : ObjRef) : NQK Kq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getRefills _)

theorem nq_refillSize (scPtr : ObjRef) : NQK Kq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillSize _)

theorem nq_refillSingle (scPtr : ObjRef) : NQK Kq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillSingle _)

theorem nq_getRefillTail (scPtr : ObjRef) : NQK Kq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getRefillTail _)

theorem nq_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : NQK Kq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillAddTail _ _)

theorem nq_refillFull (scPtr : ObjRef) : NQK Kq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillFull _)

theorem nq_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : NQK Kq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateRefillTl _ _)

theorem nq_scheduleUsed (scPtr : ObjRef) (new : Refill) : NQK Kq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_scheduleUsed _ _)

theorem nq_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NQK Kq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateRefillHd _ _)

theorem nq_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : NQK Kq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_chargeEntireHeadRefill _ _)

theorem nq_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : NQK Kq m) : NQK Kq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_checkCapAt _ _ _ ?_)

theorem nq_checkDomainTime  : NQK Kq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_checkDomainTime)

theorem nq_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : NQKE Kq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_checkHandlerEp _ _)

theorem nq_checkPrio (newPrio : Data) (authTcb : ObjRef) : NQKE Kq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_checkPrio _ _)

theorem nq_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : NQKE Kq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_checkValidIpcBuffer _ _)

theorem nq_nextDomain  : NQK Kq (nextDomain (Z := Unit)) := by
  unfold nextDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_nextDomain)

theorem nq_switchToThread (t : ObjRef) : NQK Kq (switchToThread (Z := Unit) t) := by
  unfold switchToThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_switchToThread _)

theorem nq_guardedSwitchTo (thread : ObjRef) : NQK Kq (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_guardedSwitchTo _)

theorem nq_switchToIdleThread  : NQK Kq (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_switchToIdleThread)

theorem nq_chooseThread  : NQK Kq (chooseThread (Z := Unit)) := by
  unfold chooseThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_chooseThread)

theorem nq_getScActive (scPtr : ObjRef) : NQK Kq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getScActive _)

theorem nq_isRoundRobin (scPtr : ObjRef) : NQK Kq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_isRoundRobin _)

theorem nq_handleOverrun (scPtr : ObjRef) (usage : Ticks) : NQK Kq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleOverrun _ _)

theorem nq_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : NQK Kq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_mergeNonoverlappingHeadRefill _)

theorem nq_headInsufficientLoop (scPtr : ObjRef) : NQK Kq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_headInsufficientLoop _)

theorem nq_refillBudgetCheck (usage : Ticks) : NQK Kq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillBudgetCheck _)

theorem nq_refillBudgetCheckRoundRobin (usage : Ticks) : NQK Kq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillBudgetCheckRoundRobin _)

theorem nq_commitTime  : NQK Kq (commitTime (Z := Unit)) := by
  unfold commitTime; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_commitTime)

theorem nq_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : NQK Kq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getScObjRef _ _)

theorem nq_testReschedule (fromTptr : ObjRef) : NQK Kq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_testReschedule _)

theorem nq_schedContextDonate (scPtr tcbPtr : ObjRef) : NQK Kq (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextDonate _ _)

theorem nq_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : NQK Kq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_orderedInsert _ _ _ _)

theorem nq_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : NQK Kq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_readyTimesAppend _ _)

theorem nq_tcbReleaseEnqueue (tcbPtr : ObjRef) : NQK Kq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbReleaseEnqueue _)

theorem nq_postpone (scPtr : ObjRef) : NQK Kq (postpone (Z := Unit) scPtr) := by
  unfold postpone; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_postpone _)

theorem nq_schedContextResume (scPtr : ObjRef) : NQK Kq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextResume _)

theorem nq_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NQK Kq (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_maybeDonateSc _ _)

theorem nq_mergeOverlappingRefills (scPtr : ObjRef) : NQK Kq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_mergeOverlappingRefills _)

theorem nq_refillHeadOverlappingLoop (scPtr : ObjRef) : NQK Kq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillHeadOverlappingLoop _)

theorem nq_refillUnblockCheck (scPtr : ObjRef) : NQK Kq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillUnblockCheck _)

theorem nq_completeSignal (ntfnptr tptr : ObjRef) : NQK Kq (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_completeSignal _ _)

theorem nq_schedContextCancelYieldTo (thread : ObjRef) : NQK Kq (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextCancelYieldTo _)

theorem nq_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : NQK Kq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupIpcBuffer _ _)

theorem nq_setMessageInfo (thread : ObjRef) (info : MessageInfo) : NQK Kq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setMessageInfo _ _)
end

end Fl4Proofs.P3.SInv
