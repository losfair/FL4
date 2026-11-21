/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch5 (A)): **FL4's TCB timers
keep the spec's FPU owner valid**. `OK := FK owF` (VsDom's generic `FK`):
every outcome keeps `x64_current_fpu_owner` and `domain_index`. The leaves are SpecGlobFK's
`GK` lemmas for the projection `owF`, proved the same way (VsDom's
combinators are generic in the projection), for the cone of the spec's
`send_signal` (cancel_ipc, set_thread_state, maybe_donate_sc,
possible_switch_to, the refill checks): `owk_sendSignal`, then
`owF_fires` (`Fires` keeps both; with AllDom's `dk_sendSignal'` also the
domain list and start: `fires_dom`).

`FpuOwnOK` [J] (ScArchF, l4v X64 `valid_cur_fpu`) after `Fires` then
follows from `FpuOwnOK` at the entry state and the J relation at both
ends: the owner is a spec TCB at entry, hence one of the related TCBs
(`JAtZ.obj.tcb`, ObjCover), and every related TCB is a spec TCB after the
timers (`NtfnStateRel.tcb`): `fpuOwnOK_fires` (XTopJointSchedRF2). So no
"TCBs not deleted" spec framework is needed.
-/
import Fl4Proofs.P3.SpecGlobFK
import Fl4Proofs.P3.ScAwaken
import Fl4Proofs.P3.AllDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-- The FPU owner (l4v X64 `x64_current_fpu_owner`) and the domain index
(`domain_index`, for ScNextDomB's `NdOK` after the timers). -/
def owF (σ : State Unit) : Option ObjRef × Nat := (σ.archState.x64CurrentFpuOwner, σ.domainIndex)

/-- Every outcome of `m` keeps the FPU owner and the domain index. -/
abbrev OWK {α : Type} (m : NonDet (State Unit) α) : Prop := FK owF m

/-- An `OWK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "owk_leaf" : tactic
macro_rules | `(tactic| owk_leaf) => `(tactic| fail "no owk_leaf")

macro "owk_auto" : tactic => `(tactic| repeat' (first | owk_leaf | dk_step0))

theorem owk_doMachineOp {α : Type} (mop : NonDet MachineState α) : OWK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_doMachineOp _)

theorem owk_doExtendedOp (eop : DetExtMonad Unit) : OWK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_doExtendedOp _)


theorem owk_setObject (p : ObjRef) (o : KernelObject) : OWK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setObject _ _)

theorem owk_setCap (c : Cap) (sl : CslotPtr) : OWK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setCap _ _)

theorem owk_getCap (sl : CslotPtr) : OWK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getCap _)


theorem owk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : OWK (threadSet (Z := Unit) f t) := by
  unfold threadSet; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_threadSet' _ _)

theorem owk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : OWK (threadGet (Z := Unit) f t) := by
  unfold threadGet; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_threadGet' _ _)

theorem owk_setThreadState' (t : ObjRef) (ts : ThreadState) : OWK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setThreadState' _ _)

theorem owk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    OWK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getSimpleKo' _ _)

theorem owk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    OWK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setSimpleKo' _ _ _)

theorem owk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    OWK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_updateSkObjRef' _ _ _ _)

theorem owk_getSchedContext' (q : ObjRef) : OWK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getSchedContext' _)

theorem owk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    OWK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_updateSchedContext' _ _)

theorem owk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : OWK (asUser (Z := Unit) t u) := by
  unfold asUser; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_asUser' _ _)

theorem owk_replyUnlinkTcb' (t r : ObjRef) : OWK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_replyUnlinkTcb' _ _)

theorem owk_getThreadState' (t : ObjRef) : OWK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getThreadState' _)

theorem owk_cancelIpc' (t : ObjRef) : OWK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_cancelIpc' _)

theorem owk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : OWK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getSkObjRef' _ _ _)

theorem owk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : OWK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getScObjRef' _ _)


theorem owk_getTcbQueue' (d : Domain) (p : Priority) : OWK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getTcbQueue' _ _)

theorem owk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : OWK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setTcbQueue' _ _ _)

theorem owk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : OWK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbSchedAction' _ _)

theorem owk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : OWK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getTcbObjRef' _ _)

theorem owk_setSchedulerAction' (a : SchedulerAction) : OWK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_setSchedulerAction' _)

theorem owk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : OWK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getScRefillSufficient' _ _)

theorem owk_getScRefillReady' (sc : ObjRef) : OWK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getScRefillReady' _)

theorem owk_tcbReleaseRemove' (t : ObjRef) : OWK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbReleaseRemove' _)

theorem owk_rescheduleRequired' : OWK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_rescheduleRequired' )

theorem owk_testReschedule' (t : ObjRef) : OWK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_testReschedule' _)

theorem owk_possibleSwitchTo' (t : ObjRef) : OWK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_possibleSwitchTo' _)

theorem owk_tcbEpDequeue' (t e : ObjRef) : OWK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbEpDequeue' _ _)

theorem owk_tcbNtfnDequeue' (t n : ObjRef) : OWK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbNtfnDequeue' _ _)

theorem owk_isRoundRobin' (sc : ObjRef) : OWK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_isRoundRobin' _)

theorem owk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : OWK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_updateRefillHd' _ _)

theorem owk_getRefillHead' (sc : ObjRef) : OWK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_getRefillHead' _)

theorem owk_refillPopHead' (sc : ObjRef) : OWK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_refillPopHead' _)

theorem owk_mergeOverlappingRefills' (sc : ObjRef) : OWK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_mergeOverlappingRefills' _)

theorem owk_refillHeadOverlappingLoop' (sc : ObjRef) : OWK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_refillHeadOverlappingLoop' _)

theorem owk_refillUnblockCheck' (sc : ObjRef) : OWK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_refillUnblockCheck' _)

theorem owk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : OWK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_ifCondRefillUnblockCheck' _ _ _)

theorem owk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : OWK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem owk_restartThreadIfNoFault' (t : ObjRef) : OWK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_restartThreadIfNoFault' _)

theorem owk_removeAndRestartEpQueuedThread' (t e : ObjRef) : OWK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_removeAndRestartEpQueuedThread' _ _)

theorem owk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : OWK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_removeAndRestartNtfnQueuedThread' _ _)

theorem owk_replyUnlinkSc' (sc r : ObjRef) : OWK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_replyUnlinkSc' _ _)

theorem owk_schedContextDonate' (sc t : ObjRef) : OWK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_schedContextDonate' _ _)

theorem owk_schedContextUpdateConsumed' (sc : ObjRef) : OWK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_schedContextUpdateConsumed' _)

theorem owk_schedContextCancelYieldTo' (t : ObjRef) : OWK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_schedContextCancelYieldTo' _)


theorem owk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : OWK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_orderedInsert' _ _ _ _)

theorem owk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : OWK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_readyTimesAppend' _ _)

theorem owk_tcbReleaseEnqueue' (t : ObjRef) : OWK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbReleaseEnqueue' _)

theorem owk_tcbAppend' (t : ObjRef) (q : List ObjRef) : OWK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_tcbAppend' _ _)

theorem owk_postpone' (sc : ObjRef) : OWK (postpone (Z := Unit) sc) := by
  unfold postpone; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_postpone' _)

theorem owk_schedContextResume' (sc : ObjRef) : OWK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_schedContextResume' _)


theorem owk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : OWK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_maybeDonateSc' _ _)

theorem owk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) :
    OWK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem owk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) :
    OWK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; owk_auto
macro_rules | `(tactic| owk_leaf) => `(tactic| with_reducible exact owk_updateWaitingNtfn' _ _ _)

/-- **`send_signal` keeps the FPU owner.** -/
theorem owk_sendSignal (n : ObjRef) (b : Badge) : OWK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; owk_auto

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3.Sched
open Fl4Spec

/-- **FL4's TCB timers keep the spec's FPU owner and domain index**
(`Fires`: notification signals, `owk_sendSignal`, and `reprogram_timer`
writes). -/
theorem owF_firesP {σ σ1 : State Unit} (h : Fires σ σ1) : Vs.owF σ1 = Vs.owF σ := by
  induction h with
  | refl => rfl
  | tail _ hf ih =>
    obtain ⟨σa, ho, rfl⟩ := hf
    rcases ho with rfl | ⟨n, b, he⟩
    · exact ih
    · have := Vs.owk_sendSignal n b _ ((), σa) (by rw [he]; exact Set.mem_singleton _)
      exact this.trans ih

theorem owF_fires {σ σ1 : State Unit} (h : Fires σ σ1) :
    σ1.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner :=
  congrArg Prod.fst (owF_firesP h)

/-- **FL4's TCB timers keep the domain schedule** (`domain_list`,
`domain_index`, `domain_start_index`; AllDom's `dk_sendSignal'`). -/
theorem fires_dom {σ σ1 : State Unit} (h : Fires σ σ1) :
    σ1.domainList = σ.domainList ∧ σ1.domainIndex = σ.domainIndex ∧ σ1.domainStartIndex = σ.domainStartIndex := by
  refine ⟨?_, congrArg Prod.snd (owF_firesP h), ?_⟩ <;>
  · induction h with
    | refl => rfl
    | tail _ hf ih =>
      obtain ⟨σa, ho, rfl⟩ := hf
      rcases ho with rfl | ⟨n, b, he⟩
      · exact ih
      · have := (Vs.dk_sendSignal' n b).dom (σ := _) (x := ((), σa)) (by rw [he]; exact Set.mem_singleton _)
        first | exact this.1.trans ih | exact this.2.trans ih

end Fl4Proofs.P3.Sched
