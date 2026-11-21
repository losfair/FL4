/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4b): **the spec's `finish`
(`fl4Awaken; schedule; activateThread`) keeps the machine fields `MR` reads,
the interrupt table and the current time** (`MTK`, spec side only):
MachFieldFamT's family extended by the `setDeadline` leaf (a
`machineOpLift` of the opaque rest, so none of the four fields) and one lemma
per scheduler function (`mtk_auto`), and `mtk_fl4Awaken` (the timer firing
relation: zero or more `sendSignal`s). Top: `mtk_finish`. The same for the
receive and yield handlers (`mtk_handleRecvG`, `mtk_handleYieldG`) and
`mtk_withoutPreemption` (their syscall branches never fail).
-/
import Fl4Proofs.P3.MachFieldFamT
import Fl4Spec.Ext.Timer

open Classical

namespace Fl4Proofs.P3.MachT
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF

noncomputable section

theorem mkf_setDeadline (d : Word64) : MKF (setDeadline d) := mkf_machineOpLift _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_setDeadline _))

theorem mtk_tcbReleaseDequeueG  : MTK (tcbReleaseDequeue (Z := Unit) ) := by
  unfold tcbReleaseDequeue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbReleaseDequeueG )

theorem mtk_awakenG  : MTK (awaken (Z := Unit) ) := by
  unfold awaken; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_awakenG )

theorem mtk_checkDomainTimeG  : MTK (checkDomainTime (Z := Unit) ) := by
  unfold checkDomainTime; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_checkDomainTimeG )

theorem mtk_archPrepareNextDomainG  : MTK (archPrepareNextDomain (Z := Unit) ) := by
  unfold archPrepareNextDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPrepareNextDomainG )

theorem mtk_nextDomainG  : MTK (nextDomain (Z := Unit) ) := by
  unfold nextDomain; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_nextDomainG )

theorem mtk_archSwitchToIdleThreadG  : MTK (archSwitchToIdleThread (Z := Unit) ) := by
  unfold archSwitchToIdleThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archSwitchToIdleThreadG )

theorem mtk_switchToIdleThreadG  : MTK (switchToIdleThread (Z := Unit) ) := by
  unfold switchToIdleThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_switchToIdleThreadG )

theorem mtk_lazyFpuRestoreG (t : ObjRef) : MTK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lazyFpuRestoreG _)

theorem mtk_archSwitchToThreadG (t : ObjRef) : MTK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archSwitchToThreadG _)

theorem mtk_switchToThreadG (t : ObjRef) : MTK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_switchToThreadG _)

theorem mtk_guardedSwitchToG (thread : ObjRef) : MTK (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_guardedSwitchToG _)

theorem mtk_chooseThreadG  : MTK (chooseThread (Z := Unit) ) := by
  unfold chooseThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_chooseThreadG )

theorem mtk_scheduleChooseNewThreadG  : MTK (scheduleChooseNewThread (Z := Unit) ) := by
  unfold scheduleChooseNewThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_scheduleChooseNewThreadG )

theorem mtk_scheduleSwitchThreadFastfailG (ct it : ObjRef) (ctPrio targetPrio : Priority) : MTK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_scheduleSwitchThreadFastfailG _ _ _ _)

theorem mtk_switchSchedContextG  : MTK (switchSchedContext (Z := Unit) ) := by
  unfold switchSchedContext; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_switchSchedContextG )

theorem mtk_setNextInterruptG  : MTK (setNextInterrupt (Z := Unit) ) := by
  unfold setNextInterrupt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setNextInterruptG )

theorem mtk_scAndTimerG  : MTK (scAndTimer (Z := Unit) ) := by
  unfold scAndTimer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_scAndTimerG )

theorem mtk_scheduleG  : MTK (schedule (Z := Unit) ) := by
  unfold schedule; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_scheduleG )

theorem mtk_archActivateIdleThreadG (t : ObjRef) : MTK (archActivateIdleThread (Z := Unit) t) := by
  unfold archActivateIdleThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archActivateIdleThreadG _)

theorem mtk_activateThreadG  : MTK (activateThread (Z := Unit) ) := by
  unfold activateThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_activateThreadG )

/-! The receive and yield handlers. -/

theorem mtk_tcbNtfnAppendG (tptr ntfnPtr : ObjRef) : MTK (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbNtfnAppendG _ _)

theorem mtk_getCapRegG (reg : Register) : MTK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getCapRegG _)

theorem mtk_handleNoFaultG (tptr : ObjRef) : MTK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleNoFaultG _)

theorem mtk_refillResetRrG (cscPtr : ObjRef) : MTK (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillResetRrG _)

theorem mtk_endTimesliceG (canTimeout : Bool) : MTK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_endTimesliceG _)

theorem mtk_doNbrecvFailedTransferG (thread : ObjRef) : MTK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doNbrecvFailedTransferG _)

theorem mtk_maybeReturnScG (ntfnPtr tcbPtr : ObjRef) : MTK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_maybeReturnScG _ _)

theorem mtk_completeSignalG (ntfnptr tptr : ObjRef) : MTK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_completeSignalG _ _)

theorem mtk_receiveIpcBlockedG (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : MTK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_receiveIpcBlockedG _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem mtk_receiveIpcG (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) : MTK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_receiveIpcG _ _ _ _)

theorem mtk_receiveSignalBlockedG (thread ntfnptr : ObjRef) (isBlocking : Bool) : MTK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_receiveSignalBlockedG _ _ _)

theorem mtk_receiveSignalG (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : MTK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_receiveSignalG _ _ _)

theorem mtk_lookupReplyG  : MTKE (lookupReply (Z := Unit) ) := by
  unfold lookupReply; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupReplyG )

theorem mtk_handleFaultG (thread : ObjRef) (ex : Fault) : MTK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleFaultG _ _)

set_option maxHeartbeats 2000000 in
theorem mtk_handleRecvG (isBlocking canReply : Bool) : MTK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleRecvG _ _)

theorem mtk_chargeBudgetG (consumed : Ticks) (canTimeout : Bool) : MTK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_chargeBudgetG _ _)

theorem mtk_handleYieldG  : MTK (handleYield (Z := Unit) ) := by
  unfold handleYield; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleYieldG )

/-- **A `withoutPreemption` of an `MTK` step**: every outcome is ok and keeps `msFT`. -/
theorem mtk_withoutPreemption {m : SMonad Unit Unit} (h : MTK m) {σ : State Unit} :
    ∀ y ∈ ((withoutPreemption (Z := Unit) m).run σ).1, msFT y.2 = msFT σ ∧ y.1 = .ok () := by
  intro y hy
  unfold withoutPreemption NonDetE.liftE at hy
  rw [ExceptT.run_lift] at hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨h σ x hx, rfl⟩

theorem mtk_fl4AwakenG : MTK (fl4Awaken (Z := Unit)) := by
  intro σ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact (mtk_sendSignal' n bd _ ((), σ1) (by rw [hs]; exact Set.mem_singleton _)).trans ih

/-- **The spec's `finish` keeps `msFT`.** -/
theorem mtk_finish {σ σ' : State Unit}
    (h : ((), σ') ∈ ((fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) σ).1) :
    msFT σ' = msFT σ := by
  obtain ⟨⟨u1, σ1⟩, h1, h2⟩ := h
  obtain ⟨⟨u2, σ2⟩, h3, h4⟩ := h2
  exact ((mtk_activateThreadG σ2 _ h4).trans (mtk_scheduleG σ1 _ h3)).trans (mtk_fl4AwakenG σ _ h1)

end

end Fl4Proofs.P3.MachT
