/- nq1: the NtfnQB family `NQK K` for the wake-ups, the IPC paths, the fault/timeout paths and the deletion path (generated: proofs/scratch/nq2/mknq2.sh, `nq2_auto` = `nq_auto` + the state-read rule `nq_rds`; a thread whose state is written is read in a state other than BlockedOnNotification, dequeued, or given in `K`). -/
import Fl4Proofs.P3.SpecInvNtfnQH1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_activateThread  : NQK Kq (activateThread (Z := Unit)) := by
  unfold activateThread; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_activateThread)

theorem nq_restartThreadIfNoFault (t : ObjRef) (hk_t : t ∈ Kq) : NQK Kq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_restartThreadIfNoFault _ ?_) <;> nq_mem))

theorem nq_removeAndRestartEpQueuedThread (t epptr : ObjRef) : NQK Kq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_removeAndRestartEpQueuedThread _ _)

theorem nq_cancelAllIpc (epptr : ObjRef) : NQK Kq (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_cancelAllIpc _)

theorem nq_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : NQK Kq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_removeAndRestartNtfnQueuedThread _ _)

theorem nq_cancelAllSignals (ntfnptr : ObjRef) : NQK Kq (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_cancelAllSignals _)

theorem nq_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : NQK Kq (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_removeAndRestartBadgedThread _ _ _)

theorem nq_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : NQK Kq (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_cancelBadgedSends _ _)

theorem nq_fastFinalise (a0 : Cap) (a1 : Bool) : NQK Kq (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fastFinalise _ _)

theorem nq_capDeleteOne (slot : CslotPtr) : NQK Kq (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capDeleteOne _)

theorem nq_deletingIrqHandler (irq : Irq) : NQK Kq (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_deletingIrqHandler _)

theorem nq_finaliseCap (a0 : Cap) (a1 : Bool) : NQK Kq (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_finaliseCap _ _)

/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem nq_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, NQK Kq (f k)) (k : RecDelCall) : NQKE Kq (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, NQKE Kq (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; nq_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; nq_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> nq_auto
    all_goals exact hrec' _

theorem nq_recDel (c : RecDelCall) : NQKE Kq (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => nq_recDelF hf k) c
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_recDel _)

theorem nq_capDelete (slot : CslotPtr) : NQKE Kq (capDelete (Z := Unit) slot) := by
  unfold capDelete; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capDelete _)

/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem nq_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, NQK Kq (f k)) (sl : CslotPtr) : NQKE Kq (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, NQKE Kq (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  nq_auto
  all_goals exact hrec' _

theorem nq_capRevoke (sl : CslotPtr) : NQKE Kq (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => nq_capRevokeF hf k) sl
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capRevoke _)

theorem nq_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) (hk_caller : caller ∈ Kq) : NQK Kq (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_replyPush _ _ _ _ ?_) <;> nq_mem))

theorem nq_restart (thread : ObjRef) : NQK Kq (restart (Z := Unit) thread) := by
  unfold restart; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_restart _)

theorem nq_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NQK Kq (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateWaitingNtfn _ _ _)

theorem nq_sendSignal (ntfnptr : ObjRef) (badge : Badge) : NQK Kq (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_sendSignal _ _)

theorem nq_fl4Awaken : NQK Kq (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact nq_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4Awaken)

theorem nq_handleInterrupt (irq : Irq) : NQK Kq (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleInterrupt _)

theorem nq_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NQKE Kq (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_installTcbCap _ _ _ _)

theorem nq_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NQKE Kq (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_installTcbFrameCap _ _ _)

theorem nq_invokeCnode (i : CnodeInvocation) : NQKE Kq (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeCnode _)

theorem nq_invokeIrqHandler (a0 : IrqHandlerInvocation) : NQK Kq (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeIrqHandler _)

theorem nq_maybeHandleInterrupt (inKernel : Bool) : NQK Kq (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; nq2_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_maybeHandleInterrupt _)
end

end Fl4Proofs.P3.SInv
