/-
P3 (DESIGN.md §9), invariant line G1 (rd14e, KENTRY-PLAN rd14d handoff 1):
**IRQ handler set / clear** (spec side only).

`cap_delete_one` finalises through `fast_finalise`, which FAILS on every cap but
a null, reply, endpoint or notification cap: no outcome finalises a TCB or an
SC, so no fact about the IRQ slot's contents is needed (rd14c's obstacle (b)
does not arise; `ArmAKB`'s interface suffices).

* `tb_cancelAllIpc`, `tb_cancelAllSignals`, `tb_ffNtfn` (rd14c's `tb_ik`
  over rd8a's `CP` and rd14b's `BL`, the walks of rd14d's cancelBadgedSends).
* **`ec_ffReply`** (a reply cap: `reply_remove` of a `BlockedOnReply` thread —
  not ct, ct is in Restart — may hand cur_sc back: rd14e's `et_replyRemove`;
  otherwise `cancel_ipc`), **`ec_fastFinalise`**, **`ec_capDeleteOne`** (from
  `TB σ0` with ct not `BlockedOnReply`: `EC σ0` at every outcome).
* **`perfA_irqHandler`** (every IRQ handler invocation), `CovI`,
  **`armA_covI`**, **`C14e2 := C14e1 ∨ CovI`**, **`armAKB_c14e2`**.
-/
import Fl4Proofs.P3.SpecInvRd14eA
open Classical

namespace Fl4Proofs.P3.SInvR.A14e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The endpoint / notification finalisers -/

theorem tb_cancelAllIpc (σ0 : State Unit) (e : ObjRef) : IK (TB σ0) (cancelAllIpc (Z := Unit) e) :=
  tb_ik (cfk_cancelAllIpc' e)
    (by unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault; repeat' (first | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _) | (with_reducible exact A8.ik_cp (sv_tcbNtfnDequeue _ _) (cfk_tcbNtfnDequeue' _ _) _ _) | cp_auto))
    (by unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault; repeat' (first | (with_reducible exact bl_of_svm (SVK.sv_replyUnlinkTcb _ _)) | (with_reducible exact bl_of_svm (sv_tcbNtfnDequeue _ _)) | bl14d_auto))

theorem tb_cancelAllSignals (σ0 : State Unit) (n : ObjRef) : IK (TB σ0) (cancelAllSignals (Z := Unit) n) :=
  tb_ik (cfk_cancelAllSignals' n)
    (by unfold cancelAllSignals removeAndRestartNtfnQueuedThread; repeat' (first | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _) | (with_reducible exact A8.ik_cp (sv_tcbNtfnDequeue _ _) (cfk_tcbNtfnDequeue' _ _) _ _) | cp_auto))
    (by unfold cancelAllSignals removeAndRestartNtfnQueuedThread; repeat' (first | (with_reducible exact bl_of_svm (SVK.sv_replyUnlinkTcb _ _)) | (with_reducible exact bl_of_svm (sv_tcbNtfnDequeue _ _)) | bl14d_auto))

theorem tb_ffNtfn (σ0 : State Unit) (n : ObjRef) : IK (TB σ0) (do
      schedContextMaybeUnbindNtfn (Z := Unit) n
      unbindMaybeNotification (Z := Unit) n
      cancelAllSignals (Z := Unit) n) :=
  ik_bind (tb_svm (by unfold schedContextMaybeUnbindNtfn; sv_auto) (cfk_schedContextMaybeUnbindNtfn' n)) fun _ =>
    ik_bind (tb_svm (by unfold unbindMaybeNotification; sv_auto) (cfk_unbindMaybeNotification' n)) fun _ =>
      tb_cancelAllSignals σ0 n

/-! ## The reply finaliser -/

theorem cp_ffReply (r : ObjRef) (rt : CapRights) (fin : Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (A8.CP σ0 c) (fastFinalise (Z := Unit) (.replyCap r rt) fin) := by
  simp only [fastFinalise]
  unfold replyRemove
  repeat' (first
    | (with_reducible exact A8.ik_cp (B8e.sv_cancelIpc' _) (cfk_cancelIpc' _) _ _)
    | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _)
    | (with_reducible exact A8.cp_schedContextDonate _ _ _ _)
    | ik_step0
    | cp_leaf
    | split)

/-- **The reply cap's fast finaliser from `EC σ0`** (ct not `BlockedOnReply`). -/
theorem ec_ffReply {σ0 s : State Unit} (r : ObjRef) (rt : CapRights) (fin : Bool) (h : EC σ0 s)
    (hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (fastFinalise (Z := Unit) (.replyCap r rt) fin s).1, EC σ0 y.2 := by
  intro y hy
  have et : s.curThread = σ0.curThread := cf_curThread h.1
  obtain ⟨-, hw⟩ := cp_ffReply r rt fin σ0 σ0.curSc s ⟨cf_curSc h.1, h.2.1⟩ y hy
  refine ⟨(cfk_fastFinalise' _ _ s y hy).trans h.1, hw, ?_⟩
  have hσ : ET σ0.curThread σ0.curSc s := ⟨et, h.2.2⟩
  suffices H : ET σ0.curThread σ0.curSc y.2 from H.2
  simp only [fastFinalise] at hy
  unfold NonDet.when at hy
  split at hy
  swap
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ
  obtain ⟨⟨ro, σ1⟩, h1, hy⟩ := hy
  have e1 : σ1 = s := cq5_ro (fun _ => by
    show IK _ (NonDet.liftM Reply.replyTcb (getSimpleKo (Z := Unit) KernelObject.reply r))
    unfold getSimpleKo; repeat' (first | ik_step0 | ik_unfold)) h1
  subst e1
  cases ro with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact hσ
  | some tp =>
    dsimp only at hy
    obtain ⟨w, hw, hy⟩ := hy
    unfold getThreadState at hw
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
    dsimp only at hy
    revert hy
    generalize hxs : x.tcbState = st
    cases st <;> intro hy
    case blockedOnReply r' =>
      have hne : tp ≠ σ0.curThread := by
        intro e; subst e
        exact hst x hx r' hxs
      exact et_replyRemove _ _ tp r' hne σ1 hσ y hy
    all_goals exact et_svcf (B8e.sv_cancelIpc' tp) (cfk_cancelIpc' tp) σ1 hσ y hy

/-- **`fast_finalise` from `TB σ0`** (ct not `BlockedOnReply`): `EC σ0`. -/
theorem ec_fastFinalise {σ0 s : State Unit} (cap : Cap) (fin : Bool) (h : TB σ0 s)
    (hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (fastFinalise (Z := Unit) cap fin s).1, EC σ0 y.2 := by
  intro y hy
  cases cap
  case nullCap =>
    simp only [fastFinalise] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact ec_of_tb h
  case replyCap r rt => exact ec_ffReply r rt fin (ec_of_tb h) hst y hy
  case endpointCap r b rt =>
    simp only [fastFinalise] at hy
    exact ec_of_tb ((ik_when _ (tb_cancelAllIpc σ0 r)) s h y hy)
  case notificationCap r b rt =>
    simp only [fastFinalise] at hy
    exact ec_of_tb ((ik_when _ (tb_ffNtfn σ0 r)) s h y hy)
  all_goals (simp only [fastFinalise] at hy; exact ec_of_tb (ik_fail s h y hy))

theorem sv_emptySlotNull (sl : CslotPtr) : SVK.SVM (emptySlot (Z := Unit) sl .nullCap) := by
  simp only [emptySlot, postCapDeletion, setCdt]; sv_auto

/-- **`cap_delete_one` from `TB σ0`** (ct not `BlockedOnReply`): `EC σ0`. -/
theorem ec_capDeleteOne {σ0 s : State Unit} (sl : CslotPtr) (h : TB σ0 s)
    (hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r) :
    ∀ y ∈ (capDeleteOne (Z := Unit) sl s).1, EC σ0 y.2 := by
  intro y hy
  unfold capDeleteOne at hy
  obtain ⟨⟨cap, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := cq5_ro (fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)) h1
  subst e1
  dsimp only [NonDet.unless] at hy
  split at hy
  · rw [Set.mem_singleton_iff.1 hy]; exact ec_of_tb h
  · obtain ⟨⟨fin, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = s1 := cq5_ro (fun _ => by unfold isFinalCap; repeat' (first | ik_step0 | ik_unfold)) h2
    subst e2
    obtain ⟨w, hw, hy⟩ := hy
    exact ec_svcf (sv_emptySlotNull sl) (cfk_emptySlotNull sl) w.2 (ec_fastFinalise cap fin h hst w hw) y hy

/-! ## The arm -/

/-- **Every IRQ handler invocation** from the Restart state ends in `EC σ0`. -/
theorem ec_invokeIrqHandler {σ0 s : State Unit} (i : IrqHandlerInvocation) (h : RF σ0 s) :
    ∀ x ∈ (invokeIrqHandler (Z := Unit) i s).1, EC σ0 x.2 := by
  have hst : ∀ x, s.kheap σ0.curThread = some (.tcb x) → ∀ r, x.tcbState ≠ .blockedOnReply r := by
    intro x hx r e; rw [h.rs x hx] at e; cases e
  intro x hx
  cases i with
  | aCKIrq irq =>
    exact ec_of_tb ((tb_svm (by simp only [invokeIrqHandler, archInvokeIrqHandler]; sv_auto)
        (by simp only [invokeIrqHandler, archInvokeIrqHandler]; cfk_auto) :
      IK (TB σ0) (invokeIrqHandler (Z := Unit) (.aCKIrq irq))) s h.tb x hx)
  | setIRQHandler irq cap slot =>
    unfold invokeIrqHandler at hx
    obtain ⟨⟨sl, s1⟩, h1, hx⟩ := hx
    have e1 : s1 = s := cq5_ro (fun _ => by unfold getIrqSlot; repeat' (first | ik_step0 | ik_unfold)) h1
    subst e1
    obtain ⟨w, hw, hx⟩ := hx
    exact ec_svcf (by sv_auto) (by cfk_auto) w.2 (ec_capDeleteOne sl h.tb hst w hw) x hx
  | clearIRQHandler irq =>
    unfold invokeIrqHandler at hx
    obtain ⟨⟨sl, s1⟩, h1, hx⟩ := hx
    have e1 : s1 = s := cq5_ro (fun _ => by unfold getIrqSlot; repeat' (first | ik_step0 | ik_unfold)) h1
    subst e1
    exact ec_capDeleteOne sl h.tb hst x hx

theorem perfA_irqHandler {σ0 s : State Unit} (bl call don : Bool) (i : IrqHandlerInvocation) (h : RF σ0 s) :
    PerfA σ0 bl call don (.invokeIRQHandler i) s := by
  have hI := ec_invokeIrqHandler i h
  refine perfA_tbn3 h.bs h.suff fun y hy => ?_
  change y ∈ ((NonDetE.liftE (invokeIrqHandler (Z := Unit) i) >>= fun _ => NonDetE.returnOk []).run s).1 at hy
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
    rw [SInvU.mem_ret_ok hy]
    exact ⟨fun _ _ => tbu_of_ec (hI x hx), fun e he => by cases he⟩
  · obtain ⟨x, -, rfl⟩ := ft_mem_liftE hz
    cases he

def CovI : Fl4Invocation → Prop
  | .invokeIRQHandler _ => True
  | _ => False

theorem armA_covI : ArmA CovI := by
  intro σ0 u bl cl dn b hc h
  cases b
  case invokeIRQHandler i => exact perfA_irqHandler bl cl dn i h
  all_goals exact (hc : False).elim

/-- rd14e's covered set so far: rd14d's, the Reply arm, the IRQ handler arms. -/
def C14e2 (b : Fl4Invocation) : Prop := C14e1 b ∨ CovI b

theorem armAKB_c14e2 : ArmAKB C14e2 := armAKB_c14e1.or (armAKB_of (armAK_of armA_covI))

end

end Fl4Proofs.P3.SInvR.A14e
