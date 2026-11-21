/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3):
**`finalise_cap` keeps `DWS σ0`** for every cap kind (spec side only).

* `DSt m` (rd14d's `EC σ1` for every `σ1` and rd14e's `EBN t` for every `t`)
  with its combinators; `DSt.dws` (rd14f C's `dws_of`).
* Walks: a `QN` walk (`qn14f_auto`: no TCB is bound by the cone's writers
  but reply_remove's donation to the caller), `dst_cancelAllIpc`,
  `dst_cancelAllSignals`, `dst_ffNtfn`, `et_unbindTcb` / `et_unbindFromSc`
  (rd14d's `eb_schedContextUnbindTcb` with the current thread pinned),
  `dst_unbindFromSc`, `sv14f_archFinaliseCap` (with rd13b's VSpace leaves).
* The reply arm: `ebn_replyRemove` (the caller ≠ ct: rd14e's `ebn_donate`),
  `ebn_ffReply`, **`dws_ffReply`** (ct not `BlockedOnReply`: ctq14's `CKN`).
* The SC arm: **`ebn_unbindAll_cur`** (finalising cur_sc: if ct is bound to
  it, sb2's `ScBack` makes ct its TCB, so `unbind_all_tcbs` — cur_sc is not
  the idle SC — reschedules and unbinds ct; otherwise ct is already unbound
  with no resume, by `CKN` and `EB`), `mx0_setInactive` (cur_sc's refill max
  0), `ebn_setInactive`, `ec_setInactive_ne` (an SC other than cur_sc).
* **`dws_fastFinalise`**, **`dws_capDeleteOne`**, **`dws_finaliseCap`** (from
  `DWS σ0`, `CKN`, `ScInv`, ctq's `CB`, ct ≠ idle).
-/
import Fl4Proofs.P3.SpecInvRd14fC
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Steps with both families -/

/-- rd14d's `EC σ1` for every `σ1`, rd14e's `EBN t` for every `t`. -/
structure DSt {α : Type} (m : NonDet (State Unit) α) : Prop where
  ec : ∀ σ1, IK (A14d.EC σ1) m
  en : ∀ t, IK (A14e.EBN t) m

theorem DSt.dws {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h : DSt m) : IK (DWS σ0) m :=
  dws_of h.ec h.en

theorem dst_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : DSt m)
    (hf : ∀ a, DSt (f a)) : DSt (m >>= f) :=
  ⟨fun σ1 => ik_bind (hm.ec σ1) fun a => (hf a).ec σ1, fun t => ik_bind (hm.en t) fun a => (hf a).en t⟩

theorem dst_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : DSt m) : DSt (NonDet.when P m) :=
  ⟨fun σ1 => ik_when _ (h.ec σ1), fun t => ik_when _ (h.en t)⟩

theorem dst_pure {α : Type} (a : α) : DSt (pure a : NonDet (State Unit) α) :=
  ⟨fun _ => ik_pure _, fun _ => ik_pure _⟩

theorem dst_npure {α : Type} (a : α) : DSt (NonDet.pure a : NonDet (State Unit) α) :=
  ⟨fun _ s hs y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hs,
    fun _ s hs y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hs⟩

theorem dst_liftM {α β : Type} (f : α → β) {m : NonDet (State Unit) α} (h : DSt m) : DSt (NonDet.liftM f m) := by
  unfold NonDet.liftM; exact dst_bind h fun _ => dst_npure _

theorem dst_svcf {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) : DSt m :=
  ⟨fun _ => A14d.ec_svcf h1 h2, fun _ => A14e.ebn_svm h1⟩

theorem dst_gen {α : Type} {m : NonDet (State Unit) α} (hf : CFK m) (hp : ∀ σ1 c, IK (A8.CP σ1 c) m)
    (hb : ∀ t c, IK (BL t c) m) (hq : ∀ t, IK (TP (QN t)) m) : DSt m :=
  ⟨fun σ1 => A14d.ec_ik hf (hp σ1 σ1.curSc) fun s _ h => ik_eb (hb _ _) (hq _) (nres_of_cp hp) s h,
    fun _ => ebn_of hp (hq _)⟩

/-! ## Walks -/

/-- The `QN` walk (no TCB bound). -/
macro "qn14f_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact qn_possibleSwitchTo _ _)
  | (with_reducible exact qn_rescheduleRequired _)
  | (exact ik_of_nks (fun _ _ hk h' => tp_sok hk h') (nks_ifCondG _ _ _))
  | (with_reducible exact qn_of_svm (SVK.sv_replyUnlinkTcb _ _) _)
  | (with_reducible exact qn_of_svm (sv_tcbNtfnDequeue _ _) _)
  | (with_reducible exact qn_of_svm (B8.sv_completeYieldTo' _) _)
  | ((with_reducible refine tp_threadSet _ _ ?_); intro _ _ _; rfl)
  | ((with_reducible refine tp_setObject _ _ ?_); intro _ h; cases h; done)
  | (refine qn_of_svm ?_ _; sv_auto; done)
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when)
  | ik_step0
  | ik_unfold))

theorem dst_cancelAllIpc (e : ObjRef) : DSt (cancelAllIpc (Z := Unit) e) :=
  dst_gen (cfk_cancelAllIpc' e)
    (fun σ1 c => by
      unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault
      repeat' (first | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _) | (with_reducible exact A8.ik_cp (sv_tcbNtfnDequeue _ _) (cfk_tcbNtfnDequeue' _ _) _ _) | cp_auto))
    (fun t c => by
      unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault
      repeat' (first | (with_reducible exact bl_of_svm (SVK.sv_replyUnlinkTcb _ _)) | (with_reducible exact bl_of_svm (sv_tcbNtfnDequeue _ _)) | bl14d_auto))
    (fun t => by unfold cancelAllIpc removeAndRestartEpQueuedThread restartThreadIfNoFault; qn14f_auto)

theorem dst_cancelAllSignals (n : ObjRef) : DSt (cancelAllSignals (Z := Unit) n) :=
  dst_gen (cfk_cancelAllSignals' n)
    (fun σ1 c => by
      unfold cancelAllSignals removeAndRestartNtfnQueuedThread
      repeat' (first | (with_reducible exact A11b.cp_replyUnlinkTcb _ _ _ _) | (with_reducible exact A8.ik_cp (sv_tcbNtfnDequeue _ _) (cfk_tcbNtfnDequeue' _ _) _ _) | cp_auto))
    (fun t c => by
      unfold cancelAllSignals removeAndRestartNtfnQueuedThread
      repeat' (first | (with_reducible exact bl_of_svm (SVK.sv_replyUnlinkTcb _ _)) | (with_reducible exact bl_of_svm (sv_tcbNtfnDequeue _ _)) | bl14d_auto))
    (fun t => by unfold cancelAllSignals removeAndRestartNtfnQueuedThread; qn14f_auto)

theorem dst_ffNtfn (n : ObjRef) : DSt (do
      schedContextMaybeUnbindNtfn (Z := Unit) n
      unbindMaybeNotification (Z := Unit) n
      cancelAllSignals (Z := Unit) n) :=
  dst_bind (dst_svcf (by unfold schedContextMaybeUnbindNtfn; sv_auto) (cfk_schedContextMaybeUnbindNtfn' n)) fun _ =>
    dst_bind (dst_svcf (by unfold unbindMaybeNotification; sv_auto) (cfk_unbindMaybeNotification' n)) fun _ =>
      dst_cancelAllSignals n

/-- `sched_context_unbind_tcb` with the current thread pinned (rd14d). -/
theorem et_unbindTcb (t c p : ObjRef) : IK (A14e.ET t c) (schedContextUnbindTcb (Z := Unit) p) :=
  fun s hs y hy => ⟨(cf_curThread (cfk_schedContextUnbindTcb' p s y hy)).trans hs.1,
    eb_schedContextUnbindTcb t c p s hs.1 hs.2 y hy⟩

theorem et_unbindFromSc (t c r : ObjRef) : IK (A14e.ET t c) (unbindFromSc (Z := Unit) r) := by
  unfold unbindFromSc
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun o => ik_bind (ik_maybeM (fun p => et_unbindTcb t c p) o)
    fun _ => ik_maybeM (fun p => ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun sc =>
      ik_maybeM (fun q => A14e.et_svcf (B8.sv_completeYieldTo' q) (cfk_completeYieldTo' q)) _) o

theorem dst_unbindFromSc (r : ObjRef) : DSt (unbindFromSc (Z := Unit) r) := by
  have hp : ∀ σ1 c, IK (A8.CP σ1 c) (unbindFromSc (Z := Unit) r) := fun σ1 c => by
    unfold unbindFromSc schedContextUnbindTcb
    repeat' (first | (with_reducible exact A8.ik_cp (B8.sv_completeYieldTo' _) (cfk_completeYieldTo' _) _ _) | cp_auto)
  exact ⟨fun σ1 => A14d.ec_ik (cfk_unbindFromSc' r) (hp σ1 σ1.curSc) fun s hct h y hy =>
      (et_unbindFromSc _ _ r s ⟨hct, h⟩ y hy).2,
    fun t => ebn_of hp (by unfold unbindFromSc schedContextUnbindTcb; qn14f_auto)⟩

theorem sv14f_setVmRoot (t : ObjRef) : SVK.SVM (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot getCurrentCr3 setCurrentVspaceRoot setCurrentCr3; sv_auto

theorem sv14f_deleteAsid (a : Asid) (p : ObjRef) : SVK.SVM (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid hwAsidInvalidate; sv_auto
  all_goals exact sv14f_setVmRoot _

theorem sv14f_deleteAsidPool (b : Asid) (p : ObjRef) : SVK.SVM (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool hwAsidInvalidate; sv_auto
  all_goals exact sv14f_setVmRoot _

theorem sv14f_archFinaliseCap (a : ArchCap) (fin : Bool) : SVK.SVM (archFinaliseCap (Z := Unit) a fin) := by
  unfold archFinaliseCap
  split <;> sv_auto
  all_goals first | exact sv14f_deleteAsid _ _ | exact sv14f_deleteAsidPool _ _

/-! ## The reply arm -/

/-- **`reply_remove caller r`** (`caller ≠ t`) keeps `t` unbound with no resume. -/
theorem ebn_replyRemove (t caller r : ObjRef) (hne : caller ≠ t) :
    IK (A14e.EBN t) (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove
  repeat' (first
    | (with_reducible refine A14e.ebn_donate _ _ _ ?_; assumption)
    | (with_reducible exact A14e.ebn_svm (SVK.sv_replyUnlinkTcb _ _))
    | ik_step0
    | (refine A14e.ebn_svm ?_; sv_auto; done)
    | split)

/-- The reply cap's fast finaliser keeps `EBN ct` (ct not `BlockedOnReply`). -/
theorem ebn_ffReply {s : State Unit} (r : ObjRef) (rt : CapRights) (fin : Bool) (hK : R14.CKN s)
    (hσ : A14e.EBN s.curThread s) : ∀ y ∈ (fastFinalise (Z := Unit) (.replyCap r rt) fin s).1,
      A14e.EBN s.curThread y.2 := by
  intro y hy
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
      have hne : tp ≠ σ1.curThread := by
        intro e; subst e
        exact (hK x hx).2 r' hxs
      exact ebn_replyRemove _ tp r' hne σ1 hσ y hy
    all_goals exact A14e.ebn_svm (B8e.sv_cancelIpc' tp) σ1 hσ y hy

/-- **The reply cap's fast finaliser keeps `DWS σ0`** (ct not `BlockedOnReply`). -/
theorem dws_ffReply {σ0 s : State Unit} (r : ObjRef) (rt : CapRights) (fin : Bool) (hs : DWS σ0 s)
    (hK : R14.CKN s) : ∀ y ∈ (fastFinalise (Z := Unit) (.replyCap r rt) fin s).1, DWS σ0 y.2 :=
  dws_pt hs (A14e.ec_ffReply r rt fin (ec_self hs.1) fun x hx r => (hK x hx).2 r)
    (fun hn => ebn_ffReply r rt fin hK hn)

/-! ## The SC arm -/

/-- Unbinding the TCB `t` of `p` (`t` current) leaves `t` unbound with no resume. -/
theorem ebn_unbindTcb_self (t p : ObjRef) (σ : State Unit) (hct : σ.curThread = t)
    (hT : ∀ y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t) :
    ∀ y ∈ (schedContextUnbindTcb (Z := Unit) p σ).1, A14e.EBN t y.2 := by
  intro y hy
  unfold schedContextUnbindTcb at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨n1, hk1, ez⟩ := SInvE.mem_getSchedContext hz
  obtain ⟨a1, ha1, hy⟩ := hy
  obtain ⟨eo, ea1⟩ := cq5_mem_assertOpt ha1
  have hat : a1.1 = t := by
    have := hT z.1 n1 hk1
    rw [this] at eo; exact (Option.some.inj eo).symm
  have es : a1.2 = σ := ea1.trans ez
  obtain ⟨a2, ha2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 ha2] at hy
  dsimp only at hy
  obtain ⟨b, hb, hy⟩ := hy
  rw [es] at hb
  unfold NonDet.when at hb
  split at hb
  swap
  · rename_i hne; exact absurd (hat.trans hct.symm) hne
  have nb : NRes b.2 := by
    show b.2.schedulerAction ≠ _
    rw [rescheduleRequired_cn σ b hb]; intro h'; cases h'
  obtain ⟨c2, hc2, hy⟩ := hy
  obtain ⟨c3, hc3, hy⟩ := hy
  obtain ⟨c4, hc4, hy⟩ := hy
  have s2 : SVK.SVS b.2 c2.2 := (by sv_auto : SVK.SVM (tcbSchedAction (Z := Unit) tcbSchedDequeue a1.1)) b.2 c2 hc2
  have s3 : SVK.SVS c2.2 c3.2 := (by sv_auto : SVK.SVM (tcbReleaseRemove (Z := Unit) a1.1)) c2.2 c3 hc3
  have n3 : NRes c3.2 := by
    unfold NRes at nb ⊢
    rcases (s2.trans s3).2.2 with e' | e'
    · rw [e']; exact nb
    · rw [e']; intro h''; cases h''
  have e4 : A14e.EBN t c4.2 := by
    rw [hat] at hc4
    obtain ⟨x, -, ex⟩ := SInv.mem_threadSet hc4
    refine ⟨?_, ?_⟩
    · intro p' x' hp ep
      subst ep
      rw [ex] at hp
      simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hp
      subst hp; rfl
    · unfold NRes at n3 ⊢; rw [ex]; exact n3
  exact (SInv.ik_and (by qb_auto) (by nres_auto) :
    IK (A14e.EBN t) (setScObjRef (Z := Unit) scTcbUpdate p none)) c4.2 e4 y hy

/-- **Finalising cur_sc: after `unbind_all_tcbs` ct is unbound with no resume.** -/
theorem ebn_unbindAll_cur (s : State Unit) (hEB : A14b.EB s.curThread s.curSc s) (hcb : SInvQ.CB s)
    (hni : s.curThread ≠ s.idleThread) (hK : R14.CKN s) (hSc : SInvB.ScInv s) (hnis : s.curSc ≠ s.idleSc) :
    ∀ y ∈ (schedContextUnbindAllTcbs (Z := Unit) s.curSc s).1, A14e.EBN s.curThread y.2 := by
  have hp : ∀ σ1 c, IK (A8.CP σ1 c) (schedContextUnbindAllTcbs (Z := Unit) s.curSc) := fun σ1 c => by
    unfold schedContextUnbindAllTcbs schedContextUnbindTcb; cp_auto
  have hq : IK (TP (QN s.curThread)) (schedContextUnbindAllTcbs (Z := Unit) s.curSc) := by
    unfold schedContextUnbindAllTcbs schedContextUnbindTcb; qn14f_auto
  by_cases hb : ∃ x, s.kheap s.curThread = some (.tcb x) ∧ x.tcbSchedContext = some s.curSc
  · obtain ⟨x, hx, hxb⟩ := hb
    obtain ⟨y0, k0, hy0, hyT, -⟩ := hSc.back s.curThread x s.curSc hx hxb
    intro y hy
    unfold schedContextUnbindAllTcbs at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨n1, hk1, ez⟩ := SInvE.mem_getSchedContext hz
    rw [hy0] at hk1
    obtain ⟨rfl, -⟩ : y0 = z.1 ∧ k0 = n1 := by
      injection hk1 with e; injection e with e1 e2; exact ⟨e1, e2⟩
    obtain ⟨w, hw, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hw] at hy
    dsimp only at hy
    rw [ez] at hy
    unfold NonDet.when at hy
    split at hy
    · exact ebn_unbindTcb_self _ _ s rfl (fun y n h => by rw [hy0] at h; cases h; exact hyT) y hy
    · rename_i hc
      exact absurd ⟨by rw [hyT]; exact Option.some_ne_none _, hnis⟩ hc
  · have hQ : TP (QN s.curThread) s := by
      intro p x hx ep
      subst ep
      rcases (hK x hx).1 with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ hb
    have hN : NRes s := by
      intro hres
      rcases hEB with ⟨hq', -⟩ | ⟨-, hn⟩
      · rcases hcb hres with ⟨x, hx, -⟩ | hi
        · exact hb ⟨x, hx, hq' _ x hx rfl⟩
        · exact hni hi
      · exact hn hres
    exact ebn_of hp hq s ⟨hQ, hN⟩

theorem mx0_updSc {p q : ObjRef} {f : SchedContext → SchedContext} {s : State Unit} (h : Mx0 p s)
    (hf : q = p → ∀ y, (f y).scRefillMax = 0 ∨ (f y).scRefillMax = y.scRefillMax) :
    ∀ y ∈ (updateSchedContext (Z := Unit) q f s).1, Mx0 p y.2 := by
  intro y hy z n hz
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e] at hz
  dsimp only at hz
  by_cases ep : q = p
  · subst ep
    rw [Function.update_self] at hz
    cases hz
    rcases hf rfl y0 with h0 | h0
    · exact h0
    · rw [h0]; exact h _ _ hk
  · rw [Function.update_of_ne (Ne.symm ep)] at hz; exact h z n hz

theorem mx0_setInactive (p : ObjRef) (s : State Unit) :
    ∀ y ∈ (schedContextSetInactive (Z := Unit) p s).1, Mx0 p y.2 := by
  intro y hy
  unfold schedContextSetInactive at hy
  obtain ⟨z1, hz1, z2, hz2, z3, hz3, hy⟩ := hy
  have m2 : Mx0 p z2.2 := by
    intro w n hw
    obtain ⟨y0, n0, -, e⟩ := SVK.updSc_mem hz2
    rw [e] at hw
    dsimp only at hw
    rw [Function.update_self] at hw
    cases hw; rfl
  have m3 := mx0_updSc (f := scBudgetUpdate fun _ => 0) m2 (fun _ _ => Or.inr rfl) z3 hz3
  exact mx0_updSc (f := scSporadicUpdate fun _ => false) m3 (fun _ _ => Or.inr rfl) y hy

theorem ebn_updSc (t q : ObjRef) (f : SchedContext → SchedContext) :
    IK (A14e.EBN t) (updateSchedContext (Z := Unit) q f) :=
  fun s hs y hy => ⟨tp_sok (Ipc.nks_updateSchedContext q f s y hy) hs.1, by
    have e : y.2.schedulerAction = s.schedulerAction := A14b.ak_updateSchedContext q f s y hy
    show y.2.schedulerAction ≠ _
    rw [e]; exact hs.2⟩

theorem ebn_setInactive (t p : ObjRef) : IK (A14e.EBN t) (schedContextSetInactive (Z := Unit) p) := by
  unfold schedContextSetInactive
  exact ik_bind (ebn_updSc t p _) fun _ => ik_bind (ebn_updSc t p _) fun _ =>
    ik_bind (ebn_updSc t p _) fun _ => ebn_updSc t p _

theorem cp_updSc_ne (q : ObjRef) (f : SchedContext → SchedContext) (σ1 : State Unit) (c : ObjRef) (hne : q ≠ c) :
    IK (A8.CP σ1 c) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  refine ⟨hs.1, hs.2.trans ⟨fun z n hz => ?_, id⟩⟩
  dsimp only at hz
  rw [Function.update_of_ne (Ne.symm hne)] at hz; exact ⟨z, n, hz, rfl, rfl⟩

theorem eb_updSc (t c q : ObjRef) (f : SchedContext → SchedContext) :
    IK (A14b.EB t c) (updateSchedContext (Z := Unit) q f) :=
  ik_eb (bl_of_nks (Ipc.nks_updateSchedContext q f)) (fun s hs y hy => tp_sok (Ipc.nks_updateSchedContext q f s y hy) hs)
    (fun s hs y hy => by
      have e : y.2.schedulerAction = s.schedulerAction := A14b.ak_updateSchedContext q f s y hy
      show y.2.schedulerAction ≠ _; rw [e]; exact hs)

/-- Making an SC other than `σ1`'s cur_sc inactive keeps rd14d's `EC σ1`. -/
theorem ec_setInactive_ne (σ1 : State Unit) (p : ObjRef) (hne : p ≠ σ1.curSc) :
    IK (A14d.EC σ1) (schedContextSetInactive (Z := Unit) p) := by
  have hp : IK (A8.CP σ1 σ1.curSc) (schedContextSetInactive (Z := Unit) p) := by
    unfold schedContextSetInactive
    exact ik_bind (cp_updSc_ne p _ σ1 _ hne) fun _ => ik_bind (cp_updSc_ne p _ σ1 _ hne) fun _ =>
      ik_bind (cp_updSc_ne p _ σ1 _ hne) fun _ => cp_updSc_ne p _ σ1 _ hne
  have he : IK (A14b.EB σ1.curThread σ1.curSc) (schedContextSetInactive (Z := Unit) p) := by
    unfold schedContextSetInactive
    exact ik_bind (eb_updSc _ _ p _) fun _ => ik_bind (eb_updSc _ _ p _) fun _ =>
      ik_bind (eb_updSc _ _ p _) fun _ => eb_updSc _ _ p _
  exact A14d.ec_ik (cfk_schedContextSetInactive' p) hp fun s _ h => he s h

/-! ## `fast_finalise`, `cap_delete_one`, `finalise_cap` -/

theorem dws_fastFinalise {σ0 s : State Unit} (cap : Cap) (fin : Bool) (hs : DWS σ0 s) (hK : R14.CKN s) :
    ∀ y ∈ (fastFinalise (Z := Unit) cap fin s).1, DWS σ0 y.2 := by
  cases cap
  case replyCap r rt => exact dws_ffReply r rt fin hs hK
  case endpointCap r b rt =>
    simp only [fastFinalise]; exact (dst_when _ (dst_cancelAllIpc r)).dws s hs
  case notificationCap r b rt =>
    simp only [fastFinalise]; exact (dst_when _ (dst_ffNtfn r)).dws s hs
  case nullCap => simp only [fastFinalise]; exact (dst_pure ()).dws s hs
  all_goals (simp only [fastFinalise]; exact ik_fail s hs)

/-- **`cap_delete_one` keeps `DWS σ0`** (ct not `BlockedOnReply`). -/
theorem dws_capDeleteOne {σ0 s : State Unit} (sl : CslotPtr) (hs : DWS σ0 s) (hK : R14.CKN s) :
    ∀ y ∈ (capDeleteOne (Z := Unit) sl s).1, DWS σ0 y.2 := by
  intro y hy
  unfold capDeleteOne at hy
  obtain ⟨⟨cap, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := cq5_ro (fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)) h1
  subst e1
  dsimp only [NonDet.unless] at hy
  split at hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hs
  · obtain ⟨⟨fin, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = s1 := cq5_ro (fun _ => by unfold isFinalCap; repeat' (first | ik_step0 | ik_unfold)) h2
    subst e2
    obtain ⟨w, hw, hy⟩ := hy
    exact (dst_svcf (A14e.sv_emptySlotNull sl) (cfk_emptySlotNull sl)).dws w.2 (dws_fastFinalise cap fin hs hK w hw) y hy

/-- **`finalise_cap` keeps `DWS σ0`** (module docstring). -/
theorem dws_finaliseCap {σ0 s : State Unit} (c : Cap) (fin : Bool) (hs : DWS σ0 s) (hK : R14.CKN s)
    (hSc : SInvB.ScInv s) (hcb : SInvQ.CB s) (hni : σ0.curThread ≠ σ0.idleThread) :
    ∀ y ∈ (finaliseCap (Z := Unit) c fin s).1, DWS σ0 y.2 := by
  cases c
  case replyCap r rt =>
    intro y hy
    simp only [finaliseCap] at hy
    obtain ⟨w, hw, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy]
    exact dws_ffReply r rt fin hs hK w (by simp only [fastFinalise]; exact hw)
  case endpointCap r b rt =>
    simp only [finaliseCap]; exact (dst_liftM _ (dst_when _ (dst_cancelAllIpc r))).dws s hs
  case notificationCap r b rt =>
    simp only [finaliseCap]; exact (dst_liftM _ (dst_when _ (dst_ffNtfn r))).dws s hs
  case threadCap r =>
    simp only [finaliseCap]
    refine (dst_bind (dst_when _ (dst_svcf (by unfold unbindNotification; sv_auto) (cfk_unbindNotification' r)))
      fun _ => dst_bind (dst_when _ (dst_unbindFromSc r)) fun _ =>
        dst_bind (dst_when _ (dst_svcf (sv14_suspend r) (cfk_suspend' r))) fun _ =>
          dst_bind (dst_when _ (dst_svcf (by unfold prepareThreadDelete; sv_auto) (cfk_prepareThreadDelete' r)))
            fun _ => dst_pure _).dws s hs
  case schedContextCap p b =>
    have hcf := cfk_finaliseCap (.schedContextCap p b) fin
    intro y hy
    have ecf : cfS y.2 = cfS s := hcf s y hy
    cases fin
    · simp only [finaliseCap, NonDet.when, Bool.false_eq_true, ↓reduceIte] at hy
      obtain ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩ := hy
      simp only [Set.mem_singleton_iff] at hz1 hz2 hz3 hz4 hz5 hy
      subst hz1 hz2 hz3 hz4 hz5 hy
      exact hs
    · simp only [finaliseCap, NonDet.when, ↓reduceIte] at hy
      obtain ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hy]
      by_cases hp : p = s.curSc
      · subst hp
        have hd := hs.1
        have hEB : A14b.EB s.curThread s.curSc s := by rw [hd.ct, hd.cs]; exact hd.eb
        have hni' : s.curThread ≠ s.idleThread := by rw [hd.ct, hd.it]; exact hni
        have hnis' : s.curSc ≠ s.idleSc := by rw [hd.cs, hd.is]; exact hd.nis
        have n1 := ebn_unbindAll_cur s hEB hcb hni' hK hSc hnis' z1 hz1
        have n2 := A14e.ebn_svm (B8f.sv_schedContextUnbindNtfn' s.curSc) z1.2 n1 z2 hz2
        have n3 := A14e.ebn_svm (B8f.sv_schedContextUnbindReply' s.curSc) z2.2 n2 z3 hz3
        have n4 := A14e.ebn_svm (B8f.sv_schedContextUnbindYieldFrom' s.curSc) z3.2 n3 z4 hz4
        have n5 := ebn_setInactive _ s.curSc z4.2 n4 z5 hz5
        have m5 := mx0_setInactive s.curSc z4.2 z5 hz5
        have ecf' : cfS z5.2 = cfS s := by
          have := ecf; rw [Set.mem_singleton_iff.1 hy] at this; exact this
        have hc' := ecf'
        simp only [cfS, Prod.mk.injEq] at hc'
        obtain ⟨-, e2, e3, e4, e5, -⟩ := hc'
        have n5' : A14e.EBN σ0.curThread z5.2 := by rw [← hd.ct]; exact n5
        have m5' : Mx0 σ0.curSc z5.2 := by rw [← hd.cs]; exact m5
        refine ⟨⟨e2.trans hd.cs, e3.trans hd.ct, e4.trans hd.it, e5.trans hd.is, hd.nis,
          Or.inr ⟨n5'.1, n5'.2⟩, Or.inr ⟨m5', n5'⟩⟩, ?_⟩
        intro z n hz ha _
        rw [e2] at hz
        have h0 := m5 z n hz
        simp only [scActive, activeSc, h0, lt_self_iff_false, decide_false] at ha
        exact absurd ha Bool.false_ne_true
      · have hE : A14d.EC s z5.2 := by
          have e1 := A14d.ec_schedContextUnbindAllTcbs s p s (ec_self hs.1) z1 hz1
          have e2 := A14d.ec_svcf (B8f.sv_schedContextUnbindNtfn' p) (cfk_schedContextUnbindNtfn' p) z1.2 e1 z2 hz2
          have e3 := A14d.ec_svcf (B8f.sv_schedContextUnbindReply' p) (cfk_schedContextUnbindReply' p) z2.2 e2 z3 hz3
          have e4 := A14d.ec_svcf (B8f.sv_schedContextUnbindYieldFrom' p) (cfk_schedContextUnbindYieldFrom' p)
            z3.2 e3 z4 hz4
          exact ec_setInactive_ne s p hp z4.2 e4 z5 hz5
        have hN : A14e.EBN s.curThread s → A14e.EBN s.curThread z5.2 := by
          intro hn
          have hq : IK (TP (QN s.curThread)) (schedContextUnbindAllTcbs (Z := Unit) p) := by
            unfold schedContextUnbindAllTcbs schedContextUnbindTcb; qn14f_auto
          have hpp : ∀ σ1 c, IK (A8.CP σ1 c) (schedContextUnbindAllTcbs (Z := Unit) p) := fun σ1 c => by
            unfold schedContextUnbindAllTcbs schedContextUnbindTcb; cp_auto
          have n1 := ebn_of hpp hq s hn z1 hz1
          have n2 := A14e.ebn_svm (B8f.sv_schedContextUnbindNtfn' p) z1.2 n1 z2 hz2
          have n3 := A14e.ebn_svm (B8f.sv_schedContextUnbindReply' p) z2.2 n2 z3 hz3
          have n4 := A14e.ebn_svm (B8f.sv_schedContextUnbindYieldFrom' p) z3.2 n3 z4 hz4
          exact ebn_setInactive _ p z4.2 n4 z5 hz5
        exact ⟨dw_step hs.1 hE.1 hE.2.1 hE.2.2 hN, suff_cw hs.2 hE.2.1 hE.1⟩
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · intro y ⟨z, hz, hy⟩
      rw [Set.mem_singleton_iff.1 hy]
      unfold deletingIrqHandler getIrqSlot at hz
      obtain ⟨w, hw, hz⟩ := hz
      have e : w.2 = s := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
      exact dws_capDeleteOne _ (e ▸ hs) (e ▸ hK) z hz
    · exact (dst_pure _).dws s hs
  case zombie r b n =>
    have H : IK (DWS σ0) (finaliseCap (Z := Unit) (.zombie r b n) fin) := by
      simp only [finaliseCap]; repeat' (first | ik_step0 | ik_unfold)
    exact H s hs
  case archObjectCap a =>
    simp only [finaliseCap]
    exact (dst_svcf (sv14f_archFinaliseCap a fin) (cfk_archFinaliseCap' a fin)).dws s hs
  case cnodeCap r bits g => simp only [finaliseCap]; exact (dst_pure _).dws s hs
  all_goals (simp only [finaliseCap]; exact (dst_pure _).dws s hs)

end

end Fl4Proofs.P3.SInvR.A14f
