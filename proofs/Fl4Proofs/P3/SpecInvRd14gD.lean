/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (c), (d)): **`PerfF`
for rd14d's SchedContext arms and CNode cancelBadgedSends; the tops over both
interfaces** (spec side only).

* `ec_invokeSchedContext` (rd14d's `EC` walks of `perfA_schedContext`, as one
  `IK`), **`qt_invokeSchedContext`** (rd14c's `QT ct` across every
  SchedContext arm: rd14e's `qt14e_auto`), **`perfF_schedContext`**
  (rd14e's `perfF_ecq`); **`perfF_scBindTcb`** (rd14d's `TB` walk, the bound
  TCB not ct by sb2's `BindOK`); **`perfF_cancelBadged`** (`TB` and `QT`:
  restart / Inactive writes only); `CovFD`, **`armFU_covFD`**.
* `CF14g := CF14e ∨ CovU ∨ CovFD` (`armFU_cf14g`).
* Tops: `qfu_ofW` / `qfu_fip` (rd14g C's `QFU C` at the entry / FaultIP
  outcome from `SInvW`), **`kcall_rdyOffF`** / **`kentry_rdyOffF`**: rd8w's tops
  over `ArmAKU CR` and `ArmFU CF` with the bridges `brR_ku` / `brF_ku`;
  **`kcall_rdyOffG`** / **`kentry_rdyOffG`**: `CR := fun _ => True`
  (rd14g B's `armAKU_all`: no `PerfA` input), `CF := CF14g`.
-/
import Fl4Proofs.P3.SpecInvRd14gC
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## SchedContext -/

theorem ec_invokeSchedContext (σ0 : State Unit) (i : SchedContextInvocation) (hc : CovSc i) :
    IK (EC σ0) (invokeSchedContext (Z := Unit) i) := by
  cases i with
  | invokeSchedContextConsumed p =>
    show IK (EC σ0) (returnConsumed (Z := Unit) p)
    exact ec_svcf (by unfold returnConsumed schedContextUpdateConsumed; sv_auto) (cfk_returnConsumed' p)
  | invokeSchedContextBind p cap =>
    cases cap
    case threadCap t => exact (hc : False).elim
    case notificationCap n b r =>
      show IK (EC σ0) (do schedContextBindNtfn (Z := Unit) p n; return [])
      exact ec_svcf (by unfold schedContextBindNtfn; sv_auto) (by cfk_auto)
    all_goals exact ik_fail
  | invokeSchedContextUnbindObject p cap =>
    cases cap
    case threadCap t =>
      show IK (EC σ0) (do schedContextUnbindTcb (Z := Unit) p; return [])
      exact ik_bind (ec_schedContextUnbindTcb σ0 p) fun _ => ik_pure _
    case notificationCap n b r =>
      show IK (EC σ0) (do schedContextUnbindNtfn (Z := Unit) p; return [])
      exact ec_svcf (by sv_auto; all_goals exact B8f.sv_schedContextUnbindNtfn' p) (by cfk_auto)
    all_goals exact ik_fail
  | invokeSchedContextUnbind p =>
    show IK (EC σ0) (do
      schedContextUnbindAllTcbs (Z := Unit) p
      schedContextUnbindNtfn (Z := Unit) p
      schedContextUnbindReply (Z := Unit) p
      return [])
    refine ik_bind (ec_schedContextUnbindAllTcbs σ0 p) fun _ => ?_
    refine ik_bind (ec_svcf (B8f.sv_schedContextUnbindNtfn' p) (cfk_schedContextUnbindNtfn' p)) fun _ => ?_
    exact ik_bind (ec_svcf (B8f.sv_schedContextUnbindReply' p) (cfk_schedContextUnbindReply' p)) fun _ => ik_pure _
  | invokeSchedContextYieldTo p =>
    show IK (EC σ0) (schedContextYieldTo (Z := Unit) p)
    exact ec_svcf (by unfold schedContextYieldTo returnConsumed schedContextUpdateConsumed; sv_auto)
      (cfk_schedContextYieldTo' p)

theorem qt_returnConsumed (t p : ObjRef) : IK (QT t) (returnConsumed (Z := Unit) p) :=
  qt_of_tv t fun _ => by unfold returnConsumed; tv_auto

theorem qt_completeYieldTo (t p : ObjRef) : IK (QT t) (completeYieldTo (Z := Unit) p) := by
  unfold completeYieldTo
  refine SInv.ik_bind (by qt_auto) fun yt => SInv.ik_maybeM (fun sc => ?_) yt
  exact SInv.ik_bind (qt_of_tv t fun _ => by unfold setConsumed; tv_auto) fun _ => qt_cancelYieldTo t p

/-- rd14e's `qt14e_auto` with the yield-to leaves. -/
macro "qt14g_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact qt_returnConsumed _ _)
  | (with_reducible exact qt_completeYieldTo _ _)
  | (with_reducible exact qt_replyRemove _ _ _)
  | (with_reducible refine qt_handleTimeout _ _ _ ?_; assumption)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_doIpcTransfer _ _ _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getCap _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_setCap _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_capInsert _ _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_lookupIpcBuffer _ _)
  | (with_reducible exact qt_of_tv _ fun _ => B8d.tv_getMessageInfo _)
  | (with_reducible exact qt_cancelIpc _ _)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => fk_testReschedule ..)
  | (with_reducible exact qt_of_nks (nks_ifCondG _ _ _))
  | (with_reducible refine qt_setThreadState_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_threadSet_ne _ _ _ ?_; assumption)
  | (with_reducible refine qt_setThreadState _ _ _ ?_; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))
  | ((with_reducible refine qt_threadSet _ _ _ ?_); intro _ h; exact h)
  | (with_reducible exact qt_setSimpleKo _ _ _ _)
  | (with_reducible refine qt_setObject _ _ _ ?_; intro _ h; cases h; done)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_asUser ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbSchedAction ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_tcbReleaseRemove ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_possibleSwitchTo ..)
  | (with_reducible exact qt_of_fk fun _ _ _ _ _ _ => SInvR.fk_rescheduleRequired ..)
  | (with_reducible exact qt_of_nks (nks_ifCond _))
  | (with_reducible exact qt_of_nks (nks_schedContextResume _))
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when) | (with_reducible apply SInv.ik_ite)
  | (with_reducible refine SInv.ik_maybeM (fun _ => ?_) _)
  | ik_step0 | ik_unfold
  | split))

set_option maxHeartbeats 4000000 in
theorem qt_invokeSchedContext (t : ObjRef) (i : SchedContextInvocation) :
    IK (QT t) (invokeSchedContext (Z := Unit) i) := by
  cases i with
  | invokeSchedContextConsumed p =>
    show IK (QT t) (returnConsumed (Z := Unit) p)
    exact qt_of_tv t fun _ => by unfold returnConsumed; tv_auto
  | invokeSchedContextBind p cap =>
    cases cap
    case threadCap t' =>
      show IK (QT t) (do schedContextBindTcb (Z := Unit) p t'; return [])
      unfold schedContextBindTcb; qt14e_auto
    case notificationCap n b r =>
      show IK (QT t) (do schedContextBindNtfn (Z := Unit) p n; return [])
      unfold schedContextBindNtfn; qt14e_auto
    all_goals exact ik_fail
  | invokeSchedContextUnbindObject p cap =>
    cases cap
    case threadCap t' =>
      show IK (QT t) (do schedContextUnbindTcb (Z := Unit) p; return [])
      unfold schedContextUnbindTcb; qt14e_auto
    case notificationCap n b r =>
      show IK (QT t) (do schedContextUnbindNtfn (Z := Unit) p; return [])
      unfold schedContextUnbindNtfn; qt14e_auto
    all_goals exact ik_fail
  | invokeSchedContextUnbind p =>
    show IK (QT t) (do
      schedContextUnbindAllTcbs (Z := Unit) p
      schedContextUnbindNtfn (Z := Unit) p
      schedContextUnbindReply (Z := Unit) p
      return [])
    unfold schedContextUnbindAllTcbs schedContextUnbindTcb schedContextUnbindNtfn schedContextUnbindReply
    qt14e_auto
  | invokeSchedContextYieldTo p =>
    show IK (QT t) (schedContextYieldTo (Z := Unit) p)
    unfold schedContextYieldTo; qt14g_auto

theorem perfF_schedContext {σ0 u : State Unit} (i : SchedContextInvocation) (hc : CovSc i) (h : RF σ0 u) :
    PerfF σ0 (.invokeSchedContext i) u := by
  refine perfF_ecq h.bs fun y hy _ _ => ?_
  have he : fl4PerformInvocation (Z := Unit) false false true (.invokeSchedContext i) =
      NonDetE.liftE (invokeSchedContext (Z := Unit) i) := rfl
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨ec_invokeSchedContext σ0 i hc u (ec_of_tb h.tb) x hx, qt_invokeSchedContext _ i u h.qt x hx⟩

theorem perfF_scBindTcb {σ0 u : State Unit} (c t : ObjRef) (h : RF σ0 u)
    (ht : ∀ x, u.kheap t = some (.tcb x) → x.tcbSchedContext = none) :
    PerfF σ0 (.invokeSchedContext (.invokeSchedContextBind c (.threadCap t))) u := by
  have hne : t ≠ σ0.curThread := by
    intro e; subst e
    obtain ⟨x, hx⟩ := h.ct
    have h1 := h.bd x hx
    rw [ht x hx] at h1; cases h1
  refine perfF_liftTQ _ rfl h.bs ?_ (qt_invokeSchedContext _ _) h.tb h.qt
  show IK (TB σ0) (do schedContextBindTcb (Z := Unit) c t; return [])
  refine ik_bind ?_ fun _ => ik_pure _
  refine tb_ik ?_ ?_ ?_
  · unfold schedContextBindTcb; cfk_auto
  · unfold schedContextBindTcb
    refine ik_bind (A8.cp_threadSet _ _ _ _) fun _ => ik_bind (by cp_leaf) fun _ => ?_
    refine ik_bind (A8.cp_ifCondTest _ _ σ0 _) fun _ => ik_bind (A8.cp_schedContextResume _ σ0 _) fun _ => ?_
    exact ik_bind (ik_gets _) fun _ => ik_when _ (by cp_auto)
  · unfold schedContextBindTcb
    refine SInv.ik_bind (SInv.ik_and (tp_threadSet _ _ fun _ _ e => absurd e hne) (by ks_auto)) fun _ => ?_
    refine SInv.ik_bind (SInv.ik_and (by qb_auto) (by ks_auto)) fun _ => ?_
    refine SInv.ik_bind (bl_of_nks (nks_ifCondG _ _ _)) fun _ => ?_
    refine SInv.ik_bind (bl_of_nks (nks_schedContextResume _)) fun _ => ?_
    refine SInv.ik_bind (SInv.ik_gets _) fun _ => SInv.ik_when _ ?_
    exact SInv.ik_bind (bl_of_svm (by sv_auto)) fun _ => bl_of_svm SVK.sv_rescheduleRequired'

/-! ## CNode cancelBadgedSends -/

theorem qt_cancelBadgedSends (t ep : ObjRef) (b : Badge) : IK (QT t) (cancelBadgedSends (Z := Unit) ep b) := by
  unfold cancelBadgedSends removeAndRestartBadgedThread restartThreadIfNoFault; qt14e_auto

theorem perfF_cancelBadged {σ0 u : State Unit} (cap : Cap) (h : RF σ0 u) :
    PerfF σ0 (.invokeCNode (.cancelBadgedSendsCall cap)) u := by
  refine perfF_tbq h.bs fun y hy a ha => ?_
  change y ∈ ((invokeCnode (Z := Unit) (.cancelBadgedSendsCall cap) >>= fun _ => NonDetE.returnOk []).run u).1 at hy
  obtain ⟨z, hz, ⟨a', -, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · rw [SInvU.mem_ret_ok hy]
    cases cap
    case endpointCap ep bd r =>
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
      exact ⟨ik_when _ (tb_cancelBadgedSends σ0 ep bd) u h.tb x hx,
        SInv.ik_when _ (qt_cancelBadgedSends _ ep bd) u h.qt x hx⟩
    all_goals
      obtain ⟨x, hx, -⟩ := ft_mem_liftE hz
      first | (simp [NonDet.fail] at hx) | exact hx.elim | cases hx
  · cases ha

def CovFD : Fl4Invocation → Prop
  | .invokeSchedContext _ => True
  | .invokeCNode (.cancelBadgedSendsCall _) => True
  | _ => False

theorem armFU_covFD : ArmFU CovFD := by
  intro σ0 s u h0 b I hc hB hS hi hz hbo hbr hRB hF hL hG hu
  have hR : RF σ0 u.2 := rf_restart hB hS hz hu
  cases b
  case invokeSchedContext i =>
    by_cases hb : CovSc i
    · exact perfF_schedContext i hb hR
    · cases i with
      | invokeSchedContextBind c cap =>
        cases cap
        case threadCap t => exact perfF_scBindTcb c t hR (unb_of_bindOK hbo.2 hbr hu)
        all_goals exact (hb trivial).elim
      | _ => exact (hb trivial).elim
  case invokeCNode i =>
    cases i
    case cancelBadgedSendsCall cap => exact perfF_cancelBadged cap hR
    all_goals exact (hc : False).elim
  all_goals exact (hc : False).elim

/-- The arms with `PerfF` so far. -/
def CF14g (b : Fl4Invocation) : Prop := CF14e b ∨ CovU b ∨ CovFD b

theorem armFU_cf14g : ArmFU CF14g := (armFU_of armF_c14e).or (armFU_covU.or armFU_covFD)

/-! ## Tops -/

section Tops
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
open Fl4Proofs.P3.SInvR.B8w

variable {σ : State Unit}

theorem qfu_ofW {C : Fl4Invocation → Prop} {ev : Event} (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (c : Syscall) (e : ev = .syscallEvent c)
    (hP : InvFc C c σ) : QFU C c σ := by
  have hq := qu_ofW (C := fun _ => True) h hev c e (invRc_all c σ)
  exact ⟨hP, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1, hq.1.2.2.2.2.2, hq.2.1, hq.2.2⟩

theorem qfu_fip {C : Fl4Invocation → Prop} (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, InvFc C c w.2 → QFU C c w.2 := by
  intro w hw hP
  have hq := qu_fip (C := fun _ => True) c h hct w hw (invRc_all c w.2)
  exact ⟨hP, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.1.2.2.2.2.1, hq.1.2.2.2.2.2, hq.2.1, hq.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across every kernel event** with `PerfA` asked only outside `CR` and `PerfF` only outside `CF`. -/
theorem kcall_rdyOffF {CR CF : Fl4Invocation → Prop} (hA : ArmAKU CR) (hAF : ArmFU CF) (hnd : numDomains = 1)
    (rep : Bool) (ev : Event) (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc CR c σ) (hF : ∀ c, ev = .syscallEvent c → InvFc CF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_ku hA) (brF_ku hAF) (fun c e => qu_ofW h hev c e (hP c e))
    (fun c e => qfu_ofW h hev c e (hF c e))

set_option maxHeartbeats 4000000 in
theorem kentry_rdyOffF {CR CF : Fl4Invocation → Prop} (hA : ArmAKU CR) (hAF : ArmFU CF) (hnd : numDomains = 1)
    (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc CR c w.2 ∧ InvFc CF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffW hnd c h hct (brR_ku hA) (brF_ku hAF) fun w hw =>
    ⟨qu_fip c h hct w hw (hW w hw).1, qfu_fip c h hct w hw (hW w hw).2⟩

/-- **Today's tops**: no `PerfA` input; `PerfF` asked only outside `CF14g`. -/
theorem kcall_rdyOffG (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hF : ∀ c, ev = .syscallEvent c → InvFc CF14g c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffF armAKU_all armFU_cf14g hnd rep ev h hev (fun c _ => invRc_all c σ) hF

theorem kentry_rdyOffG (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, InvFc CF14g c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffF armAKU_all armFU_cf14g hnd c h hct fun w hw => ⟨invRc_all c w.2, hW w hw⟩

/-- **The end target's shape**: with `ArmFU` for every arm, no input at all. -/
theorem kcall_rdyOff9_of (hAF : ArmFU fun _ => True) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffF armAKU_all hAF hnd rep ev h hev (fun c _ => invRc_all c σ) (fun c _ => invFc_true c σ)

theorem kentry_rdyOff9_of (hAF : ArmFU fun _ => True) (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffF armAKU_all hAF hnd c h hct fun w _ => ⟨invRc_all c w.2, invFc_true c w.2⟩

end Tops

end

end Fl4Proofs.P3.SInvR.A14g
