/-
P3 (DESIGN.md §9), invariant line G1 (rd14c, KENTRY-PLAN rd14b handoff 2):
**`PerfF` for the TCB suspend / resume / register arms** (spec side only).

* `QT t s`: `t` is a TCB whose state is Restart, Running or Inactive. An `IK`
  family with generic leaves (no step-by-step walk of the scheduler callees):
  rd4's heap-view family `SInvR.FK` (`asUser`, the queue writers,
  `possibleSwitchTo`, `rescheduleRequired`: the view erases only the arch
  field, so TCB states are kept) and IpcSchedLift's `NKS` (refill callees,
  `schedContextResume`: only SCs change) by transfer (`qt_of_fk`,
  `qt_of_nks`); `qt_setObject` / `qt_setSimpleKo` (`a_type` is asserted, so a
  TCB stays a TCB); `qt_threadSet` (a state-respecting update),
  `qt_setThreadState` (a Restart / Running / Inactive write, any thread).
* **`fpo_tb`**: rd13b's `TB σ0` and ct Running / Inactive give rd14b's `FPO`
  (RT and CBa of ct from σ0's `CAx` and `OffReady` through `CW`).
* **`perfF_tbq`**: an arm whose `ok` outcomes keep `TB σ0 ∧ QT ct` has
  rd14b's `PerfF`; **`perfF_covC`**: every arm of SpecInvRd14cA's `CovC`
  (suspend / resume / read / write / copy registers, any flags).
-/
import Fl4Proofs.P3.SpecInvRd14cA
import Fl4Proofs.P3.IpcStK
open Classical

namespace Fl4Proofs.P3.SInvR.A14c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## ct a TCB in a good state -/

abbrev GS (ts : ThreadState) : Prop := ts = .restart ∨ ts = .running ∨ ts = .inactive

/-- `t` is a TCB in a good state. -/
abbrev QT (t : ObjRef) (s : State Unit) : Prop := ∃ x, s.kheap t = some (.tcb x) ∧ GS x.tcbState

theorem qt_hv {t : ObjRef} {s s' : State Unit} (hk : ∀ q, SInvR.HV (s'.kheap q) = SInvR.HV (s.kheap q))
    (h : QT t s) : QT t s' := by
  obtain ⟨x, hx, g⟩ := h
  have e := hk t
  rw [hx] at e
  obtain ⟨x', hx', hxx⟩ := SInvR.hv_tcb e
  have es : x'.tcbState = x.tcbState := by
    have h2 := congrArg Tcb.tcbState hxx
    simpa [SInvR.hvT] using h2
  exact ⟨x', hx', by rw [es]; exact g⟩

theorem qt_sok {t : ObjRef} {s s' : State Unit} (hk : Ipc.ScOnlyK s s') (h : QT t s) : QT t s' := by
  obtain ⟨x, hx, g⟩ := h
  rcases hk.1 t with e | ⟨y, n, y', a1, -⟩
  · exact ⟨x, by rw [e]; exact hx, g⟩
  · rw [hx] at a1; cases a1

theorem qt_of_fk {t : ObjRef} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ K c u T I S, IK (SInvR.FK K c u T I S) m) : IK (QT t) m :=
  ik_of_fk (fun _ _ hk h' => qt_hv hk h') h

theorem qt_of_nks {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : Ipc.NKS m) : IK (QT t) m :=
  ik_of_nks (fun _ _ hk h' => qt_sok hk h') h

/-- A type-asserted `set_object` keeps `QT` when a TCB written is in a good state. -/
theorem qt_setObject (t p : ObjRef) (o : KernelObject) (ho : ∀ x, o = .tcb x → GS x.tcbState) :
    IK (QT t) (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨x0, h0, g0⟩ := hσ
  by_cases e : p = t
  · subst e
    rw [h0] at hk; cases hk
    cases o with
    | tcb y => exact ⟨y, by simp, ho y rfl⟩
    | _ => revert hty; simp only [aType]; first | (intro hty; cases hty) | (split_ifs <;> intro hty <;> cases hty)
  · refine ⟨x0, ?_, g0⟩
    dsimp only
    rw [Function.update_of_ne (fun h => e h.symm)]
    exact h0

theorem qt_setSimpleKo {α : Type} [Nonempty α] (t : ObjRef) (f : α → KernelObject) (p : ObjRef) (e : α) :
    IK (QT t) (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hsimp, rfl⟩, hx⟩ := hx
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hk3, hs3⟩ := mem_getObject hy3
  obtain ⟨obj', y3⟩ := y3
  simp only at hk3 hs3 hsimp; subst hs3
  rw [hk] at hk3; cases hk3
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨x0, h0, g0⟩ := hσ
  by_cases ep : p = t
  · subst ep
    rw [h0] at hk; cases hk
    exfalso
    simp only [isSimpleType, Set.mem_insert_iff, Set.mem_singleton_iff] at hsimp
    rcases hsimp with h | h | h <;> simp [aType] at h
  · refine ⟨x0, ?_, g0⟩
    dsimp only
    rw [Function.update_of_ne (fun h => ep h.symm)]
    exact h0

theorem qt_threadSet (t : ObjRef) (f : Tcb → Tcb) (p : ObjRef) (hf : ∀ x, GS x.tcbState → GS (f x).tcbState) :
    IK (QT t) (threadSet (Z := Unit) f p) := by
  intro s hs y hy
  obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hy
  obtain ⟨x0, h0, g0⟩ := hs
  rw [e]
  by_cases hp : p = t
  · subst hp
    rw [hx] at h0; cases h0
    exact ⟨f x, by simp, hf x g0⟩
  · refine ⟨x0, ?_, g0⟩
    dsimp only
    rw [Function.update_of_ne (fun h => hp h.symm)]
    exact h0

theorem qt_setThreadState (t p : ObjRef) (st : ThreadState) (hst : GS st) :
    IK (QT t) (setThreadState (Z := Unit) p st) := by
  unfold setThreadState
  refine SInv.ik_bind (qt_threadSet t _ p fun _ _ => hst) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction
  repeat' (first | (with_reducible apply SInv.ik_when) | ik_step0)

/-- The walk keeping `QT t` over the TCB arms' callees. -/
macro "qt_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible refine qt_setThreadState _ _ _ ?_; first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))
  | (with_reducible refine qt_threadSet _ _ _ ?_; intro _ h; exact h)
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
  | ik_step0 | ik_unfold))

/-- **`cancel_ipc`** without a walk: SVS keeps the TCB, rd's `StK` the other
threads' states; for `p = t` the state read is good, so only the fault is
cleared. -/
theorem qt_cancelIpc (t p : ObjRef) : IK (QT t) (cancelIpc (Z := Unit) p) := by
  intro s hs y hy
  have hS := B8e.sv_cancelIpc' p s y hy
  obtain ⟨x0, h0, g0⟩ := hs
  have e1 := hS.1 t
  rw [h0] at e1
  obtain ⟨x1, h1, -⟩ := SVK.sv_tcb (o := y.2.kheap t) (a := x0.tcbSchedContext) e1
  by_cases hp : p = t
  · subst hp
    unfold cancelIpc at hy
    obtain ⟨w, hw, hy⟩ := hy
    unfold getThreadState at hw
    obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
    rw [h0] at hx; cases hx
    obtain ⟨w2, hw2, hy⟩ := hy
    obtain ⟨x2, hx2, e2⟩ := SInv.mem_threadSet hw2
    rw [h0] at hx2; cases hx2
    have hy' : y = ((), w2.2) := by
      rcases g0 with g | g | g <;> (dsimp only at hy; rw [g] at hy; dsimp only at hy; exact Set.mem_singleton_iff.1 hy)
    rw [hy', e2]
    exact ⟨{ x0 with tcbFault := none }, by simp, g0⟩
  · obtain ⟨y0, hy0, es⟩ := (StK.st_cancelIpc (t0 := p) s y hy).1 t x1 (fun e => hp e.symm) h1
    rw [h0] at hy0; cases hy0
    exact ⟨x1, h1, by rw [es]; exact g0⟩

theorem qt_cancelYieldTo (t p : ObjRef) : IK (QT t) (schedContextCancelYieldTo (Z := Unit) p) := by
  unfold schedContextCancelYieldTo
  refine SInv.ik_bind (by qt_auto) fun yt => SInv.ik_maybeM (fun sc => ?_) yt
  refine SInv.ik_bind (by qt_auto) fun _ => ?_
  exact qt_threadSet t _ p fun x h => by simpa [tcbYieldToUpdate] using h

theorem qt_suspend (t p : ObjRef) : IK (QT t) (suspend (Z := Unit) p) := by
  unfold suspend updateRestartPc
  refine SInv.ik_bind (qt_cancelIpc t p) fun _ => ?_
  repeat' (first
    | (with_reducible exact qt_cancelYieldTo t p)
    | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
    | qt_auto)

theorem qt_restart (t p : ObjRef) : IK (QT t) (restart (Z := Unit) p) := by
  unfold restart testPossibleSwitchTo
  refine SInv.ik_bind (by qt_auto) fun _ => SInv.ik_bind (by qt_auto) fun _ => SInv.ik_when _ ?_
  refine SInv.ik_bind (qt_cancelIpc t p) fun _ => ?_
  qt_auto

/-! ## `FPO` from `TB` -/

/-- **`TB σ0` with ct Running / Inactive gives `FPO`.** -/
theorem fpo_tb {σ0 q : State Unit} (hB : A10.BS σ0) (h : TB σ0 q) {x : Tcb}
    (hx : q.kheap σ0.curThread = some (.tcb x))
    (hst : x.tcbState = .running ∨ x.tcbState = .inactive ∨ x.tcbState = .idleThreadState) : FPO q := by
  have et : q.curThread = σ0.curThread := cf_curThread h.cf
  have ecs : q.curSc = σ0.curSc := cf_curSc h.cf
  obtain ⟨y, n, hy⟩ := h.sc
  obtain ⟨y0, n0, hy0, -, em⟩ := h.cw.1 y n hy
  obtain ⟨xt, hxt, -⟩ := hB.ct
  obtain ⟨xa, c, z, m, hxa, hca, hkz, hza⟩ := hB.ca hB.ni
  rw [hxt] at hxa; cases hxa
  rw [hB.cs xt hxt] at hca; cases hca
  rw [hkz] at hy0; cases hy0
  have hact : scActive y = true := by
    show activeSc y.scRefillMax = true
    rw [em]; exact hza
  have hO : Sched.OffReady q := offReady_cw hB.off h.cf h.cw
  have hbx := h.bd x hx
  rw [← et] at hx
  refine fpo_of hx hst ?_ ?_
  · intro x' c' hx' _
    rw [hx] at hx'; cases hx'
    exact ⟨x, σ0.curSc, y, n, hx, hbx, hy, hact,
      ready_of_nat (Nat.le_trans (Nat.le_add_right _ _) (hO y n (by rw [ecs]; exact hy)))⟩
  · intro x' c' hx' hc'
    rw [hx] at hx'; cases hx'
    rw [hbx] at hc'; cases hc'
    exact ⟨y, n, hy, hact⟩

/-- **An arm keeping `TB σ0 ∧ QT ct` at every `ok` outcome has `PerfF`.** -/
theorem perfF_tbq {σ0 u : State Unit} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false true oper).run u).1, ∀ a, y.1 = .ok a →
      TB σ0 y.2 ∧ QT σ0.curThread y.2) : PerfF σ0 oper u := by
  intro y hy a ha q hq
  obtain ⟨hT, x0, hx0, g0⟩ := h y hy a ha
  have hTq : TB σ0 q.2 := tb_post false a hT q hq
  obtain ⟨w, hw, hq'⟩ := hq
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  rw [hx0] at hx; cases hx
  dsimp only at hq'
  rcases g0 with e | e | e
  · rw [e] at hq'
    obtain ⟨u1, hu1, hq2⟩ := hq'
    have hS1 := sv_whenReply false _ _ y.2 u1 hu1
    have hS2 := SVK.sv_setThreadState' _ _ u1.2 q hq2
    have e1 := (hS1.trans hS2).1 σ0.curThread
    rw [hx0] at e1
    obtain ⟨x', hx', -⟩ := SVK.sv_tcb (o := q.2.kheap σ0.curThread) (a := x0.tcbSchedContext) e1
    exact fpo_tb hB hTq hx' (Or.inl (SInv.sts_post hq2 x' hx'))
  all_goals
    rw [e] at hq'
    dsimp only at hq'
    rw [Set.mem_singleton_iff.1 hq'] at hTq ⊢
    refine fpo_tb hB hTq hx0 ?_
    rw [e]
    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)

/-! ## The TCB arms -/

/-- A lifted perform keeping `TB σ0 ∧ QT ct` has `PerfF`. -/
theorem perfF_liftTQ {σ0 u : State Unit} {oper : Fl4Invocation} (m : NonDet (State Unit) (List Data))
    (he : fl4PerformInvocation (Z := Unit) false false true oper = NonDetE.liftE m) (hB : A10.BS σ0)
    (hm : IK (TB σ0) m) (hq : IK (QT σ0.curThread) m) (h0 : TB σ0 u) (hq0 : QT σ0.curThread u) :
    PerfF σ0 oper u := by
  refine perfF_tbq hB fun y hy a _ => ?_
  rw [he] at hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨hm u h0 x hx, hq u hq0 x hx⟩

/-- `QT ct` at the Restart state. -/
theorem RF.qt {σ0 u : State Unit} (h : RF σ0 u) : QT σ0.curThread u := by
  obtain ⟨x, hx⟩ := h.ct
  exact ⟨x, hx, Or.inl (h.rs x hx)⟩

/-- The `QT` walk with suspend / restart as leaves. -/
macro "qt14_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact qt_suspend _ _)
  | (with_reducible exact qt_restart _ _)
  | (with_reducible refine SInv.ik_bind ?_ (fun _ => ?_))
  | (with_reducible apply SInv.ik_when)
  | qt_auto))

/-- **`PerfF` for every arm of `CovC`.** -/
theorem perfF_covC {σ0 u : State Unit} (b : Fl4Invocation) (hc : CovC b) (h : RF σ0 u) : PerfF σ0 b u := by
  cases b
  case invokeTCB i =>
    cases i
    case suspend t =>
      exact perfF_liftTQ _ rfl h.bs (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) (by qt14_auto) h.tb h.qt
    case resume t =>
      exact perfF_liftTQ _ rfl h.bs (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) (by qt14_auto) h.tb h.qt
    case readRegisters src sus n a =>
      exact perfF_liftTQ _ rfl h.bs (tb_ik (by cfk_auto) (by cp_auto) (by bl14_auto)) (by qt14_auto) h.tb h.qt
    case writeRegisters d r v a =>
      refine perfF_liftTQ _ rfl h.bs (tb_ik ?_ ?_ ?_) ?_ h.tb h.qt <;>
        simp only [archGetSanitiseRegisterInfo, archPostModifyRegisters]
      · cfk_auto
      · cp_auto
      · bl14_auto
      · qt14_auto
    case copyRegisters d src s1 s2 f i a =>
      refine perfF_liftTQ _ rfl h.bs (tb_ik ?_ ?_ ?_) ?_ h.tb h.qt <;>
        simp only [archGetSanitiseRegisterInfo, archPostModifyRegisters]
      · cfk_auto
      · cp_auto
      · bl14_auto
      · qt14_auto
    all_goals exact hc.elim
  all_goals exact hc.elim

/-! ## `InvF` over any covered set -/

/-- Every arm in `C` has `PerfF` from the Restart state's facts. -/
def ArmF (C : Fl4Invocation → Prop) : Prop := ∀ (σ0 u : State Unit) (b : Fl4Invocation), C b → RF σ0 u → PerfF σ0 b u

theorem armF_covC : ArmF CovC := fun _ _ b hc h => perfF_covC b hc h

theorem ArmF.or {C1 C2 : Fl4Invocation → Prop} (h1 : ArmF C1) (h2 : ArmF C2) : ArmF (fun b => C1 b ∨ C2 b) :=
  fun σ0 u b hc h => hc.elim (fun c => h1 σ0 u b c h) (fun c => h2 σ0 u b c h)

/-- rd14b's `PerfFR` asking `PerfF` only outside `C`. -/
def PerfFRc (C : Fl4Invocation → Prop) (σ0 : State Unit) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ w0 ∈ (getMessageInfo (Z := Unit) σ.curThread σ).1, ∀ a s b s',
    (.ok a, s) ∈ ((invF σ.curThread cptr w0.1).run w0.2).1 →
    (.ok b, s') ∈ ((invE true cptr σ.curThread w0.1 a).run s).1 →
    ∀ u ∈ (setThreadState (Z := Unit) σ.curThread .restart s').1, C b ∨ PerfF σ0 b u.2

theorem perfFR_ofC {C : Fl4Invocation → Prop} (hA : ArmF C) {σ0 σ : State Unit} (hB : A10.BS σ0) (hS : Suff σ0)
    (hz : KZ σ0 σ) {cptr : CapRef} (h : PerfFRc C σ0 cptr σ) : PerfFR σ0 cptr σ := by
  intro w0 hw0 a s b s' ha hb u hu
  rcases h w0 hw0 a s b s' ha hb u hu with hc | hP
  · have hz0 : KZ σ0 w0.2 := kz_trans hz (kz_getMessageInfo (V := σ) _ σ rfl w0 hw0)
    have hz1 : KZ σ0 s := kz_invF _ _ _ w0.2 hz0 _ ha
    have hz2 : KZ σ0 s' := kz_trans hz1 (kz_invE _ _ _ _ a s rfl _ hb)
    have et : σ.curThread = s'.curThread := by rw [kz_curThread hz2, kz_curThread hz]
    rw [et] at hu
    exact hA σ0 u.2 b hc (rf_restart hB hS hz2 hu)
  · exact hP

/-- rd14b's `InvF` asking `PerfF` only outside `C`. -/
def InvFc (C : Fl4Invocation → Prop) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfFRc C v.2 g.1 g.2

/-- **`InvFc` gives rd14b's `InvF`.** -/
theorem invF_ofC {C : Fl4Invocation → Prop} (hA : ArmF C) {c : Syscall} {σ : State Unit} (hEF : A8.EF σ)
    (h : InvFc C c σ) : InvF c σ := by
  intro v hv ht r cr hc g hg
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  exact perfFR_ofC hA hB hS (kz_getCapReg (V := v.2) r v.2 rfl g hg) (h v hv ht r cr hc g hg)

end

end Fl4Proofs.P3.SInvR.A14c
