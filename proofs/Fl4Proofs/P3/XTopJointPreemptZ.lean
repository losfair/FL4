/-
P3 (DESIGN.md §9): **the preemption path at `J` ending at `JAtZ`**
(KENTRY-PLAN kp8, item 7): XTopJointIrq's `JIrqSigHyp` [W] deleted.

kp7 found that only the sufficient-budget branch of `mcs_preemption_point`
reaches `check_interrupt` at a hole that is not `JAtZ`: there `OffOK` needs
l4v's `cur_sc_offset_ready` at the hole. It holds at every hole the
invocation can leave, by the time shift of the preemption point's time
update, without carrying anything through the invocation:

* `TShift σ0 σ`: the hole's time and consumed time are the base's moved by
  the same elapsed time (`update_time_stamp`: `cur_time := now`,
  `consumed_time += now - cur_time`, time not going back).
* `jAtPre_holeT`: every `JAtPre` state is a `JHole` with `TShift` from its
  base (a preempting `preemption_point`: `pp_err_eq`, `updateTimeStamp_eq'`
  and `NowAgree` [P]); `jAtPre_holeTN` also gives the base's no-switch and
  non-idle facts at the hole (kp10).
* `JHole.offOK_suff`: at such a hole with `CurInv`, a non-idle schedulable
  current thread and a sufficient head, `OffOK` holds. The base is `JAtZ`:
  for a positive consumed time its `OffOK` gives the head ready with it, for
  a zero one `Inv.rd` of the (runnable, bound, unreleased) current thread
  gives the head released (l4v `valid_sched`'s `released_sc` of a
  schedulable thread = `cur_sc_offset_ready 0`); XTopJointPP's `rdy_shift`
  moves both to the hole.
* `JHole.mcsPPJZ`: XTopJointPreempt's `JHole.mcsPPJ` with `JAt` after in
  every branch (the sufficient one by `JHole.toJ` with `offOK_suff` and
  `curOwn_of_curInv`; the charge branches were `JAtZ` already).
* `JAtZ.msArJ` (another machine state with the same memory and an arch
  state keeping `AR`), `jIrqHypZ_of`: `handle_interrupt` from a `JAt` state
  (XTopJointIrq's `JHole.handleIrqJ` over `JAtZ.toHole`; its signal premise
  is vacuous there: `JAtZ.off`, `JAtZ.own`).
* `JHole.afterInvJZ`: `after_invocation (Err _)` from a `JHole` with
  `TShift` under `PPCov ∨ PPCovT` refines `preemption_path` with `PPQZ`
  after: the spec fails, or an outcome with `JAt` after (no line pending:
  the post-budget-check state is `JAtZ`, for schedule at J, M7) or `XTopAt`
  after a handled line. `PPQZ.toPPQ`.
* `hPre_ofZ` / `dispatch_invokeJPZ` / `dispatch_invokeJEPZ`: XTopJointIrq's
  `hPre_ofI` / `dispatch_invokeJPI` / `dispatch_invokeJEPI` without
  `JIrqSigHyp` (remaining: `IrqPlat`, `PPPlat` [P], `hNS` [S],
  `JPreemptRestHypN` [W], as there).
-/
import Fl4Proofs.P3.XTopJointIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The hole's time words are the base's moved by the elapsed time**
(module docstring). -/
def TShift (σ0 σ : Fl4Spec.State Unit) : Prop :=
  σ0.curTime ≤ σ.curTime ∧ σ.consumedTime = σ0.consumedTime + (σ.curTime - σ0.curTime)

theorem TShift.refl (σ : Fl4Spec.State Unit) : TShift σ σ :=
  ⟨BitVec.le_refl _, by rw [BitVec.sub_self, BitVec.add_zero]⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

variable (arI) in
/-- Some `JHole` with `TShift` from its base ends at `(s, a, σ)`. -/
def JHoleAtT (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
    (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ ∧ TShift σ0 σ

theorem JHoleAtT.hole {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JHoleAtT (L := L) arI AR s a σ) :
    JHoleAt (L := L) arI AR s a σ :=
  let ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, _⟩ := h; ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩

/-- **`jAtPre_holeT` with the base's no-switch and non-idle facts at the
hole** (kp10: the preemption point changes neither the action nor the
current and idle threads, `pp_err_eq`). -/
theorem jAtPre_holeTN (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    JHoleAtT (L := L) arI AR s a σ ∧ σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ := by
  obtain ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hns0, hp00⟩, hpp, hσ⟩ := h
  have h := J.ppJH hAK hA hnd hP
  rw [hpp, WP.spec_ok] at h
  obtain ⟨s1, Ac1, Lst1, Hh⟩ := h rfl σ hσ
  obtain ⟨r0, -, ms0, hm0, hle0, -⟩ := spec_exists (hP.now a0 σ0)
  have hE := Sched.updateTimeStamp_eq' hnd hm0
  obtain ⟨r1, -, irq, ms, hIq, -, -⟩ := spec_exists (hP.irq a0
    { { { σ0 with machineState := ms0 } with curTime := r0.1.bv } with
      consumedTime := σ0.consumedTime + (r0.1.bv - σ0.curTime) })
  have e := pp_err_eq hE hIq _ hσ rfl
  subst e
  exact ⟨⟨Z, H, Cs, Ac1, Lst1, D, s1, a0, σ0, Hh, hle0, rfl⟩, hp00.1.1, hns0⟩

/-- **Every `JAtPre` state is a `JHole` with `TShift`** (module docstring). -/
theorem jAtPre_holeT (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    JHoleAtT (L := L) arI AR s a σ :=
  (jAtPre_holeTN hAK hA hnd hP h).1

/-- **`OffOK` at a shifted hole with a sufficient head** (module docstring). -/
theorem JHole.offOK_suff {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hC : CurInv σ)
    (hni : σ.curThread ≠ σ.idleThread) (hs : Fl4Spec.schedulable σ.curThread σ = true)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) : OffOK σ := by
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  have J := Hh.j0
  obtain ⟨xt, hkt, hxs, -⟩ := hC.tcb
  obtain ⟨x, scp, y', n', hkx, -, hrun, -, -, -⟩ := schedulable_inv hs
  rw [hkt] at hkx; cases hkx
  obtain ⟨ms, t, c, -, e⟩ := Hh.spec
  subst e
  intro _ y n hy _
  have hact := hC.active hid y n hy
  have hrd : (Fl4Spec.refillHd y).rTime + σ0.consumedTime ≤ σ0.curTime ∧
      (Fl4Spec.refillHd y).rTime ≤ σ0.curTime := by
    by_cases h0 : σ0.consumedTime = 0
    · have h := (J.inv.rd σ0.curThread xt hkt (Or.inl hrun) xt σ0.curSc y n hkt hxs hy hact hC.notRel).1
      simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h
      rw [h0, bv_add0]; exact ⟨h, h⟩
    · obtain ⟨-, h1, h2⟩ := J.off (bv_pos h0) y n hy (fun _ => hact)
      simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0] at h1 h2
      exact ⟨h1, h2⟩
  obtain ⟨hs1, hs2⟩ := rdy_shift hrd.1 hrd.2 hT.1
  refine ⟨hsuf y n hy, ?_, ?_⟩
  · simp only [Fl4Spec.refillReady', decide_eq_true_eq]
    show (Fl4Spec.refillHd y).rTime + c ≤ t
    rw [show c = σ0.consumedTime + (t - σ0.curTime) from hT.2]; exact hs1
  · simp only [Fl4Spec.refillReady, Fl4Spec.refillReady', decide_eq_true_eq, bv_add0]; exact hs2

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` from a shifted `JHole`, `JAt` after** (module
docstring). -/
theorem JHole.mcsPPJZ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
  obtain ⟨hC, hni, hnsw⟩ : CurInv σ ∧ σ.curThread ≠ σ.idleThread ∧
      σ.schedulerAction ≠ .switchThread σ.curThread := by
    rcases hcov with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, by rw [h3]; exact fun h => by cases h⟩
  have hS := Hh.xtop.fin.1.1.1
  have hR := Hh.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
  have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
  unfold syscall.mcs_preemption_point
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
  rw [hc.cur] at hct
  subst hct
  rw [schedulable_eq hR hS hc.curT] at hb
  have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
  subst hb
  cases hsch : Fl4Spec.schedulable (nodeW st s Z.c layout.node.CUR_THREAD).bv σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    step with sched.cur_sc.spec' as ⟨sc, hsc⟩
    step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
    rw [hc.cur] at hsc
    subst hsc
    obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
    have hab : b1 = Fl4Spec.scActive x := by
      rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
    have hax : Fl4Spec.scActive x = true := hact (by rw [← hs.curSc]; exact hid) x n hkx
    rw [hab, hax]
    simp only [↓reduceIte]
    step with sched.consumed.spec' as ⟨cv, hcv⟩
    rw [hc.cur] at hcv
    subst hcv
    refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni hnsw hmrt hmb _) ?_
    rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
    simp only at ha
    subst a'
    have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
    have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
      unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax]; rfl
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    have hs' : Fl4Spec.schedulable σ.curThread σ = false := by rw [ect]; exact hsch
    refine ⟨σ', ?_, ?_, Z, H, Cs, Ac, Lst', D, J'⟩
    · exact fun y hy => mem_pp_charge hs' hga (by rw [h1']; rfl) hy
    · exact fun hy => fail_pp_charge hs' hga (by rw [h1']; rfl) hy
  · simp only [↓reduceIte]
    have hs' : Fl4Spec.schedulable σ.curThread σ = true := by rw [ect]; exact hsch
    have hFT : sched.check_budget st arI s a ⦃ res => res.1 = false → ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 →
          y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR res.2.1 res.2.2 σ' ⦄ := by
      rcases hcov with ⟨-, -, -, hnt⟩ | ⟨-, -, hres, hnq, hper, xt, p, bd, r, hkt, hrr, hth, hcb⟩
      · refine WP.spec_mono (Hh.checkBudgetF hAT hC hni hnsw hmrt hmb hnt) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨ha, σ', h1, -, Lst', J'⟩ := hF hr
        simp only at ha
        subst a'
        exact ⟨σ', fun y hy => mem_pp_sched hs' (by rw [h1]; rfl) hy,
          fun hy => fail_pp_sched hs' (by rw [h1]; rfl) hy, Z, H, Cs, Ac, Lst', D, J'⟩
      · refine WP.spec_mono (Hh.checkBudgetT hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF hr
        exact ⟨z.2, fun y hy => mem_pp_sched hs' hz hy, fun hy => fail_pp_sched hs' hz hy,
          Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb) hFT) ?_
    rintro ⟨r, s', a'⟩ ⟨hT', hF⟩
    refine (WP.spec_ok _).2 ?_
    cases r
    · exact hF rfl
    · obtain ⟨e, hsuf, hsufH⟩ := hT' rfl
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hO := Hh.offOK_suff hT hC hni hs' hsufH
      obtain ⟨Lst', J'⟩ := Hh.toJ hO (Or.inl (curOwn_of_curInv hS Hh.inv hC))
      exact ⟨σ, fun y hy => mem_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy,
        fun hy => fail_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy, Z, H, Cs, Ac, Lst', D, J'⟩

/-- **A `JAtZ` state at another machine state (same memory) and arch state
keeping `AR`** (the IRQ check). -/
theorem JAtZ.msArJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (ms : Fl4Spec.MachineState) (a' : A)
    (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a σ.archState.x64CurrentCr3 → AR a' σ.archState.x64CurrentCr3) :
    ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s a' { σ with machineState := ms } :=
  (J.toHole.msAr ms a' hum hAR).toJ J.off J.own

variable (arI) in
/-- **`handle_interrupt` at `J` from a `JAt` state** (`JIrqHyp` there). -/
def JIrqHypZ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄

/-- **`JIrqHypZ` from the platform facts alone** (module docstring). -/
theorem jIrqHypZ_of (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    JIrqHypZ (L := L) arI AR := by
  intro s a σ w i hJ hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.toHole.handleIrqJ hARI hAT hIP hmb hNS (fun hO => absurd ⟨J.off, J.own⟩ hO) w i hwi h126 h127

/-- **`JIrqHypZ` per state** (g3e): at every `JAt` state with `NativeScope`
there, no ∀-form `hNS`. -/
theorem jIrqHypZ_ofN (hARI : ARIface arI AR) (hAT : P0.ArchTotal arI) (hIP : IrqPlat arI AR)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (w : U64) (i : Fl4Spec.Irq),
    JAt (L := L) arI AR s a σ → NativeScope σ → w.val = i.toNat → σ.machineState.irqMasks i = false →
    w.val ≠ 126 → w.val ≠ 127 →
    interrupt.handle_interrupt st arI s a w ⦃ r =>
      (Fl4Spec.handleInterrupt (Z := Unit) i σ).2 ∨
        ∃ z ∈ (Fl4Spec.handleInterrupt (Z := Unit) i σ).1, ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2 ⦄ := by
  intro s a σ w i hJ hN hwi _ h126 h127
  obtain ⟨Z, H, Cs, Ac, Lst, D, J⟩ := hJ
  exact J.toHole.handleIrqJN hARI hAT hIP hmb hN (fun hO => absurd ⟨J.off, J.own⟩ hO) w i hwi h126 h127

variable (arI) in
/-- What the covered preemption path ends in: a spec failure, or an outcome
of `preemption_path` from `σ1` with `JAt` after (no line pending) or `XTopAt`
after (a handled line). -/
def PPQZ (AR : A → Fl4Spec.Cr3 → Prop) (σ1 : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1,
    JAt (L := L) arI AR r.1 r.2 z.2 ∨ ∃ Z', XTopAt (L := L) AR Z' r.1 r.2 z.2

theorem PPQZ.toPPQ {σ1 : Fl4Spec.State Unit} {r : S × A} (h : PPQZ (L := L) arI AR σ1 r) :
    PPQ (L := L) arI AR σ1 r := by
  rcases h with h | ⟨z, hz, ⟨Z, H, Cs, Ac, Lst, D, J⟩ | h⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, hz, Or.inl ⟨Z, H, Cs, Ac, Lst, D, _, _, _, J.toHole⟩⟩
  · exact Or.inr ⟨z, hz, Or.inr h⟩

set_option maxHeartbeats 16000000 in
/-- **`after_invocation (Err _)` from a shifted `JHole`, `JAt` after when no
line is pending** (module docstring). -/
theorem JHole.afterInvJZ {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR) (hIrq : JIrqHypZ (L := L) arI AR) (hcov : PPCov σ ∨ PPCovT σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQZ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  unfold syscall.after_invocation
  refine WP.spec_bind (Hh.mcsPPJZ hT hAT hnd hmrt hmb hcov) ?_
  rintro ⟨s1, a1⟩ ⟨σ', hm, hmf, Z', H', Cs', Ac', Lst', D', J'⟩
  have hAR1 : AR a1 σ'.archState.x64CurrentCr3 := J'.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_bind (WP.spec_and (WP.spec_and (hIP.take a1 σ') (hIP.takeAR a1 _ hAR1)) (hIP.noIpi a1)) ?_
  rintro ⟨w, a2⟩ ⟨⟨⟨irq, ms, hIq, hnone, hsome, hum⟩, hAR2⟩, h126, h127⟩
  obtain ⟨Lst2, J2⟩ := J'.msArJ ms a2 hum (fun _ => hAR2)
  unfold syscall.check_interrupt
  by_cases hw : w = syscall.NO_IRQ
  · have hirq : irq = none := hnone.1 hw
    subst hirq
    have e : (w != syscall.NO_IRQ) = false := by simp [hw]
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨((), { σ' with machineState := ms }),
      hm _ (mem_maybeHandle_none hIq), Or.inl ⟨Z', H', Cs', Ac', Lst2, D', J2⟩⟩⟩
  · obtain ⟨i, rfl⟩ : ∃ i, irq = some i := by
      cases irq with
      | none => exact absurd (hnone.2 rfl) hw
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hwi, hmask⟩ := hsome i rfl
    have e : (w != syscall.NO_IRQ) = true := by simpa using hw
    show (do
      let (s2, a3) ← (if (w != syscall.NO_IRQ) = true then interrupt.handle_interrupt st arI s1 a2 w else ok (s1, a2))
      ok (false, s2, a3)) ⦃ _ ⦄
    rw [e]
    simp only [↓reduceIte]
    refine WP.spec_bind (hIrq s1 a2 _ w i ⟨Z', H', Cs', Ac', Lst2, D', J2⟩ hwi hmask h126 h127) ?_
    rintro ⟨s2, a3⟩ (hf | ⟨z, hz, hJ⟩)
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inl (hmf (fail_maybeHandle_some hIq hf))⟩
    · exact (WP.spec_ok _).2 ⟨rfl, Or.inr ⟨z, hm _ (mem_maybeHandle_some hIq hz), Or.inr hJ⟩⟩

/-- **`invoke_afterJ`'s `hPre` without `JIrqSigHyp`** (module docstring). -/
theorem hPre_ofZ (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypN (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  have hT := jAtPre_holeT hARI.toARKeep hA hnd hP h
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩ := hT
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP
      (jIrqHypZ_of hARI hA hIP hP.minBudget hNS) hc _) fun _ h => h.2.toPPQ
  · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hc

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPI` without `JIrqSigHyp`**. -/
theorem dispatch_invokeJPZ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypN (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZ hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPI` without `JIrqSigHyp`** (against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZ [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypN (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZ hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
