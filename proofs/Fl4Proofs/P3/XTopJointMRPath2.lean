/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the covered preemption
path under `MachPlat`, both branches** (mr1 NEXT (a)): `MR` and
`ValidIrqMasks` from the hole to the IRQ take, ending in `PPQJI`.

* `msF_mr` / `msF_vim`: `MR` and `ValidIrqMasks` move along a spec step
  keeping MachFieldFam's `msF`.
* `JHole.mcsPPJZMF`: XTopJointPreemptZ's `mcsPPJZ` with `msF σ' = msF σ`
  added to its post (a scripted copy: the four endpoints are spec outcomes of
  `chargeBudget _ false` (`mfk_chargeBudget`), of `checkBudget` (its two
  branches, `mfk_checkBudget`) and `σ` itself).
* `JHole.mcsPPJZM`: with `MR r.2 σ'.ms ∧ ValidIrqMasks σ'` after:
  `mcsPPJZMF` combined (`WP.spec_and`) with MachKeep's FL4 walk
  `MK.syscall_mcs_preemption_point` (`MRKeep` [P] at `MR`: the arch state moves
  only by FPU/remote-stall operations keeping `MR` at the hole's machine
  state), then `MachPlat.frame`.
* `JHole.afterInvJZIM`: XTopJointIrqZI's `afterInvJZI` under `MachPlat`
  (`afterInv_of_mcsIM`): no `IrqPlat`, no `IrqPlatI`, no `PPPlat`.
-/
import Fl4Proofs.P3.XTopJointMRPath
import Fl4Proofs.P3.MachFieldFam
import Fl4Proofs.P3.SpecInvNativeScopeF4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

theorem msF_mr {A : Type} {arI : machine.Arch A} {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR)
    {a : A} {σ σ' : Fl4Spec.State Unit} (hR : MR a σ.machineState) (h : MachF.msF σ' = MachF.msF σ) :
    MR a σ'.machineState := by
  simp only [MachF.msF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2.1

theorem msF_vim {σ σ' : Fl4Spec.State Unit} (hV : ValidIrqMasks σ) (h : MachF.msF σ' = MachF.msF σ) :
    ValidIrqMasks σ' := by
  simp only [MachF.msF, Prod.mk.injEq] at h
  intro i hi
  rw [h.1]; rw [h.2.2.2.2] at hi; exact hV i hi

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`mcsPPJZ` with the spec step keeping `msF`** (module docstring). -/
theorem JHole.mcsPPJZMF {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
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
    refine ⟨σ', ?_, ?_, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl),
        fun hN => SInv.ns_chargeBudget _ _ σ hN ((), σ') (by rw [h1']; rfl)⟩
    · exact fun y hy => mem_pp_charge hs' hga (by rw [h1']; rfl) hy
    · exact fun hy => fail_pp_charge hs' hga (by rw [h1']; rfl) hy
  · simp only [↓reduceIte]
    have hs' : Fl4Spec.schedulable σ.curThread σ = true := by rw [ect]; exact hsch
    have hFT : sched.check_budget st arI s a ⦃ res => res.1 = false → ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 →
          y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR res.2.1 res.2.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
      rcases hcov with ⟨-, -, -, hnt⟩ | ⟨-, -, hres, hnq, hper, xt, p, bd, r, hkt, hrr, hth, hcb⟩
      · refine WP.spec_mono (Hh.checkBudgetF hAT hC hni hnsw hmrt hmb hnt) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨ha, σ', h1, -, Lst', J'⟩ := hF hr
        simp only at ha
        subst a'
        exact ⟨σ', fun y hy => mem_pp_sched hs' (by rw [h1]; rfl) hy,
          fun hy => fail_pp_sched hs' (by rw [h1]; rfl) hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩,
          MachF.mfk_checkBudget σ (_, σ') (by rw [h1]; rfl),
          fun hN => SInv.ns_checkBudget σ hN (_, σ') (by rw [h1]; rfl)⟩
      · refine WP.spec_mono (Hh.checkBudgetT hAT hC hni hres hnq hmrt hmb hkt hrr hth hper hcb) ?_
        rintro ⟨r, s', a'⟩ hF hr
        obtain ⟨z, hz, -, V, Ac', Lst', D', J'⟩ := hF hr
        exact ⟨z.2, fun y hy => mem_pp_sched hs' hz hy, fun hy => fail_pp_sched hs' hz hy,
          ⟨Z.mv Z.G V, H, Cs, Ac', Lst', D', J'⟩, MachF.mfk_checkBudget σ z hz, fun hN => SInv.ns_checkBudget σ hN z hz⟩
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
        fun hy => fail_pp_sched hs' (by rw [checkBudget_suff hnd hsuf]; rfl) hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, rfl, fun hN => hN⟩

/-- **`mcsPPJZ` with `MR` and `ValidIrqMasks` after** (module docstring). -/
theorem JHole.mcsPPJZM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState)
    (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  refine WP.spec_mono (WP.spec_and (Hh.mcsPPJZMF hT hAT hnd hmrt hmb hcov)
    (MK.syscall_mcs_preemption_point L.total hAT hK hR)) ?_
  rintro r ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩
  exact ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

set_option maxHeartbeats 16000000 in
/-- **The covered preemption path under `MachPlat`** (module docstring), `NativeScope` at the hole
(g3b). -/
theorem JHole.afterInvJZIMN {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hIA : IrqPlatA arI AR) (hARI : ARIface arI AR)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hN : NativeScope σ)
    (hcov : PPCov σ ∨ PPCovT σ) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ :=
  afterInv_of_mcsIMN (WP.spec_mono (Hh.mcsPPJZM hT hAT hnd hmrt hmb hcov hM hK hR hV)
    fun _ ⟨σ', h1, h2, hJ, hR', hV', hn⟩ => ⟨σ', h1, h2, hJ, hR', hV', hn hN⟩) hM hIA hARI hAT hmbA e


/-- `afterInvJZIMN` from the ∀-form `hNS` (the pre-g3b statement). -/
theorem JHole.afterInvJZIM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hIA : IrqPlatA arI AR) (hARI : ARIface arI AR)
    (hmbA : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hcov : PPCov σ ∨ PPCovT σ) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ :=
  Hh.afterInvJZIMN hT hAT hnd hmrt hmb hM hK hIA hARI hmbA (hNS s a σ ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hcov hR hV e

end

end

end Fl4Proofs.P3
