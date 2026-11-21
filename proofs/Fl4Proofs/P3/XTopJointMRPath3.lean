/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the uncovered preemption
holes' MCS branches under `MachPlat`**: XTopJointPreemptE's `mcsPPJS`
(schedulable, sufficient budget: the spec state is kept), XTopJointPreemptS's
`mcsPPJC` and XTopJointPreemptM's `mcsPPJU` (not schedulable:
`chargeBudget _ false`, `mfk_chargeBudget`) with `MR r.2 σ'.ms ∧
ValidIrqMasks σ'` after. Scripted copies (scratch/mr2/mcscopy.py): the
original proof becomes a `have key` with `msF σ' = msF σ` added at its
endpoint, combined with MachKeep's FL4 walk as in XTopJointMRPath2's
`mcsPPJZM`.
-/
import Fl4Proofs.P3.XTopJointMRPath2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJS` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJSM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
    have hS := Hh.xtop.fin.1.1.1
    have hR := Hh.xtop.fin.1.1.2.2.1
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
    unfold syscall.mcs_preemption_point
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
    rw [hc.cur] at hct'
    subst hct'
    rw [schedulable_eq hR hS hc.curT] at hb
    have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
    subst hb
    rw [← ect, hsch]
    simp only [↓reduceIte]
    refine WP.spec_bind (WP.spec_and (check_budgetT hAT s a σ hS hscC hact hmb)
      (check_budget_suffT hAT s a σ hS hscC hact hmb hsuf)) ?_
    rintro ⟨r, s', a'⟩ ⟨hT', hr⟩
    simp only at hr
    subst hr
    refine (WP.spec_ok _).2 ?_
    obtain ⟨e, hsuf', hsufH⟩ := hT' rfl
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hO := Hh.offOK_suff hT hC hni hsch hsufH
    obtain ⟨Lst', J'⟩ := Hh.toJ hO (Or.inl (curOwn_of_curInv hS Hh.inv hC))
    exact ⟨σ, fun y hy => mem_pp_sched hsch (by rw [checkBudget_suff hnd hsuf']; rfl) hy,
      fun hy => fail_pp_sched hsch (by rw [checkBudget_suff hnd hsuf']; rfl) hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, rfl, fun hN => hN⟩
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJC` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJCM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hns : Vs.NoSwitch σ)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
    have hS := Hh.xtop.fin.1.1.1
    have hR := Hh.xtop.fin.1.1.2.2.1
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨hscC, -, -, -, hact, -, -⟩ := CurInv.facts hS Hh.inv hC
    have hid := curSc_ne_idleSc_of Hh.inv Hh.act hC hni
    unfold syscall.mcs_preemption_point
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
    rw [hc.cur] at hct'
    subst hct'
    rw [schedulable_eq hR hS hc.curT] at hb
    have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
    subst hb
    rw [← ect, hsch]
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with sched.cur_sc.spec' as ⟨sc, hsc⟩
    step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
    rw [hc.cur] at hsc
    subst hsc
    obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
    have hab : b1 = Fl4Spec.scActive x := by
      rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
    have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
    have hax' : Fl4Spec.scActive x = true := hact (by rw [← hs.curSc]; exact hid) x n hkx
    rw [hab, hax']
    simp only [↓reduceIte]
    step with sched.consumed.spec' as ⟨cv, hcv⟩
    rw [hc.cur] at hcv
    subst hcv
    refine WP.spec_mono (Hh.chargeBudgetJ hAT hC hni (hns σ.curThread) hmrt hmb _) ?_
    rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
    simp only at ha
    subst a'
    have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
      unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax']; rfl
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    exact ⟨σ', fun y hy => mem_pp_charge hsch hga (by rw [h1']; rfl) hy,
      fun hy => fail_pp_charge hsch hga (by rw [h1']; rfl) hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl),
        fun hN => SInv.ns_chargeBudget _ _ σ hN ((), σ') (by rw [h1']; rfl)⟩
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

set_option maxHeartbeats 16000000 in
/-- `JHole.mcsPPJU` with `MR` and `ValidIrqMasks` after (module docstring). -/
theorem JHole.mcsPPJUM {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hnc : ¬ CurInv σ) (hct : CtOK σ) (hf : CurScFree σ) (hg : Chg σ)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false) (hin : ¬ PPCovI σ)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hR : MR a σ.machineState) (hV : ValidIrqMasks σ) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧
      (NativeScope σ → NativeScope σ') ⦄ := by
  have key : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
        (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
        ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
        JAt (L := L) arI AR r.1 r.2 σ' ∧ MachF.msF σ' = MachF.msF σ ∧ (NativeScope σ → NativeScope σ') ⦄ := by
    have hax : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → Fl4Spec.scActive x = true := fun x n h => by
      cases e : Fl4Spec.scActive x with
      | true => rfl
      | false => exact (hin ⟨hsch, fun x' n' h' => by rw [h] at h'; cases h'; exact e⟩).elim
    have hS := Hh.xtop.fin.1.1.1
    have hR := Hh.xtop.fin.1.1.2.2.1
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    have hscC := Hh.curSc_in
    unfold syscall.mcs_preemption_point
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    step with Sched.sched.is_schedulable.spec' as ⟨b, hb⟩
    rw [hc.cur] at hct'
    subst hct'
    rw [schedulable_eq hR hS hc.curT] at hb
    have ect : σ.curThread = (nodeW st s Z.c layout.node.CUR_THREAD).bv := hs.curThread
    subst hb
    rw [← ect, hsch]
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with sched.cur_sc.spec' as ⟨sc, hsc⟩
    step with sporadic.sc_active.spec' as ⟨b1, hb1⟩
    rw [hc.cur] at hsc
    subst hsc
    obtain ⟨x, n, hkx, hx⟩ := hs.scs _ hscC
    have hab : b1 = Fl4Spec.scActive x := by
      rw [hb1]; show _ = decide (0 < x.scRefillMax); apply decide_eq_decide.2; rw [← hx.max]; rfl
    have hkx' : σ.kheap σ.curSc = some (.schedContext x n) := by rw [hs.curSc]; exact hkx
    have hax' : Fl4Spec.scActive x = true := hax x n hkx'
    rw [hab, hax']
    simp only [↓reduceIte]
    step with sched.consumed.spec' as ⟨cv, hcv⟩
    rw [hc.cur] at hcv
    subst hcv
    refine WP.spec_mono (Hh.chargeBudgetUJ hAT hnc hsch hct hf hg hax hmrt hmb _) ?_
    rintro ⟨s', a'⟩ ⟨ha, σ', h1, -, Lst', J'⟩
    simp only at ha
    subst a'
    have hga : Fl4Spec.getScActive (Z := Unit) σ.curSc σ = ({(true, σ)}, False) := by
      unfold Fl4Spec.getScActive Fl4Spec.NonDet.getsThe; rw [readScActive_eq' hkx', hax']; rfl
    have h1' : Fl4Spec.chargeBudget (Z := Unit) σ.consumedTime false σ = ({((), σ')}, False) := by
      rw [hs.consumed]; exact h1
    exact ⟨σ', fun y hy => mem_pp_charge hsch hga (by rw [h1']; rfl) hy,
      fun hy => fail_pp_charge hsch hga (by rw [h1']; rfl) hy, ⟨Z, H, Cs, Ac, Lst', D, J'⟩, MachF.mfk_chargeBudget _ _ σ ((), σ') (by rw [h1']; rfl),
        fun hN => SInv.ns_chargeBudget _ _ σ hN ((), σ') (by rw [h1']; rfl)⟩
  exact WP.spec_mono (WP.spec_and key (MK.syscall_mcs_preemption_point L.total hAT hK hR))
    fun _ ⟨⟨σ', h1, h2, hJ, hF, hNs⟩, hR'⟩ => ⟨σ', h1, h2, hJ, msF_mr hM hR' hF, msF_vim hV hF, hNs⟩

end

end

end Fl4Proofs.P3
