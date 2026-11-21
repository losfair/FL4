/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr1): **the preemption path's
non-schedulable branch with `MR`**: `mcs_preemption_point` when the current
thread is not schedulable charges the consumed time with no timeout fault
(`charge_budget c false`); FL4 keeps the arch state (`JHole.chargeBudgetJ`)
and the spec's `chargeBudget consumed false` keeps `MR`'s machine fields
(`mf_chargeBudgetF`), so `MR` holds after it and `afterInv_of_mcsJM` takes the
pending line by `MachPlat.takeAt`.

* `JHole.mcsPPJZM_ns`: XTopJointPreemptZ's `mcsPPJZ` (covered holes) for a
  non-schedulable current thread, with `MR r.2 σ'.ms` after (an adapted copy of
  its first branch: the original's post hides the arch equality).
* `JHole.afterInvJZJM_ns`: `after_invocation (Err)` from such a hole under
  `MachPlat` + `MR a σ.ms`, ending in `PPQJ`, no `IrqPlat.take`.
* `JAtPreM`: `JAtPre` with `MR` + `ValidMachineTime` at the preemption point's
  pre-state; `jAtPreM_hole`: such a state is a `JHole` with `MR` and
  `ValidMachineTime` (`JAtZ.ppJHM`), the start of the MR-threaded preemption
  path.
-/
import Fl4Proofs.P3.XTopJointMRPP
import Fl4Proofs.P3.MachFieldKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`mcsPPJZ` for a non-schedulable current thread, with `MR` after**
(module docstring). -/
theorem JHole.mcsPPJZM_ns {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) (hsch : Fl4Spec.schedulable σ.curThread σ = false)
    (hM : MachPlat arI MR) (hMR : MR a σ.machineState) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ⦄ := by
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
  have hsch2 : Fl4Spec.schedulable (nodeW st s Z.c layout.node.CUR_THREAD).bv σ = false := by
    rw [← ect]; exact hsch
  rw [hsch2]
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
    have hs' : Fl4Spec.schedulable σ.curThread σ = false := hsch
    refine ⟨σ', ?_, ?_, ⟨Z, H, Cs, Ac, Lst', D, J'⟩,
      hM.mfKeep hMR (Sched.MFA.of_eq (Sched.mf_chargeBudgetF _) h1')⟩
    · exact fun y hy => mem_pp_charge hs' hga (by rw [h1']; rfl) hy
    · exact fun hy => fail_pp_charge hs' hga (by rw [h1']; rfl) hy

set_option maxHeartbeats 16000000 in
/-- **The preemption path from a covered hole with a non-schedulable current
thread under `MachPlat`** (module docstring). -/
theorem JHole.afterInvJZJM_ns {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hcov : PPCov σ ∨ PPCovT σ) (hsch : Fl4Spec.schedulable σ.curThread σ = false)
    (hM : MachPlat arI MR) (hMR : MR a σ.machineState) (hIA : IrqPlatA arI AR)
    (hIrq : JIrqHypJ (L := L) arI AR) (e : error.Exc) :
    syscall.after_invocation st arI s a (.Err e) ⦃ r => r.1 = false ∧ PPQJ (L := L) arI AR σ (r.2.1, r.2.2) ⦄ :=
  afterInv_of_mcsJM (Hh.mcsPPJZM_ns hT hAT hnd hmrt hmb hcov hsch hM hMR) hM hIA hIrq e


variable (arI) in
/-- **`JAtPre` with `MR` at the preemption point's pre-state** (mr1): the
interface the invocations' preemption points must produce once `MR` is
threaded through them (KENTRY-PLAN mr1 NEXT): `MR a0 σ0.ms` and
`ValidMachineTime σ0` where the preempting `preemption_point` starts. -/
def JAtPreM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit),
    (JAt (L := L) arI AR s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0 ∧ MR a0 σ0.machineState ∧ ValidMachineTime σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1

theorem JAtPreM.toPre {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreM (L := L) arI AR MR s a σ) :
    JAtPre (L := L) arI AR s a σ :=
  by
  obtain ⟨s0, a0, σ0, ⟨hJ, hns, hp, -, -⟩, hpp, hσ⟩ := h
  exact ⟨s0, a0, σ0, ⟨hJ, hns, hp⟩, hpp, hσ⟩

/-- **Every `JAtPreM` state is a `JHole` with `MR` and `ValidMachineTime`**
(`JAtZ.ppJHM`; XTopJointPPH's `jAtPre_hole` under `MachPlat`). -/
theorem jAtPreM_hole (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hPA : PPPlatA arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JAtPreM (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s0 : S) (a0 : A)
      (σ0 : Fl4Spec.State Unit), JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ ∧
        MR a σ.machineState ∧ ValidMachineTime σ := by
  obtain ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, -, -, hR, hV⟩, hpp, hσ⟩ := h
  have h := J.ppJHM hAK hA hnd hM hPA hR hV
  rw [hpp, WP.spec_ok] at h
  obtain ⟨s1, Ac1, Lst1, Hh, hR', hV'⟩ := h rfl σ hσ
  exact ⟨Z, H, Cs, Ac1, Lst1, D, s1, a0, σ0, Hh, hR', hV'⟩

end

end

end Fl4Proofs.P3
