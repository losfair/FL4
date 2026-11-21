/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr3, mr2 NEXT (a)): **every
preemption hole of a `JAtPreMV` state ends in `PPQJI` under `MachPlat`**, with
no `PPPlat` / `IrqPlat` / `IrqPlatI`.

* `JAtPreMV AR MR`: mr1's `JAtPreM` (`JAtPre` with `MR a0 σ0.ms` and
  `ValidMachineTime σ0` at the preempting preemption point's pre-state) with
  `ValidIrqMasks σ0` [J] there as well (mr2). `JAtPreMV.toM`, `.toPre`.
* `jAtPreMV_holeQ`: XTopJointPreemptQ's `jAtPre_holeQ` chain (holeT/TN/O/K/L/Q)
  under `MachPlat`: the hole from mr1's `JAtZ.ppJHM` (MR and VMT after); the
  spec outcome named by the deterministic reads (`getCurrentTime_eq`,
  `getActiveIRQ_eq`, `pp_err_eq`) instead of `PPPlat.now/irq`; `TShift`'s
  clock monotonicity from `vmt_le_gct` (VMT at the base); `ValidIrqMasks` at
  the hole because the preemption point keeps `interruptStates` and the masks
  (`gctState`/`gaiState` move only the oracle positions and the last time).
* `jPreemptRestHypEQ_ofIM`: XTopJointIrqZJ's `jPreemptRestHypEQ_ofI` with
  mr2's `mcsPPJAM` / `mcsPPJRM` and `afterInv_of_mcsIM`.
* `hPre_ofZQIM`: `hPre_ofZQI` for `JAtPreMV`, every branch through
  `afterInvJZIM` / `afterInv_of_mcsIM ∘ mcsPPJ{I,S,C,U}M`.
Platform premises: `MachPlat` [P], `MRKeep` [P] (arch-only), `PPPlatA` [P],
`IrqPlatA` [P] (arch-only); all satisfied by `modelArch` for the MR part.
-/
import Fl4Proofs.P3.XTopJointMRPath4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **`JAtPreM` with `ValidIrqMasks` [J] at the preemption point's pre-state**
(module docstring; l4v `valid_irq_masks`, part of `invs`). -/
def JAtPreMV (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit),
    (JAt (L := L) arI AR s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0 ∧ MR a0 σ0.machineState ∧ ValidMachineTime σ0 ∧
      ValidIrqMasks σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1

theorem JAtPreMV.toM {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreMV (L := L) arI AR MR s a σ) :
    JAtPreM (L := L) arI AR MR s a σ := by
  obtain ⟨s0, a0, σ0, ⟨hJ, hns, hp, hR, hV, -⟩, hpp, hσ⟩ := h
  exact ⟨s0, a0, σ0, ⟨hJ, hns, hp, hR, hV⟩, hpp, hσ⟩

theorem JAtPreMV.toPre {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreMV (L := L) arI AR MR s a σ) :
    JAtPre (L := L) arI AR s a σ :=
  h.toM.toPre

/-- **`jAtPre_holeQ` under `MachPlat`**, with `MR`, `ValidMachineTime` and
`ValidIrqMasks` at the hole (module docstring). -/
theorem jAtPreMV_holeQ (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hPA : PPPlatA arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JAtPreMV (L := L) arI AR MR s a σ) :
    JHoleAtT (L := L) arI AR s a σ ∧ σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ ∧ CurScFree σ ∧ CtOK σ ∧
      Chg σ ∧ CtNQ σ ∧ MR a σ.machineState ∧ ValidMachineTime σ ∧ ValidIrqMasks σ := by
  obtain ⟨s0, a0, σ0, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hns0, hp00, hR0, hV0, hI0⟩, hpp, hσ⟩ := h
  have h := J.ppJHM hAK hA hnd hM hPA hR0 hV0
  rw [hpp, WP.spec_ok] at h
  obtain ⟨s1, Ac1, Lst1, Hh, hR', hV'⟩ := h rfl σ hσ
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  have e : σ = _ := pp_err_eq hE (doMachineOp_single (getActiveIRQ_eq true _)) _ hσ rfl
  subst e
  have h0 : CurScFree σ0 := curScFree_of J.inv J.own hp00
  refine ⟨⟨Z, H, Cs, Ac1, Lst1, D, s1, a0, σ0, Hh, vmt_le_gct hV0, rfl⟩, hp00.1.1, hns0,
    fun u xt hu hs => h0 u xt hu hs, hp00.1.2.2.1, hp00.1.2.2.2.1, hp00.1.2.2.2.2, hR', hV', ?_⟩
  intro i hi
  exact hI0 i hi

/-- An MCS part's post with `NativeScope σ → NativeScope σ'` at a `NativeScope`
hole (g3b). -/
theorem mcsNS {s : S} {a : A} {σ : Fl4Spec.State Unit} (hN : NativeScope σ)
    (h : syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ (NativeScope σ → NativeScope σ') ⦄) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧ ValidIrqMasks σ' ∧ NativeScope σ' ⦄ :=
  WP.spec_mono h fun _ ⟨σ', h1, h2, hJ, hR', hV', hn⟩ => ⟨σ', h1, h2, hJ, hR', hV', hn hN⟩

set_option maxHeartbeats 4000000 in
/-- **`jPreemptRestHypEQ_ofI` under `MachPlat`** (module docstring); `NativeScope` at the hole only (g3b). -/
theorem jPreemptRestHypEQ_ofIM (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
      MR a σ.machineState → ValidIrqMasks σ →
      σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CtNQ σ →
      CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
      ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
        Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
      ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
      syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  intro s a σ hJ hn hR hV hi hs hf hc hg hnq hC hsc hnsuf hcov
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  have hnt : ¬ NoTmoSend σ := fun h => hcov (Or.inl ⟨hC, hi, hs σ.curThread, h⟩)
  unfold NoTmoSend at hnt
  simp only [not_or, not_forall] at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨x0, n0, hk0, hp0⟩⟩ := hnt
  have hper : ∀ x n, σ.kheap σ.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := by
    intro x n hk; rw [hk0] at hk; cases hk; exact hp0
  obtain ⟨p, bd, r, hth⟩ : ∃ p bd r, xt.tcbTimeoutHandler = .endpointCap p bd r := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    obtain ⟨x1, -, -, -, hk1, -, hr1, -, -, -⟩ := schedulable_inv hsc
    rw [hkt] at hk1; cases hk1
    have hvm := hn _ _ hkt
    revert hr1 hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  have hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread := by
    rcases e : σ.schedulerAction with _ | u | _
    · exact Or.inl rfl
    · exact absurd e (hs u)
    · exact Or.inr rfl
  by_cases hcb : ∀ xe, σ.kheap p = some (.endpoint xe) → Endp.CanBlock false xe
  · exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hn (Hh.mcsPPJAM hA (hmrt a) (hPA.minBudget a) hC hi hres hnq hsc hnsuf hkt
      hrr hth hper hcb hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h
  · simp only [not_forall] at hcb
    obtain ⟨xe, hke, hncb⟩ := hcb
    obtain ⟨q, rfl⟩ : ∃ q, xe = .recvEP q := by
      revert hncb; cases xe <;> simp [Endp.CanBlock]
    exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hn (Hh.mcsPPJRM hA hmax htu (hmrt a) (hPA.minBudget a) hC hi hres hnq hsc
      hnsuf hkt hrr hth hper ⟨q, hke⟩ hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h

set_option maxHeartbeats 4000000 in
/-- **`hPre_ofZQI` under `MachPlat`**: every preemption hole of a related
`JAtPreMV` state ends in `JAt` after the path with no spec failure, with no
`PPPlat`/`IrqPlat` (module docstring), `NativeScope` at the
`JAtPreMV` state only (g3b). -/
theorem hPre_ofZQIMN (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 → NativeScope σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJI (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h hN1
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg, hnq, hR, -, hV⟩ :=
    jAtPreMV_holeQ hARI.toARKeep hA hnd hM hPA h
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZIMN hTs hA hnd (hmrt a1) (hPA.minBudget a1) hM hK hIA hARI hPA.minBudget hN1
      hc hR hV _) fun _ h => h
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hN1 (Hh.mcsPPJIM hi hA hM hK hR hV)) hM hIA hARI hA hPA.minBudget _)
      fun _ h => h
  by_cases hC : CurInv σ1
  · cases hsc : Fl4Spec.schedulable σ1.curThread σ1 with
    | true =>
      by_cases hsuf : ∀ y n, σ1.kheap σ1.curSc = some (.schedContext y n) →
          Fl4Spec.refillSufficient σ1.consumedTime (Fl4Spec.refillHd y) = true
      · exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hN1 (Hh.mcsPPJSM hTs hA hnd (hPA.minBudget a1) hC hni hsc hsuf hM hK hR hV))
          hM hIA hARI hA hPA.minBudget _) fun _ h => h
      · exact jPreemptRestHypEQ_ofIM hARI hA hM hK hPA hIA hmrt hmax htu s1 a1 σ1
          ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
          hN1 hR hV hni hns hfr hct hcg hnq hC hsc hsuf
          fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
    | false =>
      exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hN1 (Hh.mcsPPJCM hA (hmrt a1) (hPA.minBudget a1) hC hni hns hsc hM hK hR hV))
        hM hIA hARI hA hPA.minBudget _) fun _ h => h
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcsIMN (mcsNS hN1 (Hh.mcsPPJUM hA (hmrt a1) (hPA.minBudget a1) hC hct hfr hcg hsch hi
      hM hK hR hV)) hM hIA hARI hA hPA.minBudget _) fun _ h => h

/-- `hPre_ofZQIMN` from the ∀-form `hNS` (the pre-g3b statement). -/
theorem hPre_ofZQIM (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hM : MachPlat arI MR) (hK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPreMV (L := L) arI AR MR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJI (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 hr h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, -⟩, -⟩ := jAtPreMV_holeQ hARI.toARKeep hA hnd hM hPA h
  exact hPre_ofZQIMN hARI hA hnd hM hK hPA hIA hmrt hmax htu s1 a1 σ1 hr h
    (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩)

end

end

end Fl4Proofs.P3
