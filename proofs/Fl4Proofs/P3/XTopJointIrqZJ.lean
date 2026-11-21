/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch13): **every preemption hole
ends in `JAt` after the path, with no spec failure** (`PPQJI`).

kp17 proved the last `RestE` holes (`JPreemptRestHypC`: the current thread's
timeout fault sent to a receiver on its handler endpoint, ScChargeTR's
`JHole.mcsPPJR`; the blocking case is XTopJointPreemptA's `JHole.mcsPPJA`).
Both are `mcs_preemption_point` lemmas of the form `afterInv_of_mcsI` takes,
so with `IrqPlatI` (from `IrqPlat`, XTopJointIrqPlat `irqPlatI_of`) the
`RestE` holes end in `PPQJI` as well:

* `jPreemptRestHypEQ_ofI`: `jPreemptRestHypEQ_ofC`'s case split, ending in
  `PPQJI`.
* `hPre_ofZQI`: `hPre_ofZQ` ending in `PPQJI` (no `RestE` disjunct).
* `dispatch_invokeJAll`: the invoking dispatches ending in `PPQJI`, no
  named premise on the preemption path.
-/
import Fl4Proofs.P3.XTopJointIrqPlat
import Fl4Proofs.P3.XTopJointPreemptR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The `RestE` holes end in `PPQJI`** (module docstring;
`jPreemptRestHypEQ_ofC` with `jPreemptRestHypC_of`'s receiving case inline,
both through `afterInv_of_mcsI`). -/
theorem jPreemptRestHypEQ_ofI (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
      σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CtNQ σ →
      CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
      ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
        Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
      ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
      syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJI (L := L) arI AR σ (r.2.1, r.2.2) ⦄ := by
  intro s a σ hJ hn hi hs hf hc hg hnq hC hsc hnsuf hcov
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  have hII : IrqPlatI (L := L) arI AR := irqPlatI_of hIP
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
  · exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJA hA (hmrt a) (hP.minBudget a) hC hi hres hnq hsc hnsuf hkt
      hrr hth hper hcb) hII hARI hA hP.minBudget hNS _) fun _ h => h
  · simp only [not_forall] at hcb
    obtain ⟨xe, hke, hncb⟩ := hcb
    obtain ⟨q, rfl⟩ : ∃ q, xe = .recvEP q := by
      revert hncb; cases xe <;> simp [Endp.CanBlock]
    exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJR hA hmax htu (hmrt a) (hP.minBudget a) hC hi hres hnq hsc
      hnsuf hkt hrr hth hper ⟨q, hke⟩) hII hARI hA hP.minBudget hNS _) fun _ h => h

set_option maxHeartbeats 4000000 in
/-- **`hPre_ofZQ` ending in `PPQJI`**: every preemption hole of a related
`JAtPre` state ends in `JAt` after the path with no spec failure. -/
theorem hPre_ofZQI (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r =>
        r.1 = false ∧ PPQJI (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  have hII : IrqPlatI (L := L) arI AR := irqPlatI_of hIP
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg, hnq⟩ :=
    jAtPre_holeQ hARI.toARKeep hA hnd hP h
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZI hTs hA hnd (hmrt a1) (hP.minBudget a1) hII hARI hP.minBudget hNS hc _)
      fun _ h => h
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJI hi) hII hARI hA hP.minBudget hNS _) fun _ h => h
  by_cases hC : CurInv σ1
  · cases hsc : Fl4Spec.schedulable σ1.curThread σ1 with
    | true =>
      by_cases hsuf : ∀ y n, σ1.kheap σ1.curSc = some (.schedContext y n) →
          Fl4Spec.refillSufficient σ1.consumedTime (Fl4Spec.refillHd y) = true
      · exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJS hTs hA hnd (hP.minBudget a1) hC hni hsc hsuf)
          hII hARI hA hP.minBudget hNS _) fun _ h => h
      · exact jPreemptRestHypEQ_ofI hARI hA hP hmrt hIP hNS hmax htu s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
          (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hnq hC hsc hsuf
          fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
    | false =>
      exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJC hA (hmrt a1) (hP.minBudget a1) hC hni hns hsc)
        hII hARI hA hP.minBudget hNS _) fun _ h => h
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcsI (Hh.mcsPPJU hA (hmrt a1) (hP.minBudget a1) hC hct hfr hcg hsch hi)
      hII hARI hA hP.minBudget hNS _) fun _ h => h

set_option maxHeartbeats 4000000 in
/-- **The invoking dispatches ending in `PPQJI`** (against `fl4HandleEvent
true`'s branch; no named premise on the preemption path; the platform facts
`maxTU`/`tu` from `JEntryGlob`). -/
theorem dispatch_invokeJAll [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    fun s1 a1 σ1 h1 h2 => WP.spec_mono (hPre_ofZQI hARI hA hnd hPP hmrt hIP hNS hG.maxTU hG.tu s1 a1 σ1 h1 h2)
      fun _ h => h.2

end

end

end Fl4Proofs.P3
