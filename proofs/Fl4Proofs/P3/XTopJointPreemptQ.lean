/-
P3 (DESIGN.md §9): **the current thread in no ready queue at a preemption
hole, proved** (KENTRY-PLAN kp16): kp15's [J] premise `JHoleCtNQHyp` (l4v
`ct_not_queued` at a hole) removed.

* ScPPR's `PPR0` carries `CtNQ` (the current thread in no ready queue) from
  the invocation's start (`JAtZ.ppr0_start` from JEntryAt's `ctnq`) through
  the deletion and reset loops: `PPK.nq` for the CNode/kernel-state/restart/
  TCB-field/scheduler steps, SpecPPRQ's `ctnq_finaliseCap` for the
  finalisations (their enqueues are the restarts of threads queued on the
  finalised endpoint or notification, blocked there, so not the current
  thread, `CtOK`). `JAtPre` holds `PPR0` at the preemption point's base;
  the preemption point keeps the queues: `jAtPre_holeQ`.
* `JPreemptRestHypEQ` [W] := XTopJointPreemptE's `JPreemptRestHypE` with an
  extra `CtNQ σ →` (narrower); `jPreemptRestHypEQ_ofC` proves it from
  XTopJointPreemptA's `JPreemptRestHypC` [W] alone (kp15's
  `jPreemptRestHypE_ofC` without `JHoleCtNQHyp`); `hPre_ofZQ`,
  `dispatch_invokeJPZA`, `dispatch_invokeJEPZA` (NEW TOP: premises as
  dispatch_invokeJEPZE with `hRC : JPreemptRestHypC` for `hRest`).
-/
import Fl4Proofs.P3.XTopJointPreemptA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`jAtPre_holeL` with `CtNQ` at the hole** (module docstring). -/
theorem jAtPre_holeQ (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    JHoleAtT (L := L) arI AR s a σ ∧ σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ ∧ CurScFree σ ∧ CtOK σ ∧
      Chg σ ∧ CtNQ σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := jAtPre_holeL hAK hA hnd hP h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  obtain ⟨s0, a0, σ0, ⟨-, -, hp00⟩, -, hσ⟩ := h
  obtain ⟨r0, -, ms0, hm0, -, -⟩ := spec_exists (hP.now a0 σ0)
  have hE := Sched.updateTimeStamp_eq' hnd hm0
  obtain ⟨r1, -, irq, ms, hIq, -, -⟩ := spec_exists (hP.irq a0
    { { { σ0 with machineState := ms0 } with curTime := r0.1.bv } with
      consumedTime := σ0.consumedTime + (r0.1.bv - σ0.curTime) })
  have e := pp_err_eq hE hIq _ hσ rfl
  subst e
  exact hp00.1.2.2.2.2

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
the current thread in no ready queue** [W] (kp16: XTopJointPreemptE's
`JPreemptRestHypE` with `CtNQ σ`, narrower). Proved from
`JPreemptRestHypC` [W] (`jPreemptRestHypEQ_ofC`). -/
def JPreemptRestHypEQ (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CtNQ σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypEQ_of (h : JPreemptRestHypE (L := L) arI AR) : JPreemptRestHypEQ (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg _ => h s a σ hJ hn hi hs hf hc hg

set_option maxHeartbeats 4000000 in
/-- **`JPreemptRestHypEQ` from `JPreemptRestHypC` [W]** (kp15's
`jPreemptRestHypE_ofC` with the unqueued current thread from the hole's
`CtNQ`): outside `PPCov`, `NoTmoSend` fails (`CurInv`, non-idle, no switch
pending), so the handler is an endpoint cap and the SC not round-robin;
`NativeScope` makes the runnable thread `Running`/`Restart`; `NoSwitch`
leaves `ResumeCurThread` or `ChooseNewThread`; an idle or sending endpoint
is `JHole.mcsPPJA`, a receiving one `JPreemptRestHypC`. -/
theorem jPreemptRestHypEQ_ofC (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRC : JPreemptRestHypC (L := L) arI AR) :
    JPreemptRestHypEQ (L := L) arI AR := by
  intro s a σ hJ hn hi hs hf hc hg hnq hC hsc hnsuf hcov
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
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
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJA hA (hmrt a) (hP.minBudget a) hC hi hres hnq hsc hnsuf hkt
      hrr hth hper hcb) hIP hIrq _) fun _ h => h.2.toPPQ
  · simp only [not_forall] at hcb
    obtain ⟨xe, hke, hncb⟩ := hcb
    obtain ⟨q, rfl⟩ : ∃ q, xe = .recvEP q := by
      revert hncb; cases xe <;> simp [Endp.CanBlock]
    exact hRC s a σ ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ hn hi hs hf hc hg hC hsc hnsuf hnq hper xt p bd r q
      hkt hrr hth hke

/-- **`hPre_ofZE` with `JPreemptRestHypEQ`** (kp16: the hole's `CtNQ` by
`jAtPre_holeQ`). -/
theorem hPre_ofZQ (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypEQ (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg, hnq⟩ :=
    jAtPre_holeQ hARI.toARKeep hA hnd hP h
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  by_cases hc : PPCov σ1 ∨ PPCovT σ1
  · exact WP.spec_mono (Hh.afterInvJZ hTs hA hnd (hmrt a1) (hP.minBudget a1) hIP hIrq hc _)
      fun _ h => h.2.toPPQ
  by_cases hi : PPCovI σ1
  · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJI hi) hIP hIrq _) fun _ h => h.2.toPPQ
  by_cases hC : CurInv σ1
  · cases hsc : Fl4Spec.schedulable σ1.curThread σ1 with
    | true =>
      by_cases hsuf : ∀ y n, σ1.kheap σ1.curSc = some (.schedContext y n) →
          Fl4Spec.refillSufficient σ1.consumedTime (Fl4Spec.refillHd y) = true
      · exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJS hTs hA hnd (hP.minBudget a1) hC hni hsc hsuf)
          hIP hIrq _) fun _ h => h.2.toPPQ
      · exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
          (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hnq hC hsc hsuf
          fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi
    | false =>
      exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJC hA (hmrt a1) (hP.minBudget a1) hC hni hns hsc)
        hIP hIrq _) fun _ h => h.2.toPPQ
  · have hsch : Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1 with
      | false => rfl
      | true => exact absurd (curInv_of_sched hct e) hC
    exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJU hA (hmrt a1) (hP.minBudget a1) hC hct hfr hcg hsch hi)
      hIP hIrq _) fun _ h => h.2.toPPQ

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZE` with `JPreemptRestHypC` [W] only** (kp16; kp15's
version also took `JHoleCtNQHyp` [J]). -/
theorem dispatch_invokeJPZA [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRC : JPreemptRestHypC (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZQ hARI hA hnd hPP hmrt hIP hNS (jPreemptRestHypEQ_ofC hARI hA hPP hmrt hIP hNS hRC))

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZE` with `JPreemptRestHypC` [W] only** (kp16; kp15's
version also took `JHoleCtNQHyp` [J]; against `fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZA [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRC : JPreemptRestHypC (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZQ hARI hA hnd hPP hmrt hIP hNS (jPreemptRestHypEQ_ofC hARI hA hPP hmrt hIP hNS hRC))

end

end

end Fl4Proofs.P3
