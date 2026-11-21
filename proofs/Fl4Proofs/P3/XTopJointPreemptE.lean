/-
P3 (DESIGN.md §9): **the preemption path's schedulable branch with a
sufficient head refill** (KENTRY-PLAN kp14, (2c) part): `check_budget`
returns `true` without a charge on both sides when the head refill can pay
the consumed time, whatever the timeout handler; XTopJointPreemptZ's
`JHole.mcsPPJZ` asked `PPCov ∨ PPCovT` only for its charging branch.

* `check_budget_suffT`: FL4's `check_budget` returns `true` at a sufficient
  head (XTopJointBudgetOk's `check_budgetT`, the other branch excluded by
  `sufficient_refines` and `getScRefillSufficient_eq`).
* `JHole.mcsPPJS`: `mcs_preemption_point` at a shifted hole with `CurInv`, a
  non-idle schedulable current thread and a sufficient head: no change, `JAt`
  by `JHole.offOK_suff` and `JHole.toJ`.
* `JPreemptRestHypE` [W]: `JPreemptRestHypS` at an insufficient head
  (narrower; `jPreemptRestHypE_of`), `hPre_ofZE`, `dispatch_invokeJPZE`,
  `dispatch_invokeJEPZE`. Left: exactly the budget check's charge with an
  endpoint timeout handler outside `PPCovT` (kp5 (i)).
-/
import Fl4Proofs.P3.XTopJointPreemptS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`check_budget` at a sufficient head returns `true`** (module docstring). -/
theorem check_budget_suffT {N T C : Set U64} {c : U64} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ) (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ σ.idleSc → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) :
    sched.check_budget st ar s a ⦃ r => r.1 = true ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  have hax : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk hax _ hmb) ?_
  intro b hb
  by_cases hbt : b = true
  · rw [if_pos hbt, is_cur_domain_expired_eq]
    simp only [bind_ok]
    exact (WP.spec_ok _).2 rfl
  · exfalso
    rw [getScRefillSufficient_eq hk (by rw [(hx.strong hax).refills]; exact refills_ne (hx.strong hax).wf)] at hb
    have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb))).1
    exact hbt (eb.symm.trans (by rw [← hs.consumed]; exact hsuf x n (by rw [hs.curSc]; exact hk)))

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` at a shifted hole with `CurInv`, a schedulable
current thread and a sufficient head** (module docstring). -/
theorem JHole.mcsPPJS {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hT : TShift σ0 σ) (hAT : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hsch : Fl4Spec.schedulable σ.curThread σ = true)
    (hsuf : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
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
    fun hy => fail_pp_sched hsch (by rw [checkBudget_suff hnd hsuf']; rfl) hy, Z, H, Cs, Ac, Lst', D, J'⟩

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CurInv` and a schedulable current thread** [W] (kp14: `JPreemptRestHypE`
with the unschedulable case proved by `JHole.mcsPPJC`). Left: kp5 (i), the
budget check's charge with an endpoint timeout handler outside `PPCovT`
(waiting receivers, a reschedule pending or the thread queued; l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`'s
`send_fault_ipc`). -/
def JPreemptRestHypE (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true →
    ¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) →
      Fl4Spec.refillSufficient σ.consumedTime (Fl4Spec.refillHd y) = true) →
    ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypE_of (h : JPreemptRestHypS (L := L) arI AR) : JPreemptRestHypE (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg hC hsc _ => h s a σ hJ hn hi hs hf hc hg hC hsc

/-- **`hPre_ofZS` with `JPreemptRestHypE`** (kp14). -/
theorem hPre_ofZE (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct, hcg⟩ :=
    jAtPre_holeL hARI.toARKeep hA hnd hP h
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
          (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hC hsc hsuf
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
/-- **`dispatch_invokeJPZS` with `JPreemptRestHypE`** (kp14). -/
theorem dispatch_invokeJPZE [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZE hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZS` with `JPreemptRestHypE`** (kp14; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZE [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZE hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
