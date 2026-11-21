/-
P3 (DESIGN.md §9): **the preemption path's charge of an unschedulable
current thread with `CurInv`** (KENTRY-PLAN kp14, (2c) part): FL4's
`mcs_preemption_point` and the spec's `preemption_path` charge with
`can_timeout_fault = false` when the current thread is not schedulable, so
an endpoint timeout handler (¬`NoTmoSend`) does not matter there:
XTopJointPreempt's `JHole.mcsPPJ` asks `PPCov` (incl. `NoTmoSend`) only for
the schedulable branch.

* `JHole.mcsPPJC`: that branch with `CurInv`, a non-idle current thread and
  no switch pending (ScChargeH's `JHole.chargeBudgetJ`), `JAt` after.
* `JPreemptRestHypS` [W]: `JPreemptRestHypM` at a schedulable current thread
  (narrower; `jPreemptRestHypS_of`), `hPre_ofZS`, `dispatch_invokeJPZS`,
  `dispatch_invokeJEPZS`. Left: the schedulable branch's budget check with an
  endpoint timeout handler outside `PPCovT` (kp5 (i)).
-/
import Fl4Proofs.P3.XTopJointPreemptM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`mcs_preemption_point` at a hole with `CurInv` and an unschedulable
current thread** (module docstring; XTopJointPreempt's `JHole.mcsPPJ` charge
branch without `NoTmoSend`, `JAt` after). -/
theorem JHole.mcsPPJC {s0 : S} {a0 : A} {σ0 : Fl4Spec.State Unit} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (Hh : JHole (L := L) arI AR Z H Cs Ac Lst D s0 a0 σ0 s a σ) (hAT : P0.ArchTotal arI)
    (hmrt : sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hC : CurInv σ) (hni : σ.curThread ≠ σ.idleThread) (hns : Vs.NoSwitch σ)
    (hsch : Fl4Spec.schedulable σ.curThread σ = false) :
    syscall.mcs_preemption_point st arI s a ⦃ r => ∃ σ',
      (∀ y, y ∈ (Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').1 → y ∈ (Fl4Spec.preemptionPath (Z := Unit) σ).1) ∧
      ((Fl4Spec.maybeHandleInterrupt (Z := Unit) true σ').2 → (Fl4Spec.preemptionPath (Z := Unit) σ).2) ∧
      JAt (L := L) arI AR r.1 r.2 σ' ⦄ := by
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
    fun hy => fail_pp_charge hsch hga (by rw [h1']; rfl) hy, Z, H, Cs, Ac, Lst', D, J'⟩

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CurInv` and a schedulable current thread** [W] (kp14: `JPreemptRestHypS`
with the unschedulable case proved by `JHole.mcsPPJC`). Left: kp5 (i), the
budget check's charge with an endpoint timeout handler outside `PPCovT`
(waiting receivers, a reschedule pending or the thread queued; l4v
`check_budget`'s `charge_budget … True` → `end_timeslice` → `handle_timeout`'s
`send_fault_ipc`). -/
def JPreemptRestHypS (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    CurInv σ → Fl4Spec.schedulable σ.curThread σ = true → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypS_of (h : JPreemptRestHypM (L := L) arI AR) : JPreemptRestHypS (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc hg hC _ => h s a σ hJ hn hi hs hf hc hg hC

/-- **`hPre_ofZM` with `JPreemptRestHypS`** (kp14). -/
theorem hPre_ofZS (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypS (L := L) arI AR) :
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
      exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
        (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hC hsc
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
/-- **`dispatch_invokeJPZM` with `JPreemptRestHypS`** (kp14). -/
theorem dispatch_invokeJPZS [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypS (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZS hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZM` with `JPreemptRestHypS`** (kp14; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZS [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypS (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZS hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
