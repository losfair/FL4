/-
P3 (DESIGN.md §9): **`cur_sc_chargeable` at a preemption hole** (KENTRY-PLAN
kp13, (2b) case (b), first part).

kp11/kp12 (b): at a hole without `CurInv` whose current thread is not
schedulable and whose current SC is active, the spec's preemption path
charges the current SC (`charge_budget consumed false`). `Inv` after the
charge needs that the SC's owner is in no `inClassR` state (else its
`RelIfBound` may break: the charge can leave the head refill not ready).
For the current thread as owner kp12's `ct_not_inClassR` gives it; for any
other owner it is l4v `cur_sc_chargeable`, carried since kp13 as ScPPR's
`Chg` in `PPR0` (every thread bound to the current SC is the current thread
or inactive): `JAtZ.ppr0_start` from `CurInv`, `PPK` steps (`PPK.ina`), the
finalisations by SpecPPR's `TR.chg` and SpecPPRC (endpoint and notification
frames).

* `jAtPre_holeL`: XTopJointPreemptK's `jAtPre_holeK` with `Chg` at the hole.
* `owner_not_inClassR`: at such a hole every thread bound to the active
  current SC is in no `inClassR` state.
* `JPreemptRestHypL` [W]: `JPreemptRestHypK` at a hole with `Chg`
  (narrower; `jPreemptRestHypL_of`), `hPre_ofZL`, `dispatch_invokeJPZL` /
  `dispatch_invokeJEPZL`. Left in it as before: (b) (now with `Chg`, so the
  charge's `Inv` is provable: the owner-parametrised `charge_budget` at a
  `JHole`, kp13 section) and (2c).
-/
import Fl4Proofs.P3.XTopJointPreemptK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **(b)'s owner fact** (module docstring): with `CtOK`, `CurScFree` and
`Chg`, an unschedulable current thread leaves every thread bound to the
active current SC outside `inClassR` (l4v `cur_sc_chargeable`). -/
theorem owner_not_inClassR {σ : Fl4Spec.State Unit} (hc : CtOK σ) (hf : CurScFree σ) (hg : Chg σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = false) {u : Fl4Spec.ObjRef} {xt : Fl4Spec.Tcb}
    {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap u = some (.tcb xt)) (hl : xt.tcbSchedContext = some σ.curSc)
    (hky : σ.kheap σ.curSc = some (.schedContext y n)) (ha : Fl4Spec.scActive y = true) :
    ¬ inClassR xt.tcbState xt.tcbFault := by
  rcases hg u xt hk hl with e | e
  · subst e; exact ct_not_inClassR hc hf hs hk hl hky ha
  · intro hcl
    rw [e] at hcl
    rcases hcl with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩
    · cases h
    all_goals cases h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`jAtPre_holeK` with `Chg` at the hole** (module docstring). -/
theorem jAtPre_holeL (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    JHoleAtT (L := L) arI AR s a σ ∧ σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ ∧ CurScFree σ ∧ CtOK σ ∧
      Chg σ := by
  refine ⟨(jAtPre_holeK hAK hA hnd hP h).1, (jAtPre_holeK hAK hA hnd hP h).2.1,
    (jAtPre_holeK hAK hA hnd hP h).2.2.1, (jAtPre_holeK hAK hA hnd hP h).2.2.2.1,
    (jAtPre_holeK hAK hA hnd hP h).2.2.2.2, ?_⟩
  obtain ⟨s0, a0, σ0, ⟨-, -, hp00⟩, -, hσ⟩ := h
  obtain ⟨r0, -, ms0, hm0, -, -⟩ := spec_exists (hP.now a0 σ0)
  have hE := Sched.updateTimeStamp_eq' hnd hm0
  obtain ⟨r1, -, irq, ms, hIq, -, -⟩ := spec_exists (hP.irq a0
    { { { σ0 with machineState := ms0 } with curTime := r0.1.bv } with
      consumedTime := σ0.consumedTime + (r0.1.bv - σ0.curTime) })
  have e := pp_err_eq hE hIq _ hσ rfl
  subst e
  exact hp00.1.2.2.2.1

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CtOK`, `CurScFree` and `Chg`** [W] (kp13: `JPreemptRestHypK` narrowed by
`jAtPre_holeL`). Left: (b) no `CurInv`, current thread not schedulable,
active current SC (l4v `charge_budget` of `cur_sc`; its owner is in no
`inClassR` state by `owner_not_inClassR`), and kp5 (i) (`CurInv`, an
endpoint timeout handler with waiting receivers). -/
def JPreemptRestHypL (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ →
    (CurInv σ ∨ Fl4Spec.schedulable σ.curThread σ = false) → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypL_of (h : JPreemptRestHypK (L := L) arI AR) : JPreemptRestHypL (L := L) arI AR :=
  fun s a σ hJ hn hi hs hf hc _ => h s a σ hJ hn hi hs hf hc

/-- **`hPre_ofZK` with `JPreemptRestHypL`** (kp13). -/
theorem hPre_ofZL (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypL (L := L) arI AR) :
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
  · have hcs : CurInv σ1 ∨ Fl4Spec.schedulable σ1.curThread σ1 = false := by
      cases e : Fl4Spec.schedulable σ1.curThread σ1
      · exact Or.inr rfl
      · exact Or.inl (curInv_of_sched hct e)
    exact hRest s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcg hcs
      fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZK` with `JPreemptRestHypL`** (kp13). -/
theorem dispatch_invokeJPZL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypL (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZL hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZK` with `JPreemptRestHypL`** (kp13; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypL (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZL hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
