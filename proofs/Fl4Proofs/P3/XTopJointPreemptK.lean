/-
P3 (DESIGN.md §9): **a schedulable current thread at a preemption hole has
`CurInv`** (KENTRY-PLAN kp12, (2b) case (a)).

kp11 (a): at a hole without `CurInv` whose current thread is schedulable,
the spec's `check_budget` may `end_timeslice` the current thread and then
postpone the current SC, release-enqueueing its owner, which is not the
current thread; `Inv.rel` can break, and no `JAtZ` fact excludes it. It is
excluded by ScPPR's `CtOK` (the current thread linked to the current SC or
to none, blocked on nothing), which `PPR0` carries since kp12 (from
`Entered`/`CurInv`/`CurRun` at the invocation's start, `JAtZ.ppr0_start`;
kept by `PPK` steps and, via SpecPPR's `TR.tst`, by the finalisations:
deletion only clears links, sets states `Restart`/`Inactive`, and donates an
SC only to a reply's caller, blocked on the reply). l4v counterparts: the
current thread's SC is `cur_sc` (`cur_sc_tcb_are_bound` at the invocation;
`sched_context_donate`'s donee is the `BlockedOnReply` caller, never the
current thread, `ct_in_state activatable`).

* `curInv_of_sched`: `CtOK` and a schedulable current thread give `CurInv`
  (its SC is the current SC, active and released from the queue).
* `jAtPre_holeK`: XTopJointPreemptO's `jAtPre_holeO` with `CtOK` at the hole
  (the preemption point keeps the heap, the current thread and SC).
* `JPreemptRestHypK` [W]: `JPreemptRestHypJ` at a hole with `CtOK` and
  `CurScFree`, hence `CurInv ∨ ¬ schedulable` (stated as premise). Left:
  (b) no `CurInv`, current thread not schedulable, active current SC (charge
  through the SC's owner: needs l4v `cur_sc_chargeable`, kp12 section), and
  (2c) `CurInv`, ¬`NoTmoSend`, ¬`PPCovT`. `jPreemptRestHypK_of`,
  `hPre_ofZK`, `dispatch_invokeJPZK` / `dispatch_invokeJEPZK`.
-/
import Fl4Proofs.P3.XTopJointPreemptO
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **`CtOK` and a schedulable current thread give `CurInv`** (module
docstring). -/
theorem curInv_of_sched {σ : Fl4Spec.State Unit} (hc : CtOK σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = true) : CurInv σ := by
  obtain ⟨x, scp, y, n, hk, hsc, hr, hky, ha, hq⟩ := schedulable_inv hs
  have e : scp = σ.curSc := by
    rcases (hc x hk).1 with e | e <;> rw [hsc] at e <;> cases e; rfl
  subst e
  exact ⟨⟨x, hk, hsc, NotIpcBlk.of_runnable hr⟩, ⟨y, n, hky⟩, fun _ y' n' h => by
    rw [hky] at h; cases h; exact ha, hq⟩

/-- **(b) for the current thread as the current SC's owner**: at a hole
with `CtOK` and `CurScFree`, an unschedulable current thread bound to the
active current SC is in no `inClassR` state (so `InvBut σ' ct → Inv σ'`
after the charge needs no `RelIfBound` of it). What (b) still lacks is the
same for an owner other than the current thread (l4v `cur_sc_chargeable`;
kp12 section). -/
theorem ct_not_inClassR {σ : Fl4Spec.State Unit} (hc : CtOK σ) (hf : CurScFree σ)
    (hs : Fl4Spec.schedulable σ.curThread σ = false) {xt : Fl4Spec.Tcb} {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap σ.curThread = some (.tcb xt)) (hl : xt.tcbSchedContext = some σ.curSc)
    (hky : σ.kheap σ.curSc = some (.schedContext y n)) (ha : Fl4Spec.scActive y = true) :
    ¬ inClassR xt.tcbState xt.tcbFault := fun hcl => by
  have hr := inClass_runnable hcl.cls (hc xt hk).2.2
  rw [schedulable_of hk hl hr hky ha (hf _ xt hk hl)] at hs
  cases hs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **`jAtPre_holeO` with `CtOK` at the hole** (module docstring). -/
theorem jAtPre_holeK (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPre (L := L) arI AR s a σ) :
    JHoleAtT (L := L) arI AR s a σ ∧ σ.curThread ≠ σ.idleThread ∧ Vs.NoSwitch σ ∧ CurScFree σ ∧ CtOK σ := by
  refine ⟨(jAtPre_holeO hAK hA hnd hP h).1, (jAtPre_holeO hAK hA hnd hP h).2.1,
    (jAtPre_holeO hAK hA hnd hP h).2.2.1, (jAtPre_holeO hAK hA hnd hP h).2.2.2, ?_⟩
  obtain ⟨s0, a0, σ0, ⟨-, -, hp00⟩, -, hσ⟩ := h
  obtain ⟨r0, -, ms0, hm0, -, -⟩ := spec_exists (hP.now a0 σ0)
  have hE := Sched.updateTimeStamp_eq' hnd hm0
  obtain ⟨r1, -, irq, ms, hIq, -, -⟩ := spec_exists (hP.irq a0
    { { { σ0 with machineState := ms0 } with curTime := r0.1.bv } with
      consumedTime := σ0.consumedTime + (r0.1.bv - σ0.curTime) })
  have e := pp_err_eq hE hIq _ hσ rfl
  subst e
  exact hp00.1.2.2.1

variable (arI) in
/-- **The preemption path outside `PPCov ∨ PPCovT ∨ PPCovI` at a hole with
`CtOK` and `CurScFree`, so with `CurInv` or an unschedulable current thread**
[W] (kp12: `JPreemptRestHypJ` narrowed by `jAtPre_holeK` and
`curInv_of_sched`). Left: (b) no `CurInv`, current thread not schedulable,
active current SC (l4v `charge_budget` of `cur_sc` through its owner under
`cur_sc_chargeable`), and kp5 (i) (`CurInv`, an endpoint timeout handler
with waiting receivers). -/
def JPreemptRestHypK (AR : A → Fl4Spec.Cr3 → Prop) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ →
    (CurInv σ ∨ Fl4Spec.schedulable σ.curThread σ = false) → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) →
    syscall.after_invocation st arI s a (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ (r.2.1, r.2.2) ⦄

theorem jPreemptRestHypK_of (h : JPreemptRestHypJ (L := L) arI AR) : JPreemptRestHypK (L := L) arI AR :=
  fun s a σ hJ hn hi hs _ _ _ hc => h s a σ hJ hn hi hs hc

/-- **`hPre_ofZJ` with `JPreemptRestHypK`** (kp12). -/
theorem hPre_ofZK (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypK (L := L) arI AR) :
    ∀ (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit), RelTopM (L := L) s1 σ1 →
      JAtPre (L := L) arI AR s1 a1 σ1 →
      syscall.after_invocation st arI s1 a1 (.Err .Preempted) ⦃ r => PPQ (L := L) arI AR σ1 (r.2.1, r.2.2) ⦄ := by
  intro s1 a1 σ1 _ h
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh, hTs⟩, hni, hns, hfr, hct⟩ := jAtPre_holeK hARI.toARKeep hA hnd hP h
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
      (hNS s1 a1 σ1 ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩) hni hns hfr hct hcs
      fun h' => h'.elim (fun h2 => hc (Or.inl h2)) fun h2 => h2.elim (fun h3 => hc (Or.inr h3)) hi

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZJ` with `JPreemptRestHypK`** (kp12). -/
theorem dispatch_invokeJPZK [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypK (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZK hARI hA hnd hPP hmrt hIP hNS hRest)

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZJ` with `JPreemptRestHypK`** (kp12; against
`fl4HandleEvent true`'s branch). -/
theorem dispatch_invokeJEPZK [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (number : I64) (call bl don : Bool)
    (hn : InvSys number call bl don)
    (hG : JEntryGlob (L := L) arI AR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (hP : JPathAt (L := L) arI AR Z H Cs D s ar σ ct call bl don false (L.mem s (regA ct layout.reg.CAP)))
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypK (L := L) arI AR) :
    syscall.dispatch_syscall st arI s ar number ⦃ r =>
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZK hARI hA hnd hPP hmrt hIP hNS hRest)

end

end

end Fl4Proofs.P3
