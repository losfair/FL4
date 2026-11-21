/-
P3 (DESIGN.md §9): **the preemption path's last named premise removed**
(KENTRY-PLAN kp17 (3)): XTopJointPreemptA's `JPreemptRestHypC` [W] (the
current thread's timeout fault sent to a receiver waiting on its handler's
endpoint, inside `check_budget`'s charge) proved.

* `jPreemptRestHypC_of`: from ScChargeTR's `JHole.mcsPPJR` (the action
  `ResumeCurThread` or `ChooseNewThread` from `NoSwitch`) and
  `afterInv_of_mcs`, with the platform facts `hmax`/`htu` [P] (l4v: the
  arch's `ticks_to_us` and `maxTicksToUs`; `JEntryGlob.maxTU`/`tu`).
* `dispatch_invokeJPZR`, `dispatch_invokeJEPZR` (NEW TOP): XTopJointPreemptQ's
  `dispatch_invokeJPZA`/`JEPZA` without `hRC`.
-/
import Fl4Proofs.P3.ScChargeTR
import Fl4Proofs.P3.XTopJointPreemptQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`JPreemptRestHypC` [W] proved** (module docstring): `NativeScope` and the
hole's facts as `jPreemptRestHypEQ_ofC`; the receiving endpoint is
`JHole.mcsPPJR`. -/
theorem jPreemptRestHypC_of (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ (a : A) v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    JPreemptRestHypC (L := L) arI AR := by
  intro s a σ hJ hn hi hs hf hc hg hC hsc hnsuf hnq hper xt p bd r q hkt hrr hth hke
  obtain ⟨Z, H, Cs, Ac, Lst, D, s0, a0, σ0, Hh⟩ := hJ
  have hIrq := jIrqHypZ_of hARI hA hIP hP.minBudget hNS
  have hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread := by
    rcases e : σ.schedulerAction with _ | u | _
    · exact Or.inl rfl
    · exact absurd e (hs u)
    · exact Or.inr rfl
  exact WP.spec_mono (afterInv_of_mcs (Hh.mcsPPJR hA hmax htu (hmrt a) (hP.minBudget a) hC hi hres hnq hsc hnsuf
    hkt hrr hth hper ⟨q, hke⟩) hIP hIrq _) fun _ h => h.2.toPPQ

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJPZA` without `JPreemptRestHypC` [W]** (kp17: proved by
`jPreemptRestHypC_of` from `JEntryGlob`'s platform facts `maxTU`/`tu`). -/
theorem dispatch_invokeJPZR [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
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
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (DispInv call bl don) σ r ⦄ :=
  dispatch_invokeJ arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZQ hARI hA hnd hPP hmrt hIP hNS (jPreemptRestHypEQ_ofC hARI hA hPP hmrt hIP hNS
      (jPreemptRestHypC_of hARI hA hPP hmrt hIP hNS hG.maxTU hG.tu)))

set_option maxHeartbeats 4000000 in
/-- **`dispatch_invokeJEPZA` without `JPreemptRestHypC` [W]** (kp17; against
`fl4HandleEvent true`'s branch): no named premise left on the preemption
path. -/
theorem dispatch_invokeJEPZR [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A)
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
      DispPost (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true (invSysOf call bl)) σ r ⦄ :=
  dispatch_invokeJE arI s ar σ J ct hct number call bl don hn hG hE hP _
    (hPre_ofZQ hARI hA hnd hPP hmrt hIP hNS (jPreemptRestHypEQ_ofC hARI hA hPP hmrt hIP hNS
      (jPreemptRestHypC_of hARI hA hPP hmrt hIP hNS hG.maxTU hG.tu)))

end

end

end Fl4Proofs.P3
