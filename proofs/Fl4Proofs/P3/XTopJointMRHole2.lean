/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr3): **the preemption point as
the invocations' loops will use it under `MachPlat`** (the interface for mr2
NEXT (b): every preempting loop calls this instead of XTopJointPP's `ppJD`,
which takes the false `PPPlat`).

* `irqVF σ` = (IRQ masks, interrupt table): the fields `ValidIrqMasks` reads.
  `ivk_preemptionPoint`: every outcome of the spec's `preemptionPoint` keeps
  them (the clock read and the IRQ sample move only the oracle positions and
  the last machine time), so `ValidIrqMasks` is kept (`vim_pp`).
* `JAtZ.ppJDMV`: mr1's `JAtZ.ppJDM` (MR, VMT after) as an `ok` equation for
  FL4's `preemption_point` with, at a continuing outcome, `JAtZ`, `PPR0`,
  `NoSwitch`, `MR`, `ValidMachineTime`, `ValidIrqMasks` (the loop invariant
  again), and at a preempting outcome `JAtPreMV` (XTopJointMRHole), which
  `hPre_ofZQIM` consumes. A loop that carries `MR a σ.ms ∧ ValidMachineTime σ ∧
  ValidIrqMasks σ` beside its `JAtZ` invariant thus ends in `JAtPreMV` when
  preempted.
-/
import Fl4Proofs.P3.XTopJointMRHole
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecIV
open Fl4Spec

/-- The fields `ValidIrqMasks` reads. -/
def irqVF (σ : State Unit) := (σ.machineState.irqMasks, σ.interruptStates)

theorem ivk_doMachineOp {α : Type} {mop : NonDet MachineState α}
    (hm : ∀ ms x, x ∈ (mop ms).1 → x.2.irqMasks = ms.irqMasks) : FK irqVF (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨hm2, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have e : ms'.irqMasks = σ.machineState.irqMasks := hm _ _ hm2
  simp only [irqVF, e]

theorem ivk_gct : ∀ ms x, x ∈ (getCurrentTime ms).1 → x.2.irqMasks = ms.irqMasks := by
  intro ms x hx
  rw [getCurrentTime_eq] at hx
  rw [Set.mem_singleton_iff.1 hx]
  rfl

theorem ivk_gai (b : Bool) : ∀ ms x, x ∈ (getActiveIRQ b ms).1 → x.2.irqMasks = ms.irqMasks := by
  intro ms x hx
  rw [getActiveIRQ_eq] at hx
  rw [Set.mem_singleton_iff.1 hx]
  rfl

theorem ivk_doExtendedOp (eop : DetExtMonad Unit) : FK irqVF (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

/-- **The preemption point keeps the IRQ masks and the interrupt table.** -/
theorem ivk_preemptionPoint : FKE irqVF (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive
  repeat' (first
    | exact ivk_doExtendedOp _
    | exact ivk_doMachineOp ivk_gct
    | exact ivk_doMachineOp (ivk_gai _)
    | dk_step0)

end SpecIV

/-- **`ValidIrqMasks` is kept by every outcome of the preemption point.** -/
theorem vim_pp {σ : Fl4Spec.State Unit} {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) (hV : ValidIrqMasks σ) : ValidIrqMasks y.2 := by
  have e := ivk_preemptionPoint σ y hy
  simp only [irqVF, Prod.mk.injEq] at e
  intro i hi
  rw [e.1]
  exact hV i (by rw [← e.2]; exact hi)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The preemption point at a `JAtZ` state carrying `MR`, `ValidMachineTime`
and `ValidIrqMasks`** (module docstring): continuing with the invariant
again, or preempted at a `JAtPreMV` state. -/
theorem JAtZ.ppJDMV {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hPA : PPPlatA arI AR)
    (hR : MR a σ.machineState) (hV : ValidMachineTime σ) (hVI : ValidIrqMasks σ) (hns : Vs.NoSwitch σ)
    (hRd : PPR0 σ) :
    ∃ r, sched.preemption_point st arI s a = ok r ∧ ∃ σ',
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          (∃ (Ac' : Set U64) (Lst' : U64 → List U64), JAtZ (L := L) arI AR Z H Cs Ac' Lst' D r.2.1 r.2.2 σ') ∧
          PPR0 σ' ∧ Vs.NoSwitch σ') ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1 ∧
          JAtPreMV (L := L) arI AR MR r.2.1 r.2.2 σ')) ∧
      XTopAt (L := L) AR Z r.2.1 r.2.2 σ' ∧
      MR r.2.2 σ'.machineState ∧ ValidMachineTime σ' ∧ ValidIrqMasks σ' := by
  obtain ⟨⟨r1, s', a'⟩, hr, σ', hcase, hX', hJ', hR', hV'⟩ := spec_exists (J.ppJDM hAK hA hnd hM hPA hR hV hRd)
  refine ⟨(r1, s', a'), hr, σ', ?_, hX', hR', hV', ?_⟩
  · rcases hcase with ⟨rfl, hm0⟩ | ⟨rfl, hm⟩
    · obtain ⟨hJ0, hp'⟩ := hJ' rfl
      exact Or.inl ⟨rfl, hm0, hJ0, hp', Vs.ake_preemptionPoint'.noSwitch hm0 hns⟩
    · exact Or.inr ⟨rfl, hm, s, a, σ, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hns, hRd, hR, hV, hVI⟩, hr, hm⟩
  · rcases hcase with ⟨-, hm0⟩ | ⟨-, hm⟩
    · exact vim_pp hm0 hVI
    · exact vim_pp hm hVI

end

end

end Fl4Proofs.P3
