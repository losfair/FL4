/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch13 (0)): **the check of
`IrqPlatI.act`, and what it shows about `IrqPlat.take`.**

* `JAt` does NOT imply l4v `valid_irq_masks` (an inactive line is masked in
  the machine): `JAtZ.msArJ` gives `JAt` at `{σ with machineState := ms}` for
  ANY `ms` with the same memory, so the spec's `irqMasks` are unconstrained
  by `JAt`. So `IrqPlatI.act` (∀ `JAt` states) is not implied by its
  predicate as a statement about masks.
* But `act` is not even needed: `IrqPlat.take` is quantified over every spec
  state `σ`, and at a state whose machine masks every line the spec's
  `getActiveIRQ` reports `none` (`getActiveIRQ_masked`). Since
  `take_pending_irq a` does not depend on `σ`, `IrqPlat.take` forces
  `take_pending_irq` to return `NO_IRQ` from every arch state
  (`IrqPlat.noIrq`), and `act` follows (`irqPlatI_of`).
* FINDING (lead decision, outside this line: `IrqPlat` lives in
  XTopJointPreempt): `IrqPlat.take` is a ∀-over-states platform premise that
  is satisfiable only by a platform that never reports a pending interrupt.
  Every theorem taking `IrqPlat` therefore covers only the no-interrupt
  branch of `check_interrupt`; the `handle_interrupt` branches below it are
  dead under that premise. The genuine M4 correspondence needs the spec
  machine state tied to the platform state (l4v: the machine state is shared
  between the levels), i.e. a relation `MR a σ.machineState` carried in the
  joint relation from the entry (arch ops keeping it with their machine-op
  counterparts) and `take` stated under `MR a σ.machineState`; then
  `valid_irq_masks` [J] at the hole state on the path is what `act` needs
  (the platform fact "no masked line is reported" is `take`'s `irqMasks i =
  false` conjunct).
-/
import Fl4Proofs.P3.XTopJointIrqZI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- At a spec state whose machine masks every line, `getActiveIRQ` has a
`none` outcome. -/
theorem getActiveIRQ_masked (σ : Fl4Spec.State Unit) (hm : ∀ i, σ.machineState.irqMasks i = true) :
    ∃ σ'', ((none : Option Fl4Spec.Irq), σ'') ∈
      (Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ).1 := by
  let ms1 : Fl4Spec.MachineState := { σ.machineState with irqState := σ.machineState.irqState + 1 }
  have hg : ((none : Option Fl4Spec.Irq), ms1) ∈ (Fl4Spec.getActiveIRQ true σ.machineState).1 := by
    unfold Fl4Spec.getActiveIRQ
    refine mem_bind_nd (x := (σ.machineState.irqMasks, σ.machineState)) rfl ?_
    refine mem_bind_nd (x := ((), ms1)) rfl ?_
    refine mem_bind_nd (x := (Fl4Spec.irqOracle ms1.irqState, ms1)) rfl ?_
    simp only [hm, true_or, ↓reduceIte]
    first | rfl | exact Set.mem_singleton _
  refine ⟨{ σ with machineState := ms1 }, ?_⟩
  unfold Fl4Spec.doMachineOp
  refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
  refine mem_bind_nd (x := ((none, ms1), σ)) ⟨hg, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ with machineState := ms1 })) (Set.mem_singleton _) ?_
  rfl

/-- The singleton outcome of `getActiveIRQ` at an all-masked state is `none`. -/
theorem getActiveIRQ_masked_eq {σ σ'' : Fl4Spec.State Unit} {irq : Option Fl4Spec.Irq}
    (hm : ∀ i, σ.machineState.irqMasks i = true)
    (h : Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, σ'')}, False)) :
    irq = none := by
  obtain ⟨σ3, h3⟩ := getActiveIRQ_masked σ hm
  rw [h] at h3
  exact (Prod.mk.inj (Set.mem_singleton_iff.1 h3)).1.symm

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`IrqPlat` forces `take_pending_irq` to report no line** (module
docstring: `take` at the all-masked copy of any spec state). -/
theorem IrqPlat.noIrq (hIP : IrqPlat arI AR) (σ : Fl4Spec.State Unit) (a : A) :
    arI.take_pending_irq a ⦃ r => r.1 = syscall.NO_IRQ ⦄ := by
  let σm : Fl4Spec.State Unit := { σ with machineState := { σ.machineState with irqMasks := fun _ => true } }
  refine WP.spec_mono (hIP.take a σm) ?_
  rintro r ⟨irq, ms, hq, hn, -, -⟩
  exact hn.2 (getActiveIRQ_masked_eq (σ := σm) (fun _ => rfl) hq)

/-- **`IrqPlatI` from `IrqPlat`**: `act` is implied (no line is ever
reported under `IrqPlat`). -/
theorem irqPlatI_of (hIP : IrqPlat arI AR) : IrqPlatI (L := L) arI AR := by
  refine ⟨hIP, fun s a σ _ => ?_⟩
  refine WP.spec_mono (WP.spec_and (hIP.noIrq σ a) (hIP.take a σ)) ?_
  rintro r ⟨hno, irq0, ms0, hq0, hn0, -, -⟩ irq ms hq i hi
  have h0 : irq0 = none := hn0.1 hno
  rw [hq] at hq0
  have e := Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hq0).1
  have e2 : irq = irq0 := (Prod.mk.inj e).1
  rw [e2, h0] at hi
  exact absurd hi (by simp)

end

end

end Fl4Proofs.P3
