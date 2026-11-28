/-
P3 (p3J gen 24): **stage Q of the interrupt footprint and the derived interrupt top.**

* P3JMcIrqF's `jEvRef_irqAFt` at the multicore tops' globals (collapse A, Q: on the narrowed `MachPlat` /
  `IrqPlatA` themselves; the stage-Q transport copy `Fl4ProofsQ.P3.jEvRef_irqAFt` this module made is gone).
* **`irqFootWC_of_J`**: gen 23's `IrqFootWC` [J] holds at every state, from `BudFootJ`, `IrqSigFootJ`,
  `FinFootJ` [J] (P3JMcIrqF) and globals of the interrupt top (`SInvX` and `CKI` from `RunMcWK`'s `RunCK`).
* **`kernel_entry_runMcWK_irqJ`**: the interrupt clause `RunMcWK` → `RunMcWK` (gen 23's
  `kernel_entry_runMcWK_irqWC`) with `BudFootJ`, `IrqSigFootJ`, `FinFootJ` in place of `IrqFootWC`.

Named premises: `BudFootJ`, `IrqSigFootJ`, `FinFootJ` [J] (P3JMcIrqF); U45nv's globals as in
`kernel_entry_runMcWK_irqWC`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`IrqFootWC` from the three phase footprints** (module docstring). -/
theorem irqFootWC_of_J (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hIA : IrqPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hBud : BudFootJ (st := st) (L := L) arI AR) (hSig : IrqSigFootJ (st := st) (L := L) arI AR)
    (hFn : FinFootJ (st := st) (L := L) arI AR) (s : S) (a : A) (σ : Fl4Spec.State Unit) :
    IrqFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV w a1 hw
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_irqAFt J hX hCK hw hBud (Or.inl hSig) hFn hARI hA hnd (MachPlatF.toT hM hIp)
    hKD hIA (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWK` to `RunMcWK`, with the three phase footprints** (module
docstring; `hBud`, `hSig`, `hFn` [J]). -/
theorem kernel_entry_runMcWK_irqJ [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    (hBud : BudFootJ (st := st) (L := L) arI AR) (hSig : IrqSigFootJ (st := st) (L := L) arI AR)
    (hFn : FinFootJ (st := st) (L := L) arI AR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_irqWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW hR
    (irqFootWC_of_J hARI hA hnd hM hIp hKD hIA hT hmax htu hBud hSig hFn s a σ)

end

end Fl4Proofs.P3.Mc
