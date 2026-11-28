/-
P3 (p3J gen 25): **"every SC is round-robin" carried by the multicore run; the interrupt top with `FinFootJ` only.**

* P3JMcIrqR's `jEvRef_irqAFtR` at the multicore tops' globals (collapse A, Q: on the narrowed `MachPlat` /
  `IrqPlatA`; the stage-Q transport copy `Fl4ProofsQ.P3.jEvRef_irqAFtR` this module made is gone).
* **`rr_evOut`**: every clause outcome (`EvOut`, with or without the FaultIP write) of a `CKI ∧ RR` state is `RR`
  (P3JRrSys's `kcall_rr`, the FaultIP write by `rq_fl4SyscallFaultIP`).
* **`RunMcWKR := RunMcWKN ∧ RR`**; **`runMcWKR_of`**: a clause top that ends in `RunMcWK` at an `EvOut` outcome ends
  in `RunMcWKR` from a `RunMcWKR` state; **`runMcWKR_w2`**: the 2-core boot witness is `RunMcWKR` (`rr_fInit`).
* **`irqFootWC_of_JR`**: gen 23's `IrqFootWC` [J] at every `NoSig ∧ RR` state from `FinFootJ` alone.
* **`kernel_entry_runMcWKR_irqJ`**: the interrupt clause `RunMcWKR` → `RunMcWKR` with **only `FinFootJ`** [J]
  (gen 24's `kernel_entry_runMcWKN_irqJ` also took `BudFootJ`).

Named premises: `FinFootJ` [J] (P3JMcIrqF); U45nv's globals as in `kernel_entry_runMcWK_irqWC`.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqR
import Fl4Proofs.P3.P3JMcNs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

/-- **Every clause outcome of a `CKI ∧ RR` state is `RR`.** -/
theorem rr_evOut {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (hC : SInvCk.CKI σ)
    (h : SInvRr.RR σ) (he : EvOut fip ev σ σ') : SInvRr.RR σ' := by
  cases fip with
  | false => exact SInvRr.kcall_rr true ev hC h _ he
  | true =>
    obtain ⟨w, hw, h2⟩ := he
    have hw' : SInvCk.CKI w.2 := SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ hC _ hw
    have hn' : SInvRr.RR w.2 := (SInvRr.rq_fl4SyscallFaultIP σ.curThread σ w hw).trans h
    exact SInvRr.kcall_rr true ev hw' hn' _ h2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The multicore run predicate with no signal line and every SC round-robin** (module docstring). -/
def RunMcWKR (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWKN (L := L) arI AR MR s a σ ∧ SInvRr.RR σ

variable {arI AR MR}

/-- **A clause top's `RunMcWK` outcome is `RunMcWKR` from a `RunMcWKR` state** (module docstring). -/
theorem runMcWKR_of {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {fip : Bool} {ev : Fl4Spec.Event}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) (hO : EvOut fip ev σ σ')
    (hR' : RunMcWK (L := L) arI AR MR s' a' σ') : RunMcWKR (L := L) arI AR MR s' a' σ' :=
  ⟨runMcWKN_of hR.1 hO hR', rr_evOut hR.1.1.1.1.2 hR.2 hO⟩

set_option maxHeartbeats 4000000 in
/-- `IrqFootWC` at a `NoSig ∧ RR` state from `FinFootJ` alone. -/
theorem irqFootWC_of_JR (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hIA : IrqPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hFn : FinFootJ (st := st) (L := L) arI AR) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hN : SInvNs.NoSig σ) (hRR : SInvRr.RR σ) :
    IrqFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV w a1 hw
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_irqAFtR J hX hCK hw hRR (Or.inr hN) hFn hARI hA hnd
    (MachPlatF.toT hM hIp) hKD hIA (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWKR` to `RunMcWKR`, with `FinFootJ` only** (module docstring;
`hFn` [J]). -/
theorem kernel_entry_runMcWKR_irqJ [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    (hFn : FinFootJ (st := st) (L := L) arI AR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  refine WP.spec_mono (kernel_entry_runMcWK_irqWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW
    hR.1.1 (irqFootWC_of_JR hARI hA hnd hM hIp hKD hIA hT hmax htu hFn s a σ hR.1.2 hR.2) w a1 hw) ?_
  rintro r ⟨σ', hO, hR'⟩
  exact ⟨σ', hO, runMcWKR_of hR hO hR'⟩

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.Mc

/-- **The 2-core boot witness is `RunMcWKR`.** -/
theorem runMcWKR_w2 : RunMcWKR (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨runMcWKN_w2, SInvRr.rr_fInit⟩

end Fl4Proofs.P3.JBootQ.M2
