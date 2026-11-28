/-
P3 (p3J gen 24): **"no signal line" carried by the multicore run; the interrupt top without `IrqSigFootJ`.**

* **`RunMcWKN := RunMcWK ∧ NoSig`** (P3JNsKit's `NoSig`: no IRQ line of the spec state is `IRQSignal`).
* **`noSig_evOut`**: every clause outcome (`EvOut`, with or without the FaultIP write) of a `CKI ∧ NoSig` state is
  `NoSig` (P3JNsSys's `kcall_noSig`, the FaultIP write by `gkn_fl4SyscallFaultIP`). **`runMcWKN_of`**: a clause top
  that ends in `RunMcWK` at an `EvOut` outcome ends in `RunMcWKN` from a `RunMcWKN` state — so each of gen 23's six
  `kernel_entry_runMcWK_…WC` tops lifts to `RunMcWKN` with no new premise.
* **`noSig_fInit`**, **`runMcWKN_w2`**: the 2-core boot witness (FL4's boot IRQ states: line 125 timer, 126 / 127
  reserved, the rest inactive) is `RunMcWKN`.
* **`kernel_entry_runMcWKN_irqJ`**: the interrupt clause `RunMcWKN` → `RunMcWKN` with **only `BudFootJ` and
  `FinFootJ`** [J]: at a `NoSig` entry the handler never takes its signal branch (P3JMcIrqF's composition with
  `Or.inr`), so `IrqSigFootJ` is discharged on these runs.

Named premises: `BudFootJ`, `FinFootJ` [J] (P3JMcIrqF); U45nv's globals as in `kernel_entry_runMcWK_irqWC`.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqFQ
import Fl4Proofs.P3.P3JNsSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

/-- **Every clause outcome of a `CKI ∧ NoSig` state is `NoSig`.** -/
theorem noSig_evOut {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (hC : SInvCk.CKI σ)
    (h : SInvNs.NoSig σ) (he : EvOut fip ev σ σ') : SInvNs.NoSig σ' := by
  cases fip with
  | false => exact SInvNs.kcall_noSig true ev hC h _ he
  | true =>
    obtain ⟨w, hw, h2⟩ := he
    have hw' : SInvCk.CKI w.2 := SInvV.hv_fl4SyscallFaultIP (P := SInvCk.CKI) σ.curThread σ hC _ hw
    have hn' : SInvNs.NoSig w.2 :=
      SInvNs.gkn_fl4SyscallFaultIP σ.curThread SInvNs.NoSig SInvNs.wln_noSig σ h _ hw
    exact SInvNs.kcall_noSig true ev hw' hn' _ h2

/-- **The boot IRQ states have no signal line.** -/
theorem noSig_fInit : SInvNs.NoSig JBootQ.fInitASt := by
  intro irq
  show JBootQ.ipiIS irq ≠ _
  unfold JBootQ.ipiIS
  simp only [Function.update_apply]
  split_ifs
  all_goals first
    | (intro h; cases h)
    | (intro h; simp [initASt] at h)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The multicore run predicate with no signal line** (module docstring). -/
def RunMcWKN (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ ∧ SInvNs.NoSig σ

variable {arI AR MR}

/-- **A clause top's `RunMcWK` outcome is `RunMcWKN` from a `RunMcWKN` state** (module docstring). -/
theorem runMcWKN_of {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {fip : Bool} {ev : Fl4Spec.Event}
    (hR : RunMcWKN (L := L) arI AR MR s a σ) (hO : EvOut fip ev σ σ')
    (hR' : RunMcWK (L := L) arI AR MR s' a' σ') : RunMcWKN (L := L) arI AR MR s' a' σ' :=
  ⟨hR', noSig_evOut hR.1.1.1.2 hR.2 hO⟩

set_option maxHeartbeats 4000000 in
/-- `IrqFootWC` at a `NoSig` state from `BudFootJ` and `FinFootJ` (`IrqSigFootJ` not needed). -/
theorem irqFootWC_of_JN (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hIA : IrqPlatA arI AR) (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hBud : BudFootJ (st := st) (L := L) arI AR) (hFn : FinFootJ (st := st) (L := L) arI AR) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hN : SInvNs.NoSig σ) :
    IrqFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV w a1 hw
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_irqAFt J hX hCK hw hBud (Or.inr hN) hFn hARI hA hnd
    (MachPlatF.toT hM hIp) hKD hIA (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWKN` to `RunMcWKN`, with `BudFootJ` and `FinFootJ` only** (module
docstring; `hBud`, `hFn` [J]). -/
theorem kernel_entry_runMcWKN_irqJ [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    (hBud : BudFootJ (st := st) (L := L) arI AR) (hFn : FinFootJ (st := st) (L := L) arI AR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKN (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWKN (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  refine WP.spec_mono (kernel_entry_runMcWK_irqWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW
    hR.1 (irqFootWC_of_JN hARI hA hnd hM hIp hKD hIA hT hmax htu hBud hFn s a σ hR.2) w a1 hw) ?_
  rintro r ⟨σ', hO, hR'⟩
  exact ⟨σ', hO, runMcWKN_of hR hO hR'⟩

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.Mc

/-- **The 2-core boot witness is `RunMcWKN`.** -/
theorem runMcWKN_w2 : RunMcWKN (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨runMcWK_w2, noSig_fInit⟩

end Fl4Proofs.P3.JBootQ.M2
