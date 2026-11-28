/-
P3 (line jboot, gen 5): **the gen-4 witness `w1` / `σ1` is a `JReachU34` state** (irqfix's
`JReachU34 := JReachU17 ∧ IrqStB`, XTopJointKEntryU34), next to int/j21's JBootU34 for the gen-3 witness `w0`
(`jReachU34_w0`, `jReachU34_w0I`, `u34_w0I`, `OpaqueWK`; not restated here).

* `σ1_irqStB`: `σ1` keeps `fInitASt`'s interrupt states (all inactive), so every line above `maxIRQ` is inactive.
* **`jReachU34_w1`** (`wMR = modelMR`) and **`jReachU34_w1I`** (irqfix's `ipiMR`, the relation at which `warI`
  meets `MachPlatF` / `IpiF` with no oracle assumption): the running-root-thread witness starts U34.
* **`u34_w1I (O : OpaqueWK)`**: every premise of `kernel_entry_reachU34` at `wst` / `warI` / `wAR` / `ipiMR`
  (JBootU34's `u34_w0I`) with the start state `jReachU34_w1I`.
* **`opaqueW_toK`**: wit's `OpaqueW` gives `OpaqueWK` (it is `OpaqueW` without `ipi`), so `OpaqueWK` is no
  stronger an assumption.

Premises: `OpaqueWK` [P] in `u34_w1I` only (JBootU34's; the opaque Fl4Spec constants). No sorry. New module;
no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Ipi
import Fl4Proofs.P3.JBootU34
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- `IrqStB` at the gen-4 spec state: its interrupt states are `fInitASt`'s (all inactive). -/
theorem σ1_irqStB : SInvIB.IrqStB σ1 := fun _ _ => rfl

/-- **`JReachU34` at the gen-4 witness** (`modelMR`; non-idle current thread). -/
theorem jReachU34_w1 : JReachU34 (L := wL) warI wAR wMR w1 σ1.machineState σ1 :=
  ⟨jReachU17_w1, σ1_irqStB⟩

/-- **`JReachU34` at `ipiMR` for the gen-4 witness** (the start state of `kernel_entry_reachU34` on `warI`). -/
theorem jReachU34_w1I : JReachU34 (L := wL) warI wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨jReachU17_w1_ipi, σ1_irqStB⟩

/-- **wit's `OpaqueW` gives `OpaqueWK`** (`OpaqueWK` is `OpaqueW` without its `ipi` field). -/
theorem opaqueW_toK (O : OpaqueW) : OpaqueWK :=
  ⟨O.nd, O.max, O.wcet, O.unit, O.per, O.dl, O.pin⟩

/-- **Every premise of `kernel_entry_reachU34` at the witness platform, started at the gen-4 witness**, under
`OpaqueWK` [P] (no `irqOracle` fact). -/
theorem u34_w1I (O : OpaqueWK) :
    ARIface warI wAR ∧ P0.ArchTotal warI ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI ipiMR ∧ IpiF warI ipiMR ∧
      MRKeepD warI ipiMR ∧ MRKeepIo warI ipiMR ∧ MRKeepIoapic warI ipiMR ∧
      (∀ a c, wAR a c → warI.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI wAR ∧ TimeAgree warI ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI wAR ∧ PortInValMR warI ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      JReachU34 (L := wL) warI wAR ipiMR w1 σ1.machineState σ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -⟩ := u34_w0I O
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, jReachU34_w1I⟩

end

end Fl4Proofs.P3.JBoot
