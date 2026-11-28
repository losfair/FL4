/-
P3 (line p3J, gen 6): **`kernel_entry_reachU40` at the jboot witness** (arch `warI1`, JBootIoa).

* **`jReachU40_w0I1`**: `JReachU40 warI1 wAR ipiMR w0 fInitASt.machineState fInitASt` (`JReachU40.of_U38
  jReachU38_w0I1`).
* **`u40_w0I1 (O : OpaqueWK)`**: every premise of `kernel_entry_reachU40` at `wst` / `warI1` / `wAR` / `ipiMR`
  (U39's: `u39_w0I1`) with its start `jReachU40_w0I1`. Left: only U40's per-entry syscall / event [J]s.
* **`warI1_fInitIpi_start`**: at irqfix3's `fInitIpiASt` (126 / 127 reserved, `IrqStB` false there:
  `fInitIpi_not_irqStB`) the start's spec half `IrqCarry ∧ IoaRel warI1` holds (`fInitIpi_irqCarry`,
  `fInitIpi_ioaStart`), so any `JReachU17` there is a U40 start (`JReachU40.of_fInitIpi`). The `JReachU17`
  itself at `fInitIpiASt` needs an FL4 state whose IRQ words encode the reserved lines (w0's are all 0, which
  `IrqRel` relates to `irqInactive`): open.

Named premises: `OpaqueWK` [P] (JBootU34) only. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootIoa
import Fl4Proofs.P3.XTopJointKEntryU40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **`JReachU40` at the witness** (arch `warI1`, `ipiMR`). -/
theorem jReachU40_w0I1 : JReachU40 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  JReachU40.of_U38 jReachU38_w0I1

/-- **Every premise of `kernel_entry_reachU40` at the witness platform** with its start state, under
`OpaqueWK` [P]. Only U40's per-entry [J]s remain. -/
theorem u40_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧ IoaMap warI1 ∧
      JReachU40 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, _⟩ := u39_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, jReachU40_w0I1⟩

/-- **The U40 start's spec half at `fInitIpiASt`** (lines 126 / 127 reserved), for the witness arch, where
U34's `IrqStB` fails. -/
theorem warI1_fInitIpi_start :
    (SInvIB.IrqCarry SInvIB.fInitIpiASt ∧ IoaRel warI1 SInvIB.fInitIpiASt) ∧ ¬ SInvIB.IrqStB SInvIB.fInitIpiASt :=
  ⟨fInitIpi_ioaStart warI1_ioaRel, SInvIB.fInitIpi_not_irqStB⟩

/-- **A `JReachU17` at `fInitIpiASt` on the witness platform is a U40 start.** -/
theorem jReachU40_fInitIpi {s : WSt} {a : MachineState}
    (hJ : JReachU17 (L := wL) warI1 wAR ipiMR s a SInvIB.fInitIpiASt) :
    JReachU40 (L := wL) warI1 wAR ipiMR s a SInvIB.fInitIpiASt :=
  JReachU40.of_fInitIpi hJ warI1_ioaRel

end

end Fl4Proofs.P3.JBoot
