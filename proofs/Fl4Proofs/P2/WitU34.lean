/-
P2 (line jboot, gen 5; audit F4): **jboot's witness platform meets `LocPlat` with no `irqOracle` premise**
(`wit_locPlatK`, under `OpaqueWK`: wit's `OpaqueW` without `ipi`, int21's JBootU34).

The old `LocPlat` (`MachPlat` unmasking any line, `IrqPlatA.noIpi` at every arch state) needed `OpaqueW.ipi` (the
opaque IRQ oracle never yields 126 / 127; JBootIpi). Collapse A, Q wrote irqfix's fix back into `MachPlat` (=
`MachPlatF ∧ IpiF`) and `IrqPlatA` (without `noIpi`), which `warI` meets at `ipiMR` with no oracle fact. Here:
* `wit_locPlatK (O : OpaqueWK) : LocPlat wst warI wAR ipiMR` (JBootU34's `u34_w0I` facts);
* `wit_ioapicI : MRKeepIoapic warI ipiMR`;
* `per_not_of_timeConsts`: `OpaqueWK.per` is not a consequence of the spec's `TimeConsts` axioms.
Collapse A, Q removed U2 (`serializable_fl4_localU2`) and with it gen 5's `wit_exec_uncond'` / `wit_U2_uncond'` /
`wit_U2_uncond_of` (U2's non-vacuity over WitU34Gen's copies) and `w1_nonIdleI`.

**Premises**: `OpaqueWK` [P] only (the opaque Fl4Spec constants: `numDomains = 1`, `maxTicksToUs`,
`kernelWCETUs`, `timerUnit`, `MAX_PERIOD_US < 2^61`, `setDeadlineImpl` determinism, a port-read value). No sorry.
-/
import Fl4Proofs.P2.WitPlat
import Fl4Proofs.P3.JBoot1U34
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.E2E (LocalPath SP SerStep)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBoot

noncomputable section

/-- **The concrete platform meets `LocPlat`** (`MachPlat` = `MachPlatF ∧ IpiF`, at `ipiMR`) under
`OpaqueWK` [P]: no `irqOracle` fact. -/
theorem wit_locPlatK (O : OpaqueWK) : LocPlat wst warI wAR ipiMR := by
  obtain ⟨hari, htot, hnd, hMF, hIp, hkd, hio, -, -, hIA, hT, hmax, htu, href, hpi, hsx, hdr, -⟩ := u34_w0I O
  exact ⟨hari, htot, hnd, MachPlatF.toT hMF hIp, hkd, hio,
    ⟨fun _ _ _ => (WP.spec_ok _).2 trivial, fun a => (warI_timeAgreeK O).mb a⟩, hIA, hT, hmax, htu, href, hpi,
    hsx, hdr⟩

/-- `MRKeepIoapic` at `ipiMR` (the model's IOAPIC operations leave the state). -/
theorem wit_ioapicI : MRKeepIoapic warI ipiMR :=
  ⟨fun _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h, fun _ _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h⟩

/-! ## The remaining `OpaqueWK` facts -/

/-- A `TimeConsts` value meeting every axiom, with FL4's WCET and timer unit and `maxPeriodUs = 2 ^ 61`. -/
def wTCbig : Fl4Spec.TimeConsts :=
    { maxPeriodUs := 2305843009213693952,
      kernelWCETUs := 10, ticksPerTimerUnit := 1, timerUnit := 1,
      kernelWCET_us_pos2 := by decide
      MIN_BUDGET_le_MAX_PERIOD := by decide
      ticks_per_timer_unit_non_zero := by decide
      MIN_BUDGET_bound := by decide
      getCurrentTime_buffer_bound := by decide
      kernelWCET_pos' := by decide
      MIN_BUDGET_pos' := by decide
      init_domain_time_pos := by decide
      init_domain_time_bound := by decide
      getCurrentTime_buffer_pos := by decide }

/-- **`OpaqueWK.per` is not a consequence of the spec's `TimeConsts` axioms**: a `TimeConsts` with FL4's WCET
(10) and timer unit (1) and `maxPeriodUs = 2 ^ 61` meets every axiom (`getCurrentTime_buffer_bound` gives only
`maxPeriodUs < 2 ^ 64 / 5`), while `TimeAgree.maxPeriod` (FL4's `max_period_us = max_us / 8`, a `u64`) needs
`MAX_PERIOD_US < 2 ^ 61`. So `per` is a genuine fact about the opaque `timeConsts`. -/
theorem per_not_of_timeConsts : ∃ tc : Fl4Spec.TimeConsts, tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧
    2305843009213693952 ≤ tc.maxPeriodUs.toNat :=
  ⟨wTCbig, rfl, rfl, by decide⟩

end
end Fl4Proofs.P2.Wit
