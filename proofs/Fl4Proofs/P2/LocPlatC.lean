/-
# P2 (line p3mc, gen 46): the re-base's interface — **`LocPlatC`**, the one thing the V15 trunk reads off the
platform, with an instance on the fixed platform (`MachPlatF` + `IpiF` + `IrqPlatK`) and no `irqOracle` fact

Handoff §51b (the collapse follow-up, first step). Every P2 top takes `P : LocPlat st arI AR MR` (P2/E2EVFl4W3:
`MachPlat` and `IrqPlatA` among its 15 fields), and (before collapse A, Q) `LocPlat` could not hold at any `MR` that keeps the IPI vectors
126 / 127 masked unless the opaque `irqOracle` avoided them (P3/JBootIpi `ipi_forces_oracle`; `OpaqueH.ipi`,
P2/LocPlatModel). Inside the trunk, `P` is read **only** through `PathObl.chainOf_exists P` (P2/E2EVFl4W3:142: the
`loc_chain_all` call; every other field occurrence `P.ari … P.dr` of P2 is in that call or its three W9 / W13 /
U12a variants), i.e. through the proposition "every `JReachU17` exit has a P3 chain". `SerExitW P` uses it only
inside `Classical.choose`, whose proof argument is irrelevant. So:

* **`LocPlatC st arI AR MR`** (Prop): `nd : numDomains = 1` and `chain`: every `JReachU17` exit has a `ChainOf`
  (P2/E2EVFl4W3, base, platform-free).
* **`LocPlat.toC`** (the platform gives it: `chainOf_exists`).
* `chainCC`, **`SerExitC`**, `SerExitC.chainOf`; **`serExitW_iff_C`**: `SerExitW P K Ch ↔ SerExitC P.toC K Ch`
  (`Iff.rfl`: the two `Classical.choose` are over the same proposition).
* **`locPlatC_wit`**: `LocPlatC wst warI wAR ipiMR` from `OpaqueWK` [P] only (jboot's witness platform,
  P2/WitU34 `wit_locPlatK`): **no `irqOracle` assumption** (`OpaqueWK` = `OpaqueH` without `ipi`; `MR = ipiMR`
  keeps 126 / 127 masked).
* `jReachU17_of_U40`: a U46-line exit (`JReachU40 = (JReachU17 ∧ IrqCarry) ∧ IoaRel`, P3/XTopJointKEntryU40) is a
  `JReachU17` exit, so `SerExitC`'s exits include every U46 exit (U46's `IrqCarry` / `IoaRel` are extra facts at
  the exit, not obligations on the chain).

What remains for the re-base (handoff §51b): restate the V15 trunk's `P : LocPlat` parameter as `P : LocPlatC`
(in place, the old statements one-line corollaries through `LocPlat.toC` and `serExitW_iff_C`); its bottom
(P2/E2EVFl4W3 `SerExitW`, P2/E2EPU6 / E2EPU7, the W4–W16 and U1–U5 files) is touched by the collapse PR, so that
step waits for it.

No named premise beyond `OpaqueWK` [P] (in `locPlatC_wit`); no existing statement changed (new module).

**Gen 54:** `LocPlatC`, `LocPlat.toC`, `chainCC`, `chainCC_spec`, `SerExitC`, `SerExitC.chainOf` and
`serExitW_iff_C` moved, unchanged, to P2/E2EVFl4W3 (the bottom of the V15 trunk, which is re-based onto them in
place); `jReachU17_of_U40` and `locPlatC_wit` stay here. The slot obligations also read two P3 facts at chain
states (`ChainRun`, `ChainAct0`): the trunk's platform is `LocPlatCR` (P2/E2EPU12a), its witness instance
`locPlatCR_wit` (P2/V15PlatW).

**Collapse A, Q:** irqfix's `MachPlatT` / `IrqPlatK` are written back into `MachPlat` / `IrqPlatA`, so `LocPlat`
itself is the fixed platform (there is **no hidden `irqOracle` fact** in `LocPlat` any more: JBootIpi's
`ipi_forces_oracle`, which showed the old `MachPlat` + `IrqPlatA` forcing one, is removed). The copy
`Fl4ProofsQ.P2.PathObl.LocPlat` (P2/WitU34Gen) is gone, and with it `LocPlatC.ofQ` and `serExitQ_iff_C` (now
`LocPlat.toC` and `serExitW_iff_C`); `locPlatC_wit` is `(wit_locPlatK O).toC`.
-/
import Fl4Proofs.P2.WitU34
import Fl4Proofs.P2.E2EPV15AD
import Fl4Proofs.P3.XTopJointKEntryU40
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)

noncomputable section
open Classical

section
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {st arI AR MR}

/-- **A U46-line exit is a `JReachU17` exit** (module docstring). -/
theorem jReachU17_of_U40 {σe : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (h : Fl4Proofs.P3.SInvR.G5.JReachU40 (L := L) arI AR MR σe a3 τ) :
    Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σe a3 τ :=
  h.1.1

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.Wit
open Fl4Proofs.P2.PathObl Fl4Proofs.P3 Fl4Proofs.P3.JBoot

/-- **`LocPlatC` on jboot's witness platform at `ipiMR`, from `OpaqueWK` [P] only — no `irqOracle` fact**
(module docstring). -/
theorem locPlatC_wit (O : OpaqueWK) : LocPlatC wst warI wAR ipiMR :=
  (wit_locPlatK O).toC

end Fl4Proofs.P2.Wit
