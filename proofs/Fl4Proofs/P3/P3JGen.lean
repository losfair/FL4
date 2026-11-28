/-
P3 (line p3J, gen 2): **`kernel_entry_reachU35`'s proof transported onto the narrowed path premises**
(P3JXport's kernel-checked copy; the maps are `scratch/p3J/pairs.txt`, written by `genL.py`).

Definitions `JPathAtM`, …, `JPathAtMU29` ↦ `JPathAtML`, …, `JPathAtMU29L` and `JPathAtMU30` ↦ `JPathAtMU35`
(P3JLook); the 16 conversions and the two consumers that apply the path premise ↦ their P3JLook re-proofs;
every other constant of U35's cone mentioning these ↦ its copy (`Fl4ProofsJ…`; collapse A, N / I / Q: the
`Fl4ProofsJI…` / `Fl4ProofsJQ…` / `Fl4ProofsJQI…` copies of the earlier transports' copies are gone, the cone is
the base one). The copy `Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU35` is U35 with
`KDispHypsKVU35` ↦ its copy (fields on `JPathAtMU35`); XTopJointKEntryU36 states it. No premise added; no
sorry.
-/
import Fl4Proofs.P3.P3JXport
open Lean Meta Elab Command

namespace Fl4Proofs.P3.P3JX

/-- The narrowing's maps (module docstring). -/
def specL : Spec where
  recMap := []
  defMap :=
    [(`Fl4Proofs.P3.JPathAtM, `Fl4Proofs.P3.JPathAtML),
     (`Fl4Proofs.P3.JPathAtM35, `Fl4Proofs.P3.JPathAtM35L),
     (`Fl4Proofs.P3.JPathAtM35E, `Fl4Proofs.P3.JPathAtM35EL),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtM36E, `Fl4Proofs.P3.SInvR.G5.JPathAtM36EL),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU4, `Fl4Proofs.P3.SInvR.G5.JPathAtMU4L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU7, `Fl4Proofs.P3.SInvR.G5.JPathAtMU7L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU12, `Fl4Proofs.P3.SInvR.G5.JPathAtMU12L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU17, `Fl4Proofs.P3.SInvR.G5.JPathAtMU17L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU18, `Fl4Proofs.P3.SInvR.G5.JPathAtMU18L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU19, `Fl4Proofs.P3.SInvR.G5.JPathAtMU19L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU21, `Fl4Proofs.P3.SInvR.G5.JPathAtMU21L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU25, `Fl4Proofs.P3.SInvR.G5.JPathAtMU25L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU26, `Fl4Proofs.P3.SInvR.G5.JPathAtMU26L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU27, `Fl4Proofs.P3.SInvR.G5.JPathAtMU27L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU28, `Fl4Proofs.P3.SInvR.G5.JPathAtMU28L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU29, `Fl4Proofs.P3.SInvR.G5.JPathAtMU29L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU30, `Fl4Proofs.P3.SInvR.G5.JPathAtMU35)]
  constMap :=
    [(`Fl4Proofs.P3.JPathAtM35.toM, `Fl4Proofs.P3.JPathAtM35L.toML),
     (`Fl4Proofs.P3.JPathAtM35E.to35, `Fl4Proofs.P3.JPathAtM35EL.to35L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtM36E.to35E, `Fl4Proofs.P3.SInvR.G5.JPathAtM36EL.to35EL),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU4.to36E, `Fl4Proofs.P3.SInvR.G5.JPathAtMU4L.to36EL),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU7.toU4, `Fl4Proofs.P3.SInvR.G5.JPathAtMU7L.toU4L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU12.toU7, `Fl4Proofs.P3.SInvR.G5.JPathAtMU12L.toU7L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU17.toU12, `Fl4Proofs.P3.SInvR.G5.JPathAtMU17L.toU12L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU18.toU17, `Fl4Proofs.P3.SInvR.G5.JPathAtMU18L.toU17L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU19.toU18, `Fl4Proofs.P3.SInvR.G5.JPathAtMU19L.toU18L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU21.toU19, `Fl4Proofs.P3.SInvR.G5.JPathAtMU21L.toU19L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU25.toU21, `Fl4Proofs.P3.SInvR.G5.JPathAtMU25L.toU21L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU26.toU25, `Fl4Proofs.P3.SInvR.G5.JPathAtMU26L.toU25L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU27.toU26, `Fl4Proofs.P3.SInvR.G5.JPathAtMU27L.toU26L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU28.toU27, `Fl4Proofs.P3.SInvR.G5.JPathAtMU28L.toU27L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU29.toU28, `Fl4Proofs.P3.SInvR.G5.JPathAtMU29L.toU28L),
     (`Fl4Proofs.P3.SInvR.G5.JPathAtMU30.toU29, `Fl4Proofs.P3.SInvR.G5.JPathAtMU35.toU29L),
     (`Fl4Proofs.P3.handle_invocation_entryJMU, `Fl4Proofs.P3.handle_invocation_entryJMUL),
     (`Fl4Proofs.P3.handle_invocation_entryJMUM, `Fl4Proofs.P3.handle_invocation_entryJMUML)]

end Fl4Proofs.P3.P3JX

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3JX in
run_cmd liftCoreM do
  let (n, r) ← transport specL [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU35]
  logInfo m!"p3J transport: {n} copied, {r} reused"

#check @Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU35
