/-
P3 (line p3J, gen 10): **`kernel_entry_reachU41`'s proof transported onto `ArchSwF'`** (stage 2 of
P3KXport's kernel-checked copy; stage 1 is P3KGen1, whose copies are reused).

* Definition `ArchSwF` ↦ `ArchSwF'` (ArchSwIdle: the idle half asks `IdleVt σ`).
* Records `KFinAtR5` / `KFinAtR31` / `KFinAtR27` / `KFinAtR` ↦ P3KFin's `…I` (`arch : ArchSwF'`, the root
  facts `FinRootR` carried; `KFinAtRI.fo : FinRootI`).
* Constants: G7eChain's `scnt_refines0FA` / `sw_refinesFA` ↦ ArchSwIdle's `…I`; the record conversions
  `KFinAtR8.to5`, `KFinAtR5.to31`, `KFinAtR31.to27`, `KFinAtR27.toR` ↦ P3KFin's; the old finish path
  `jat_scheduleWP0FZR` (now on the g7e chain), `jat_scheduleFR2ZR`, `jat_scheduleSR2ZRP`, `jat_finishJRP`,
  `jat_finishJRN`, `jat_finishJRNM` ↦ P3KFin's (collapse A, Q: the base `jat_finishJRNM`, formerly its
  `Fl4ProofsQ` copy).
* Every other constant of U41's cone using these ↦ its copy under `Fl4ProofsK…`. The copy
  `Fl4ProofsK.P3.SInvR.G5.kernel_entry_reachU41` is U41 with `KFinAtR41` / `KFinEv41` ↦ their copies
  (`arch : ArchSwF'`); XTopJointKEntryU42 states it. No premise added; no sorry.
-/
import Fl4Proofs.P3.P3KFin
open Lean Meta Elab Command

namespace Fl4Proofs.P3.P3KX

/-- The narrowing's maps (module docstring). -/
def specK : Spec where
  recMap :=
    [(`Fl4Proofs.P3.KFinAtR, `Fl4Proofs.P3.KFinAtRI),
     (`Fl4Proofs.P3.KFinAtR27, `Fl4Proofs.P3.KFinAtR27I),
     (`Fl4Proofs.P3.KFinAtR31, `Fl4Proofs.P3.KFinAtR31I),
     (`Fl4Proofs.P3.SInvR.G5.KFinAtR5, `Fl4Proofs.P3.SInvR.G5.KFinAtR5I)]
  defMap := [(`Fl4Proofs.P3.Sched.ArchSwF, `Fl4Proofs.P3.Sched.ArchSwF')]
  constMap :=
    [(`Fl4Proofs.P3.Sched.scnt_refines0FA, `Fl4Proofs.P3.Sched.scnt_refines0FAI),
     (`Fl4Proofs.P3.Sched.sw_refinesFA, `Fl4Proofs.P3.Sched.sw_refinesFAI),
     (`Fl4Proofs.P3.SInvR.G5.KFinAtR8.to5, `Fl4Proofs.P3.SInvR.G5.KFinAtR8.to5I),
     (`Fl4Proofs.P3.SInvR.G5.KFinAtR5.to31, `Fl4Proofs.P3.SInvR.G5.KFinAtR5I.to31I),
     (`Fl4Proofs.P3.KFinAtR31.to27, `Fl4Proofs.P3.KFinAtR31I.to27I),
     (`Fl4Proofs.P3.KFinAtR27.toR, `Fl4Proofs.P3.KFinAtR27I.toRI),
     (`Fl4Proofs.P3.jat_scheduleWP0FZR, `Fl4Proofs.P3.jat_scheduleWP0FZRI),
     (`Fl4Proofs.P3.jat_scheduleFR2ZR, `Fl4Proofs.P3.jat_scheduleFR2ZRI),
     (`Fl4Proofs.P3.jat_scheduleSR2ZRP, `Fl4Proofs.P3.jat_scheduleSR2ZRPI),
     (`Fl4Proofs.P3.jat_finishJRP, `Fl4Proofs.P3.jat_finishJRPI),
     (`Fl4Proofs.P3.jat_finishJRN, `Fl4Proofs.P3.jat_finishJRNI),
     (`Fl4Proofs.P3.jat_finishJRNM, `Fl4Proofs.P3.jat_finishJRNMQI)]

end Fl4Proofs.P3.P3KX

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specK [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU41]
  logInfo m!"p3K transport: {n} copied, {r} reused"

#check @Fl4ProofsK.P3.SInvR.G5.kernel_entry_reachU41
