/-
P3 (p3J gen 22): **stage K for P3JStTrap** (as P3JStEvK): the base entry (collapse A, Q: formerly its stage-Q copy) transported by P3JStIrqK's `specKSt`
into `Fl4ProofsK…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStTrap
import Fl4Proofs.P3.P3JStEvK
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specKSt [`Fl4Proofs.P3.SInvR.G5.trap_entryStU41]
  logInfo m!"p3J g22 trap K transport: {n} copied, {r} reused"

#check @Fl4ProofsK.P3.SInvR.G5.trap_entryStU41
