/-
P3 (p3J gen 29): **stage K for P3JSysSt** (as P3JStTrapK): the base entry (collapse A, Q: formerly its stage-Q copy) transported by P3JStIrqK's `specKSt`
into `Fl4ProofsK…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JSysSt
import Fl4Proofs.P3.P3JStTrapK
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specKSt [`Fl4Proofs.P3.SInvR.G5.sys_entryStFU41]
  logInfo m!"p3J g29 sys K transport: {n} copied, {r} reused"

#check @Fl4ProofsK.P3.SInvR.G5.sys_entryStFU41
