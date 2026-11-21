/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`GK` for every
spec function of the syscall entry** (spec side only; outside the `JAtZ` cone).

One lemma per spec function reachable from `fl4KernelEntrySyscall` that
MachFieldFamT's `MTK` family leaves out (the functions reaching a machine-time
or IRQ writer: `updateTimeStamp`, `getActiveIRQ`, `maskInterrupt`,
`setIrqState`, the timer and port operations, `clearMemory`/`freeMemory`, and
their callers, plus the decodes), bottom-up by `gk_auto` (generated:
scratch/invB/gen2.py from the spec's call graph). By hand: `rec_del` and
`cap_revoke` (the pre-fixed point of DomRecDel's `dk_recDel` /
`dk_capRevoke`, at the predicate "every `GK` predicate is kept"),
`fl4Awaken` (each fired timer is MachFieldFamT's `sendSignal`), and the
higher-order `syscall`, `orChoiceE`, `checkCapAt`, `archNoReturn`,
`decodeIrqControlInvocationWith`, `portIn`, `portOut`.
-/
import Fl4Proofs.P3.SpecInvValidMachineTimeKit

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

