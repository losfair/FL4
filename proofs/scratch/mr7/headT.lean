/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **the TCB cap installs
at `MachPlat`**: XTopJointTcbInstall's `install_tcb_capJ` … `tcb_configureJ`
and XTopJointTcbSsp's `install_fhJ` … `tcb_set_sched_paramsJ` with the
deletion loop's preempted invariant `WJPM` (XTopJointMRDel: `WJP` and
`JAtPreMV`) for `WJP`, so a preempted install ends in `JAtPreMV` (what mr4's
`decOK_JM` asks of the `JPreDecHyp` kinds). Generated: scratch/mr7/gentcb.py
+ headT.lean. The copies (names with an `M` suffix: `TcbInsWM`,
`install_tcb_capJM`, …, `tcb_set_sched_paramsJM`) differ from the originals
only in the preempted invariant (`TcbInsWM.del : DelHypsWRZ (W kb) (WJPM ..)`)
and in `top_of_instJM`'s / `ssp_tailJM`'s preempted branch, which reads
`JAtPreMV` off `WJPM`.
-/
import Fl4Proofs.P3.XTopJointTcbSsp
import Fl4Proofs.P3.XTopJointMRDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

