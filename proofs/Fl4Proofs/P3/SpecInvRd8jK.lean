/-
P3 (DESIGN.md §9), invariant line G1 (rd8j; de-duplicated in rd8p): **the
`KZ` facts rd12b does not state** (spec side only, outside the JAtZ cone).

rd8j restated rd12b's shell pieces here while SpecInvRd12bA / C reached
`JointAt`. They no longer do (scratch/rd8h/anc.py), so rd8j / rd8m now use
rd12b's originals (`A12b.scO` / `svOf` / `kz_sv` / `kz_trans` / `kz_curThread`,
`A12b.invF` / `invE` / `invFin` / `invPost` / `fl4HandleInvocationR_eq` /
`kz_invF` / `kz_invE`, `A12b.mem_handleE_cases`, `A12b.sendArgs` / `srArgs`).
Only the four `KZ` facts below have no rd12b counterpart.
-/
import Fl4Proofs.P3.SpecInvRd12bC
import Fl4Proofs.P3.SpecInvRd8hR
open Classical

namespace Fl4Proofs.P3.SInvR.B8j
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

theorem kz_act {σ0 s : State Unit} (h : A12b.KZ σ0 s) : s.schedulerAction = σ0.schedulerAction :=
  congrArg (fun p => p.2.2) h

theorem kz_time {σ0 s : State Unit} (h : A12b.KZ σ0 s) : s.curTime = σ0.curTime :=
  congrArg (fun p => p.1.2.2) h

theorem kz_cfS {σ0 s : State Unit} (h : A12b.KZ σ0 s) : cfS s = cfS σ0 :=
  congrArg (fun p => p.2.1) h

theorem svs_kz {σ0 s : State Unit} (h : A12b.KZ σ0 s) : SVK.SVS σ0 s :=
  ⟨fun p => A12b.kz_sv h p, kz_time h, Or.inl (kz_act h)⟩

end

end Fl4Proofs.P3.SInvR.B8j
