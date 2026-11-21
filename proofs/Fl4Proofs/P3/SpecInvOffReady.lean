/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`OffReady`
(l4v `cur_sc_offset_ready`) as a spec-only invariant: definition and boot**
(spec side only; outside the `JAtZ` cone).

* `OffReady` is ScCur's (`Sched.OffReady`: the current SC's head refill time
  plus the consumed time is not after the current time), the field
  `KBudgetB.off` of `kernel_entryJ26P` reads (at `faultIPSt σ ct x`).
* `boot_offReady`: the spec's initial state (`initASt`): the current SC is the
  idle SC, whose head refill starts at 0, with consumed and current time 0.
-/
import Fl4Proofs.P3.SpecInvValidMachineTime

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec

noncomputable section

theorem initKheap_idleSc : initKheap idleScPtr = some (.schedContext
      { defaultSchedContext with
        scTcb := some idleThreadPtr,
        scRefills := [{ rTime := 0, rAmount := MAX_PERIOD }, { rTime := MAX_PERIOD, rAmount := 0 }],
        scBudget := MAX_PERIOD,
        scRefillMax := MIN_REFILLS } 0) := by
  unfold initKheap
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self]

/-- **`OffReady` at boot.** -/
theorem boot_offReady : Sched.OffReady (initASt (Z := Unit)) := by
  intro y n hy
  have h : initKheap idleScPtr = some (.schedContext y n) := hy
  rw [initKheap_idleSc] at h
  cases h
  show (0 : Nat) + 0 ≤ 0
  rfl

end

end Fl4Proofs.P3.SInvV
