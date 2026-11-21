/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`CtNQR`
(l4v `ct_not_in_q`: under `resume_cur_thread` the current thread is in no
ready queue) as a spec-only invariant: definition and boot** (spec side only;
outside the `JAtZ` cone).

* `CtNQR σ := schedulerAction = resumeCurThread → ∀ d p, ct ∉ readyQueues d p`.
  At the entry (`Entered σ`: action = resume) it gives ScPPR's `CtNQ σ`, the
  fields `JEntryAt.ctnq`, `KDispHypsKV26.recv`'s ct_not_in_q and
  `KBudgetB.tmo`'s right disjunct of `kernel_entryJ26P` (`CtNQR.ctnq`).
* `boot_ctNQR`: the spec's initial state has empty ready queues.
-/
import Fl4Proofs.P3.SpecInvValidMachineTime

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec

noncomputable section

/-- **[J] l4v `ct_not_in_q`** (module docstring). -/
def CtNQR (σ : State Unit) : Prop :=
  σ.schedulerAction = .resumeCurThread → ∀ d p, σ.curThread ∉ σ.readyQueues d p

/-- At a resume state, `CtNQR` is ScPPR's `CtNQ` (by definition). -/
theorem CtNQR.ctnq {σ : State Unit} (h : CtNQR σ) (hr : σ.schedulerAction = .resumeCurThread) :
    ∀ d p, σ.curThread ∉ σ.readyQueues d p := h hr

/-- **`CtNQR` at boot.** -/
theorem boot_ctNQR : CtNQR (initASt (Z := Unit)) := fun _ _ _ h => List.not_mem_nil h

end

end Fl4Proofs.P3.SInvV
