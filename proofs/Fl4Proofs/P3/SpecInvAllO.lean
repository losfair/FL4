/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, g1c): **OnlyIdle (l4v
`only_idle`) carried across the syscall entry and every kernel event**, spec side
only (namespace SInvAll, outside the JAtZ cone). The frame family is
SpecInvAllO1..O6 (`OIK N := IK (OIS N)`, `OIS N := TP (oiQ N)`, generated); the
idle pointer is constant by sg1's `IdK` family (SpecInvSgI6).

* `onlyIdle_iff : OnlyIdle σ ↔ OIS σ.idleThread σ` (definitional).
* `kentry_onlyIdle (c) : OnlyIdle σ → ∀ y ∈ (fl4KernelEntrySyscall true c σ).1,
  OnlyIdle y.2`, `kcall_onlyIdle (rep) (ev)` (every event): no premise.
  g1b's [J] premise `hoi` is gone.
-/
import Fl4Proofs.P3.SpecInvAllO6
import Fl4Proofs.P3.SpecInvSgI6
import Fl4Proofs.P3.SpecInvAllC

open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

theorem onlyIdle_iff (σ : State Unit) : OnlyIdle σ ↔ OIS σ.idleThread σ := Iff.rfl

/-- `OnlyIdle` from `OIS N` at a state whose idle pointer is `N`. -/
theorem onlyIdle_of_ois {N : ObjRef} {s : State Unit} (h : OIS N s) (hN : s.idleThread = N) : OnlyIdle s := by
  intro t x ht hs; rw [hN]; exact h t x ht hs

/-- **OnlyIdle across the syscall entry** (no premise). -/
theorem kentry_onlyIdle (c : Syscall) {σ : State Unit} (h : OnlyIdle σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, OnlyIdle y.2 := fun y hy =>
  onlyIdle_of_ois (oi_fl4KernelEntrySyscall (N := σ.idleThread) true c σ h y hy)
    (SInvG.idk_fl4KernelEntrySyscall (N := σ.idleThread) true c σ rfl y hy)

/-- **OnlyIdle across every kernel event** (`fl4CallKernel rep ev`, any event; no premise). -/
theorem kcall_onlyIdle (rep : Bool) (ev : Event) {σ : State Unit} (h : OnlyIdle σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, OnlyIdle y.2 := fun y hy =>
  onlyIdle_of_ois (oi_fl4CallKernel (N := σ.idleThread) rep ev σ h y hy)
    (SInvG.idk_fl4CallKernel (N := σ.idleThread) rep ev σ rfl y hy)

end

end Fl4Proofs.P3.SInvAll
