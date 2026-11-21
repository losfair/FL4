/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq2): **EpQAll at the exit
of the syscall entry and of every kernel event** (spec side only, outside the
`JAtZ` cone).

`epQAll_of` (SpecInvEqA) at the exit, from:
* `RPos` (this line's carried field: `kentry_rpos` / `kcall_rpos`, SpecInvEqS);
* `ScInv` (sb2's `kentry_scInv` / `kcall_scInv`);
* `EpQB` (nq3 / il2's `kentry_nqIL` / `kcall_nqIL`);
* `Rdy` at the exit, **taken as a hypothesis by name** (`hRy`): rd's whole-entry
  carry of `Rdy` (`kentry_rdy`) is proved by another line; it is the same
  statement shape, so it plugs in directly.
Every other premise is a carried invariant at the entry state (g1a's bundle) or
l4v's `ct_active` (`ha`, as in il2 / fo1 / g1a). No [J] / [P] / [W] / [S].
-/
import Fl4Proofs.P3.SpecInvEqS
import Fl4Proofs.P3.SpecInvSbT
import Fl4Proofs.P3.SpecInvNtfnQLX
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

/-- **EpQAll (and RPos) at every outcome of the syscall entry.** -/
theorem kentry_epQAll (c : Syscall) {σ : State Unit} (hP : RPos σ) (hR : SInvR.Rdy σ) (hS : SInvB.ScInv σ)
    (hU : SInvU.UtInv3 σ) (hV : VfhAll σ) (hL : SInvB.ScLive σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hN : NtfnQB σ ∧ EpQB σ)
    (hLT : IfLiveT σ)
    (hRy : ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.Rdy y.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, EpQAll y.2 ∧ RPos y.2 := by
  intro y hy
  have hp := kentry_rpos true c hP hR hS y hy
  exact ⟨epQAll_of (hRy y hy) (SInvB.kentry_scInv c hS hU hV hL y hy)
    (kentry_nqIL true c ha hN hU hLT y hy).2.1 hp, hp⟩

/-- **EpQAll (and RPos) at every outcome of every kernel event.** -/
theorem kcall_epQAll (rep : Bool) (ev : Event) {σ : State Unit} (hP : RPos σ) (hR : SInvR.Rdy σ)
    (hS : SInvB.ScInv σ) (hU : SInvU.UtInv3 σ) (hV : VfhAll σ) (hL : SInvB.ScLive σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hLT : IfLiveT σ)
    (hRy : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.Rdy y.2) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EpQAll y.2 ∧ RPos y.2 := by
  intro y hy
  have hp := kcall_rpos rep ev hP hR hS y hy
  exact ⟨epQAll_of (hRy y hy) (SInvB.kcall_scInv rep ev hS hU hV hL y hy)
    (kcall_nqIL rep ev ha hN hU hLT y hy).2.1 hp, hp⟩

end

end Fl4Proofs.P3.SInvE
