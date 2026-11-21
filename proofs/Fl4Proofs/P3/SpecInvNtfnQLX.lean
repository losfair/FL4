/-
P3 (DESIGN.md §9), invariant line G1 (il2): **the tops carrying
`NtfnQB ∧ EpQB ∧ IfLiveT`** across the syscall entry and every kernel event
(spec side only).

`ha` is l4v's `ct_active` (the current thread is a TCB in an active state; for
an interrupt event it may be the idle thread), `hU : UtInv3 σ` is carried by
ut8's `kentry_utInv2` / `kcall_utInv2`, NtfnQB ∧ EpQB and IfLiveT are carried
here. No other premise: `PerfGapIL` (the untyped and arch performs) is proved
(`perfGapIL`, SpecInvNtfnQLA).
-/
import Fl4Proofs.P3.SpecInvNtfnQLS
import Fl4Proofs.P3.SpecInvNtfnQLA
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

/-- **IfLiveT kept by the syscall entry** (no premise beyond `ha`, the carried invariants). -/
theorem kentry_ifLiveT (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, IfLiveT y.2 :=
  kentry_ifLiveT_of perfGapIL rep c ha hN hU h

/-- **IfLiveT kept by every kernel event** (no premise beyond `ha`, the carried invariants). -/
theorem kcall_ifLiveT (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, IfLiveT y.2 :=
  kcall_ifLiveT_of perfGapIL rep ev ha hN hU h

/-- **NtfnQB ∧ EpQB ∧ IfLiveT kept by the syscall entry** (nq3's `_live` top with
IfLiveT now carried; `UtInv3` from ut8). -/
theorem kentry_nqIL (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState)
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, NtfnQB y.2 ∧ EpQB y.2 ∧ IfLiveT y.2 := by
  have ha' : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState := by
    obtain ⟨x0, hx0, ha0⟩ := ha
    intro x hx; rw [hx0] at hx; cases hx; exact ha0
  intro y hy
  have h1 := kentry_ntfnQB_liveT rep c ha' hN hU.1.1.1 hU.1 h y hy
  exact ⟨h1.1, h1.2, kentry_ifLiveT rep c ha hN hU h y hy⟩

/-- **NtfnQB ∧ EpQB ∧ IfLiveT kept by every kernel event.** -/
theorem kcall_nqIL (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hN : NtfnQB σ ∧ EpQB σ) (hU : UtInv3 σ) (h : IfLiveT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NtfnQB y.2 ∧ EpQB y.2 ∧ IfLiveT y.2 := by
  have ha' : ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState) := by
    obtain ⟨x0, hx0, ha0⟩ := ha
    intro x hx; rw [hx0] at hx; cases hx; exact ha0
  intro y hy
  have h1 := kcall_ntfnQB_liveT rep ev ha' hN hU.1.1.1 hU.1 h y hy
  exact ⟨h1.1, h1.2, kcall_ifLiveT rep ev ha hN hU h y hy⟩

end

end Fl4Proofs.P3.SInv
