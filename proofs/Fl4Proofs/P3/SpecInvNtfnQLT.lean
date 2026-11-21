/-
P3 (DESIGN.md §9), invariant line G1 (il1): **IfLiveT gives nq3's [J]
IfLiveB**, and nq3's `_live` tops stated over IfLiveT (spec side only).

`IfLiveT` (SpecInvNtfnQL: every live TCB holds a thread cap) implies
`IfLiveB` (an IPC-blocked TCB inside an untyped region is named by some cap):
IPC-blocked states are live, and a thread cap names its TCB. The tops below
still take `IfLiveT σ` as a premise: carrying it across the entry
(`kentry_ifLiveT`) is the il1 handoff (KENTRY-PLAN il1).
-/
import Fl4Proofs.P3.SpecInvNtfnQH3
import Fl4Proofs.P3.SpecInvNtfnQLM
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

theorem ifLiveB_of {σ : State Unit} (h : IfLiveT σ) : IfLiveB σ :=
  fun _ _ hy hb _ => ifLiveT_objRefs h hy (liveSt_of_ipcBlk hb)

/-- `kentry_ntfnQB_live` over `IfLiveT`. -/
theorem kentry_ntfnQB_liveT (rep : Bool) (c : Syscall) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) (h : NtfnQB σ ∧ EpQB σ)
    (hU : SInvU.UtInv σ) (hU2 : SInvU.UtInv'' σ) (hL : IfLiveT σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, NtfnQB y.2 ∧ EpQB y.2 :=
  kentry_ntfnQB_live rep c ha h hU hU2 (ifLiveB_of hL)

/-- `kcall_ntfnQB_live` over `IfLiveT`. -/
theorem kcall_ntfnQB_liveT (rep : Bool) (ev : Event) {σ : State Unit}
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState))
    (h : NtfnQB σ ∧ EpQB σ) (hU : SInvU.UtInv σ) (hU2 : SInvU.UtInv'' σ) (hL : IfLiveT σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NtfnQB y.2 ∧ EpQB y.2 :=
  kcall_ntfnQB_live rep ev ha h hU hU2 (ifLiveB_of hL)

end

end Fl4Proofs.P3.SInv
