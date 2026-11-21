/- invA: NativeScope across the kernel entries (the frame lemmas: SpecInvNativeScopeF1..F6). -/
import Fl4Proofs.P3.SpecInvNativeScopeF6
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-! ## The entries -/


/-- **NativeScope across the syscall entry** (invA (b)). -/
theorem kentry_nativeScope (c : Syscall) {σ : State Unit} (h : NativeScopeS σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, NativeScopeS y.2 :=
  fun y hy => ns_fl4KernelEntrySyscall true c σ h y hy

/-- **NativeScope across every kernel event** (invA (c)): `fl4CallKernel rep ev`
for any event (interrupts, faults, the timer, syscalls without the FaultIP write). -/
theorem kcall_nativeScope (rep : Bool) (ev : Event) {σ : State Unit} (h : NativeScopeS σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, NativeScopeS y.2 :=
  fun y hy => ns_fl4CallKernel rep ev σ h y hy

/-- **NativeScope at boot** (invA (d)): the initial state `initASt`. -/
theorem boot_nativeScope : NativeScopeS (initASt (Z := Unit)) := by
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [nsQ]) | simp_all [nsQ]


end

end Fl4Proofs.P3.SInv
