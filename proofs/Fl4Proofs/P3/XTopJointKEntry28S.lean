/-
P3 (DESIGN.md §9), invariant line G3 (g3b), spec side only (imports
SpecInvNativeScopeF6 alone, outside the JAtZ cone): **`NativeScope` at the
states where `kernel_entryJ28` needs it**, from `NativeScope` at the entry
state (SInvB's `SInvA.ns`) by invA's NSK family.

* `SInvN.ns_front`: at every outcome of the front end (the `FaultIP` write,
  then the handled syscall event with the preemption path on an error), i.e.
  XTopJointKEntry's `specFront c σ`: where `finish` starts.
* `SInvN.ns_of_kheap`: `NativeScope` reads only the heap.
-/
import Fl4Proofs.P3.SpecInvNativeScopeF6
open Classical

namespace Fl4Proofs.P3.SInvN
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 2000000

/-- **`NativeScope` at the front end's outcomes** (module docstring). -/
theorem ns_frontK (t : ObjRef) (rep : Bool) (c : Syscall) :
    NSK (fl4SyscallFaultIP (Z := Unit) t >>= fun _ =>
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c))
        (fun _ => withoutPreemption preemptionPath))) := by
  ns_auto

/-- **`NativeScope` at every outcome of the front end from `NativeScope` at
the entry** (module docstring). -/
theorem ns_front (rep : Bool) (c : Syscall) {σ : State Unit} (h : NativeScopeS σ) :
    ∀ y ∈ ((fl4SyscallFaultIP (Z := Unit) σ.curThread >>= fun _ =>
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c))
        (fun _ => withoutPreemption preemptionPath))) σ).1, NativeScopeS y.2 :=
  fun y hy => ns_frontK σ.curThread rep c σ h y hy

/-- `NativeScope` reads only the heap. -/
theorem ns_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) (h : NativeScopeS σ) : NativeScopeS σ' := by
  intro p x hp
  rw [e] at hp
  exact h p x hp

end

end Fl4Proofs.P3.SInvN
