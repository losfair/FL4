/-
P3 (DESIGN.md §9), invariant line G1 (invA): **the bridge from
SpecInvNativeScope's `NativeScopeS` to IpcLeaves' `NativeScope`** (the form
the top's `hNS` / `hNSR` [S] name). A leaf importing both; everything else of
the invariant stays outside the JAtZ cone.
-/
import Fl4Proofs.P3.SpecInvNativeScope
import Fl4Proofs.P3.IpcLeaves
open Classical

namespace Fl4Proofs.P3.SInv

theorem nativeScopeS_iff (σ : Fl4Spec.State Unit) : NativeScopeS σ ↔ Fl4Proofs.P3.Endp.NativeScope σ :=
  Iff.rfl

/-- NativeScope across the syscall entry, in IpcLeaves' form. -/
theorem kentry_nativeScope' (c : Fl4Spec.Syscall) {σ : Fl4Spec.State Unit}
    (h : Fl4Proofs.P3.Endp.NativeScope σ) :
    ∀ y ∈ ((Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c) σ).1, Fl4Proofs.P3.Endp.NativeScope y.2 :=
  kentry_nativeScope c h

/-- NativeScope at boot, in IpcLeaves' form. -/
theorem boot_nativeScope' : Fl4Proofs.P3.Endp.NativeScope (Fl4Spec.initASt (Z := Unit)) := boot_nativeScope

end Fl4Proofs.P3.SInv
