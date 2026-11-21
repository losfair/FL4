/-
P3 (DESIGN.md §9), invariant line G1 (sg1): **the bridge from SpecInvSgE's
`SpecGlobS` to SpecGlob.lean's `SpecGlob`** (the form `WJ` / `JEntryAt.sg` /
`decode_invocation_cnodeJ_steps`'s `hsg` take). A leaf importing both (SpecGlob's
module lies in the JAtZ cone); everything else of the SpecGlob line stays outside
it.
-/
import Fl4Proofs.P3.SpecInvSgE
import Fl4Proofs.P3.SpecGlob
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec

theorem sg_capAt (σ : State Unit) (p : ObjRef) (c : CnodeIndex) :
    SInvU.capAt σ (p, c) = Fl4Proofs.P3.capOpt (σ.kheap p) c := by
  unfold SInvU.capAt
  cases σ.kheap p with
  | none => rfl
  | some o => cases o <;> first | rfl | (simp only [SInvU.capView, Fl4Proofs.P3.capOpt]; split <;> rfl)

theorem isFrameCap_iff (a : Cap) : IsFrameCap a ↔ Fl4Proofs.P3.IsPageCap a := by
  cases a with
  | archObjectCap ac => cases ac <;> exact Iff.rfl
  | _ => exact Iff.rfl

theorem specGlobS_iff (σ : State Unit) : SpecGlobS σ ↔ Fl4Proofs.P3.SpecGlob σ := by
  constructor
  · intro h
    refine ⟨fun irq a ha => h.irq irq a (by rw [sg_capAt]; exact ha), fun p cref a ha hp irq => ?_,
      fun p cref a ha hp => ?_⟩
    · exact h.ref p cref a (by rw [sg_capAt]; exact ha) (fun e => hp ((isFrameCap_iff a).1 e)) irq
    · exact h.idle p cref a (by rw [sg_capAt]; exact ha) (fun e => hp ((isFrameCap_iff a).1 e))
  · intro h
    refine ⟨fun irq a ha => h.irq irq a (by rw [← sg_capAt]; exact ha), fun p cref a ha hp irq => ?_,
      fun p cref a ha hp => ?_⟩
    · exact h.ref p cref a (by rw [← sg_capAt]; exact ha) (fun e => hp ((isFrameCap_iff a).2 e)) irq
    · exact h.idle p cref a (by rw [← sg_capAt]; exact ha) (fun e => hp ((isFrameCap_iff a).2 e))

/-- **SpecGlob across the syscall entry**, in SpecGlob.lean's form. -/
theorem kentry_specGlob' (c : Syscall) {σ : State Unit} (hG : Fl4Proofs.P3.SpecGlob σ) (hI : IdleOutV σ)
    (hU : SInvU.UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, Fl4Proofs.P3.SpecGlob y.2 ∧ IdleOutV y.2 := by
  intro y hy
  obtain ⟨h1, h2⟩ := kentry_specGlob c ((specGlobS_iff σ).2 hG) hI hU y hy
  exact ⟨(specGlobS_iff _).1 h1, h2⟩

/-- **SpecGlob across every kernel event**, in SpecGlob.lean's form. -/
theorem kcall_specGlob' (rep : Bool) (ev : Event) {σ : State Unit} (hG : Fl4Proofs.P3.SpecGlob σ)
    (hI : IdleOutV σ) (hU : SInvU.UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, Fl4Proofs.P3.SpecGlob y.2 ∧ IdleOutV y.2 := by
  intro y hy
  obtain ⟨h1, h2⟩ := kcall_specGlob rep ev ((specGlobS_iff σ).2 hG) hI hU y hy
  exact ⟨(specGlobS_iff _).1 h1, h2⟩

end Fl4Proofs.P3.SInvG
