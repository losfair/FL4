/-
P3 (DESIGN.md §9), CSpace: FL4's `same_object_as` (`soB`) is l4v's
`same_object_as` on the abstract caps (`soB_iff`), for well-formed caps, a
frame cap's region not wrapping. TCB ThreadControl's `check_cap_at` tests
are these.
-/
import Fl4Proofs.P3.FinDefs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

set_option maxHeartbeats 4000000 in
theorem soB_iff_nf (a b : capability.Cap) (ha : CapWf a) (hb : CapWf b) (hnu : isUt a = false)
    (hnf : isFrame a = false) :
    soB a b = true ↔ Fl4Spec.sameObjectAs (absCap a) (absCap b) := by
  cases a <;> simp [isUt, isFrame] at hnu hnf <;> cases b <;> simp only [soB] <;>
    (try rw [srB_of_eq (by simp [objects.same_region_as]; rfl)]) <;>
    simp [Fl4Spec.sameObjectAs, Fl4Spec.sameRegionAs, absCap, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.objRefOf,
      Fl4Spec.isCnodeCap, Fl4Spec.bitsOf, Fl4Spec.isThreadCap, Fl4Spec.isSchedContextCap, Fl4Spec.archSameRegionAs,
      Fl4Spec.sameAobjectAs, Fl4Spec.isArchCap, Fl4Spec.isIrqControlDescendant]
  all_goals (rw [show ∀ a b, srB a b = true ↔ objects.same_region_as a b = ok true from fun a b => by
    rw [srB_eq]; simp])
  all_goals (simp [objects.same_region_as, UScalar.eq_equiv_bv_eq, apply_ite, eq_comm])
  case CNode.CNode => intro _; exact ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  case IrqHandler.IrqHandler i j =>
    simp only [CapWf] at ha hb
    constructor
    · intro h; rw [h]
    · intro h
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth] at this
      have h1 : i.bv.toNat < 256 := ha
      have h2 : j.bv.toNat < 256 := hb
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
      exact this
  case SchedContext.SchedContext p sb p' sb' =>
    simp only [CapWf] at ha hb
    intro _
    constructor
    · intro h; have := congrArg BitVec.toNat h; show sb.val - _ = sb'.val - _; rw [show sb.val = sb'.val from this]
    · intro h; apply BitVec.eq_of_toNat_eq; show sb.val = sb'.val; omega
  case IoPort.IoPort f l vc f' l' vc' =>
    simp only [CapWf] at ha hb
    have k : ∀ x y : U64, x.val < 2 ^ 16 → y.val < 2 ^ 16 →
        (x.bv = y.bv ↔ (BitVec.setWidth 16 x.bv : BitVec 16) = BitVec.setWidth 16 y.bv) := by
      intro x y hx hy
      constructor
      · intro h; rw [h]
      · intro h
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_setWidth] at this
        have h1 : x.bv.toNat < 2 ^ 16 := hx
        have h2 : y.bv.toNat < 2 ^ 16 := hy
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
        exact this
    rw [k f f' ha.1 hb.1, k l l' ha.2 hb.2]
  case Ept.Ept p level m asid va p' level' m' asid' va' =>
    intro _
    exact ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩

/-- **FL4's `same_object_as` is the spec's**, for well-formed caps, a frame
cap's region not wrapping (`sameObjectAs` with itself). -/
theorem soB_iff (a b : capability.Cap) (ha : CapWf a) (hb : CapWf b)
    (hfw : isFrame a = true → Fl4Spec.sameObjectAs (absCap a) (absCap a)) :
    soB a b = true ↔ Fl4Spec.sameObjectAs (absCap a) (absCap b) := by
  cases hu : isUt a
  · cases hf : isFrame a
    · exact soB_iff_nf a b ha hb hu hf
    · obtain ⟨p, sz, r, d, m, ep, asd, v, rfl⟩ : ∃ p sz r d m ep asd v, a = .Frame p sz r d m ep asd v := by
        cases a <;> simp [isFrame] at hf; exact ⟨_, _, _, _, _, _, _, _, rfl⟩
      have hw := hfw rfl
      simp only [absCap, Fl4Spec.sameObjectAs, Fl4Spec.sameAobjectAs] at hw
      cases b <;> simp only [soB] <;>
        (try rw [srB_of_eq (by simp [objects.same_region_as]; rfl)]) <;>
        simp [Fl4Spec.sameObjectAs, Fl4Spec.sameRegionAs, absCap, Fl4Spec.sameAobjectAs, Fl4Spec.archSameRegionAs]
      rename_i p' sz' r' d' m' ep' asd' v'
      have hfs : ∀ a b : capability.FrameSize, frameSizeOf a = frameSizeOf b ↔ a = b := by
        intro a b; cases a <;> cases b <;> simp [frameSizeOf]
      have hbv : ∀ x y : U64, x.bv = y.bv ↔ x = y :=
        fun x y => ⟨fun h => UScalar.eq_of_val_eq (congrArg BitVec.toNat h), fun h => h ▸ rfl⟩
      simp only [hfs, hbv, fsB_iff]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl, hw.2⟩
      · rintro ⟨rfl, rfl, rfl, -⟩; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨p, sb, fi, d, rfl⟩ : ∃ p sb fi d, a = .Untyped p sb fi d := by
      cases a <;> simp [isUt] at hu; exact ⟨_, _, _, _, rfl⟩
    simp [soB, absCap, Fl4Spec.sameObjectAs]

end

end Fl4Proofs.P3
