/-
P3 (DESIGN.md §9), CSpace: FL4's parent test at an insertion is l4v's
`should_be_parent_of` (`sbp_eq`), for a new cap of the source's shape whose
region does not wrap; on the way, FL4's region test of such caps implies
the spec's `same_region_as` (`srB_spec_self`).
-/
import Fl4Proofs.P3.MdbOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem srB_ut (p sb fi fi' : U64) (d d' : Bool) :
    srB (.Untyped p sb fi d) (.Untyped p sb fi' d') = decide (p ≤ core.num.U64.wrapping_add p (maskF sb)) := by
  apply srB_of_eq
  simp [objects.same_region_as, objects.cap_is_physical, capability.Cap.ptr, objects.cap_size_bits, mask_eq, lift]

theorem srB_frame (p : U64) (sz : capability.FrameSize) (r r' : U64) (d d' m m' e e' : Bool) (a a' v v' : U64) :
    srB (.Frame p sz r d m e a v) (.Frame p sz r' d' m' e' a' v') =
      decide (p ≤ core.num.U64.wrapping_add p (maskF (fbitsF sz))) := by
  apply srB_of_eq
  simp [objects.same_region_as, frame_bits_eq, mask_eq, lift]

theorem maskF_val {b : U64} (h : b.val < 64) : (maskF b).val = 2 ^ b.val - 1 := by
  obtain ⟨m, hm, hv⟩ := spec_exists (mask_spec b h)
  have h1 := mask_eq b
  rw [objects_mask_eq, hm] at h1
  have : maskF b = m := by simpa using h1.symm
  rw [this, hv]

/-- No wrap: `p ≤ p + (2^n - 1)` as words is the spec's `r ≤ r + (1 << n) - 1`. -/
theorem nowrap_spec {p m : U64} {n : Nat} (hn : n < 64) (hm : m.val = 2 ^ n - 1)
    (h : p ≤ core.num.U64.wrapping_add p m) :
    p.bv ≤ p.bv + ((1 : BitVec 64) <<< n) - 1 := by
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hp : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have e : p.bv + ((1 : BitVec 64) <<< n) - 1 = (core.num.U64.wrapping_add p m).bv := by
    apply BitVec.eq_of_toNat_eq
    rw [core.num.U64.wrapping_add_bv_eq]
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft]
    simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.one_shiftLeft, Nat.mod_eq_of_lt hp]
    have hmv : m.bv.toNat = 2 ^ n - 1 := hm
    rw [hmv]
    have := p.bv.isLt
    omega
  rw [e]; exact h

theorem natCast_shl_one (n : Nat) : (((1 <<< n : Nat)) : BitVec 64) = (1 : BitVec 64) <<< n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.one_shiftLeft]

theorem fbitsF_val (sz : capability.FrameSize) :
    (fbitsF sz).val = Fl4Spec.pageBitsForSize (frameSizeOf sz) := by
  have h := frame_bits_eq sz
  cases sz <;> simp [capability.FrameSize.bits] at h <;> rw [← h] <;> rfl

theorem srB_spec_self (c d : capability.Cap) (hsh : shape d = shape c) (hs : srB c c = true) (he : EncWf c) :
    Fl4Spec.sameRegionAs (absCap c) (absCap d) := by
  cases c <;> cases d <;> simp [shape] at hsh
  case Untyped.Untyped p sb fi dev p' sb' fi' dev' =>
    obtain ⟨rfl, rfl⟩ := hsh
    rw [srB_ut] at hs
    have hsb : sb'.val < 64 := he.2
    have h := nowrap_spec hsb (maskF_val hsb) (by simpa using hs)
    simp only [absCap, Fl4Spec.sameRegionAs, Fl4Spec.objSize, Fl4Spec.isPhysical, Fl4Spec.objRefOf,
      natCast_shl_one]
    exact ⟨trivial, BitVec.le_refl _, h, BitVec.le_refl _⟩
  case Frame.Frame p sz r dev m ept a v p' sz' r' dev' m' ept' a' v' =>
    obtain ⟨rfl, rfl⟩ := hsh
    rw [srB_frame] at hs
    have hb : (fbitsF sz').val < 64 := by
      have := frame_bits_eq sz'; cases sz' <;> simp [capability.FrameSize.bits] at this <;> rw [← this] <;> decide
    have h := nowrap_spec hb (maskF_val hb) (by simpa using hs)
    rw [fbitsF_val] at h
    simp [absCap, Fl4Spec.sameRegionAs, Fl4Spec.archSameRegionAs]
    exact h
  case Null.Null => exact absurd hs (by rw [srB_of_eq (v := false) rfl]; simp)
  case Zombie.Zombie => exact absurd hs (by rw [srB_of_eq (v := false) rfl]; simp)
  all_goals (try casesm* _ ∧ _); subst_vars
  all_goals simp [absCap, Fl4Spec.sameRegionAs, Fl4Spec.isEpCap, Fl4Spec.isNtfnCap, Fl4Spec.objRefOf,
    Fl4Spec.isCnodeCap, Fl4Spec.bitsOf, Fl4Spec.isThreadCap, Fl4Spec.isSchedContextCap, Fl4Spec.archSameRegionAs]

theorem u64_beq (x y : U64) : (x == y) = decide (x.bv = y.bv) := by
  rw [Bool.eq_iff_iff]; simp [UScalar.eq_equiv_bv_eq]

theorem sbp_eq (srcC c : capability.Cap) (io : Bool) (hsh : shape c = shape srcC)
    (hs : srB srcC srcC = true) (he : EncWf srcC) (hk : SameBadgeKind c srcC) :
    decide (Fl4Spec.shouldBeParentOf (absCap srcC) io (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) = isPF io srcC c (revF c srcC) := by
  have hsr := srB_spec_self srcC c hsh hs he
  have hsrB : srB srcC c = true := by rw [srB_congr rfl hsh]; exact hs
  have hrv : decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)) = revF c srcC := by
    have := revF_spec c srcC hk
    cases h : revF c srcC <;> simp_all
  rw [hrv]
  unfold Fl4Spec.shouldBeParentOf isPF
  rw [hsrB]
  simp only [eq_true hsr, true_and, Bool.and_true]
  cases srcC <;> cases c <;> simp [shape] at hsh
  all_goals (try casesm* _ ∧ _); subst_vars
  all_goals cases io <;> simp [absCap, isBadged, badgeF, Fl4Spec.capEpBadge, UScalar.eq_equiv_bv_eq,
    Fl4Spec.shouldBeArchParentOf, u64_beq]
end

end Fl4Proofs.P3
