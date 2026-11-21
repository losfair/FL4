/-
P3 (DESIGN.md §9), CSpace: **a null slot is not original** (`NullOrig`), the
invariant the deletion loop's zombie count-down needs at `J` (with `LiveJ`):
after deleting a zombie's last slot the slot is null, and so not in use.

* `NullOrig th m σ` [J]: every abstract slot holding a null cap has no
  original bit (l4v `valid_nullcaps` of `valid_mdb'`: a null CTE has
  `nullMDBNode`, whose `mdbRevocable` is false).
* `NullOrig.notInUse`: a null slot is not `InUse` (the original bits only on
  abstract slots, `JKern.orig`).
* Kept by the loop's steps: `NullOrig.of_same` (slots' caps and the original
  bits kept: the finalisations, preemption point, post deletion, by
  `orig_eq_of_slots` from `SlotsSame` and `CdtRel` before and after);
  `NullOrig.empty` (`empty_slot` clears the emptied slot's bit);
  `NullOrig.setCap` (a non-null cap written, the spec's `set_cap` keeps the
  bits); `NullOrig.swap` (`cap_swap_for_delete` swaps the caps and the
  bits: `capSwapForDelete_orig_val`).
-/
import Fl4Proofs.P3.XTopJointLiveKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section Spec
open Fl4Spec

theorem setOriginal_mem {sl : CslotPtr} {v : Bool} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setOriginal (Z := Unit) sl v σ).1) :
    x.2.isOriginalCap = Function.update σ.isOriginalCap sl v := by
  unfold setOriginal at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]

theorem no_setCdtF (c : Cdt) : NO (fun _ => False) (setCdt (Z := Unit) c) := by
  unfold setCdt
  exact no_get_put (fun σ => OKeep.refl _ σ)

/-- **`cap_swap` swaps the two slots' original bits.** -/
theorem capSwap_orig_val {c1 c2 : Cap} {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {σ : State Unit}
    {x : Unit × State Unit} (hx : x ∈ (capSwap (Z := Unit) c1 s1 c2 s2 σ).1) :
    x.2.isOriginalCap s1 = σ.isOriginalCap s2 ∧ x.2.isOriginalCap s2 = σ.isOriginalCap s1 := by
  unfold capSwap at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy5] at hx
  obtain ⟨y6, hy6, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy6] at hx
  obtain ⟨y7, hy7, hx⟩ := hx
  obtain ⟨y8, hy8, hx⟩ := hx
  obtain ⟨y9, hy9, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy9] at hx
  obtain ⟨y10, hy10, hx⟩ := hx
  have e11 := setOriginal_mem hx
  have e10 := setOriginal_mem hy10
  have k1 := no_setCap (d := fun _ => False) _ _ _ y1 hy1
  have k2 := no_setCap (d := fun _ => False) _ _ _ y2 hy2
  have k7 := no_setCdtF _ _ y7 hy7
  have k8 := no_doExtendedOp (d := fun _ => False) _ _ y8 hy8
  have hall : ∀ sl, y8.2.isOriginalCap sl = σ.isOriginalCap sl := fun sl =>
    (k8 sl id).trans ((k7 sl id).trans ((k2 sl id).trans (k1 sl id)))
  rw [e11, e10]
  simp only [Function.update_apply, if_neg hne, if_neg (Ne.symm hne), if_pos rfl]
  exact ⟨hall s2, hall s1⟩

/-- **`cap_swap_for_delete` of two slots swaps their original bits.** -/
theorem capSwapForDelete_orig_val {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {σ : State Unit}
    {x : Unit × State Unit} (hx : x ∈ (capSwapForDelete (Z := Unit) s1 s2 σ).1) :
    x.2.isOriginalCap s1 = σ.isOriginalCap s2 ∧ x.2.isOriginalCap s2 = σ.isOriginalCap s1 := by
  unfold capSwapForDelete NonDet.when at hx
  rw [if_pos hne] at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  have k1 := no_getCap (d := fun _ => False) s1 σ y1 hy1
  have k2 := no_getCap (d := fun _ => False) s2 _ y2 hy2
  obtain ⟨h1, h2⟩ := capSwap_orig_val hne hx
  exact ⟨h1.trans ((k2 s2 id).trans (k1 s2 id)), h2.trans ((k2 s1 id).trans (k1 s1 id))⟩

/-- `cap_swap_for_delete` keeps the other slots' bits. -/
theorem capSwapForDelete_orig_oth {s1 s2 : CslotPtr} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (capSwapForDelete (Z := Unit) s1 s2 σ).1) {sl : CslotPtr} (h1 : sl ≠ s1) (h2 : sl ≠ s2) :
    x.2.isOriginalCap sl = σ.isOriginalCap sl :=
  capSwapForDelete_orig s1 s2 σ x hx sl (fun h => h.elim h1 h2)

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`empty_slot` keeps `NullOrig`**: the emptied slot's bit cleared, the
other slots' caps and bits kept. -/
theorem NullOrig.empty {th : TypedHeap} (hP : Placed th) {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hN : NullOrig th (L.mem s) σ) (hR : StateRel th (L.mem s) σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    (hcn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hes : ((), σ') ∈ (Fl4Spec.emptySlot (Z := Unit) sl .nullCap σ).1)
    (hoth : ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y) :
    NullOrig th (L.mem s') σ' := by
  have hcs := (emptySlot_cdt_orig hR hA hcn hes).2
  intro sl' hA' h
  rw [hcs]
  show Function.update σ.isOriginalCap sl false sl' = false
  by_cases he : sl' = sl
  · subst he; simp
  · rw [Function.update_of_ne he]
    have hne : cslotAddr sl' ≠ cslotAddr sl := fun e => he (cslotAddr_inj hP hA' hA e)
    exact hN sl' hA' (by rw [← hoth _ hA'.isSlot hne]; exact h)

/-- **A non-null cap written by the spec's `set_cap` keeps `NullOrig`.** -/
theorem NullOrig.setCap {th : TypedHeap} (hP : Placed th) {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hN : NullOrig th m σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {ac : Fl4Spec.Cap}
    (hsc : Fl4Spec.setCap (Z := Unit) ac sl σ = ({((), σ')}, False))
    (hx : capV m' (cslotAddr sl) ≠ .Null)
    (hoth : ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV m' y = capV m y) : NullOrig th m' σ' := by
  have hk := no_setCap (d := fun _ => False) ac sl σ ((), σ') (by rw [hsc]; rfl)
  intro sl' hA' h
  rw [show σ'.isOriginalCap sl' = σ.isOriginalCap sl' from hk sl' id]
  have hne : cslotAddr sl' ≠ cslotAddr sl := fun e => hx (e ▸ h)
  exact hN sl' hA' (by rw [← hoth _ hA'.isSlot hne]; exact h)

/-- **The zombie at `sl` swapped with its first slot keeps `NullOrig`**
(the caps and the bits of the two slots swapped, the others kept). -/
theorem NullOrig.swap {th : TypedHeap} (hP : Placed th) {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hN : NullOrig th m σ) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {p zt n : U64} (hz : ZOK th p zt n)
    (hsc : Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ')}, False))
    (hx : capV m (cslotAddr sl) = .Zombie p zt n) (hpx : p ≠ cslotAddr sl)
    (hcv : ∀ y, IsSlot th y → capV m' y = if y = cslotAddr sl then capV m p
      else if y = p then capV m (cslotAddr sl) else capV m y) : NullOrig th m' σ' := by
  have hH : AbsSlot th (homeSl p zt) := home_abs hz
  have hHa : cslotAddr (homeSl p zt) = p := home_addr p _
  have hHne : homeSl p zt ≠ sl := fun e => hpx (by rw [← e, hHa])
  have hmem : ((), σ') ∈ (Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ).1 := by rw [hsc]; rfl
  obtain ⟨o1, o2⟩ := capSwapForDelete_orig_val hHne hmem
  intro sl' hA' h
  have h' := hcv _ hA'.isSlot
  rw [h] at h'
  by_cases e1 : cslotAddr sl' = cslotAddr sl
  · obtain rfl := cslotAddr_inj hP hA' hA e1
    rw [if_pos rfl] at h'
    show σ'.isOriginalCap sl' = false
    rw [o2]
    exact hN _ hH (by rw [hHa]; exact h'.symm)
  · rw [if_neg e1] at h'
    by_cases e2 : cslotAddr sl' = p
    · rw [if_pos e2, hx] at h'; cases h'
    · rw [if_neg e2] at h'
      have n1 : sl' ≠ homeSl p zt := fun e => e2 (by rw [e, hHa])
      have n2 : sl' ≠ sl := fun e => e1 (by rw [e])
      rw [capSwapForDelete_orig_oth hmem n1 n2]
      exact hN sl' hA' h'.symm

end

end

end Fl4Proofs.P3
