/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut1): **the writers of
the untyped invariant that keep it on their own** (spec side only).

`UtInv` (SpecInvUt) is downward closed: removing an untyped cap, removing a
heap object, raising a free index (up to the size) or setting an original flag
keeps all five facts, and adding a heap object keeps them when the address lies
in no untyped cap's free part (`CapShrink`, `utInvV_shrink`). So the writers
below are leaves of an `IK UtInv` proof with no side condition, or with one
read at the same state:
* `ik_setCap_nonUt`: `set_cap` of a cap that is not an untyped cap (every
  `set_cap` of the spec but the untyped ones: zombies, nulls, arch updates,
  TCB installs, IRQ / ASID / IO-port caps);
* `ikp_setCap_raise`: `set_cap` of the slot's own untyped cap with a larger
  free index up to the size (`invoke_untyped`'s first write,
  `set_untyped_cap_as_full`);
* `ik_deleteObjects_utInv`: `delete_objects` of any range;
* `ik_setOriginal_true`;
* `ikp_retype_utInv`: `retype_region` at addresses that held no object and lie
  in no free part; `utRet_new` gives that for a decoded non-reset retype after
  the free index is raised (UtDisj for the other caps).
-/
import Fl4Proofs.P3.SpecInvUt
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Shrinking the untyped cap state -/

/-- The view `w'` has no more untyped room than `w`: every new heap address is
in no free part of `w`, every untyped cap of `w'` is one of `w` in the same slot
with a free index at least as large (at most the size), the CDT is the same and
no original flag of `w` is cleared. -/
structure CapShrink (w' w : UView) : Prop where
  keys : ∀ p, w'.1 p = true → w.1 p = true ∨
    ∀ sl d b n f, w.2.1 sl = some (.untypedCap d b n f) → p.toNat ∉ utFr b n f
  caps : ∀ sl d b n f', w'.2.1 sl = some (.untypedCap d b n f') →
    ∃ f, w.2.1 sl = some (.untypedCap d b n f) ∧ f ≤ f' ∧ f' ≤ 2 ^ n
  cdt : w'.2.2.1 = w.2.2.1
  orig : ∀ sl, w.2.2.2 sl = true → w'.2.2.2 sl = true

theorem utFr_mono {b : ObjRef} {n f f' k : Nat} (hf : f ≤ f') (hk : k ∈ utFr b n f') : k ∈ utFr b n f :=
  ⟨by have := hk.1; omega, hk.2⟩

theorem utInvV_shrink {w' w : UView} (h : CapShrink w' w) (hI : UtInvV w) : UtInvV w' := by
  obtain ⟨hF, hW, hD, hDe, hO⟩ := hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sl d b n f' hc p hp hk
    obtain ⟨f, hc0, hff, -⟩ := h.caps sl d b n f' hc
    rcases h.keys p hp with hp0 | hnew
    · exact hF sl d b n f hc0 p hp0 (utFr_mono hff hk)
    · exact hnew sl d b n f hc0 (utFr_mono hff hk)
  · intro sl d b n f' hc
    obtain ⟨f, hc0, -, hf'⟩ := h.caps sl d b n f' hc
    obtain ⟨h1, h2, -⟩ := hW sl d b n f hc0
    exact ⟨h1, h2, hf'⟩
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 k hk1 hk2
    obtain ⟨g1, hg1, hle1, -⟩ := h.caps s1 d1 b1 n1 f1 hc1
    obtain ⟨g2, hg2, hle2, -⟩ := h.caps s2 d2 b2 n2 f2 hc2
    exact hD s1 s2 d1 b1 n1 g1 d2 b2 n2 g2 hne hg1 hg2 k (utFr_mono hle1 hk1) (utFr_mono hle2 hk2)
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 hov
    obtain ⟨g1, hg1, hle1, -⟩ := h.caps s1 d1 b1 n1 f1 hc1
    obtain ⟨g2, hg2, hle2, -⟩ := h.caps s2 d2 b2 n2 f2 hc2
    rw [h.cdt]
    rcases hDe s1 s2 d1 b1 n1 g1 d2 b2 n2 g2 hne hg1 hg2 hov with ⟨hd, hr⟩ | ⟨hd, hr⟩
    · exact Or.inl ⟨hd, fun k hk hk' => hr k hk (utFr_mono hle1 hk')⟩
    · exact Or.inr ⟨hd, fun k hk hk' => hr k hk (utFr_mono hle2 hk')⟩
  · intro sl d b n f' hc
    obtain ⟨f, hc0, -⟩ := h.caps sl d b n f' hc
    exact h.orig sl (hO sl d b n f hc0)

/-- A computation whose every outcome shrinks the untyped cap state keeps `UtInv`. -/
theorem ik_utInv_of_shrink {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ σ x, x ∈ (m σ).1 → UtInv σ → CapShrink (uV x.2) (uV σ)) : IK UtInv m :=
  fun σ hσ x hx => utInvV_shrink (h σ x hx hσ) hσ

/-- A cap that did not change: its free index is at most the size (UtWf). -/
theorem same_cap {σ : State Unit} (hI : UtInv σ) {sl : CslotPtr} {d : Bool} {b : ObjRef} {n f : Nat}
    (hc : capAt σ sl = some (.untypedCap d b n f)) :
    ∃ f0, capAt σ sl = some (.untypedCap d b n f0) ∧ f0 ≤ f ∧ f ≤ 2 ^ n :=
  ⟨f, hc, le_refl _, (hI.2.1 sl d b n f hc).2.2⟩

/-! ## `delete_objects` -/

theorem ik_deleteObjects_utInv (ptr : Word) (bits : Nat) : IK UtInv (deleteObjects (Z := Unit) ptr bits) :=
  ik_utInv_of_shrink fun σ x hx hI => by
    obtain ⟨ms, e⟩ := deleteObjects_out hx
    have hk : ∀ p, x.2.kheap p = if p ∈ delR ptr bits then none else σ.kheap p := by
      rw [e]; intro p; rfl
    refine ⟨fun p hp => Or.inl ?_, fun sl d b n f' hc => ?_, by rw [e]; rfl, fun sl h => by rw [e]; exact h⟩
    · have hp' : (x.2.kheap p).isSome = true := hp
      rw [hk p] at hp'
      split_ifs at hp' <;> first | exact hp' | simp at hp'
    · have hc' : capAt x.2 sl = some (.untypedCap d b n f') := hc
      unfold capAt at hc'
      rw [hk sl.1] at hc'
      split_ifs at hc' <;> first | exact same_cap hI hc' | simp at hc'

/-! ## `set_cap` -/

theorem setObject_out {p : ObjRef} {o : KernelObject} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ old, σ.kheap p = some old ∧ y.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨old, z2⟩ := z
  simp only at hk hs; subst hs
  obtain ⟨w, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨u, hu, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hu] at hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨old, hk, rfl⟩

theorem capAt_upd (σ : State Unit) (o : ObjRef) (O : KernelObject) (sl : CslotPtr) :
    capAt { σ with kheap := Function.update σ.kheap o (some O) } sl =
      if sl.1 = o then capView O sl.2 else capAt σ sl := by
  unfold capAt
  by_cases h : sl.1 = o
  · simp only [h, Function.update_self, if_true]
  · simp only [Function.update_of_ne h, if_neg h]

theorem dom_update_some {cn : CnodeContents} {r : CnodeIndex} (hr : r ∈ dom cn) (c : Cap) :
    dom (Function.update cn r (some c)) = dom cn := by
  ext x
  by_cases e : x = r
  · subst e; simp only [dom, Set.mem_setOf_eq, Function.update_self]
    exact ⟨fun _ => hr, fun _ => by simp⟩
  · simp only [dom, Set.mem_setOf_eq, Function.update_of_ne e]

/-- The outcome of `set_cap`: the heap addresses, the CDT and the original
flags are kept; every other slot's cap is kept; the written slot holds its old
cap or the new one. -/
theorem setCap_out {c : Cap} {sl : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setCap (Z := Unit) c sl σ).1) :
    (∀ p, (y.2.kheap p).isSome = (σ.kheap p).isSome) ∧ (∀ sl', sl' ≠ sl → capAt y.2 sl' = capAt σ sl') ∧
      (capAt y.2 sl = capAt σ sl ∨ capAt y.2 sl = some c) ∧ y.2.cdt = σ.cdt ∧
      y.2.isOriginalCap = σ.isOriginalCap := by
  obtain ⟨o, r⟩ := sl
  unfold setCap at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨obj, z2⟩ := z
  simp only at hk hs; subst hs
  dsimp only at hy
  -- the object written
  have key : ∃ O, y ∈ (setObject (Z := Unit) o O z2).1 ∧ (∀ j, j ≠ r → capView O j = capView obj j) ∧
      (capView O r = capView obj r ∨ capView O r = some c) := by
    cases obj with
    | cnode sz cn =>
      dsimp only at hy
      split_ifs at hy with hcnd
      · obtain ⟨w, hw, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 hw
        have hwf : wellFormedCnodeN sz (Function.update cn r (some c)) := by
          unfold wellFormedCnodeN; rw [dom_update_some hcnd.1]; exact hcnd.2
        refine ⟨_, hy, fun j hj => ?_, Or.inr ?_⟩
        · simp only [capView_cnode, if_pos hwf, if_pos hcnd.2, Function.update_of_ne hj]
        · simp only [capView_cnode, if_pos hwf, Function.update_self]
      · first | exact hy.elim | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
    | tcb t =>
      dsimp only at hy
      split_ifs at hy with h0 h1 h2 h3 h4 h5 <;>
        first
        | exact hy.elim
        | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
        | (obtain ⟨w, hw, hy⟩ := hy
           obtain rfl := Set.mem_singleton_iff.1 hw
           refine ⟨_, hy, fun j hj => ?_, ?_⟩
           · simp only [capView_tcb, tcbCnodeMap, Function.update_apply]
             split_ifs <;> first | rfl | (exfalso; subst_vars; exact hj rfl)
           · simp only [capView_tcb, tcbCnodeMap, Function.update_apply]
             subst_vars
             split_ifs <;> first | (left; rfl) | (right; rfl))
    | _ => first | exact hy.elim | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
  obtain ⟨O, hyO, hj, hr⟩ := key
  obtain ⟨old, hold, e⟩ := setObject_out hyO
  have hkeys : ∀ p, (y.2.kheap p).isSome = (z2.kheap p).isSome := by
    intro p; rw [e]
    by_cases h : p = o
    · subst h; simp only [Function.update_self, hk]; rfl
    · simp only [Function.update_of_ne h]
  refine ⟨hkeys, fun sl' hne => ?_, ?_, by rw [e], by rw [e]⟩
  · rw [e, capAt_upd]
    split_ifs with h1
    · obtain ⟨p', j⟩ := sl'
      simp only at h1; subst h1
      have hjr : j ≠ r := fun h => hne (by rw [h])
      rw [hj j hjr]; unfold capAt; simp only [hk]
    · rfl
  · rw [e, capAt_upd, if_pos rfl]
    have hc0 : capAt z2 (o, r) = capView obj r := by unfold capAt; simp only [hk]
    rw [hc0]; exact hr

/-- **`set_cap` of a cap that is not untyped keeps `UtInv`.** -/
theorem ik_setCap_nonUt (c : Cap) (sl : CslotPtr) (hc : ∀ d b n f, c ≠ .untypedCap d b n f) :
    IK UtInv (setCap (Z := Unit) c sl) :=
  ik_utInv_of_shrink fun σ x hx hI => by
    obtain ⟨hk, hoth, hsl, hcdt, horig⟩ := setCap_out hx
    refine ⟨fun p hp => Or.inl ?_, fun sl' d b n f' hcap => ?_, hcdt,
      fun s h => by show x.2.isOriginalCap s = true; rw [horig]; exact h⟩
    · show (σ.kheap p).isSome = true; rw [← hk p]; exact hp
    · have hcap' : capAt x.2 sl' = some (.untypedCap d b n f') := hcap
      by_cases e : sl' = sl
      · subst e
        rcases hsl with h | h
        · rw [h] at hcap'; exact same_cap hI hcap'
        · rw [h] at hcap'; cases hcap'; exact absurd rfl (hc d b n f')
      · rw [hoth sl' e] at hcap'; exact same_cap hI hcap'

/-- **`set_cap` raising the free index of the slot's own untyped cap (up to the
size) keeps `UtInv`** (`invoke_untyped`'s first write, `set_untyped_cap_as_full`). -/
theorem ikp_setCap_raise {σ : State Unit} {sl : CslotPtr} {d : Bool} {b : ObjRef} {n f f' : Nat}
    (hc0 : capAt σ sl = some (.untypedCap d b n f)) (hff : f ≤ f') (hf' : f' ≤ 2 ^ n) :
    IKp UtInv σ (setCap (Z := Unit) (.untypedCap d b n f') sl) := by
  intro hI x hx
  refine utInvV_shrink ?_ hI
  obtain ⟨hk, hoth, hsl, hcdt, horig⟩ := setCap_out hx
  refine ⟨fun p hp => Or.inl ?_, fun sl' d' b' n' g hcap => ?_, hcdt,
    fun s h => by show x.2.isOriginalCap s = true; rw [horig]; exact h⟩
  · show (σ.kheap p).isSome = true; rw [← hk p]; exact hp
  · have hcap' : capAt x.2 sl' = some (.untypedCap d' b' n' g) := hcap
    by_cases e : sl' = sl
    · subst e
      rcases hsl with h | h
      · rw [h] at hcap'; exact same_cap hI hcap'
      · rw [h] at hcap'; cases hcap'; exact ⟨f, hc0, hff, hf'⟩
    · rw [hoth sl' e] at hcap'; exact same_cap hI hcap'

/-! ## Original flags -/

theorem ik_setOriginal_true (sl : CslotPtr) : IK UtInv (setOriginal (Z := Unit) sl true) := by
  unfold setOriginal
  refine ik_gets_bind fun σ => ikp_modify fun hI => utInvV_shrink ?_ hI
  refine ⟨fun p hp => Or.inl hp, fun sl' d b n f' hc => same_cap hI hc, rfl, fun s h => ?_⟩
  show Function.update σ.isOriginalCap sl true s = true
  by_cases e : s = sl
  · subst e; simp
  · rw [Function.update_of_ne e]; exact h

/-! ## `retype_region` -/

/-- A new object holds no untyped cap. -/
theorem default_noUt {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (dm : Domain)
    (i : CnodeIndex) (d : Bool) (b : ObjRef) (m f : Nat) :
    capView (defaultObject ty dev n dm) i ≠ some (.untypedCap d b m f) := by
  intro h
  cases ty with
  | untyped => exact hty rfl
  | capTableObject =>
    simp only [defaultObject, capView_cnode] at h
    split_ifs at h <;> (try simp only [emptyCnode] at h) <;> (try split_ifs at h) <;> cases h
  | tcbObject =>
    simp only [defaultObject, capView_tcb, tcbCnodeMap, defaultTcb, Function.update_apply] at h
    split_ifs at h <;> cases h
  | _ => cases h

/-- **`retype_region` at fresh addresses outside every free part keeps `UtInv`.** -/
theorem ikp_retype_utInv {σ : State Unit} {bA : ApiObjectType → Nat → Nat} {rb : ObjRef} {n oB : Nat}
    {ty : ApiObjectType} {dev : Bool}
    (hnew : ∀ q ∈ retPtrs rb n (bA ty oB), σ.kheap q = none ∧
      ∀ sl d b m f, capAt σ sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f) :
    IKp UtInv σ (retypeRegionWith (Z := Unit) bA rb n oB ty dev) := by
  intro hI y hy
  rcases (retypeRegionWith_out hy).2 with e | ⟨hty, e⟩
  · rw [e]; exact hI
  · rw [e]
    refine utInvV_shrink (w := uV σ) ⟨fun p hp => ?_, fun sl d b m f' hc => ?_, rfl, fun _ h => h⟩ hI
    · have hp' : (retKh σ (retPtrs rb n (bA ty oB)) (defaultObject ty dev oB σ.curDomain) p).isSome = true := hp
      unfold retKh at hp'
      split_ifs at hp' with hm
      · exact Or.inr (hnew p hm).2
      · exact Or.inl hp'
    · have hc' : capAt { σ with kheap := retKh σ (retPtrs rb n (bA ty oB)) (defaultObject ty dev oB σ.curDomain) } sl = some (.untypedCap d b m f') := hc
      dsimp only [capAt, retKh] at hc'
      split_ifs at hc' with hm
      · exact absurd hc' (default_noUt hty dev oB σ.curDomain sl.2 d b m f')
      · exact same_cap hI hc'

/-- **The new addresses of a decoded non-reset retype lie in no other free
part** (UtDisj with the source cap's old free part), and below the source cap's
new free index `rb + len·2^o - base`. -/
theorem utRet_new {σ : State Unit} (hI : UtInv σ) {srcSlot : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype srcSlot false base rb ty sz slots dev)) :
    ∃ bits fi, capAt σ srcSlot = some (.untypedCap dev base bits fi) ∧
      fi ≤ rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat ∧
      rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat ≤ 2 ^ bits ∧
      ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none ∧
        q.toNat < base.toNat + (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat) ∧
        ∀ sl d b m f, sl ≠ srcSlot → capAt σ sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f := by
  obtain ⟨bits, fi, hc, hfit, h1, -, h3⟩ := utRet_region hI.2.1 hok
  simp only [Bool.false_eq_true, if_false] at h1
  refine ⟨bits, fi, hc, by omega, by omega, fun q hq => ⟨retPtrs_fresh hI.1 hc hfit h1 h3 q hq, ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
  have hk' := List.mem_range.1 hk
  have hkn : (k + 1) * 2 ^ fl4ObjBitsApi ty sz ≤ slots.length * 2 ^ fl4ObjBitsApi ty sz :=
    Nat.mul_le_mul_right _ hk'
  have e : (k + 1) * 2 ^ fl4ObjBitsApi ty sz = k * 2 ^ fl4ObjBitsApi ty sz + 2 ^ fl4ObjBitsApi ty sz :=
    Nat.succ_mul _ _
  have hy := Nat.two_pow_pos (fl4ObjBitsApi ty sz)
  have htn : (ptrAdd rb (k * 2 ^ fl4ObjBitsApi ty sz)).toNat = rb.toNat + k * 2 ^ fl4ObjBitsApi ty sz := by
    unfold ptrAdd
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k * 2 ^ fl4ObjBitsApi ty sz < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
  rw [htn]
  refine ⟨by omega, fun sl d b m f hne hcs hq' => ?_⟩
  exact hI.2.2.1 srcSlot sl dev base bits fi d b m f (Ne.symm hne) hc hcs _ ⟨by omega, by omega⟩ hq'

end

end Fl4Proofs.P3.SInvU
