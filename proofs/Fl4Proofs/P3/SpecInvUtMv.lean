/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut3): **the remaining cap
writers for `UtInv'`** (spec side only; imports only Fl4Spec via SpecInvUtSw).

* `NNU c`: a non-null cap that is not untyped. `hv_setCap_nn`: `set_cap` of
  such a cap keeps `UtInv'` (no decode fact: the written slot is a CDT parent
  only with a non-null cap, which it still holds).
* `CapRel c0 c` (the decode's relation between a slot's cap `c0` and the cap
  `c` written for it: `mask_cap` / `update_cap_data` keep untyped caps and
  never make one): both non-null, and `c = c0` or neither is untyped.
* `hv_capInsert` (any cap): for an untyped `c` the decode's facts `CIOK`
  (`derive_cap`'s `ensure_no_children src`, and `c` the source's own cap);
  `set_untyped_cap_as_full` empties the source's free part and the copy is a
  CDT child of the source (`utInv'_ccG`: `utInv'_ccU` with any free index).
* `hv_capMove` (CNode Move/Mutate/Rotate): the view is the old one renamed by
  the transposition of source and (null) destination, the destination's cap
  replaced by a `CapRel` cap, the now null source cut from its parent.
* `hv_capSwap` (CNode Rotate with source = destination): `hv_capSwap_same`
  with `CapRel` caps.
-/
import Fl4Proofs.P3.SpecInvUtSw
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `set_cap` of a non-null cap that is not untyped -/

/-- A non-null cap that is not untyped. -/
def NNU (c : Cap) : Prop := c ≠ .nullCap ∧ ∀ d b n f, c ≠ .untypedCap d b n f

theorem utInv'_vCap_nn {w : UView} (hI : UtInv'V w) {sl : CslotPtr} {c : Cap} (hc : NNU c) :
    UtInv'V (vCap sl c w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun s d b n f h => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hd => hd, fun _ _ _ _ _ _ ho => ho⟩ hU, fun x q h => ?_, hA⟩
  · rw [vCap_cap] at h
    split_ifs at h with e
    · exact absurd (Option.some.inj h) (hc.2 d b n f)
    · exact same_capV hU.2.1 h
  · rw [vCap_cap]
    split_ifs with e
    · exact ⟨c, rfl, hc.1⟩
    · exact hO x q h

/-- **`set_cap` of a non-null cap that is not untyped keeps `UtInv'`.** -/
theorem hv_setCap_nn (c : Cap) (hc : NNU c) (sl : CslotPtr) : HV UtInv'V UtInv'V (setCap (Z := Unit) c sl) :=
  hv_pin fun w hw => hv_mono (hv_setCap c sl w) fun w' e => by rw [e]; exact utInv'_vCap_nn hw hc

theorem ik_setCap_nn (c : Cap) (hc : NNU c) (sl : CslotPtr) : IK UtInv' (setCap (Z := Unit) c sl) :=
  hv_setCap_nn c hc sl

/-! ## The decode's cap relation -/

/-- The cap `c` written for a slot holding `c0`. -/
def CapRel (c0 c : Cap) : Prop :=
  c0 ≠ .nullCap ∧ c ≠ .nullCap ∧ (c = c0 ∨ (∀ d b n f, c ≠ .untypedCap d b n f) ∧ ∀ d b n f, c0 ≠ .untypedCap d b n f)

theorem vCap_same {w : UView} {sl : CslotPtr} {c : Cap} (h : w.2.1 sl = some c) : vCap sl c w = w := by
  unfold vCap
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext x
  show Function.update w.2.1 sl (some c) x = w.2.1 x
  by_cases e : x = sl
  · subst e; rw [Function.update_self, h]
  · rw [Function.update_of_ne e]

theorem utInv'_vCap_rel {w : UView} (hI : UtInv'V w) {sl : CslotPtr} {c0 c : Cap} (h0 : w.2.1 sl = some c0)
    (hr : CapRel c0 c) : UtInv'V (vCap sl c w) := by
  rcases hr.2.2 with e | ⟨hn, -⟩
  · subst e; rw [vCap_same h0]; exact hI
  · exact utInv'_vCap_nn hI ⟨hr.2.1, hn⟩

/-! ## Two more view writers -/

/-- Cutting a childless slot that holds no untyped cap from its parent. -/
theorem utInv'_cut {w : UView} (hI : UtInv'V w) {s : CslotPtr} (hk : ∀ x, w.2.2.1 x ≠ some s)
    (hnu : ∀ d b n f, w.2.1 s ≠ some (.untypedCap d b n f)) :
    UtInv'V (vCdt (Function.update w.2.2.1 s none) w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  have hv : (none : Option CslotPtr) ≠ some s := fun e => by cases e
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun sl d b n f h => same_capV hU.2.1 h,
    fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 h1 h2 hd => ?_, fun _ _ _ _ _ _ ho => ho⟩ hU, fun x q h => ?_,
    lu_acyc hk hv hA⟩
  · have hs2 : s2 ≠ s := fun e => by subst e; exact hnu _ _ _ _ h2
    exact (lu_tg hk hv hs2).2 hd
  · have h' : Function.update w.2.2.1 s none x = some q := h
    by_cases e : x = s
    · subst e; rw [Function.update_self] at h'; cases h'
    · rw [Function.update_of_ne e] at h'; exact hO x q h'

/-- The original flag of a slot that holds no untyped cap. -/
theorem utInv'_vOrig {w : UView} (hI : UtInv'V w) {s : CslotPtr} (v : Bool)
    (hnu : ∀ d b n f, w.2.1 s ≠ some (.untypedCap d b n f)) : UtInv'V (vOrig s v w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun sl d b n f h => same_capV hU.2.1 h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hd => hd, fun sl d b n f h ho => ?_⟩ hU, hO, hA⟩
  have hs : sl ≠ s := fun e => by subst e; exact hnu _ _ _ _ h
  show Function.update w.2.2.2 s v sl = true
  rw [Function.update_of_ne hs]; exact ho

/-! ## `cap_insert` of an untyped copy -/

/-- **`create_cap` / `cap_insert` of an untyped cap with any free index** as a
CDT child of `src` (`utInv'_ccU` with the free index `fD`). -/
theorem utInv'_ccG {w : UView} (hI : UtInv'V w) {src dest : CslotPtr} (hne : dest ≠ src)
    (hk : ∀ c, w.2.2.1 c ≠ some dest) {dS : Bool} {bS : ObjRef} {nS fS : Nat}
    (hs : w.2.1 src = some (.untypedCap dS bS nS fS)) {dev : Bool} {p : ObjRef} {bits fD : Nat}
    (hR : ∀ k ∈ utR p bits, k ∈ utR bS nS ∧ k ∉ utFr bS nS fS)
    (hE : ∀ q, w.1 q = true → q.toNat ∉ utFr p bits fD)
    (hWf : bits ≤ untypedMaxBits ∧ p.toNat % 2 ^ bits = 0 ∧ fD ≤ 2 ^ bits)
    (hAn : ∀ sl d b n f, sl ≠ src → sl ≠ dest → w.2.1 sl = some (.untypedCap d b n f) →
      (∃ k, k ∈ utR p bits ∧ k ∈ utR b n) →
      src ∈ descendantsOf sl w.2.2.1 ∧ ∀ k ∈ utR bS nS, k ∉ utFr b n f) :
    UtInv'V (vCC src dest (.untypedCap dev p bits fD) w) := by
  obtain ⟨⟨hF, hW, hD, hDe, hOr⟩, hO, hA⟩ := hI
  have hv : (some src : Option CslotPtr) ≠ some dest := fun e => hne (Option.some.inj e).symm
  have hcap : ∀ sl, sl ≠ dest → (vCC src dest (.untypedCap dev p bits fD) w).2.1 sl = w.2.1 sl :=
    fun sl h => by rw [vCC_cap, if_neg h]
  have hdst : (vCC src dest (.untypedCap dev p bits fD) w).2.1 dest = some (.untypedCap dev p bits fD) := by
    rw [vCC_cap, if_pos rfl]
  have hcdt : (vCC src dest (.untypedCap dev p bits fD) w).2.2.1 = Function.update w.2.2.1 dest (some src) := rfl
  have hdesc : ∀ x y, y ≠ dest → y ∈ descendantsOf x w.2.2.1 →
      y ∈ descendantsOf x (vCC src dest (.untypedCap dev p bits fD) w).2.2.1 :=
    fun x y hy h => by rw [hcdt]; exact (lu_tg hk hv hy).2 h
  have side : ∀ s d b n f, s ≠ dest → (vCC src dest (.untypedCap dev p bits fD) w).2.1 s = some (.untypedCap d b n f) →
      (∀ k, k ∈ utR p bits → k ∉ utFr b n f) ∧
      ((∃ k, k ∈ utR p bits ∧ k ∈ utR b n) →
        dest ∈ descendantsOf s (vCC src dest (.untypedCap dev p bits fD) w).2.2.1 ∧
          ∀ k, k ∈ utR p bits → k ∉ utFr b n f) := by
    intro s d b n f hs1 hc
    rw [hcap s hs1] at hc
    by_cases e : s = src
    · subst e; rw [hs] at hc; cases hc
      refine ⟨fun k hk => (hR k hk).2, fun _ => ⟨?_, fun k hk => (hR k hk).2⟩⟩
      exact Relation.TransGen.single (show Function.update w.2.2.1 dest (some s) dest = some s by
        rw [Function.update_self])
    · have hno : ∀ k, k ∈ utR p bits → k ∉ utFr b n f := by
        intro k hk hk2
        obtain ⟨-, h2⟩ := hAn s d b n f e hs1 hc ⟨k, hk, utFr_sub hk2⟩
        exact h2 k (hR k hk).1 hk2
      refine ⟨hno, fun hov => ⟨?_, hno⟩⟩
      obtain ⟨h1, -⟩ := hAn s d b n f e hs1 hc hov
      have h1' := hdesc s src (Ne.symm hne) h1
      exact Relation.TransGen.tail h1' (show Function.update w.2.2.1 dest (some src) dest = some src by
        rw [Function.update_self])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, (cdt_cc hO hA hne hk ⟨_, hs, by intro h; cases h⟩).1,
    (cdt_cc hO hA hne hk ⟨_, hs, by intro h; cases h⟩).2⟩
  · intro sl d b n f hc q hq hk2
    by_cases e : sl = dest
    · subst e; rw [hdst] at hc; cases hc
      exact hE q hq hk2
    · rw [hcap sl e] at hc; exact hF sl d b n f hc q hq hk2
  · intro sl d b n f hc
    by_cases e : sl = dest
    · subst e; rw [hdst] at hc; cases hc; exact hWf
    · rw [hcap sl e] at hc; exact hW sl d b n f hc
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 k hk1 hk2
    by_cases e1 : s1 = dest
    · subst e1; rw [hdst] at hc1; cases hc1
      exact (side s2 d2 b2 n2 f2 (Ne.symm hne') hc2).1 k (utFr_sub hk1) hk2
    · by_cases e2 : s2 = dest
      · subst e2; rw [hdst] at hc2; cases hc2
        exact (side s1 d1 b1 n1 f1 hne' hc1).1 k (utFr_sub hk2) hk1
      · rw [hcap s1 e1] at hc1; rw [hcap s2 e2] at hc2
        exact hD s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 k hk1 hk2
  · intro s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 hov
    by_cases e1 : s1 = dest
    · subst e1; rw [hdst] at hc1; cases hc1
      exact Or.inr ((side s2 d2 b2 n2 f2 (Ne.symm hne') hc2).2 hov)
    · by_cases e2 : s2 = dest
      · subst e2; rw [hdst] at hc2; cases hc2
        obtain ⟨k, h1, h2⟩ := hov
        exact Or.inl ((side s1 d1 b1 n1 f1 hne' hc1).2 ⟨k, h2, h1⟩)
      · rw [hcap s1 e1] at hc1; rw [hcap s2 e2] at hc2
        rcases hDe s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne' hc1 hc2 hov with ⟨hd, hr⟩ | ⟨hd, hr⟩
        · exact Or.inl ⟨hdesc s1 s2 e2 hd, hr⟩
        · exact Or.inr ⟨hdesc s2 s1 e1 hd, hr⟩
  · intro sl d b n f hc
    show Function.update w.2.2.2 dest true sl = true
    by_cases e : sl = dest
    · subst e; rw [Function.update_self]
    · rw [Function.update_of_ne e]; rw [hcap sl e] at hc; exact hOr sl d b n f hc

/-- An untyped cap is in the same region as itself (UtWf: the region does not wrap). -/
theorem sameRegionAs_self {d : Bool} {b : ObjRef} {n f : Nat} (hn : n < 64) (hfit : b.toNat + 2 ^ n ≤ 2 ^ 64) :
    sameRegionAs (.untypedCap d b n f) (.untypedCap d b n f) := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlt : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have h1 : (1 : Word).toNat = 1 := rfl
  have e1 : ((1 : Word) <<< n).toNat = 2 ^ n := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h1, Nat.one_mul, Nat.mod_eq_of_lt hlt]
  have e2 : (b + (1 : Word) <<< n - 1).toNat = b.toNat + 2 ^ n - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, e1, h1]
    rcases Nat.lt_or_ge (b.toNat + 2 ^ n) (2 ^ 64) with h | h
    · rw [Nat.mod_eq_of_lt h]
      have : 2 ^ 64 - 1 + (b.toNat + 2 ^ n) = (b.toNat + 2 ^ n - 1) + 2 ^ 64 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have h' : b.toNat + 2 ^ n = 2 ^ 64 := by omega
      rw [h', Nat.mod_self]
  refine ⟨rfl, BitVec.le_refl _, ?_, BitVec.le_refl _⟩
  show b ≤ b + (1 : Word) <<< n - 1
  rw [BitVec.le_def, e2]; omega

/-- What `cap_insert` of an untyped cap needs from the decode (`derive_cap`'s
`ensure_no_children` and the cap read from the source slot). -/
def CIOK (w : UView) (c : Cap) (src : CslotPtr) : Prop :=
  ∀ d b n f, c = .untypedCap d b n f → w.2.1 src = some c ∧ ∀ x, w.2.2.1 x ≠ some src

theorem ciok_nonUt {w : UView} {c : Cap} {src : CslotPtr} (h : ∀ d b n f, c ≠ .untypedCap d b n f) :
    CIOK w c src := fun d b n f e => absurd e (h d b n f)

/-- **`cap_insert` of an untyped copy keeps `UtInv'`.** -/
theorem hv_capInsert_ut {d : Bool} {b : ObjRef} {n f : Nat} (src dest : CslotPtr) :
    HV (fun w => UtInv'V w ∧ w.2.1 src = some (.untypedCap d b n f) ∧ ∀ x, w.2.2.1 x ≠ some src) UtInv'V
      (capInsert (Z := Unit) (.untypedCap d b n f) src dest) := by
  unfold capInsert
  refine hv_getCap_bind fun w sc ⟨hw, hs, hk⟩ hsc => ?_
  obtain rfl : sc = .untypedCap d b n f := Option.some.inj (hsc.symm.trans hs)
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hw.2.1 x dest hx; rw [hoc] at hc'; cases hc'; exact hcn rfl
  have hne : dest ≠ src := fun e => by subst e; rw [hs] at hoc; cases hoc
  have hW := hw.1.2.1 src d b n f hs
  have hfi : f ≤ 2 ^ n := hW.2.2
  have hfit : n < 64 ∧ b.toNat + 2 ^ n ≤ 2 ^ 64 := by
    have : n < 64 := by have := hW.1; unfold untypedMaxBits at this; omega
    exact ⟨this, fit_of_aligned (by omega) hW.2.1⟩
  unfold setUntypedCapAsFull
  rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
  subst w2
  refine hv_pure_bind ?_
  refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
  subst w3
  refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
  subst w4
  refine hv_bind (hv_updateCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  have ho : w.2.2.2 src = true := hw.1.2.2.2.2 src d b n f hs
  have hpar : shouldBeParentOf (.untypedCap d b n f) ((vCap dest (.untypedCap d b n f)
      (vCap src (maxFreeIndexUpdate (.untypedCap d b n f)) w)).2.2.2 src) (.untypedCap d b n f)
      (decide (isCapRevocable (.untypedCap d b n f) (.untypedCap d b n f))) :=
    ⟨ho, sameRegionAs_self hfit.1 hfit.2, trivial⟩
  rw [if_pos (decide_eq_true hpar), show decide (isCapRevocable (.untypedCap d b n f) (.untypedCap d b n f)) = true
    from decide_eq_true trivial]
  -- the source with an empty free part
  let w1 := vCap src (.untypedCap d b n (2 ^ n)) w
  have hI1 : UtInv'V w1 := utInv'_raise hw hs hfi (le_refl _)
  have hs1 : w1.2.1 src = some (.untypedCap d b n (2 ^ n)) := by rw [vCap_cap, if_pos rfl]
  have hfin : UtInv'V (vCC src dest (.untypedCap d b n f) w1) := by
    refine utInv'_ccG hI1 hne hkd hs1 (fun k hk => ⟨hk, fun hk' => ?_⟩) (fun q hq => hw.1.1 src d b n f hs q hq)
      ⟨hW.1, hW.2.1, hfi⟩ (fun sl d' b' n' f' hsl hsd hc hov => ?_)
    · have := hk'.1; have := hk'.2; omega
    · have hc' : w.2.1 sl = some (.untypedCap d' b' n' f') := by
        have : w1.2.1 sl = w.2.1 sl := by rw [vCap_cap, if_neg hsl]
        rw [← this]; exact hc
      obtain ⟨k, hk1, hk2⟩ := hov
      rcases hw.1.2.2.2.1 src sl d b n f d' b' n' f' (Ne.symm hsl) hs hc' ⟨k, hk1, hk2⟩ with ⟨hd, -⟩ | ⟨hd, hr⟩
      · exact absurd hd (desc_noKids hk)
      · exact ⟨hd, hr⟩
  exact hfin

theorem hv_capInsert (c : Cap) (src dest : CslotPtr) :
    HV (fun w => UtInv'V w ∧ CIOK w c src) UtInv'V (capInsert (Z := Unit) c src dest) := by
  by_cases hu : ∃ d b n f, c = .untypedCap d b n f
  · obtain ⟨d, b, n, f, rfl⟩ := hu
    intro σ ⟨hI, hc⟩ y hy
    obtain ⟨h1, h2⟩ := hc d b n f rfl
    exact hv_capInsert_ut src dest σ ⟨hI, h1, h2⟩ y hy
  · have hnu : ∀ d b n f, c ≠ .untypedCap d b n f := fun d b n f e => hu ⟨d, b, n, f, e⟩
    exact fun σ h y hy => hv_capInsert_nonUt c hnu src dest σ h.1 y hy

/-! ## `cap_move` -/

theorem map_sw_of {a b : CslotPtr} {o : Option CslotPtr} (ha : o ≠ some a) (hb : o ≠ some b) :
    o.map (sw a b) = o := by
  cases o with
  | none => rfl
  | some p =>
    have h1 : p ≠ a := fun e => ha (by rw [e])
    have h2 : p ≠ b := fun e => hb (by rw [e])
    simp [sw, h1, h2]

/-- **`cap_move` of a `CapRel` cap to a null slot keeps `UtInv'`**; afterwards the
source is null and every other slot but the destination is unchanged. -/
theorem hv_capMove {w : UView} (hI : UtInv'V w) {c0 c : Cap} {src dest : CslotPtr} (hs : w.2.1 src = some c0)
    (hd : w.2.1 dest = some .nullCap) (hr : CapRel c0 c) (hne : src ≠ dest) :
    HV (· = w) (fun w' => UtInv'V w' ∧ w'.2.1 src = some .nullCap ∧ w'.2.1 dest = some c ∧
      ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (capMove (Z := Unit) c src dest) := by
  unfold capMove
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_pure_bind ?_
  refine hv_pure_bind ?_
  refine hv_bind (hv_setCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_bind (hv_setOriginal _ _ _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  have hds : dest ≠ src := Ne.symm hne
  have sw1 : sw src dest src = dest := by simp [sw]
  have sw2 : sw src dest dest = src := by simp [sw, hds]
  have swx : ∀ x, x ≠ src → x ≠ dest → sw src dest x = x := fun x h1 h2 => by simp [sw, h1, h2]
  obtain ⟨hU, hO, hA⟩ := hI
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hss : w.2.2.1 src ≠ some src := fun h => hA src (Relation.TransGen.single h)
  have hsd : w.2.2.1 src ≠ some dest := hkd src
  -- the renamed view, the destination's cap replaced, the source cut and unflagged
  let w2 := vRen (sw src dest) w
  have hI2 : UtInv'V w2 := utInv'_rename (sw_sw src dest) ⟨hU, hO, hA⟩
  have hd2 : w2.2.1 dest = some c0 := by show w.2.1 (sw src dest dest) = _; rw [sw2, hs]
  let w3 := vCap dest c w2
  have hI3 : UtInv'V w3 := utInv'_vCap_rel hI2 hd2 hr
  have hsrc3 : w3.2.1 src = some .nullCap := by
    show Function.update (fun x => w.2.1 (sw src dest x)) dest (some c) src = _
    rw [Function.update_of_ne hne, sw1, hd]
  have hnu3 : ∀ d b n f, w3.2.1 src ≠ some (.untypedCap d b n f) := fun d b n f h => by
    rw [hsrc3] at h; cases h
  have hk3 : ∀ x, w3.2.2.1 x ≠ some src := by
    intro x hx
    have hx' : (w.2.2.1 (sw src dest x)).map (sw src dest) = some src := hx
    cases e : w.2.2.1 (sw src dest x) with
    | none => rw [e] at hx'; cases hx'
    | some p =>
      rw [e] at hx'
      simp only [Option.map_some, Option.some.injEq] at hx'
      have : p = dest := by rw [← sw_sw src dest p, hx', sw1]
      subst this; exact hkd _ e
  have hI4 := utInv'_cut hI3 hk3 hnu3
  have hI5 := utInv'_vOrig hI4 false hnu3
  suffices key : ∀ W : UView, W = vOrig src false (vCdt (Function.update w3.2.2.1 src none) w3) →
      UtInv'V W ∧ W.2.1 src = some .nullCap ∧ W.2.1 dest = some c ∧
        ∀ x, x ≠ src → x ≠ dest → W.2.1 x = w.2.1 x by
    refine key _ ?_
    unfold vOrig vCdt vCap
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext x
      show Function.update (Function.update w.2.1 dest (some c)) src (some .nullCap) x =
        Function.update (fun x => w.2.1 (sw src dest x)) dest (some c) x
      by_cases e1 : x = src
      · subst e1; rw [Function.update_self, Function.update_of_ne hne, sw1, hd]
      · rw [Function.update_of_ne e1]
        by_cases e2 : x = dest
        · subst e2; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne e2, Function.update_of_ne e2, swx x e1 e2]
    · funext x
      show (if Function.update (Function.update w.2.2.1 dest (w.2.2.1 src)) src none x = some src then some dest
          else Function.update (Function.update w.2.2.1 dest (w.2.2.1 src)) src none x) =
        Function.update (fun x => (w.2.2.1 (sw src dest x)).map (sw src dest)) src none x
      by_cases e1 : x = src
      · subst e1; simp only [Function.update_self]; rfl
      · rw [Function.update_of_ne e1, Function.update_of_ne e1]
        by_cases e2 : x = dest
        · subst e2; rw [Function.update_self, sw2, if_neg hss, map_sw_of hss hsd]
        · rw [Function.update_of_ne e2, swx x e1 e2]
          by_cases e3 : w.2.2.1 x = some src
          · rw [if_pos e3, e3]; simp [sw1]
          · rw [if_neg e3, map_sw_of e3 (hkd x)]
    · funext x
      show Function.update (Function.update w.2.2.2 dest (w.2.2.2 src)) src false x =
        Function.update (fun x => w.2.2.2 (sw src dest x)) src false x
      by_cases e1 : x = src
      · subst e1; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e1, Function.update_of_ne e1]
        by_cases e2 : x = dest
        · subst e2; rw [Function.update_self, sw2]
        · rw [Function.update_of_ne e2, swx x e1 e2]
  intro W hW
  subst hW
  refine ⟨hI5, ?_, ?_, fun x h1 h2 => ?_⟩
  · show w3.2.1 src = _; exact hsrc3
  · show Function.update (fun x => w.2.1 (sw src dest x)) dest (some c) dest = _
    rw [Function.update_self]
  · show Function.update (fun x => w.2.1 (sw src dest x)) dest (some c) x = _
    rw [Function.update_of_ne h2, swx x h1 h2]

/-! ## `cap_swap` with transformed caps -/

/-- **`cap_swap` of `CapRel` caps keeps `UtInv'`.** -/
theorem hv_capSwap {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {c1' c2' c1 c2 : Cap} (h1r : CapRel c1' c1)
    (h2r : CapRel c2' c2) :
    HV (fun w => UtInv'V w ∧ w.2.1 s1 = some c1' ∧ w.2.1 s2 = some c2') UtInv'V (capSwap (Z := Unit) c1 s1 c2 s2) := by
  refine hv_pin fun w ⟨hI, h1, h2⟩ => ?_
  unfold capSwap
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.1 s1) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_gets_bind (fun w => w.2.2.1 s2) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_pure_bind ?_
  refine hv_bind (hv_setCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  refine hv_bind (hv_setOriginal _ _ _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  have hs21 : s2 ≠ s1 := Ne.symm hne
  have sw1 : sw s1 s2 s1 = s2 := by simp [sw]
  have sw2 : sw s1 s2 s2 = s1 := by simp [sw, hs21]
  have swx : ∀ x, x ≠ s1 → x ≠ s2 → sw s1 s2 x = x := fun x h1 h2 => by simp [sw, h1, h2]
  have hm : ∀ o : Option CslotPtr, (if o = some s1 then some s2 else if o = some s2 then some s1 else o) =
      o.map (sw s1 s2) := by
    intro o; cases o with
    | none => simp
    | some p =>
      by_cases e1 : p = s1
      · subst e1; simp [sw1]
      · by_cases e2 : p = s2
        · subst e2; simp [sw2, hs21]
        · simp [e1, e2, swx p e1 e2]
  suffices hsuff : ∀ T : Cdt, T = (fun x => (w.2.2.1 (sw s1 s2 x)).map (sw s1 s2)) →
      UtInv'V (vOrig s2 (w.2.2.2 s1) (vOrig s1 (w.2.2.2 s2) (vCdt T (vCap s2 c1 (vCap s1 c2 w))))) by
    refine hsuff _ ?_
    funext x
    by_cases e2 : x = s2
    · subst e2; rw [Function.update_self, sw2]; exact hm _
    · rw [Function.update_of_ne e2]
      by_cases e1 : x = s1
      · subst e1; rw [Function.update_self, sw1]; exact hm _
      · rw [Function.update_of_ne e1, swx x e1 e2]; exact hm _
  intro T hT
  subst hT
  have key : vOrig s2 (w.2.2.2 s1) (vOrig s1 (w.2.2.2 s2)
      (vCdt (fun x => (w.2.2.1 (sw s1 s2 x)).map (sw s1 s2)) (vCap s2 c1 (vCap s1 c2 w)))) =
      vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) w)) := by
    unfold vOrig vCdt vCap vRen
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · funext x
      show Function.update (Function.update w.2.1 s1 (some c2)) s2 (some c1) x =
        Function.update (Function.update (fun x => w.2.1 (sw s1 s2 x)) s1 (some c2)) s2 (some c1) x
      by_cases e2 : x = s2
      · subst e2; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne e2, Function.update_of_ne e2]
        by_cases e1 : x = s1
        · subst e1; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne e1, Function.update_of_ne e1, swx x e1 e2]
    · funext x
      show Function.update (Function.update w.2.2.2 s1 (w.2.2.2 s2)) s2 (w.2.2.2 s1) x = w.2.2.2 (sw s1 s2 x)
      by_cases e2 : x = s2
      · subst e2; rw [Function.update_self, sw2]
      · rw [Function.update_of_ne e2]
        by_cases e1 : x = s1
        · subst e1; rw [Function.update_self, sw1]
        · rw [Function.update_of_ne e1, swx x e1 e2]
  rw [key]
  have hR := utInv'_rename (sw_sw s1 s2) hI
  have hR1 : (vRen (sw s1 s2) w).2.1 s1 = some c2' := by show w.2.1 (sw s1 s2 s1) = _; rw [sw1, h2]
  have hR2 : (vCap s1 c2 (vRen (sw s1 s2) w)).2.1 s2 = some c1' := by
    rw [vCap_cap, if_neg hs21]; show w.2.1 (sw s1 s2 s2) = _; rw [sw2, h1]
  exact utInv'_vCap_rel (utInv'_vCap_rel hR hR1 h2r) hR2 h1r

end

end Fl4Proofs.P3.SInvU
