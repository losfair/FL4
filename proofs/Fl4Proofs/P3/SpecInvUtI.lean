/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **`invoke_untyped`
without reset keeps `UtInv'`** (spec side only).

The chain (FL4's `invoke_untyped`, `invokeUntypedWith fl4ObjBitsApi`): the
source cap's free index is raised past the new objects (`utInv'_raise`), the
objects are written at fresh addresses outside every free part
(`utInv'_retype`, from `utRet_new`), `init_arch_objects` is a frame, and one
`create_cap` per destination slot (`hv_ccLoop` for caps that are not untyped,
`hv_ccLoopU` for untyped children: their regions are pairwise disjoint pieces of
the source's region below its new free index, and by UtDesc every other
untyped cap overlapping them is an ancestor of the source).

Inputs from the decode (`decode_untyped_invocation`): `UtRetOK` (SpecInvUt)
and `DestNull` (every destination slot held a null cap: `ensure_empty`); by
CdtOK the destinations are CDT leaves.
-/
import Fl4Proofs.P3.SpecInvUtCC
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Combinators -/

theorem hv_bind' {P Q R : UView → Prop} {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ}
    (hm : HV P R m) (hg : ∀ a, HV R Q (g a)) : HV P Q (NonDet.bind m g) := hv_bind hm hg

theorem hv_ret' {Q : UView → Prop} {α : Type} {w : UView} (a : α) (hw : Q w) :
    HV (· = w) Q (NonDet.pure a : NonDet (State Unit) α) := hv_ret a hw

theorem run_liftE_mem {ε α : Type} {m : NonDet (State Unit) α} {σ : State Unit} {y : Except ε α × State Unit}
    (h : y ∈ ((NonDetE.liftE (ε := ε) m).run σ).1) : ∃ x ∈ (m σ).1, y.2 = x.2 := by
  unfold NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hx, by rw [Set.mem_singleton_iff.1 hy]⟩

/-! ## The free-index raise -/

theorem vCap_cap {sl : CslotPtr} {c : Cap} {w : UView} (s : CslotPtr) :
    (vCap sl c w).2.1 s = if s = sl then some c else w.2.1 s := by
  by_cases e : s = sl
  · subst e; simp [vCap]
  · simp [vCap, e]

theorem utInv'_raise {w : UView} (hI : UtInv'V w) {sl : CslotPtr} {d : Bool} {b : ObjRef} {n f f' : Nat}
    (hc : w.2.1 sl = some (.untypedCap d b n f)) (hff : f ≤ f') (hf' : f' ≤ 2 ^ n) :
    UtInv'V (vCap sl (.untypedCap d b n f') w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  refine ⟨utInvV_shrink (w := w) ⟨fun p hp => Or.inl hp, fun s d' b' n' g hc' => ?_, rfl, fun _ h => h⟩ hU,
    fun c q h => ?_, hA⟩
  · rw [vCap_cap] at hc'
    split_ifs at hc' with e
    · subst e; cases hc'; exact ⟨f, hc, hff, hf'⟩
    · exact same_capV hU.2.1 hc'
  · rw [vCap_cap]; split_ifs with e
    · exact ⟨_, rfl, by intro h; cases h⟩
    · exact hO c q h

/-! ## `retype_region` -/

theorem utInv'_retype {σ : State Unit} (hI : UtInv' σ) {bA : ApiObjectType → Nat → Nat} {rb : ObjRef}
    {n oB : Nat} {ty : ApiObjectType} {dev : Bool}
    (hnew : ∀ q ∈ retPtrs rb n (bA ty oB), σ.kheap q = none ∧
      ∀ sl d b m f, capAt σ sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f)
    {y : List ObjRef × State Unit} (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev σ).1) :
    UtInv' y.2 ∧ y.1 = retPtrs rb n (bA ty oB) ∧ y.2.cdt = σ.cdt ∧
      (∀ sl, σ.kheap sl.1 ≠ none → capAt y.2 sl = capAt σ sl) ∧ (ty = .untyped → y.2 = σ) := by
  obtain ⟨h1, h2⟩ := retypeRegionWith_out hy
  have hU := ikp_retype_utInv hnew hI.1 y hy
  have hcap : ∀ sl, σ.kheap sl.1 ≠ none → capAt y.2 sl = capAt σ sl := by
    intro sl hs
    rcases h2 with e | ⟨-, e⟩
    · rw [e]
    · rw [e]
      have hk : retKh σ (retPtrs rb n (bA ty oB)) (defaultObject ty dev oB σ.curDomain) sl.1 = σ.kheap sl.1 := by
        unfold retKh; rw [if_neg (fun hm => hs (hnew sl.1 hm).1)]
      unfold capAt; simp only [hk]
  have hcdt : y.2.cdt = σ.cdt := by rcases h2 with e | ⟨-, e⟩ <;> rw [e]
  refine ⟨⟨hU, fun c q h => ?_, fun x hx => ?_⟩, h1, hcdt, hcap, fun hty => ?_⟩
  · have h' : σ.cdt c = some q := by rw [← hcdt]; exact h
    obtain ⟨cap, hc, hcn⟩ := hI.2.1 c q h'
    have hk : σ.kheap q.1 ≠ none := by
      intro e; have hc' : capAt σ q = some cap := hc; unfold capAt at hc'; rw [e] at hc'; cases hc'
    exact ⟨cap, by show capAt y.2 q = _; rw [hcap q hk]; exact hc, hcn⟩
  · have hx' : Relation.TransGen (parentOf σ.cdt) x x := by rw [← hcdt]; exact hx
    exact hI.2.2 x hx'
  · rcases h2 with e | ⟨hne, -⟩
    · exact e
    · exact absurd hty hne

/-! ## Arithmetic -/

theorem ptrAdd_toNat {rb : ObjRef} {k o : Nat} (h : rb.toNat + k * 2 ^ o < 2 ^ 64) :
    (ptrAdd rb (k * 2 ^ o)).toNat = rb.toNat + k * 2 ^ o := by
  unfold ptrAdd
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k * 2 ^ o < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h]

theorem fi_new {base rb : ObjRef} {len o bits : Nat} (hb : bits < 64) (h1 : base.toNat ≤ rb.toNat)
    (h3 : rb.toNat + len * 2 ^ o ≤ base.toNat + 2 ^ bits) (hfit : base.toNat + 2 ^ bits ≤ 2 ^ 64) :
    unat (rb + (BitVec.ofNat 64 len <<< o) - base) = rb.toNat + len * 2 ^ o - base.toNat := by
  have hlt : 2 ^ bits < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hb
  have hpo : 1 ≤ 2 ^ o := Nat.one_le_two_pow
  have hl1 : len ≤ len * 2 ^ o := Nat.le_mul_of_pos_right _ hpo
  have e1 : (BitVec.ofNat 64 len <<< o).toNat = len * 2 ^ o := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  show (rb + (BitVec.ofNat 64 len <<< o) - base).toNat = _
  rw [BitVec.toNat_sub, BitVec.toNat_add, e1]
  have hbl : base.toNat < 2 ^ 64 := base.isLt
  rcases Nat.lt_or_ge (rb.toNat + len * 2 ^ o) (2 ^ 64) with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : 2 ^ 64 - base.toNat + (rb.toNat + len * 2 ^ o) = (rb.toNat + len * 2 ^ o - base.toNat) + 2 ^ 64 := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have heq : rb.toNat + len * 2 ^ o = 2 ^ 64 := by omega
    rw [heq, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

/-! ## The `create_cap` loops -/

theorem defaultCap_nonUt {ty : ApiObjectType} (hty : ty ≠ .untyped) (o : ObjRef) (s : Nat) (dev : Bool) :
    ∀ d b n f, defaultCap ty o s dev ≠ .untypedCap d b n f := by
  intro d b n f h
  cases ty <;> first | exact hty rfl | cases h

theorem lu_kids {t : Cdt} {d x src : CslotPtr} (hx : x ≠ src) (hk : ∀ c, t c ≠ some x) :
    ∀ c, Function.update t d (some src) c ≠ some x := by
  intro c hc
  by_cases e : c = d
  · subst e; rw [Function.update_self] at hc; exact hx (Option.some.inj hc).symm
  · rw [Function.update_of_ne e] at hc; exact hk c hc

/-- **The `create_cap` loop, caps that are not untyped.** -/
theorem hv_ccLoop {ty : ApiObjectType} (hty : ty ≠ .untyped) (objSz : Nat) (src : CslotPtr) (dev : Bool) :
    ∀ (L : List (CslotPtr × ObjRef)) (w : UView), UtInv'V w → (∃ c, w.2.1 src = some c ∧ c ≠ .nullCap) →
      (∀ x ∈ L, x.1 ≠ src ∧ ∀ c, w.2.2.1 c ≠ some x.1) →
      HV (· = w) UtInv'V (NonDet.mapMx (createCap (Z := Unit) ty objSz src dev) L)
  | [], w, hI, _, _ => by unfold NonDet.mapMx; exact hv_ret' _ hI
  | (d, p) :: L, w, hI, hs, hL => by
    unfold NonDet.mapMx
    refine hv_bind' (hv_createCap ty objSz src dev d p w) fun _ => ?_
    have hd := hL (d, p) (List.mem_cons.2 (Or.inl rfl))
    have hne : d ≠ src := hd.1
    refine hv_ccLoop hty objSz src dev L _ (utInv'_cc hI hne hd.2 hs (defaultCap_nonUt hty _ _ _)) ?_ ?_
    · obtain ⟨c, hc, hcn⟩ := hs
      exact ⟨c, by rw [vCC_cap, if_neg (Ne.symm hne)]; exact hc, hcn⟩
    · intro x hx
      have hx' := hL x (List.mem_cons.2 (Or.inr hx))
      exact ⟨hx'.1, lu_kids hx'.1 hx'.2⟩

/-- What `create_cap` of an untyped child at `x = (dest, p)` needs (`utInv'_ccU`). -/
def ItemU (w : UView) (src : CslotPtr) (bS : ObjRef) (nS fS sz : Nat) (x : CslotPtr × ObjRef) : Prop :=
  x.1 ≠ src ∧ (∀ c, w.2.2.1 c ≠ some x.1) ∧ (∀ k ∈ utR x.2 sz, k ∈ utR bS nS ∧ k ∉ utFr bS nS fS) ∧
    (∀ q, w.1 q = true → q.toNat ∉ utR x.2 sz) ∧ (sz ≤ untypedMaxBits ∧ x.2.toNat % 2 ^ sz = 0) ∧
    (∀ sl d b n f, sl ≠ src → sl ≠ x.1 → w.2.1 sl = some (.untypedCap d b n f) →
      (∃ k, k ∈ utR x.2 sz ∧ k ∈ utR b n) →
      src ∈ descendantsOf sl w.2.2.1 ∧ ∀ k ∈ utR bS nS, k ∉ utFr b n f)

/-- Disjoint regions of size `2^sz`. -/
def RDisj (sz : Nat) (x y : CslotPtr × ObjRef) : Prop := ∀ k, k ∈ utR x.2 sz → k ∉ utR y.2 sz

theorem itemU_step {w : UView} {src d : CslotPtr} {p : ObjRef} {dev : Bool} {bS : ObjRef} {nS fS sz : Nat}
    (hne : d ≠ src) (hk : ∀ c, w.2.2.1 c ≠ some d) {x : CslotPtr × ObjRef} (hx : ItemU w src bS nS fS sz x)
    (hdj : RDisj sz (d, p) x) : ItemU (vCC src d (.untypedCap dev p sz 0) w) src bS nS fS sz x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  have hv : (some src : Option CslotPtr) ≠ some d := fun e => hne (Option.some.inj e).symm
  refine ⟨h1, lu_kids h1 h2, h3, h4, h5, fun sl d' b n f hs1 hs2 hc hov => ?_⟩
  rw [vCC_cap] at hc
  split_ifs at hc with e
  · subst e; cases hc
    obtain ⟨k, hk1, hk2⟩ := hov
    exact absurd hk1 (hdj k hk2)
  · obtain ⟨h1', h2'⟩ := h6 sl d' b n f hs1 hs2 hc hov
    exact ⟨(lu_tg hk hv (Ne.symm hne)).2 h1', h2'⟩

/-- **The `create_cap` loop, untyped children.** -/
theorem hv_ccLoopU (sz : Nat) (src : CslotPtr) (dev dS : Bool) (bS : ObjRef) (nS fS : Nat) :
    ∀ (L : List (CslotPtr × ObjRef)) (w : UView), L.Pairwise (RDisj sz) → UtInv'V w →
      w.2.1 src = some (.untypedCap dS bS nS fS) → (∀ x ∈ L, ItemU w src bS nS fS sz x) →
      HV (· = w) UtInv'V (NonDet.mapMx (createCap (Z := Unit) .untyped sz src dev) L)
  | [], w, _, hI, _, _ => by unfold NonDet.mapMx; exact hv_ret' _ hI
  | (d, p) :: L, w, hP, hI, hs, hL => by
    unfold NonDet.mapMx
    refine hv_bind' (hv_createCap .untyped sz src dev d p w) fun _ => ?_
    rw [List.pairwise_cons] at hP
    obtain ⟨hne, hk, hR, hE, hWf, hAn⟩ := hL (d, p) (List.mem_cons.2 (Or.inl rfl))
    refine hv_ccLoopU sz src dev dS bS nS fS L _ hP.2 (utInv'_ccU hI hne hk hs hR hE hWf hAn) ?_ ?_
    · show (vCC src d (.untypedCap dev p sz 0) w).2.1 src = _
      rw [vCC_cap, if_neg (Ne.symm hne)]; exact hs
    · intro x hx
      exact itemU_step hne hk (hL x (List.mem_cons.2 (Or.inr hx))) (hP.1 x hx)

theorem pw_zip {α β : Type} {R : β → β → Prop} :
    ∀ (l1 : List α) (l2 : List β), l2.Pairwise R → (l1.zip l2).Pairwise (fun a b => R a.2 b.2)
  | [], _, _ => List.Pairwise.nil
  | _ :: _, [], _ => List.Pairwise.nil
  | a :: as, b :: bs, h => by
    rw [List.pairwise_cons] at h
    rw [List.zip_cons_cons]
    exact List.Pairwise.cons (fun x hx => h.1 _ (List.of_mem_zip hx).2) (pw_zip as bs h.2)

theorem retPtrs_mem {rb : ObjRef} {n o : Nat} {q : ObjRef} (h : q ∈ retPtrs rb n o) :
    ∃ k, k < n ∧ q = ptrAdd rb (k * 2 ^ o) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  exact ⟨k, List.mem_range.1 hk, rfl⟩

theorem retPtrs_pw {rb : ObjRef} {n o : Nat} (hfit : rb.toNat + n * 2 ^ o ≤ 2 ^ 64) :
    (retPtrs rb n o).Pairwise (fun a b => ∀ k, k ∈ utR a o → k ∉ utR b o) := by
  unfold retPtrs
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (R := (· < ·)) (fun {i j} hi hj hij => ?_) (List.pairwise_lt_range)
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have hpo := Nat.two_pow_pos o
  have m1 : (i + 1) * 2 ^ o ≤ j * 2 ^ o := Nat.mul_le_mul_right _ hij
  have m2 : (j + 1) * 2 ^ o ≤ n * 2 ^ o := Nat.mul_le_mul_right _ hj'
  have e1 : (i + 1) * 2 ^ o = i * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  have e2 : (j + 1) * 2 ^ o = j * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  intro k hk1 hk2
  simp only [utR, Set.mem_setOf_eq] at hk1 hk2
  rw [ptrAdd_toNat (by omega)] at hk1
  rw [ptrAdd_toNat (by omega)] at hk2
  omega

/-! ## `invoke_untyped` without reset -/

/-- **The decode's `ensure_empty` on the destination slots.** -/
def DestNull (σ : State Unit) : UntypedInvocation → Prop
  | .retype _ _ _ _ _ _ slots _ => ∀ d ∈ slots, capAt σ d = some .nullCap

theorem destNull_view {σ σ' : State Unit} (h : uV σ' = uV σ) {ui : UntypedInvocation} (hd : DestNull σ ui) :
    DestNull σ' ui := by
  cases ui with
  | retype _ _ _ _ _ _ slots _ =>
    intro d hd'
    have hcap : capAt σ' = capAt σ := congrArg (fun w : UView => w.2.1) h
    rw [hcap]; exact hd d hd'

/-- **`invoke_untyped` without reset keeps `UtInv'`** (at the decode's checks). -/
theorem invokeUntyped_utInv' {σ : State Unit} (hI : UtInv' σ) {s : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype s false base rb ty sz slots dev))
    (hdn : DestNull σ (.retype s false base rb ty sz slots dev)) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s false base rb ty sz slots dev)) σ).1,
      UtInv' y.2 := by
  intro y hy
  have hok' := hok
  obtain ⟨-, -, -, ho, -, -, -, -⟩ := hok'
  obtain ⟨bits, fi, hc, hfiN1, hfiN2, hq⟩ := utRet_new hI.1 hok
  obtain ⟨bits', fi', hc', hfit, h1, hal, h3⟩ := utRet_region hI.1.2.1 hok
  rw [hc] at hc'; cases hc'
  simp only [Bool.false_eq_true, if_false] at h1
  obtain ⟨hbits, -⟩ := UtWf.fit hI.1.2.1 hc
  have hfi : unat (rb + (BitVec.ofNat 64 slots.length <<< (fl4ObjBitsApi ty sz)) - base) = rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat :=
    fi_new hbits (by omega) h3 hfit
  simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
  replace hy := run_returnOk_bind_mem hy
  obtain ⟨x, hx, e⟩ := run_liftE_mem hy
  rw [e]
  -- getCap
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1 hc1; subst s1
  rw [hc] at hc1; cases hc1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  -- the free-index raise
  obtain ⟨x4, hx4, hx⟩ := hx
  have hv4 := hv_setCap _ _ (uV σ) σ rfl x4 hx4
  simp only [bitsOf] at hv4
  rw [hfi] at hv4
  have hI4 : UtInv' x4.2 := by
    show UtInv'V _; rw [hv4]; exact utInv'_raise hI hc hfiN1 hfiN2
  have hkey4 : ∀ q, (x4.2.kheap q).isSome = (σ.kheap q).isSome := fun q => congrFun (congrArg (fun w : UView => w.1) hv4) q
  have hcap4 : capAt x4.2 = Function.update (capAt σ) s (some (.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat))) :=
    congrArg (fun w : UView => w.2.1) hv4
  have hcdt4 : x4.2.cdt = σ.cdt := congrArg (fun w : UView => w.2.2.1) hv4
  -- the retype
  obtain ⟨x5, hx5, hx⟩ := hx
  have hnew : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), x4.2.kheap q = none ∧
      ∀ sl d b m f, capAt x4.2 sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f := by
    intro q hqm
    obtain ⟨hq1, hq2, hq3⟩ := hq q hqm
    refine ⟨?_, fun sl d b m f hcs => ?_⟩
    · have := hkey4 q; rw [hq1] at this
      cases e : x4.2.kheap q with
      | none => rfl
      | some _ => rw [e] at this; cases this
    · rw [hcap4] at hcs
      by_cases es : sl = s
      · subst es; rw [Function.update_self] at hcs; cases hcs
        intro hm; have := hm.1; omega
      · rw [Function.update_of_ne es] at hcs; exact hq3 sl d b m f es hcs
  obtain ⟨hI5, hy5, hcdt5, hcap5, hut5⟩ := utInv'_retype hI4 hnew hx5
  -- init_arch_objects
  obtain ⟨x6, hx6, hx⟩ := hx
  have hv6 : uV x6.2 = uV x5.2 := uk_initArchObjects (uvw := uV x5.2) _ _ _ _ _ _ x5.2 rfl x6 hx6
  rw [hy5] at hx
  -- facts about the destinations
  have hsk : σ.kheap s.1 ≠ none := by
    intro e; have hc0 : capAt σ s = _ := hc; unfold capAt at hc0; rw [e] at hc0; cases hc0
  have hk4s : x4.2.kheap s.1 ≠ none := by
    intro e; have := hkey4 s.1; rw [e] at this
    cases e' : σ.kheap s.1 with
    | none => exact hsk e'
    | some _ => rw [e'] at this; cases this
  have hdst : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), x.1 ≠ s ∧ ∀ c, σ.cdt c ≠ some x.1 := by
    intro x hxm
    have hn := hdn x.1 (List.of_mem_zip hxm).1
    refine ⟨fun e => ?_, fun c hcx => ?_⟩
    · rw [e, hc] at hn; cases hn
    · obtain ⟨cap, hcap, hcn⟩ := hI.2.1 c x.1 hcx
      have hcap' : capAt σ x.1 = some cap := hcap
      rw [hn] at hcap'; cases hcap'; exact hcn rfl
  by_cases hty : ty = .untyped
  · -- untyped children
    subst hty
    have ho' : fl4ObjBitsApi .untyped sz = sz := rfl
    simp only [ho'] at *
    have e5 : x5.2 = x4.2 := by first | exact hut5 rfl | exact hut5 trivial | exact hut5
    have hw6 : uV x6.2 = vCap s (.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ sz - base.toNat)) (uV σ) := by
      rw [hv6, e5, hv4]
    refine hv_ccLoopU sz s dev dev base bits (rb.toNat + slots.length * 2 ^ sz - base.toNat) _ (uV x6.2)
      (pw_zip _ _ (retPtrs_pw (by omega))) (by rw [hv6, e5]; exact hI4) (by rw [hw6, vCap_cap, if_pos rfl])
      (fun x hxm => ?_) x6.2 rfl _ hx
    obtain ⟨hx1, hx2⟩ := hdst x hxm
    obtain ⟨k, hk, hxk⟩ := retPtrs_mem (List.of_mem_zip hxm).2
    have hpo := Nat.two_pow_pos sz
    have m2 : (k + 1) * 2 ^ sz ≤ slots.length * 2 ^ sz := Nat.mul_le_mul_right _ hk
    have e2 : (k + 1) * 2 ^ sz = k * 2 ^ sz + 2 ^ sz := Nat.succ_mul _ _
    have hxt : x.2.toNat = rb.toNat + k * 2 ^ sz := by rw [hxk]; exact ptrAdd_toNat (by omega)
    have hin : ∀ k', k' ∈ utR x.2 sz → k' ∈ utFr base bits fi ∧
        k' < base.toNat + (rb.toNat + slots.length * 2 ^ sz - base.toNat) := by
      intro k' hk'; simp only [utR, utFr, Set.mem_setOf_eq] at hk' ⊢; rw [hxt] at hk'; omega
    refine ⟨hx1, by rw [hw6]; exact hx2, fun k' hk' => ⟨utFr_sub (hin k' hk').1, fun hm => ?_⟩, fun q hq' hm => ?_,
      ⟨ho, ?_⟩, fun sl d b n f hs1 hs2 hcs hov => ?_⟩
    · have := (hin k' hk').2; have := hm.1; omega
    · rw [hw6] at hq'
      exact hI.1.1 s dev base bits fi hc q hq' (hin _ hm).1
    · rw [hxt, Nat.add_mul_mod_self_right]; exact hal
    · rw [hw6, vCap_cap, if_neg hs1] at hcs
      obtain ⟨k0, hk0, hk0'⟩ := hov
      rcases hI.1.2.2.2.1 s sl dev base bits fi d b n f (Ne.symm hs1) hc hcs ⟨k0, utFr_sub (hin k0 hk0).1, hk0'⟩ with
        ⟨-, hr⟩ | ⟨hd, hr⟩
      · exact absurd (hin k0 hk0).1 (hr k0 hk0')
      · exact ⟨by rw [hw6]; exact hd, hr⟩
  · -- caps that are not untyped
    refine hv_ccLoop hty sz s dev _ (uV x6.2) (by rw [hv6]; exact hI5)
      ⟨.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat), ?_, by intro h; cases h⟩
      (fun x hxm => ?_) x6.2 rfl _ hx
    · rw [hv6]; show capAt x5.2 s = _; rw [hcap5 s hk4s, hcap4, Function.update_self]
    · obtain ⟨hx1, hx2⟩ := hdst x hxm
      refine ⟨hx1, fun c hcx => hx2 c ?_⟩
      have : (uV x6.2).2.2.1 = σ.cdt := by rw [hv6]; show x5.2.cdt = _; rw [hcdt5, hcdt4]
      rw [this] at hcx; exact hcx

end

end Fl4Proofs.P3.SInvU
