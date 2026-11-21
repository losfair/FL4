/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **the `create_cap`
loop of a retype keeps `NV N`** (spec side only; imports SpecInvUtP3).

Items `(dest, p)`: the new object at `p` spans `utR p o` (`o = obj_bits_api`);
`ItemN` collects what one `create_cap` needs and what the earlier ones keep: the
destination is a null CDT leaf reached through a CNode, no cap covers the new
object's range, every slot inside the range is null (and, for an untyped child,
there is none), and every other untyped cap overlapping the range is an
ancestor of the source whose free part misses it. `capRng_default`: a new cap
covers only its own object's range. `nv_ccLoop`: the loop keeps `NV N`
(`nv_cc` / `nv_ccU` per item, `itemN_step` for the later items, `UtFitV` for
the untyped caps' sizes).
-/
import Fl4Proofs.P3.SpecInvUtP3
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-- Every untyped cap fits in the address space (UtWf). -/
def UtFitV (w : UView) : Prop :=
  ∀ u d b n f, w.2.1 u = some (.untypedCap d b n f) → n < 64 ∧ b.toNat + 2 ^ n ≤ 2 ^ 64

theorem utR_self {p : ObjRef} {o : Nat} : p.toNat ∈ utR p o := by
  simp only [utR, Set.mem_setOf_eq]; have := Nat.two_pow_pos o; omega

theorem utR_add {p : ObjRef} {k o : Nat} (hk : k < 2 ^ o) (hp : p.toNat + 2 ^ o ≤ 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat ∈ utR p o := by
  have hk64 : k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt (by omega)]
  simp only [utR, Set.mem_setOf_eq]; omega

/-- **A new cap covers only its object's range.** -/
theorem capRng_default (ty : ApiObjectType) (sz : Nat) (dev : Bool) (p : ObjRef)
    (hp : p.toNat + 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64) :
    ∀ r ∈ capRng (defaultCap ty p sz dev), r.toNat ∈ utR p (fl4ObjBitsApi ty sz) := by
  intro r hr
  cases ty with
  | archObject a =>
    cases a
    all_goals first
      | exact hr.elim
      | (have e : some p = some r := hr; cases e; exact utR_self)
      | (obtain ⟨k, hk, e⟩ := hr; subst e; exact utR_add hk hp)
  | _ =>
    first
      | exact hr.elim
      | (have e : r = p := hr; subst e; exact utR_self)

theorem defaultCap_nz (ty : ApiObjectType) (p : ObjRef) (sz : Nat) (dev : Bool) :
    ∀ r b n, defaultCap ty p sz dev ≠ .zombie r b n := by
  intro r b n e; cases ty <;> cases e

theorem defaultCap_bits (ty : ApiObjectType) (p : ObjRef) {sz : Nat} (hsz : sz < 64) (dev : Bool) :
    CapBitsOK (defaultCap ty p sz dev) := by
  intro b hb
  cases ty <;> cases hb <;> omega

/-- The loop's facts about an item `(dest, p)`. -/
def ItemN (w : UView) (src : CslotPtr) (o : Nat) (U : Bool) (x : CslotPtr × ObjRef) : Prop :=
  w.2.1 x.1 = some .nullCap ∧ DestRefV w x.1 ∧ (∀ c, w.2.2.1 c ≠ some x.1) ∧ x.1 ≠ src ∧
  (∀ s c r, w.2.1 s = some c → r ∈ capRng c → r.toNat ∉ utR x.2 o) ∧
  (∀ y c, w.2.1 y = some c → y.1.toNat ∈ utR x.2 o → c = .nullCap ∧ U = false) ∧
  (∀ u d b n f, u ≠ src → w.2.1 u = some (.untypedCap d b n f) → ∀ k ∈ utR x.2 o, k ∈ utR b n →
    src ∈ descendantsOf u w.2.2.1 ∧ k ∉ utFr b n f)

theorem vCC_cases {src d0 : CslotPtr} {c0 : Cap} {w : UView} {s : CslotPtr} {c : Cap}
    (h : (vCC src d0 c0 w).2.1 s = some c) : (s = d0 ∧ c = c0) ∨ (s ≠ d0 ∧ w.2.1 s = some c) := by
  rw [vCC_cap] at h; split_ifs at h with e
  · exact Or.inl ⟨e, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨e, h⟩

/-- The later items keep their facts across a `create_cap`. -/
theorem itemN_step {w : UView} {src d0 : CslotPtr} {p0 : ObjRef} {o : Nat} {c0 : Cap} {U : Bool}
    (hk0 : ∀ c, w.2.2.1 c ≠ some d0) (hne0 : d0 ≠ src) (hd0 : w.2.1 d0 = some .nullCap)
    (hc0 : ∀ r ∈ capRng c0, r.toNat ∈ utR p0 o)
    (hU0 : ∀ d b n f, c0 = .untypedCap d b n f → ∀ k ∈ utR b n, k ∈ utR p0 o)
    {x : CslotPtr × ObjRef} (hx : ItemN w src o U x) (hxd : x.1 ≠ d0)
    (hdisj : ∀ k ∈ utR p0 o, k ∉ utR x.2 o) (hdout : d0.1.toNat ∉ utR x.2 o) :
    ItemN (vCC src d0 c0 w) src o U x := by
  obtain ⟨h1, ⟨s1, c1, hs1, hr1, hz1, hsh1⟩, h3, h4, h5, h6, h7⟩ := hx
  refine ⟨?_, ⟨s1, c1, ?_, hr1, hz1, hsh1⟩, lu_kids h4 h3, h4, ?_, ?_, ?_⟩
  · rw [vCC_cap, if_neg hxd]; exact h1
  · rw [vCC_cap, if_neg]
    · exact hs1
    · intro e; subst e; rw [hd0] at hs1; cases hs1; exact sRefs_nn hr1 rfl
  · intro s c r hs hr
    rcases vCC_cases hs with ⟨-, rfl⟩ | ⟨-, hs⟩
    · exact hdisj _ (hc0 r hr)
    · exact h5 s c r hs hr
  · intro y c hy hin
    rcases vCC_cases hy with ⟨rfl, -⟩ | ⟨-, hy⟩
    · exact absurd hin hdout
    · exact h6 y c hy hin
  · intro u d b n f hu hus k hk hkb
    rcases vCC_cases hus with ⟨-, e⟩ | ⟨-, hus'⟩
    · exact absurd hk (hdisj k (hU0 d b n f e.symm k hkb))
    · obtain ⟨h1', h2'⟩ := h7 u d b n f hu hus' k hk hkb
      exact ⟨desc_cc hk0 hne0 (Ne.symm hne0) h1', h2'⟩

/-- **The `create_cap` loop keeps `NV N`.** -/
theorem nv_ccLoop (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev dS : Bool) (bS : ObjRef) (nS fS : Nat)
    (hsz : sz < 64) (hnS : nS < 64) (hfS : bS.toNat + 2 ^ nS ≤ 2 ^ 64) :
    ∀ (L : List (CslotPtr × ObjRef)) (w : UView), NV N w → UtFitV w → w.2.1 src = some (.untypedCap dS bS nS fS) →
      L.Pairwise (fun x y => x.1 ≠ y.1 ∧ ∀ k ∈ utR x.2 (fl4ObjBitsApi ty sz), k ∉ utR y.2 (fl4ObjBitsApi ty sz)) →
      (∀ x ∈ L, ∀ y ∈ L, x.1.1.toNat ∉ utR y.2 (fl4ObjBitsApi ty sz)) →
      (∀ x ∈ L, x.2.toNat + 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64 ∧
        ∀ k ∈ utR x.2 (fl4ObjBitsApi ty sz), k ∈ utR bS nS ∧ k ∉ utFr bS nS fS) →
      (∀ x ∈ L, ItemN w src (fl4ObjBitsApi ty sz) (decide (ty = .untyped)) x) →
      HV (· = w) (NV N) (NonDet.mapMx (createCap (Z := Unit) ty sz src dev) L)
  | [], w, hN, _, _, _, _, _, _ => by unfold NonDet.mapMx; exact hv_ret' _ hN
  | (d, p) :: L, w, hN, hF, hs, hP, hO, hB, hI => by
    unfold NonDet.mapMx
    refine hv_bind' (hv_createCap ty sz src dev d p w) fun _ => ?_
    rw [List.pairwise_cons] at hP
    obtain ⟨hd, hDR, hk, hne, hfr, hsl, hanc⟩ := hI (d, p) List.mem_cons_self
    obtain ⟨hpf, hpin⟩ := hB (d, p) List.mem_cons_self
    have hcr := capRng_default ty sz dev p hpf
    have hdelS := mem_delR_iff hnS hfS
    have hNw : NV N (vCC src d (defaultCap ty p sz dev) w) := by
      by_cases hty : ty = .untyped
      · subst hty
        have hpd := mem_delR_iff hsz hpf
        exact nv_ccU hN hd hDR hk hne hs hpd hfr
          (fun x c' hx hdel => by have := (hsl x c' hx ((hpd _).1 hdel)).2; simp at this)
          (fun r hr => (hdelS r).2 (hpin _ ((hpd r).1 hr)).1)
      · refine nv_cc hN hd hDR hk hne hs (defaultCap_nonUt hty _ _ _) (defaultCap_nz _ _ _ _)
          (defaultCap_bits _ _ hsz _) ?_ ?_ ?_ ?_ ?_
        · intro s c' r hs' hr hr'
          exact hfr s c' r hs' hr' (hcr r hr)
        · intro r hr i c' hi
          exact (hsl (r, i) c' hi (hcr r (sRefs_sub_capRng _ hr))).1
        · intro r hr; exact (hdelS r).2 (hpin _ (hcr r hr)).1
        · intro r hr; exact (hpin _ (hcr r hr)).2
        · intro u d' b n f hu hus r hr hrd
          obtain ⟨hn', hf'⟩ := hF u d' b n f hus
          have hrd' : r.toNat ∈ utR b n := by
            rcases hrd with h | h
            · exact (mem_delR_iff hn' hf' r).1 h
            · exact h
          exact hanc u d' b n f hu hus r.toNat (hcr r hr) hrd'
    refine nv_ccLoop ty sz src dev dS bS nS fS hsz hnS hfS L _ hNw ?_ ?_ hP.2 ?_ ?_ ?_
    · intro u d' b n f hu
      rcases vCC_cases hu with ⟨-, e⟩ | ⟨-, hu'⟩
      · by_cases hty : ty = .untyped
        · subst hty; cases e; exact ⟨hsz, hpf⟩
        · exact absurd e.symm (defaultCap_nonUt hty _ _ _ _ _ _ _)
      · exact hF u d' b n f hu'
    · rw [vCC_cap, if_neg (Ne.symm hne)]; exact hs
    · exact fun x hx y hy => hO x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    · exact fun x hx => hB x (List.mem_cons_of_mem _ hx)
    · intro x hx
      refine itemN_step hk hne hd hcr ?_ (hI x (List.mem_cons_of_mem _ hx)) (hP.1 x hx).1.symm (hP.1 x hx).2
        (hO (d, p) List.mem_cons_self x (List.mem_cons_of_mem _ hx))
      intro d' b n f e k hk'
      by_cases hty : ty = .untyped
      · subst hty; cases e; exact hk'
      · exact absurd e (defaultCap_nonUt hty _ _ _ _ _ _ _)

end

end Fl4Proofs.P3.SInvU
