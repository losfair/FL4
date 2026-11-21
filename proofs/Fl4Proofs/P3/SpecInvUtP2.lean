/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut8): **the cap-view steps
of the untyped performs keep `NV N = UtNV ∧ IrqOutV N`** (spec side only;
imports SpecInvUtP1). `UtInv'` along the same chains is ut2/ut3's.

* `nv_sameNN`: a view with the same non-null caps and the same CDT (what
  `retype_region` and `delete_objects` of a region with only null slots do).
* `nv_setUt`: rewriting a slot's untyped cap with another free index, when no
  cap covers an address of the new free part (the free-index raise of a retype,
  the free-index writes of a reset).
* `nv_cc` / `nv_ccU`: `create_cap` of a new non-untyped / untyped cap at a null
  CDT-leaf destination reached through a CNode (`DestRefV`), for an object no
  existing cap covers, inside the source untyped's region below its free index,
  every other untyped cap overlapping it being an ancestor of the source.
-/
import Fl4Proofs.P3.SpecInvUtP1
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The new facts with the IRQ-node fact. -/
def NV (N : Irq → ObjRef) (w : UView) : Prop := UtNV w ∧ IrqOutV N w

variable {N : Irq → ObjRef}

theorem ut_nn {d : Bool} {b : ObjRef} {n f : Nat} : Cap.untypedCap d b n f ≠ .nullCap := fun e => by cases e

theorem covR_nn {c : Cap} {r : ObjRef} (h : r ∈ covR c) : c ≠ .nullCap := by
  rintro rfl; rw [covR_null] at h; exact h

/-! ## Same non-null caps -/

theorem nv_sameNN {w w' : UView} (hcdt : w'.2.2.1 = w.2.2.1)
    (h1 : ∀ s c, w'.2.1 s = some c → c ≠ .nullCap → w.2.1 s = some c)
    (h2 : ∀ s c, w.2.1 s = some c → c ≠ .nullCap → w'.2.1 s = some c) (h : NV N w) : NV N w' := by
  obtain ⟨⟨hC, hU, hF, hK, hS, hZ, hB⟩, hO⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u d b n f hu s c r hs hr hrd
    show s ∈ descendantsOf u w'.2.2.1
    rw [hcdt]; exact hC u d b n f (h1 _ _ hu ut_nn) s c r (h1 _ _ hs (capRng_nn hr)) hr hrd
  · intro p c hp hne hin
    obtain ⟨u, d, b, n, f, hu, hr⟩ := hin
    obtain ⟨s, c', hs, hr'⟩ := hU p c (h1 _ _ hp hne) hne ⟨u, d, b, n, f, h1 _ _ hu ut_nn, hr⟩
    exact ⟨s, c', h2 _ _ hs (sRefs_nn hr'), hr'⟩
  · intro u d b n f hu s c r hs hr
    exact hF u d b n f (h1 _ _ hu ut_nn) s c r (h1 _ _ hs (capRng_nn hr)) hr
  · intro sa ca sb cb r ha hb hra hrb
    exact hK sa ca sb cb r (h1 _ _ ha (capRng_nn hra)) (h1 _ _ hb (sRefs_nn hrb)) hra hrb
  · intro sa ca r ha hr i c' hi hne
    exact hS sa ca r (h1 _ _ ha (sRefs_nn hr)) hr i c' (h1 _ _ hi hne) hne
  · intro sz r b n hz s' c' hne hs' hr
    exact hZ sz r b n (h1 _ _ hz (fun e => by cases e)) s' c' hne (h1 _ _ hs' (objRefs_nn hr)) hr
  · intro s c hs
    by_cases hc : c = .nullCap
    · subst hc; intro b hb; cases hb
    · exact hB s c (h1 _ _ hs hc)
  · intro irq s c hs hr
    exact hO irq s c (h1 _ _ hs (covR_nn hr)) hr

/-! ## Rewriting an untyped cap's free index -/

theorem nv_setUt {w : UView} (h : NV N w) {src : CslotPtr} {d : Bool} {b : ObjRef} {n f f' : Nat}
    (h0 : w.2.1 src = some (.untypedCap d b n f))
    (hfree : ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r.toNat ∉ utFr b n f') :
    NV N (vCap src (.untypedCap d b n f') w) := by
  obtain ⟨⟨hC, hU, hF, hK, hS, hZ, hB⟩, hO⟩ := h
  have hcap : ∀ s c, (vCap src (.untypedCap d b n f') w).2.1 s = some c →
      (s = src ∧ c = .untypedCap d b n f') ∨ (s ≠ src ∧ w.2.1 s = some c) := fun s c h => upd_cap h
  have hkeep : ∀ s c, w.2.1 s = some c → (∀ d' b' n' f'', c ≠ .untypedCap d' b' n' f'') →
      (vCap src (.untypedCap d b n f') w).2.1 s = some c := by
    intro s c hs hnu
    rw [vCap_cap]
    split_ifs with e
    · subst e; rw [h0] at hs; cases hs; exact absurd rfl (hnu _ _ _ _)
    · exact hs
  have hnuR : ∀ c r, r ∈ capRng c → ∀ d' b' n' f'', c ≠ .untypedCap d' b' n' f'' := by
    intro c r hr d' b' n' f'' e; subst e; rw [capRng_ut] at hr; exact hr
  have hnuS : ∀ c r, r ∈ sRefs c → ∀ d' b' n' f'', c ≠ .untypedCap d' b' n' f'' := by
    intro c r hr d' b' n' f'' e; subst e; simp [sRefs] at hr
  have hold : ∀ s c r, (vCap src (.untypedCap d b n f') w).2.1 s = some c → r ∈ capRng c → w.2.1 s = some c := by
    intro s c r hs hr
    rcases hcap s c hs with ⟨-, rfl⟩ | ⟨-, hs⟩
    · rw [capRng_ut] at hr; exact hr.elim
    · exact hs
  have holdS : ∀ s c r, (vCap src (.untypedCap d b n f') w).2.1 s = some c → r ∈ sRefs c → w.2.1 s = some c :=
    fun s c r hs hr => hold s c r hs (sRefs_sub_capRng c hr)
  have hut : ∀ u d' b' n' f'', (vCap src (.untypedCap d b n f') w).2.1 u = some (.untypedCap d' b' n' f'') →
      ∃ f0, w.2.1 u = some (.untypedCap d' b' n' f0) ∧ (u = src → f'' = f') ∧ (u ≠ src → f0 = f'') := by
    intro u d' b' n' f'' hu
    rcases hcap u _ hu with ⟨rfl, e⟩ | ⟨hne, hu⟩
    · cases e; exact ⟨f, h0, fun _ => rfl, fun h => absurd rfl h⟩
    · exact ⟨f'', hu, fun h => absurd h hne, fun _ => rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u d' b' n' f'' hu s c r hs hr hrd
    obtain ⟨f0, hu0, -, -⟩ := hut u d' b' n' f'' hu
    exact hC u d' b' n' f0 hu0 s c r (hold s c r hs hr) hr hrd
  · intro p c hp hne hin
    obtain ⟨u, d', b', n', f'', hu, hr⟩ := hin
    obtain ⟨f0, hu0, -, -⟩ := hut u d' b' n' f'' hu
    have hp' : ∃ c0, w.2.1 p = some c0 ∧ c0 ≠ .nullCap := by
      rcases hcap p c hp with ⟨rfl, -⟩ | ⟨-, hp⟩
      · exact ⟨_, h0, ut_nn⟩
      · exact ⟨c, hp, hne⟩
    obtain ⟨c0, hp0, hn0⟩ := hp'
    obtain ⟨s, c', hs, hr'⟩ := hU p c0 hp0 hn0 ⟨u, d', b', n', f0, hu0, hr⟩
    exact ⟨s, c', hkeep s c' hs (hnuS c' _ hr'), hr'⟩
  · intro u d' b' n' f'' hu s c r hs hr
    obtain ⟨f0, hu0, h1, h2⟩ := hut u d' b' n' f'' hu
    by_cases e : u = src
    · subst e; rw [h1 rfl]; rw [h0] at hu0; cases hu0
      exact hfree s c r (hold s c r hs hr) hr
    · rw [← h2 e]; exact hF u d' b' n' f0 hu0 s c r (hold s c r hs hr) hr
  · intro sa ca sb cb r ha hb hra hrb
    exact hK sa ca sb cb r (hold _ _ _ ha hra) (holdS _ _ _ hb hrb) hra hrb
  · intro sa ca r ha hr i c' hi hne
    have ha' := holdS _ _ _ ha hr
    rcases hcap (r, i) c' hi with ⟨e, rfl⟩ | ⟨-, hi'⟩
    · exact hS sa ca r ha' hr i _ (e ▸ h0) ut_nn
    · exact hS sa ca r ha' hr i c' hi' hne
  · intro sz r b' n' hz s' c' hne hs' hr
    have hz' : w.2.1 sz = some (.zombie r b' n') := by
      rcases hcap sz _ hz with ⟨-, e⟩ | ⟨-, hz⟩
      · cases e
      · exact hz
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs''⟩
    · simp [objRefs] at hr
    · exact hZ sz r b' n' hz' s' c' hne hs'' hr
  · intro s c hs
    rcases hcap s c hs with ⟨-, rfl⟩ | ⟨-, hs⟩
    · intro b hb; cases hb
    · exact hB s c hs
  · intro irq s c hs hr
    rcases hcap s c hs with ⟨-, rfl⟩ | ⟨-, hs⟩
    · exact hO irq src _ h0 hr
    · exact hO irq s c hs hr

/-! ## `create_cap` -/

theorem vCC_cdt {src dest : CslotPtr} {dc : Cap} {w : UView} :
    (vCC src dest dc w).2.2.1 = Function.update w.2.2.1 dest (some src) := rfl

/-- The descendants after a `create_cap` at a leaf `dest` with parent `src`. -/
theorem desc_cc {t : Cdt} {src dest : CslotPtr} (hk : ∀ x, t x ≠ some dest) (hne : dest ≠ src) {u y : CslotPtr}
    (hy : y ≠ dest) (h : y ∈ descendantsOf u t) : y ∈ descendantsOf u (Function.update t dest (some src)) :=
  (lu_tg hk (fun e => hne (Option.some.inj e).symm) hy).2 h

theorem desc_cc_dest {t : Cdt} {src dest : CslotPtr} (hk : ∀ x, t x ≠ some dest) (hne : dest ≠ src) {u : CslotPtr}
    (h : u = src ∨ src ∈ descendantsOf u t) : dest ∈ descendantsOf u (Function.update t dest (some src)) := by
  have hd : parentOf (Function.update t dest (some src)) src dest := by
    show Function.update t dest (some src) dest = some src
    exact Function.update_self _ _ _
  rcases h with rfl | h
  · exact Relation.TransGen.single hd
  · exact Relation.TransGen.tail (desc_cc hk hne (fun e => hne e.symm) h) hd

/-- **`create_cap` of a new non-untyped cap keeps `NV N`.** -/
theorem nv_cc {w : UView} (hN : NV N w) {src dest : CslotPtr} {c : Cap} {dS : Bool} {bS : ObjRef} {nS fS : Nat}
    (hd : w.2.1 dest = some .nullCap) (hDR : DestRefV w dest) (hk : ∀ x, w.2.2.1 x ≠ some dest) (hne : dest ≠ src)
    (hsrc : w.2.1 src = some (.untypedCap dS bS nS fS))
    (hnu : ∀ d b n f, c ≠ .untypedCap d b n f) (hnz : ∀ r b n, c ≠ .zombie r b n) (hcb : CapBitsOK c)
    (hfr : ∀ s c' r, w.2.1 s = some c' → r ∈ capRng c → r ∉ capRng c')
    (hslots : ∀ r ∈ sRefs c, ∀ i c', w.2.1 (r, i) = some c' → c' = .nullCap)
    (hin : capRng c ⊆ delR bS nS) (hnf : ∀ r ∈ capRng c, r.toNat ∉ utFr bS nS fS)
    (hanc : ∀ u d b n f, u ≠ src → w.2.1 u = some (.untypedCap d b n f) → ∀ r ∈ capRng c,
      (r ∈ delR b n ∨ r.toNat ∈ utR b n) → src ∈ descendantsOf u w.2.2.1 ∧ r.toNat ∉ utFr b n f) :
    NV N (vCC src dest c w) := by
  obtain ⟨⟨hC, hU, hF, hK, hS, hZ, hB⟩, hO⟩ := hN
  have hcap : ∀ s x, (vCC src dest c w).2.1 s = some x → (s = dest ∧ x = c) ∨ (s ≠ dest ∧ w.2.1 s = some x) := by
    intro s x h; rw [vCC_cap] at h; split_ifs at h with e
    · exact Or.inl ⟨e, (Option.some.inj h).symm⟩
    · exact Or.inr ⟨e, h⟩
  have hkeep : ∀ s x, w.2.1 s = some x → x ≠ .nullCap → (vCC src dest c w).2.1 s = some x := by
    intro s x hs hx; rw [vCC_cap, if_neg]; · exact hs
    intro e; subst e; rw [hd] at hs; cases hs; exact hx rfl
  have hut : ∀ u d b n f, (vCC src dest c w).2.1 u = some (.untypedCap d b n f) →
      u ≠ dest ∧ w.2.1 u = some (.untypedCap d b n f) := by
    intro u d b n f h
    rcases hcap u _ h with ⟨-, e⟩ | h'
    · exact absurd e.symm (hnu d b n f)
    · exact h'
  have hcsrc : covR c ⊆ covR (.untypedCap dS bS nS fS) := by rw [covR_nonUt hnu]; exact hin
  have hdn : dest.1 ∉ sRefs c := by
    obtain ⟨s1, c1, hs1, hr1, -, -⟩ := hDR
    intro h; exact hfr s1 c1 dest.1 hs1 (sRefs_sub_capRng c h) (sRefs_sub_capRng c1 hr1)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- UtCh
    intro u d b n f hu s' c' r hs' hr hrd
    obtain ⟨hud, hu'⟩ := hut u d b n f hu
    rw [vCC_cdt]
    rcases hcap s' c' hs' with ⟨rfl, rfl⟩ | ⟨hs'd, hs''⟩
    · refine desc_cc_dest hk hne ?_
      by_cases e : u = src
      · exact Or.inl e
      · exact Or.inr (hanc u d b n f e hu' r hr (Or.inl hrd)).1
    · exact desc_cc hk hne hs'd (hC u d b n f hu' s' c' r hs'' hr hrd)
  · -- IfUnsafe
    intro p cp hp hne' hin'
    obtain ⟨u, d, b, n, f, hu, hr⟩ := hin'
    have hin0 : InUtV w p.1 := ⟨u, d, b, n, f, (hut u d b n f hu).2, hr⟩
    rcases hcap p cp hp with ⟨rfl, -⟩ | ⟨-, hp'⟩
    · obtain ⟨s0, c0, hs0, hr0⟩ := (posOK_of_destRef ⟨hC, hU, hF, hK, hS, hZ, hB⟩ hDR).1 hin0
      exact ⟨s0, c0, hkeep s0 c0 hs0 (sRefs_nn hr0), hr0⟩
    · obtain ⟨s0, c0, hs0, hr0⟩ := hU p cp hp' hne' hin0
      exact ⟨s0, c0, hkeep s0 c0 hs0 (sRefs_nn hr0), hr0⟩
  · -- CapFree
    intro u d b n f hu s' c' r hs' hr
    have hu' := (hut u d b n f hu).2
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs''⟩
    · by_cases e : u = src
      · subst e; rw [hsrc] at hu'; cases hu'; exact hnf r hr
      · intro hm
        exact (hanc u d b n f e hu' r hr (Or.inr (utFr_sub hm))).2 hm
    · exact hF u d b n f hu' s' c' r hs'' hr
  · -- CapKind
    intro sa ca sb cb r ha hb hra hrb
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩ <;> rcases hcap sb cb hb with ⟨-, rfl⟩ | ⟨-, hb'⟩
    · rfl
    · exact absurd (sRefs_sub_capRng cb hrb) (hfr sb cb r hb' hra)
    · exact absurd hra (hfr sa ca r ha' (sRefs_sub_capRng _ hrb))
    · exact hK sa ca sb cb r ha' hb' hra hrb
  · -- CnShape
    intro sa ca r ha hr i c' hi hne'
    rcases hcap (r, i) c' hi with ⟨e, rfl⟩ | ⟨hid, hi'⟩
    · rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · exact absurd (by rw [← e]; exact hr) hdn
      · have := (posOK_of_destRef ⟨hC, hU, hF, hK, hS, hZ, hB⟩ hDR).2 sa ca ha' (by rw [← e]; exact hr)
        rw [← e] at this; exact this
    · rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · exact absurd (hslots r hr i c' hi') hne'
      · exact hS sa ca r ha' hr i c' hi' hne'
  · -- ZFinal
    intro sz r b n hz s' c' hne' hs'
    have hz' : w.2.1 sz = some (.zombie r b n) := by
      rcases hcap sz _ hz with ⟨-, e⟩ | ⟨-, hz⟩
      · exact absurd e.symm (hnz r b n)
      · exact hz
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs''⟩
    · intro hr
      exact hfr sz _ r hz' (objRefs_sub_capRng _ hr) (objRefs_sub_capRng _ (by simp [objRefs]))
    · exact hZ sz r b n hz' s' c' hne' hs''
  · -- CnBits
    intro s x hs
    rcases hcap s x hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · exact hcb
    · exact hB s x hs'
  · -- IrqOut
    intro irq s x hs
    rcases hcap s x hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · exact fun h => hO irq src _ hsrc (hcsrc h)
    · exact hO irq s x hs'

/-- **`create_cap` of a new untyped cap keeps `NV N`.** -/
theorem nv_ccU {w : UView} (hN : NV N w) {src dest : CslotPtr} {dev : Bool} {p : ObjRef} {sz : Nat}
    {dS : Bool} {bS : ObjRef} {nS fS : Nat}
    (hd : w.2.1 dest = some .nullCap) (hDR : DestRefV w dest) (hk : ∀ x, w.2.2.1 x ≠ some dest) (hne : dest ≠ src)
    (hsrc : w.2.1 src = some (.untypedCap dS bS nS fS))
    (hpd : ∀ r, r ∈ delR p sz ↔ r.toNat ∈ utR p sz)
    (hfr : ∀ s c' r, w.2.1 s = some c' → r ∈ capRng c' → r.toNat ∉ utR p sz)
    (hemp : ∀ x c', w.2.1 x = some c' → x.1 ∉ delR p sz)
    (hin : delR p sz ⊆ delR bS nS) :
    NV N (vCC src dest (.untypedCap dev p sz 0) w) := by
  obtain ⟨⟨hC, hU, hF, hK, hS, hZ, hB⟩, hO⟩ := hN
  have hcap : ∀ s x, (vCC src dest (.untypedCap dev p sz 0) w).2.1 s = some x →
      (s = dest ∧ x = .untypedCap dev p sz 0) ∨ (s ≠ dest ∧ w.2.1 s = some x) := by
    intro s x h; rw [vCC_cap] at h; split_ifs at h with e
    · exact Or.inl ⟨e, (Option.some.inj h).symm⟩
    · exact Or.inr ⟨e, h⟩
  have hkeep : ∀ s x, w.2.1 s = some x → x ≠ .nullCap → (vCC src dest (.untypedCap dev p sz 0) w).2.1 s = some x := by
    intro s x hs hx; rw [vCC_cap, if_neg]; · exact hs
    intro e; subst e; rw [hd] at hs; cases hs; exact hx rfl
  have hold : ∀ s c r, (vCC src dest (.untypedCap dev p sz 0) w).2.1 s = some c → r ∈ capRng c →
      s ≠ dest ∧ w.2.1 s = some c := by
    intro s c r hs hr
    rcases hcap s c hs with ⟨-, rfl⟩ | h
    · rw [capRng_ut] at hr; exact hr.elim
    · exact h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- UtCh
    intro u d b n f hu s' c' r hs' hr hrd
    obtain ⟨hs'd, hs''⟩ := hold s' c' r hs' hr
    rw [vCC_cdt]
    rcases hcap u _ hu with ⟨-, e⟩ | ⟨hud, hu'⟩
    · cases e; exact absurd ((hpd r).1 hrd) (hfr s' c' r hs'' hr)
    · exact desc_cc hk hne hs'd (hC u d b n f hu' s' c' r hs'' hr hrd)
  · -- IfUnsafe
    intro q cp hq hne' hin'
    rcases hcap q cp hq with ⟨rfl, -⟩ | ⟨-, hq'⟩
    · obtain ⟨u, d, b, n, f, hu, hr⟩ := hin'
      rcases hcap u _ hu with ⟨-, e⟩ | ⟨-, hu'⟩
      · cases e; exact absurd hr (hemp _ _ hd)
      · obtain ⟨s0, c0, hs0, hr0⟩ :=
          (posOK_of_destRef ⟨hC, hU, hF, hK, hS, hZ, hB⟩ hDR).1 ⟨u, d, b, n, f, hu', hr⟩
        exact ⟨s0, c0, hkeep s0 c0 hs0 (sRefs_nn hr0), hr0⟩
    · obtain ⟨u, d, b, n, f, hu, hr⟩ := hin'
      rcases hcap u _ hu with ⟨-, e⟩ | ⟨-, hu'⟩
      · cases e; exact absurd hr (hemp _ _ hq')
      · obtain ⟨s0, c0, hs0, hr0⟩ := hU q cp hq' hne' ⟨u, d, b, n, f, hu', hr⟩
        exact ⟨s0, c0, hkeep s0 c0 hs0 (sRefs_nn hr0), hr0⟩
  · -- CapFree
    intro u d b n f hu s' c' r hs' hr
    obtain ⟨-, hs''⟩ := hold s' c' r hs' hr
    rcases hcap u _ hu with ⟨-, e⟩ | ⟨-, hu'⟩
    · cases e; intro hm; exact hfr s' c' r hs'' hr (utFr_sub hm)
    · exact hF u d b n f hu' s' c' r hs'' hr
  · -- CapKind
    intro sa ca sb cb r ha hb hra hrb
    exact hK sa ca sb cb r (hold _ _ _ ha hra).2 (hold _ _ _ hb (sRefs_sub_capRng _ hrb)).2 hra hrb
  · -- CnShape
    intro sa ca r ha hr i c' hi hne'
    have ha' := (hold _ _ _ ha (sRefs_sub_capRng _ hr)).2
    rcases hcap (r, i) c' hi with ⟨e, rfl⟩ | ⟨-, hi'⟩
    · have := (posOK_of_destRef ⟨hC, hU, hF, hK, hS, hZ, hB⟩ hDR).2 sa ca ha' (by rw [← e]; exact hr)
      rw [← e] at this; exact this
    · exact hS sa ca r ha' hr i c' hi' hne'
  · -- ZFinal
    intro sz' r b n hz s' c' hne' hs'
    have hz' : w.2.1 sz' = some (.zombie r b n) := by
      rcases hcap sz' _ hz with ⟨-, e⟩ | ⟨-, hz⟩
      · cases e
      · exact hz
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs''⟩
    · simp [objRefs]
    · exact hZ sz' r b n hz' s' c' hne' hs''
  · -- CnBits
    intro s x hs
    rcases hcap s x hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · intro b hb; cases hb
    · exact hB s x hs'
  · -- IrqOut
    intro irq s x hs
    rcases hcap s x hs with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · exact fun h => hO irq src _ hsrc (hin h)
    · exact hO irq s x hs'

end

end Fl4Proofs.P3.SInvU
