/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut4): **a derived cap put
into a null slot as a CDT leaf keeps the six facts of `UtInv''`** (spec side
only; imports SpecInvUtN).

`utN_leaf`: the view after writing `c` (derived from the cap `c0` of `src`,
`RefRel c0 c`) into the null slot `dest` with CDT parent `src` or `src`'s parent
(`cap_insert` of a non-untyped cap). The destination must be reachable through a
non-Zombie slot-holding cap (`DestRefV`: the lookup that found it); this is the
decode / transfer fact the callers carry.
-/
import Fl4Proofs.P3.SpecInvUtN
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- What `derive_cap` / `mask_cap` / `update_cap_data` give for a non-untyped
cap: no new reference, the same shape, no Zombie, and nothing from a Zombie. -/
def RefRel (c0 c : Cap) : Prop :=
  capRng c ⊆ capRng c0 ∧ shp c = shp c0 ∧ (∀ r b n, c ≠ .zombie r b n) ∧
    (∀ r b n, c0 = .zombie r b n → capRng c = ∅) ∧ (∀ d b n f, c ≠ .untypedCap d b n f)

/-- The slot is reached through a non-Zombie slot-holding cap, within its range. -/
def DestRefV (w : UView) (dest : CslotPtr) : Prop :=
  ∃ s1 c1, w.2.1 s1 = some c1 ∧ dest.1 ∈ sRefs c1 ∧ (∀ r b n, c1 ≠ .zombie r b n) ∧ SlotShape c1 dest.2

theorem slotShape_shp {a b : Cap} (h : shp a = shp b) (ha : ∀ r x n, a ≠ .zombie r x n)
    (hb : ∀ r x n, b ≠ .zombie r x n) {i : CnodeIndex} (hs : SlotShape a i) (hr : ∃ x, shp a = some x) :
    SlotShape b i := by
  obtain ⟨x, hx⟩ := hr
  cases a <;> cases b <;> simp_all [shp, SlotShape]

theorem upd_cap {f : CslotPtr → Option Cap} {d sl : CslotPtr} {c x : Cap}
    (h : Function.update f d (some c) sl = some x) : (sl = d ∧ x = c) ∨ (sl ≠ d ∧ f sl = some x) := by
  by_cases e : sl = d
  · subst e; rw [Function.update_self] at h; exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [Function.update_of_ne e] at h; exact Or.inr ⟨e, h⟩

theorem utN_leaf {w w' : UView} (hI : UtInv'V w) (hN : UtNV w) {src dest : CslotPtr} {c0 c : Cap}
    {v : Option CslotPtr} (hd : w.2.1 dest = some .nullCap) (hs : w.2.1 src = some c0) (hR : RefRel c0 c)
    (hv : v = some src ∨ v = w.2.2.1 src) (hvd : v ≠ some dest) (hD : DestRefV w dest)
    (h1 : w'.2.1 = Function.update w.2.1 dest (some c)) (h2 : w'.2.2.1 = Function.update w.2.2.1 dest v) :
    UtNV w' := by
  obtain ⟨-, hO, -⟩ := hI
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  obtain ⟨hRo, hRs, hRz, hRz0, hRu⟩ := hR
  obtain ⟨s1, c1, hs1, hr1, hz1, hsh1⟩ := hD
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hc1n : c1 ≠ .nullCap := sRefs_nn hr1
  have hs1d : s1 ≠ dest := fun e => by subst e; rw [hd] at hs1; cases hs1; exact hc1n rfl
  have hcap : ∀ sl x, w'.2.1 sl = some x → (sl = dest ∧ x = c) ∨ (sl ≠ dest ∧ w.2.1 sl = some x) :=
    fun sl x h => upd_cap (h1 ▸ h)
  have hold : ∀ sl, sl ≠ dest → w'.2.1 sl = w.2.1 sl := fun sl e => by rw [h1]; exact Function.update_of_ne e _ _
  have hut : ∀ u d b n f, w'.2.1 u = some (.untypedCap d b n f) → u ≠ dest ∧ w.2.1 u = some (.untypedCap d b n f) := by
    intro u d b n f h
    rcases hcap u _ h with ⟨-, e⟩ | h'
    · exact absurd e.symm (hRu d b n f)
    · exact h'
  have htg : ∀ x y, y ≠ dest → Relation.TransGen (parentOf w.2.2.1) x y →
      Relation.TransGen (parentOf w'.2.2.1) x y := fun x y hy h => by rw [h2]; exact (lu_tg hk hvd hy).2 h
  have hsd : ∀ r, r ∈ capRng c → src ≠ dest := by
    intro r hr e; subst e; rw [hd] at hs; cases hs; exact absurd (hRo hr) (by simp [capRng, objRefs])
  have hsR : ∀ r, r ∈ sRefs c → r ∈ sRefs c0 := by
    intro r hr
    obtain ⟨x, hx⟩ := shp_of_sRefs hr
    exact sRefs_of_shp (objRefs_of_capRng_shp (hRo (sRefs_sub_capRng c hr)) (hRs ▸ hx)) (hRs ▸ hx)
  have hz0 : ∀ r, r ∈ capRng c → ∀ a b n, c0 ≠ .zombie a b n := fun r hr a b n e => by
    rw [hRz0 a b n e] at hr; exact hr.elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- UtCh
    intro u d b n f hu s' c' r hs' hr hrd
    obtain ⟨hud, hu⟩ := hut u d b n f hu
    rcases hcap s' c' hs' with ⟨e, rfl⟩ | ⟨hne, hs'⟩
    · rw [e]
      have hsrc : Relation.TransGen (parentOf w.2.2.1) u src := hC u d b n f hu src c0 r hs (hRo hr) hrd
      have hsd' := hsd r hr
      have hdp : w'.2.2.1 dest = v := by rw [h2]; exact Function.update_self _ _ _
      show Relation.TransGen (parentOf w'.2.2.1) u dest
      rcases hv with hv | hv
      · exact Relation.TransGen.tail (htg u src hsd' hsrc) (show w'.2.2.1 dest = some src by rw [hdp, hv])
      · obtain ⟨b', hb0, hb'⟩ := Relation.TransGen.tail'_iff.1 hsrc
        have hb'' : w.2.2.1 src = some b' := hb'
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 hb0 with e | hb
        · rw [e] at hb''
          exact Relation.TransGen.single (show w'.2.2.1 dest = some u by rw [hdp, hv]; exact hb'')
        · have hb'' : w.2.2.1 src = some b' := hb'
          have hbd : b' ≠ dest := fun e => hk src (e ▸ hb'')
          exact Relation.TransGen.tail (htg u b' hbd hb) (show w'.2.2.1 dest = some b' by rw [hdp, hv]; exact hb'')
    · exact htg u s' hne (hC u d b n f hu s' c' r hs' hr hrd)
  · -- IfUnsafe
    intro p cp hp hne hin
    have hin' : InUtV w p.1 := by
      obtain ⟨u, d, b, n, f, hu, hr⟩ := hin; exact ⟨u, d, b, n, f, (hut u d b n f hu).2, hr⟩
    rcases hcap p cp hp with ⟨rfl, -⟩ | ⟨hpd, hp⟩
    · exact ⟨s1, c1, (hold s1 hs1d).trans hs1, hr1⟩
    · obtain ⟨s0, c0', hs0, hr0⟩ := hU p cp hp hne hin'
      have hs0d : s0 ≠ dest := fun e => by
        subst e; rw [hd] at hs0; cases hs0; exact sRefs_nn hr0 rfl
      exact ⟨s0, c0', (hold s0 hs0d).trans hs0, hr0⟩
  · -- CapFree
    intro u d b n f hu s' c' r hs' hr
    have hu' := (hut u d b n f hu).2
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · exact hF u d b n f hu' src c0 r hs (hRo hr)
    · exact hF u d b n f hu' s' c' r hs' hr
  · -- CapKind
    intro sa ca sb cb r ha hb hra hrb
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩ <;> rcases hcap sb cb hb with ⟨-, rfl⟩ | ⟨-, hb'⟩
    · rfl
    · rw [hRs]; exact hK src c0 sb cb r hs hb' (hRo hra) hrb
    · rw [hRs]; exact hK sa ca src c0 r ha' hs hra (hsR r hrb)
    · exact hK sa ca sb cb r ha' hb' hra hrb
  · -- CnShape
    intro sa ca r ha hr i c' hi hne
    have hcz : ∀ (sa : CslotPtr) (ca : Cap), r ∈ sRefs c1 → w.2.1 sa = some ca → r ∈ objRefs ca → sa ≠ s1 →
        ∀ a b n, ca ≠ .zombie a b n := by
      intro sa ca hr1 ha hra hne a b n e
      subst e
      have hra' : r = a := by simpa [objRefs] using hra
      rw [← hra'] at ha
      exact hZ sa r b n ha s1 c1 (Ne.symm hne) hs1 (sRefs_sub c1 hr1)
    rcases hcap (r, i) c' hi with ⟨e, rfl⟩ | ⟨hid, hi'⟩
    · -- the written slot
      have hr1' : r ∈ sRefs c1 := by rw [show r = dest.1 by rw [← e]]; exact hr1
      have hsh1' : SlotShape c1 i := by rw [show i = dest.2 by rw [← e]]; exact hsh1
      rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · have h0 : shp c0 = shp c1 := hK src c0 s1 c1 r hs hs1 (hRo (sRefs_sub_capRng _ hr)) hr1'
        exact slotShape_shp (h0.symm.trans hRs.symm) hz1 hRz hsh1' (shp_of_sRefs hr1')
      · have hne1 : sa ≠ s1 ∨ ca = c1 := by
          by_cases e1 : sa = s1
          · subst e1; rw [hs1] at ha'; exact Or.inr (Option.some.inj ha').symm
          · exact Or.inl e1
        have hzca : ∀ a b n, ca ≠ .zombie a b n := by
          rcases hne1 with h | rfl
          · exact hcz sa ca hr1' ha' (sRefs_sub _ hr) h
          · exact hz1
        have h0 : shp ca = shp c1 := hK sa ca s1 c1 r ha' hs1 (sRefs_sub_capRng _ hr) hr1'
        exact slotShape_shp h0.symm hz1 hzca hsh1' (shp_of_sRefs hr1')
    · rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · have hr0 := hsR r hr
        have hz0' := hz0 r (sRefs_sub_capRng _ hr)
        exact slotShape_shp hRs.symm hz0' hRz (hS src c0 r hs hr0 i c' hi' hne) (shp_of_sRefs hr0)
      · exact hS sa ca r ha' hr i c' hi' hne
  · -- ZFinal
    intro sz r b n hz s' c' hne hs'
    rcases hcap sz _ hz with ⟨-, e⟩ | ⟨hzd, hz'⟩
    · exact absurd e.symm (hRz r b n)
    · rcases hcap s' c' hs' with ⟨rfl, rfl⟩ | ⟨-, hs''⟩
      · intro hr
        by_cases e : src = sz
        · subst e; rw [hz'] at hs; cases hs; exact hz0 r (objRefs_sub_capRng _ hr) r b n rfl
        · have hrc : r ∈ capRng c0 := hRo (objRefs_sub_capRng _ hr)
          have hsh : shp c0 = some b := hK src c0 sz _ r hs hz' hrc (by simp [sRefs])
          exact hZ sz r b n hz' src c0 e hs (objRefs_of_capRng_shp hrc hsh)
      · exact hZ sz r b n hz' s' c' hne hs''
  · -- CnBits
    intro sa ca ha
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
    · intro b hb; exact hB src c0 hs b (by rw [← hRs]; exact hb)
    · exact hB sa ca ha'

/-- **`cap_insert` of a derived non-untyped cap keeps `UtInv''`**, given the
derivation relation to the source's cap and the destination's lookup fact. -/
theorem hv_capInsertN (c : Cap) (src dest : CslotPtr) :
    HV (fun w => UtInv''V w ∧ (∀ c0, w.2.1 src = some c0 → RefRel c0 c) ∧ DestRefV w dest) UtInv''V
      (capInsert (Z := Unit) c src dest) := by
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  obtain ⟨hw, hrr, hD⟩ := hw
  have hR := hrr sc hsc
  have hnu := hR.2.2.2.2
  have hnu' : isUntypedCap c = false := by
    cases c <;> first | rfl | exact absurd rfl (hnu _ _ _ _)
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hw.1.2.1 x dest hx; rw [hoc] at hc'; cases hc'; exact hcn rfl
  unfold setUntypedCapAsFull
  rw [if_neg (fun h => by rw [hnu'] at h; exact Bool.false_ne_true h.2.1)]
  refine hv_pure_bind ?_
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
  refine ⟨utInv'_leaf hw.1 hk ?hv hnu, utN_leaf hw.1 hw.2 hoc hsc hR ?hor ?hnd hD rfl rfl⟩
  case hv =>
    intro p hp
    split at hp
    · rename_i hpar
      obtain rfl := Option.some.inj hp
      have hnn := sameRegionAs_nn (of_decide_eq_true hpar).2.1
      refine ⟨fun e => ?_, sc, hsc, hnn⟩
      subst e; rw [hoc] at hsc; cases hsc; exact hnn rfl
    · have hp' : w.2.2.1 src = some p := hp
      exact ⟨fun e => hk src (e ▸ hp'), hw.1.2.1 src p hp'⟩
  case hor =>
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  case hnd =>
    intro hp
    split at hp
    · rename_i hpar
      have hnn := sameRegionAs_nn (of_decide_eq_true hpar).2.1
      obtain rfl := Option.some.inj hp
      rw [hoc] at hsc; cases hsc; exact hnn rfl
    · exact hk src hp

end

end Fl4Proofs.P3.SInvU
