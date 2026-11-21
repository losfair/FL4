/-
P3 (DESIGN.md §9), invariant line G1 (sl4): **the carried form of `ScKind`**
and its cap-writer leaves (groundwork for removing sl3's `ScKind` from the tops;
spec side only).

* **`ScKindR`** (l4v `valid_caps` typing over `cap_range`): a cap whose RANGE
  (ut6's `capRng`: a frame cap covers its whole frame) contains the object of an
  SC cap is an SC cap to that object. It implies sl3's `ScKind` (`scKind_of_R`).
  The range form is what the writers need: DeriveSubframe makes caps to interior
  pages of a large frame, whose cap names only its base; a retyped SC is fresh
  for ut1's `CapFreeV`, which speaks of ranges.
* Leaves: `skr_of_uk` (view frames), `skr_of_kheap`, `skr_setCap_g` (a general
  cap write), `skr_setCap_null`, **`KindRel c0 c`** (a derived cap: SC-ness both
  ways, range inside the source's) and **`skr_capInsert_kr`** (cap_insert of a
  cap `KindRel` to the source slot's cap), `skr_setCap_fresh` (a cap whose range
  no other cap meets: `create_cap` of a retyped object).
-/
import Fl4Proofs.P3.SpecInvSlC
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000

/-- **ScKindR** (see the module docstring). -/
def ScKindRV (w : UView) : Prop :=
  ∀ s r b s' c', w.2.1 s = some (.schedContextCap r b) → w.2.1 s' = some c' → r ∈ capRng c' →
    ∃ b', c' = .schedContextCap r b'

abbrev ScKindR (σ : State Unit) : Prop := ScKindRV (uV σ)

theorem scKind_of_R {w : UView} (h : ScKindRV w) : ScKindV w :=
  fun s r b s' c' h1 h2 h3 => h s r b s' c' h1 h2 (objRefs_sub_capRng c' h3)

theorem skr_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK ScKindR m := by
  intro σ hσ x hx
  have e := h (uV σ) σ rfl x hx
  show ScKindRV (uV x.2); rw [e]; exact hσ

theorem skr_of_kheap {σ σ' : State Unit} (e : σ'.kheap = σ.kheap) (h : ScKindR σ) : ScKindR σ' := by
  have hc : SInvU.capAt σ' = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [e]
  intro s r b s' c' h1 h2 h3
  change SInvU.capAt σ' s = _ at h1
  change SInvU.capAt σ' s' = _ at h2
  rw [hc] at h1 h2
  exact h s r b s' c' h1 h2 h3

/-- **A general cap write**: a new SC cap's object is in the range only of SC
caps to it elsewhere; an object in the new cap's range is that SC cap's, or no
SC cap elsewhere names it. -/
theorem skr_setCap_g (c : Cap) (sl : CslotPtr) (σ : State Unit)
    (hc1 : ∀ r b, c = .schedContextCap r b → ∀ s' c', s' ≠ sl → SInvU.capAt σ s' = some c' → r ∈ capRng c' →
      ∃ b', c' = .schedContextCap r b')
    (hc2 : ∀ r ∈ capRng c, (∃ b, c = .schedContextCap r b) ∨
      ∀ s b, s ≠ sl → SInvU.capAt σ s ≠ some (.schedContextCap r b)) :
    IKp ScKindR σ (setCap (Z := Unit) c sl) := by
  intro hK y hy
  obtain ⟨-, hne, hsl, -, -⟩ := SInvU.setCap_out hy
  intro s r b s' c' hs hs' hrr
  change SInvU.capAt y.2 s = _ at hs
  change SInvU.capAt y.2 s' = _ at hs'
  by_cases ess : s' = s
  · subst ess; rw [hs] at hs'; cases hs'; exact ⟨b, rfl⟩
  by_cases es : s = sl
  · subst es
    rcases hsl with h | h
    · rw [h] at hs
      have h' : SInvU.capAt σ s' = some c' := by rw [← hne s' ess]; exact hs'
      exact hK _ r b s' c' hs h' hrr
    · rw [h] at hs; cases hs
      exact hc1 r b rfl s' c' ess (by rw [← hne s' ess]; exact hs') hrr
  · have hs0 : SInvU.capAt σ s = some (.schedContextCap r b) := by rw [← hne s es]; exact hs
    by_cases es' : s' = sl
    · subst es'
      rcases hsl with h | h
      · exact hK s r b _ c' hs0 (by show SInvU.capAt σ _ = _; rw [← h]; exact hs') hrr
      · rw [h] at hs'; cases hs'
        rcases hc2 r hrr with hb | hn
        · exact hb
        · exact absurd hs0 (hn s b es)
    · exact hK s r b s' c' hs0 (by show SInvU.capAt σ s' = _; rw [← hne s' es']; exact hs') hrr

theorem skr_setCap_null (sl : CslotPtr) : IK ScKindR (setCap (Z := Unit) .nullCap sl) :=
  fun σ => skr_setCap_g _ _ σ (fun _ _ h => by cases h) (fun r hr => by simp [capRng, objRefs] at hr)

/-- A cap whose range meets no other slot's cap's range, and that is no SC cap
or names an object no other slot's SC cap names. -/
theorem skr_setCap_fresh (c : Cap) (sl : CslotPtr) (σ : State Unit)
    (hF : ∀ r ∈ capRng c, ∀ s' c', s' ≠ sl → SInvU.capAt σ s' = some c' → r ∉ capRng c')
    (hS : ∀ r b, c = .schedContextCap r b → r ∈ capRng c) :
    IKp ScKindR σ (setCap (Z := Unit) c sl) := by
  refine skr_setCap_g c sl σ (fun r b e s' c' hs' h0 hr => absurd hr (hF r (hS r b e) s' c' hs' h0)) fun r hr => ?_
  refine Or.inr fun s b hs e => hF r hr s _ hs e ?_
  simp [capRng, objRefs]

/-- **A derived cap**: SC-ness both ways, the range inside the source's. -/
def KindRel (c0 c : Cap) : Prop :=
  (∀ r b, c = .schedContextCap r b → ∃ b', c0 = .schedContextCap r b') ∧
    (∀ r b, c0 = .schedContextCap r b → ∃ b', c = .schedContextCap r b') ∧ capRng c ⊆ capRng c0

theorem kindRel_refl (c : Cap) : KindRel c c :=
  ⟨fun _ b e => ⟨b, e⟩, fun _ b e => ⟨b, e⟩, fun _ h => h⟩

theorem capRng_untyped {c : Cap} (h : isUntypedCap c = true) : capRng c = ∅ := by
  cases c <;> simp_all [isUntypedCap, capRng, objRefs]

/-- `set_untyped_cap_as_full` keeps ScKindR. -/
theorem skr_setUntypedCapAsFull (srcCap newCap : Cap) (src : CslotPtr) :
    IK ScKindR (setUntypedCapAsFull (Z := Unit) srcCap newCap src) := by
  intro σ hσ y hy
  unfold setUntypedCapAsFull at hy
  split at hy
  · rename_i hu
    have hu1 := hu.1
    cases srcCap <;> simp [isUntypedCap] at hu1
    refine skr_setCap_g _ _ σ (fun r b e => by simp [freeIndexUpdate] at e) (fun r hr => ?_) hσ y hy
    simp [freeIndexUpdate, capRng, objRefs] at hr
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ

/-- **`cap_insert` of a cap `KindRel` to the source slot's cap.** -/
theorem skr_capInsert_kr (newCap : Cap) (src dest : CslotPtr) (σ : State Unit) (c0 : Cap)
    (hc : SInvU.capAt σ src = some c0) (hk : KindRel c0 newCap) :
    IKp ScKindR σ (capInsert (Z := Unit) newCap src dest) := by
  intro hσ x hx
  unfold capInsert at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := SInvU.getCap_capAt hy1
  obtain ⟨srcCap, s1⟩ := y1
  simp only at e1 hc1; subst s1
  have es : srcCap = c0 := Option.some.inj (hc1.symm.trans hc)
  subst es
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨e3, hc3⟩ := SInvU.getCap_capAt hy3
  obtain ⟨oldCap, s3⟩ := y3
  simp only at e3 hc3; subst s3
  obtain ⟨y4, ⟨ha, rfl⟩, hx⟩ := hx
  simp only at ha
  obtain ⟨y5, hy5, hx⟩ := hx
  have h5 : ScKindR y5.2 := skr_setUntypedCapAsFull _ _ _ σ hσ y5 hy5
  -- the source keeps an SC cap (an SC cap is no untyped cap)
  have hsrc : ∀ r b, srcCap = .schedContextCap r b → SInvU.capAt y5.2 src = some (.schedContextCap r b) := by
    intro r b e
    unfold setUntypedCapAsFull at hy5
    split at hy5
    · rename_i hu; rw [e] at hu; simp [isUntypedCap] at hu
    · rw [Set.mem_singleton_iff.1 hy5, hc, e]
  obtain ⟨y6, hy6, hx⟩ := hx
  have h6 : ScKindR y6.2 := by
    refine skr_setCap_g newCap dest y5.2 (fun r b e s' c' hs' h0 hr => ?_) (fun r hr => ?_) h5 y6 hy6
    · obtain ⟨b', e'⟩ := hk.1 r b e
      exact h5 src r b' s' c' (hsrc r b' e') h0 hr
    · by_cases hs : ∃ b, newCap = .schedContextCap r b
      · exact Or.inl hs
      · refine Or.inr fun s b' _ e => hs ?_
        have hsrc5 : ∃ c5, SInvU.capAt y5.2 src = some c5 ∧ r ∈ capRng c5 := by
          by_cases hu : ∃ r' b'', srcCap = .schedContextCap r' b''
          · obtain ⟨r', b'', e''⟩ := hu
            exact ⟨_, hsrc r' b'' e'', e'' ▸ hk.2.2 hr⟩
          · unfold setUntypedCapAsFull at hy5
            split at hy5
            · rename_i hu'
              rw [capRng_untyped hu'.2.1] at hr; simp at hr
            · rw [Set.mem_singleton_iff.1 hy5]; exact ⟨_, hc, hk.2.2 hr⟩
        obtain ⟨c5, h5c, h5r⟩ := hsrc5
        obtain ⟨b5, e5⟩ := h5 s r b' src c5 e h5c h5r
        have : c5 = srcCap ∨ ∃ r' b'', srcCap = .schedContextCap r' b'' := by
          unfold setUntypedCapAsFull at hy5
          split at hy5
          · rename_i hu'
            rw [capRng_untyped hu'.2.1] at hr; simp at hr
          · left; rw [Set.mem_singleton_iff.1 hy5, hc] at h5c; exact (Option.some.inj h5c).symm
        rcases this with e6 | ⟨r', b'', e''⟩
        · subst e6; rw [e5] at hk; exact hk.2.1 r b5 rfl
        · rw [hsrc r' b'' e''] at h5c; cases h5c; cases e5; rw [e''] at hk; exact hk.2.1 _ _ rfl
  refine (?_ : IK ScKindR _) y6.2 h6 x hx
  repeat' (first | (with_reducible exact ik_doExtendedOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

end

end Fl4Proofs.P3.SInvL
