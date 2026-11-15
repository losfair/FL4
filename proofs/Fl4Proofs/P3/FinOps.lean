/-
P3 (DESIGN.md §9), CSpace: **the slot operations keep `FinInv`**
(`insert_full_fin`, `move_full_fin`, `swap_full_fin`, `empty_full_fin`,
`insert_ctl_full_fin`): first `FinM` from FL4's word-level effects
(`insert_finM`, `move_finM`, `swap_finM`, `empty_finM`, `insert_ctl_finM`),
then with the refinement and `MdbInv` of `MdbFull`/`CtlIns`, and `KTyped`
from the spec side (`FinSpec`).

A copied, moved or swapped cap names the source's object (`okey`): CNode
Copy, Mint, Move, Mutate and Rotate (`copied_okey`). A control cap's child
(an IRQ handler, an IO port) overlaps no cap of the MDB.
-/
import Fl4Proofs.P3.FinSpec
import Fl4Proofs.P3.CtlIns
import Fl4Proofs.P3.MdbStepOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem okey_fullF (a c : capability.Cap) : okey ((fullF a c).getD a) = okey a := by
  cases a <;> cases c <;> simp only [fullF, Option.getD_none] <;> try rfl
  split_ifs <;> rfl

/-! ## FL4's word-level effects -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a copy keeps `FinM`**, for a cap of the source's
shape and object. -/
theorem insert_finM (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hF : FinM (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC) (hkey : okey c = okey srcC)
    (hzb : isZb srcC = false) :
    cdt.insert st s c src dest ⦃ s' => ∀ b, (insG G src dest b).chains.flatten.Nodup →
      FinM (L.mem s') (insG G src dest b) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW b hnd
  have hcap : ∀ a, IsSlot th a → capV (L.mem s') a =
      if a = dest then c else if a = src then (fullF srcC c).getD srcC else capV (L.mem s) a := by
    intro a ha
    have := hW.capAt' ha he hes hsrcC
    rw [capAt_capV] at this
    by_cases h1 : a = dest
    · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
    · by_cases h2 : a = src
      · subst h2; simp only [h1, ↓reduceIte] at this ⊢; simpa using this
      · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
  refine hF.insert hsrc hdest b hnd ?_ ?_ ?_ ?_
  · rw [hcap dest hd, if_pos rfl, hcv]; exact CapSim.of_shape hsh hkey
  · rw [hcap dest hd, if_pos rfl, isZb_of_shape hsh]; exact hzb
  · rw [hcap src hs, if_neg hne, if_pos rfl, hcv]
    exact CapSim.of_shape (fullF_shape srcC c).1 (okey_fullF srcC c)
  · intro z hz hzs
    have hzd : z ≠ dest := fun e => hdest (e ▸ hz)
    rw [hcap z (hslot z hz), if_neg hzd, if_neg hzs]

/-- The caps after `cdt::insert` of a control cap's child: the new cap at
`dest`, every other slot's as it was. -/
theorem insert_ctl_caps (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hctl : CtlPair srcC c) :
    cdt.insert st s c src dest ⦃ s' => ∀ a, IsSlot th a →
      capV (L.mem s') a = if a = dest then c else capV (L.mem s) a ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hfull := hctl.facts.2.2.2.2.2.2.2.2.2.1
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW a ha
  have := hW.capAt' ha he hes hsrcC
  rw [capAt_capV] at this
  by_cases h1 : a = dest
  · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
  · by_cases h2 : a = src
    · subst h2; simp only [h1, ↓reduceIte, hfull, Option.getD_none] at this ⊢
      rw [hcv]; simpa using this
    · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this

/-- **`cdt::insert` of a control cap's child keeps `FinM`**, for a cap
overlapping no cap of the MDB. -/
theorem insert_ctl_finM (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hF : FinM (L.mem s) G) {src dest : U64} (hsrc : src ∈ G.chains.flatten)
    (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten) {srcC : capability.Cap}
    (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hctl : CtlPair srcC c)
    (hov : ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap c) (absCap (capV (L.mem s) y)))
    (hfr : ∀ y ∈ G.chains.flatten, srB c (capV (L.mem s) y) = false) :
    cdt.insert st s c src dest ⦃ s' => ∀ b, (insG G src dest b).chains.flatten.Nodup →
      FinM (L.mem s') (insG G src dest b) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hcv := capV_of_capAt hsrcC
  have hfull := hctl.facts.2.2.2.2.2.2.2.2.2.1
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  apply WP.spec_mono (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)
  intro s' hW b hnd
  have hcap : ∀ a, IsSlot th a → capV (L.mem s') a = if a = dest then c else capV (L.mem s) a := by
    intro a ha
    have := hW.capAt' ha he hes hsrcC
    rw [capAt_capV] at this
    by_cases h1 : a = dest
    · subst h1; simp only [↓reduceIte] at this ⊢; simpa using this
    · by_cases h2 : a = src
      · subst h2; simp only [h1, ↓reduceIte, hfull, Option.getD_none] at this ⊢
        rw [hcv]; simpa using this
      · simp only [h1, h2, ↓reduceIte] at this ⊢; rw [capAt_capV] at this; simpa using this
  have hne' : ∀ z ∈ G.chains.flatten, z ≠ dest := fun z hz e => hdest (e ▸ hz)
  refine hF.fresh_ins hsrc hdest b hnd (fun z hz => by rw [hcap z (hslot z hz), if_neg (hne' z hz)])
    (fun w hw => ?_)
  rw [hcap dest hd, if_pos rfl, hcap w (hslot w hw), if_neg (hne' w hw)]
  refine ⟨hov w hw, fun _ => hfr w hw, fun hf => ?_⟩
  obtain ⟨p, sz, v, dv, m, ep, a, va, e⟩ : ∃ p sz v dv m ep a va, capV (L.mem s) w = .Frame p sz v dv m ep a va := by
    cases h : capV (L.mem s) w <;> rw [h] at hf <;> simp [isFrame] at hf
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  rw [e]
  rcases hctl.cases with ⟨-, i, rfl⟩ | ⟨-, f, l, vcpu, rfl⟩
  · rw [srB_irqH]; simp
  · rw [srB_ioP]; simp [shape]

/-- **`cdt::move_cap` keeps `FinM`**, for a cap of the old one's shape and
object. -/
theorem move_finM (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hF : FinM (L.mem s) G) {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdestm : dest ∉ G.chains.flatten) {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hsh : shape c = shape srcC) (hkey : okey c = okey srcC) :
    cdt.move_cap st s c src dest ⦃ s' => (renG G (Equiv.swap src dest)).chains.flatten.Nodup →
      FinM (L.mem s') (renG G (Equiv.swap src dest)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrcm
  have hne : src ≠ dest := fun e => hdestm (e ▸ hsrcm)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrcm h0
      refine Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrcm with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  apply WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx)
  intro s' hW hnd
  have hcv := capV_of_capAt hsrcC
  have hdne : ∀ a, a ∈ G.chains.flatten → a ≠ dest := fun a h e => hdestm (e ▸ h)
  refine hF.rename _ hnd (fun a ha => ?_)
  by_cases has : a = src
  · rw [has, Equiv.swap_apply_left, capV_of_capAt (c := c) (by rw [hW.capAt' hd he hne]; simp), hcv]
    exact CapSim.of_shape hsh hkey
  · rw [Equiv.swap_apply_of_ne_of_ne has (hdne a ha)]
    have := hW.capAt' (hslot a ha) he hne
    rw [if_neg (hdne a ha), if_neg has, capAt_capV, capAt_capV] at this
    simp at this; rw [this]; exact CapSim.refl _

/-- **`cdt::swap` keeps `FinM`**, for caps of the old ones' shapes and
objects. -/
theorem swap_finM (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    (hF : FinM (L.mem s) G) {s1 s2 : U64} (hm1 : s1 ∈ G.chains.flatten) (hm2 : s2 ∈ G.chains.flatten)
    (hne : s1 ≠ s2) (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2)
    (hsh1 : shape c1 = shape (capV (L.mem s) s1)) (hk1 : okey c1 = okey (capV (L.mem s) s1))
    (hsh2 : shape c2 = shape (capV (L.mem s) s2)) (hk2 : okey c2 = okey (capV (L.mem s) s2)) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => (renG G (Equiv.swap s1 s2)).chains.flatten.Nodup →
      FinM (L.mem s') (renG G (Equiv.swap s1 s2)) ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNx : ∀ a, a ∈ G.chains.flatten → nextOf (L.mem s) a = 0#u64 ∨ IsSlot th (nextOf (L.mem s) a) := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have hPx : ∀ a, a ∈ G.chains.flatten → prevOf (L.mem s) a = 0#u64 ∨ IsSlot th (prevOf (L.mem s) a) := by
    intro a ha; by_cases h : prevOf (L.mem s) a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link ha h).1)
  apply WP.spec_mono (swap_fields hP s c1 c2 _ _ (hslot _ hm1) (hslot _ hm2) hne he1 he2 (hPx _ hm1) (hNx _ hm1)
    (hPx _ hm2) (hNx _ hm2))
  intro s' hW hnd
  refine hF.rename _ hnd (fun a ha => ?_)
  by_cases e1 : a = s1
  · have h := (hW _ (hslot _ hm2)).1
    rw [capAt_capV, if_pos rfl] at h
    rw [e1, Equiv.swap_apply_left]; simp at h; rw [h]; exact CapSim.of_shape hsh1 hk1
  · by_cases e2 : a = s2
    · have h := (hW _ (hslot _ hm1)).1
      rw [capAt_capV, if_neg hne, if_pos rfl] at h
      rw [e2, Equiv.swap_apply_right]; simp at h; rw [h]; exact CapSim.of_shape hsh2 hk2
    · have h := (hW _ (hslot _ ha)).1
      rw [capAt_capV, if_neg e2, if_neg e1, capAt_capV] at h
      rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; simp at h; rw [h]; exact CapSim.refl _

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` keeps `FinM`.** -/
theorem empty_finM {th : TypedHeap} (hP : Placed th) (s : S) (a : A) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hF : FinM (L.mem s) G) {x : U64} (hxm : x ∈ G.chains.flatten)
    {c : capability.Cap} (hc : capAt (L.mem s) x = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a x .Null ⦃ r => (remG G x).chains.flatten.Nodup → FinM (L.mem r.1) (remG G x) ⦄ := by
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hx := hslot x hxm
  have hnx : nextOf (L.mem s) x = 0#u64 ∨ (IsSlot th (nextOf (L.mem s) x) ∧ nextOf (L.mem s) x ≠ x) := by
    rcases hM.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s) x = 0#u64 ∨ (IsSlot th (prevOf (L.mem s) x) ∧ prevOf (L.mem s) x ≠ x) := by
    by_cases h0 : prevOf (L.mem s) x = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hx.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM.prev_ne_next hP hxm
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, -⟩ hnd
  refine hF.remove hM x hnd (fun y hy hyx => ?_)
  have := hW.capAt' (hslot y hy); rw [if_neg hyx, capAt_capV, capAt_capV] at this; simpa using this

end


/-! ## With the refinement -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::insert` of a derived cap refines `cap_insert` and keeps `MdbInv`
and `FinInv`**, for a cap naming the source's object. -/
theorem insert_full_fin (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hsh : shape c = shape srcC) (hbd : badgeF c = badgeF srcC ∨ badgeF srcC = 0#u64)
    (hut : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs))) (hzb : isZb srcC = false)
    (hkey : okey c = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 c) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        ((isUt srcC = true → c = srcC) → MdbStep (L.mem s) G (L.mem s') G') ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hcv0 := capV_of_capAt hsrcC
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hself : srB srcC srcC = true := by
    have := hI.self _ hsrcm (by rw [hcv0]; exact hzb); unfold srM at this; rw [hcv0] at this; exact this
  have hk := sameBadgeKind_of_shape hsh
  obtain ⟨hwf, rfl⟩ := hca
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) =
      isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) := by
    rw [hC.orig _ hAs]; exact sbp_eq srcC c _ hsh hself hes hk
  have hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
    intro hn
    have h0 : isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) = false := by
      rw [← hb]; simpa using hn
    rw [← hcv0] at h0 hsh hbd hzb
    exact MdbInv.sib (th := th) hI hsrcm hzb hsh hbd h0
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (insert_refines' th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c _ ⟨hwf, rfl⟩ hcv he hcnn hk)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (insert_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb)
  obtain ⟨s3, h3, hfin⟩ := spec_exists
    (insert_finM hP s G hM hFI.fm hsrcm hAd.isSlot hdestm hsrcC c he hsh hkey hzb)
  obtain ⟨s4, h4, hstep⟩ := spec_exists
    (insert_mstep hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hsh hbd hut hzb hkey hv)
  rw [h1] at h2 h3 h4
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  subst e e3 e4
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hins, hR', hV', hM', hC', hG'⟩ := hpost hsib
  refine ⟨σ', G', hins, hR', hV', hM', hC', ?_, ⟨hFI.kt.sub (ksub_of_eq (capInsert_nks _ _ _) hins), ?_⟩, ?_⟩
  · rw [hG', hb]; exact hinv
  · have hnd := hM'.tree.nodup
    rw [hG', hb] at hnd ⊢; exact hfin _ hnd
  · rw [hG', hb]; exact hstep

/-- **`cdt::insert` of a control cap's child refines `cap_insert` and keeps
`MdbInv` and `FinInv`**, the new cap overlapping no cap of the MDB. -/
theorem insert_ctl_full_fin (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (hwf : CapWf c) (hcv : CapValid th c) (he : EncWf c) (hctl : CtlPair srcC c)
    (hfr : ∀ y ∈ G.chains.flatten, srB c (capV (L.mem s) y) = false)
    (hov : ∀ y ∈ G.chains.flatten, ¬ Ovl (absCap c) (absCap (capV (L.mem s) y))) :
    cdt.insert st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capInsert (Z := Unit) (absCap c) (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        (∀ a, IsSlot th a → capV (L.mem s') a = if a = cslotAddr (pd.bv, idxd) then c else capV (L.mem s) a) ∧
        (∃ b, G' = insG G (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) b) ∧
        MdbStep (L.mem s) G (L.mem s') G' ⦄ := by
  obtain ⟨-, -, -, -, -, hzb, hcnn, hsnn, -, -, hk⟩ := hctl.facts
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hb : decide (Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC)))) =
      isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) := by
    rw [hC.orig _ hAs]; exact hctl.sbp _
  have hsib : ¬ Fl4Spec.shouldBeParentOf (absCap srcC) (σ.isOriginalCap (ps.bv, idxs)) (absCap c)
      (decide (Fl4Spec.isCapRevocable (absCap c) (absCap srcC))) →
      ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (ps.bv, idxs)) := by
    intro hn y hy
    have h0 : isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC) = false := by
      rw [← hb]; simpa using hn
    rw [hctl.pf_eq] at h0
    obtain ⟨z, hz⟩ := desc_tail_child hy
    rw [hI.orig z _ hz] at h0; cases h0
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (insert_refines' th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c _ ⟨hwf, rfl⟩ hcv he hcnn hk)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (insert_ctl_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hctl hfr)
  obtain ⟨s3, h3, hfin⟩ := spec_exists
    (insert_ctl_finM hP s G hM hFI.fm hsrcm hAd.isSlot hdestm hsrcC c he hctl hov hfr)
  obtain ⟨s4, h4, hcaps⟩ := spec_exists
    (insert_ctl_caps hP s G hM hsrcm hAd.isSlot hdestm hsrcC c he hctl)
  obtain ⟨s5, h5, hstep⟩ := spec_exists
    (insert_ctl_mstep hP s G hM hsrcm hAd.isSlot hdestm hsrcC c he hctl
      (isPF (revOf (L.mem s) (cslotAddr (ps.bv, idxs))) srcC c (revF c srcC)))
  rw [h1] at h2 h3 h4 h5
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  have e5 := eq_of_ok_eq h5
  subst e e3 e4 e5
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hins, hR', hV', hM', hC', hG'⟩ := hpost hsib
  refine ⟨σ', G', hins, hR', hV', hM', hC', ?_, ⟨hFI.kt.sub (ksub_of_eq (capInsert_nks _ _ _) hins), ?_⟩, hcaps,
    ⟨_, hG'⟩, by rw [hG', hb]; exact hstep⟩
  · rw [hG', hb]; exact hinv
  · have hnd := hM'.tree.nodup
    rw [hG', hb] at hnd ⊢; exact hfin _ hnd

/-- **`cdt::move_cap` refines `cap_move` and keeps `MdbInv` and `FinInv`**,
for a new cap of the old one's shape, badge and object. -/
theorem move_full_fin (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {ps pd : U64} {rs rd : Nat} (hps : th ps = some (.cnode rs)) (hpd : th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok srcC)
    (hsnn : srcC ≠ .Null)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    (c : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel c a) (hcv : CapValid th c) (he : EncWf c)
    (hcnn : c ≠ .Null) (hsh : shape c = shape srcC) (hbd : badgeF c = badgeF srcC)
    (hkey : okey c = okey srcC)
    (hv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 srcC → Vs.VCapOK P L4 L3 L2 L1 c) :
    cdt.move_cap st s c (cslotAddr (ps.bv, idxs)) (cslotAddr (pd.bv, idxd)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capMove (Z := Unit) a (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        ((isUt srcC = true → c = srcC) → MdbStep (L.mem s) G (L.mem s') G') ⦄ := by
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsrcm := (hM.members _).2 ⟨hAs.isSlot, srcC, hsrcC, hsnn⟩
  have hdestm : cslotAddr (pd.bv, idxd) ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [hdst] at h0
    exact hn (eq_of_ok_eq h0).symm
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (move_refines th s σ G hR hV hP hM hC hps hpd hls hld hsrcC hsnn hdst c a hca hcv he hcnn)
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (move_mdbinv hP s G hM hI hsrcm hAd.isSlot hdestm hsrcC c he hcnn hsh hbd)
  obtain ⟨s3, h3, hfin⟩ := spec_exists
    (move_finM hP s G hM hFI.fm hsrcm hAd.isSlot hdestm hsrcC c he hsh hkey)
  obtain ⟨s4, h4, hstep⟩ := spec_exists
    (move_mstep hP s G hM hsrcm hAd.isSlot hdestm hsrcC c he hsh hkey hv)
  rw [h1] at h2 h3 h4
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  subst e e3 e4
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hmv, hR', hV', hM', hC', hG'⟩ := hpost
  refine ⟨σ', G', hmv, hR', hV', hM', hC', by rw [hG']; exact hinv,
    ⟨hFI.kt.sub (ksub_of_eq (capMove_nks _ _ _) hmv), ?_⟩, by rw [hG']; exact hstep⟩
  have hnd := hM'.tree.nodup
  rw [hG'] at hnd ⊢; exact hfin hnd

/-- **`cdt::swap` refines `cap_swap` and keeps `MdbInv` and `FinInv`**, for
new caps of the old ones' shapes, badges and objects. -/
theorem swap_full_fin (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {p1 p2 : U64} {r1 r2 : Nat} (hp1 : th p1 = some (.cnode r1)) (hp2 : th p2 = some (.cnode r2))
    {i1 i2 : List Bool} (hl1 : i1.length = r1) (hl2 : i2.length = r2)
    (hne : (p1.bv, i1) ≠ (p2.bv, i2))
    {o1 o2 : capability.Cap} (ho1 : capAt (L.mem s) (cslotAddr (p1.bv, i1)) = ok o1) (hon1 : o1 ≠ .Null)
    (ho2 : capAt (L.mem s) (cslotAddr (p2.bv, i2)) = ok o2) (hon2 : o2 ≠ .Null)
    (c1 : capability.Cap) (a1 : Fl4Spec.Cap) (hca1 : CapRel c1 a1) (hcv1 : CapValid th c1) (he1 : EncWf c1)
    (hcn1 : c1 ≠ .Null) (hsh1 : shape c1 = shape o1) (hbd1 : badgeF c1 = badgeF o1) (hk1 : okey c1 = okey o1)
    (c2 : capability.Cap) (a2 : Fl4Spec.Cap) (hca2 : CapRel c2 a2) (hcv2 : CapValid th c2) (he2 : EncWf c2)
    (hcn2 : c2 ≠ .Null) (hsh2 : shape c2 = shape o2) (hbd2 : badgeF c2 = badgeF o2) (hk2 : okey c2 = okey o2)
    (hv1 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 o1 → Vs.VCapOK P L4 L3 L2 L1 c1)
    (hv2 : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 o2 → Vs.VCapOK P L4 L3 L2 L1 c2) :
    cdt.swap st s c1 (cslotAddr (p1.bv, i1)) c2 (cslotAddr (p2.bv, i2)) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) a1 (p1.bv, i1) a2 (p2.bv, i2) σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧ FinInv th (L.mem s') σ' G' ∧
        ((isUt o1 = true → c1 = o1) → (isUt o2 = true → c2 = o2) → MdbStep (L.mem s) G (L.mem s') G') ⦄ := by
  have hA1 : AbsSlot th (p1.bv, i1) := ⟨p1, rfl, Or.inl (by simpa [hl1] using hp1)⟩
  have hA2 : AbsSlot th (p2.bv, i2) := ⟨p2, rfl, Or.inl (by simpa [hl2] using hp2)⟩
  have hAne : cslotAddr (p1.bv, i1) ≠ cslotAddr (p2.bv, i2) := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm1 := (hM.members _).2 ⟨hA1.isSlot, o1, ho1, hon1⟩
  have hm2 := (hM.members _).2 ⟨hA2.isSlot, o2, ho2, hon2⟩
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (swap_refines th s σ G hR hV hP hM hC hp1 hp2 hl1 hl2 hne ho1 hon1 ho2 hon2 c1 a1 hca1 hcv1 he1 hcn1
      c2 a2 hca2 hcv2 he2 hcn2)
  rw [← capV_of_capAt ho1] at hsh1 hbd1 hk1 hv1
  rw [← capV_of_capAt ho2] at hsh2 hbd2 hk2 hv2
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (swap_mdbinv hP s G hM hI hm1 hm2 hAne c1 c2 he1 he2 hcn1 hcn2 hsh1 hbd1 hsh2 hbd2)
  obtain ⟨s3, h3, hfin⟩ := spec_exists
    (swap_finM hP s G hM hFI.fm hm1 hm2 hAne c1 c2 he1 he2 hsh1 hk1 hsh2 hk2)
  obtain ⟨s4, h4, hstep⟩ := spec_exists
    (swap_mstep hP s G hM hm1 hm2 hAne c1 c2 he1 he2 hsh1 hk1 hsh2 hk2 hv1 hv2)
  rw [h1] at h2 h3 h4
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  subst e e3 e4
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hsw, hG', hR', hV', hM', hC'⟩ := hpost
  refine ⟨σ', G', hsw, hR', hV', hM', hC', by rw [hG']; exact hinv,
    ⟨hFI.kt.sub (ksub_of_eq (capSwap_nks _ _ _ _) hsw), ?_⟩, fun u1 u2 => by
      rw [hG']; rw [capV_of_capAt ho1, capV_of_capAt ho2] at hstep; exact hstep u1 u2⟩
  have hnd := hM'.tree.nodup
  rw [hG'] at hnd ⊢; exact hfin hnd

end

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

/-- **`cdt::empty_slot` refines `empty_slot` and keeps `MdbInv` and `FinInv`.** -/
theorem empty_full_fin (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a (cslotAddr (px.bv, idx)) .Null ⦃ r => r.2 = a ∧
      ∃ σ' G', Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ')}, False) ∧
        StateRel th (L.mem r.1) σ' ∧ SlotsValid th (L.mem r.1) ∧ MdbLinks th (L.mem r.1) G' ∧
        CdtRel th (L.mem r.1) σ' G' ∧ MdbInv (L.mem r.1) G' ∧ FinInv th (L.mem r.1) σ' G' ∧
        MdbStep (L.mem s) G (L.mem r.1) G' ⦄ := by
  have hAx : AbsSlot th (px.bv, idx) := ⟨px, rfl, Or.inl (by simpa [hl] using hpx)⟩
  have hxm := (hM.members _).2 ⟨hAx.isSlot, c, hc, hcn⟩
  obtain ⟨r1, h1, hpost⟩ := spec_exists (empty_slot_refines (ar := ar) th s a σ G hR hV hP hM hC hpx hl hc hcn)
  obtain ⟨r2, h2, hinv⟩ := spec_exists (empty_slot_mdbinv (ar := ar) hP s a G hM hI hxm hc hcn)
  obtain ⟨r3, h3, hfin⟩ := spec_exists (empty_finM (ar := ar) hP s a G hM hFI.fm hxm hc hcn)
  obtain ⟨r4, h4, hstep⟩ := spec_exists (empty_mstep (ar := ar) hP s a G hM hxm hc hcn)
  rw [h1] at h2 h3 h4
  have e := eq_of_ok_eq h2
  have e3 := eq_of_ok_eq h3
  have e4 := eq_of_ok_eq h4
  subst e e3 e4
  rw [h1, WP.spec_ok]
  obtain ⟨hra, σ', G', hes, hR', hV', hM', hC', hG'⟩ := hpost
  refine ⟨hra, σ', G', hes, hR', hV', hM', hC', by rw [hG']; exact hinv,
    ⟨hFI.kt.sub (ksub_of_eq (emptySlot_nks _ _) hes), ?_⟩, by rw [hG']; exact hstep⟩
  have hnd := hM'.tree.nodup
  rw [hG'] at hnd ⊢; exact hfin hnd

end

end

end Fl4Proofs.P3
