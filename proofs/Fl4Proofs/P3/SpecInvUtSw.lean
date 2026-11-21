/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **`cap_swap` of the
slots' own caps keeps `UtInv'`** (spec side only): the view after the swap is
the old view renamed by the transposition of the two slots (caps, CDT links in
both directions, original flags), and `UtInv'` is invariant under renaming
(`utInv'_rename`). Covers `cap_swap_for_delete` (rec_del's zombie reduction).
-/
import Fl4Proofs.P3.SpecInvUtIns
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- The transposition of two slots. -/
def sw (a b x : CslotPtr) : CslotPtr := if x = a then b else if x = b then a else x

theorem sw_sw (a b x : CslotPtr) : sw a b (sw a b x) = x := by
  unfold sw
  by_cases h1 : x = a
  · subst h1; by_cases h2 : b = x <;> simp [h2]
  · by_cases h2 : x = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem sw_inj {a b x y : CslotPtr} (h : sw a b x = sw a b y) : x = y := by
  rw [← sw_sw a b x, h, sw_sw]

/-- The view renamed by `π` (an involution). -/
def vRen (π : CslotPtr → CslotPtr) (w : UView) : UView :=
  (w.1, fun x => w.2.1 (π x), fun x => (w.2.2.1 (π x)).map π, fun x => w.2.2.2 (π x))

theorem ren_po {π : CslotPtr → CslotPtr} (hπ : ∀ x, π (π x) = x) {t : Cdt} {a b : CslotPtr} :
    parentOf (fun x => (t (π x)).map π) a b ↔ parentOf t (π a) (π b) := by
  show (t (π b)).map π = some a ↔ t (π b) = some (π a)
  constructor
  · intro h
    cases e : t (π b) with
    | none => rw [e] at h; cases h
    | some p => rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; rw [← h, hπ]
  · intro h; rw [h]; simp only [Option.map_some, hπ]

theorem tg_map {r p : CslotPtr → CslotPtr → Prop} (f : CslotPtr → CslotPtr) (h : ∀ a b, r a b → p (f a) (f b))
    {x y : CslotPtr} (hxy : Relation.TransGen r x y) : Relation.TransGen p (f x) (f y) := by
  induction hxy with
  | single hab => exact Relation.TransGen.single (h _ _ hab)
  | tail _ hbc ih => exact Relation.TransGen.tail ih (h _ _ hbc)

theorem ren_tg {π : CslotPtr → CslotPtr} (hπ : ∀ x, π (π x) = x) {t : Cdt} {x y : CslotPtr} :
    Relation.TransGen (parentOf (fun x => (t (π x)).map π)) x y ↔ Relation.TransGen (parentOf t) (π x) (π y) := by
  constructor
  · intro h
    exact tg_map (r := parentOf (fun x => (t (π x)).map π)) (p := parentOf t) π
      (fun a b hab => (ren_po hπ (t := t)).1 hab) h
  · intro h
    have := tg_map (r := parentOf t) (p := parentOf (fun x => (t (π x)).map π)) π
      (fun a b hab => (ren_po hπ (t := t)).2 (by rw [hπ, hπ]; exact hab)) h
    rwa [hπ, hπ] at this

/-- **`UtInv'` is invariant under renaming the slots.** -/
theorem utInv'_rename {π : CslotPtr → CslotPtr} (hπ : ∀ x, π (π x) = x) {w : UView} (hI : UtInv'V w) :
    UtInv'V (vRen π w) := by
  obtain ⟨⟨hF, hW, hD, hDe, hOr⟩, hO, hA⟩ := hI
  have hinj : ∀ x y, π x = π y → x = y := fun x y h => by rw [← hπ x, h, hπ]
  refine ⟨⟨fun sl d b n f hc => hF (π sl) d b n f hc, fun sl d b n f hc => hW (π sl) d b n f hc,
    fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 => hD (π s1) (π s2) d1 b1 n1 f1 d2 b2 n2 f2
      (fun e => hne (hinj _ _ e)) hc1 hc2, fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hne hc1 hc2 hov => ?_,
    fun sl d b n f hc => hOr (π sl) d b n f hc⟩, fun c p h => ?_, fun x hx => hA (π x) ((ren_tg hπ).1 hx)⟩
  · rcases hDe (π s1) (π s2) d1 b1 n1 f1 d2 b2 n2 f2 (fun e => hne (hinj _ _ e)) hc1 hc2 hov with ⟨hd, hr⟩ | ⟨hd, hr⟩
    · exact Or.inl ⟨(ren_tg hπ).2 hd, hr⟩
    · exact Or.inr ⟨(ren_tg hπ).2 hd, hr⟩
  · have h' : (w.2.2.1 (π c)).map π = some p := h
    have : w.2.2.1 (π c) = some (π p) := (ren_po hπ (a := p) (b := c)).1 h'
    obtain ⟨cap, hcap, hcn⟩ := hO _ _ this
    exact ⟨cap, hcap, hcn⟩

/-- **`cap_swap` of the slots' own caps keeps `UtInv'`.** -/
theorem hv_capSwap_same {s1 s2 : CslotPtr} (hne : s1 ≠ s2) (c1 c2 : Cap) :
    HV (fun w => UtInv'V w ∧ w.2.1 s1 = some c1 ∧ w.2.1 s2 = some c2) UtInv'V (capSwap (Z := Unit) c1 s1 c2 s2) := by
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
      (vCdt (fun x => (w.2.2.1 (sw s1 s2 x)).map (sw s1 s2)) (vCap s2 c1 (vCap s1 c2 w)))) = vRen (sw s1 s2) w := by
    unfold vOrig vCdt vCap vRen
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · funext x
      show Function.update (Function.update w.2.1 s1 (some c2)) s2 (some c1) x = w.2.1 (sw s1 s2 x)
      by_cases e2 : x = s2
      · subst e2; rw [Function.update_self, sw2, h1]
      · rw [Function.update_of_ne e2]
        by_cases e1 : x = s1
        · subst e1; rw [Function.update_self, sw1, h2]
        · rw [Function.update_of_ne e1, swx x e1 e2]
    · funext x
      show Function.update (Function.update w.2.2.2 s1 (w.2.2.2 s2)) s2 (w.2.2.2 s1) x = w.2.2.2 (sw s1 s2 x)
      by_cases e2 : x = s2
      · subst e2; rw [Function.update_self, sw2]
      · rw [Function.update_of_ne e2]
        by_cases e1 : x = s1
        · subst e1; rw [Function.update_self, sw1]
        · rw [Function.update_of_ne e1, swx x e1 e2]
  rw [key]
  exact utInv'_rename (sw_sw s1 s2) hI

/-- **`cap_swap_for_delete` keeps `UtInv'`.** -/
theorem hv_capSwapForDelete (s1 s2 : CslotPtr) : HV UtInv'V UtInv'V (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  unfold NonDet.when
  split
  · rename_i hne
    refine hv_getCap_bind fun w c1 hw h1 => ?_
    refine hv_getCap_bind fun w' c2 hw' h2 => ?_
    subst w'
    exact fun σ hσ y hy => hv_capSwap_same hne c1 c2 σ ⟨hσ ▸ hw, hσ ▸ h1, hσ ▸ h2⟩ y hy
  · exact hv_uk fun _ => ik_pure' _

theorem ik_capSwapForDelete (s1 s2 : CslotPtr) : IK UtInv' (capSwapForDelete (Z := Unit) s1 s2) :=
  hv_capSwapForDelete s1 s2

end

end Fl4Proofs.P3.SInvU
