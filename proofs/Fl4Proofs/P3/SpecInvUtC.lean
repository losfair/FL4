/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **the CDT facts the
untyped invariant needs, and the CDT writers** (spec side only; imports only
Fl4Spec via SpecInvUtR).

* `CdtOK` (l4v `mdb_cte_at`, the parent half): every CDT parent slot holds a
  non-null cap. So an empty (null) slot, and a slot of no object, has no CDT
  child: a cap written there (`create_cap`, `cap_insert`, `cap_move`) is a
  CDT leaf, and no chain between untyped slots passes through it.
* `CdtAcyc` (l4v `no_mloop`): the CDT has no cycle (`empty_slot` reparents the
  children of the emptied slot to its parent; with a self-parent the emptied
  slot would keep a child).
* `UtInv' = UtInv ∧ CdtOK ∧ CdtAcyc`, on the view `uV`, so every function of
  the generated frames SpecInvUtF1..F4 keeps it (`ik_utInv'_of_uk`); boot.
* `HV P Q m`: Hoare triple over the view (`P (uV σ) → Q (uV y.2)`), with the
  view writers `setCdt` / `setOriginal` / `setCap` (exact: the written slot
  holds the new cap) as transformers `vCdt` / `vOrig` / `vCap`.
* `CapShrinkD`: `CapShrink` with the CDT allowed to change as long as every
  descendant pair of untyped slots of the new view stays a descendant pair.
* `ik_emptySlot'`: `empty_slot` keeps `UtInv'` (chains through the emptied
  slot get shorter: `es_tg_new` / `es_tg_old`).
-/
import Fl4Proofs.P3.SpecInvUtR
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- `CdtOK` on the view (l4v `mdb_cte_at`, parent half). -/
def CdtOKV (w : UView) : Prop := ∀ c p, w.2.2.1 c = some p → ∃ cap, w.2.1 p = some cap ∧ cap ≠ .nullCap

/-- `CdtAcyc` on the view (l4v `no_mloop`). -/
def CdtAcycV (w : UView) : Prop := ∀ x, ¬ Relation.TransGen (parentOf w.2.2.1) x x

/-- The untyped invariant with its CDT facts. -/
def UtInv'V (w : UView) : Prop := UtInvV w ∧ CdtOKV w ∧ CdtAcycV w

/-- **CdtOK [J]** (l4v `mdb_cte_at`). -/
abbrev CdtOK (σ : State Unit) : Prop := CdtOKV (uV σ)
/-- **CdtAcyc [J]** (l4v `no_mloop`). -/
abbrev CdtAcyc (σ : State Unit) : Prop := CdtAcycV (uV σ)
/-- **The carried untyped invariant** `UtInv ∧ CdtOK ∧ CdtAcyc`. -/
abbrev UtInv' (σ : State Unit) : Prop := UtInv'V (uV σ)

theorem po_iff {t : Cdt} {p c : CslotPtr} : parentOf t p c ↔ t c = some p := Iff.rfl

theorem tg_last {t : Cdt} {x y : CslotPtr} (h : Relation.TransGen (parentOf t) x y) : ∃ a, t y = some a := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ h _ => exact ⟨_, h⟩

theorem tg_first {t : Cdt} {x y : CslotPtr} (h : Relation.TransGen (parentOf t) x y) : ∃ c, t c = some x := by
  obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
  exact ⟨c, hc⟩

theorem ik_utInv'_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK UtInv' m :=
  ik_of_uk (fun _ _ e hI => by show UtInv'V _; rw [e]; exact hI) h

theorem ike_utInv'_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE UtInv' m :=
  ik_utInv'_of_uk h

/-- **(d) boot.** -/
theorem boot_utInv' : UtInv' (initASt (Z := Unit)) := by
  refine ⟨boot_utInv, fun c p h => ?_, fun x hx => ?_⟩
  · exact absurd h (by simp [uV, initASt, initCdt])
  · obtain ⟨c, hc⟩ := tg_first hx
    exact absurd hc (by simp [uV, initASt, initCdt])

theorem UtInv'.ut {σ : State Unit} (h : UtInv' σ) : UtInv σ := h.1

/-! ## Shrinking with a CDT change -/

structure CapShrinkD (w' w : UView) : Prop where
  keys : ∀ p, w'.1 p = true → w.1 p = true ∨
    ∀ sl d b n f, w.2.1 sl = some (.untypedCap d b n f) → p.toNat ∉ utFr b n f
  caps : ∀ sl d b n f', w'.2.1 sl = some (.untypedCap d b n f') →
    ∃ f, w.2.1 sl = some (.untypedCap d b n f) ∧ f ≤ f' ∧ f' ≤ 2 ^ n
  desc : ∀ s1 s2 d1 b1 n1 f1 d2 b2 n2 f2, w'.2.1 s1 = some (.untypedCap d1 b1 n1 f1) →
    w'.2.1 s2 = some (.untypedCap d2 b2 n2 f2) → s2 ∈ descendantsOf s1 w.2.2.1 → s2 ∈ descendantsOf s1 w'.2.2.1
  orig : ∀ sl d b n f, w'.2.1 sl = some (.untypedCap d b n f) → w.2.2.2 sl = true → w'.2.2.2 sl = true

theorem utInvV_shrinkD {w' w : UView} (h : CapShrinkD w' w) (hI : UtInvV w) : UtInvV w' := by
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
    rcases hDe s1 s2 d1 b1 n1 g1 d2 b2 n2 g2 hne hg1 hg2 hov with ⟨hd, hr⟩ | ⟨hd, hr⟩
    · exact Or.inl ⟨h.desc s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 hc1 hc2 hd, fun k hk hk' => hr k hk (utFr_mono hle1 hk')⟩
    · exact Or.inr ⟨h.desc s2 s1 d2 b2 n2 f2 d1 b1 n1 f1 hc2 hc1 hd, fun k hk hk' => hr k hk (utFr_mono hle2 hk')⟩
  · intro sl d b n f' hc
    obtain ⟨f, hc0, -⟩ := h.caps sl d b n f' hc
    exact h.orig sl d b n f' hc (hO sl d b n f hc0)

theorem same_capV {w : UView} (hW : UtWfV w) {sl : CslotPtr} {d : Bool} {b : ObjRef} {n f : Nat}
    (hc : w.2.1 sl = some (.untypedCap d b n f)) :
    ∃ f0, w.2.1 sl = some (.untypedCap d b n f0) ∧ f0 ≤ f ∧ f ≤ 2 ^ n :=
  ⟨f, hc, le_refl _, (hW sl d b n f hc).2.2⟩

/-! ## The view Hoare triple -/

/-- Every outcome of `m` from a state whose view satisfies `P` has a view satisfying `Q`. -/
def HV (P Q : UView → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P (uV σ) → ∀ y, y ∈ (m σ).1 → Q (uV y.2)

def vCdt (t : Cdt) (w : UView) : UView := (w.1, w.2.1, t, w.2.2.2)
def vOrig (sl : CslotPtr) (v : Bool) (w : UView) : UView := (w.1, w.2.1, w.2.2.1, Function.update w.2.2.2 sl v)
def vCap (sl : CslotPtr) (c : Cap) (w : UView) : UView := (w.1, Function.update w.2.1 sl (some c), w.2.2.1, w.2.2.2)

section HVc
variable {P Q R : UView → Prop}

theorem hv_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : HV P R m)
    (hg : ∀ a, HV R Q (g a)) : HV P Q (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm σ hσ y hy) x hx

theorem hv_mono {α : Type} {m : NonDet (State Unit) α} {Q' : UView → Prop} (h : HV P Q m)
    (hq : ∀ w, Q w → Q' w) : HV P Q' m :=
  fun σ hσ y hy => hq _ (h σ hσ y hy)

theorem hv_pin {α : Type} {m : NonDet (State Unit) α} (h : ∀ w, P w → HV (· = w) Q m) : HV P Q m :=
  fun σ hσ y hy => h _ hσ σ rfl y hy

theorem hv_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : HV P P m :=
  fun σ hσ y hy => by rw [h (uV σ) σ rfl y hy]; exact hσ

theorem hv_ik {α : Type} {m : NonDet (State Unit) α} {I : UView → Prop} (h : IK (fun σ => I (uV σ)) m) :
    HV I I m := h

theorem hv_ret {α : Type} {w : UView} (a : α) (hw : Q w) : HV (· = w) Q (pure a : NonDet (State Unit) α) := by
  intro σ hσ y hy
  rw [Set.mem_singleton_iff.1 hy]; rw [hσ]; exact hw

theorem hv_pure_bind {α γ : Type} {a : α} {g : α → NonDet (State Unit) γ} (h : HV P Q (g a)) :
    HV P Q ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hσ x hx

theorem hv_gets_bind {α γ : Type} {f : State Unit → α} {k : α → NonDet (State Unit) γ} (F : UView → α)
    (hF : ∀ σ, f σ = F (uV σ)) (h : ∀ w, P w → HV (· = w) Q (k (F w))) : HV P Q (NonDet.gets f >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [hF] at hx
  exact h _ hσ σ rfl x hx

theorem hv_getCap_bind {α : Type} {sl : CslotPtr} {k : Cap → NonDet (State Unit) α}
    (h : ∀ w c, P w → w.2.1 sl = some c → HV (· = w) Q (k c)) : HV P Q (getCap (Z := Unit) sl >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e, hc⟩ := getCap_capAt hy
  obtain ⟨c, s⟩ := y
  simp only at e hc; subst e
  exact h _ c hσ hc s rfl x hx

end HVc

/-! ## The view writers -/

theorem hv_setCdt (t : Cdt) (w : UView) : HV (· = w) (· = vCdt t w) (setCdt (Z := Unit) t) := by
  intro σ hσ y hy
  unfold setCdt at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  rw [Set.mem_singleton_iff.1 hy]
  subst hσ; rfl

theorem hv_setOriginal (sl : CslotPtr) (v : Bool) (w : UView) :
    HV (· = w) (· = vOrig sl v w) (setOriginal (Z := Unit) sl v) := by
  intro σ hσ y hy
  unfold setOriginal at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  rw [Set.mem_singleton_iff.1 hy]
  subst hσ; rfl

theorem hv_doExtendedOp {P : UView → Prop} (e : DetExtMonad Unit) : HV P P (doExtendedOp (Z := Unit) e) :=
  hv_uk fun _ => ik_doExtendedOp (fun _ _ h => h) _

theorem tcbI_01 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 1 := by decide
theorem tcbI_02 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 2 := by decide
theorem tcbI_03 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 3 := by decide
theorem tcbI_04 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 4 := by decide
theorem tcbI_05 : tcbCnodeIndex 0 ≠ tcbCnodeIndex 5 := by decide
theorem tcbI_10 : tcbCnodeIndex 1 ≠ tcbCnodeIndex 0 := by decide
theorem tcbI_12 : tcbCnodeIndex 1 ≠ tcbCnodeIndex 2 := by decide
theorem tcbI_13 : tcbCnodeIndex 1 ≠ tcbCnodeIndex 3 := by decide
theorem tcbI_14 : tcbCnodeIndex 1 ≠ tcbCnodeIndex 4 := by decide
theorem tcbI_15 : tcbCnodeIndex 1 ≠ tcbCnodeIndex 5 := by decide
theorem tcbI_20 : tcbCnodeIndex 2 ≠ tcbCnodeIndex 0 := by decide
theorem tcbI_21 : tcbCnodeIndex 2 ≠ tcbCnodeIndex 1 := by decide
theorem tcbI_23 : tcbCnodeIndex 2 ≠ tcbCnodeIndex 3 := by decide
theorem tcbI_24 : tcbCnodeIndex 2 ≠ tcbCnodeIndex 4 := by decide
theorem tcbI_25 : tcbCnodeIndex 2 ≠ tcbCnodeIndex 5 := by decide
theorem tcbI_30 : tcbCnodeIndex 3 ≠ tcbCnodeIndex 0 := by decide
theorem tcbI_31 : tcbCnodeIndex 3 ≠ tcbCnodeIndex 1 := by decide
theorem tcbI_32 : tcbCnodeIndex 3 ≠ tcbCnodeIndex 2 := by decide
theorem tcbI_34 : tcbCnodeIndex 3 ≠ tcbCnodeIndex 4 := by decide
theorem tcbI_35 : tcbCnodeIndex 3 ≠ tcbCnodeIndex 5 := by decide
theorem tcbI_40 : tcbCnodeIndex 4 ≠ tcbCnodeIndex 0 := by decide
theorem tcbI_41 : tcbCnodeIndex 4 ≠ tcbCnodeIndex 1 := by decide
theorem tcbI_42 : tcbCnodeIndex 4 ≠ tcbCnodeIndex 2 := by decide
theorem tcbI_43 : tcbCnodeIndex 4 ≠ tcbCnodeIndex 3 := by decide
theorem tcbI_45 : tcbCnodeIndex 4 ≠ tcbCnodeIndex 5 := by decide
theorem tcbI_50 : tcbCnodeIndex 5 ≠ tcbCnodeIndex 0 := by decide
theorem tcbI_51 : tcbCnodeIndex 5 ≠ tcbCnodeIndex 1 := by decide
theorem tcbI_52 : tcbCnodeIndex 5 ≠ tcbCnodeIndex 2 := by decide
theorem tcbI_53 : tcbCnodeIndex 5 ≠ tcbCnodeIndex 3 := by decide
theorem tcbI_54 : tcbCnodeIndex 5 ≠ tcbCnodeIndex 4 := by decide

/-- `set_cap`: the written slot holds the new cap. -/
theorem setCap_at {c : Cap} {sl : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setCap (Z := Unit) c sl σ).1) : capAt y.2 sl = some c := by
  obtain ⟨o, r⟩ := sl
  unfold setCap at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨obj, z2⟩ := z
  simp only at hk hs; subst hs
  dsimp only at hy
  have key : ∃ O, y ∈ (setObject (Z := Unit) o O z2).1 ∧ capView O r = some c := by
    cases obj with
    | cnode sz cn =>
      dsimp only at hy
      split_ifs at hy with hcnd
      · obtain ⟨w, hw, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 hw
        have hwf : wellFormedCnodeN sz (Function.update cn r (some c)) := by
          unfold wellFormedCnodeN; rw [dom_update_some hcnd.1]; exact hcnd.2
        exact ⟨_, hy, by simp only [capView_cnode, if_pos hwf, Function.update_self]⟩
      · first | exact hy.elim | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
    | tcb t =>
      dsimp only at hy
      split_ifs at hy with h0 h1 h2 h3 h4 h5 <;>
        first
        | exact hy.elim
        | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
        | (obtain ⟨w, hw, hy⟩ := hy
           obtain rfl := Set.mem_singleton_iff.1 hw
           refine ⟨_, hy, ?_⟩
           subst_vars
           simp only [capView_tcb, tcbCnodeMap, Function.update_apply, tcbI_01, tcbI_02, tcbI_03, tcbI_04, tcbI_05, tcbI_10, tcbI_12, tcbI_13, tcbI_14, tcbI_15, tcbI_20, tcbI_21, tcbI_23, tcbI_24, tcbI_25, tcbI_30, tcbI_31, tcbI_32, tcbI_34, tcbI_35, tcbI_40, tcbI_41, tcbI_42, tcbI_43, tcbI_45, tcbI_50, tcbI_51, tcbI_52, tcbI_53, tcbI_54, if_true, if_false])
    | _ => first | exact hy.elim | (obtain ⟨w, hw, -⟩ := hy; exact hw.elim)
  obtain ⟨O, hyO, hO⟩ := key
  obtain ⟨old, -, e⟩ := setObject_out hyO
  rw [e, capAt_upd, if_pos rfl]; exact hO

theorem hv_setCap (c : Cap) (sl : CslotPtr) (w : UView) : HV (· = w) (· = vCap sl c w) (setCap (Z := Unit) c sl) := by
  intro σ hσ y hy
  subst hσ
  obtain ⟨hk, hoth, -, hcdt, horig⟩ := setCap_out hy
  have hat := setCap_at hy
  unfold uV vCap
  simp only [hcdt, horig, Prod.mk.injEq, and_true]
  refine ⟨funext fun p => hk p, funext fun sl' => ?_⟩
  by_cases e : sl' = sl
  · subst e; rw [Function.update_self]; exact hat
  · rw [Function.update_of_ne e]; exact hoth sl' e

/-! ## `empty_slot` -/

/-- The CDT after `empty_slot s`: the children of `s` become children of its parent. -/
def es (t : Cdt) (s : CslotPtr) : Cdt := Function.update (fun p => if t p = some s then t s else t p) s none

theorem es_po {t : Cdt} {s a b : CslotPtr} (h : es t s b = some a) :
    b ≠ s ∧ (t b = some a ∨ (t b = some s ∧ t s = some a)) := by
  by_cases hb : b = s
  · subst hb; simp [es] at h
  · refine ⟨hb, ?_⟩
    unfold es at h
    rw [Function.update_of_ne hb] at h
    split at h
    · exact Or.inr ⟨by assumption, h⟩
    · exact Or.inl h

theorem es_noKid {t : Cdt} (hA : ∀ x, ¬ Relation.TransGen (parentOf t) x x) {s b : CslotPtr} :
    es t s b ≠ some s := by
  intro h
  by_cases hb : b = s
  · subst hb; simp [es] at h
  · unfold es at h
    rw [Function.update_of_ne hb] at h
    split at h
    · exact hA s (Relation.TransGen.single h)
    · rename_i hn; exact hn h

theorem es_tg_old {t : Cdt} {s x y : CslotPtr} (h : Relation.TransGen (parentOf (es t s)) x y) :
    Relation.TransGen (parentOf t) x y := by
  have step : ∀ a b, parentOf (es t s) a b → Relation.TransGen (parentOf t) a b := by
    intro a b hab
    rcases (es_po hab).2 with h1 | ⟨h1, h2⟩
    · exact Relation.TransGen.single h1
    · exact Relation.TransGen.head h2 (Relation.TransGen.single h1)
  induction h with
  | single hab => exact step _ _ hab
  | tail _ hbc ih => exact Relation.TransGen.trans ih (step _ _ hbc)

theorem es_tg_new {t : Cdt} (hA : ∀ x, ¬ Relation.TransGen (parentOf t) x x) {s x y : CslotPtr}
    (h : Relation.TransGen (parentOf t) x y) (hx : x ≠ s) :
    (y ≠ s → Relation.TransGen (parentOf (es t s)) x y) ∧
      (y = s → ∀ a, t s = some a → x = a ∨ Relation.TransGen (parentOf (es t s)) x a) := by
  induction h with
  | single hxy =>
    rename_i y
    refine ⟨fun hy => Relation.TransGen.single ?_, fun hy a ha => ?_⟩
    · show es t s y = some x
      have hxy' : t y = some x := hxy
      unfold es; rw [Function.update_of_ne hy]
      rw [if_neg (show ¬ t y = some s by rw [hxy']; exact fun e => hx (Option.some.inj e))]; exact hxy'
    · subst hy
      have hxy' : t y = some x := hxy
      rw [hxy'] at ha; exact Or.inl (Option.some.inj ha)
  | tail hxb hby ih =>
    rename_i b y
    have hby' : t y = some b := hby
    refine ⟨fun hy => ?_, fun hy a ha => ?_⟩
    · by_cases hb : b = s
      · subst hb
        obtain ⟨a, ha⟩ := tg_last hxb
        have hes : es t b y = some a := by
          unfold es; rw [Function.update_of_ne hy]; rw [if_pos hby']; exact ha
        rcases ih.2 rfl a ha with e | h'
        · subst e; exact Relation.TransGen.single hes
        · exact Relation.TransGen.tail h' hes
      · have hes : es t s y = some b := by
          unfold es; rw [Function.update_of_ne hy]
          rw [if_neg (show ¬ t y = some s by rw [hby']; exact fun e => hb (Option.some.inj e))]; exact hby'
        exact Relation.TransGen.tail (ih.1 hb) hes
    · subst hy
      rw [hby'] at ha; obtain rfl := Option.some.inj ha
      have hb : b ≠ y := fun e => by subst e; exact hA b (Relation.TransGen.single hby')
      exact Or.inr (ih.1 hb)

/-- The view after `empty_slot s` of a non-null cap. -/
def vEs (s : CslotPtr) (w : UView) : UView :=
  vCap s .nullCap (vOrig s false (vCdt (es w.2.2.1 s) w))

theorem utInv'_vEs {w : UView} (hI : UtInv'V w) {s : CslotPtr} {c : Cap} (hc : w.2.1 s = some c)
    (hnn : c ≠ .nullCap) : UtInv'V (vEs s w) := by
  obtain ⟨hU, hO, hA⟩ := hI
  have hcap : ∀ sl, sl ≠ s → (vEs s w).2.1 sl = w.2.1 sl := fun sl h => Function.update_of_ne h _ _
  have hnu : ∀ sl d b n f, (vEs s w).2.1 sl = some (.untypedCap d b n f) → sl ≠ s := by
    intro sl d b n f h e; subst e
    simp [vEs, vCap] at h
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun sl d b n f h => ?_, fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 h1 h2 hd => ?_,
    fun sl d b n f h ho => ?_⟩ hU, fun c' p h => ?_, fun x hx => ?_⟩
  · have := hnu sl d b n f h
    rw [hcap sl this] at h; exact same_capV hU.2.1 h
  · exact (es_tg_new hA hd (hnu s1 _ _ _ _ h1)).1 (hnu s2 _ _ _ _ h2)
  · show Function.update w.2.2.2 s false sl = true
    rw [Function.update_of_ne (hnu sl d b n f h)]; exact ho
  · have h' : es w.2.2.1 s c' = some p := h
    have hps : p ≠ s := fun e => by subst e; exact es_noKid hA h'
    rw [hcap p hps]
    rcases (es_po h').2 with h1 | ⟨-, h2⟩
    · exact hO _ _ h1
    · exact hO _ _ h2
  · exact hA x (es_tg_old hx)

theorem hv_emptySlot (s : CslotPtr) (info : Cap) : HV UtInv'V UtInv'V (emptySlot (Z := Unit) s info) := by
  unfold emptySlot
  refine hv_getCap_bind fun w c hw hc => ?_
  split
  · exact hv_ret _ hw
  · rename_i hnn
    refine hv_mono (Q := (· = vEs s w)) ?_ (fun _ e => e ▸ utInv'_vEs hw hc hnn)
    refine hv_gets_bind (fun w => w.2.2.1 s) (fun _ => rfl) fun w1 hw1 => ?_
    subst hw1
    refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w2 hw2 => ?_
    subst hw2
    refine hv_pure_bind ?_
    refine hv_bind (hv_setCdt _ _) fun _ => ?_
    refine hv_bind (hv_doExtendedOp _) fun _ => ?_
    refine hv_bind (hv_setOriginal _ _ _) fun _ => ?_
    refine hv_bind (hv_setCap _ _ _) fun _ => ?_
    exact hv_uk fun _ => uk_postCapDeletion _

/-- **`empty_slot` keeps `UtInv'`.** -/
theorem ik_emptySlot' (s : CslotPtr) (info : Cap) : IK UtInv' (emptySlot (Z := Unit) s info) :=
  hv_emptySlot s info

end

end Fl4Proofs.P3.SInvU
