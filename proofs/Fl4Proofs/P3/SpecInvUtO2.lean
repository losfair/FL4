/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut7): **the carried family
`P3 N σ := UtInv'' σ ∧ IrqOutV N (uV σ)`, the untyped-copy insert, and the IPC
cap transfer** (spec side only; imports SpecInvUtO1).

* `utN_utCopy` / **`hv_capInsertN_ut`**: `cap_insert` of an untyped cap's own
  copy (`derive_cap` ran `ensure_no_children src`) into a null `PosOK` slot keeps
  `UtInv''`. The source has no CDT child, so by `UtCh` no cap covers any address
  of its region: the region facts for the raised source and the copy are
  vacuous; `CapFree` for the copy is the source's old free part, for the raised
  source the free part is empty; the copy's slot is made non-null at a `PosOK`
  position (IfUnsafe, CnShape).
* `CI3 w c src` (the inserted cap is the source's untyped cap with no children,
  or `RefRel`-derived from the source's cap) and **`hv_capInsert3`** (`P3 N`
  kept by such an insert into a `PosOK` slot; ut6's `hv_capInsertP` + the above +
  `hv_capInsertIO`).
* Lookups: `okv_deriveCapR` (`derive_cap` gives the source's untyped cap after
  `ensure_no_children`, or a `RefRel` cap, or null), `okv_lookupCap`,
  `okv_unifyFailure`, `getReceiveSlots_dest` (the receive slot is reached through
  a CNode cap in a slot, so it is `DestRefV`).
* **`p3_doNormalTransfer`** (no premise), via `p3_transferCapsLoop` /
  `p3_transferCaps`.
* Family leaves with no decode fact: `p3_of`, `p3_of_uk`, `p3_capDeleteOne`,
  `p3_recDel_cte` / `_fin`, `p3_capDelete`, `p3_checkCapAt_ins` (n < 6),
  `p3_installTcbCap`.
-/
import Fl4Proofs.P3.SpecInvUtO1
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The untyped copy -/

theorem utFr_full (b : ObjRef) (n : Nat) (k : Nat) : k ∉ utFr b n (2 ^ n) := by
  intro h; obtain ⟨h1, h2⟩ := h; omega

theorem utN_utCopy {w w' : UView} (hI : UtInv'V w) (hN : UtNV w) {src dest : CslotPtr} {d : Bool} {b : ObjRef}
    {n f : Nat} {v : Option CslotPtr}
    (hd : w.2.1 dest = some .nullCap) (hs : w.2.1 src = some (.untypedCap d b n f))
    (hk0 : ∀ x, w.2.2.1 x ≠ some src) (hP : PosOK w dest)
    (h1 : w'.2.1 = Function.update (Function.update w.2.1 src (some (.untypedCap d b n (2 ^ n)))) dest
      (some (.untypedCap d b n f)))
    (h2 : w'.2.2.1 = Function.update w.2.2.1 dest v) (hvd : v ≠ some dest) : UtNV w' := by
  obtain ⟨-, hO, -⟩ := hI
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  have hsd : src ≠ dest := fun e => by subst e; rw [hd] at hs; cases hs
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hcap : ∀ sl x, w'.2.1 sl = some x → (dest = sl ∧ x = .untypedCap d b n f) ∨
      (src = sl ∧ x = .untypedCap d b n (2 ^ n)) ∨ (sl ≠ dest ∧ sl ≠ src ∧ w.2.1 sl = some x) := by
    intro sl x h
    rw [h1] at h
    rcases upd_cap h with ⟨e1, e2⟩ | ⟨ne1, h'⟩
    · exact Or.inl ⟨e1.symm, e2⟩
    · rcases upd_cap h' with ⟨e1, e2⟩ | ⟨ne2, h''⟩
      · exact Or.inr (Or.inl ⟨e1.symm, e2⟩)
      · exact Or.inr (Or.inr ⟨ne1, ne2, h''⟩)
  have hold : ∀ sl, sl ≠ dest → sl ≠ src → w'.2.1 sl = w.2.1 sl := fun sl e1 e2 => by
    rw [h1, Function.update_of_ne e1, Function.update_of_ne e2]
  have hrng : ∀ sl x r, w'.2.1 sl = some x → r ∈ capRng x → sl ≠ dest ∧ sl ≠ src ∧ w.2.1 sl = some x := by
    intro sl x r h hr
    rcases hcap sl x h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | h'
    · rw [capRng_ut] at hr; exact hr.elim
    · rw [capRng_ut] at hr; exact hr.elim
    · exact h'
  -- no cap covers an address of the source's region
  have hnone : ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r ∉ delR b n := by
    intro s c r h hr hrd
    exact desc_noKids hk0 (hC src d b n f hs s c r h hr hrd)
  have hut : ∀ u d' b' n' f', w'.2.1 u = some (.untypedCap d' b' n' f') →
      ((u = dest ∨ u = src) ∧ d = d' ∧ b = b' ∧ n = n' ∧ (f = f' ∨ 2 ^ n = f')) ∨
        (u ≠ dest ∧ u ≠ src ∧ w.2.1 u = some (.untypedCap d' b' n' f')) := by
    intro u d' b' n' f' h
    rcases hcap u _ h with ⟨e, e'⟩ | ⟨e, e'⟩ | h'
    · cases e'; exact Or.inl ⟨Or.inl e.symm, rfl, rfl, rfl, Or.inl rfl⟩
    · cases e'; exact Or.inl ⟨Or.inr e.symm, rfl, rfl, rfl, Or.inr rfl⟩
    · exact Or.inr h'
  have hinut : ∀ q, InUtV w' q → InUtV w q := by
    rintro q ⟨u, d', b', n', f', hu, hq⟩
    rcases hut u d' b' n' f' hu with ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, -, hu'⟩
    · exact ⟨src, d, b, n, f, hs, hq⟩
    · exact ⟨u, d', b', n', f', hu', hq⟩
  have hwit : ∀ q s0 c0, w.2.1 s0 = some c0 → q ∈ sRefs c0 → ∃ s c', w'.2.1 s = some c' ∧ q ∈ sRefs c' := by
    intro q s0 c0 h0 hq
    have e1 : s0 ≠ dest := fun e => by subst e; rw [hd] at h0; cases h0; exact sRefs_nn hq rfl
    have e2 : s0 ≠ src := fun e => by subst e; rw [hs] at h0; cases h0; simp [sRefs] at hq
    exact ⟨s0, c0, (hold s0 e1 e2).trans h0, hq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- UtCh
    intro u d' b' n' f' hu s' c' r hs' hr hrd
    obtain ⟨hsd', hss', hs''⟩ := hrng s' c' r hs' hr
    rcases hut u d' b' n' f' hu with ⟨-, rfl, rfl, rfl, -⟩ | ⟨hud, -, hu'⟩
    · exact (hnone s' c' r hs'' hr hrd).elim
    · show Relation.TransGen (parentOf w'.2.2.1) u s'
      rw [h2]; exact (lu_tg hk hvd hsd').2 (hC u d' b' n' f' hu' s' c' r hs'' hr hrd)
  · -- IfUnsafe
    intro p cp hp hne hin
    have hin' := hinut p.1 hin
    rcases hcap p cp hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, hp'⟩
    · obtain ⟨s0, c0, h0, hq⟩ := hP.1 hin'; exact hwit _ s0 c0 h0 hq
    · obtain ⟨s0, c0, h0, hq⟩ := hU _ _ hs (fun e => by cases e) hin'; exact hwit _ s0 c0 h0 hq
    · obtain ⟨s0, c0, h0, hq⟩ := hU p cp hp' hne hin'; exact hwit _ s0 c0 h0 hq
  · -- CapFree
    intro u d' b' n' f' hu s' c' r hs' hr
    obtain ⟨-, -, hs''⟩ := hrng s' c' r hs' hr
    rcases hut u d' b' n' f' hu with ⟨-, rfl, rfl, rfl, rfl | rfl⟩ | ⟨-, -, hu'⟩
    · exact hF src d b n f hs s' c' r hs'' hr
    · exact utFr_full b n _
    · exact hF u d' b' n' f' hu' s' c' r hs'' hr
  · -- CapKind
    intro sa ca sb cb r ha hb hra hrb
    exact hK sa ca sb cb r (hrng sa ca r ha hra).2.2 (hrng sb cb r hb (sRefs_sub_capRng _ hrb)).2.2 hra hrb
  · -- CnShape
    intro sa ca r ha hr i c' hi hne
    have ha' := (hrng sa ca r ha (sRefs_sub_capRng _ hr)).2.2
    rcases hcap (r, i) c' hi with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, hi'⟩
    · rw [e] at hP; exact hP.2 sa ca ha' hr
    · exact hS sa ca r ha' hr i _ (by rw [← e]; exact hs) (fun h => by cases h)
    · exact hS sa ca r ha' hr i c' hi' hne
  · -- ZFinal
    intro sz r b0 n0 hz s' c' hne hs'
    obtain ⟨-, -, hz'⟩ := hrng sz _ r hz (objRefs_sub_capRng _ (by simp [objRefs]))
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hs''⟩
    · simp [objRefs]
    · simp [objRefs]
    · exact hZ sz r b0 n0 hz' s' c' hne hs''
  · -- CnBits
    intro sa ca ha
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, ha'⟩
    · intro bb hb; simp [shp] at hb
    · intro bb hb; simp [shp] at hb
    · exact hB sa ca ha'

theorem hv_utN_copy {d : Bool} {b : ObjRef} {n f : Nat} (src dest : CslotPtr) :
    HV (fun w => UtInv''V w ∧ w.2.1 src = some (.untypedCap d b n f) ∧ (∀ x, w.2.2.1 x ≠ some src) ∧ PosOK w dest)
      UtNV (capInsert (Z := Unit) (.untypedCap d b n f) src dest) := by
  unfold capInsert
  refine hv_getCap_bind fun w sc ⟨hw, hs, hk0, hP⟩ hsc => ?_
  obtain rfl : sc = .untypedCap d b n f := Option.some.inj (hsc.symm.trans hs)
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hw.1.2.1 x dest hx; rw [hoc] at hc'; cases hc'; exact hcn rfl
  have hne : dest ≠ src := fun e => by subst e; rw [hs] at hoc; cases hoc
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
  refine utN_utCopy hw.1 hw.2 hoc hs hk0 hP rfl rfl ?_
  split
  · exact fun h => hne (Option.some.inj h).symm
  · exact hkd src

/-- **`cap_insert` of an untyped cap's own copy keeps `UtInv''`** (source childless, destination `PosOK`). -/
theorem hv_capInsertN_ut {d : Bool} {b : ObjRef} {n f : Nat} (src dest : CslotPtr) :
    HV (fun w => UtInv''V w ∧ w.2.1 src = some (.untypedCap d b n f) ∧ (∀ x, w.2.2.1 x ≠ some src) ∧ PosOK w dest)
      UtInv''V (capInsert (Z := Unit) (.untypedCap d b n f) src dest) := fun σ hσ y hy =>
  ⟨hv_capInsert_ut src dest σ ⟨hσ.1.1, hσ.2.1, hσ.2.2.1⟩ y hy, hv_utN_copy src dest σ hσ y hy⟩

/-! ## The family -/

/-- **The carried family**: `UtInv''` and the IRQ-node fact for a fixed node map `N`. -/
def P3V (N : Irq → ObjRef) (w : UView) : Prop := UtInv''V w ∧ IrqOutV N w

abbrev P3 (N : Irq → ObjRef) (σ : State Unit) : Prop := P3V N (uV σ)

theorem utInv3_iff {σ : State Unit} : UtInv3 σ ↔ P3 σ.interruptIrqNode σ := Iff.rfl

/-- The inserted cap: the source's own childless untyped cap, or derived from the source's cap. -/
def CI3 (w : UView) (c : Cap) (src : CslotPtr) : Prop :=
  ∃ c0, w.2.1 src = some c0 ∧
    ((c = c0 ∧ (∃ d b n f, c0 = .untypedCap d b n f) ∧ ∀ x, w.2.2.1 x ≠ some src) ∨ RefRel c0 c)

variable {N : Irq → ObjRef}

/-- **`cap_insert` keeps `P3 N`** for a `CI3` cap into a `PosOK` slot. -/
theorem hv_capInsert3 (c : Cap) (src dest : CslotPtr) :
    HV (fun w => P3V N w ∧ CI3 w c src ∧ PosOK w dest) (P3V N) (capInsert (Z := Unit) c src dest) := by
  intro σ hσ y hy
  obtain ⟨⟨hI, hO⟩, ⟨c0, hs, hc⟩, hP⟩ := hσ
  have hcov : ∀ c1, (uV σ).2.1 src = some c1 → covR c ⊆ covR c1 := by
    intro c1 h1; rw [hs] at h1; cases h1
    rcases hc with ⟨rfl, -, -⟩ | hR
    · exact subset_rfl
    · exact covR_sub_of_refRel hR
  refine ⟨?_, hv_capInsertIO c src dest σ ⟨hO, hcov⟩ y hy⟩
  rcases hc with ⟨rfl, ⟨d, b, n, f, rfl⟩, hk⟩ | hR
  · exact hv_capInsertN_ut src dest σ ⟨hI, hs, hk, hP⟩ y hy
  · exact hv_capInsertP c src dest σ ⟨hI, fun c1 h1 => by rw [hs] at h1; cases h1; exact hR, hP⟩ y hy

theorem p3_of {α : Type} {m : NonDet (State Unit) α} (hU : IK UtInv'' m) (hO : IK (IO N) m) : IK (P3 N) m :=
  fun σ h y hy => ⟨hU σ h.1 y hy, hO σ h.2 y hy⟩

theorem p3_of_uk {α : Type} {m : NonDet (State Unit) α} (h : ∀ v, UK v m) : IK (P3 N) m :=
  ik_of_uk (fun _ _ e hI => by show P3V N _; rw [e]; exact hI) h

theorem p3e_of_uk {ε α : Type} {m : NonDetE (State Unit) ε α} (h : ∀ v, UKE v m) : IKE (P3 N) m := p3_of_uk h

theorem p3_of_view {σ σ' : State Unit} (h : uV σ' = uV σ) (hI : P3 N σ) : P3 N σ' := by
  show P3V N (uV σ'); rw [h]; exact hI

theorem p3_capDeleteOne (sl : CslotPtr) : IK (P3 N) (capDeleteOne (Z := Unit) sl) :=
  p3_of (ik_capDeleteOneN sl) (io_capDeleteOne sl)

theorem p3_recDel_cte (s : CslotPtr) (e : Bool) : IKE (P3 N) (recDel (Z := Unit) (.cTEDeleteCall s e)) :=
  p3_of (ikN_recDel_cte s e) (io_recDel _)

theorem p3_recDel_fin (s : CslotPtr) (e : Bool) : IKE (P3 N) (recDel (Z := Unit) (.finaliseSlotCall s e)) :=
  p3_of (ikN_recDel_fin s e) (io_recDel _)

theorem p3_capDelete (slot : CslotPtr) : IKE (P3 N) (capDelete (Z := Unit) slot) :=
  p3_of (ikN_capDelete slot) (io_capDelete slot)

theorem p3_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : ObjRef) (sl : CslotPtr) (n : Nat) (hn : n < 6) :
    IK (P3 N) (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap t) sl (capInsert c src (t, tcbCnodeIndex n)))) :=
  p3_of (ikN_checkCapAt_ins c src t sl n hn) (io_checkCapAt_ins c src _ sl _)

theorem p3_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr))
    (hn : n < 6) : IKE (P3 N) (installTcbCap (Z := Unit) target slot n slotOpt) := by
  cases slotOpt with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine ike_bind (p3_capDelete _) fun _ => ?_
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (p3_checkCapAt_ins c src target slot n hn)

/-! ## Lookups -/

theorem refRel_self {c : Cap} (hz : ∀ r b n, c ≠ .zombie r b n) (hu : ∀ d b n f, c ≠ .untypedCap d b n f) :
    RefRel c c :=
  ⟨subset_rfl, rfl, hz, fun r b n e => absurd e (hz r b n), hu⟩

/-- **`derive_cap`**: the derived cap is null, the source's own untyped cap after
`ensure_no_children`, or derived (`RefRel`). -/
theorem okv_deriveCapR {w : UView} (sl : CslotPtr) (c : Cap) :
    OkV w (fun c' => c' ≠ .nullCap → (c' = c ∧ (∃ d b n f, c = .untypedCap d b n f) ∧ ∀ x, w.2.2.1 x ≠ some sl) ∨
      RefRel c c') (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap
  split
  · unfold archDeriveCap
    split <;> first
      | exact okv_throw _
      | exact okv_returnOk fun h => absurd rfl h
      | exact okv_returnOk fun _ => Or.inr (refRel_self (fun _ _ _ e => by cases e) (fun _ _ _ _ e => by cases e))
      | exact okv_returnOk fun _ => Or.inr ⟨fun _ h => h, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e),
          fun _ _ _ _ e => (by cases e)⟩
  · refine okv_bind (fun _ => uk_ensureNoChildren sl) (okv_ensureNoChildren sl) fun _ hk => okv_returnOk ?_
    exact fun _ => Or.inl ⟨rfl, ⟨_, _, _, _, rfl⟩, hk⟩
  · exact okv_returnOk fun h => absurd rfl h
  · exact okv_returnOk fun h => absurd rfl h
  · rename_i h1 h2 h3 h4
    exact okv_returnOk fun _ => Or.inr (refRel_self (fun r b n e => h3 r b n e) (fun d b n f e => h2 d b n f e))

theorem okv_unifyFailure {w : UView} {F α : Type} {P : α → Prop} {m : NonDetE (State Unit) F α}
    (h : OkV w P m) : OkV w P (unifyFailure (Z := Unit) m) := by
  intro σ hσ a s hs
  unfold unifyFailure NonDetE.handleE at hs
  rw [ExceptT.run_mk] at hs
  obtain ⟨z, hz, hs⟩ := hs
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok b =>
    have e := Set.mem_singleton_iff.1 hs
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h σ hσ _ _ hz
  | error e =>
    have e' := Set.mem_singleton_iff.1 hs; simp at e'

theorem okv_lookupCap {w : UView} (t : ObjRef) (cp : CapRef) :
    OkV w (fun c => ∃ s, w.2.1 s = some c) (lookupCap (Z := Unit) t cp) := by
  unfold lookupCap
  refine okv_bind_uk (fun _ => uk_lookupSlotForThread _ _) fun x => ?_
  obtain ⟨sl, cr⟩ := x
  intro σ hσ a s hs
  obtain ⟨x, hx, e⟩ := mem_liftE' hs
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact ⟨sl, by rw [← hσ]; exact (getCap_capAt hx).2⟩

/-- The receive slots are reached through a CNode cap in a slot. -/
theorem getReceiveSlots_dest (t : ObjRef) (b : Option ObjRef) (σ : State Unit) :
    ∀ x ∈ (getReceiveSlots (Z := Unit) t b σ).1, ∀ d ∈ x.1, DestRefV (uV σ) d := by
  intro x hx
  cases b with
  | none => unfold getReceiveSlots at hx; rw [Set.mem_singleton_iff.1 hx]; simp
  | some buf =>
    unfold getReceiveSlots at hx
    obtain ⟨y, hy, hx⟩ := hx
    have hvy : uV y.2 = uV σ := uk_mem (fun _ => uk_loadCapTransfer _) hy
    unfold emptyOnFailure NonDetE.catch at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨r, s⟩ := z
    cases r with
    | error e => rw [Set.mem_singleton_iff.1 hx]; simp
    | ok l =>
      rw [Set.mem_singleton_iff.1 hx]
      have key : OkV (uV y.2) (fun l : List CslotPtr => ∀ d ∈ l, DestRefV (uV y.2) d) (do
          let cnode ← unifyFailure (Z := Unit) (lookupCap t y.1.ctReceiveRoot)
          let slot ← unifyFailure (Z := Unit) (lookupTargetSlot cnode y.1.ctReceiveIndex (unat y.1.ctReceiveDepth))
          let cap ← NonDetE.liftE (getCap (Z := Unit) slot)
          NonDetE.whenE (cap ≠ .nullCap) (NonDetE.throwError ())
          NonDetE.returnOk [slot]) := by
        refine okv_bind (fun _ => by uk_auto) (okv_unifyFailure (okv_lookupCap _ _)) fun cn hcn => ?_
        refine okv_bind (fun _ => by uk_auto)
          (okv_unifyFailure (okv_lookupSlotForCnodeOpN false cn _ _ hcn)) fun sl hsl => ?_
        exact okv_liftE_getCap_bind fun _ _ => okv_whenE_bind fun _ => okv_returnOk (by simpa using hsl)
      rw [← hvy]; exact key y.2 rfl l s hz

/-! ## The IPC cap transfer -/

theorem whenE_throw_ok {ε : Type} {c : Prop} [Decidable c] {e : ε} {σ : State Unit} {z : Except ε Unit × State Unit}
    {u : Unit} (hz : z ∈ ((NonDetE.whenE c (NonDetE.throwError e) : NonDetE (State Unit) ε Unit).run σ).1)
    (hu : z.1 = .ok u) : ¬ c ∧ z.2 = σ := by
  unfold NonDetE.whenE at hz
  split at hz
  · rw [Set.mem_singleton_iff.1 hz] at hu; cases hu
  · rename_i hc; exact ⟨hc, by rw [Set.mem_singleton_iff.1 hz]⟩

theorem p3_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (caps : List (Cap × CslotPtr)) (n : Nat) (slots : List CslotPtr) (mi : MessageInfo) (σ : State Unit),
      P3 N σ → slots.length ≤ 1 → (∀ d ∈ slots, DestRefV (uV σ) d) →
      (slots ≠ [] → ∀ p ∈ caps, capAt σ p.2 = some p.1) →
      ∀ y ∈ (transferCapsLoop (Z := Unit) ep rb n caps slots mi σ).1, P3 N y.2
  | [], n, slots, mi, σ, hI, _, _, _, y, hy => by
    unfold transferCapsLoop at hy; rw [Set.mem_singleton_iff.1 hy]; exact hI
  | (cap, slot) :: more, n, slots, mi, σ, hI, hl, hD, hc, y, hy => by
    have ih := p3_transferCapsLoop ep rb more (n + 1)
    unfold transferCapsLoop constOnFailure NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hyz : y.2 = z.2 := by
      obtain ⟨r, s⟩ := z
      cases r <;> (rw [Set.mem_singleton_iff.1 hy])
    rw [hyz]
    clear hy hyz
    replace hz := run_returnOk_bind_mem hz
    try dsimp only at hz
    split at hz
    · obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
      have hv := uk_mem (fun _ => uk_setExtraBadge _ _ _) hx
      obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
      refine ih slots _ x.2 (p3_of_view hv hI) hl (fun d hd => by rw [hv]; exact hD d hd) (fun hne p hp => ?_) w hw
      rw [capAt_of_view hv]; exact hc hne p (List.mem_cons.2 (Or.inr hp))
    · split at hz
      · rename_i hne
        obtain ⟨z0, hz0, ⟨c', hc', hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
        · obtain ⟨r0, s0⟩ := z0
          simp only at hc'; subst hc'
          have hv0 : uV s0 = uV σ := uk_deriveCap slot cap σ rfl _ hz0
          have hd := okv_deriveCapR slot cap σ rfl c' s0 hz0
          obtain ⟨z1, hz1, ⟨u, hu, hz⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hz
          · obtain ⟨hnn, hs1⟩ := whenE_throw_ok hz1 hu
            obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
            rw [hs1] at hx
            have hI0 := p3_of_view hv0 hI
            have hcs := hc hne (cap, slot) (List.mem_cons.2 (Or.inl rfl))
            obtain ⟨dd, tl, rfl⟩ : ∃ dd tl, slots = dd :: tl := by
              cases slots with
              | nil => exact absurd rfl hne
              | cons a t => exact ⟨a, t, rfl⟩
            have hok : CI3 (uV s0) c' slot := by
              refine ⟨cap, by show capAt s0 slot = _; rw [capAt_of_view hv0]; exact hcs, ?_⟩
              rcases hd hnn with ⟨e1, hu', hk⟩ | hR
              · exact Or.inl ⟨e1, hu', by rw [hv0]; exact hk⟩
              · exact Or.inr hR
            have hP : PosOK (uV s0) dd := by
              rw [hv0]; exact posOK_of_destRef hI.1.2 (hD dd (List.mem_cons_self))
            have hIx := hv_capInsert3 c' slot dd s0 ⟨hI0, hok, hP⟩ x hx
            obtain ⟨w, hw, rfl⟩ := mem_liftE' hz
            have htl : tl = [] := by
              simp only [List.length_cons] at hl; exact List.eq_nil_of_length_eq_zero (by omega)
            subst htl
            exact ih [] _ x.2 hIx (by simp) (fun _ h => absurd h List.not_mem_nil) (fun h => absurd rfl h) w hw
          · have hs1 : z1.2 = s0 := by
              unfold NonDetE.whenE at hz1
              split at hz1 <;> (rw [Set.mem_singleton_iff.1 hz1])
            show P3 N z1.2
            rw [hs1]; exact p3_of_view hv0 hI
        · exact p3_of_view (uk_deriveCap slot cap σ rfl _ hz0) hI
      · rw [Set.mem_singleton_iff.1 hz]; exact hI

theorem p3_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (recv : ObjRef)
    (rbuf : Option ObjRef) (σ : State Unit) (hI : P3 N σ) (hc : ∀ p ∈ caps, capAt σ p.2 = some p.1) :
    ∀ y ∈ (transferCaps (Z := Unit) info caps ep recv rbuf σ).1, P3 N y.2 := by
  intro y hy
  unfold transferCaps at hy
  obtain ⟨x, hx, hy⟩ := hy
  have hv := uk_mem (fun _ => uk_getReceiveSlots _ _) hx
  have hlen := getReceiveSlots_len recv rbuf σ x hx
  have hdst := getReceiveSlots_dest recv rbuf σ x hx
  obtain ⟨x2, hx2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hx2
  dsimp only at hy
  cases rbuf with
  | none => rw [Set.mem_singleton_iff.1 hy]; exact p3_of_view hv hI
  | some b =>
    exact p3_transferCapsLoop ep b caps 0 x.1 _ x.2 (p3_of_view hv hI) hlen
      (fun d hd => by rw [hv]; exact hdst d hd)
      (fun _ p hp => by rw [capAt_of_view hv]; exact hc p hp) y hy

/-- **The normal IPC transfer keeps `P3 N`** (no premise). -/
theorem p3_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (recv : ObjRef) (rbuf : Option ObjRef) :
    IK (P3 N) (doNormalTransfer (Z := Unit) sender sbuf ep badge grant recv rbuf) := by
  intro σ hI y hy
  unfold doNormalTransfer at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  have hv1 := uk_mem (fun _ => uk_getMessageInfo _) hx1
  have hI1 : P3 N x1.2 := p3_of_view hv1 hI
  have tail : ∀ (caps : List (Cap × CslotPtr)) (s : State Unit), P3 N s → (∀ p ∈ caps, capAt s p.2 = some p.1) →
      ∀ y ∈ ((do
        let mrsTransferred ← copyMrs (Z := Unit) sender sbuf recv rbuf x1.1.miLength
        let mi' ← transferCaps x1.1 caps ep recv rbuf
        setMessageInfo recv { miLength := mrsTransferred, miExtraCaps := mi'.miExtraCaps, miCapsUnwrapped := mi'.miCapsUnwrapped, miLabel := x1.1.miLabel }
        asUser recv (setRegister badge_register badge)) s).1, P3 N y.2 := by
    intro caps s hs hc y hy
    obtain ⟨x3, hx3, hy⟩ := hy
    have hv3 := uk_mem (fun _ => uk_copyMrs _ _ _ _ _) hx3
    obtain ⟨x4, hx4, hy⟩ := hy
    have hI4 := p3_transferCaps _ _ _ _ _ x3.2 (p3_of_view hv3 hs)
      (fun p hp => by rw [capAt_of_view hv3]; exact hc p hp) x4 hx4
    exact (p3_of_uk fun _ => by uk_auto) x4.2 hI4 y hy
  simp only at hy
  split at hy
  · obtain ⟨x2, hx2, hy⟩ := hy
    unfold NonDetE.catch at hx2
    obtain ⟨z, hz, hx2⟩ := hx2
    have hvz : uV z.2 = uV x1.2 := uk_lookupExtraCaps _ _ _ x1.2 rfl z hz
    obtain ⟨r, s⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      exact tail [] s (p3_of_view hvz hI1) (fun p hp => absurd hp List.not_mem_nil) y hy
    | ok l =>
      obtain rfl := Set.mem_singleton_iff.1 hx2
      refine tail l s (p3_of_view hvz hI1) (fun p hp => ?_) y hy
      have := okv_lookupExtraCaps sender sbuf x1.1 x1.2 rfl l s hz p hp
      rw [capAt_of_view hvz]; exact this
  · obtain ⟨x2, hx2, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hx2
    exact tail [] x1.2 hI1 (fun p hp => absurd hp List.not_mem_nil) y hy

end

end Fl4Proofs.P3.SInvU
