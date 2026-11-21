/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut5): **`cap_move`,
`cap_swap` and `cap_swap_for_delete` keep `UtInv''`** (spec side only; imports
SpecInvUtN2).

* `PosOK w x`: the slot position `x` may hold a non-null cap (IfUnsafe: its
  object, if inside an untyped region, is referenced by a slot-holding cap;
  CnShape: `x` is in the slot range of every slot-holding cap to its object).
  Every non-null slot is one (`posOK_of_nn`), and so is every destination found
  by a lookup (`posOK_of_destRef`).
* `utN_ren`: the seven facts are invariant under renaming slots by an
  involution, as long as every non-null cap lands on a `PosOK` position.
* `RefEq c0 c` (what `update_cap_data` / `mask_cap` give in place, CNode
  Mutate/Rotate): `c = c0`, or neither is a Zombie or untyped and both have the
  same `objRefs` and shape. `utN_vCapEq`.
* Exact views: `capMove_view`, `capSwap_view` (SpecInvUtMv's computations).
* **`hv_capMoveN`**, **`hv_capSwapN`**, **`hv_capSwapForDeleteN`**, and
  `posOK_move` (Rotate's second move).
-/
import Fl4Proofs.P3.SpecInvUtN2
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Positions -/

/-- The slot `x` may hold a non-null cap. -/
def PosOK (w : UView) (x : CslotPtr) : Prop :=
  (InUtV w x.1 → ∃ s c', w.2.1 s = some c' ∧ x.1 ∈ sRefs c') ∧
    ∀ s c', w.2.1 s = some c' → x.1 ∈ sRefs c' → SlotShape c' x.2

theorem posOK_of_nn {w : UView} (hN : UtNV w) {x : CslotPtr} {c : Cap} (hx : w.2.1 x = some c)
    (hc : c ≠ .nullCap) : PosOK w x :=
  ⟨fun hin => hN.2.1 x c hx hc hin, fun s c' hs hr => hN.2.2.2.2.1 s c' x.1 hs hr x.2 c hx hc⟩

theorem posOK_of_destRef {w : UView} (hN : UtNV w) {x : CslotPtr} (hD : DestRefV w x) : PosOK w x := by
  obtain ⟨-, -, -, hK, -, hZ, -⟩ := hN
  obtain ⟨s1, c1, hs1, hr1, hz1, hsh1⟩ := hD
  refine ⟨fun _ => ⟨s1, c1, hs1, hr1⟩, fun s c' hs hr => ?_⟩
  have hzc : ∀ a b n, c' ≠ .zombie a b n := by
    intro a b n e
    subst e
    have ha : x.1 = a := by simpa [sRefs] using hr
    by_cases es : s1 = s
    · subst es; rw [hs] at hs1; cases hs1; exact hz1 a b n rfl
    · rw [← ha] at hs; exact hZ s x.1 b n hs s1 c1 es hs1 (sRefs_sub c1 hr1)
  have h0 : shp c1 = shp c' := hK s1 c1 s c' x.1 hs1 hs (sRefs_sub_capRng c1 hr1) hr
  exact slotShape_shp h0 hz1 hzc hsh1 (shp_of_sRefs hr1)

/-! ## Renaming -/

theorem utN_ren {π : CslotPtr → CslotPtr} (hπ : ∀ x, π (π x) = x) {w : UView} (hN : UtNV w)
    (hP : ∀ x c, w.2.1 (π x) = some c → c ≠ .nullCap → PosOK w x) : UtNV (vRen π w) := by
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  have hinj : ∀ x y, π x = π y → x = y := fun x y h => by rw [← hπ x, h, hπ]
  have hin : ∀ q, InUtV (vRen π w) q → InUtV w q := fun q ⟨u, d, b, n, f, hu, hr⟩ =>
    ⟨π u, d, b, n, f, hu, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u d b n f hu s c r hs hr hrd
    exact (ren_tg hπ).2 (hC (π u) d b n f hu (π s) c r hs hr hrd)
  · intro p c hp hne hq
    obtain ⟨s, c', hs, hr⟩ := (hP p c hp hne).1 (hin _ hq)
    exact ⟨π s, c', by show w.2.1 (π (π s)) = _; rw [hπ]; exact hs, hr⟩
  · intro u d b n f hu s c r hs hr
    exact hF (π u) d b n f hu (π s) c r hs hr
  · intro s c s' c' r hs hs' hr hr'
    exact hK _ _ _ _ r hs hs' hr hr'
  · intro s c r hs hr i c' hi hne
    exact (hP (r, i) c' hi hne).2 (π s) c hs hr
  · intro s r b n hs s' c' hne hs'
    exact hZ (π s) r b n hs (π s') c' (fun e => hne (hinj _ _ e)) hs'
  · intro s c hs
    exact hB (π s) c hs

/-! ## Cutting a null childless slot, original flags -/

theorem utN_cut {w : UView} (hN : UtNV w) {s : CslotPtr} (hk : ∀ x, w.2.2.1 x ≠ some s)
    (hs : w.2.1 s = some .nullCap) : UtNV (vCdt (Function.update w.2.2.1 s none) w) := by
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  have hv : (none : Option CslotPtr) ≠ some s := fun e => by cases e
  refine ⟨fun u d b n f hu s' c r hs' hr hrd => ?_, hU, hF, hK, hS, hZ, hB⟩
  have hs's : s' ≠ s := fun e => by
    have h' : w.2.1 s' = some c := hs'
    subst e; rw [hs] at h'; cases h'; exact capRng_nn hr rfl
  exact (lu_tg hk hv hs's).2 (hC u d b n f hu s' c r hs' hr hrd)

theorem utN_vOrig {w : UView} (h : UtNV w) (s : CslotPtr) (v : Bool) : UtNV (vOrig s v w) := h

/-! ## Replacing a cap by one with the same references -/

/-- What `update_cap_data` / `mask_cap` give in place. -/
def RefEq (c0 c : Cap) : Prop :=
  c = c0 ∨ (c0 ≠ .nullCap ∧ objRefs c = objRefs c0 ∧ shp c = shp c0 ∧ (∀ r b n, c ≠ .zombie r b n) ∧
    (∀ r b n, c0 ≠ .zombie r b n) ∧ (∀ d b n f, c ≠ .untypedCap d b n f) ∧ (∀ d b n f, c0 ≠ .untypedCap d b n f) ∧
    capRng c = capRng c0)

theorem sRefs_eq {c0 c : Cap} (ho : objRefs c = objRefs c0) (hs : shp c = shp c0) : sRefs c = sRefs c0 := by
  ext r; constructor
  · intro h
    obtain ⟨x, hx⟩ := shp_of_sRefs h
    exact sRefs_of_shp (by rw [← ho]; exact sRefs_sub c h) (by rw [← hs]; exact hx)
  · intro h
    obtain ⟨x, hx⟩ := shp_of_sRefs h
    exact sRefs_of_shp (by rw [ho]; exact sRefs_sub c0 h) (by rw [hs]; exact hx)

theorem slotShape_iff {a b : Cap} (h : shp a = shp b) (ha : ∀ r x n, a ≠ .zombie r x n)
    (hb : ∀ r x n, b ≠ .zombie r x n) (i : CnodeIndex) : SlotShape a i ↔ SlotShape b i := by
  cases a <;> cases b <;> simp_all [shp, SlotShape]

theorem RefEq.sRefs' {c0 c : Cap} (h : RefEq c0 c) : sRefs c = sRefs c0 := by
  rcases h with rfl | ⟨-, ho, hs, -⟩
  · rfl
  · exact sRefs_eq ho hs

theorem RefEq.objRefs' {c0 c : Cap} (h : RefEq c0 c) : objRefs c = objRefs c0 := by
  rcases h with rfl | ⟨-, ho, -⟩
  · rfl
  · exact ho

theorem RefEq.shp' {c0 c : Cap} (h : RefEq c0 c) : shp c = shp c0 := by
  rcases h with rfl | ⟨-, -, hs, -⟩
  · rfl
  · exact hs

theorem RefEq.shape {c0 c : Cap} (h : RefEq c0 c) (i : CnodeIndex) : SlotShape c i ↔ SlotShape c0 i := by
  rcases h with rfl | ⟨-, -, hs, hz, hz0, -⟩
  · exact Iff.rfl
  · exact slotShape_iff hs hz hz0 i

theorem RefEq.ut {c0 c : Cap} (h : RefEq c0 c) {d : Bool} {b : ObjRef} {n f : Nat}
    (hc : c = .untypedCap d b n f) : c0 = c := by
  rcases h with rfl | ⟨-, -, -, -, -, hu, -⟩
  · rfl
  · exact absurd hc (hu d b n f)

theorem RefEq.zb {c0 c : Cap} (h : RefEq c0 c) {r : ObjRef} {b : Option Nat} {n : Nat}
    (hc : c = .zombie r b n) : c0 = c := by
  rcases h with rfl | ⟨-, -, -, hz, -⟩
  · rfl
  · exact absurd hc (hz r b n)

theorem RefEq.nn {c0 c : Cap} (h : RefEq c0 c) (hc : c ≠ .nullCap) : c0 ≠ .nullCap := by
  rcases h with rfl | ⟨h0, -⟩
  · exact hc
  · exact h0

theorem utN_vCapEq {w : UView} (hN : UtNV w) {sl : CslotPtr} {c0 c : Cap} (h0 : w.2.1 sl = some c0)
    (hR : RefEq c0 c) : UtNV (vCap sl c w) := by
  rcases hR with rfl | hR'
  · rw [vCap_same h0]; exact hN
  have hR : RefEq c0 c := Or.inr hR'
  obtain ⟨hn0, ho, hsh, hz, hz0, hu, hu0, hcr⟩ := hR'
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  have hsr := sRefs_eq ho hsh
  have hcap : ∀ x y, (vCap sl c w).2.1 x = some y → (x = sl ∧ y = c) ∨ (x ≠ sl ∧ w.2.1 x = some y) :=
    fun x y h => upd_cap h
  have hold : ∀ x, x ≠ sl → (vCap sl c w).2.1 x = w.2.1 x := fun x e => Function.update_of_ne e _ _
  have hut : ∀ u d b n f, (vCap sl c w).2.1 u = some (.untypedCap d b n f) →
      w.2.1 u = some (.untypedCap d b n f) := by
    intro u d b n f h
    rcases hcap u _ h with ⟨-, e⟩ | ⟨-, h'⟩
    · exact absurd e.symm (hu d b n f)
    · exact h'
  have hin : ∀ q, InUtV (vCap sl c w) q → InUtV w q := fun q ⟨u, d, b, n, f, hu', hr⟩ =>
    ⟨u, d, b, n, f, hut _ _ _ _ _ hu', hr⟩
  have hpb : ∀ x y, (vCap sl c w).2.1 x = some y → ∃ y0, w.2.1 x = some y0 ∧ (objRefs y = objRefs y0 ∧ capRng y = capRng y0) ∧
      shp y = shp y0 ∧ sRefs y = sRefs y0 ∧ (y ≠ .nullCap → y0 ≠ .nullCap) ∧
      (∀ i, SlotShape y i ↔ SlotShape y0 i) ∧ ((∃ r b n, y = .zombie r b n) → y = y0) := by
    intro x y h
    rcases hcap x y h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · exact ⟨c0, h0, ⟨ho, hcr⟩, hsh, hsr, fun _ => hn0, hR.shape, fun ⟨r, b, n, e⟩ => absurd e (hz r b n)⟩
    · exact ⟨y, h', ⟨rfl, rfl⟩, rfl, rfl, id, fun _ => Iff.rfl, fun _ => rfl⟩
  have hpf : ∀ x y0, w.2.1 x = some y0 → ∃ y, (vCap sl c w).2.1 x = some y ∧ sRefs y = sRefs y0 := by
    intro x y0 h
    by_cases e : x = sl
    · subst e; rw [h0] at h; cases h
      exact ⟨c, by simp [vCap], hsr⟩
    · exact ⟨y0, by rw [hold x e]; exact h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u d b n f hu' s y r hs hr hrd
    obtain ⟨y0, hs0, hoy, -⟩ := hpb s y hs
    exact hC u d b n f (hut _ _ _ _ _ hu') s y0 r hs0 (by rw [← hoy.2]; exact hr) hrd
  · intro p y hp hne hq
    obtain ⟨y0, hp0, -, -, -, hnn, -⟩ := hpb p y hp
    obtain ⟨s, c', hs, hr⟩ := hU p y0 hp0 (hnn hne) (hin _ hq)
    obtain ⟨y', hs', hsr'⟩ := hpf s c' hs
    exact ⟨s, y', hs', by rw [hsr']; exact hr⟩
  · intro u d b n f hu' s y r hs hr
    obtain ⟨y0, hs0, hoy, -⟩ := hpb s y hs
    exact hF u d b n f (hut _ _ _ _ _ hu') s y0 r hs0 (by rw [← hoy.2]; exact hr)
  · intro sa ya sb yb r ha hb hra hrb
    obtain ⟨a0, ha0, hoa, hsa, -⟩ := hpb sa ya ha
    obtain ⟨b0, hb0, -, hsb, hsrb, -⟩ := hpb sb yb hb
    rw [hsa, hsb]
    exact hK sa a0 sb b0 r ha0 hb0 (by rw [← hoa.2]; exact hra) (by rw [← hsrb]; exact hrb)
  · intro sa ya r ha hr i y hi hne
    obtain ⟨a0, ha0, -, -, hsra, -, hsha, -⟩ := hpb sa ya ha
    obtain ⟨y0, hi0, -, -, -, hnn, -⟩ := hpb (r, i) y hi
    exact (hsha i).2 (hS sa a0 r ha0 (by rw [← hsra]; exact hr) i y0 hi0 (hnn hne))
  · intro s r b n hs s' y hne hs'
    obtain ⟨z0, hz0, -, -, -, -, -, hzz⟩ := hpb s _ hs
    have e := hzz ⟨r, b, n, rfl⟩
    rw [← e] at hz0
    obtain ⟨y0, hy0, hoy, -⟩ := hpb s' y hs'
    rw [hoy.1]; exact hZ s r b n hz0 s' y0 hne hy0
  · intro s y hs bb hbb
    obtain ⟨y0, hy0, -, hsy, -⟩ := hpb s y hs
    exact hB s y0 hy0 bb (by rw [← hsy]; exact hbb)

/-! ## Exact views of `cap_move` and `cap_swap` -/

/-- The view after `cap_move c src dest` (SpecInvUtMv's computation). -/
def mvV (src dest : CslotPtr) (c : Cap) (w : UView) : UView :=
  vOrig src false (vCdt (Function.update (vCap dest c (vRen (sw src dest) w)).2.2.1 src none)
    (vCap dest c (vRen (sw src dest) w)))

theorem capMove_view {w : UView} {c : Cap} {src dest : CslotPtr} (hne : src ≠ dest)
    (hd : w.2.1 dest = some .nullCap) (hss : w.2.2.1 src ≠ some src) (hsd : w.2.2.1 src ≠ some dest)
    (hkd : ∀ x, w.2.2.1 x ≠ some dest) :
    HV (· = w) (· = mvV src dest c w) (capMove (Z := Unit) c src dest) := by
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
  unfold mvV vOrig vCdt vCap
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

theorem capSwap_view {w : UView} {s1 s2 : CslotPtr} (hne : s1 ≠ s2) (c1 c2 : Cap) :
    HV (· = w) (· = vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) w))) (capSwap (Z := Unit) c1 s1 c2 s2) := by
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
      vOrig s2 (w.2.2.2 s1) (vOrig s1 (w.2.2.2 s2) (vCdt T (vCap s2 c1 (vCap s1 c2 w)))) =
        vCap s2 c1 (vCap s1 c2 (vRen (sw s1 s2) w)) by
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

/-! ## The writers -/

theorem utN_mvV {w : UView} (hI : UtInv'V w) (hN : UtNV w) {c0 c : Cap} {src dest : CslotPtr}
    (hs : w.2.1 src = some c0) (hd : w.2.1 dest = some .nullCap) (hre : RefEq c0 c) (hpd : PosOK w dest)
    (hne : src ≠ dest) : UtNV (mvV src dest c w) := by
  obtain ⟨-, hO, -⟩ := hI
  have hds : dest ≠ src := Ne.symm hne
  have sw1 : sw src dest src = dest := by simp [sw]
  have sw2 : sw src dest dest = src := by simp [sw, hds]
  have swx : ∀ x, x ≠ src → x ≠ dest → sw src dest x = x := fun x h1 h2 => by simp [sw, h1, h2]
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hN2 : UtNV (vRen (sw src dest) w) := by
    refine utN_ren (sw_sw src dest) hN fun x c' hx hc' => ?_
    by_cases e1 : x = src
    · subst e1; rw [sw1, hd] at hx; cases hx; exact absurd rfl hc'
    · by_cases e2 : x = dest
      · subst e2; exact hpd
      · rw [swx x e1 e2] at hx; exact posOK_of_nn hN hx hc'
  have hd2 : (vRen (sw src dest) w).2.1 dest = some c0 := by
    show w.2.1 (sw src dest dest) = _; rw [sw2, hs]
  have hN3 := utN_vCapEq hN2 hd2 hre
  have hsrc3 : (vCap dest c (vRen (sw src dest) w)).2.1 src = some .nullCap := by
    show Function.update (fun x => w.2.1 (sw src dest x)) dest (some c) src = _
    rw [Function.update_of_ne hne, sw1, hd]
  have hk3 : ∀ x, (vCap dest c (vRen (sw src dest) w)).2.2.1 x ≠ some src := by
    intro x hx
    have hx' : (w.2.2.1 (sw src dest x)).map (sw src dest) = some src := hx
    cases e : w.2.2.1 (sw src dest x) with
    | none => rw [e] at hx'; cases hx'
    | some p =>
      rw [e] at hx'
      simp only [Option.map_some, Option.some.injEq] at hx'
      have : p = dest := by rw [← sw_sw src dest p, hx', sw1]
      subst this; exact hkd _ e
  exact utN_vOrig (utN_cut hN3 hk3 hsrc3) _ _

/-- **`cap_move` of a `RefEq` cap to a null `PosOK` slot keeps `UtInv''`**; afterwards
the source is null and every other slot but the destination is unchanged. -/
theorem hv_capMoveN {w : UView} (hI : UtInv''V w) {c0 c : Cap} {src dest : CslotPtr}
    (hs : w.2.1 src = some c0) (hd : w.2.1 dest = some .nullCap) (hr : CapRel c0 c) (hre : RefEq c0 c)
    (hpd : PosOK w dest) (hne : src ≠ dest) :
    HV (· = w) (fun w' => UtInv''V w' ∧ w'.2.1 src = some .nullCap ∧ w'.2.1 dest = some c ∧
      ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (capMove (Z := Unit) c src dest) := by
  intro σ hσ y hy
  obtain ⟨hI1, h1, h2, h3⟩ := hv_capMove hI.1 hs hd hr hne σ hσ y hy
  obtain ⟨-, hO, hA⟩ := hI.1
  have hkd : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hss : w.2.2.1 src ≠ some src := fun h => hA src (Relation.TransGen.single h)
  have hv := capMove_view (c := c) hne hd hss (hkd src) hkd σ hσ y hy
  refine ⟨⟨hI1, ?_⟩, h1, h2, h3⟩
  rw [hv]; exact utN_mvV hI.1 hI.2 hs hd hre hpd hne

/-- After `cap_move`, a position that was `PosOK` still is (Rotate's second move). -/
theorem posOK_move {w w' : UView} {c0 c : Cap} {src dest : CslotPtr} (hs : w.2.1 src = some c0)
    (hre : RefEq c0 c) (h1 : w'.2.1 src = some .nullCap) (h2 : w'.2.1 dest = some c)
    (h3 : ∀ x, x ≠ src → x ≠ dest → w'.2.1 x = w.2.1 x) (hd : w.2.1 dest = some .nullCap)
    {x : CslotPtr} (h : PosOK w x) : PosOK w' x := by
  have hcap : ∀ s y, w'.2.1 s = some y → (s = src ∧ y = .nullCap) ∨ (s = dest ∧ y = c) ∨ w.2.1 s = some y := by
    intro s y hy
    by_cases e1 : s = src
    · subst e1; rw [h1] at hy; cases hy; exact Or.inl ⟨rfl, rfl⟩
    · by_cases e2 : s = dest
      · subst e2; rw [h2] at hy; cases hy; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rw [h3 s e1 e2] at hy; exact Or.inr (Or.inr hy)
  refine ⟨fun hin => ?_, fun s y hy hr => ?_⟩
  · obtain ⟨u, d, b, n, f, hu, hr⟩ := hin
    have hin' : InUtV w x.1 := by
      rcases hcap u _ hu with ⟨-, e⟩ | ⟨-, e⟩ | hu'
      · cases e
      · exact ⟨src, d, b, n, f, by rw [hs, hre.ut e.symm, ← e], hr⟩
      · exact ⟨u, d, b, n, f, hu', hr⟩
    obtain ⟨s0, c', hs0, hr0⟩ := h.1 hin'
    by_cases e1 : s0 = src
    · subst e1; rw [hs] at hs0; cases hs0
      exact ⟨dest, c, h2, by rw [hre.sRefs']; exact hr0⟩
    · by_cases e2 : s0 = dest
      · subst e2; rw [hd] at hs0; cases hs0; simp [sRefs] at hr0
      · exact ⟨s0, c', by rw [h3 s0 e1 e2]; exact hs0, hr0⟩
  · rcases hcap s y hy with ⟨-, rfl⟩ | ⟨-, rfl⟩ | hy'
    · simp [sRefs] at hr
    · exact (hre.shape x.2).2 (h.2 src c0 hs (by rw [← hre.sRefs']; exact hr))
    · exact h.2 s y hy' hr

/-- **`cap_swap` of `RefEq` caps keeps `UtInv''`.** -/
theorem hv_capSwapN {s1 s2 : CslotPtr} (hne : s1 ≠ s2) {c1' c2' c1 c2 : Cap} (h1r : CapRel c1' c1)
    (h2r : CapRel c2' c2) (h1e : RefEq c1' c1) (h2e : RefEq c2' c2) :
    HV (fun w => UtInv''V w ∧ w.2.1 s1 = some c1' ∧ w.2.1 s2 = some c2') UtInv''V
      (capSwap (Z := Unit) c1 s1 c2 s2) := by
  refine hv_pin fun w ⟨hI, h1, h2⟩ => ?_
  intro σ hσ y hy
  have hU := hv_capSwap hne h1r h2r σ (by rw [hσ]; exact ⟨hI.1, h1, h2⟩) y hy
  have hv := capSwap_view (w := w) hne c1 c2 σ hσ y hy
  refine ⟨hU, ?_⟩
  rw [hv]
  have hs21 : s2 ≠ s1 := Ne.symm hne
  have sw1 : sw s1 s2 s1 = s2 := by simp [sw]
  have sw2 : sw s1 s2 s2 = s1 := by simp [sw, hs21]
  have swx : ∀ x, x ≠ s1 → x ≠ s2 → sw s1 s2 x = x := fun x h1 h2 => by simp [sw, h1, h2]
  have hN2 : UtNV (vRen (sw s1 s2) w) := by
    refine utN_ren (sw_sw s1 s2) hI.2 fun x c' hx hc' => ?_
    by_cases e1 : x = s1
    · subst e1; exact posOK_of_nn hI.2 h1 h1r.1
    · by_cases e2 : x = s2
      · subst e2; exact posOK_of_nn hI.2 h2 h2r.1
      · rw [swx x e1 e2] at hx; exact posOK_of_nn hI.2 hx hc'
  have hR1 : (vRen (sw s1 s2) w).2.1 s1 = some c2' := by show w.2.1 (sw s1 s2 s1) = _; rw [sw1, h2]
  have hR2 : (vCap s1 c2 (vRen (sw s1 s2) w)).2.1 s2 = some c1' := by
    rw [vCap_cap, if_neg hs21]; show w.2.1 (sw s1 s2 s2) = _; rw [sw2, h1]
  exact utN_vCapEq (utN_vCapEq hN2 hR1 h2e) hR2 h1e

/-- **`cap_swap_for_delete` keeps `UtInv''`** when each non-null cap lands on a
`PosOK` position. -/
theorem hv_capSwapForDeleteN (s1 s2 : CslotPtr) :
    HV (fun w => UtInv''V w ∧ ∀ c1 c2, w.2.1 s1 = some c1 → w.2.1 s2 = some c2 →
      (c1 ≠ .nullCap → PosOK w s2) ∧ (c2 ≠ .nullCap → PosOK w s1)) UtInv''V
      (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete
  unfold NonDet.when
  split
  · rename_i hne
    refine hv_getCap_bind fun w c1 hw h1 => ?_
    refine hv_getCap_bind fun w' c2 hw' h2 => ?_
    subst w'
    intro σ hσ y hy
    have hU := hv_capSwap_same hne c1 c2 σ (by rw [hσ]; exact ⟨hw.1.1, h1, h2⟩) y hy
    have hv := capSwap_view (w := w) hne c1 c2 σ hσ y hy
    refine ⟨hU, ?_⟩
    rw [hv]
    obtain ⟨hp1, hp2⟩ := hw.2 c1 c2 h1 h2
    have hs21 : s2 ≠ s1 := Ne.symm hne
    have sw1 : sw s1 s2 s1 = s2 := by simp [sw]
    have sw2 : sw s1 s2 s2 = s1 := by simp [sw, hs21]
    have swx : ∀ x, x ≠ s1 → x ≠ s2 → sw s1 s2 x = x := fun x h1 h2 => by simp [sw, h1, h2]
    have hN2 : UtNV (vRen (sw s1 s2) w) := by
      refine utN_ren (sw_sw s1 s2) hw.1.2 fun x c' hx hc' => ?_
      by_cases e1 : x = s1
      · subst e1; rw [sw1, h2] at hx; cases hx; exact hp2 hc'
      · by_cases e2 : x = s2
        · subst e2; rw [sw2, h1] at hx; cases hx; exact hp1 hc'
        · rw [swx x e1 e2] at hx; exact posOK_of_nn hw.1.2 hx hc'
    have hR1 : (vRen (sw s1 s2) w).2.1 s1 = some c2 := by show w.2.1 (sw s1 s2 s1) = _; rw [sw1, h2]
    have hR2 : (vCap s1 c2 (vRen (sw s1 s2) w)).2.1 s2 = some c1 := by
      rw [vCap_cap, if_neg hs21]; show w.2.1 (sw s1 s2 s2) = _; rw [sw2, h1]
    exact utN_vCapEq (utN_vCapEq hN2 hR1 (Or.inl rfl)) hR2 (Or.inl rfl)
  · exact hv_mono (hv_uk fun _ => ik_pure' _) fun w h => h.1

end

end Fl4Proofs.P3.SInvU
