/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut5): **the pieces of
`rec_del` for `UtInv''`** (spec side only; imports SpecInvUtN3).

* Slot indices: `natToCref_zero` (index 0 of a radix-`L` object is `L` zero
  bits), `natToCref_of_len` (every bit list of length `L ≤ 64` is a
  `natToCref L k`, `k < 2^L`), `tcb_natToCref` (a TCB's slots are a 3-bit
  Zombie's).
* Finality (`is_final_cap'`): `final_unique` (a final cap's object is
  referenced from no other slot), `nonfinal_other` (a non-final CNode / thread
  / Zombie cap's object is referenced from another slot).
* `utN_vCapGen`: replacing a cap by one with the same references and shape, the
  slot range only growing where slots are non-null, a Zombie only if it is the
  sole reference; `utN_zombieW` (the Zombie `finalise_cap` makes of a final
  CNode / thread cap).
* `emptySlot_view`, `capDeleteOne_keep` (the other slots keep their caps),
  `capDeleteOne_irq` (no outcome on a slot holding an IRQ handler cap).
* **`fin_step`**: what `finalise_cap cap (is_final cap)` gives `rec_del`: `UtInv''`
  kept, the slot still holds `cap`, a removeable remainder makes the slot's
  removal safe (`SafeDelV`), a non-removeable one can be written back.
* `posOK_firstSlot` (a Zombie may move to its first slot).
-/
import Fl4Proofs.P3.SpecInvUtN3
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Slot index arithmetic -/

/-- The low `n` bits of `x`, most significant first. -/
def ubits (x : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => x.testBit n :: ubits x n

theorem ubits_succ (x n : Nat) : ubits x (n + 1) = x.testBit n :: ubits x n := rfl

theorem ubits_length (x n : Nat) : (ubits x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ubits_succ, ih]

theorem getElem_ubits (x n i : Nat) (h : i < (ubits x n).length) :
    (ubits x n)[i] = x.testBit (n - 1 - i) := by
  induction n generalizing i with
  | zero => simp [ubits_length] at h
  | succ n ih =>
    cases i with
    | zero => simp [ubits_succ]
    | succ i =>
      simp only [ubits_succ, List.getElem_cons_succ]
      rw [ih]; congr 1; omega

theorem ubits_drop (x : Nat) {k n : Nat} (hk : k ≤ n) : (ubits x n).drop k = ubits x (n - k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [ubits_succ, List.drop_succ_cons]
    rw [ih (by omega)]
    congr 1; omega

theorem ubits_eq_of_mod {x y n : Nat} (h : x % 2 ^ n = y % 2 ^ n) : ubits x n = ubits y n := by
  apply List.ext_getElem
  · simp [ubits_length]
  · intro i h1 h2
    simp only [getElem_ubits]
    have := congrArg (fun z => z.testBit (n - 1 - i)) h
    simp only [Nat.testBit_mod_two_pow] at this
    simp [ubits_length] at h1
    have hlt : n - 1 - i < n := by omega
    simpa [hlt] using this

theorem toBl_ubits (x : BitVec 64) : toBl x = ubits x.toNat 64 := by
  apply List.ext_getElem
  · simp [toBl, ubits_length]
  · intro i h1 h2
    simp only [toBl, List.getElem_map, List.getElem_reverse, List.getElem_range, getElem_ubits,
      BitVec.getLsbD, List.length_range]

theorem natToCref_ubits (L k : Nat) (hL : L ≤ 64) : natToCref L k = ubits (k % 2 ^ 64) L := by
  unfold natToCref
  rw [show wordBits = 64 from rfl, toBl_ubits, ubits_drop _ (by omega), BitVec.toNat_ofNat]
  congr 1; omega

theorem ubits_zero_val (n : Nat) : ubits 0 n = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ubits_succ, ih, Nat.zero_testBit]; rfl

theorem natToCref_zero (L : Nat) (hL : L ≤ 64) : natToCref L 0 = List.replicate L false := by
  rw [natToCref_ubits L 0 hL, Nat.zero_mod, ubits_zero_val]

/-- The value of a bit list, most significant first. -/
def bval : List Bool → Nat
  | [] => 0
  | b :: t => (if b then 2 ^ t.length else 0) + bval t

theorem bval_lt : ∀ l : List Bool, bval l < 2 ^ l.length
  | [] => by simp [bval]
  | b :: t => by
    have := bval_lt t
    simp only [bval, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem ubits_bval : ∀ l : List Bool, ubits (bval l) l.length = l
  | [] => rfl
  | b :: t => by
    have ht := bval_lt t
    rw [List.length_cons, ubits_succ]
    cases b
    · show (0 + bval t).testBit t.length :: ubits (0 + bval t) t.length = false :: t
      rw [Nat.zero_add, Nat.testBit_lt_two_pow ht, ubits_bval t]
    · show (2 ^ t.length + bval t).testBit t.length :: ubits (2 ^ t.length + bval t) t.length = true :: t
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ht, Bool.not_false,
        ubits_eq_of_mod (y := bval t) (Nat.add_mod_left _ _), ubits_bval t]

theorem natToCref_of_len (i : List Bool) (hL : i.length ≤ 64) :
    ∃ k, k < 2 ^ i.length ∧ i = natToCref i.length k := by
  refine ⟨bval i, bval_lt i, ?_⟩
  have h2 : 2 ^ i.length ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hL
  rw [natToCref_ubits _ _ hL, Nat.mod_eq_of_lt (lt_of_lt_of_le (bval_lt i) h2), ubits_bval]

theorem tcb_natToCref {k : Nat} (hk : k < 6) : tcbCnodeIndex k = natToCref 3 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | rfl

theorem zcb_le {w : UView} (hB : CnBitsV w) {s : CslotPtr} {r : ObjRef} {b : Option Nat} {n : Nat}
    (h : w.2.1 s = some (.zombie r b n)) : zombieCteBits b ≤ 64 := by
  cases b with
  | none => decide
  | some b => exact hB s _ h b rfl

/-! ## Finality -/

theorem getCap_set_capAt (σ : State Unit) (sl : CslotPtr) (a : Cap) :
    (getCap (Z := Unit) sl σ).1 = {(a, σ)} ↔ capAt σ sl = some a := by
  have ndb : ∀ {α β : Type} (m : NonDet (State Unit) α) (f : α → NonDet (State Unit) β) (s : State Unit),
      (m >>= f) s = ({r | ∃ x ∈ (m s).1, r ∈ (f x.1 x.2).1}, (m s).2 ∨ ∃ x ∈ (m s).1, (f x.1 x.2).2) :=
    fun _ _ _ => rfl
  have ndp : ∀ {α : Type} (x : α) (s : State Unit), (pure x : NonDet (State Unit) α) s = ({(x, s)}, False) :=
    fun _ _ => rfl
  obtain ⟨o, c⟩ := sl
  unfold getCap getObject capAt
  cases h : σ.kheap o with
  | none =>
    simp [ndb, ndp, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail]
  | some obj =>
    cases obj with
    | cnode sz cs =>
      by_cases hwf : wellFormedCnodeN sz cs <;> cases hc : cs c <;>
        simp [ndb, ndp, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail, capView, NonDet.pure,
          NonDet.assert, hwf, hc]
    | tcb t =>
      cases hc : tcbCnodeMap t c <;>
        simp [ndb, ndp, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail, capView, NonDet.pure, hc]
    | _ => simp [ndb, ndp, NonDet.getsThe, readObject, h, NonDet.assertOpt, NonDet.fail, capView, NonDet.pure]

theorem objRef_mem_gen {c : Cap} {r : ObjRef} (h : GenObjRef.objRef r ∈ genObjRefs c) : r ∈ objRefs c := by
  rcases h with (⟨x, hx, e⟩ | ⟨x, -, e⟩) | ⟨x, -, e⟩
  · cases e; exact hx
  · cases e
  · cases e

theorem genObjRefs_sh {c : Cap} {r : ObjRef} (h : r ∈ sRefs c) : genObjRefs c = {GenObjRef.objRef r} := by
  cases c <;> simp_all [sRefs, genObjRefs, objRefs, capIrqs, capIrqOpt, archCapSetMap]

theorem final_unique {σ : State Unit} {c : Cap} {sl : CslotPtr} (hf : isFinalCap' (Z := Unit) c σ)
    (hs : capAt σ sl = some c) {r : ObjRef} (hr : r ∈ objRefs c) :
    ∀ s' c', capAt σ s' = some c' → r ∈ objRefs c' → s' = sl := by
  obtain ⟨c0, hc0⟩ := hf
  have h1 : GenObjRef.objRef r ∈ genObjRefs c := Or.inl (Or.inl ⟨r, hr, rfl⟩)
  have mem : ∀ s' c', capAt σ s' = some c' → r ∈ objRefs c' →
      s' ∈ {cref | ∃ cap', ((getCap cref : SMonad Unit Cap) σ).1 = {(cap', σ)} ∧
        genObjRefs c ∩ genObjRefs cap' ≠ ∅} := by
    intro s' c' h hr'
    refine ⟨c', (getCap_set_capAt σ s' c').2 h, fun e => ?_⟩
    have : GenObjRef.objRef r ∈ genObjRefs c ∩ genObjRefs c' := ⟨h1, Or.inl (Or.inl ⟨r, hr', rfl⟩)⟩
    rw [e] at this; exact this
  intro s' c' h hr'
  have m1 := mem s' c' h hr'
  have m2 := mem sl c hs hr
  rw [hc0] at m1 m2
  rw [Set.mem_singleton_iff.1 m1]
  exact (Set.mem_singleton_iff.1 m2).symm

theorem nonfinal_other {σ : State Unit} {c : Cap} {sl : CslotPtr} (hnf : ¬ isFinalCap' (Z := Unit) c σ)
    (hs : capAt σ sl = some c) {r : ObjRef} (hr : r ∈ sRefs c) :
    ∃ s' c', s' ≠ sl ∧ capAt σ s' = some c' ∧ r ∈ objRefs c' := by
  have hg := genObjRefs_sh hr
  by_contra hno
  apply hnf
  refine ⟨sl, Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨c', hc', hov⟩ := hx
    have hcx : capAt σ x = some c' :=
      (getCap_capAt (x := (c', σ)) (by rw [hc']; exact Set.mem_singleton _)).2
    rw [Set.mem_singleton_iff]
    by_contra hne
    apply hov
    rw [hg]
    ext g
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl hg'
    exact hno ⟨x, c', hne, hcx, objRef_mem_gen hg'⟩
  · rw [Set.mem_singleton_iff.1 hx]
    refine ⟨c, (getCap_set_capAt σ sl c).2 hs, ?_⟩
    intro e
    have : GenObjRef.objRef r ∈ genObjRefs c ∩ genObjRefs c := by rw [hg]; exact ⟨rfl, rfl⟩
    rw [e] at this; exact this

/-! ## Replacing a cap: the general form -/

theorem utN_vCapGen {w : UView} (hN : UtNV w) {sl : CslotPtr} {c0 c : Cap} (h0 : w.2.1 sl = some c0)
    (hn0 : c0 ≠ .nullCap) (ho : objRefs c = objRefs c0) (hcr : capRng c = capRng c0) (hsh : shp c = shp c0)
    (hu : ∀ d b n f, c ≠ .untypedCap d b n f)
    (hss : ∀ r, r ∈ sRefs c → ∀ i c', w.2.1 (r, i) = some c' → c' ≠ .nullCap → SlotShape c0 i → SlotShape c i)
    (hz : ∀ r b n, c = .zombie r b n → ∀ s' c', s' ≠ sl → w.2.1 s' = some c' → r ∉ objRefs c') :
    UtNV (vCap sl c w) := by
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
      shp y = shp y0 ∧ sRefs y = sRefs y0 ∧ (y ≠ .nullCap → y0 ≠ .nullCap) := by
    intro x y h
    rcases hcap x y h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · exact ⟨c0, h0, ⟨ho, hcr⟩, hsh, hsr, fun _ => hn0⟩
    · exact ⟨y, h', ⟨rfl, rfl⟩, rfl, rfl, id⟩
  have hpf : ∀ x y0, w.2.1 x = some y0 → ∃ y, (vCap sl c w).2.1 x = some y ∧ sRefs y = sRefs y0 ∧
      objRefs y = objRefs y0 := by
    intro x y0 h
    by_cases e : x = sl
    · subst e; rw [h0] at h; cases h
      exact ⟨c, by simp [vCap], hsr, ho⟩
    · exact ⟨y0, by rw [hold x e]; exact h, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u d b n f hu' s y r hs hr hrd
    obtain ⟨y0, hs0, hoy, -⟩ := hpb s y hs
    exact hC u d b n f (hut _ _ _ _ _ hu') s y0 r hs0 (by rw [← hoy.2]; exact hr) hrd
  · intro p y hp hne hq
    obtain ⟨y0, hp0, -, -, -, hnn⟩ := hpb p y hp
    obtain ⟨s, c', hs, hr⟩ := hU p y0 hp0 (hnn hne) (hin _ hq)
    obtain ⟨y', hs', hsr', -⟩ := hpf s c' hs
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
    obtain ⟨y0, hi0, -, -, -, hnn⟩ := hpb (r, i) y hi
    rcases hcap sa ya ha with ⟨rfl, rfl⟩ | ⟨-, ha'⟩
    · have hr0 : r ∈ sRefs c0 := by rw [← hsr]; exact hr
      exact hss r hr i y0 hi0 (hnn hne) (hS sa c0 r h0 hr0 i y0 hi0 (hnn hne))
    · exact hS sa ya r ha' hr i y0 hi0 (hnn hne)
  · intro s r b n hs s' y hne hs'
    rcases hcap s _ hs with ⟨rfl, e⟩ | ⟨hsl, hs0⟩
    · have hs'' : w.2.1 s' = some y := by rw [← hold s' hne]; exact hs'
      exact hz r b n e.symm s' y hne hs''
    · obtain ⟨y0, hy0, hoy, -⟩ := hpb s' y hs'
      rw [hoy.1]; exact hZ s r b n hs0 s' y0 hne hy0
  · intro s y hs bb hbb
    obtain ⟨y0, hy0, -, hsy, -⟩ := hpb s y hs
    exact hB s y0 hy0 bb (by rw [← hsy]; exact hbb)

/-- **The Zombie of a final CNode / thread cap** may be written over it. -/
theorem utN_zombieW {w : UView} (hI : UtInv'V w) (hN : UtNV w) {s : CslotPtr} {c0 : Cap} {r : ObjRef}
    {b : Option Nat} {n : Nat} (h0 : w.2.1 s = some c0) (hr : objRefs c0 = {r}) (hsh : shp c0 = some b)
    (hss : ∀ i, SlotShape c0 i → SlotShape (.zombie r b n) i)
    (hfin : ∀ s' c', w.2.1 s' = some c' → r ∈ objRefs c' → s' = s) :
    UtInv''V (vCap s (.zombie r b n) w) := by
  have hn0 : c0 ≠ .nullCap := by intro e; subst e; simp [objRefs] at hr
  refine ⟨utInv'_vCap_nn hI ⟨fun e => (by cases e), fun _ _ _ _ e => (by cases e)⟩, ?_⟩
  refine utN_vCapGen hN h0 hn0 (by rw [hr]; rfl)
    (by rw [capRng_of_shp (c := Cap.zombie r b n) (x := b) rfl, capRng_of_shp hsh, hr]; rfl) (by rw [hsh]; rfl) (fun _ _ _ _ e => by cases e)
    (fun _ _ i _ _ _ h => hss i h) ?_
  intro r' b' n' e s' c' hne hs' hr'
  injection e with e1 e2 e3
  subst e1
  exact hne (hfin s' c' hs' hr')

/-! ## `empty_slot` / `cap_delete_one` views -/

theorem emptySlot_view (s : CslotPtr) (info : Cap) (w : UView) :
    HV (· = w) (fun w' => (w' = w ∧ w.2.1 s = some .nullCap) ∨ w' = vEs s w) (emptySlot (Z := Unit) s info) := by
  unfold emptySlot
  refine hv_getCap_bind fun w0 c hw hc => ?_
  subst hw
  split
  · rename_i h; subst h; exact hv_ret _ (Or.inl ⟨rfl, hc⟩)
  · refine hv_mono (Q := (· = vEs s w0)) ?_ (fun _ e => Or.inr e)
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

/-- `empty_slot` keeps `UtInv''` (when safe) and leaves the slot null. -/
theorem hv_emptySlotN0 (s : CslotPtr) (info : Cap) :
    HV (fun w => UtInv''V w ∧ ∀ c, w.2.1 s = some c → SafeDelV w s c)
      (fun w' => UtInv''V w' ∧ w'.2.1 s = some .nullCap) (emptySlot (Z := Unit) s info) := by
  refine hv_pin fun w hw => ?_
  intro σ hσ y hy
  refine ⟨hv_emptySlotN s info σ (by rw [hσ]; exact hw) y hy, ?_⟩
  rcases emptySlot_view s info w σ hσ y hy with ⟨e, h⟩ | e
  · rw [e]; exact h
  · rw [e]; unfold vEs; rw [vCap_cap, if_pos rfl] <;> rfl

theorem capDeleteOne_keep (isl x : CslotPtr) (hx : x ≠ isl) (w : UView) :
    HV (· = w) (fun w' => w'.2.1 x = w.2.1 x) (capDeleteOne (Z := Unit) isl) := by
  unfold capDeleteOne
  refine hv_getCap_bind fun w0 c hw hc => ?_
  subst hw
  unfold NonDet.unless
  split
  · exact hv_ret _ rfl
  · refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_isFinalCap c) fun fin => ?_
    refine hv_bind (R := (· = w0)) (hv_uk fun _ => uk_fastFinalise c fin) fun _ => ?_
    refine hv_mono (emptySlot_view isl .nullCap w0) fun w' h => ?_
    rcases h with ⟨rfl, -⟩ | rfl
    · rfl
    · unfold vEs; rw [vCap_cap, if_neg hx] <;> rfl

theorem capDeleteOne_irq {σ : State Unit} {isl : CslotPtr} {i : Irq} (h : capAt σ isl = some (.irqHandlerCap i)) :
    ∀ y, y ∉ (capDeleteOne (Z := Unit) isl σ).1 := by
  intro y hy
  unfold capDeleteOne at hy
  obtain ⟨⟨c, s⟩, hz, hy⟩ := hy
  obtain ⟨e, hc⟩ := getCap_capAt hz
  simp only at e hc; subst e
  rw [h] at hc; cases hc
  try unfold NonDet.unless at hy
  dsimp only at hy
  rw [if_neg (fun e => by cases e)] at hy
  obtain ⟨a, -, hy⟩ := hy
  obtain ⟨b, hb, -⟩ := hy
  have : (fastFinalise (Z := Unit) (.irqHandlerCap i) a.1 a.2).1 = ∅ := rfl
  rw [this] at hb; exact hb

/-! ## `finalise_cap` -/

macro "ov_auto2" : tactic => `(tactic| repeat' (first
  | (refine ov_bind fun _ => ?_) | (refine ov_bind' fun _ => ?_)
  | (refine ov_liftM fun _ => ?_)
  | exact ov_fail
  | (refine ov_pure ?_) | (refine ov_pure' ?_)
  | (refine ov_ite ?_ ?_)
  | rfl
  | split))

theorem finaliseCap_null {c : Cap} (hs : sRefs c = ∅) (fin : Bool) :
    OV (fun p : Cap × Cap => p.1 = .nullCap) (finaliseCap (Z := Unit) c fin) := by
  cases c <;> simp only [finaliseCap, archFinaliseCap] <;>
    (try exact absurd hs (Set.singleton_ne_empty _)) <;> ov_auto2

theorem finaliseCap_thread_val (r : ObjRef) (fin : Bool) :
    OV (fun p : Cap × Cap => p.1 = if fin then .zombie r none 6 else .nullCap)
      (finaliseCap (Z := Unit) (.threadCap r) fin) := by
  simp only [finaliseCap]; ov_auto2

theorem uk_finaliseCap_nonIrq (c : Cap) (h : ∀ i, c ≠ .irqHandlerCap i) (fin : Bool) :
    ∀ v, UK v (finaliseCap (Z := Unit) c fin) := by
  intro v
  cases c <;> simp only [finaliseCap] <;> first | exact absurd rfl (h _) | uk_auto

theorem ik_finaliseCap_irq (i : Irq) (fin : Bool) (sl : CslotPtr) :
    ∀ σ, UtInv'' σ → capAt σ sl = some (.irqHandlerCap i) →
      ∀ y ∈ (finaliseCap (Z := Unit) (.irqHandlerCap i) fin σ).1, UtInv'' y.2 ∧ capAt y.2 sl = some (.irqHandlerCap i) := by
  intro σ hI hc y hy
  simp only [finaliseCap] at hy
  split at hy
  · obtain ⟨z, hz, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy]
    unfold deletingIrqHandler getIrqSlot at hz
    obtain ⟨u, hu, hz⟩ := hz
    rw [Set.mem_singleton_iff.1 hu] at hz
    dsimp only at hz
    refine ⟨ik_capDeleteOneN _ σ hI z hz, ?_⟩
    by_cases e : sl = (σ.interruptIrqNode i, [])
    · rw [e] at hc; exact absurd hz (capDeleteOne_irq hc z)
    · have := capDeleteOne_keep _ sl e (uV σ) σ rfl z hz
      exact this.trans hc
  · rw [Set.mem_singleton_iff.1 hy]; exact ⟨hI, hc⟩

/-- A non-final slot-holding cap leaves another slot-holding reference. -/
theorem safeDel_nonfinal {σ : State Unit} (hI : UtInv'' σ) {s : CslotPtr} {c : Cap} (hc : capAt σ s = some c)
    (hnf : ¬ isFinalCap' (Z := Unit) c σ) : SafeDelV (uV σ) s c := by
  intro r hr
  obtain ⟨s', c', hne, hs', hr'⟩ := nonfinal_other hnf hc hr
  obtain ⟨x, hx⟩ := shp_of_sRefs hr
  have hk := hI.2.2.2.2.1 s' c' s c r hs' hc (objRefs_sub_capRng _ hr') hr
  exact Or.inl ⟨s', c', hne, hs', sRefs_of_shp hr' (hk.trans hx)⟩

/-- A removeable Zombie's slot may be emptied. -/
theorem safeDel_zombie {w : UView} (hN : UtNV w) {s : CslotPtr} {r : ObjRef} {b : Option Nat} {n : Nat}
    (hs : w.2.1 s = some (.zombie r b n)) (hrm : capRemoveable (.zombie r b n) s) :
    SafeDelV w s (.zombie r b n) := by
  intro r' hr'
  have e : r' = r := by simpa [sRefs] using hr'
  subst e
  refine Or.inr fun i c' hne hi => ?_
  by_contra hc'
  obtain ⟨k, hk, hik⟩ := hN.2.2.2.2.1 s _ r' hs hr' i c' hi hc'
  rcases hrm with h0 | ⟨h1, hcy⟩
  · omega
  · have : k = 0 := by omega
    subst this
    rw [natToCref_zero _ (zcb_le hN.2.2.2.2.2.2 hs)] at hik
    exact hne (by rw [hik]; exact hcy)

/-- What `finalise_cap cap (is_final cap)` gives `rec_del` at a slot holding `cap`. -/
theorem fin_step {σ : State Unit} (hI : UtInv'' σ) {s : CslotPtr} {cap : Cap} (hc : capAt σ s = some cap)
    (hnn : cap ≠ .nullCap) {y : (Cap × Cap) × State Unit}
    (hy : y ∈ (finaliseCap (Z := Unit) cap (decide (isFinalCap' (Z := Unit) cap σ)) σ).1) :
    UtInv'' y.2 ∧ capAt y.2 s = some cap ∧ (capRemoveable y.1.1 s → SafeDelV (uV y.2) s cap) ∧
      (¬ capRemoveable y.1.1 s → UtInv''V (vCap s y.1.1 (uV y.2))) := by
  by_cases hsr : sRefs cap = ∅
  · have hnull : y.1.1 = .nullCap := finaliseCap_null hsr _ σ y hy
    have hA : UtInv'' y.2 ∧ capAt y.2 s = some cap := by
      by_cases hirq : ∃ i, cap = .irqHandlerCap i
      · obtain ⟨i, rfl⟩ := hirq
        exact ik_finaliseCap_irq i _ s σ hI hc y hy
      · have hv : uV y.2 = uV σ :=
          uk_finaliseCap_nonIrq cap (fun i e => hirq ⟨i, e⟩) _ (uV σ) σ rfl y hy
        refine ⟨by show UtInv''V _; rw [hv]; exact hI, ?_⟩
        show (uV y.2).2.1 s = _
        rw [hv]; exact hc
    refine ⟨hA.1, hA.2, fun _ => safeDel_of_sRefs hsr, fun hrm => ?_⟩
    exact absurd (by rw [hnull]; trivial) hrm
  · have hB := hI.2.2.2.2.2.2.2
    cases cap with
    | cnodeCap r bits g =>
      simp only [finaliseCap] at hy
      rw [Set.mem_singleton_iff.1 hy]
      dsimp only
      by_cases hf : isFinalCap' (Z := Unit) (.cnodeCap r bits g) σ
      · rw [decide_eq_true hf, if_pos rfl]
        have hbits : bits ≤ 64 := hB s _ hc bits rfl
        have hfin := final_unique hf hc (r := r) (by simp [objRefs])
        refine ⟨hI, hc, fun hrm => ?_, fun _ => ?_⟩
        · -- a zero-radix CNode holding its own cap
          rcases hrm with h0 | ⟨h1, hcy⟩
          · exact absurd h0 (Nat.two_pow_pos bits).ne'
          · have hb0 : bits = 0 := by
              rcases Nat.eq_zero_or_pos bits with h | h
              · exact h
              · have := Nat.one_lt_two_pow (n := bits) (by omega); omega
            subst hb0
            intro r' hr'
            have e : r' = r := by simpa [sRefs] using hr'
            subst e
            refine Or.inr fun i c' hne hi => ?_
            by_contra hc'
            have hl : i.length = 0 := hI.2.2.2.2.2.1 s _ r' hc hr' i c' hi hc'
            rw [List.length_eq_zero_iff] at hl
            subst hl
            exact hne hcy
        · refine utN_zombieW hI.1 hI.2 hc (by simp [objRefs]) rfl (fun i hi => ?_) hfin
          have hi' : i.length = bits := hi
          obtain ⟨k, hk, hik⟩ := natToCref_of_len i (by omega)
          exact ⟨k, by rw [← hi']; exact hk, by show i = natToCref bits k; rw [hik, hi']⟩
      · rw [decide_eq_false hf, if_neg Bool.false_ne_true]
        exact ⟨hI, hc, fun _ => safeDel_nonfinal hI hc hf, fun hrm => absurd trivial hrm⟩
    | threadCap r =>
      have hv : uV y.2 = uV σ :=
        uk_finaliseCap_nonIrq (.threadCap r) (fun i e => by cases e) _ (uV σ) σ rfl y hy
      have hval := finaliseCap_thread_val r _ σ y hy
      have hI2 : UtInv'' y.2 := by show UtInv''V _; rw [hv]; exact hI
      have hc2 : capAt y.2 s = some (.threadCap r) := by show (uV y.2).2.1 s = _; rw [hv]; exact hc
      by_cases hf : isFinalCap' (Z := Unit) (.threadCap r) σ
      · rw [decide_eq_true hf, if_pos rfl] at hval
        rw [hval]
        refine ⟨hI2, hc2, fun hrm => ?_, fun _ => ?_⟩
        · exfalso; rcases hrm with h | ⟨h, -⟩ <;> omega
        · rw [hv]
          refine utN_zombieW hI.1 hI.2 hc (by simp [objRefs]) rfl (fun i hi => ?_)
            (final_unique hf hc (r := r) (by simp [objRefs]))
          obtain ⟨k, hk, hik⟩ := hi
          exact ⟨k, hk, by rw [hik]; exact tcb_natToCref hk⟩
      · rw [decide_eq_false hf, if_neg Bool.false_ne_true] at hval
        rw [hval]
        refine ⟨hI2, hc2, fun _ => ?_, fun hrm => absurd trivial hrm⟩
        rw [hv]; exact safeDel_nonfinal hI hc hf
    | zombie r b n =>
      simp only [finaliseCap] at hy
      obtain ⟨u, hu, hy⟩ := hy
      obtain ⟨-, rfl⟩ := hu
      rw [Set.mem_singleton_iff.1 hy]
      dsimp only
      refine ⟨hI, hc, fun hrm => safeDel_zombie hI.2 hc hrm, fun _ => ?_⟩
      show UtInv''V (vCap s _ (uV σ)); rw [vCap_same hc]; exact hI
    | _ => exact absurd rfl hsr

/-- A Zombie may move to its first slot (`cap_swap_for_delete` in `reduce_zombie`). -/
theorem posOK_firstSlot {w : UView} (hN : UtNV w) {slot : CslotPtr} {ptr : ObjRef} {b : Option Nat} {n : Nat}
    (hz : w.2.1 slot = some (.zombie ptr b (n + 1))) :
    PosOK w (ptr, List.replicate (zombieCteBits b) false) := by
  refine ⟨fun _ => ⟨slot, _, hz, by simp [sRefs]⟩, fun s' c' hs' hr' => ?_⟩
  have hs : s' = slot := by
    by_contra hne
    exact hN.2.2.2.2.2.1 slot ptr b (n + 1) hz s' c' hne hs' (sRefs_sub _ hr')
  subst hs
  rw [hz] at hs'; cases hs'
  exact ⟨0, by omega, (natToCref_zero _ (zcb_le hN.2.2.2.2.2.2 hz)).symm⟩

end

end Fl4Proofs.P3.SInvU
