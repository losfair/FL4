/-
P3 (DESIGN.md §9), CSpace: **writing a cap into any slot of the typed heap**,
a CNode's or a TCB's. The spec's `set_cap` on a TCB slot updates one of the
six cap fields of the TCB. With it, `empty_slot` and `cap_swap` hold for
TCB slots too (`empty_full_abs`, `swap_full_abs`), which the deletion of a
TCB's zombie needs.
-/
import Fl4Proofs.P3.CnodeRevoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option maxHeartbeats 1000000

/-! ## The spec's `set_cap` on a TCB slot -/

section Spec
open Fl4Spec
variable {Z : Type}

/-- The TCB with cap field `i` (`tcb_cnode_index i`) set to `a`. -/
def tcbSet (tcb : Tcb) (i : Nat) (a : Cap) : Tcb :=
  if i = 0 then { tcb with tcbCtable := a }
  else if i = 1 then { tcb with tcbVtable := a }
  else if i = 2 then { tcb with tcbIpcframe := a }
  else if i = 3 then { tcb with tcbFaultHandler := a }
  else if i = 4 then { tcb with tcbTimeoutHandler := a }
  else { tcb with tcbEpt := a }

theorem tcbIdx_ne {i j : Nat} (hi : i < tcbSlots) (hj : j < tcbSlots) (h : i ≠ j) :
    tcbCnodeIndex i ≠ tcbCnodeIndex j := fun e => h (tcbCnodeIndex_inj hi hj e)

theorem tcbCnodeMap_set (tcb : Tcb) {i : Nat} (hi : i < tcbSlots) (a : Cap) :
    tcbCnodeMap (tcbSet tcb i a) = Function.update (tcbCnodeMap tcb) (tcbCnodeIndex i) (some a) := by
  have d : ∀ i j, i < tcbSlots → j < tcbSlots → i ≠ j → tcbCnodeIndex i ≠ tcbCnodeIndex j :=
    fun i j hi hj h => tcbIdx_ne hi hj h
  have d01 := d 0 1 (by decide) (by decide) (by decide)
  have d02 := d 0 2 (by decide) (by decide) (by decide)
  have d03 := d 0 3 (by decide) (by decide) (by decide)
  have d04 := d 0 4 (by decide) (by decide) (by decide)
  have d12 := d 1 2 (by decide) (by decide) (by decide)
  have d13 := d 1 3 (by decide) (by decide) (by decide)
  have d14 := d 1 4 (by decide) (by decide) (by decide)
  have d23 := d 2 3 (by decide) (by decide) (by decide)
  have d24 := d 2 4 (by decide) (by decide) (by decide)
  have d34 := d 3 4 (by decide) (by decide) (by decide)
  have d05 := d 0 5 (by decide) (by decide) (by decide)
  have d15 := d 1 5 (by decide) (by decide) (by decide)
  have d25 := d 2 5 (by decide) (by decide) (by decide)
  have d35 := d 3 5 (by decide) (by decide) (by decide)
  have d45 := d 4 5 (by decide) (by decide) (by decide)
  funext x
  unfold tcbSlots at hi
  interval_cases i <;>
    simp only [tcbSet, tcbCnodeMap, Function.update_apply, Nat.zero_ne_one, OfNat.ofNat_ne_one, ↓reduceIte,
      show ¬ (2 : Nat) = 0 by decide, show ¬ (3 : Nat) = 0 by decide, show ¬ (4 : Nat) = 0 by decide,
      show ¬ (2 : Nat) = 1 by decide, show ¬ (3 : Nat) = 1 by decide, show ¬ (4 : Nat) = 1 by decide,
      show ¬ (3 : Nat) = 2 by decide, show ¬ (4 : Nat) = 2 by decide, show ¬ (4 : Nat) = 3 by decide,
      show ¬ (1 : Nat) = 0 by decide,
      show ¬ (5 : Nat) = 0 by decide, show ¬ (5 : Nat) = 1 by decide, show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 3 by decide, show ¬ (5 : Nat) = 4 by decide] <;>
    split_ifs <;> simp_all

/-- The abstract state after writing `a` into cap slot `i` of the TCB at `t`. -/
def setTcbSlot (σ : State Z) (t : ObjRef) (tcb : Tcb) (i : Nat) (a : Cap) : State Z :=
  { σ with kheap := Function.update σ.kheap t (some (.tcb (tcbSet tcb i a))) }

theorem setCap_tcb {σ : State Z} {t : ObjRef} {tcb : Tcb} {i : Nat} (a : Cap)
    (hk : σ.kheap t = some (.tcb tcb)) (hi : i < tcbSlots) :
    setCap (Z := Z) a (t, tcbCnodeIndex i) σ = ({((), setTcbSlot σ t tcb i a)}, False) := by
  have hobj : getObject (Z := Z) t σ = ({(.tcb tcb, σ)}, False) := by
    simp [getObject, NonDet.getsThe, readObject, hk, NonDet.assertOpt]; rfl
  have hset : setObject (Z := Z) t (.tcb (tcbSet tcb i a)) σ = ({((), setTcbSlot σ t tcb i a)}, False) := by
    unfold setObject
    show (getObject t >>= _) σ = _
    rw [nd_bind_single hobj]
    have ha : NonDet.assert (σ := State Z) (aType (.tcb tcb) = aType (.tcb (tcbSet tcb i a))) σ =
        ({((), σ)}, False) := by simp [NonDet.assert, aType]
    show (NonDet.assert _ >>= _) σ = _
    rw [nd_bind_single ha]
    show (NonDet.get >>= _) σ = _
    rw [nd_bind_single (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl)]
    rfl
  have d : ∀ i j, i < tcbSlots → j < tcbSlots → i ≠ j → tcbCnodeIndex i ≠ tcbCnodeIndex j :=
    fun i j hi hj h => tcbIdx_ne hi hj h
  have d10 := d 1 0 (by decide) (by decide) (by decide)
  have d20 := d 2 0 (by decide) (by decide) (by decide)
  have d30 := d 3 0 (by decide) (by decide) (by decide)
  have d40 := d 4 0 (by decide) (by decide) (by decide)
  have d21 := d 2 1 (by decide) (by decide) (by decide)
  have d31 := d 3 1 (by decide) (by decide) (by decide)
  have d41 := d 4 1 (by decide) (by decide) (by decide)
  have d32 := d 3 2 (by decide) (by decide) (by decide)
  have d42 := d 4 2 (by decide) (by decide) (by decide)
  have d43 := d 4 3 (by decide) (by decide) (by decide)
  have d50 := d 5 0 (by decide) (by decide) (by decide)
  have d51 := d 5 1 (by decide) (by decide) (by decide)
  have d52 := d 5 2 (by decide) (by decide) (by decide)
  have d53 := d 5 3 (by decide) (by decide) (by decide)
  have d54 := d 5 4 (by decide) (by decide) (by decide)
  unfold setCap
  show (getObject t >>= _) σ = _
  rw [nd_bind_single hobj]
  rw [← hset]
  unfold tcbSlots at hi
  interval_cases i <;> simp only [tcbSet, d10, d20, d30, d40, d21, d31, d41, d32, d42, d43, d50, d51, d52, d53, d54, ↓reduceIte,
    show ¬ (2 : Nat) = 0 by decide, show ¬ (3 : Nat) = 0 by decide, show ¬ (4 : Nat) = 0 by decide,
    show ¬ (2 : Nat) = 1 by decide, show ¬ (3 : Nat) = 1 by decide, show ¬ (4 : Nat) = 1 by decide,
    show ¬ (3 : Nat) = 2 by decide, show ¬ (4 : Nat) = 2 by decide, show ¬ (4 : Nat) = 3 by decide,
    show ¬ (1 : Nat) = 0 by decide,
      show ¬ (5 : Nat) = 0 by decide, show ¬ (5 : Nat) = 1 by decide, show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 3 by decide, show ¬ (5 : Nat) = 4 by decide] <;> rw [nd_pure_bind]

end Spec

/-! ## The relation after a TCB slot gets a related cap -/

section
variable {Z : Type}

theorem StateRel.update_tcb_slot {th : TypedHeap} {mem mem' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    {t : U64} (ht : th t = some .tcb) {tcb : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb tcb))
    {i : Nat} (hi : i < tcbSlots) {c : capability.Cap} {a : Fl4Spec.Cap}
    (hca : CapRel c a) (hcv : CapValid th c)
    (hcap : ∀ x, IsSlot th x → capAt mem' x = if x = slotOf t i then ok c else capAt mem x) :
    StateRel th mem' (setTcbSlot σ t.bv tcb i a) ∧ SlotsValid th mem' := by
  have hsp : IsSlotAt th t i := Or.inr ⟨ht, hi⟩
  have hself : capAt mem' (slotOf t i) = ok c := by rw [hcap _ ⟨_, _, hsp, rfl⟩]; simp
  have hother : ∀ q j, IsSlotAt th q j → ¬ (q = t ∧ j = i) →
      capAt mem' (slotOf q j) = capAt mem (slotOf q j) := by
    intro q j hq hne
    rw [hcap _ ⟨_, _, hq, rfl⟩, if_neg]
    intro h
    rcases hq.apart hP hsp hne with h' | h' <;> rw [h] at h' <;> omega
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro q r' hq
    have htq : q ≠ t := by rintro rfl; rw [ht] at hq; cases hq
    have hb : q.bv ≠ t.bv := fun h => htq (bv_inj h)
    obtain ⟨cs', hk', hwf', hs'⟩ := hR.cnode q r' hq
    refine ⟨cs', by simp [setTcbSlot, Function.update_of_ne hb, hk'], hwf', ?_⟩
    intro idx' hl
    unfold SlotRel
    rw [slotAddr_ofBl, hother _ _ (Or.inl ⟨r', hq, hl ▸ blVal_lt idx'⟩) (fun h => htq h.1), ← slotAddr_ofBl]
    exact hs' idx' hl
  · intro q hq
    obtain ⟨tcb', hk', hs'⟩ := hR.tcb q hq
    by_cases hqt : q = t
    · subst hqt
      rw [hk] at hk'; cases hk'
      refine ⟨tcbSet tcb i a, by simp [setTcbSlot], fun j hj => ?_⟩
      show SlotRel _ (slotOf q j) _
      rw [tcbCnodeMap_set tcb hi]
      by_cases hji : j = i
      · subst hji; exact ⟨c, a, hself, by simp, hca⟩
      · have hne : Fl4Spec.tcbCnodeIndex j ≠ Fl4Spec.tcbCnodeIndex i := fun h => hji (tcbCnodeIndex_inj hj hi h)
        unfold SlotRel
        rw [hother _ _ (Or.inr ⟨hq, hj⟩) (fun h => hji h.2), Function.update_of_ne hne]
        exact hs' j hj
    · have hb : q.bv ≠ t.bv := fun h => hqt (bv_inj h)
      refine ⟨tcb', by simp [setTcbSlot, Function.update_of_ne hb, hk'], fun j hj => ?_⟩
      show SlotRel _ (slotOf q j) _
      unfold SlotRel
      rw [hother _ _ (Or.inr ⟨hq, hj⟩) (fun h => hqt h.1)]
      exact hs' j hj
  · intro q r' hq j hj c' hc'
    have htq : q ≠ t := by rintro rfl; rw [ht] at hq; cases hq
    change capAt _ (slotOf q j) = _ at hc'
    rw [hother _ _ (Or.inl ⟨r', hq, hj⟩) (fun h => htq h.1)] at hc'
    exact hV.cnode q r' hq j hj c' hc'
  · intro q hq j hj c' hc'
    by_cases hqi : q = t ∧ j = i
    · obtain ⟨rfl, rfl⟩ := hqi
      change capAt _ (slotOf q j) = _ at hc'
      rw [hself] at hc'; have e : c = c' := by simpa using hc'
      subst e; exact hcv
    · change capAt _ (slotOf q j) = _ at hc'
      rw [hother _ _ (Or.inr ⟨hq, hj⟩) hqi] at hc'
      exact hV.tcb q hq j hj c' hc'

/-- **Writing a related cap into any slot of the typed heap**: the spec's
`set_cap` has a single outcome, which changes only the slot's object, and
the states are related again. -/
theorem StateRel.update_abs_slot {th : TypedHeap} {mem mem' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : StateRel th mem σ) (hV : SlotsValid th mem) (hP : Placed th)
    {sl : Fl4Spec.CslotPtr} (hs : AbsSlot th sl) {c : capability.Cap} {a : Fl4Spec.Cap}
    (hca : CapRel c a) (hcv : CapValid th c)
    (hcap : ∀ x, IsSlot th x → capAt mem' x = if x = cslotAddr sl then ok c else capAt mem x) :
    ∃ σ', Fl4Spec.setCap (Z := Z) a sl σ = ({((), σ')}, False) ∧
      StateRel th mem' σ' ∧ SlotsValid th mem' ∧
      σ' = { σ with kheap := σ'.kheap } ∧ (∀ q, q ≠ sl.1 → σ'.kheap q = σ.kheap q) := by
  obtain ⟨p, h1, h2 | ⟨ht, i, hi, hidx⟩⟩ := hs
  · obtain ⟨o, idx⟩ := sl
    simp only at h1 h2; subst h1
    obtain ⟨cs, hk, hwf, -⟩ := hR.cnode p _ h2
    have hcap' : ∀ x, IsSlot th x → capAt mem' x = if x = slotOf p (blVal 0 idx) then ok c else capAt mem x := by
      intro x hx; rw [hcap x hx, show cslotAddr (p.bv, idx) = slotOf p (blVal 0 idx) from slotAddr_ofBl p idx]
    obtain ⟨hR', hV'⟩ := StateRel.update_cnode_slot hR hV hP h2 hk hwf rfl hca hcv hcap'
    refine ⟨_, setCap_cnode a hk hwf rfl, hR', hV', rfl, fun q hq => ?_⟩
    simp [setCnodeSlot, Function.update_of_ne hq]
  · obtain ⟨o, idx⟩ := sl
    simp only at h1 hidx; subst h1 hidx
    obtain ⟨tcb, hk, -⟩ := hR.tcb p ht
    have he : cslotAddr (p.bv, Fl4Spec.tcbCnodeIndex i) = slotOf p i := by
      show slotAddr p.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hi]
    have hcap' : ∀ x, IsSlot th x → capAt mem' x = if x = slotOf p i then ok c else capAt mem x := by
      intro x hx; rw [hcap x hx, he]
    obtain ⟨hR', hV'⟩ := StateRel.update_tcb_slot hR hV hP ht hk hi hca hcv hcap'
    refine ⟨_, setCap_tcb a hk hi, hR', hV', rfl, fun q hq => ?_⟩
    simp [setTcbSlot, Function.update_of_ne hq]

end

/-! ## `empty_slot` on any slot of the typed heap -/

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

theorem empty_slot_refines_abs (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {xs : Fl4Spec.CslotPtr} (hAx : AbsSlot th xs)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr xs) = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a (cslotAddr xs) .Null ⦃ r => r.2 = a ∧
      ∃ σ' G', Fl4Spec.emptySlot (Z := Unit) xs .nullCap σ = ({((), σ')}, False) ∧
        StateRel th (L.mem r.1) σ' ∧ SlotsValid th (L.mem r.1) ∧ MdbLinks th (L.mem r.1) G' ∧
        CdtRel th (L.mem r.1) σ' G' ∧ G' = remG G (cslotAddr xs) ∧
        (∀ y, IsSlot th y → capAt (L.mem r.1) y = if y = cslotAddr xs then ok .Null else capAt (L.mem s) y) ∧
        prevOf (L.mem r.1) (cslotAddr xs) = 0#u64 ∧ nextOf (L.mem r.1) (cslotAddr xs) = 0#u64 ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr xs → y ∉ G.chains.flatten →
          prevOf (L.mem r.1) y = prevOf (L.mem s) y ∧ nextOf (L.mem r.1) y = nextOf (L.mem s) y) ⦄ := by
  have hx : IsSlot th (cslotAddr xs) := hAx.isSlot
  have hxm : cslotAddr xs ∈ G.chains.flatten := (hM.members _).2 ⟨hx, c, hc, hcn⟩
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hnx : nextOf (L.mem s) (cslotAddr xs) = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) (cslotAddr xs)) ∧ nextOf (L.mem s) (cslotAddr xs) ≠ cslotAddr xs) := by
    rcases hM.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s) (cslotAddr xs) = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) (cslotAddr xs)) ∧ prevOf (L.mem s) (cslotAddr xs) ≠ cslotAddr xs) := by
    by_cases h0 : prevOf (L.mem s) (cslotAddr xs) = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hx.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM.prev_ne_next hP hxm
  have hNc : Canonical (nextOf (L.mem s) (cslotAddr xs)) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  obtain ⟨c', ac, hc', hrel, hget⟩ := hR.abs_cap hAx
  rw [hc] at hc'; cases eq_of_ok_eq hc'
  have hacn : ac ≠ .nullCap := fun h => hcn ((hrel.null_iff).1 h)
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, hra⟩
  refine ⟨hra, ?_⟩
  have hR1 : StateRel th (L.mem s) (emptySlotCdtState σ xs) := StateRel.of_kheap hR rfl
  have hcap' : ∀ y, IsSlot th y → capAt (L.mem r.1) y =
      if y = cslotAddr xs then ok .Null else capAt (L.mem s) y := by
    intro y hy; rw [hW.capAt' hy]
  obtain ⟨σ2, h2, hR2, hV2, -, -⟩ := StateRel.update_abs_slot hR1 hV hP hAx
    (show CapRel .Null .nullCap from ⟨trivial, rfl⟩) trivial hcap'
  refine ⟨_, ⟨Mdb.removeChains (cslotAddr xs) G.chains, Mdb.removePar (cslotAddr xs) G.par⟩,
    emptySlot_eq hget hacn h2, hR2, hV2, ?_, ?_, rfl, fun y hy => hW.capAt' hy, ?_, ?_, ?_⟩
  · refine MdbLinks.remove hP hM hxm ⟨fun y hy => hW.prevOf' hy, fun y hy => hW.nextOf' hy hNc hPN, ?_, ?_⟩
    · rw [hW.capAt' hx]; simp
    · intro y hy hyx; rw [hW.capAt' hy]; simp [hyx]
  · obtain ⟨σ2', h2', -, -, hσ2, -⟩ := StateRel.update_abs_slot hR1 hV hP hAx
      (show CapRel .Null .nullCap from ⟨trivial, rfl⟩) trivial hcap'
    rw [h2] at h2'
    have e : σ2 = σ2' := by simpa using h2'
    subst e
    refine CdtRel.remove hP hC _ hAx ?_ ?_ (fun y hy => hW.revOf' hy)
    · rw [hσ2]; rfl
    · rw [hσ2]; rfl
  · rw [hW.prevOf' hx, if_pos rfl]
  · rw [hW.nextOf' hx hNc hPN, if_pos rfl]
  · intro y hy hyx hym
    have g1 : ¬ (nextOf (L.mem s) (cslotAddr xs) ≠ 0#u64 ∧ y = nextOf (L.mem s) (cslotAddr xs)) := by
      rintro ⟨h0, e⟩; exact hym (e ▸ (hM.next_link hxm h0).1)
    have g2 : ¬ (prevOf (L.mem s) (cslotAddr xs) ≠ 0#u64 ∧ y = prevOf (L.mem s) (cslotAddr xs)) := by
      rintro ⟨h0, e⟩; exact hym (e ▸ (hM.prev_link hxm h0).1)
    rw [hW.prevOf' hy, hW.nextOf' hy hNc hPN, if_neg hyx, if_neg hyx, if_neg g1, if_neg g2]
    exact ⟨rfl, rfl⟩

/-- **`cdt::empty_slot` (no cleanup) refines `empty_slot` and keeps
`MdbInv`**, on any slot of the typed heap. -/
theorem empty_full_abs (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {xs : Fl4Spec.CslotPtr} (hAx : AbsSlot th xs)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr xs) = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a (cslotAddr xs) .Null ⦃ r => r.2 = a ∧
      ∃ σ' G', Fl4Spec.emptySlot (Z := Unit) xs .nullCap σ = ({((), σ')}, False) ∧
        StateRel th (L.mem r.1) σ' ∧ SlotsValid th (L.mem r.1) ∧ MdbLinks th (L.mem r.1) G' ∧
        CdtRel th (L.mem r.1) σ' G' ∧ MdbInv (L.mem r.1) G' ∧ G' = remG G (cslotAddr xs) ∧
        (∀ y, IsSlot th y → capAt (L.mem r.1) y = if y = cslotAddr xs then ok .Null else capAt (L.mem s) y) ∧
        prevOf (L.mem r.1) (cslotAddr xs) = 0#u64 ∧ nextOf (L.mem r.1) (cslotAddr xs) = 0#u64 ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr xs → y ∉ G.chains.flatten →
          prevOf (L.mem r.1) y = prevOf (L.mem s) y ∧ nextOf (L.mem r.1) y = nextOf (L.mem s) y) ⦄ := by
  have hxm := (hM.members _).2 ⟨hAx.isSlot, c, hc, hcn⟩
  obtain ⟨r1, h1, hpost⟩ := spec_exists (empty_slot_refines_abs (ar := ar) th s a σ G hR hV hP hM hC hAx hc hcn)
  obtain ⟨r2, h2, hinv⟩ := spec_exists (empty_slot_mdbinv (ar := ar) hP s a G hM hI hxm hc hcn)
  rw [h1] at h2
  have e := eq_of_ok_eq h2
  subst e
  rw [h1, WP.spec_ok]
  obtain ⟨hra, σ', G', hes, hR', hV', hM', hC', hG', h1, h2, h3, h4⟩ := hpost
  exact ⟨hra, σ', G', hes, hR', hV', hM', hC', by rw [hG']; exact hinv, hG', h1, h2, h3, h4⟩

end

/-! ## `cap_swap` on any two slots of the typed heap -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem swap_refines_abs (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {sl1 sl2 : Fl4Spec.CslotPtr} (hA1 : AbsSlot th sl1) (hA2 : AbsSlot th sl2) (hne : sl1 ≠ sl2)
    {o1 o2 : capability.Cap} (ho1 : capAt (L.mem s) (cslotAddr sl1) = ok o1) (hon1 : o1 ≠ .Null)
    (ho2 : capAt (L.mem s) (cslotAddr sl2) = ok o2) (hon2 : o2 ≠ .Null)
    (c1 : capability.Cap) (a1 : Fl4Spec.Cap) (hca1 : CapRel c1 a1) (hcv1 : CapValid th c1) (he1 : EncWf c1)
    (hcn1 : c1 ≠ .Null)
    (c2 : capability.Cap) (a2 : Fl4Spec.Cap) (hca2 : CapRel c2 a2) (hcv2 : CapValid th c2) (he2 : EncWf c2)
    (hcn2 : c2 ≠ .Null) :
    cdt.swap st s c1 (cslotAddr sl1) c2 (cslotAddr sl2) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) a1 sl1 a2 sl2 σ = ({((), σ')}, False) ∧
        G' = renG G (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧
        (∀ x, IsSlot th x → capAt (L.mem s') x =
          (if x = cslotAddr sl2 then ok c1 else if x = cslotAddr sl1 then ok c2 else capAt (L.mem s) x)) ∧
        (∀ x, IsSlot th x → x ∉ G.chains.flatten → x ≠ cslotAddr sl1 → x ≠ cslotAddr sl2 →
          prevOf (L.mem s') x = prevOf (L.mem s) x ∧ nextOf (L.mem s') x = nextOf (L.mem s) x) ⦄ := by
  have hs1 := hA1.isSlot
  have hs2 := hA2.isSlot
  have hAne : cslotAddr sl1 ≠ cslotAddr sl2 := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm1 : cslotAddr sl1 ∈ G.chains.flatten := (hM.members _).2 ⟨hs1, o1, ho1, hon1⟩
  have hm2 : cslotAddr sl2 ∈ G.chains.flatten := (hM.members _).2 ⟨hs2, o2, ho2, hon2⟩
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hNx : ∀ a, a ∈ G.chains.flatten → nextOf (L.mem s) a = 0#u64 ∨ IsSlot th (nextOf (L.mem s) a) := by
    intro a ha; rcases hM.next_mem ha with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have hPx : ∀ a, a ∈ G.chains.flatten → prevOf (L.mem s) a = 0#u64 ∨ IsSlot th (prevOf (L.mem s) a) := by
    intro a ha; by_cases h : prevOf (L.mem s) a = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link ha h).1)
  apply WP.spec_mono (swap_fields hP s c1 c2 _ _ hs1 hs2 hAne he1 he2 (hPx _ hm1) (hNx _ hm1)
    (hPx _ hm2) (hNx _ hm2))
  intro s' hW
  have hcap1 : ∀ x, IsSlot th x → capAt (L.mem (wrCap (L := L) s (cslotAddr sl1) c2)) x =
      if x = cslotAddr sl1 then ok c2 else capAt (L.mem s) x := by
    intro x hx; rw [capAt_wrCap hP s hs1 he2 hx]
  obtain ⟨σ1, h1, hR1, hV1, hσ1, -⟩ := StateRel.update_abs_slot hR hV hP hA1 hca2 hcv2 hcap1
  have hcap2 : ∀ x, IsSlot th x → capAt (L.mem s') x =
      if x = cslotAddr sl2 then ok c1
      else capAt (L.mem (wrCap (L := L) s (cslotAddr sl1) c2)) x := by
    intro x hx
    rw [(hW x hx).1, capAt_wrCap hP s hs1 he2 hx]
  obtain ⟨σ2, h2, hR2, hV2, hσ2, -⟩ := StateRel.update_abs_slot hR1 hV1 hP hA2 hca1 hcv1 hcap2
  have hio : σ2.isOriginalCap = σ.isOriginalCap := by rw [hσ2, hσ1]
  have hcdt : σ2.cdt = σ.cdt := by rw [hσ2, hσ1]
  have hsw := capSwap_eq h1 h2 hio hcdt
  refine ⟨_, ⟨G.chains.map (List.map (Equiv.swap (cslotAddr sl1) (cslotAddr sl2))),
    Mdb.conjPar (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) G.par⟩, hsw, rfl,
    StateRel.of_kheap hR2 rfl, hV2,
    MdbLinks.rename (e := Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) hM ?_, ?_, fun x hx => (hW x hx).1, ?_⟩
  · exact RenLinks.swap hP hM hm1 hm2 hAne hcn1 hcn2 (fun x hx => ⟨(hW x hx).1, (hW x hx).2.1, (hW x hx).2.2.1⟩)
  · refine CdtRel.swap hP hC _ hA1 hA2 hne ?_ ?_ ?_
    · exact swap_cdt_eq σ _ _ hne
    · exact swap_io_eq σ _ _ hne
    · intro x hx
      rw [(hW x hx).2.2.2.1]
      by_cases e2 : x = cslotAddr sl2
      · rw [if_pos e2, e2, Equiv.swap_apply_right]
      · by_cases e1 : x = cslotAddr sl1
        · rw [if_neg e2, if_pos e1, e1, Equiv.swap_apply_left]
        · rw [if_neg e2, if_neg e1, Equiv.swap_apply_of_ne_of_ne e1 e2]
  · intro x hx hxm hx1 hx2
    have hnm : ∀ u, u ∈ G.chains.flatten → x ≠ u := fun u hu e => hxm (e ▸ hu)
    have h1n : ¬ (nextOf (L.mem s) (cslotAddr sl1) ≠ 0#u64 ∧ x = nextOf (L.mem s) (cslotAddr sl1)) := by
      rintro ⟨h0, h⟩; exact hnm _ (hM.next_link hm1 h0).1 h
    have h1p : ¬ (prevOf (L.mem s) (cslotAddr sl1) ≠ 0#u64 ∧ x = prevOf (L.mem s) (cslotAddr sl1)) := by
      rintro ⟨h0, h⟩; exact hnm _ (hM.prev_link hm1 h0).1 h
    have hq : ∀ q, (q = cslotAddr sl2 ∨ q = 0#u64 ∨ q ∈ G.chains.flatten) → ¬ (q ≠ 0#u64 ∧ x = q) := by
      rintro q (h | h | h) ⟨h0, e⟩
      · exact hx2 (e.trans h)
      · exact h0 h
      · exact hnm q h e
    have hn2 : ∀ u, u ∈ G.chains.flatten → (nextOf (L.mem s) u = 0#u64 ∨ nextOf (L.mem s) u ∈ G.chains.flatten) := by
      intro u hu; rcases hM.next_mem hu with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
    have hp2 : ∀ u, u ∈ G.chains.flatten → (prevOf (L.mem s) u = 0#u64 ∨ prevOf (L.mem s) u ∈ G.chains.flatten) := by
      intro u hu; by_cases h : prevOf (L.mem s) u = 0#u64
      · exact Or.inl h
      · exact Or.inr (hM.prev_link hu h).1
    obtain ⟨-, hpv, hnx, -, -⟩ := hW x hx
    refine ⟨?_, ?_⟩
    · rw [hpv]
      have g1 := hq (if prevOf (L.mem s) (cslotAddr sl1) ≠ 0#u64 ∧ cslotAddr sl2 = prevOf (L.mem s) (cslotAddr sl1)
          then cslotAddr sl2 else nextOf (L.mem s) (cslotAddr sl2)) (by
        split_ifs
        · exact Or.inl rfl
        · rcases hn2 _ hm2 with h | h <;> [exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)])
      simp only [ne_eq] at g1
      rw [if_neg g1, if_neg hx2, if_neg hx1]; beta_reduce; rw [if_neg h1n]
    · rw [hnx]
      have g1 := hq (if nextOf (L.mem s) (cslotAddr sl1) ≠ 0#u64 ∧ cslotAddr sl2 = nextOf (L.mem s) (cslotAddr sl1)
          then cslotAddr sl2 else prevOf (L.mem s) (cslotAddr sl2)) (by
        split_ifs
        · exact Or.inl rfl
        · rcases hp2 _ hm2 with h | h <;> [exact Or.inr (Or.inl h); exact Or.inr (Or.inr h)])
      simp only [ne_eq] at g1
      rw [if_neg g1, if_neg hx2, if_neg hx1]; beta_reduce; rw [if_neg h1p]

theorem swap_full_abs (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {sl1 sl2 : Fl4Spec.CslotPtr} (hA1 : AbsSlot th sl1) (hA2 : AbsSlot th sl2) (hne : sl1 ≠ sl2)
    {o1 o2 : capability.Cap} (ho1 : capAt (L.mem s) (cslotAddr sl1) = ok o1) (hon1 : o1 ≠ .Null)
    (ho2 : capAt (L.mem s) (cslotAddr sl2) = ok o2) (hon2 : o2 ≠ .Null)
    (c1 : capability.Cap) (a1 : Fl4Spec.Cap) (hca1 : CapRel c1 a1) (hcv1 : CapValid th c1) (he1 : EncWf c1)
    (hcn1 : c1 ≠ .Null) (hsh1 : shape c1 = shape o1) (hbd1 : badgeF c1 = badgeF o1)
    (c2 : capability.Cap) (a2 : Fl4Spec.Cap) (hca2 : CapRel c2 a2) (hcv2 : CapValid th c2) (he2 : EncWf c2)
    (hcn2 : c2 ≠ .Null) (hsh2 : shape c2 = shape o2) (hbd2 : badgeF c2 = badgeF o2) :
    cdt.swap st s c1 (cslotAddr sl1) c2 (cslotAddr sl2) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) a1 sl1 a2 sl2 σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧
        G' = renG G (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) ∧
        (∀ x, IsSlot th x → capAt (L.mem s') x =
          (if x = cslotAddr sl2 then ok c1 else if x = cslotAddr sl1 then ok c2 else capAt (L.mem s) x)) ∧
        (∀ x, IsSlot th x → x ∉ G.chains.flatten → x ≠ cslotAddr sl1 → x ≠ cslotAddr sl2 →
          prevOf (L.mem s') x = prevOf (L.mem s) x ∧ nextOf (L.mem s') x = nextOf (L.mem s) x) ⦄ := by
  have hAne : cslotAddr sl1 ≠ cslotAddr sl2 := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm1 := (hM.members _).2 ⟨hA1.isSlot, o1, ho1, hon1⟩
  have hm2 := (hM.members _).2 ⟨hA2.isSlot, o2, ho2, hon2⟩
  obtain ⟨s1, h1, hpost⟩ := spec_exists
    (swap_refines_abs th s σ G hR hV hP hM hC hA1 hA2 hne ho1 hon1 ho2 hon2 c1 a1 hca1 hcv1 he1 hcn1
      c2 a2 hca2 hcv2 he2 hcn2)
  rw [← capV_of_capAt ho1] at hsh1 hbd1
  rw [← capV_of_capAt ho2] at hsh2 hbd2
  obtain ⟨s2, h2, hinv⟩ := spec_exists
    (swap_mdbinv hP s G hM hI hm1 hm2 hAne c1 c2 he1 he2 hcn1 hcn2 hsh1 hbd1 hsh2 hbd2)
  rw [h1] at h2
  have e := eq_of_ok_eq h2
  subst e
  rw [h1, WP.spec_ok]
  obtain ⟨σ', G', hsw, hG', hR', hV', hM', hC', hcp, hnl⟩ := hpost
  exact ⟨σ', G', hsw, hR', hV', hM', hC', by rw [hG']; exact hinv, hG', hcp, hnl⟩

end

/-! ## `cap_swap` with an empty slot (whose links are clear) -/

section
variable {th : TypedHeap}

/-- The renaming of the ghost tree for a swap of the linked slot `s2` with
the unlinked slot `s1` (its links 0). -/
theorem RenLinks.swap1 (hP : Placed th) {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {s1 s2 : U64} (hs1 : IsSlot th s1) (h1m : s1 ∉ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten)
    {c2 : capability.Cap} (hc2 : c2 ≠ .Null)
    (hF : ∀ x, IsSlot th x →
      capAt mem' x = (if x = s2 then ok .Null else if x = s1 then ok c2 else capAt mem x) ∧
      prevOf mem' x = (if nextOf mem s2 ≠ 0#u64 ∧ x = nextOf mem s2 then s1 else if x = s2 then 0#u64
        else if x = s1 then prevOf mem s2 else prevOf mem x) ∧
      nextOf mem' x = (if prevOf mem s2 ≠ 0#u64 ∧ x = prevOf mem s2 then s1 else if x = s2 then 0#u64
        else if x = s1 then nextOf mem s2 else nextOf mem x)) :
    RenLinks th mem mem' (Equiv.swap s1 s2) G := by
  have hslot : ∀ a, a ∈ G.chains.flatten → IsSlot th a := fun a h => ((hM.members a).1 h).1
  have hz : ∀ a, a ∈ G.chains.flatten → a ≠ 0#u64 := fun a h => (hslot a h).ne_zero hP
  have hz1 : s1 ≠ 0#u64 := hs1.ne_zero hP
  have hz2 := hz s2 h2m
  have hne : s1 ≠ s2 := fun e => h1m (e ▸ h2m)
  have hsw : ∀ y, y ≠ s1 → y ≠ s2 → Equiv.swap s1 s2 y = y := fun y a b => Equiv.swap_apply_of_ne_of_ne a b
  have e0 : Equiv.swap s1 s2 0#u64 = 0#u64 := hsw _ hz1.symm hz2.symm
  have nmem : ∀ u, u ∈ G.chains.flatten → nextOf mem u ≠ s1 := by
    intro u hu h; rcases hM.next_mem hu with h' | ⟨h', -⟩
    · rw [h] at h'; exact hz1 h'
    · rw [h] at h'; exact h1m h'
  have pmem : ∀ u, u ∈ G.chains.flatten → prevOf mem u ≠ s1 := by
    intro u hu h
    have hp0 : prevOf mem u ≠ 0#u64 := by rw [h]; exact hz1
    have := (hM.prev_link hu hp0).1; rw [h] at this; exact h1m this
  have nself : ∀ u, u ∈ G.chains.flatten → nextOf mem u ≠ u := by
    intro u hu; rcases hM.next_mem hu with h | ⟨-, h⟩
    · rw [h]; exact (hz u hu).symm
    · exact h
  have pself : ∀ u, u ∈ G.chains.flatten → prevOf mem u ≠ u := by
    intro u hu h
    have hp0 : prevOf mem u ≠ 0#u64 := by rw [h]; exact hz u hu
    have := (hM.prev_link hu hp0).2; rw [h] at this; exact nself u hu this
  refine ⟨e0, ?_, ?_, ?_⟩
  · intro a ha
    have hF' := fun x hx => (hF x hx).2.2
    have ha1 : a ≠ s1 := fun e => h1m (e ▸ ha)
    by_cases h2 : a = s2
    · subst h2
      rw [Equiv.swap_apply_right, hF' s1 hs1]
      have g1 : ¬ (prevOf mem a ≠ 0#u64 ∧ s1 = prevOf mem a) := fun h => pmem a ha h.2.symm
      rw [if_neg g1, if_neg hne, if_pos rfl, hsw _ (nmem a ha) (nself a ha)]
    · rw [hsw a ha1 h2, hF' a (hslot a ha), if_neg h2, if_neg ha1]
      by_cases hn2 : nextOf mem a = s2
      · have hPa : prevOf mem s2 = a := by rw [← hn2]; exact (hM.next_link ha (by rw [hn2]; exact hz2)).2
        rw [if_pos ⟨by rw [hPa]; exact hz a ha, hPa.symm⟩, hn2, Equiv.swap_apply_right]
      · have g : ¬ (prevOf mem s2 ≠ 0#u64 ∧ a = prevOf mem s2) := by
          rintro ⟨h0, h⟩
          apply hn2; rw [h]; exact (hM.prev_link h2m h0).2
        rw [if_neg g, hsw _ (nmem a ha) hn2]
  · intro a ha
    have hF' := fun x hx => (hF x hx).2.1
    have ha1 : a ≠ s1 := fun e => h1m (e ▸ ha)
    by_cases h2 : a = s2
    · subst h2
      rw [Equiv.swap_apply_right, hF' s1 hs1]
      have g1 : ¬ (nextOf mem a ≠ 0#u64 ∧ s1 = nextOf mem a) := fun h => nmem a ha h.2.symm
      rw [if_neg g1, if_neg hne, if_pos rfl, hsw _ (pmem a ha) (pself a ha)]
    · rw [hsw a ha1 h2, hF' a (hslot a ha), if_neg h2, if_neg ha1]
      by_cases hp2 : prevOf mem a = s2
      · have hNa : nextOf mem s2 = a := by rw [← hp2]; exact (hM.prev_link ha (by rw [hp2]; exact hz2)).2
        rw [if_pos ⟨by rw [hNa]; exact hz a ha, hNa.symm⟩, hp2, Equiv.swap_apply_right]
      · have g : ¬ (nextOf mem s2 ≠ 0#u64 ∧ a = nextOf mem s2) := by
          rintro ⟨h0, h⟩
          apply hp2; rw [h]; exact (hM.next_link h2m h0).2
        rw [if_neg g, hsw _ (pmem a ha) hp2]
  · intro x
    have hcap := fun x hx => (hF x hx).1
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hys := hslot y hy
      have hy1 : y ≠ s1 := fun e => h1m (e ▸ hy)
      by_cases h2 : y = s2
      · subst h2; rw [Equiv.swap_apply_right]
        exact ⟨hs1, c2, by rw [hcap s1 hs1]; simp [hne], hc2⟩
      rw [hsw y hy1 h2]
      obtain ⟨-, c, hc, hcn⟩ := (hM.members y).1 hy
      exact ⟨hys, c, by rw [hcap y hys, if_neg h2, if_neg hy1]; exact hc, hcn⟩
    · rintro ⟨hx, c, hc, hcn⟩
      by_cases h1 : x = s1
      · subst h1; exact ⟨s2, h2m, Equiv.swap_apply_right _ _⟩
      by_cases h2 : x = s2
      · subst h2; rw [hcap x hx, if_pos rfl] at hc; cases eq_of_ok_eq hc; exact absurd rfl hcn
      rw [hcap x hx, if_neg h2, if_neg h1] at hc
      exact ⟨x, (hM.members x).2 ⟨hx, c, hc, hcn⟩, hsw x h1 h2⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`cdt::swap` of an empty slot `sl1` (links clear) with a linked slot
`sl2`** refines `cap_swap NullCap sl1 a2 sl2`: the ghost tree renames
`sl2` to `sl1`. -/
theorem swap_null_full (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    {sl1 sl2 : Fl4Spec.CslotPtr} (hA1 : AbsSlot th sl1) (hA2 : AbsSlot th sl2) (hne : sl1 ≠ sl2)
    (ho1 : capAt (L.mem s) (cslotAddr sl1) = ok .Null)
    (hp1 : prevOf (L.mem s) (cslotAddr sl1) = 0#u64) (hn1 : nextOf (L.mem s) (cslotAddr sl1) = 0#u64)
    {c2 : capability.Cap} (ho2 : capAt (L.mem s) (cslotAddr sl2) = ok c2) (hon2 : c2 ≠ .Null) :
    cdt.swap st s .Null (cslotAddr sl1) c2 (cslotAddr sl2) ⦃ s' =>
      ∃ σ' G', Fl4Spec.capSwap (Z := Unit) .nullCap sl1 (absCap c2) sl2 σ = ({((), σ')}, False) ∧
        StateRel th (L.mem s') σ' ∧ SlotsValid th (L.mem s') ∧ MdbLinks th (L.mem s') G' ∧
        CdtRel th (L.mem s') σ' G' ∧ MdbInv (L.mem s') G' ∧
        G' = renG G (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) ∧
        prevOf (L.mem s') (cslotAddr sl2) = 0#u64 ∧ nextOf (L.mem s') (cslotAddr sl2) = 0#u64 ∧
        (∀ x, IsSlot th x → x ≠ cslotAddr sl1 → x ≠ cslotAddr sl2 → capAt (L.mem s') x = capAt (L.mem s) x →
          capAt (L.mem s) x = ok .Null → prevOf (L.mem s') x = prevOf (L.mem s) x ∧
            nextOf (L.mem s') x = nextOf (L.mem s) x) ∧
        (∀ x, IsSlot th x → capAt (L.mem s') x =
          (if x = cslotAddr sl2 then ok .Null else if x = cslotAddr sl1 then ok c2 else capAt (L.mem s) x)) ∧
        MdbStep (L.mem s) G (L.mem s') G' ⦄ := by
  have hs1 := hA1.isSlot
  have hs2 := hA2.isSlot
  have hAne : cslotAddr sl1 ≠ cslotAddr sl2 := fun h => hne (cslotAddr_inj hP hA1 hA2 h)
  have hm2 : cslotAddr sl2 ∈ G.chains.flatten := (hM.members _).2 ⟨hs2, c2, ho2, hon2⟩
  have hm1 : cslotAddr sl1 ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c, hc, hcn⟩ := (hM.members _).1 h; rw [ho1] at hc; exact hcn (eq_of_ok_eq hc).symm
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hPx2 : prevOf (L.mem s) (cslotAddr sl2) = 0#u64 ∨ IsSlot th (prevOf (L.mem s) (cslotAddr sl2)) := by
    by_cases h : prevOf (L.mem s) (cslotAddr sl2) = 0#u64
    · exact Or.inl h
    · exact Or.inr (hslot _ (hM.prev_link hm2 h).1)
  have hNx2 : nextOf (L.mem s) (cslotAddr sl2) = 0#u64 ∨ IsSlot th (nextOf (L.mem s) (cslotAddr sl2)) := by
    rcases hM.next_mem hm2 with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr (hslot _ h)]
  have he1 : EncWf capability.Cap.Null := by rw [capAt_words] at ho1; exact decode_encWf ho1
  have he2 : EncWf c2 := by rw [capAt_words] at ho2; exact decode_encWf ho2
  have hca2 : CapRel c2 (absCap c2) := by
    obtain ⟨c', a', hc', hca', -⟩ := hR.abs_cap hA2
    rw [ho2] at hc'; cases eq_of_ok_eq hc'
    exact ⟨hca'.1, rfl⟩
  have hcv2 : CapValid th c2 := hV.abs hA2 ho2
  apply WP.spec_mono (swap_fields hP s .Null c2 _ _ hs1 hs2 hAne he1 he2 (Or.inl hp1) (Or.inl hn1) hPx2 hNx2)
  intro s' hW
  have hW' : ∀ x, IsSlot th x →
      capAt (L.mem s') x = (if x = cslotAddr sl2 then ok .Null else if x = cslotAddr sl1 then ok c2
        else capAt (L.mem s) x) ∧
      prevOf (L.mem s') x = (if nextOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ x = nextOf (L.mem s) (cslotAddr sl2)
        then cslotAddr sl1 else if x = cslotAddr sl2 then 0#u64
        else if x = cslotAddr sl1 then prevOf (L.mem s) (cslotAddr sl2) else prevOf (L.mem s) x) ∧
      nextOf (L.mem s') x = (if prevOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ x = prevOf (L.mem s) (cslotAddr sl2)
        then cslotAddr sl1 else if x = cslotAddr sl2 then 0#u64
        else if x = cslotAddr sl1 then nextOf (L.mem s) (cslotAddr sl2) else nextOf (L.mem s) x) ∧
      revOf (L.mem s') x = (if x = cslotAddr sl2 then revOf (L.mem s) (cslotAddr sl1)
        else if x = cslotAddr sl1 then revOf (L.mem s) (cslotAddr sl2) else revOf (L.mem s) x) ∧
      fbOf (L.mem s') x = (if x = cslotAddr sl2 then fbOf (L.mem s) (cslotAddr sl1)
        else if x = cslotAddr sl1 then fbOf (L.mem s) (cslotAddr sl2) else fbOf (L.mem s) x) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hW x hx
    refine ⟨h1, ?_, ?_, h4, h5⟩
    · rw [h2]; simp only [hp1, hn1, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    · rw [h3]; simp only [hp1, hn1, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
  -- the spec
  have hcap1 : ∀ x, IsSlot th x → capAt (L.mem (wrCap (L := L) s (cslotAddr sl1) c2)) x =
      if x = cslotAddr sl1 then ok c2 else capAt (L.mem s) x := by
    intro x hx; rw [capAt_wrCap hP s hs1 he2 hx]
  obtain ⟨σ1, h1, hR1, hV1, hσ1, -⟩ := StateRel.update_abs_slot hR hV hP hA1 hca2 hcv2 hcap1
  have hcap2 : ∀ x, IsSlot th x → capAt (L.mem s') x =
      if x = cslotAddr sl2 then ok .Null
      else capAt (L.mem (wrCap (L := L) s (cslotAddr sl1) c2)) x := by
    intro x hx
    rw [(hW x hx).1, capAt_wrCap hP s hs1 he2 hx]
  obtain ⟨σ2, h2, hR2, hV2, hσ2, -⟩ := StateRel.update_abs_slot hR1 hV1 hP hA2
    (show CapRel .Null .nullCap from ⟨trivial, rfl⟩) trivial hcap2
  have hio : σ2.isOriginalCap = σ.isOriginalCap := by rw [hσ2, hσ1]
  have hcdt : σ2.cdt = σ.cdt := by rw [hσ2, hσ1]
  have hsw := capSwap_eq h1 h2 hio hcdt
  have hRen := RenLinks.swap1 hP hM hs1 hm1 hm2 hon2 (fun x hx => ⟨(hW' x hx).1, (hW' x hx).2.1, (hW' x hx).2.2.1⟩)
  refine ⟨_, renG G (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)), hsw,
    StateRel.of_kheap hR2 rfl, hV2, MdbLinks.rename hM hRen, ?_, ?_, rfl, ?_, ?_, ?_, fun x hx => (hW' x hx).1, ?_⟩
  · refine CdtRel.swap hP hC _ hA1 hA2 hne ?_ ?_ ?_
    · exact swap_cdt_eq σ _ _ hne
    · exact swap_io_eq σ _ _ hne
    · intro x hx
      rw [(hW x hx).2.2.2.1]
      by_cases e2 : x = cslotAddr sl2
      · rw [if_pos e2, e2, Equiv.swap_apply_right]
      · by_cases e1 : x = cslotAddr sl1
        · rw [if_neg e2, if_pos e1, e1, Equiv.swap_apply_left]
        · rw [if_neg e2, if_neg e1, Equiv.swap_apply_of_ne_of_ne e1 e2]
  · refine MdbInv.rename hM hI _ hRen.e0 hRen.next ?_ ?_ ?_
    · intro a ha
      have ha1 : a ≠ cslotAddr sl1 := fun e => hm1 (e ▸ ha)
      by_cases h2 : a = cslotAddr sl2
      · subst h2
        rw [Equiv.swap_apply_right]
        have := (hW' _ hs1).1
        rw [if_neg hAne, if_pos rfl] at this
        rw [capV_of_capAt this, capV_of_capAt ho2]; exact ⟨rfl, rfl⟩
      · rw [Equiv.swap_apply_of_ne_of_ne ha1 h2]
        have := (hW' _ (hslot a ha)).1
        rw [if_neg h2, if_neg ha1] at this
        have e : capV (L.mem s') a = capV (L.mem s) a := by
          have h1 := capAt_capV (L.mem s') a
          rw [this, capAt_capV] at h1
          exact (eq_of_ok_eq h1).symm
        rw [e]; exact ⟨rfl, rfl⟩
    · intro a ha
      have ha1 : a ≠ cslotAddr sl1 := fun e => hm1 (e ▸ ha)
      by_cases h2 : a = cslotAddr sl2
      · subst h2; rw [Equiv.swap_apply_right, (hW' _ hs1).2.2.2.1, if_neg hAne, if_pos rfl]
      · rw [Equiv.swap_apply_of_ne_of_ne ha1 h2, (hW' _ (hslot a ha)).2.2.2.1, if_neg h2, if_neg ha1]
    · intro a ha
      have ha1 : a ≠ cslotAddr sl1 := fun e => hm1 (e ▸ ha)
      by_cases h2 : a = cslotAddr sl2
      · subst h2; rw [Equiv.swap_apply_right, (hW' _ hs1).2.2.2.2, if_neg hAne, if_pos rfl]
      · rw [Equiv.swap_apply_of_ne_of_ne ha1 h2, (hW' _ (hslot a ha)).2.2.2.2, if_neg h2, if_neg ha1]
  · rw [(hW' _ hs2).2.1]
    have g : ¬ (nextOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ cslotAddr sl2 = nextOf (L.mem s) (cslotAddr sl2)) := by
      rintro ⟨-, h⟩
      rcases hM.next_mem hm2 with h' | ⟨-, h'⟩
      · rw [← h] at h'; exact hs2.ne_zero hP h'
      · exact h' h.symm
    rw [if_neg g, if_pos rfl]
  · rw [(hW' _ hs2).2.2.1]
    have g : ¬ (prevOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ cslotAddr sl2 = prevOf (L.mem s) (cslotAddr sl2)) := by
      rintro ⟨h0, h⟩
      have := (hM.prev_link hm2 h0).2
      rw [← h] at this
      rcases hM.next_mem hm2 with h' | ⟨-, h'⟩
      · rw [this] at h'; exact hs2.ne_zero hP h'
      · exact h' this
    rw [if_neg g, if_pos rfl]
  · intro x hx hx1 hx2 _ hxn
    have hxm : x ∉ G.chains.flatten := by
      intro h; obtain ⟨-, c, hc, hcn⟩ := (hM.members _).1 h; rw [hxn] at hc; exact hcn (eq_of_ok_eq hc).symm
    have g1 : ¬ (nextOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ x = nextOf (L.mem s) (cslotAddr sl2)) := by
      rintro ⟨h0, h⟩; exact hxm (h ▸ (hM.next_link hm2 h0).1)
    have g2 : ¬ (prevOf (L.mem s) (cslotAddr sl2) ≠ 0#u64 ∧ x = prevOf (L.mem s) (cslotAddr sl2)) := by
      rintro ⟨h0, h⟩; exact hxm (h ▸ (hM.prev_link hm2 h0).1)
    rw [(hW' x hx).2.1, (hW' x hx).2.2.1, if_neg g1, if_neg g2, if_neg hx2, if_neg hx1, if_neg hx2, if_neg hx1]
    exact ⟨rfl, rfl⟩
  · refine MdbStep.rename hM _ (fun a ha => ?_) (fun a ha P L4 L3 L2 L1 hok => ?_)
    all_goals have ha1 : a ≠ cslotAddr sl1 := fun e => hm1 (e ▸ ha)
    by_cases h2 : a = cslotAddr sl2
    · subst h2
      rw [Equiv.swap_apply_right, (hW' _ hs1).2.2.2.1, if_neg hAne, if_pos rfl]
      have := (hW' _ hs1).1
      rw [if_neg hAne, if_pos rfl] at this
      rw [capV_of_capAt this, capV_of_capAt ho2]; exact ⟨CapAlike.refl _, rfl⟩
    · rw [Equiv.swap_apply_of_ne_of_ne ha1 h2, (hW' _ (hslot a ha)).2.2.2.1, if_neg h2, if_neg ha1]
      have := (hW' _ (hslot a ha)).1
      rw [if_neg h2, if_neg ha1] at this
      have e : capV (L.mem s') a = capV (L.mem s) a := by
        have h1 := capAt_capV (L.mem s') a
        rw [this, capAt_capV] at h1
        exact (eq_of_ok_eq h1).symm
      rw [e]; exact ⟨CapAlike.refl _, rfl⟩
    by_cases h2 : a = cslotAddr sl2
    · subst h2
      rw [Equiv.swap_apply_right]
      have := (hW' _ hs1).1
      rw [if_neg hAne, if_pos rfl] at this
      rw [capV_of_capAt this]; rw [capV_of_capAt ho2] at hok; exact hok
    · rw [Equiv.swap_apply_of_ne_of_ne ha1 h2]
      have := (hW' _ (hslot a ha)).1
      rw [if_neg h2, if_neg ha1] at this
      have e : capV (L.mem s') a = capV (L.mem s) a := by
        have h1 := capAt_capV (L.mem s') a
        rw [this, capAt_capV] at h1
        exact (eq_of_ok_eq h1).symm
      rw [e]; exact hok

end

/-! ## Replacing a cap by a zombie in place -/

theorem srB_zombie (p zt n : U64) (b : capability.Cap) : srB (.Zombie p zt n) b = false :=
  srB_of_eq (by unfold objects.same_region_as; rfl)

theorem chunkL_zap {R R' : U64 → U64 → Bool} {x : U64} :
    ∀ {L : List U64}, Mdb.ChunkL R L → (∀ a w, a ∈ L → w ∈ L → a ≠ x → R' a w = R a w) →
      (∀ w, R' x w = false) → Mdb.ChunkL R' L
  | [], _, _, _ => trivial
  | a :: L, ⟨hca, hL⟩, hR, hx => by
    refine ⟨?_, chunkL_zap hL (fun b w hb hw => hR b w (List.mem_cons_of_mem _ hb) (List.mem_cons_of_mem _ hw)) hx⟩
    by_cases hax : a = x
    · subst hax
      clear hca hL hR
      induction L with
      | nil => trivial
      | cons v L ih => exact ⟨fun _ w _ => hx w, ih⟩
    · have hsub : ∀ w ∈ L, R' a w = R a w := fun w hw => hR a w (List.mem_cons_self) (List.mem_cons_of_mem _ hw) hax
      clear hL hR hx
      induction L with
      | nil => trivial
      | cons v L ih =>
        obtain ⟨h1, h2⟩ := hca
        refine ⟨fun hv w hw => ?_, ih h2 (fun w hw => hsub w (List.mem_cons_of_mem _ hw))⟩
        rw [hsub v List.mem_cons_self] at hv
        rw [hsub w (List.mem_cons_of_mem _ hw)]
        exact h1 hv w hw

/-- **`MdbInv` when the cap of the linked slot `x` becomes a zombie** in
place: the old cap has no other cap in its region, and no badge; the
untyped caps containing it contain the zombie. -/
theorem MdbInv.zombify {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hI : MdbInv mem G) {x : U64} (hx : x ∈ G.chains.flatten)
    (hl : ∀ y, IsSlot th y → prevOf mem' y = prevOf mem y ∧ nextOf mem' y = nextOf mem y ∧
      revOf mem' y = revOf mem y ∧ fbOf mem' y = fbOf mem y)
    (hcap : ∀ y, IsSlot th y → y ≠ x → capV mem' y = capV mem y)
    {p zt n : U64} (hZ : capV mem' x = .Zombie p zt n)
    (hbx : isBadged (capV mem x) = false) (hbf : badgeF (capV mem x) = 0#u64)
    (h1 : ∀ y ∈ G.chains.flatten, y ≠ x → srB (capV mem y) (.Zombie p zt n) = srB (capV mem y) (capV mem x))
    (h2 : ∀ y ∈ G.chains.flatten, y ≠ x → srB (capV mem x) (capV mem y) = false) :
    MdbInv mem' G := by
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hrev : ∀ y ∈ G.chains.flatten, revOf mem' y = revOf mem y := fun y hy => (hl y (hslot y hy)).2.2.1
  have hfb : ∀ y ∈ G.chains.flatten, fbOf mem' y = fbOf mem y := fun y hy => (hl y (hslot y hy)).2.2.2
  have hnx : ∀ y ∈ G.chains.flatten, nextOf mem' y = nextOf mem y := fun y hy => (hl y (hslot y hy)).2.1
  have hcv : ∀ y ∈ G.chains.flatten, y ≠ x → capV mem' y = capV mem y := fun y hy hyx => hcap y (hslot y hy) hyx
  -- `is_mdb_parent_of` with the zombie as the child
  have hpm_to : ∀ a ∈ G.chains.flatten, a ≠ x → isPM mem' a x = isPM mem a x := by
    intro a ha hax
    unfold isPM isPF
    rw [hrev a ha, hcv a ha hax, hZ, hfb x hx, h1 a ha hax]
    by_cases hb : isBadged (capV mem a) = true
    · have e : badgeF (capability.Cap.Zombie p zt n) = 0#u64 := rfl
      simp only [hb, ↓reduceIte, e, hbf]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
  have hpm_from : ∀ w, isPM mem' x w = false := by
    intro w; unfold isPM isPF; rw [hZ, srB_zombie]; simp
  have hpm_other : ∀ a ∈ G.chains.flatten, ∀ w ∈ G.chains.flatten, a ≠ x → w ≠ x → isPM mem' a w = isPM mem a w := by
    intro a ha w hw hax hwx
    unfold isPM; rw [hrev a ha, hcv a ha hax, hcv w hw hwx, hfb w hw]
  have hnodesc : ∀ y, ¬ Mdb.Desc G.par y x := by
    intro y hy
    have hpm := hI.desc x y hy
    have hym := (desc_mem hM hy).1
    have hyx : y ≠ x := by
      rintro rfl
      obtain ⟨ch, hch, hxch⟩ := List.mem_flatten.1 hx
      exact Mdb.not_desc_self (hM.tree.seg ch hch) ((List.nodup_flatten.1 hM.tree.nodup).1 _ hch) hxch hy
    unfold isPM isPF at hpm
    rw [h2 y hym hyx] at hpm
    simp at hpm
  refine ⟨fun c q hq => by rw [hrev q (hM.tree.par_mem c q hq).2]; exact hI.orig c q hq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a y hy
    obtain ⟨hym, ham⟩ := desc_mem hM hy
    by_cases hax : a = x
    · subst hax; exact absurd hy (hnodesc y)
    by_cases hyx : y = x
    · subst hyx; rw [hpm_to a ham hax]; exact hI.desc a y hy
    · rw [hpm_other a ham y hym hax hyx]; exact hI.desc a y hy
  · intro y hy hn a ha hnd
    rw [hnx y hy] at hn hnd ⊢
    have ham : a ∈ G.chains.flatten := by
      rcases ha with rfl | h
      · exact hy
      · exact (desc_mem hM h).2
    have hnm : nextOf mem y ∈ G.chains.flatten := by
      rcases hM.next_mem hy with h | ⟨h, -⟩
      · exact absurd h hn
      · exact h
    by_cases hax : a = x
    · subst hax; exact hpm_from _
    by_cases hwx : nextOf mem y = x
    · rw [hwx] at hnd ⊢; rw [hpm_to a ham hax]; have := hI.after y hy hn a ha; rw [hwx] at this; exact this hnd
    · rw [hpm_other a ham _ hnm hax hwx]; exact hI.after y hy hn a ha hnd
  · intro ch hch
    have hchm : ∀ a ∈ ch, a ∈ G.chains.flatten := fun a ha => List.mem_flatten.2 ⟨ch, hch, ha⟩
    refine chunkL_zap (x := x) (hI.chunk ch hch) (fun a w ha hw hax => srF_congr ?_
      (by rw [hcv a (hchm a ha) hax]) (hrev a (hchm a ha))) (fun w => ?_)
    · unfold srM
      rw [hcv a (hchm a ha) hax]
      by_cases hwx : w = x
      · subst hwx; rw [hZ, h1 a (hchm a ha) hax]
      · rw [hcv w (hchm w hw) hwx]
    · rw [srF_nf (by rw [hZ]; rfl)]; unfold srM; rw [hZ, srB_zombie]
  · intro y hy hn hb hs hbd hbd0
    rw [hnx y hy] at hn hs hbd hbd0 ⊢
    have hnm : nextOf mem y ∈ G.chains.flatten := by
      rcases hM.next_mem hy with h | ⟨h, -⟩
      · exact absurd h hn
      · exact h
    by_cases hyx : y = x
    · subst hyx; rw [hZ] at hb; simp [isBadged] at hb
    by_cases hwx : nextOf mem y = x
    · rw [hwx, hZ] at hbd0; simp [badgeF] at hbd0
    rw [hfb _ hnm]
    rw [hcv y hy hyx] at hb hbd
    rw [hcv _ hnm hwx] at hbd hbd0
    unfold srM at hs; rw [hcv y hy hyx, hcv _ hnm hwx] at hs
    exact hI.badges y hy hn hb hs hbd hbd0
  · intro y hy hu
    by_cases hyx : y = x
    · subst hyx; rw [hZ] at hu; simp [isUt] at hu
    · rw [hcv y hy hyx] at hu; rw [hrev y hy]; exact hI.utrev y hy hu
  · intro y hy hz
    by_cases hyx : y = x
    · subst hyx; rw [hZ] at hz; simp [isZb] at hz
    · rw [hcv y hy hyx] at hz; unfold srM; rw [hcv y hy hyx]; exact hI.self y hy hz

end

end Fl4Proofs.P3
