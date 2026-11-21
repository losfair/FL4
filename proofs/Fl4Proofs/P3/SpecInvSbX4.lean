/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **the untyped and arch gap
performs** keep `ScInv` (spec side only; imports SpecInvSbX3 and ut8's
SpecInvUtP6 for the decode facts `GapOKN`).

* The view algebra: `symB_of_unb` (a binding view changed only at points
  unbound before and after keeps `SymB`).
* Detype: `sc_detype` (a set holding no bound TCB / SC), `sc_deleteObjects_p`;
  `unb_of_live`: **`ScLive` + UtInv3's UtCh**: a childless untyped's region holds
  no bound TCB / SC (a cap naming it would be a CDT child; a global object lies
  outside every cap's range, the untyped's own included).
* Retype: `sc_retype_kh` (default objects at addresses holding no object: the
  default TCB / SC is unbound, the default SC inactive and not sporadic),
  `sc_retypeRegionWith_p`.
* `sc_resetUntypedCap`, `sc_utBody`, **`sc_invokeUntyped`** (ut1's
  `utRet_fresh` / `utRet_fresh_after_reset`), **`sc_makePool`**,
  `si_archNonMP` (every other arch perform is a binding frame).
-/
import Fl4Proofs.P3.SpecInvSbX3
import Fl4Proofs.P3.SpecInvUtP6
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The view algebra -/

theorem symB_of_unb {b b' : ObjRef → BV} (h : SymB b)
    (hd : ∀ p, b' p = b p ∨ (¬ Bound (b p) ∧ ¬ Bound (b' p))) : SymB b' := by
  refine ⟨fun u c hu => ?_, fun p u hp => ?_⟩
  · rcases hd u with e | ⟨-, hn⟩
    · rw [e] at hu
      have h1 := h.1 u c hu
      rcases hd c with e' | ⟨hn', -⟩
      · rw [e']; exact h1
      · exact absurd ⟨u, Or.inr h1⟩ hn'
    · exact absurd ⟨c, Or.inl hu⟩ hn
  · rcases hd p with e | ⟨-, hn⟩
    · rw [e] at hp
      have h1 := h.2 p u hp
      rcases hd u with e' | ⟨hn', -⟩
      · rw [e']; exact h1
      · exact absurd ⟨p, Or.inl h1⟩ hn'
    · exact absurd ⟨u, Or.inr hp⟩ hn

theorem bv_congr {k k' : KHeap} {p : ObjRef} (h : k' p = k p) : bv k' p = bv k p := by
  unfold bv; rw [h]

theorem notBound_none {k : KHeap} {p : ObjRef} (h : k p = none) : ¬ Bound (bv k p) := by
  rintro ⟨c, hc | hc⟩
  · obtain ⟨x, hx, -⟩ := bv_t.1 hc; rw [h] at hx; cases hx
  · obtain ⟨y, n, hy, -⟩ := bv_s.1 hc; rw [h] at hy; cases hy

theorem notBound_of {k : KHeap} {p : ObjRef} {o : KernelObject} (hk : k p = some o)
    (hT : ∀ x, o = .tcb x → x.tcbSchedContext = none) (hS : ∀ y n, o = .schedContext y n → y.scTcb = none) :
    ¬ Bound (bv k p) := by
  rintro ⟨c, hc | hc⟩
  · obtain ⟨x, hx, e⟩ := bv_t.1 hc
    rw [hk] at hx
    rw [hT x (Option.some.inj hx)] at e; cases e
  · obtain ⟨y, n, hy, e⟩ := bv_s.1 hc
    rw [hk] at hy
    rw [hS y n (Option.some.inj hy)] at e; cases e

/-! ## Detype -/

theorem sc_detype {σ : State Unit} (D : Set ObjRef) (hI : ScInv σ) (hD : ∀ p ∈ D, ¬ Bound (bv σ.kheap p)) :
    ScInv (detype D σ) := by
  have hk : ∀ x, (detype D σ).kheap x = if x ∈ D then none else σ.kheap x := fun _ => rfl
  rw [scInv_iff] at hI ⊢
  refine ⟨symB_of_unb hI.1 fun p => ?_, fun p y n hp => ?_⟩
  · by_cases h : p ∈ D
    · exact Or.inr ⟨hD p h, notBound_none (by rw [hk, if_pos h])⟩
    · exact Or.inl (bv_congr (by rw [hk, if_neg h]))
  · rw [hk] at hp
    split_ifs at hp
    exact hI.2 p y n hp

theorem deleteObjects_out' {ptr : Word} {bits : Nat} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (deleteObjects (Z := Unit) ptr bits σ).1) :
    ∃ s1 : State Unit, s1.kheap = σ.kheap ∧ y.2 = detype (SInvU.delR ptr bits) s1 := by
  unfold deleteObjects at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hk1 : y1.2.kheap = σ.kheap :=
    (ik_doMachineOp (P := fun s => s.kheap = σ.kheap) (fun _ _ h => h) _) σ rfl y1 h1
  exact ⟨y1.2, hk1, by rw [Set.mem_singleton_iff.1 hy]; rfl⟩

theorem sc_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hD : ∀ p ∈ SInvU.delR ptr bits, ¬ Bound (bv σ.kheap p)) : IKp ScInv σ (deleteObjects (Z := Unit) ptr bits) := by
  intro hσ y hy
  obtain ⟨s1, hk1, e⟩ := deleteObjects_out' hy
  rw [e]
  have h1 : ScInv s1 := scInv_of_br hσ (by rw [hk1]; exact BR.refl _)
  exact sc_detype _ h1 fun p hp => by rw [hk1]; exact hD p hp

/-- **No bound TCB / SC in a childless untyped's region** (`ScLive` and UtInv3's UtCh). -/
theorem unb_of_live {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : ScLive σ) {u : CslotPtr} {dev : Bool}
    {b : ObjRef} {n fi : Nat} (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) :
    ∀ p ∈ SInvU.delR b n, ¬ Bound (bv σ.kheap p) := by
  intro p hp hB
  rcases hL p hB with ⟨s, c, hs, hr⟩ | hout
  · exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c p hs (SInvU.objRefs_sub_capRng c hr) hp)
  · exact hout u _ hc hp

/-! ## Retype -/

theorem dflt_unb {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) :
    (∀ x, defaultObject ty dev o d = .tcb x → x.tcbSchedContext = none) ∧
    (∀ y n, defaultObject ty dev o d = .schedContext y n → y.scTcb = none ∧ rneQ y) := by
  cases ty with
  | untyped => exact absurd rfl hty
  | tcbObject => exact ⟨fun x h => (by cases h; rfl), fun y n h => (by cases h)⟩
  | schedContextObject =>
    refine ⟨fun x h => (by cases h), fun y n h => ?_⟩
    cases h
    exact ⟨rfl, fun h => by simp [defaultSchedContext, scActive, activeSc] at h⟩
  | _ => exact ⟨fun x h => (by cases h), fun y n h => (by cases h)⟩

theorem sc_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (hI : ScInv σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none)
    (hd : (∀ x, dO = .tcb x → x.tcbSchedContext = none) ∧ (∀ y n, dO = .schedContext y n → y.scTcb = none ∧ rneQ y)) :
    ScInv { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  have hk : ∀ q, ({ σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } :
      State Unit).kheap q = if q ∈ ps then some dO else σ.kheap q := fun q => SInvU.foldr_upd ps dO σ.kheap q
  rw [scInv_iff] at hI ⊢
  refine ⟨symB_of_unb hI.1 fun p => ?_, fun p y n hp => ?_⟩
  · by_cases h : p ∈ ps
    · exact Or.inr ⟨notBound_none (hF p h),
        notBound_of (by rw [hk, if_pos h]) hd.1 fun y n e => (hd.2 y n e).1⟩
    · exact Or.inl (bv_congr (by rw [hk, if_neg h]))
  · rw [hk] at hp
    split_ifs at hp
    · exact (hd.2 y n (Option.some.inj hp)).2
    · exact hI.2 p y n hp

theorem sc_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none) :
    IKp ScInv σ (retypeRegionWith (Z := Unit) bA ptr n o ty dev) := by
  intro hσ y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show ScInv z3.2
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets' hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets' hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact sc_retype_kh _ _ hσ hF (dflt_unb hty dev o _)
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## The untyped invocation -/

theorem sc_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi)) (hD : ∀ p ∈ SInvU.delR b n, ¬ Bound (bv σ.kheap p)) :
    IKp ScInv σ (ExceptT.run (resetUntypedCap (Z := Unit) s)) := by
  intro hσ y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := SInvU.run_liftE_bind_mem hy
  obtain ⟨cap, s'⟩ := x
  obtain ⟨hs, hcx⟩ := SInvU.getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := SInvU.run_returnOk_bind_mem hy
  replace hy := SInvU.run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hσ
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, objRefOf] at hz
    have hz0 : ScInv z.2 := sc_deleteObjects_p b n σ hD hσ z hz
    refine (?_ : SIKE _) z.2 hz0 y hy
    try dsimp only
    si_auto

/-- The untyped retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem sc_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    IKp ScInv σ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) := by
  intro hσ x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : ScInv x4.2 := (sik_of_sbk fun _ => sb_setCap _ _) _ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := sc_retypeRegionWith_p fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  refine (?_ : SIK _) x5.2 hb5 _ hx
  si_auto

/-- **`invoke_untyped`** from the decode's facts (`UtRetOK`, ut1) with `UtInv`, and,
for a reset, no bound TCB / SC in the region. -/
theorem sc_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hI : SInvU.UtInv σ)
    (hok : SInvU.UtRetOK σ ui)
    (hD : ∀ s dev b n fi, SInvU.capAt σ s = some (.untypedCap dev b n fi) → (∀ c, σ.cdt c ≠ some s) →
      ∀ p ∈ SInvU.delR b n, ¬ Bound (bv σ.kheap p)) :
    IKp ScInv σ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui)) := by
  intro hσ y hy
  cases ui with
  | retype s reset base rb ty sz slots dev =>
    cases reset
    · have hfr := SInvU.utRet_fresh hI hok
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
      replace hy := SInvU.run_returnOk_bind_mem hy
      obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
      exact sc_utBody s base rb ty sz slots dev σ hfr hσ x hx
    · have hok' := hok
      obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := hok'
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
      rw [ExceptT.run_bind] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hbz := sc_resetUntypedCap s hc (hD s dev base bits fi hc (hr rfl)) hσ z hz
      have hfz := SInvU.utRet_fresh_after_reset hI hok z hz
      obtain ⟨r, s1⟩ := z
      cases r with
      | error e =>
        first
          | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
          | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
      | ok u =>
        try dsimp only at hy
        obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
        exact sc_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-! ## MakePool and the other arch performs -/

theorem sc_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit)
    (hD : ∀ p ∈ SInvU.delR frame page_bits, ¬ Bound (bv σ.kheap p)) (hfr : frame ∈ SInvU.delR frame page_bits) :
    IKp ScInv σ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  intro hσ y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := sc_deleteObjects_p frame page_bits σ hD hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := deleteObjects_out' h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hfr]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : ScInv y3.2 := (sik_of_sbk fun _ => sb_setCap _ _) _ hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := sc_retypeRegionWith_p objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'
    exact hn3) hb3 y4 h4
  refine (?_ : SIK _) y4.2 hb4 y hy
  si_auto

/-- Every arch perform but MakePool is a binding frame. -/
theorem si_archNonMP (ai : Fl4ArchInvocation) (h : ∀ a, ai ≠ .spec (.invokeASIDControl a)) :
    SIKE (fl4ArchPerformInvocation (Z := Unit) ai) := by
  cases ai with
  | spec i =>
    cases i with
    | invokeASIDControl a => exact absurd rfl (h a)
    | _ => exact sike_of_sbke fun _ => by simp only [fl4ArchPerformInvocation, archPerformInvocation]; sb_auto
  | _ => exact sike_of_sbke fun _ => by simp only [fl4ArchPerformInvocation]; sb_auto

end

end Fl4Proofs.P3.SInvB
