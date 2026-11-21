/-
P3 (DESIGN.md §9), invariant line G1 (fo1): **`FT` across the untyped
invocation and MakePool** (spec side only).

The two heap writes that bypass `set_object`'s type assertion:
* `retype_region` writes only addresses holding no object (ut1's
  `utRet_fresh` / `utRet_fresh_after_reset`), so the owner's TCB is kept
  (`oi_retypeRegionWith_p`);
* `delete_objects` of a childless untyped's region (the reset, MakePool's
  parent): the owner holds a thread cap (`FT`), and ut4's UtCh makes a cap
  naming an object of the region a CDT descendant of the untyped, so the owner
  is outside the region (**`owner_out`**, il2's `rqDet_of_live` pattern;
  `oi_deleteObjects_p`).
`IL` is il2's (`il_invokeUntyped`, `il_makePool`, at `K = oL σ ++ K`); the owner
part is `oi_invokeUntyped` / `oi_makePool` (the OI skeleton of il2's proofs).
Tops: **`fo_invokeUntyped`**, **`fo_makePool`**.
-/
import Fl4Proofs.P3.SpecInvFoD
import Fl4Proofs.P3.SpecInvNtfnQLA
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {Qo : Option ObjRef}

/-- **The owner lies outside a childless untyped's region** (it holds a thread cap; UtCh). -/
theorem owner_out {σ : State Unit} (hU : UtInv'' σ) {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) {t : ObjRef}
    (hT : HasTC σ t) : t ∉ delR b n := by
  obtain ⟨s, hs⟩ := hT
  intro hm
  exact desc_noKids hk (hU.2.1 u dev b n fi hc s (.threadCap t) t hs
    (objRefs_sub_capRng _ (by simp [objRefs])) hm)

theorem oi_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (h : ∀ t, Qo = some t → t ∉ delR ptr bits) : IKp (OI Qo) σ (deleteObjects (Z := Unit) ptr bits) := by
  intro hσ y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  rw [e]
  refine ⟨hσ.1, fun t ht => ?_⟩
  obtain ⟨x, hx⟩ := hσ.2 t ht
  exact ⟨x, by show (if t ∈ delR ptr bits then none else σ.kheap t) = _; rw [if_neg (h t ht)]; exact hx⟩

theorem oi_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ retPtrs ptr n (bA ty o), σ.kheap q = none) :
    IKp (OI Qo) σ (retypeRegionWith (Z := Unit) bA ptr n o ty dev) := by
  intro hσ y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show OI Qo z3.2
  unfold NonDet.when at h3
  split at h3
  · obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    refine ⟨hσ.1, fun t ht => ?_⟩
    obtain ⟨x, hx⟩ := hσ.2 t ht
    refine ⟨x, ?_⟩
    show (List.foldr _ σ.kheap _) t = _
    rw [foldr_upd, if_neg (fun hm => by rw [hF t hm] at hx; cases hx)]
    exact hx
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

set_option maxHeartbeats 4000000 in
theorem oi_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : capAt σ s = some (.untypedCap dev b n fi)) (h : ∀ t, Qo = some t → t ∉ delR b n) :
    IKp (OI Qo) σ (ExceptT.run (resetUntypedCap (Z := Unit) s)) := by
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
    simp only [bitsOf, objRefOf] at hz
    have hz0 := oi_deleteObjects_p b n σ h hσ z hz
    refine (?_ : OIKE Qo _) z.2 hz0 y hy
    try dsimp only
    oi_auto

set_option maxHeartbeats 4000000 in
theorem oi_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit)
    (hfr : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) (hσ : OI Qo σ) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) σ).1, OI Qo x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : OI Qo x4.2 := oi_setCap _ _ _ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := oi_retypeRegionWith_p (Qo := Qo) fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 : OI Qo x6.2 := oi_initArchObjects _ _ _ _ _ _ _ hb5 x6 hx6
  exact ik_mapMx (fun _ => oi_createCap _ _ _ _ _) _ _ hb6 x hx

set_option maxHeartbeats 4000000 in
/-- The owner part of `invoke_untyped`. -/
theorem oi_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hσ : OI Qo σ) (hU : UtInv'' σ)
    (hok : UtGapOK (uV σ) ui) (hT : ∀ t, Qo = some t → HasTC σ t) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, OI Qo y.2 := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok1 : UtRetOK σ (.retype s reset base rb ty sz slots dev) := utRetOK_of_V h1
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok1
  cases reset
  · have hfr := utRet_fresh hU.1.1 hok1
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact oi_utBody s base rb ty sz slots dev σ hfr hσ x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := oi_resetUntypedCap s hc (fun t ht => owner_out hU hc (hr rfl) (hT t ht)) hσ z hz
    have hfz := utRet_fresh_after_reset hU.1.1 hok1 z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact oi_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-- **`invoke_untyped` keeps `ILF K`**. -/
theorem fo_invokeUntyped {K : List ObjRef} (ui : UntypedInvocation) (σ : State Unit) (hσ : ILF K σ)
    (hU : UtInv'' σ) (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, ILF K y.2 := fun y hy =>
  ft_back (il_invokeUntyped ui σ (il_oL hσ.1 hσ.2) hU hok y hy)
    (oi_invokeUntyped ui σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ hU hok (fun t ht => (hσ.2 t ht).2) y hy)

/-- The owner part of MakePool. -/
theorem oi_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hσ : OI Qo σ)
    (hU : UtInv'' σ) (hok : MpOKN (uV σ) (.makePool frame slot parent base)) (hT : ∀ t, Qo = some t → HasTC σ t) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, OI Qo y.2 := by
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hfr : frame ∈ delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := UtWf.fit (σ := σ) hU.1.1.2.1 hc
    exact (mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := oi_deleteObjects_p frame page_bits σ (fun t ht => owner_out hU hc' hk (hT t ht)) hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := Fl4Proofs.P3.SInv.deleteObjects_out h1
    rw [e1]; show (if frame ∈ delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hfr]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : OI Qo y3.2 := oi_setCap _ _ _ hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := oi_retypeRegionWith_p (Qo := Qo) objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'; exact hn3) hb3 y4 h4
  refine (?_ : OIK Qo _) y4.2 hb4 y hy
  oi_auto

/-- **MakePool keeps `ILF K`**. -/
theorem fo_makePool {K : List ObjRef} (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit)
    (hσ : ILF K σ) (hU : UtInv'' σ) (hok : MpOKN (uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, ILF K y.2 :=
  fun y hy => ft_back (il_makePool frame slot parent base σ (il_oL hσ.1 hσ.2) hU hok y hy)
    (oi_makePool frame slot parent base σ ⟨rfl, fun t ht => (hσ.2 t ht).1⟩ hU hok (fun t ht => (hσ.2 t ht).2) y hy)

end

end Fl4Proofs.P3.SInvF
