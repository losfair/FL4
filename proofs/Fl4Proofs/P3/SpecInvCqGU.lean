/-
P3 (DESIGN.md §9), invariant line G1 (ctq11): **`RT` across the untyped
performs** (`invoke_untyped`, MakePool; spec side only), the leaves of the
`RT` family that read the state (SpecInvCqG).

* Detype (`rt_detype`, `rt_deleteObjects_p`): under `resume_cur_thread` the
  current thread's TCB has an SC, so it is live (`liveO`), and sl4's
  `noLive_reg` keeps every live object out of a childless untyped's region.
* Retype (`rt_retype_kh`, `rt_retypeRegionWith_p`): retyped addresses hold
  no object (UtInv3 freshness: `utRet_fresh`, `utRet_fresh_after_reset`),
  and the current thread's does, so it is not overwritten.
* **`rt_invokeUntyped`**, **`rt_makePool`**: the hypotheses of sl4's
  `sln_invokeUntyped` / `sln_makePool` at the perform state (sl's `ScLiveT`,
  `UtInv''`, the idle objects outside every cap's range, the decode's
  `UtGapOK` / `MpOKN`); no new premise.
-/
import Fl4Proofs.P3.SpecInvCqGF5
import Fl4Proofs.P3.SpecInvSlU
open Classical

namespace Fl4Proofs.P3.SInvQ.R11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Detype -/

theorem rt_detype (D : Set ObjRef) {σ : State Unit} (h : RT σ)
    (hD : ∀ p ∈ D, ∀ o, σ.kheap p = some o → ¬ liveO o) : RT (detype D σ) := by
  intro hs
  obtain ⟨x, hx, hn⟩ := h hs
  refine ⟨x, ?_, hn⟩
  show (if σ.curThread ∈ D then none else σ.kheap σ.curThread) = _
  rw [if_neg (fun hm => hD _ hm _ hx hn)]; exact hx

theorem rt_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hD : ∀ p ∈ SInvU.delR ptr bits, ∀ o, σ.kheap p = some o → ¬ liveO o) (hσ : RT σ) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits σ).1, RT y.2 := by
  intro y hy
  unfold deleteObjects at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have r1 : RT y1.2 := (ik_doMachineOp (P := RT) (fun _ _ h => h) _) σ hσ y1 h1
  have hk1 : y1.2.kheap = σ.kheap :=
    (ik_doMachineOp (P := fun s => s.kheap = σ.kheap) (fun _ _ h => h) _) σ rfl y1 h1
  rw [Set.mem_singleton_iff.1 hy]
  exact rt_detype _ r1 fun p hp o ho => hD p hp o (by rw [← hk1]; exact ho)

/-! ## Retype -/

theorem rt_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : RT σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none) :
    RT { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  intro hs
  obtain ⟨x, hx, hn⟩ := h hs
  refine ⟨x, ?_, hn⟩
  show ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap σ.curThread = _
  rw [foldr_upd ps dO σ.kheap, if_neg (fun hm => by rw [hF _ hm] at hx; cases hx)]; exact hx

/-- `retype_region` at addresses holding no object. -/
theorem rt_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none) (hσ : RT σ) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1, RT y.2 := by
  intro y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show RT z3.2
  unfold NonDet.when at h3
  split at h3
  · obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact rt_retype_kh _ _ hσ hF
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## The reset -/

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a slot holding an untyped whose region holds no live object. -/
theorem rt_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hD : ∀ p ∈ SInvU.delR b n, ∀ o, σ.kheap p = some o → ¬ liveO o) (hσ : RT σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, RT y.2 := by
  intro y hy
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
    have hz0 := rt_deleteObjects_p b n σ hD hσ z hz
    refine (?_ : RTKE _) z.2 hz0 y hy
    try dsimp only
    rt_auto

/-! ## The body -/

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset. -/
theorem rt_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) (hσ : RT σ) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) σ).1, RT x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : RT x4.2 := rt_setCap _ _ _ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := rt_retypeRegionWith_p fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 : RT x6.2 := (show RTK (initArchObjects (Z := Unit) ty dev rb slots.length sz x5.1) by rt_auto)
    x5.2 hb5 x6 hx6
  exact (show RTK (NonDet.mapMx (createCap (Z := Unit) ty sz s dev) (slots.zip x5.1)) by rt_auto) x6.2 hb6 x hx

variable {I : ObjRef × ObjRef}

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `RT`** (sl4's `sln_invokeUntyped` hypotheses). -/
theorem rt_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hσ : RT σ) (hS : ScLiveT I σ)
    (hU : UtInv'' σ) (h1 : IrqOutV (fun _ => I.1) (uV σ)) (h2 : IrqOutV (fun _ => I.2) (uV σ))
    (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, RT y.2 := by
  intro y hy
  obtain ⟨g1, -, -⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok1 : UtRetOK σ (.retype s reset base rb ty sz slots dev) := utRetOK_of_V g1
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok1
  cases reset
  · have hfr := utRet_fresh hU.1.1 hok1
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact rt_utBody s base rb ty sz slots dev σ hfr hσ x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hk := hr rfl
    have hbz := rt_resetUntypedCap s hc (noLive_reg hS hU h1 h2 hc hk) hσ z hz
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
      exact rt_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-! ## MakePool -/

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `RT`** (sl4's `sln_makePool` hypotheses). -/
theorem rt_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hσ : RT σ)
    (hS : ScLiveT I σ) (hU : UtInv'' σ) (h1 : IrqOutV (fun _ => I.1) (uV σ)) (h2 : IrqOutV (fun _ => I.2) (uV σ))
    (hok : MpOKN (uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, RT y.2 := by
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hfr : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  have hb1 := rt_deleteObjects_p frame page_bits σ (noLive_reg hS hU h1 h2 hc' hk) hσ y1 hy1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' hy1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hfr]
  obtain ⟨y2, hy2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt hy2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, hy3, hy⟩ := hy
  have hb3 : RT y3.2 := rt_setCap _ _ _ hb1 y3 hy3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out hy3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at hy4
  have hb4 := rt_retypeRegionWith_p objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'; exact hn3) hb3 y4 hy4
  refine (?_ : RTK _) y4.2 hb4 y hy
  rt_auto

end

end Fl4Proofs.P3.SInvQ.R11
