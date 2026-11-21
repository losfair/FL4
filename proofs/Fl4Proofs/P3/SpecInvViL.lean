/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi3): **valid_idle across the untyped
and MakePool performs** (vi2's handoff item 3; spec side only; imports SpecInvViK and ut8's
SpecInvUtP6 for the decode facts).

* Detype: **`vi_detype`** (a set containing neither `N` nor `S` keeps `VIT`: `ObjOK` is per
  object), **`vi_deleteObjects`** (region `delR ptr bits ∌ N, S`).
* Retype: `objOK_dflt` (a default object at `p ∉ {N, S}` satisfies `ObjOK`: unbound TCB /
  SC, empty queues), `vi_retype_kh`, **`vi_retypeRegionWith_p`** (targets hold no object, so
  they are neither `N` nor `S`, which are objects).
* `vi_resetUntypedCap` (the reset deletes the held untyped's region), `vi_utBody`,
  **`vi_invokeUntyped`** (ut1's `utRet_fresh` / `utRet_fresh_after_reset`), **`vi_makePool`**.
  The region facts come from the entry's `IO (fun _ => N)` / `IrqOutV (fun _ => S)`: the
  untyped cap is held, and an untyped cap's `covR` is its region (l4v: `invoke_untyped_invs`
  uses `valid_global_refs` for the same: idle_thread_ptr / idle_sc_ptr ∉ untyped_range).
-/
import Fl4Proofs.P3.SpecInvViK
import Fl4Proofs.P3.SpecInvUtP6
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Detype -/

theorem vi_detype (D : Set ObjRef) {σ : State Unit} (h : VIT N S T b σ) (hN : N ∉ D) (hS : S ∉ D) :
    VIT N S T b (detype D σ) := by
  have hk : ∀ q, (detype D σ).kheap q = if q ∈ D then none else σ.kheap q := fun _ => rfl
  obtain ⟨h1, h2, h3, ⟨x, hx⟩, ⟨sc, n, hs⟩, h6⟩ := h
  refine ⟨h1, h2, h3, ⟨x, by rw [hk, if_neg hN]; exact hx⟩, ⟨sc, n, by rw [hk, if_neg hS]; exact hs⟩,
    fun p o hp => ?_⟩
  rw [hk] at hp
  split_ifs at hp
  exact h6 p o hp

theorem vi_deleteObjects (ptr : Word) (bits : Nat) (hN : N ∉ delR ptr bits) (hS : S ∉ delR ptr bits) :
    IK (VIT N S T b) (deleteObjects (Z := Unit) ptr bits) := by
  intro σ hσ y hy
  unfold deleteObjects at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : VIT N S T b y1.2 :=
    (show IK (VIT N S T b) (doMachineOp (Z := Unit) (freeMemory ptr bits)) by vi_auto) σ hσ y1 h1
  rw [Set.mem_singleton_iff.1 hy]
  exact vi_detype (delR ptr bits) hb1 hN hS

/-! ## Retype -/

theorem objOK_dflt {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) {p : ObjRef}
    (hN : p ≠ N) (hS : p ≠ S) : ObjOK N S N p (defaultObject ty dev o d) := by
  cases ty <;> simp_all [defaultObject, ObjOK, defaultTcb, defaultSchedContext, defaultEp, defaultNotification,
    defaultNtfn, Endpoint.epQueue, Ntfn.ntfnQueue]

theorem vi_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : VI N S b σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none) (hd : ∀ p, p ≠ N → p ≠ S → ObjOK N S N p dO) :
    VI N S b { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  have hk : ∀ q, ({ σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } :
      State Unit).kheap q = if q ∈ ps then some dO else σ.kheap q := fun q => foldr_upd ps dO σ.kheap q
  obtain ⟨h1, h2, h3, ⟨x, hx⟩, ⟨sc, n, hs⟩, h6⟩ := h
  have hNp : N ∉ ps := fun hm => by rw [hF N hm] at hx; cases hx
  have hSp : S ∉ ps := fun hm => by rw [hF S hm] at hs; cases hs
  refine ⟨h1, h2, h3, ⟨x, by rw [hk, if_neg hNp]; exact hx⟩, ⟨sc, n, by rw [hk, if_neg hSp]; exact hs⟩,
    fun p o hp => ?_⟩
  rw [hk] at hp
  split_ifs at hp with hm
  · cases hp
    exact hd p (fun e => hNp (e ▸ hm)) (fun e => hSp (e ▸ hm))
  · exact h6 p o hp

theorem vi_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ retPtrs ptr n (bA ty o), σ.kheap q = none) (hσ : VI N S b σ) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1, VI N S b y.2 := by
  intro y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show VI N S b z3.2
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets_vi hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets_vi hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact vi_retype_kh _ _ hσ hF fun p h1 h2 => objOK_dflt hty dev o _ h1 h2
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## The untyped invocation -/

theorem vi_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {bb : ObjRef} {n fi : Nat}
    (hc : capAt σ s = some (.untypedCap dev bb n fi)) (hN : N ∉ delR bb n) (hS : S ∉ delR bb n)
    (hσ : VI N S b σ) : ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, VI N S b y.2 := by
  intro y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s'⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev bb n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hσ
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev bb n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, objRefOf] at hz
    have hz0 : VI N S b z.2 := vi_deleteObjects bb n hN hS σ hσ z hz
    refine (?_ : IKE (VI N S b) _) z.2 hz0 y hy
    try dsimp only
    vi_auto

/-- The untyped retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem vi_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hfr : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none)
    (hσ : VI N S b σ) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) σ).1, VI N S b x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : VI N S b x4.2 := vi_setCap _ _ _ hσ x4 hx4
  have hk4 := (setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := vi_retypeRegionWith_p fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  refine (?_ : IK (VI N S b) _) x5.2 hb5 _ hx
  vi_auto

/-- **`invoke_untyped`** from the decode's facts (`UtRetOK`, ut1) with `UtInv`, and the held
untyped's region excluding `N` and `S`. -/
theorem vi_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hσ : VI N S b σ) (hI : UtInv σ)
    (hok : UtRetOK σ ui)
    (hD : ∀ s dev bb n fi, capAt σ s = some (.untypedCap dev bb n fi) → N ∉ delR bb n ∧ S ∉ delR bb n) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, VI N S b y.2 := by
  intro y hy
  cases ui with
  | retype s reset base rb ty sz slots dev =>
    cases reset
    · have hfr := utRet_fresh hI hok
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
      replace hy := run_returnOk_bind_mem hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      exact vi_utBody s base rb ty sz slots dev σ hfr hσ x hx
    · have hok' := hok
      obtain ⟨bits, fi, hc, -, -, -, -, -⟩ := hok'
      simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
      rw [ExceptT.run_bind] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hd := hD s dev base bits fi hc
      have hbz := vi_resetUntypedCap s hc hd.1 hd.2 hσ z hz
      have hfz := utRet_fresh_after_reset hI hok z hz
      obtain ⟨r, s1⟩ := z
      cases r with
      | error e =>
        first
          | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
          | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
      | ok u =>
        try dsimp only at hy
        obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
        exact vi_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-! ## MakePool -/

theorem vi_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hσ : VI N S b σ)
    (hN : N ∉ delR frame page_bits) (hS : S ∉ delR frame page_bits) (hfr : frame ∈ delR frame page_bits) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, VI N S b y.2 := by
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 : VI N S b y1.2 := vi_deleteObjects frame page_bits hN hS σ hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    unfold deleteObjects at h1
    obtain ⟨z1, -, h1⟩ := h1
    rw [Set.mem_singleton_iff.1 h1]
    show (if frame ∈ delR frame page_bits then none else z1.2.kheap frame) = none
    rw [if_pos hfr]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : VI N S b y3.2 := vi_setCap _ _ _ hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := vi_retypeRegionWith_p objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'
    exact hn3) hb3 y4 h4
  refine (?_ : IK (VI N S b) _) y4.2 hb4 y hy
  vi_auto

end

end Fl4Proofs.P3.SInvI
