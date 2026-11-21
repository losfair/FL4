/-
P3 (DESIGN.md §9), invariant line G1 (ctq15): **EB across the performs**,
part 10: the Untyped retype (with or without reset) and MakePool keep `EB k`
(spec side only, outside the JAtZ cone). These arms may precede `handle_recv`
in the first phase, so `EB k` is kept for both `k`.

* TQ: ctq3's `tq_invokeUntyped` / `tq_makePool` (queued threads are runnable,
  so live, so named by a cap: `rqDet_of_live` with `IfLiveTN`, which il2's
  carried IfLiveT gives: ctq4's `ifLiveTN_of_ifLiveT`). T4: the generated
  `q4_invokeUntypedWith` / `q4_performAsidControlInvocation`.
* `SR k := SA ∧ RBk k`: the heap occurs only as "`t` is a runnable TCB" (the
  switch target, the release queue, the current thread under resume), so
  `sa_of_keep` / `rb_of_keep` apply. `detype` of a childless untyped's region
  removes no runnable TCB (`rnDet_of_live`: the same argument as
  `rqDet_of_live`); `retype_region` writes only addresses holding no object
  (ut1's `utRet_fresh` / `utRet_fresh_after_reset`), so no runnable TCB is
  overwritten. The rest by the generated `sa_*` / `rb_*` leaves.
-/
import Fl4Proofs.P3.SpecInvCqM1
import Fl4Proofs.P3.SpecInvCqL
import Fl4Proofs.P3.SpecInvCqGU
open Classical

namespace Fl4Proofs.P3.SInvQ.P15
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The heap-only part beside TQ and T4 -/

abbrev SR (k : Bool) (s : State Unit) : Prop := SA s ∧ RBk k s

theorem ike_and {A B : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (ha : IKE A m)
    (hb : IKE B m) : IKE (fun σ => A σ ∧ B σ) m :=
  fun σ h x hx => ⟨ha σ h.1 x hx, hb σ h.2 x hx⟩

theorem sr_keep {k : Bool} {σ σ' : State Unit} (h : SR k σ) (hk : ∀ t, RnH t σ.kheap → RnH t σ'.kheap)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hr : σ'.releaseQueue = σ.releaseQueue)
    (hq : σ'.readyQueues = σ.readyQueues) (hc : σ'.curThread = σ.curThread)
    (hi : σ'.idleThread = σ.idleThread) : SR k σ' :=
  ⟨sa_of_keep h.1 hk ha hr hq hc, rb_of_keep h.2 hk ha hr hq hc hi⟩

/-- **No runnable TCB in a childless untyped's region** (`rqDet_of_live` for any runnable TCB). -/
theorem rnDet_of_live {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : IfLiveTN σ)
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) :
    ∀ t, RnH t σ.kheap → t ∉ SInvU.delR b n := by
  intro t ⟨y, hy, hr⟩ hm
  have hl : y.tcbState ∉ ({.inactive, .idleThreadState} : Set ThreadState) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h] at hr <;> simp [runnable] at hr
  obtain ⟨s, c, hs, hr'⟩ := hL t y hy hl ⟨u, dev, b, n, fi, hc, hm⟩
  exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c t hs (SInvU.objRefs_sub_capRng c hr') hm)

theorem sr_detype {k : Bool} (D : Set ObjRef) {σ : State Unit} (h : SR k σ) (hD : ∀ t, RnH t σ.kheap → t ∉ D) :
    SR k (detype D σ) := by
  refine sr_keep h (fun t ht => ?_) rfl rfl rfl rfl rfl
  obtain ⟨x, hx, hr⟩ := ht
  refine ⟨x, ?_, hr⟩
  show (if t ∈ D then none else σ.kheap t) = _
  rw [if_neg (hD t ⟨x, hx, hr⟩)]; exact hx

theorem sr_deleteObjects_p {k : Bool} (ptr : Word) (bits : Nat) (σ : State Unit)
    (hD : ∀ t, RnH t σ.kheap → t ∉ SInvU.delR ptr bits) :
    IKp (SR k) σ (deleteObjects (Z := Unit) ptr bits) := by
  intro hσ y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  rw [e]
  exact sr_detype _ hσ hD

theorem sr_retype_kh {k : Bool} {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : SR k σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none) :
    SR k { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  refine sr_keep h (fun t ht => ?_) rfl rfl rfl rfl rfl
  obtain ⟨x, hx, hr⟩ := ht
  refine ⟨x, ?_, hr⟩
  show (ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap) t = _
  rw [SInvU.foldr_upd, if_neg (fun hm => by rw [hF t hm] at hx; cases hx)]; exact hx

/-- `retype_region` at addresses holding no object. -/
theorem sr_retypeRegionWith_p {k : Bool} (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat)
    (ty : ApiObjectType) (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none) :
    IKp (SR k) σ (retypeRegionWith (Z := Unit) bA ptr n o ty dev) := by
  intro hσ y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show SR k z3.2
  unfold NonDet.when at h3
  split at h3
  · obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact sr_retype_kh _ _ hσ hF
  · rw [Set.mem_singleton_iff.1 h3]; exact hσ

/-! ## The reset and the body -/

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a slot whose untyped region holds no runnable TCB. -/
theorem sr_resetUntypedCap {k : Bool} (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hD : ∀ t, RnH t σ.kheap → t ∉ SInvU.delR b n) :
    IKp (SR k) σ (ExceptT.run (resetUntypedCap (Z := Unit) s)) := by
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
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hz0 : SR k z.2 := sr_deleteObjects_p b n σ hD hσ z hz
    refine (ike_and (?_ : SAKE _) (?_ : RBKE k _) : IKE (SR k) _) z.2 hz0 y hy
    · try dsimp only
      sa_auto
    · try dsimp only
      rb_auto

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem sr_utBody {k : Bool} (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    (slots : List CslotPtr) (dev : Bool) (σ : State Unit)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    IKp (SR k) σ (do
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
  have hb4 : SR k x4.2 := (ik_and (sa_setCap _ _) (rb_setCap _ _) : IK (SR k) _) σ hσ x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := sr_retypeRegionWith_p (k := k) fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  refine (ik_and (?_ : SAK _) (?_ : RBK k _) : IK (SR k) _) x5.2 hb5 _ hx
  · sa_auto
  · rb_auto

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `SR k`** (the decode's `UtRetOK`, `UtInv''`, `IfLiveTN`). -/
theorem sr_invokeUntyped {k : Bool} (ui : UntypedInvocation) (σ : State Unit) (hU : UtInv'' σ)
    (hL : IfLiveTN σ) (hok : UtRetOK σ ui) :
    IKp (SR k) σ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui)) := by
  intro hσ y hy
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok
  cases reset
  · have hfr := utRet_fresh hU.1.1 hok
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact sr_utBody s base rb ty sz slots dev σ hfr hσ x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := sr_resetUntypedCap s hc (rnDet_of_live hU hL hc (hr rfl)) hσ z hz
    have hfz := utRet_fresh_after_reset hU.1.1 hok z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact sr_utBody s base rb ty sz slots dev s1 hfz hbz x hx

/-- **`invoke_untyped` keeps `EB k`**. -/
theorem eb_fl4InvokeUntyped {k : Bool} (ui : UntypedInvocation) (σ : State Unit) (hU : UtInv'' σ)
    (hL : IfLiveTN σ) (hok : UtRetOK σ ui) :
    IKp (EB k) σ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui)) := by
  intro hσ y hy
  have hT := tq_invokeUntyped ui σ hU.1.1 hok
    (fun _ _ _ _ _ hc hk => rqDet_of_live hU hL hσ.1.1.1.1 hc hk) hσ.1.1.1 y hy
  have hQ := q4_invokeUntypedWith fl4ObjBitsApi ui σ hσ.1.2 y hy
  have hR := sr_invokeUntyped ui σ hU hL hok ⟨hσ.1.1.2, hσ.2⟩ y hy
  exact ⟨⟨⟨hT, hR.1⟩, hQ⟩, hR.2⟩

/-! ## MakePool -/

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `SR k`** (the parent slot holds a childless page-sized untyped at the frame). -/
theorem sr_makePool {k : Bool} (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit)
    (hD : ∀ t, RnH t σ.kheap → t ∉ SInvU.delR frame page_bits) (hf : frame ∈ SInvU.delR frame page_bits) :
    IKp (SR k) σ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  intro hσ y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := sr_deleteObjects_p (k := k) frame page_bits σ hD hσ y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hf]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : SR k y3.2 := (ik_and (sa_setCap _ _) (rb_setCap _ _) : IK (SR k) _) y1.2 hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hb4 := sr_retypeRegionWith_p (k := k) objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'; exact hn3) hb3 y4 h4
  refine (ik_and (?_ : SAK _) (?_ : RBK k _) : IK (SR k) _) y4.2 hb4 y hy
  · sa_auto
  · rb_auto

/-- **MakePool keeps `EB k`** (the decode's `MpOKN`, `UtInv''`, `IfLiveTN`). -/
theorem eb_makePool {k : Bool} (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit)
    (hU : UtInv'' σ) (hL : IfLiveTN σ) (hok : MpOKN (uV σ) (.makePool frame slot parent base)) :
    IKp (EB k) σ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base)) := by
  intro hσ y hy
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  obtain ⟨hD, hf⟩ := rqMp_of hU hL hσ.1.1.1.1 hc' hk
  have hT := tq_makePool frame slot parent base σ hD hf hσ.1.1.1 y hy
  have hQ := q4_performAsidControlInvocation (.makePool frame slot parent base) σ hσ.1.2 y hy
  have hR := sr_makePool frame slot parent base σ (rnDet_of_live hU hL hc' hk) hf ⟨hσ.1.1.2, hσ.2⟩ y hy
  exact ⟨⟨⟨hT, hR.1⟩, hQ⟩, hR.2⟩

/-! ## The arms -/

/-- **The Untyped arm keeps `EB k`.** -/
theorem eb_perfUntyped (k bl call don : Bool) (ui : UntypedInvocation) :
    HKE (fun σ => EB k σ ∧ UtInv'' σ ∧ IfLiveTN σ ∧ UtRetOK σ ui) (EB k)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeUntyped ui)) := by
  intro σ hσ y hy
  simp only [fl4PerformInvocation] at hy
  obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
  rw [e]; exact eb_fl4InvokeUntyped ui σ hσ.2.1 hσ.2.2.1 hσ.2.2.2 hσ.1 z hz

/-- **The MakePool arm keeps `EB k`.** -/
theorem eb_perfMakePool (k bl call don : Bool) (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) :
    HKE (fun σ => EB k σ ∧ UtInv'' σ ∧ IfLiveTN σ ∧ MpOKN (uV σ) (.makePool frame slot parent base)) (EB k)
      (fl4PerformInvocation (Z := Unit) bl call don
        (.invokeArchObject (.spec (.invokeASIDControl (.makePool frame slot parent base))))) := by
  intro σ hσ y hy
  simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation] at hy
  obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
  obtain ⟨z, hz, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  exact eb_makePool frame slot parent base σ hσ.2.1 hσ.2.2.1 hσ.2.2.2 hσ.1 z hz

end

end Fl4Proofs.P3.SInvQ.P15
