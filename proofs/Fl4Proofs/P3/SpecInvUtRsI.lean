/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **`invoke_untyped`
with reset keeps `UtInv'`** (spec side only): `reset_untyped_cap`
(`reset_utInv'`, under the named premise `DetypeOK` [J]) and then the
non-reset chain from the reset's facts `RSV` instead of the old free part:
the free-index write by `rs_setCap`, the new objects at addresses of the
emptied region, the `create_cap` loops (SpecInvUtI).
-/
import Fl4Proofs.P3.SpecInvUtRs
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- **`invoke_untyped` with reset keeps `UtInv'`** (at the decode's checks, under `DetypeOK` [J]). -/
theorem invokeUntyped_reset_utInv' {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) {s : CslotPtr}
    {base rb : ObjRef} {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtRetOK σ (.retype s true base rb ty sz slots dev))
    (hdn : DestNull σ (.retype s true base rb ty sz slots dev)) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s true base rb ty sz slots dev)) σ).1,
      UtInv' y.2 := by
  intro y hy
  have hok' := hok
  obtain ⟨bits, fi, hc, ho, -, -, -, hr⟩ := hok'
  have hk : ∀ c, σ.cdt c ≠ some s := hr rfl
  obtain ⟨bits', fi', hc', hfit, h1, hal, h3⟩ := utRet_region hI.1.2.1 hok
  rw [hc] at hc'; cases hc'
  simp only [if_true, Nat.add_zero] at h1
  obtain ⟨hbits, -⟩ := UtWf.fit hI.1.2.1 hc
  have hfi : unat (rb + (BitVec.ofNat 64 slots.length <<< (fl4ObjBitsApi ty sz)) - base) =
      rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat := fi_new hbits (by omega) h3 hfit
  have hfiN : rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat ≤ 2 ^ bits := by omega
  simp only [invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
  rw [ExceptT.run_bind] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hPz := reset_utInv' hI hDT hc hk z hz
  obtain ⟨r, s1⟩ := z
  change PR s dev base bits σ.cdt s1 at hPz
  cases r with
  | error e =>
    first
      | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hPz.1)
      | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hPz.1)
  | ok u => ?_
  try dsimp only at hy
  obtain ⟨hI1, hR1⟩ := hPz
  obtain ⟨x, hx, e⟩ := run_liftE_mem hy
  rw [e]
  -- getCap
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := getCap_capAt hx1
  obtain ⟨cap, s2⟩ := x1
  simp only at e1 hc1; subst s2
  have hcs : ∃ f0, capAt s1 s = some (.untypedCap dev base bits f0) := by
    rcases hR1.1 with h | h
    · exact h
    · exfalso
      have h' : (s1.kheap s.1).isSome = false := h
      unfold capAt at hc1
      cases e' : s1.kheap s.1 with
      | none => rw [e'] at hc1; cases hc1
      | some _ => rw [e'] at h'; cases h'
  obtain ⟨f0, hcs⟩ := hcs
  rw [hcs] at hc1; cases hc1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  -- the free-index write
  obtain ⟨x4, hx4, hx⟩ := hx
  obtain ⟨hv4, hex⟩ := hv_setCap_ex _ _ (uV s1) s1 rfl x4 hx4
  simp only [bitsOf] at hv4
  rw [hfi] at hv4
  obtain ⟨hI4', hR4'⟩ := rs_setCap hI1 hR1 hex hfiN
  have hI4 : UtInv' x4.2 := by show UtInv'V _; rw [hv4]; exact hI4'
  have hR4 : RSV s dev base bits σ.cdt (uV x4.2) := by rw [hv4]; exact hR4'
  have hcap4 : capAt x4.2 = Function.update (capAt s1) s
      (some (.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat))) :=
    congrArg (fun w : UView => w.2.1) hv4
  have hcdt4 : x4.2.cdt = σ.cdt := hR4.2.2.1
  -- the retype
  have hin : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), q.toNat ∈ utR base bits ∧
      q.toNat < base.toNat + (rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat) := by
    intro q hqm
    obtain ⟨k, hk', rfl⟩ := retPtrs_mem hqm
    have hpo := Nat.two_pow_pos (fl4ObjBitsApi ty sz)
    have m2 : (k + 1) * 2 ^ (fl4ObjBitsApi ty sz) ≤ slots.length * 2 ^ (fl4ObjBitsApi ty sz) :=
      Nat.mul_le_mul_right _ hk'
    have e2 : (k + 1) * 2 ^ (fl4ObjBitsApi ty sz) = k * 2 ^ (fl4ObjBitsApi ty sz) + 2 ^ (fl4ObjBitsApi ty sz) :=
      Nat.succ_mul _ _
    rw [ptrAdd_toNat (by omega)]
    simp only [utR, Set.mem_setOf_eq]
    omega
  obtain ⟨x5, hx5, hx⟩ := hx
  have hnew : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), x4.2.kheap q = none ∧
      ∀ sl d b m f, capAt x4.2 sl = some (.untypedCap d b m f) → q.toNat ∉ utFr b m f := by
    intro q hqm
    obtain ⟨hq1, hq2⟩ := hin q hqm
    refine ⟨?_, fun sl d b m f hcs' => ?_⟩
    · cases e' : x4.2.kheap q with
      | none => rfl
      | some _ => exact absurd hq1 (hR4.2.1 q (show (x4.2.kheap q).isSome = true by rw [e']; rfl))
    · by_cases es : sl = s
      · subst es; rw [hcap4, Function.update_self] at hcs'; cases hcs'
        intro hm; have := hm.1; omega
      · exact (hR4.2.2.2.2.1 sl d b m f es hcs').1 _ hq1
  obtain ⟨hI5, hy5, hcdt5, hcap5, hut5⟩ := utInv'_retype hI4 hnew hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hv6 : uV x6.2 = uV x5.2 := uk_initArchObjects (uvw := uV x5.2) _ _ _ _ _ _ x5.2 rfl x6 hx6
  rw [hy5] at hx
  have hk4s : x4.2.kheap s.1 ≠ none := by
    intro e'; have hc0 : capAt x4.2 s = _ := congrFun hcap4 s
    rw [Function.update_self] at hc0; unfold capAt at hc0; rw [e'] at hc0; cases hc0
  have hdst : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), x.1 ≠ s ∧ ∀ c, σ.cdt c ≠ some x.1 := by
    intro x hxm
    have hn := hdn x.1 (List.of_mem_zip hxm).1
    refine ⟨fun e' => ?_, fun c hcx => ?_⟩
    · rw [e', hc] at hn; cases hn
    · obtain ⟨cap, hcap, hcn⟩ := hI.2.1 c x.1 hcx
      have hcap' : capAt σ x.1 = some cap := hcap
      rw [hn] at hcap'; cases hcap'; exact hcn rfl
  by_cases hty : ty = .untyped
  · subst hty
    have ho' : fl4ObjBitsApi .untyped sz = sz := rfl
    simp only [ho'] at *
    have e5 : x5.2 = x4.2 := by first | exact hut5 rfl | exact hut5 trivial | exact hut5
    have hw6 : uV x6.2 = uV x4.2 := by rw [hv6, e5]
    refine hv_ccLoopU sz s dev dev base bits (rb.toNat + slots.length * 2 ^ sz - base.toNat) _ (uV x6.2)
      (pw_zip _ _ (retPtrs_pw (by omega))) (by rw [hw6]; exact hI4)
      (by rw [hw6]; show capAt x4.2 s = _; rw [hcap4, Function.update_self]) (fun x hxm => ?_) x6.2 rfl _ hx
    obtain ⟨hx1, hx2⟩ := hdst x hxm
    obtain ⟨k, hk', hxk⟩ := retPtrs_mem (List.of_mem_zip hxm).2
    have hpo := Nat.two_pow_pos sz
    have m2 : (k + 1) * 2 ^ sz ≤ slots.length * 2 ^ sz := Nat.mul_le_mul_right _ hk'
    have e2 : (k + 1) * 2 ^ sz = k * 2 ^ sz + 2 ^ sz := Nat.succ_mul _ _
    have hxt : x.2.toNat = rb.toNat + k * 2 ^ sz := by rw [hxk]; exact ptrAdd_toNat (by omega)
    have hreg : ∀ k', k' ∈ utR x.2 sz → k' ∈ utR base bits ∧
        k' < base.toNat + (rb.toNat + slots.length * 2 ^ sz - base.toNat) := by
      intro k' hk2; simp only [utR, Set.mem_setOf_eq] at hk2 ⊢; rw [hxt] at hk2; omega
    refine ⟨hx1, by rw [hw6]; show ∀ c, x4.2.cdt c ≠ some x.1; rw [hcdt4]; exact hx2, fun k' hk2 => ⟨(hreg k' hk2).1, fun hm => ?_⟩, fun q hq' hm => ?_,
      ⟨ho, ?_⟩, fun sl d b n f hs1 hs2 hcs' hov => ?_⟩
    · have := (hreg k' hk2).2; have := hm.1; omega
    · rw [hw6] at hq'
      exact hR4.2.1 q hq' (hreg _ hm).1
    · rw [hxt, Nat.add_mul_mod_self_right]; exact hal
    · rw [hw6] at hcs'
      have h5 := hR4.2.2.2.2.1 sl d b n f hs1 hcs'
      obtain ⟨k0, hk0, hk0'⟩ := hov
      refine ⟨by rw [hw6]; show s ∈ descendantsOf sl x4.2.cdt; rw [hcdt4]; exact h5.2 ⟨k0, (hreg k0 hk0).1, hk0'⟩, h5.1⟩
  · refine hv_ccLoop hty sz s dev _ (uV x6.2) (by rw [hv6]; exact hI5)
      ⟨.untypedCap dev base bits (rb.toNat + slots.length * 2 ^ (fl4ObjBitsApi ty sz) - base.toNat), ?_,
        by intro h; cases h⟩ (fun x hxm => ?_) x6.2 rfl _ hx
    · rw [hv6]; show capAt x5.2 s = _; rw [hcap5 s hk4s, hcap4, Function.update_self]
    · obtain ⟨hx1, hx2⟩ := hdst x hxm
      refine ⟨hx1, fun c hcx => hx2 c ?_⟩
      have : (uV x6.2).2.2.1 = σ.cdt := by rw [hv6]; show x5.2.cdt = _; rw [hcdt5, hcdt4]
      rw [this] at hcx; exact hcx

end

end Fl4Proofs.P3.SInvU
