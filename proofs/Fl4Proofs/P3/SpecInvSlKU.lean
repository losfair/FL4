/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **`ScKindR` across the untyped
retype without reset** (spec side only; the no-reset half of the untyped retype for SpecInvSlKE, on
ut8's view algebra, SpecInvUtP4 / P5).

* `skrV_fresh`: a cap write whose range no other slot's cap meets (sl4's
  `skr_setCap_fresh` on the view), `skrV_of_sub`: every non-null cap is an old
  one or has an empty range and is no SC cap.
* **`skr_ccLoop`**: the `create_cap` loop over items whose object windows are
  pairwise disjoint and met by no cap's range (ut8's `ItemN`, its range half):
  each new cap's range lies in its window (`capRng_default`).
* **`skr_tail`** (ut8's `nv_tail` pruned to what ScKindR reads): the free-index
  raise writes an untyped cap, the retype's new objects hold only null caps,
  every old cap's range misses the retype window (`hfr`, from `CapFreeV`).
-/
import Fl4Proofs.P3.SpecInvSlKD
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-- **A fresh cap write on the view.** -/
theorem skrV_fresh {w w' : UView} (hK : ScKindRV w) {d : CslotPtr} {c0 : Cap}
    (hc : ∀ s, w'.2.1 s = if s = d then some c0 else w.2.1 s)
    (hF : ∀ r ∈ capRng c0, ∀ s c, s ≠ d → w.2.1 s = some c → r ∉ capRng c)
    (hS : ∀ r b, c0 = .schedContextCap r b → r ∈ capRng c0) : ScKindRV w' := by
  intro s r b s' c' h1 h2 h3
  rw [hc] at h1 h2
  by_cases es : s = d
  · rw [if_pos es] at h1
    have e0 : c0 = .schedContextCap r b := Option.some.inj h1
    have hr := hS r b e0
    by_cases es' : s' = d
    · rw [if_pos es'] at h2; exact ⟨b, (Option.some.inj h2).symm.trans e0⟩
    · rw [if_neg es'] at h2; exact absurd h3 (hF r hr s' c' es' h2)
  · rw [if_neg es] at h1
    by_cases es' : s' = d
    · rw [if_pos es'] at h2
      have e0 : c' = c0 := (Option.some.inj h2).symm
      subst e0
      exact absurd (show r ∈ capRng (.schedContextCap r b) by simp [capRng, objRefs]) (hF r h3 s _ es h1)
    · rw [if_neg es'] at h2; exact hK s r b s' c' h1 h2 h3

/-- Every non-null cap of `w'` is an old one, or harmless. -/
theorem skrV_of_sub {w w' : UView} (hK : ScKindRV w)
    (h : ∀ sl c, w'.2.1 sl = some c → c ≠ .nullCap →
      (capRng c = ∅ ∧ ∀ r b, c ≠ .schedContextCap r b) ∨ w.2.1 sl = some c) : ScKindRV w' := by
  intro s r b s' c' h1 h2 h3
  rcases h s _ h1 (fun e => by cases e) with ⟨-, hn⟩ | h1'
  · exact absurd rfl (hn r b)
  · rcases h s' c' h2 (capRng_nn h3) with ⟨he, -⟩ | h2'
    · rw [he] at h3; exact h3.elim
    · exact hK s r b s' c' h1' h2' h3

/-- **The `create_cap` loop keeps `ScKindR`** over fresh, disjoint windows. -/
theorem skr_ccLoop (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool) :
    ∀ (L : List (CslotPtr × ObjRef)) (w : UView), ScKindRV w →
      L.Pairwise (fun x y => ∀ k ∈ utR x.2 (fl4ObjBitsApi ty sz), k ∉ utR y.2 (fl4ObjBitsApi ty sz)) →
      (∀ x ∈ L, x.2.toNat + 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64) →
      (∀ x ∈ L, ∀ s c r, w.2.1 s = some c → r ∈ capRng c → r.toNat ∉ utR x.2 (fl4ObjBitsApi ty sz)) →
      HV (· = w) ScKindRV (NonDet.mapMx (createCap (Z := Unit) ty sz src dev) L)
  | [], w, hK, _, _, _ => by unfold NonDet.mapMx; exact hv_ret' _ hK
  | (d, p) :: L, w, hK, hP, hB, hI => by
    unfold NonDet.mapMx
    refine hv_bind' (hv_createCap ty sz src dev d p w) fun _ => ?_
    rw [List.pairwise_cons] at hP
    have hcr := capRng_default ty sz dev p (hB (d, p) List.mem_cons_self)
    have hK' : ScKindRV (vCC src d (defaultCap ty p sz dev) w) := by
      refine skrV_fresh hK (fun s => vCC_cap s)
        (fun r hr s c _ hs hrc => hI (d, p) List.mem_cons_self s c r hs hrc (hcr r hr)) ?_
      intro r b e; rw [e]; simp [capRng, objRefs]
    refine skr_ccLoop ty sz src dev L _ hK' hP.2 (fun x hx => hB x (List.mem_cons_of_mem _ hx)) ?_
    intro x hx s c r hs hr
    rcases vCC_cases hs with ⟨-, rfl⟩ | ⟨-, hs⟩
    · exact hP.1 x hx _ (hcr r hr)
    · exact hI x (List.mem_cons_of_mem _ hx) s c r hs hr

set_option maxHeartbeats 8000000 in
/-- **The retype without reset keeps `ScKindR`** (ut8's `nv_tail`, pruned). -/
theorem skr_tail {σ : State Unit} (hK : ScKindR σ) {s : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool} {bits fi0 : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev base bits fi0))
    (hbits : bits < 64) (hfit : base.toNat + 2 ^ bits ≤ 2 ^ 64)
    (hlo : base.toNat ≤ rb.toNat)
    (hhi : rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz ≤ base.toNat + 2 ^ bits)
    (hfr : ∀ s' c r, SInvU.capAt σ s' = some c → r ∈ capRng c →
      ¬ (rb.toNat ≤ r.toNat ∧ r.toNat < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz))
    (hheap : ∀ q, (σ.kheap q).isSome = true →
      ¬ (rb.toNat ≤ q.toNat ∧ q.toNat < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz))
    (hnd : slots.Nodup) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s false base rb ty sz slots dev)) σ).1,
      ScKindR y.2 := by
  intro y hy
  have hfitR : rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64 := by omega
  simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
  replace hy := run_returnOk_bind_mem hy
  obtain ⟨x, hx, e⟩ := run_liftE_mem hy
  rw [e]
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1 hc1; subst s1
  rw [hc] at hc1; cases hc1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  -- the free-index raise: an untyped cap at `s`
  obtain ⟨x4, hx4, hx⟩ := hx
  have hv4 := hv_setCap _ _ (uV σ) σ rfl x4 hx4
  have hkey4 : ∀ q, (x4.2.kheap q).isSome = (σ.kheap q).isSome :=
    fun q => congrFun (congrArg (fun w : UView => w.1) hv4) q
  have hold4 : ∀ sl c, SInvU.capAt x4.2 sl = some c →
      (sl = s ∧ isUntypedCap c = true) ∨ (sl ≠ s ∧ SInvU.capAt σ sl = some c) := by
    intro sl c h
    have h' : (uV x4.2).2.1 sl = some c := h
    rw [hv4, vCap_cap] at h'
    split_ifs at h' with es
    · left; cases h'; exact ⟨es, rfl⟩
    · right; exact ⟨es, h'⟩
  -- retype_region
  obtain ⟨x5, hx5, hx⟩ := hx
  obtain ⟨hy5, h5⟩ := retypeRegionWith_out hx5
  have hnew : ∀ q ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz), (x4.2.kheap q).isSome = false := by
    intro q hq
    rw [hkey4]
    cases e : σ.kheap q with
    | none => rfl
    | some _ => exact absurd (retPtrs_rng hq hfitR) (hheap q (by rw [e]; rfl))
  have hsame : ∀ sl, (σ.kheap sl.1).isSome = true → SInvU.capAt x5.2 sl = SInvU.capAt x4.2 sl := by
    intro sl hsl
    rcases h5 with e5 | ⟨-, e5⟩
    · rw [e5]
    · rw [e5]
      have hm : sl.1 ∉ retPtrs rb slots.length (fl4ObjBitsApi ty sz) := fun hm => by
        have := hnew _ hm; rw [hkey4, hsl] at this; cases this
      unfold SInvU.capAt retKh; try dsimp only
      rw [if_neg hm]
  have hnewc : ∀ sl c, SInvU.capAt x5.2 sl = some c → (σ.kheap sl.1).isSome = false → c = .nullCap := by
    intro sl c hsl hn
    have h4n : SInvU.capAt x4.2 sl = none := by
      cases e4 : SInvU.capAt x4.2 sl with
      | none => rfl
      | some c' =>
        exfalso
        rcases hold4 sl c' e4 with ⟨rfl, -⟩ | ⟨-, h'⟩
        · rw [capAt_some_heap hc] at hn; cases hn
        · rw [capAt_some_heap h'] at hn; cases hn
    rcases h5 with e5 | ⟨hty, e5⟩
    · rw [e5, h4n] at hsl; cases hsl
    · rw [e5] at hsl
      unfold SInvU.capAt retKh at hsl; try dsimp only at hsl
      split_ifs at hsl with hm
      · exact default_null hty _ _ _ _ hsl
      · unfold SInvU.capAt at h4n; rw [h4n] at hsl; cases hsl
  -- init_arch_objects
  obtain ⟨x6, hx6, hx⟩ := hx
  have hv6 : uV x6.2 = uV x5.2 := uk_initArchObjects (uvw := uV x5.2) _ _ _ _ _ _ x5.2 rfl x6 hx6
  rw [hy5] at hx
  have hold6 : ∀ sl c, (uV x6.2).2.1 sl = some c → c ≠ .nullCap →
      isUntypedCap c = true ∨ SInvU.capAt σ sl = some c := by
    intro sl c hsl hn
    rw [hv6] at hsl
    have hsl' : SInvU.capAt x5.2 sl = some c := hsl
    by_cases hh : (σ.kheap sl.1).isSome = true
    · rw [hsame sl hh] at hsl'
      rcases hold4 sl c hsl' with ⟨-, hu⟩ | ⟨-, h'⟩
      · exact Or.inl hu
      · exact Or.inr h'
    · exact absurd (hnewc sl c hsl' (by simpa using hh)) hn
  have hK6 : ScKindRV (uV x6.2) := by
    refine skrV_of_sub hK fun sl c hsl hn => ?_
    rcases hold6 sl c hsl hn with hu | h'
    · exact Or.inl ⟨capRng_untyped hu, fun r b e => by rw [e] at hu; simp [isUntypedCap] at hu⟩
    · exact Or.inr h'
  -- the loop
  have hxr : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), rb.toNat ≤ x.2.toNat ∧
      x.2.toNat + 2 ^ fl4ObjBitsApi ty sz ≤ rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz :=
    fun x hx => zip_rng hx hfitR
  have hinR : ∀ x ∈ slots.zip (retPtrs rb slots.length (fl4ObjBitsApi ty sz)), ∀ k ∈ utR x.2 (fl4ObjBitsApi ty sz),
      rb.toNat ≤ k ∧ k < rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz := by
    intro x hx k hk
    have := hxr x hx; have := hk.1; have := hk.2; omega
  refine skr_ccLoop ty sz s dev _ (uV x6.2) hK6
    ((pw_zip2 _ _ hnd (retPtrs_pw hfitR)).imp fun h => h.2) (fun x hx => by have := hxr x hx; omega) ?_ x6.2 rfl _ hx
  intro x hx s' c r hs' hr hm
  rcases hold6 s' c hs' (capRng_nn hr) with hu | hs''
  · rw [capRng_untyped hu] at hr; exact hr
  · exact hfr s' c r hs'' hr (hinR x hx _ hm)

set_option maxHeartbeats 8000000 in
/-- **The untyped retype without reset keeps `ScKindR`**, from the carried
`UtInv''` and ut8's decode facts (`UtGapOK`; `p3_invokeUntyped`'s no-reset case). -/
theorem skr_invokeUntyped0 {σ : State Unit} (hK : ScKindR σ) (hU : UtInv'' σ) {s : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtGapOK (uV σ) (.retype s false base rb ty sz slots dev)) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) (.retype s false base rb ty sz slots dev)) σ).1, ScKindR y.2 := by
  intro y hy
  obtain ⟨h1, -, h3⟩ := hok
  obtain ⟨hI, hN⟩ := hU
  have hok' := h1
  obtain ⟨bits, fi, hc, ho, hw1, hrb, hw, hr⟩ := hok'
  have hc' : SInvU.capAt σ s = some (.untypedCap dev base bits fi) := hc
  obtain ⟨bits', fi', hc'', hfit, h1r, hal, h3r⟩ := utRet_region hI.1.2.1 (utRetOK_of_V h1)
  rw [hc'] at hc''; cases hc''
  obtain ⟨hbits, -⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc'
  obtain ⟨hsz, s1, nc, off, win, hs1, hcn, hle, he⟩ := h3
  obtain ⟨hnd, -⟩ := utDest_of hN.2.2.2.2.2.2 hs1 hcn hle he
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1r
  refine skr_tail hK hc' hbits hfit (by omega) h3r ?_ ?_ hnd y hy
  · intro s' c r hs' hr hm
    exact hN.2.2.1 s dev base bits fi hc s' c r hs' hr ⟨by omega, by omega⟩
  · intro q hq hm
    exact hI.1.1 s dev base bits fi hc q hq ⟨by omega, by omega⟩

end

end Fl4Proofs.P3.SInvL
