/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **`krGap : KrGap`** (the reset retype
and MakePool keep `ScKindR`) and the tops with no `ScKind` premise (spec side only).

* `ks_retype`: `retype_region` keeps `KS σ0` (new objects hold only null caps; an
  overwritten object only loses caps).
* **`skr_makePool`**: MakePool anchored at its start `σ`: the detype only drops
  caps, the parent's free-index raise writes an untyped cap, the pool cap is
  `KOk σ` because no cap of `σ` covers the frame (ut8's `clear_of_childless`:
  UtCh + the decode's childless check).
* `RK σ0 src dev b n` (a `WLH` predicate on vih2's view): every non-null cap is the
  source's or an old one of `σ0`, and the source holds an untyped cap of the same
  region; `rk_setCap_ut`, `rk_detype`, **`rk_reset`** (`reset_untyped_cap`: what
  ut8's `RNV` gave, without its `NV N`).
* **`skr_invokeUntyped1`** (retype with reset: `rk_reset`, ut2's `RSV` heap fact,
  then SpecInvSlKU's `skr_tail`), **`krGap`**.
* Tops: **`kentry_scKindR` / `kcall_scKindR`**, **`kentry_slB2` / `kcall_slB2`**,
  **`kentry_scLive2` / `kcall_scLive2`** (SpecInvSlKT's `_of` forms at `krGap`).
-/
import Fl4Proofs.P3.SpecInvSlKT
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU
open Fl4Proofs.P3.SInvV (hV hV_cap WLH wlh_of_hV)

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

/-! ## `retype_region` and MakePool -/

theorem ks_retype {bA : ApiObjectType → Nat → Nat} {rb : ObjRef} {n oB : Nat} {ty : ApiObjectType} {dev : Bool}
    {a τ : State Unit} (hτ : KS a τ) {y : List ObjRef × State Unit}
    (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev τ).1) : KS a y.2 := by
  obtain ⟨-, ⟨-, e2⟩ | ⟨hty, e2⟩⟩ := vfh_retypeRegionWith_out hy
  · rw [e2]; exact hτ
  · have hk : ∀ q, y.2.kheap q = if q ∈ retPtrs rb n (bA ty oB) then some (defaultObject ty dev oB τ.curDomain)
        else τ.kheap q := fun q => by rw [e2]; rfl
    intro sl c hc
    rw [hk] at hc
    split_ifs at hc with hp
    · rw [vfh_default_null hty hc]; exact kok_null
    · exact hτ sl c hc

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `ScKindR`**, from the decode's `MpOKN` and the carried `UtInv''`. -/
theorem skr_makePool {σ : State Unit} (hK : ScKindR σ) (hU : UtInv'' σ) {a : AsidControlInvocation}
    (hm : MpOKN (uV σ) a) : ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, ScKindR y.2 := by
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hm
    have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
    have hClr := clear_of_childless hU.2 hc hk
    intro y hy
    simp only [performAsidControlInvocation] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hkz := (deleteObjects_kheap hz).1
    have hz0 : KS σ z.2 := by
      intro sl c hc1
      rw [hkz] at hc1
      split_ifs at hc1
      · simp [capOpt] at hc1
      · exact KS.refl hK sl c hc1
    obtain ⟨x1, h1, hy⟩ := hy
    obtain ⟨hs1, hc1⟩ := getCap_capAt h1
    have hpo := vfh_srcOut hU hc' hk
    have hcz : capOpt (z.2.kheap parent.1) parent.2 = some (.untypedCap dev frame page_bits fi) := by
      rw [hkz, if_neg hpo, ← vfh_capAt]; exact hc'
    rw [vfh_capAt, hcz] at hc1
    obtain ⟨x2, h2, hy⟩ := hy
    have hv2 : KS σ x2.2 := by
      rw [← Option.some.inj hc1] at h2
      rw [hs1] at h2
      exact ks_setCap _ (kok_maxFree rfl) z.2 hz0 x2 h2
    obtain ⟨x3, h3, hy⟩ := hy
    rw [← retypeRegionWith_objBitsApi] at h3
    have hv3 : KS σ x3.2 := ks_retype hv2 h3
    have hW : UtWf σ := hU.1.1.2.1
    obtain ⟨hn64, hfit⟩ := hW.fit hc'
    have hfr : frame ∈ delR frame page_bits := by
      rw [mem_delR_iff hn64 hfit]
      have := Nat.two_pow_pos page_bits
      simp only [utR, Set.mem_setOf_eq]
      omega
    have hkp : KOk σ (.archObjectCap (.asidPoolCap frame base)) := by
      refine ⟨(fun _ _ e => by cases e), fun r hr => Or.inr fun s b e => ?_⟩
      have er : r = frame := by simpa [capRng, acRng, aobjRef, eq_comm] using hr
      subst er
      exact hClr s _ r e (by simp [capRng, objRefs]) hfr
    have hrest : IK (KS σ) (do
        capInsert (Z := Unit) (.archObjectCap (.asidPoolCap frame base)) parent slot
        NonDet.assert (asidLowBitsOf base = 0)
        let asidTable ← NonDet.gets fun s : State Unit => s.archState.x64AsidTable
        let asidTable' ← pure (Function.update asidTable (asidHighBitsOf base) (some frame))
        NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }) := by
      refine ik_bind (ks_capInsert _ _ hkp) fun _ => ?_
      hv_auto
    exact (hrest x3.2 hv3 y hy).cur

/-! ## The reset -/

/-- Every non-null cap is the source's or an old one; the source holds an untyped cap. -/
def RK (σ0 : State Unit) (src : CslotPtr) (dev : Bool) (b : ObjRef) (n : Nat) (σ : State Unit) : Prop :=
  (∀ (sl : CslotPtr) (c : Cap), capOpt (σ.kheap sl.1) sl.2 = some c → c ≠ .nullCap →
    sl = src ∨ capOpt (σ0.kheap sl.1) sl.2 = some c) ∧
  ∃ f, capOpt (σ.kheap src.1) src.2 = some (.untypedCap dev b n f)

instance (σ0 : State Unit) (src : CslotPtr) (dev : Bool) (b : ObjRef) (n : Nat) : WLH (RK σ0 src dev b n) :=
  wlh_of_hV fun σ σ' e h => by
    refine ⟨fun sl c hc hn => h.1 sl c (by rw [← hV_cap e]; exact hc) hn, ?_⟩
    obtain ⟨f, hf⟩ := h.2
    exact ⟨f, by rw [hV_cap e]; exact hf⟩

theorem rk_setCap_ut {σ0 : State Unit} {src : CslotPtr} {dev : Bool} {b : ObjRef} {n : Nat} (f' : Nat) :
    IK (RK σ0 src dev b n) (setCap (Z := Unit) (.untypedCap dev b n f') src) := by
  obtain ⟨o, r⟩ := src
  intro σ hσ x hx
  refine ⟨fun sl c hc hn => ?_, f', ?_⟩
  · obtain ⟨p, l⟩ := sl
    rw [vfh_setCap_view hx p l] at hc
    split_ifs at hc with h
    · left; obtain ⟨rfl, rfl⟩ := h; rfl
    · exact hσ.1 (p, l) c hc hn
  · rw [vfh_setCap_view hx o r, if_pos ⟨rfl, rfl⟩]

theorem rk_detype {σ0 σ σd : State Unit} {R : Set ObjRef} {src : CslotPtr} {dev : Bool} {b : ObjRef} {n : Nat}
    (hk : ∀ p, σd.kheap p = if p ∈ R then none else σ.kheap p) (hsrc : src.1 ∉ R)
    (h : RK σ0 src dev b n σ) : RK σ0 src dev b n σd := by
  refine ⟨fun sl c hc hn => ?_, ?_⟩
  · rw [hk] at hc
    split_ifs at hc
    · simp [capOpt] at hc
    · exact h.1 sl c hc hn
  · rw [hk, if_neg hsrc]; exact h.2

set_option maxHeartbeats 4000000 in
/-- **`reset_untyped_cap`** ends in `RK σ`. -/
theorem rk_reset {σ : State Unit} (hU : UtInv'' σ) {src : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) src) σ).1, RK σ src dev b n y.2 := by
  have h0 : RK σ src dev b n σ := ⟨fun sl c hc' _ => Or.inr hc', fi, by rw [← vfh_capAt]; exact hc⟩
  intro y hy
  unfold resetUntypedCap at hy
  obtain ⟨x, hx, hy⟩ := run_liftE_bind_mem hy
  obtain ⟨cap, s⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hy
  rw [hc] at hcx; cases hcx
  replace hy := run_returnOk_bind_mem hy
  replace hy := run_returnOk_bind_mem hy
  dsimp only at hy
  by_cases hf0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from hf0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact h0
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from hf0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hkz := (deleteObjects_kheap hz).1
    have hz0 : RK σ src dev b n z.2 := rk_detype hkz (vfh_srcOut hU hc hk) h0
    refine (?_ : IKE (RK σ src dev b n) _) z.2 hz0 y hy
    try dsimp only
    repeat' (first
      | exact rk_setCap_ut _
      | (refine ike_mapMEx_mem _ fun _ _ => ?_)
      | hv_leaf | ik_step0 | ik_unfold
      | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)
      | split)

set_option maxHeartbeats 8000000 in
/-- **The untyped retype with reset keeps `ScKindR`.** -/
theorem skr_invokeUntyped1 {σ : State Unit} (hK : ScKindR σ) (hU : UtInv'' σ) {s : CslotPtr} {base rb : ObjRef}
    {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : UtGapOK (uV σ) (.retype s true base rb ty sz slots dev)) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) (.retype s true base rb ty sz slots dev)) σ).1, ScKindR y.2 := by
  intro y hy
  obtain ⟨h1, -, h3⟩ := hok
  have hU0 := hU
  obtain ⟨hI, hN⟩ := hU
  have hok' := h1
  obtain ⟨bits, fi, hc, ho, hw1, hrb, hw, hr⟩ := hok'
  have hc' : SInvU.capAt σ s = some (.untypedCap dev base bits fi) := hc
  obtain ⟨bits', fi', hc'', hfit, h1r, hal, h3r⟩ := utRet_region hI.1.2.1 (utRetOK_of_V h1)
  rw [hc'] at hc''; cases hc''
  obtain ⟨hbits, -⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc'
  obtain ⟨hsz, s1, nc, off, win, hs1, hcn, hle, he⟩ := h3
  obtain ⟨hnd, -⟩ := utDest_of hN.2.2.2.2.2.2 hs1 hcn hle he
  have hpd := mem_delR_iff hbits hfit
  have hk : ∀ c, σ.cdt c ≠ some s := hr rfl
  simp only [↓reduceIte, Nat.add_zero] at h1r
  have hClr := clear_of_childless hN hc hk
  simp only [invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
  rw [ExceptT.run_bind] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hRK := rk_reset hU0 hc' hk z hz
  have hPz := reset_utInv' hI (detypeOK_of ⟨hI, hN⟩) hc' hk z hz
  obtain ⟨r, s2⟩ := z
  have hK2 : ScKindR s2 := by
    refine skrV_of_sub hK fun sl c hsl hn => ?_
    have hsl' : capOpt (s2.kheap sl.1) sl.2 = some c := by rw [← vfh_capAt]; exact hsl
    rcases hRK.1 sl c hsl' hn with rfl | h0
    · obtain ⟨f, hf⟩ := hRK.2
      rw [hsl'] at hf; cases hf
      exact Or.inl ⟨capRng_untyped rfl, fun _ _ e => by cases e⟩
    · exact Or.inr (by show SInvU.capAt σ sl = some c; rw [vfh_capAt]; exact h0)
  cases r with
  | error e =>
    first
      | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hK2)
      | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hK2)
  | ok u => ?_
  try dsimp only at hy
  have hy' : y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi
      (.retype s false base rb ty sz slots dev)) s2).1 := by
    simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte]
    exact run_returnOk_bind_mem' hy
  obtain ⟨hIz, hRS⟩ := hPz
  change RSV s dev base bits σ.cdt (uV s2) at hRS
  obtain ⟨-, hR2, -, -, -, -, -⟩ := hRS
  obtain ⟨f2, hf2⟩ := hRK.2
  have hf2' : SInvU.capAt s2 s = some (.untypedCap dev base bits f2) := by rw [vfh_capAt]; exact hf2
  have hclr2 : ∀ s' c r, SInvU.capAt s2 s' = some c → r ∈ capRng c → r ∉ delR base bits := by
    intro s' c r hs' hr
    have hs'' : capOpt (s2.kheap s'.1) s'.2 = some c := by rw [← vfh_capAt]; exact hs'
    rcases hRK.1 s' c hs'' (capRng_nn hr) with rfl | hs0
    · rw [hf2] at hs''; cases hs''; rw [capRng_untyped rfl] at hr; exact hr.elim
    · exact hClr s' c r (by show SInvU.capAt σ s' = some c; rw [vfh_capAt]; exact hs0) hr
  refine skr_tail hK2 hf2' hbits hfit (by omega) h3r ?_ ?_ hnd y hy'
  · intro s' c r hs' hr hm
    exact hclr2 s' c r hs' hr ((hpd r).2 ⟨by omega, by omega⟩)
  · intro q hq hm
    exact hR2 q hq ⟨by omega, by omega⟩

/-- **The retype performs keep `ScKindR`.** -/
theorem krGap : KrGap :=
  ⟨fun _ _ _ _ _ _ _ _ hK hU hok => skr_invokeUntyped1 hK hU hok, fun _ _ hK hU hm => skr_makePool hK hU hm⟩

/-! ## Tops -/

/-- **`ScKindR` across the syscall entry** (`hU : UtInv3 σ`, a G1 field). -/
theorem kentry_scKindR (c : Syscall) {σ : State Unit} (hK : ScKindR σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScKindR y.2 :=
  kentry_scKindR_of krGap c hK hU

/-- **`ScKindR` across every kernel event.** -/
theorem kcall_scKindR (rep : Bool) (ev : Event) {σ : State Unit} (hK : ScKindR σ) (hU : UtInv3 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScKindR y.2 :=
  kcall_scKindR_of krGap rep ev hK hU

/-- **ScLiveT ∧ NtfnScB kept by the syscall entry**, no `ScKind` premise. -/
theorem kentry_scLive2 (c : Syscall) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 :=
  kentry_scLive2_of krGap c h hE ha hct

/-- **ScLiveT ∧ NtfnScB kept by every kernel event**, no `ScKind` premise. -/
theorem kcall_scLive2 (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 :=
  kcall_scLive2_of krGap rep ev h hE ha hct

/-- **The bundle `SlB ∧ ScKindR` kept by the syscall entry** (no `ScKind` premise). -/
theorem kentry_slB2 (c : Syscall) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SlB2 y.2 :=
  kentry_slB2_of krGap c h hE ha hct

/-- **The bundle `SlB ∧ ScKindR` kept by every kernel event** (no `ScKind` premise). -/
theorem kcall_slB2 (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SlB2 y.2 :=
  kcall_slB2_of krGap rep ev h hE ha hct

end

end Fl4Proofs.P3.SInvL
