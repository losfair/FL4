/-
P3 (DESIGN.md §9), invariant line G1 (vfh3): **the retype performs keep
`VfhV ∧ CnDom`** (spec side only, outside the JAtZ cone; vfh2 handoff step 2).

The untyped retype (`fl4InvokeUntyped`, with or without the reset) and ASID
control's MakePool (`performAsidControlInvocation`) are the only performs that
remove or create objects, so they break `DomK` and are proved pointwise at the
perform state `σ`, from the decode's facts (`VUt` / `VMp`, SpecInvVfhX; ut3's
`UtRetOK` / `MpOK`) and the carried untyped invariant `UtInv'' σ` (ut4..ut6;
only its exported facts `UtChV`, `regNull_of`, `UtInv` are used):

* `vfh_retype`: `retype_region` at addresses holding no object keeps `VS a`
  (default objects hold only null caps; a CNode cap of the old state names a
  full, hence existing, object, so none names a new address) and the new CNodes
  are full (`emptyCnode`).
* `vs_createCap`, `vfh_utMain` (the retype body after the reset: the source
  slot and the destinations are no fault-handler slots of an anchor `a`, the
  new caps are `CnOk` at the retype state).
* `vfh_detype` (`delete_objects` of a region no CNode cap points into keeps
  `VfhV ∧ CnDom`), `vfh_noRef` (UtCh + the decode's `ensure_no_children`: no
  cap covers a childless untyped's region), `vfh_srcOut` (RegNull: the
  untyped's own slot lies outside its region), `vfh_reset` (the reset ends in
  `VS a` for an anchor `a` at which the source and destinations are not `Bad`:
  the destinations' CNodes are `DRef`, so outside the region).
* **`vfh_fl4InvokeUntyped`**, **`vfh_makePool`**.
-/
import Fl4Proofs.P3.SpecInvVfhX
import Fl4Proofs.P3.SpecInvUtN8
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Bridges to the untyped view -/

theorem vfh_capAt (σ : State Unit) (sl : CslotPtr) : SInvU.capAt σ sl = capOpt (σ.kheap sl.1) sl.2 := by
  unfold SInvU.capAt
  cases σ.kheap sl.1 with
  | none => rfl
  | some o => cases o <;> first | rfl | (simp only [SInvU.capView, capOpt]; split <;> rfl)

theorem vfh_cnOk_ut {σ : State Unit} {d : Bool} {b : ObjRef} {n f : Nat} : CnOk σ (.untypedCap d b n f) :=
  cnOk_of_nc fun _ _ _ e => by cases e

theorem vfh_notBad_ut {σ : State Unit} (hv : VfhV σ) {sl : CslotPtr} {d : Bool} {b : ObjRef} {n f : Nat}
    (hc : SInvU.capAt σ sl = some (.untypedCap d b n f)) : ¬ vfh_Bad σ sl :=
  vfh_notBad_old (c := .untypedCap d b n f) hv (by rw [← vfh_capAt]; exact hc) (vfh_not_untyped rfl)

theorem vfh_cn_capRng (p : ObjRef) (r : Nat) (g : CapRef) : p ∈ capRng (.cnodeCap p r g) := by
  simp [capRng, objRefs]

/-- **No cap covers a childless untyped's region** (UtCh). -/
theorem vfh_noRef {σ : State Unit} (hU : UtInv'' σ) {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hu : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) {s : CslotPtr} {c : Cap}
    {r : ObjRef} (hs : SInvU.capAt σ s = some c) (hr : r ∈ capRng c) : r ∉ delR b n :=
  fun hR => desc_noKids hk (hU.2.1 u dev b n fi hu s c r hs hr hR)

/-- A `DRef` object lies outside a childless untyped's region. -/
theorem vfh_dref_out {σ : State Unit} (hU : UtInv'' σ) {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hu : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) {p : ObjRef}
    (h : DRef σ p) : p ∉ delR b n := by
  obtain ⟨s, r, g, hs⟩ := h
  exact vfh_noRef hU hu hk (by rw [vfh_capAt]; exact hs) (vfh_cn_capRng p r g)

/-- **The untyped's own slot lies outside its region** (RegNull). -/
theorem vfh_srcOut {σ : State Unit} (hU : UtInv'' σ) {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hu : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) : u.1 ∉ delR b n := by
  intro hR
  have := regNull_of hU.2.1 hU.2.2.1 u dev b n fi hu hk u _ hu hR
  cases this

/-! ## `delete_objects` -/

theorem vfh_detype {σ σd : State Unit} {R : Set ObjRef}
    (hk : ∀ p, σd.kheap p = if p ∈ R then none else σ.kheap p) (hv : VfhV σ) (hd : CnDom σ)
    (hno : ∀ (s : CslotPtr) q r g, capOpt (σ.kheap s.1) s.2 = some (.cnodeCap q r g) → q ∉ R) :
    VfhV σd ∧ CnDom σd := by
  refine ⟨fun p c h3 h6 => ?_, fun sl c hc => ?_⟩
  · rw [hk] at h3 h6
    split_ifs at h3 h6 with hp
    · simp [capOpt] at h3
    · exact hv p c h3 h6
  · intro p r g e l hl
    rw [hk] at hc
    split_ifs at hc with hp
    · simp [capOpt] at hc
    · have hq := hno sl p r g (by rw [← e]; exact hc)
      rw [hk, if_neg hq]
      exact hd sl c hc p r g e l hl

theorem vfh_notBad_detype {σ σd : State Unit} {R : Set ObjRef}
    (hk : ∀ p, σd.kheap p = if p ∈ R then none else σ.kheap p) {sl : CslotPtr} (hp : sl.1 ∉ R)
    (h : ¬ vfh_Bad σ sl) : ¬ vfh_Bad σd sl := by
  rintro ⟨e, h6⟩
  rw [hk, if_neg hp] at h6
  exact h ⟨e, h6⟩

/-! ## `retype_region` -/

theorem vfh_retypeRegionWith_out {bA : ApiObjectType → Nat → Nat} {rb : ObjRef} {n oB : Nat}
    {ty : ApiObjectType} {dev : Bool} {σ : State Unit} {y : List ObjRef × State Unit}
    (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev σ).1) :
    y.1 = retPtrs rb n (bA ty oB) ∧ ((ty = .untyped ∧ y.2 = σ) ∨ (ty ≠ .untyped ∧
      y.2 = { σ with kheap := retKh σ (retPtrs rb n (bA ty oB)) (defaultObject ty dev oB σ.curDomain) })) := by
  unfold retypeRegionWith at hy
  obtain ⟨a1, h1, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨a2, h2, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨a3, h3, hy⟩ := hy; obtain rfl := Set.mem_singleton_iff.1 hy
  refine ⟨rfl, ?_⟩
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    right
    obtain ⟨b1, g1, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g1
    obtain ⟨b2, g2, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g2
    obtain ⟨b3, g3, h3⟩ := h3; obtain rfl := Set.mem_singleton_iff.1 g3
    obtain rfl := Set.mem_singleton_iff.1 h3
    refine ⟨hty, ?_⟩
    exact congrArg (fun kh => ({ σ with kheap := kh } : State Unit)) (funext fun q => foldr_upd _ _ _ q)
  · rename_i hty
    left
    obtain rfl := Set.mem_singleton_iff.1 h3
    exact ⟨not_not.1 hty, rfl⟩

/-- The caps of a default object are null. -/
theorem vfh_default_null {ty : ApiObjectType} (hty : ty ≠ .untyped) {dev : Bool} {n : Nat} {d : Domain}
    {l : CnodeIndex} {c : Cap} (h : capOpt (some (defaultObject ty dev n d)) l = some c) : c = .nullCap := by
  cases ty with
  | untyped => exact absurd rfl hty
  | capTableObject =>
    simp only [defaultObject, capOpt, emptyCnode] at h
    split_ifs at h <;> first | exact (Option.some.inj h).symm | cases h
  | tcbObject =>
    simp only [defaultObject, capOpt, tcbCnodeMap, Function.update_apply] at h
    split_ifs at h <;> simp_all [defaultTcb]
  | _ => simp [defaultObject, capOpt] at h

theorem vfh_emptyCnode_wf (n : Nat) : wellFormedCnodeN n (emptyCnode n) := by
  unfold wellFormedCnodeN
  ext x
  simp [dom, emptyCnode]

/-- **`retype_region` at fresh addresses keeps `VS a`**; the new CNodes are full. -/
theorem vfh_retype {bA : ApiObjectType → Nat → Nat} {rb : ObjRef} {n oB : Nat} {ty : ApiObjectType} {dev : Bool}
    {a τ : State Unit} (hτ : VS a τ) (hf : ∀ q ∈ retPtrs rb n (bA ty oB), τ.kheap q = none)
    {y : List ObjRef × State Unit} (hy : y ∈ (retypeRegionWith (Z := Unit) bA rb n oB ty dev τ).1) :
    VS a y.2 ∧ y.1 = retPtrs rb n (bA ty oB) ∧ ∀ p ∈ y.1, ty = .capTableObject → CnFull y.2 p oB := by
  obtain ⟨e1, ⟨hty, e2⟩ | ⟨hty, e2⟩⟩ := vfh_retypeRegionWith_out hy
  · refine ⟨by rw [e2]; exact hτ, e1, fun p _ ht => ?_⟩
    rw [hty] at ht; cases ht
  · have hk : ∀ q, y.2.kheap q = if q ∈ retPtrs rb n (bA ty oB) then some (defaultObject ty dev oB τ.curDomain)
        else τ.kheap q := fun q => by rw [e2]; rfl
    have dk : DomK τ y.2 := by
      intro p l h
      rw [hk] at h
      split_ifs at h with hp
      · rw [hf p hp]; rfl
      · exact h
    refine ⟨⟨fun p c h3 h6 => ?_, hτ.2.1.trans dk, fun sl c hc => ?_⟩, e1, fun p hp ht => ?_⟩
    · rw [hk] at h3 h6
      split_ifs at h3 h6 with hp
      · rw [vfh_default_null hty h3]; exact vfh_null
      · exact hτ.1 p c h3 h6
    · rw [hk] at hc
      split_ifs at hc with hp
      · rw [vfh_default_null hty hc]; exact cnOk_null
      · exact (hτ.2.2 sl c hc).mono dk
    · subst ht
      rw [e1] at hp
      intro l hl
      rw [hk, if_pos hp]
      show capOpt (some (.cnode oB (emptyCnode oB))) l ≠ none
      simp only [capOpt, if_pos (vfh_emptyCnode_wf oB)]
      simp [emptyCnode, hl]

/-! ## `create_cap` and the retype body -/

theorem vs_createCap {σ0 : State Unit} (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) (hb : ¬ vfh_Bad σ0 x.1) (hk : CnOk σ0 (defaultCap ty x.2 sz dev)) :
    IK (VS σ0) (createCap (Z := Unit) ty sz src dev x) := by
  obtain ⟨d, o⟩ := x
  unfold createCap
  dsimp only
  exact ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ik_bind (vs_setCdt _) fun _ =>
    ik_bind (vs_doExtendedOp _) fun _ => ik_bind (vs_setOriginal _ _) fun _ => vs_setCap_nb hb hk

theorem vfh_defaultCap_ok {σ : State Unit} {ty : ApiObjectType} {o : ObjRef} {sz : Nat} {dev : Bool}
    (h : ty = .capTableObject → CnFull σ o sz) : CnOk σ (defaultCap ty o sz dev) := by
  cases ty with
  | capTableObject =>
    intro p r g e
    simp only [defaultCap, Cap.cnodeCap.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact h rfl
  | _ => exact cnOk_of_nc fun _ _ _ e => by simp [defaultCap] at e

theorem vfh_fresh_setCap {c : Cap} {sl : CslotPtr} {τ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setCap (Z := Unit) c sl τ).1) {ps : List ObjRef} (hf : ∀ q ∈ ps, τ.kheap q = none) :
    ∀ q ∈ ps, x.2.kheap q = none := by
  intro q hq
  have h := (setCap_out hx).1 q
  rw [hf q hq] at h
  cases e : x.2.kheap q with
  | none => rfl
  | some _ => rw [e] at h; simp at h

set_option maxHeartbeats 4000000 in
/-- **The retype body** (after the reset) keeps `VS a`. -/
theorem vfh_utMain {a τ : State Unit} (hτ : VS a τ) (srcSlot : CslotPtr) (base retypeBase : ObjRef)
    (newType : ApiObjectType) (objSz : Nat) (slots : List CslotPtr) (isDevice : Bool)
    (hsrc : ¬ vfh_Bad a srcSlot) (hdst : ∀ d ∈ slots, ¬ vfh_Bad a d)
    (hf : ∀ q ∈ retPtrs retypeBase slots.length (fl4ObjBitsApi newType objSz), τ.kheap q = none) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) srcSlot
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi newType objSz)
      let freeRef ← pure (retypeBase + totalObjectSize)
      setCap (.untypedCap isDevice base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) srcSlot
      let orefs ← retypeRegionWith fl4ObjBitsApi retypeBase slots.length objSz newType isDevice
      initArchObjects newType isDevice retypeBase slots.length objSz orefs
      NonDet.mapMx (createCap newType objSz srcSlot isDevice) (slots.zip orefs) : NonDet (State Unit) Unit) τ).1,
      VS a x.2 := by
  intro x hx
  obtain ⟨x1, h1, hx⟩ := hx
  obtain ⟨hs1, -⟩ := getCap_capAt h1
  obtain ⟨x2, h2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨x3, h3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 h3
  obtain ⟨x4, h4, hx⟩ := hx
  obtain ⟨x5, h5, hx⟩ := hx
  obtain ⟨x6, h6, hx⟩ := hx
  dsimp only at h4 h5 h6 hx
  have hτ1 : VS a x1.2 := by rw [hs1]; exact hτ
  have hv4 : VS a x4.2 := vs_setCap_nb hsrc vfh_cnOk_ut x1.2 hτ1 x4 h4
  have hf4 := vfh_fresh_setCap h4 (ps := retPtrs retypeBase slots.length (fl4ObjBitsApi newType objSz))
    (by rw [hs1]; exact hf)
  obtain ⟨hv5, e5, hcn⟩ := vfh_retype hv4 hf4 h5
  have hv6 : VS x5.2 x6.2 :=
    (by hv_auto : IK (VS x5.2) (initArchObjects (Z := Unit) newType isDevice retypeBase slots.length objSz x5.1))
      x5.2 (VS.refl hv5.cur) x6 h6
  have hloop : IK (VS x5.2) (NonDet.mapMx (createCap (Z := Unit) newType objSz srcSlot isDevice) (slots.zip x5.1)) := by
    refine vfh_ik_mapMx_mem _ fun p hp => ?_
    have hm := List.of_mem_zip hp
    exact vs_createCap _ _ _ _ p (fun hb => hdst p.1 hm.1 (hb.back hv5.2.1))
      (vfh_defaultCap_ok fun ht => hcn p.2 hm.2 ht)
  exact hv5.trans (hloop x6.2 hv6 x hx)

/-! ## The reset -/

macro "vfh_rs_auto" hs:term : tactic => `(tactic| repeat' (first
  | exact vs_setCap_nb $hs vfh_cnOk_ut
  | (refine ike_mapMEx_mem _ fun _ _ => ?_)
  | hv_leaf | ik_step0 | ik_unfold
  | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)
  | split))

set_option maxHeartbeats 4000000 in
/-- **The reset ends in `VS a`**, with the source and the destinations not `Bad` at `a`. -/
theorem vfh_reset {σ : State Unit} (hv : VfhV σ) (hd : CnDom σ) (hU : UtInv'' σ) {src : CslotPtr} {dev : Bool}
    {b : ObjRef} {n fi : Nat} (hc : SInvU.capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some src)
    {slots : List CslotPtr} (hdst : ∀ d ∈ slots, ¬ vfh_Bad σ d ∧ DRef σ d.1) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) src) σ).1,
      ∃ a, VS a y.2 ∧ ¬ vfh_Bad a src ∧ ∀ d ∈ slots, ¬ vfh_Bad a d := by
  have hsrc : ¬ vfh_Bad σ src :=
    vfh_notBad_ut hv hc
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
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨σ, VS.refl ⟨hv, hd⟩, hsrc, fun d hd' => (hdst d hd').1⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hkz := (deleteObjects_kheap hz).1
    have hno : ∀ (s : CslotPtr) q r g, capOpt (σ.kheap s.1) s.2 = some (.cnodeCap q r g) → q ∉ delR b n :=
      fun s q r g h => vfh_noRef hU hc hk (by rw [vfh_capAt]; exact h) (vfh_cn_capRng q r g)
    have hz0 := vfh_detype hkz hv hd hno
    have hsz : ¬ vfh_Bad z.2 src := vfh_notBad_detype hkz (vfh_srcOut hU hc hk) hsrc
    refine ⟨z.2, ?_, hsz, fun d hd' =>
      vfh_notBad_detype hkz (vfh_dref_out hU hc hk (hdst d hd').2) (hdst d hd').1⟩
    refine (?_ : IKE (VS z.2) _) z.2 (VS.refl hz0) y hy
    try dsimp only
    vfh_rs_auto hsz

/-! ## The untyped invocation -/

set_option maxHeartbeats 4000000 in
/-- **The untyped retype keeps `VfhV ∧ CnDom`**, from the decode's `UtRetOK` /
`VUt` and the carried `UtInv''` at the perform state. -/
theorem vfh_fl4InvokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hv : VfhV σ) (hd : CnDom σ)
    (hU : UtInv'' σ) (hok : UtRetOK σ ui) (hu : VUt σ ui) :
    ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, VfhV y.2 ∧ CnDom y.2 := by
  cases ui with
  | retype src reset base rb ty sz slots dev =>
    obtain ⟨bits, fi, hc, -, -, -, -, hk⟩ := id hok
    have hsrc : ¬ vfh_Bad σ src :=
      vfh_notBad_ut hv hc
    intro y hy
    simp only [fl4InvokeUntyped, invokeUntypedWith] at hy
    obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      cases reset
      · simp only [NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hz
        have hz2 : z.2 = σ := (ike_returnOk (P := fun s => s = σ) () :
          IKE (fun s => s = σ) (NonDetE.returnOk () : NonDetE (State Unit) Unit Unit)) σ rfl z hz
        have hf := utRet_fresh hU.1.1 hok
        rw [hz2] at hx
        exact (vfh_utMain (VS.refl ⟨hv, hd⟩) src base rb ty sz slots dev hsrc (fun d hd' => (hu d hd').1) hf x hx).cur
      · simp only [NonDetE.whenE, ↓reduceIte] at hz
        obtain ⟨a, ha, has, had⟩ := vfh_reset hv hd hU hc (hk rfl) hu z hz
        have hf := utRet_fresh_after_reset hU.1.1 hok z hz
        exact (vfh_utMain ha src base rb ty sz slots dev has had hf x hx).cur
    · cases reset
      · simp only [NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hz
        have hz2 : z.2 = σ := (ike_returnOk (P := fun s => s = σ) () :
          IKE (fun s => s = σ) (NonDetE.returnOk () : NonDetE (State Unit) Unit Unit)) σ rfl z hz
        rw [hz2]; exact ⟨hv, hd⟩
      · simp only [NonDetE.whenE, ↓reduceIte] at hz
        obtain ⟨a, ha, -, -⟩ := vfh_reset hv hd hU hc (hk rfl) hu z hz
        exact ha.cur

/-! ## MakePool -/

theorem vfh_retPtrs_one (rb : ObjRef) (o : Nat) : retPtrs rb 1 o = [rb] := by
  simp [retPtrs, ptrAdd]

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `VfhV ∧ CnDom`**, from the decode's `MpOK` / `VMp` and the
carried `UtInv''` at the perform state. -/
theorem vfh_makePool (iv : AsidControlInvocation) (σ : State Unit) (hv : VfhV σ) (hd : CnDom σ)
    (hU : UtInv'' σ) (hok : MpOK σ iv) (hm : VMp σ iv) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) iv σ).1, VfhV y.2 ∧ CnDom y.2 := by
  cases iv with
  | makePool frame slot parent base =>
    obtain ⟨dev, fi, hc, hk⟩ := hok
    obtain ⟨hsb, hsr⟩ := hm
    have hpb : ¬ vfh_Bad σ parent :=
      vfh_notBad_ut hv hc
    intro y hy
    simp only [performAsidControlInvocation] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hkz := (deleteObjects_kheap hz).1
    have hno : ∀ (s : CslotPtr) q r g, capOpt (σ.kheap s.1) s.2 = some (.cnodeCap q r g) →
        q ∉ delR frame page_bits :=
      fun s q r g h => vfh_noRef hU hc hk (by rw [vfh_capAt]; exact h) (vfh_cn_capRng q r g)
    have hz0 := vfh_detype hkz hv hd hno
    have hpo := vfh_srcOut hU hc hk
    have hpz : ¬ vfh_Bad z.2 parent := vfh_notBad_detype hkz hpo hpb
    have hsz : ¬ vfh_Bad z.2 slot := vfh_notBad_detype hkz (vfh_dref_out hU hc hk hsr) hsb
    -- the parent's cap is still the untyped cap
    have hcz : capOpt (z.2.kheap parent.1) parent.2 = some (.untypedCap dev frame page_bits fi) := by
      rw [hkz, if_neg hpo, ← vfh_capAt]; exact hc
    obtain ⟨x1, h1, hy⟩ := hy
    obtain ⟨hs1, hc1⟩ := getCap_capAt h1
    rw [vfh_capAt, hcz] at hc1
    obtain ⟨x2, h2, hy⟩ := hy
    have hv2 : VS z.2 x2.2 := by
      rw [← Option.some.inj hc1] at h2
      rw [hs1] at h2
      exact vs_setCap_nb hpz (vfh_maxFree_nc rfl |> cnOk_of_nc) z.2 (VS.refl hz0) x2 h2
    -- the pool's address is in the region, so it holds no object
    have hW : UtWf σ := hU.1.1.2.1
    obtain ⟨hn64, hfit⟩ := hW.fit hc
    have hfr : frame ∈ delR frame page_bits := by
      rw [mem_delR_iff hn64 hfit]
      have := Nat.two_pow_pos page_bits
      simp only [utR, Set.mem_setOf_eq]
      omega
    have hf2 : ∀ q ∈ retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0), x2.2.kheap q = none := by
      refine vfh_fresh_setCap h2 ?_
      intro q hq
      rw [vfh_retPtrs_one] at hq
      rw [List.mem_singleton.1 hq, hs1, hkz, if_pos hfr]
    obtain ⟨x3, h3, hy⟩ := hy
    rw [← retypeRegionWith_objBitsApi] at h3
    obtain ⟨hv3, -, -⟩ := vfh_retype hv2 hf2 h3
    have hsl3 : ¬ vfh_Bad x3.2 slot := fun hb => hsz (hb.back hv3.2.1)
    have hrest : IK (VS x3.2) (do
        capInsert (Z := Unit) (.archObjectCap (.asidPoolCap frame base)) parent slot
        NonDet.assert (asidLowBitsOf base = 0)
        let asidTable ← NonDet.gets fun s : State Unit => s.archState.x64AsidTable
        let asidTable' ← pure (Function.update asidTable (asidHighBitsOf base) (some frame))
        NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }) := by
      refine ik_bind (vs_capInsert _ _ (fun hb => (hsl3 hb).elim) (vfh_arch_ok _)) fun _ => ?_
      hv_auto
    exact (hv3.trans (hrest x3.2 (VS.refl hv3.cur) y hy)).cur

end

end Fl4Proofs.P3.SInv
