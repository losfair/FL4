/-
P3 (DESIGN.md §9), invariant line G1 (il2): **IfLiveT across `invoke_untyped`**
(the untyped half of `PerfGapIL`; spec side only).

No step of `invoke_untyped` removes a thread cap or makes a thread live:
* `TCF σ0 σ` (no new thread caps: every thread cap of `σ` sat in the same slot
  at `σ0`), `NTC σ s` (no thread cap in `s`): the reset's and the body's cap
  writes go to slots holding none (the untyped's own slot; the destinations,
  null at the decode, ut3's `DestNull`, and distinct, ut8's `utDest_of`).
* `il_detype` / `il_deleteObjects_p`: the reset's region holds only null slots
  (ut4's `regNull_of`, the untyped childless), so every thread cap survives.
* `il_retype_kh` / `il_retypeRegionWith_p`: the retype writes default objects
  (Inactive TCBs, null slots, ut8's `default_null`) at addresses holding no
  object (ut1's `utRet_fresh` / `utRet_fresh_after_reset`).
* **`il_invokeUntyped (ui) (σ) (hσ : IL K σ) (hU : UtInv'' σ) (hok : UtGapOK (uV σ) ui)`**.
-/
import Fl4Proofs.P3.SpecInvNtfnQLP
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

/-- No new thread caps from `σ0` to `σ`. -/
def TCF (σ0 σ : State Unit) : Prop :=
  ∀ sl t, SInvU.capAt σ sl = some (.threadCap t) → SInvU.capAt σ0 sl = some (.threadCap t)

/-- No thread cap in `s`. -/
def NTC (σ : State Unit) (s : CslotPtr) : Prop := ∀ t, SInvU.capAt σ s ≠ some (.threadCap t)

theorem tcf_refl (σ : State Unit) : TCF σ σ := fun _ _ h => h

theorem tcf_trans {σ0 σ1 σ2 : State Unit} (h1 : TCF σ0 σ1) (h2 : TCF σ1 σ2) : TCF σ0 σ2 :=
  fun sl t h => h1 sl t (h2 sl t h)

theorem capAt_view {σ σ' : State Unit} (h : uV σ' = uV σ) : SInvU.capAt σ' = SInvU.capAt σ :=
  congrArg (fun w : UView => w.2.1) h

theorem tcf_view {σ σ' : State Unit} (h : uV σ' = uV σ) : TCF σ σ' :=
  fun sl t e => by rw [capAt_view h] at e; exact e

theorem ntc_tcf {σ0 σ : State Unit} {s : CslotPtr} (h : TCF σ0 σ) (h0 : NTC σ0 s) : NTC σ s :=
  fun t e => h0 t (h s t e)

/-- `set_cap` of a non-thread cap: no new thread caps, and the slot holds none. -/
theorem setCap_ntc {c : Cap} {sl : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hc : ∀ t, c ≠ .threadCap t) (hy : y ∈ (setCap (Z := Unit) c sl σ).1) : TCF σ y.2 ∧ NTC y.2 sl := by
  have hv := hv_setCap c sl (uV σ) σ rfl y hy
  have hcap : ∀ x, SInvU.capAt y.2 x = if x = sl then some c else SInvU.capAt σ x := fun x => by
    show (uV y.2).2.1 x = _; rw [hv, vCap_cap]; rfl
  refine ⟨fun x t e => ?_, fun t e => ?_⟩
  · rw [hcap] at e
    split_ifs at e
    · injection e with e; exact absurd e (hc t)
    · exact e
  · rw [hcap, if_pos rfl] at e
    injection e with e; exact hc t e

/-! ## Detype -/

theorem capAt_detype (D : Set ObjRef) (σ : State Unit) (p : CslotPtr) :
    SInvU.capAt (detype D σ) p = if p.1 ∈ D then none else SInvU.capAt σ p := by
  unfold SInvU.capAt
  show (match (if p.1 ∈ D then none else σ.kheap p.1) with | some o => capView o p.2 | none => none) = _
  split_ifs <;> rfl

theorem il_detype (D : Set ObjRef) {σ : State Unit} (h : IL Kq σ)
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ D → c = .nullCap) :
    IL Kq (detype D σ) ∧ TCF σ (detype D σ) := by
  have hT : ∀ t, HasTC σ t → HasTC (detype D σ) t := by
    rintro t ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [capAt_detype, if_neg (fun hm => by cases hR p _ hp hm)]; exact hp
  refine ⟨⟨fun t y hy hl => hT t ?_, fun t ht => hT t (h.2 t ht)⟩, fun p t e => ?_⟩
  · have hk : (detype D σ).kheap t = if t ∈ D then none else σ.kheap t := rfl
    rw [hk] at hy
    split_ifs at hy
    exact h.1 t y hy hl
  · rw [capAt_detype] at e
    split_ifs at e
    exact e

theorem il_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR ptr bits → c = .nullCap) (hσ : IL Kq σ) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits σ).1, IL Kq y.2 ∧ TCF σ y.2 := by
  intro y hy
  obtain ⟨s1, hk1, e⟩ := deleteObjects_out hy
  have hc1 : SInvU.capAt s1 = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [hk1]
  have h1 : IL Kq s1 := il_of_kheap hk1 hσ
  rw [e]
  obtain ⟨h2, h3⟩ := il_detype (SInvU.delR ptr bits) h1 (fun p c hp hm => hR p c (by rw [← hc1]; exact hp) hm)
  exact ⟨h2, fun p t e' => by rw [← hc1]; exact h3 p t e'⟩

/-! ## Retype -/

theorem il_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : IL Kq σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none) (hd : ∀ y, dO = .tcb y → ¬ liveSt y.tcbState)
    (hc : ∀ i c, capView dO i = some c → c = .nullCap) :
    IL Kq { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } ∧
      TCF σ { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  have hk : ∀ q, ({ σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } :
      State Unit).kheap q = if q ∈ ps then some dO else σ.kheap q := fun q => foldr_upd ps dO σ.kheap q
  have hcap : ∀ p, SInvU.capAt { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } p =
      if p.1 ∈ ps then capView dO p.2 else SInvU.capAt σ p := by
    intro p
    unfold SInvU.capAt
    rw [hk]
    split_ifs <;> rfl
  have hT : ∀ t, HasTC σ t → HasTC { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } t := by
    rintro t ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [hcap, if_neg]; exact hp
    intro hm
    have := hF _ hm
    unfold SInvU.capAt at hp; rw [this] at hp; cases hp
  refine ⟨⟨fun t y hy hl => hT t ?_, fun t ht => hT t (h.2 t ht)⟩, fun p t e => ?_⟩
  · rw [hk] at hy
    split_ifs at hy
    · cases hy; exact absurd hl (hd y rfl)
    · exact h.1 t y hy hl
  · rw [hcap] at e
    split_ifs at e
    · cases hc _ _ e
    · exact e

theorem dflt_live {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) :
    ∀ y, defaultObject ty dev o d = .tcb y → ¬ liveSt y.tcbState := by
  intro y h
  cases ty
  case untyped => exact absurd rfl hty
  all_goals (simp only [defaultObject] at h) <;> first
    | (cases h; done)
    | (cases h; simp [defaultTcb, liveSt])

/-- `retype_region` at addresses holding no object. -/
theorem il_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none) (hσ : IL Kq σ) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1, IL Kq y.2 ∧ TCF σ y.2 := by
  intro y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show IL Kq z3.2 ∧ TCF σ z3.2
  unfold NonDet.when at h3
  split at h3
  · rename_i hty
    obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact il_retype_kh _ _ hσ hF (dflt_live hty dev o _) (fun i c hc => default_null hty dev o _ i hc)
  · rw [Set.mem_singleton_iff.1 h3]; exact ⟨hσ, tcf_refl _⟩

/-! ## The reset -/

/-- The reset's invariant: IfLiveT, no new thread caps, none in the untyped's slot. -/
def RI (K : List ObjRef) (σ0 : State Unit) (s : CslotPtr) (σ : State Unit) : Prop :=
  IL K σ ∧ TCF σ0 σ ∧ NTC σ s

theorem ri_of {K : List ObjRef} {σ0 : State Unit} {s : CslotPtr} {α : Type} {m : NonDet (State Unit) α}
    (hL : ILK K m) (hU : ∀ v, UK v m) : IK (RI K σ0 s) m := by
  intro σ h y hy
  have hv := hU _ σ rfl y hy
  exact ⟨hL σ h.1 y hy, tcf_trans h.2.1 (tcf_view hv), fun t e => h.2.2 t (by rw [← capAt_view hv]; exact e)⟩

theorem ri_setCapUt {K : List ObjRef} {σ0 : State Unit} {s : CslotPtr} (dev : Bool) (b : ObjRef) (n f : Nat) :
    IK (RI K σ0 s) (setCap (Z := Unit) (.untypedCap dev b n f) s) := by
  intro σ h y hy
  obtain ⟨h1, h2⟩ := setCap_ntc (fun t e => by cases e) hy
  exact ⟨il_setCap_nt _ _ σ h.2.2 h.1 y hy, tcf_trans h.2.1 h1, h2⟩

macro "ri_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact ri_setCapUt _ _ _ _)
  | (with_reducible refine ike_mapMEx (fun _ => ?_) _)
  | ik_step0
  | (exact ri_of (by il_auto) (fun _ => by uk_auto))
  | ik_unfold
  | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a childless untyped's slot (its region's slots are null). -/
theorem il_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR b n → c = .nullCap) (hσ : IL Kq σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, RI Kq σ s y.2 := by
  intro y hy
  have hntc0 : NTC σ s := fun t e => by rw [hc] at e; cases e
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
    exact ⟨hσ, tcf_refl _, hntc0⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [bitsOf, objRefOf] at hz
    obtain ⟨hz0, hzt⟩ := il_deleteObjects_p (Kq := Kq) b n σ hR hσ z hz
    refine (?_ : IKE (RI Kq σ s) _) z.2 ⟨hz0, hzt, ntc_tcf hzt hntc0⟩ y hy
    try dsimp only
    ri_auto

/-! ## The body -/

theorem nodup_zip_fst {α β : Type} : ∀ {l1 : List α} {l2 : List β}, l1.Nodup → ((l1.zip l2).map Prod.fst).Nodup
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: l1, b :: l2, h => by
    rw [List.nodup_cons] at h
    simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => h.1 ?_, nodup_zip_fst h.2⟩
    obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
    have := (List.of_mem_zip hp).1
    rw [e] at this; exact this

/-- `create_cap` into a slot holding no thread cap; only that slot's cap changes. -/
theorem il_createCap (ty : ApiObjectType) (sz : Nat) (s : CslotPtr) (dev : Bool) (d : CslotPtr) (o : ObjRef)
    (σ : State Unit) (hd : NTC σ d) (hσ : IL Kq σ) :
    ∀ y ∈ (createCap (Z := Unit) ty sz s dev (d, o) σ).1,
      IL Kq y.2 ∧ ∀ x, x ≠ d → SInvU.capAt y.2 x = SInvU.capAt σ x := by
  intro y hy
  unfold createCap at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [mem_gets h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have hk : IK (fun s => s.kheap = σ.kheap) (setCdt (Z := Unit) (Function.update σ.cdt d (some s))) := by
    repeat' (first | ik_step0 | ik_unfold)
  have k3 := hk σ rfl y3 h3
  obtain ⟨y4, h4, hy⟩ := hy
  have k4 : y4.2.kheap = σ.kheap :=
    (ik_doExtendedOp (P := fun s => s.kheap = σ.kheap) (fun _ _ h => h) _) y3.2 k3 y4 h4
  obtain ⟨y5, h5, hy⟩ := hy
  have k5 : y5.2.kheap = σ.kheap := (show IK (fun s => s.kheap = σ.kheap) (setOriginal (Z := Unit) d true) by
    repeat' (first | ik_step0 | ik_unfold)) y4.2 k4 y5 h5
  have hc5 : SInvU.capAt y5.2 = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [k5]
  have hv := hv_setCap (defaultCap ty o sz dev) d (uV y5.2) y5.2 rfl y hy
  refine ⟨il_setCap_nt _ _ y5.2 (fun t e => hd t (by rw [← hc5]; exact e)) (il_of_kheap k5 hσ) y hy, fun x hx => ?_⟩
  show (uV y.2).2.1 x = _
  rw [hv, vCap_cap, if_neg hx]
  exact congrFun hc5 x

theorem il_ccLoop (ty : ApiObjectType) (sz : Nat) (s : CslotPtr) (dev : Bool) :
    ∀ (l : List (CslotPtr × ObjRef)) (σ : State Unit), (l.map Prod.fst).Nodup → (∀ p ∈ l, NTC σ p.1) → IL Kq σ →
      ∀ y ∈ (NonDet.mapMx (createCap (Z := Unit) ty sz s dev) l σ).1, IL Kq y.2
  | [], σ, _, _, hσ => fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hσ
  | (d, o) :: l, σ, hn, hd, hσ => by
    intro y ⟨y1, h1, hy⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hb1, hk1⟩ := il_createCap ty sz s dev d o σ (hd _ (List.mem_cons_self ..)) hσ y1 h1
    refine il_ccLoop ty sz s dev l y1.2 hn.2 (fun p hp t e => ?_) hb1 y hy
    have hne : p.1 ≠ d := fun e' => hn.1 (by rw [← e']; exact List.mem_map.2 ⟨p, hp, rfl⟩)
    rw [hk1 _ hne] at e
    exact hd p (List.mem_cons_of_mem _ hp) t e

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset. -/
theorem il_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hs : NTC σ s) (hd : ∀ d ∈ slots, NTC σ d) (hn : slots.Nodup)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) (hσ : IL Kq σ) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) σ).1, IL Kq x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : IL Kq x4.2 := il_setCap_nt _ _ _ hs hσ x4 hx4
  have ht4 := (setCap_ntc (fun t e => by cases e) hx4).1
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  obtain ⟨hb5, ht5⟩ := il_retypeRegionWith_p (Kq := Kq) fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 : IL Kq x6.2 := (show ILK Kq (initArchObjects (Z := Unit) ty dev rb slots.length sz x5.1) by il_auto) _ hb5 x6 hx6
  have hv6 : uV x6.2 = uV x5.2 := (show ∀ v, UK v (initArchObjects (Z := Unit) ty dev rb slots.length sz x5.1) from
    fun _ => by uk_auto) _ x5.2 rfl x6 hx6
  have ht6 : TCF σ x6.2 := tcf_trans ht4 (tcf_trans ht5 (tcf_view hv6))
  exact il_ccLoop ty sz s dev _ x6.2 (nodup_zip_fst hn)
    (fun p hp => ntc_tcf ht6 (hd _ (List.of_mem_zip hp).1)) hb6 x hx

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps IfLiveT** (with `K`), from ut8's decode facts and `UtInv''`. -/
theorem il_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hσ : IL Kq σ) (hU : UtInv'' σ)
    (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, IL Kq y.2 := by
  intro y hy
  obtain ⟨h1, h2, h3⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok1 : UtRetOK σ (.retype s reset base rb ty sz slots dev) := utRetOK_of_V h1
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok1
  have hdn : ∀ d ∈ slots, NTC σ d := fun d hd t e => by
    have := h2 d hd; rw [show (uV σ).2.1 d = SInvU.capAt σ d from rfl] at this; rw [this] at e; cases e
  have hnd : slots.Nodup := by
    obtain ⟨-, s1, nc, off, win, hs1, hcn, hle, he⟩ := h3
    exact (utDest_of hU.2.2.2.2.2.2.2 hs1 hcn hle he).1
  have hs0 : NTC σ s := fun t e => by rw [hc] at e; cases e
  cases reset
  · have hfr := utRet_fresh hU.1.1 hok1
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact il_utBody s base rb ty sz slots dev σ hs0 hdn hnd hfr hσ x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR base bits → c = .nullCap :=
      fun p c hp hm => regNull_of hU.2.1 hU.2.2.1 s dev base bits fi hc (hr rfl) p c hp hm
    have hbz := il_resetUntypedCap (Kq := Kq) s hc hR hσ z hz
    have hfz := utRet_fresh_after_reset hU.1.1 hok1 z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz.1)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz.1)
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact il_utBody s base rb ty sz slots dev s1 hbz.2.2 (fun d hd => ntc_tcf hbz.2.1 (hdn d hd)) hnd hfz hbz.1 x hx


/-! ## `PerfGapIL` reduced to the arch performs -/

/-- **[P] The arch performs keep `IL K`** (what remains of `PerfGapIL`; not an
invariant premise but an unproved lemma about one perform family): every
`set_cap` of an arch perform overwrites the invoked arch / VSpace cap's slot
(ut8's `ArchOKN`: `MapOK`, the unmap's slot holds the decoded cap) or a null
destination (MakePool's pool slot, DeriveSubframe's destinations), MakePool's
detype frees a childless untyped's region (null slots, ut4's `RegNull`) and its
retype a fresh address; no TCB state is written. l4v:
`arch_perform_invocation_invs`, `perform_asid_control_invocation_invs`. -/
def PerfGapILA : Prop :=
  ∀ (N : Irq → ObjRef) (K : List ObjRef) (ai : Fl4ArchInvocation) (σ : State Unit),
    ILP N K σ → NodeIs N σ → DecodedFrom (uV σ) (.invokeArchObject ai) →
      ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) ai).run σ).1, IL K y.2

/-- `PerfGapIL` from the arch half: the untyped performs are `il_invokeUntyped`. -/
theorem perfGapIL_of (hA : PerfGapILA) : PerfGapIL := by
  intro N K blk call don inv σ hgap hσ hN hD y hy
  cases inv with
  | invokeUntyped ui =>
    obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
    have hf : GapOKN (uV σ) (.invokeUntyped ui) :=
      okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    exact il_invokeUntyped ui σ hσ.1.1 hσ.2.1 hf z hz
  | invokeArchObject ai =>
    simp only [fl4PerformInvocation] at hy
    exact hA N K ai σ hσ hN hD y hy
  | _ => exact (hgap : False).elim

end

end Fl4Proofs.P3.SInv
