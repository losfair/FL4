/-
P3 (DESIGN.md §9), invariant line G1 (sl4): **`SL I K ∧ NtfnScB` across
`invoke_untyped` and MakePool** (the untyped half of sl3's `SlGap`; spec side
only). il2's SpecInvNtfnQLU with `NCap` (thread and SC caps) for thread caps:

* `NCF σ0 σ` (no new thread / SC caps), `NNC σ s` (no thread / SC cap in `s`):
  the reset's and the body's cap writes go to slots holding none.
* Detype (`sln_detype`, `sln_deleteObjects_p`): the region's slots are null (ut4's
  `regNull_of`), so every name survives; NtfnScB needs **no live object in the
  region** (`noLive_reg`): a live object is named (a cap naming it would be a CDT
  child of the childless untyped, UtInv3's UtCh) or idle (outside every cap's
  range: sg1's `IdleOutV` for `I.1`, `IdleScOutV` for `I.2`), so a surviving
  notification's SC (live: its `sc_ntfn` is set) survives too.
* Retype (`sln_retype_kh`, `sln_retypeRegionWith_p`): default objects are not
  live, hold null slots, and a default notification has no SC.
* **`sln_invokeUntyped`**, **`sln_makePool`**.
-/
import Fl4Proofs.P3.SpecInvSlP3
import Fl4Proofs.P3.SpecInvNtfnQLA
import Fl4Proofs.P3.SpecInvSbX4
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000
set_option maxErrors 2000

variable {I : ObjRef × ObjRef} {K : List ObjRef}

/-- No new thread / SC caps from `σ0` to `σ`. -/
def NCF (σ0 σ : State Unit) : Prop :=
  ∀ sl p c, SInvU.capAt σ sl = some c → NCap p c → SInvU.capAt σ0 sl = some c

/-- No thread / SC cap in `s`. -/
def NNC (σ : State Unit) (s : CslotPtr) : Prop := ∀ p c0, SInvU.capAt σ s = some c0 → ¬ NCap p c0

theorem ncf_refl (σ : State Unit) : NCF σ σ := fun _ _ _ h _ => h

theorem ncf_trans {σ0 σ1 σ2 : State Unit} (h1 : NCF σ0 σ1) (h2 : NCF σ1 σ2) : NCF σ0 σ2 :=
  fun sl p c h hn => h1 sl p c (h2 sl p c h hn) hn

theorem ncf_view {σ σ' : State Unit} (h : uV σ' = uV σ) : NCF σ σ' :=
  fun sl p c e _ => by rw [capAt_view h] at e; exact e

theorem nnc_ncf {σ0 σ : State Unit} {s : CslotPtr} (h : NCF σ0 σ) (h0 : NNC σ0 s) : NNC σ s :=
  fun p c e hn => h0 p c (h s p c e hn) hn

theorem nnc_view {σ σ' : State Unit} {s : CslotPtr} (h : uV σ' = uV σ) (h0 : NNC σ s) : NNC σ' s :=
  fun p c e => h0 p c (by rw [← capAt_view h]; exact e)

theorem nnc_of {σ : State Unit} {s : CslotPtr} {c : Cap} (hs : SInvU.capAt σ s = some c) (hc : ∀ p, ¬ NCap p c) :
    NNC σ s := fun p c0 e => by rw [hs] at e; cases e; exact hc p

theorem ncap_null (p : ObjRef) : ¬ NCap p .nullCap := fun h => h

/-- `set_cap` of a cap that is no thread / SC cap. -/
theorem setCap_nnc {c : Cap} {sl : CslotPtr} {σ : State Unit} {y : Unit × State Unit}
    (hc : ∀ p, ¬ NCap p c) (hy : y ∈ (setCap (Z := Unit) c sl σ).1) : NCF σ y.2 ∧ NNC y.2 sl := by
  have hv := hv_setCap c sl (uV σ) σ rfl y hy
  have hcap : ∀ x, SInvU.capAt y.2 x = if x = sl then some c else SInvU.capAt σ x := fun x => by
    show (uV y.2).2.1 x = _; rw [hv, vCap_cap]; rfl
  refine ⟨fun x p c' e hn => ?_, fun p c' e => ?_⟩
  · rw [hcap] at e
    split_ifs at e
    · injection e with e; subst e; exact absurd hn (hc p)
    · exact e
  · rw [hcap, if_pos rfl] at e
    injection e with e; subst e; exact hc p

/-- `SL I K ∧ NtfnScB` with no new names, from the two families and a cap-view frame. -/
theorem slnc_of {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h2 : NBK m)
    (hU : ∀ v, UK v m) : IK (fun s => SLN I K s ∧ NCF σ0 s) m := by
  intro σ h y hy
  exact ⟨⟨h1 σ h.1.1 y hy, h2 σ h.1.2 y hy⟩, ncf_trans h.2 (ncf_view (hU _ σ rfl y hy))⟩

/-! ## Detype -/

/-- **No live object in a childless untyped's region** (ScLiveT, UtInv3's UtCh,
the idle objects outside every cap's range). -/
theorem noLive_reg {σ : State Unit} (hS : ScLiveT I σ) (hU : UtInv'' σ)
    (h1 : IrqOutV (fun _ => I.1) (uV σ)) (h2 : IrqOutV (fun _ => I.2) (uV σ))
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) :
    ∀ p ∈ SInvU.delR b n, ∀ o, σ.kheap p = some o → ¬ liveO o := by
  intro p hp o ho hl
  by_cases e1 : p = I.1
  · subst e1; exact h1 default u _ hc hp
  by_cases e2 : p = I.2
  · subst e2; exact h2 default u _ hc hp
  obtain ⟨s, c, hs, hn⟩ := hS p o ho hl e1 e2
  exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c p hs (SInvU.objRefs_sub_capRng c (ncap_objRefs hn)) hp)

theorem sl_detype (D : Set ObjRef) {σ : State Unit} (h : SL I K σ)
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ D → c = .nullCap) :
    SL I K (detype D σ) ∧ NCF σ (detype D σ) := by
  have hT : ∀ t, HasN σ t → HasN (detype D σ) t := by
    rintro t ⟨p, c, hp, hn⟩
    refine ⟨p, c, ?_, hn⟩
    rw [capAt_detype, if_neg (fun hm => by obtain rfl := hR p c hp hm; exact ncap_null t hn)]; exact hp
  refine ⟨⟨fun t o ho hl h1 h2 => hT t ?_, fun t ht => (h.2 t ht).imp_left (hT t)⟩, fun p t c e _ => ?_⟩
  · have hk : (detype D σ).kheap t = if t ∈ D then none else σ.kheap t := rfl
    rw [hk] at ho
    split_ifs at ho
    exact h.1 t o ho hl h1 h2
  · rw [capAt_detype] at e
    split_ifs at e
    exact e

theorem nb_detype (D : Set ObjRef) {σ : State Unit} (h : NtfnScB σ)
    (hD : ∀ p ∈ D, ∀ o, σ.kheap p = some o → ¬ liveO o) : NtfnScB (detype D σ) := by
  have hk : ∀ x, (detype D σ).kheap x = if x ∈ D then none else σ.kheap x := fun _ => rfl
  intro n ntf c hn hc
  rw [hk] at hn
  split_ifs at hn
  obtain ⟨y, k, hy, hyn⟩ := h n ntf c hn hc
  refine ⟨y, k, ?_, hyn⟩
  have hl : liveO (.schedContext y k) := by
    show scLv y
    exact Or.inr (Or.inl (by rw [hyn]; exact Option.some_ne_none _))
  rw [hk, if_neg (fun hm => hD c hm _ hy hl)]; exact hy

theorem sln_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit)
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR ptr bits → c = .nullCap)
    (hD : ∀ p ∈ SInvU.delR ptr bits, ∀ o, σ.kheap p = some o → ¬ liveO o) (hσ : SLN I K σ) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits σ).1, SLN I K y.2 ∧ NCF σ y.2 := by
  intro y hy
  obtain ⟨s1, hk1, e⟩ := SInvB.deleteObjects_out' hy
  have hc1 : SInvU.capAt s1 = SInvU.capAt σ := by funext x; unfold SInvU.capAt; rw [hk1]
  have h1 : SL I K s1 := sl_of_kheap hk1 hσ.1
  rw [e]
  obtain ⟨h2, h3⟩ := sl_detype (SInvU.delR ptr bits) h1 (fun p c hp hm => hR p c (by rw [← hc1]; exact hp) hm)
  refine ⟨⟨h2, nb_detype _ (nb_of_kheap hk1 hσ.2) fun p hp o ho => hD p hp o (by rw [← hk1]; exact ho)⟩,
    fun p t c e' hn => by rw [← hc1]; exact h3 p t c e' hn⟩

/-! ## Retype -/

theorem dflt_nl {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) :
    ¬ liveO (defaultObject ty dev o d) := by
  cases ty
  case untyped => exact absurd rfl hty
  all_goals first
    | exact fun h => h
    | exact fun h => h rfl
    | (simp only [defaultObject, liveO, scLv, defaultSchedContext, defaultTcb]; simp)

theorem dflt_nsc {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (o : Nat) (d : Domain) :
    ∀ ntf, defaultObject ty dev o d = .notification ntf → ntf.ntfnSc = none := by
  intro ntf h
  cases ty
  case untyped => exact absurd rfl hty
  case notificationObject => simp only [defaultObject] at h; cases h; rfl
  all_goals (simp only [defaultObject] at h; cases h)

theorem sln_retype_kh {σ : State Unit} (ps : List ObjRef) (dO : KernelObject) (h : SLN I K σ)
    (hF : ∀ q ∈ ps, σ.kheap q = none) (hd : ¬ liveO dO) (hn : ∀ ntf, dO = .notification ntf → ntf.ntfnSc = none)
    (hc : ∀ i c, capView dO i = some c → c = .nullCap) :
    SLN I K { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } ∧
      NCF σ { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } := by
  have hk : ∀ q, ({ σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } :
      State Unit).kheap q = if q ∈ ps then some dO else σ.kheap q := fun q => foldr_upd ps dO σ.kheap q
  have hcap : ∀ p, SInvU.capAt { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } p =
      if p.1 ∈ ps then capView dO p.2 else SInvU.capAt σ p := by
    intro p
    unfold SInvU.capAt
    rw [hk]
    split_ifs <;> rfl
  have hT : ∀ t, HasN σ t →
      HasN { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some dO)) σ.kheap } t := by
    rintro t ⟨p, c, hp, hn'⟩
    refine ⟨p, c, ?_, hn'⟩
    rw [hcap, if_neg]; exact hp
    intro hm
    have := hF _ hm
    unfold SInvU.capAt at hp; rw [this] at hp; cases hp
  refine ⟨⟨⟨fun t o ho hl h1 h2 => hT t ?_, fun t ht => (h.1.2 t ht).imp_left (hT t)⟩, ?_⟩, fun p t c e hn' => ?_⟩
  · rw [hk] at ho
    split_ifs at ho
    · cases ho; exact absurd hl hd
    · exact h.1.1 t o ho hl h1 h2
  · intro n ntf c hn' hc'
    rw [hk] at hn'
    split_ifs at hn' with hm
    · cases hn'; rw [hn ntf rfl] at hc'; cases hc'
    · obtain ⟨y, k, hy, hyn⟩ := h.2 n ntf c hn' hc'
      refine ⟨y, k, ?_, hyn⟩
      rw [hk, if_neg (fun hm' => by rw [hF c hm'] at hy; cases hy)]; exact hy
  · rw [hcap] at e
    split_ifs at e
    · obtain rfl := hc _ _ e; exact absurd hn' (ncap_null t)
    · exact e

/-- `retype_region` at addresses holding no object. -/
theorem sln_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat) (ty : ApiObjectType)
    (dev : Bool) (σ : State Unit) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none) (hσ : SLN I K σ) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1, SLN I K y.2 ∧ NCF σ y.2 := by
  intro y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show SLN I K z3.2 ∧ NCF σ z3.2
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
    exact sln_retype_kh _ _ hσ hF (dflt_nl hty dev o _) (dflt_nsc hty dev o _)
      (fun i c hc => default_null hty dev o _ i hc)
  · rw [Set.mem_singleton_iff.1 h3]; exact ⟨hσ, ncf_refl _⟩

/-! ## The reset -/

/-- The reset's invariant: `SL I K ∧ NtfnScB`, no new names, none in the untyped's slot. -/
def RSl (I : ObjRef × ObjRef) (K : List ObjRef) (σ0 : State Unit) (s : CslotPtr) (σ : State Unit) : Prop :=
  SLN I K σ ∧ NCF σ0 σ ∧ NNC σ s

theorem rsl_of {σ0 : State Unit} {s : CslotPtr} {α : Type} {m : NonDet (State Unit) α}
    (h1 : SLK I K m) (h2 : NBK m) (hU : ∀ v, UK v m) : IK (RSl I K σ0 s) m := by
  intro σ h y hy
  have hv := hU _ σ rfl y hy
  exact ⟨⟨h1 σ h.1.1 y hy, h2 σ h.1.2 y hy⟩, ncf_trans h.2.1 (ncf_view hv), nnc_view hv h.2.2⟩

theorem rsl_setCapUt {σ0 : State Unit} {s : CslotPtr} (dev : Bool) (b : ObjRef) (n f : Nat) :
    IK (RSl I K σ0 s) (setCap (Z := Unit) (.untypedCap dev b n f) s) := by
  intro σ h y hy
  obtain ⟨h1, h2⟩ := setCap_nnc (c := .untypedCap dev b n f) (fun p e => e) hy
  exact ⟨⟨sl_setCap_nt _ _ σ h.2.2 h.1.1 y hy, nb_setCap _ _ σ h.1.2 y hy⟩, ncf_trans h.2.1 h1, h2⟩

macro "rsl_auto" : tactic => `(tactic| repeat' (first
  | (with_reducible exact rsl_setCapUt _ _ _ _)
  | (with_reducible refine ike_mapMEx (fun _ => ?_) _)
  | ik_step0
  | (exact rsl_of (by sl_auto) (by nb_auto) (fun _ => by uk_auto))
  | ik_unfold
  | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a childless untyped's slot. -/
theorem sln_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR b n → c = .nullCap)
    (hD : ∀ p ∈ SInvU.delR b n, ∀ o, σ.kheap p = some o → ¬ liveO o) (hσ : SLN I K σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, RSl I K σ s y.2 := by
  intro y hy
  have hnn0 : NNC σ s := nnc_of hc (fun p e => e)
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
    exact ⟨hσ, ncf_refl _, hnn0⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, objRefOf] at hz
    obtain ⟨hz0, hzt⟩ := sln_deleteObjects_p b n σ hR hD hσ z hz
    refine (?_ : IKE (RSl I K σ s) _) z.2 ⟨hz0, hzt, nnc_ncf hzt hnn0⟩ y hy
    try dsimp only
    rsl_auto

/-! ## The body -/

/-- `create_cap` into a slot holding no thread / SC cap; only that slot's cap changes. -/
theorem sl_createCap (ty : ApiObjectType) (sz : Nat) (s : CslotPtr) (dev : Bool) (d : CslotPtr) (o : ObjRef)
    (σ : State Unit) (hd : NNC σ d) (hσ : SL I K σ) :
    ∀ y ∈ (createCap (Z := Unit) ty sz s dev (d, o) σ).1,
      SL I K y.2 ∧ ∀ x, x ≠ d → SInvU.capAt y.2 x = SInvU.capAt σ x := by
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
  refine ⟨sl_setCap_nt _ _ y5.2 (fun p c e => hd p c (by rw [← hc5]; exact e)) (sl_of_kheap k5 hσ) y hy,
    fun x hx => ?_⟩
  show (uV y.2).2.1 x = _
  rw [hv, vCap_cap, if_neg hx]
  exact congrFun hc5 x

theorem sln_ccLoop (ty : ApiObjectType) (sz : Nat) (s : CslotPtr) (dev : Bool) :
    ∀ (l : List (CslotPtr × ObjRef)) (σ : State Unit), (l.map Prod.fst).Nodup → (∀ p ∈ l, NNC σ p.1) →
      SLN I K σ → ∀ y ∈ (NonDet.mapMx (createCap (Z := Unit) ty sz s dev) l σ).1, SLN I K y.2
  | [], σ, _, _, hσ => fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hσ
  | (d, o) :: l, σ, hn, hd, hσ => by
    intro y ⟨y1, h1, hy⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hb1, hk1⟩ := sl_createCap ty sz s dev d o σ (hd _ (List.mem_cons_self ..)) hσ.1 y1 h1
    have hn1 : NtfnScB y1.2 := nb_createCap ty sz s dev (d, o) σ hσ.2 y1 h1
    refine sln_ccLoop ty sz s dev l y1.2 hn.2 (fun p hp q c e => ?_) ⟨hb1, hn1⟩ y hy
    have hne : p.1 ≠ d := fun e' => hn.1 (by rw [← e']; exact List.mem_map.2 ⟨p, hp, rfl⟩)
    rw [hk1 _ hne] at e
    exact hd p (List.mem_cons_of_mem _ hp) q c e

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset. -/
theorem sln_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat) (slots : List CslotPtr)
    (dev : Bool) (σ : State Unit) (hs : NNC σ s) (hd : ∀ d ∈ slots, NNC σ d) (hn : slots.Nodup)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) (hσ : SLN I K σ) :
    ∀ x ∈ ((do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs)) σ).1, SLN I K x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : SLN I K x4.2 := ⟨sl_setCap_nt _ _ _ hs hσ.1 x4 hx4, nb_setCap _ _ _ hσ.2 x4 hx4⟩
  have ht4 := (setCap_nnc (c := .untypedCap _ _ _ _) (fun p e => e) hx4).1
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  obtain ⟨hb5, ht5⟩ := sln_retypeRegionWith_p fl4ObjBitsApi rb slots.length sz ty dev x4.2
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) hb4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 : SLN I K x6.2 := sln_ik (sl_initArchObjects _ _ _ _ _ _) (nb_initArchObjects _ _ _ _ _ _) _ hb5 x6 hx6
  have hv6 : uV x6.2 = uV x5.2 := (show ∀ v, UK v (initArchObjects (Z := Unit) ty dev rb slots.length sz x5.1) from
    fun _ => by uk_auto) _ x5.2 rfl x6 hx6
  have ht6 : NCF σ x6.2 := ncf_trans ht4 (ncf_trans ht5 (ncf_view hv6))
  exact sln_ccLoop ty sz s dev _ x6.2 (nodup_zip_fst hn)
    (fun p hp => nnc_ncf ht6 (hd _ (List.of_mem_zip hp).1)) hb6 x hx

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `SL I K ∧ NtfnScB`** (ut8's decode facts, `UtInv''`, the idle
objects outside every cap's range). -/
theorem sln_invokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hσ : SLN I K σ) (hU : UtInv'' σ)
    (h1 : IrqOutV (fun _ => I.1) (uV σ)) (h2 : IrqOutV (fun _ => I.2) (uV σ)) (hok : UtGapOK (uV σ) ui) :
    ∀ y ∈ (ExceptT.run (fl4InvokeUntyped (Z := Unit) ui) σ).1, SLN I K y.2 := by
  intro y hy
  obtain ⟨g1, g2, g3⟩ := hok
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok1 : UtRetOK σ (.retype s reset base rb ty sz slots dev) := utRetOK_of_V g1
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok1
  have hdn : ∀ d ∈ slots, NNC σ d := fun d hd => by
    have := g2 d hd; rw [show (uV σ).2.1 d = SInvU.capAt σ d from rfl] at this
    exact nnc_of this ncap_null
  have hnd : slots.Nodup := by
    obtain ⟨-, s1, nc, off, win, hs1, hcn, hle, he⟩ := g3
    exact (utDest_of hU.2.2.2.2.2.2.2 hs1 hcn hle he).1
  have hs0 : NNC σ s := nnc_of hc (fun p e => e)
  cases reset
  · have hfr := utRet_fresh hU.1.1 hok1
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact sln_utBody s base rb ty sz slots dev σ hs0 hdn hnd hfr hσ x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hk := hr rfl
    have hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR base bits → c = .nullCap :=
      fun p c hp hm => regNull_of hU.2.1 hU.2.2.1 s dev base bits fi hc hk p c hp hm
    have hbz := sln_resetUntypedCap s hc hR (noLive_reg hσ.1.1 hU h1 h2 hc hk) hσ z hz
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
      exact sln_utBody s base rb ty sz slots dev s1 hbz.2.2 (fun d hd => nnc_ncf hbz.2.1 (hdn d hd)) hnd hfz hbz.1 x hx

/-! ## MakePool -/

theorem sln_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hσ : SLN I K σ)
    (hU : UtInv'' σ) (h1 : IrqOutV (fun _ => I.1) (uV σ)) (h2 : IrqOutV (fun _ => I.2) (uV σ))
    (hok : MpOKN (uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, SLN I K y.2 := by
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hR : ∀ p c, SInvU.capAt σ p = some c → p.1 ∈ SInvU.delR frame page_bits → c = .nullCap :=
    fun p c hp hm => regNull_of hU.2.1 hU.2.2.1 parent dev frame page_bits fi hc hk p c hp hm
  have hfr : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  intro y hy
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hb1, ht1⟩ := sln_deleteObjects_p frame page_bits σ hR (noLive_reg hσ.1.1 hU h1 h2 hc' hk) hσ y1 hy1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' hy1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hfr]
  have hp1 : NNC y1.2 parent := nnc_ncf ht1 (nnc_of hc' fun p e => e)
  obtain ⟨y2, hy2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt hy2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, hy3, hy⟩ := hy
  have hb3 : SLN I K y3.2 := ⟨sl_setCap_nt _ _ _ hp1 hb1.1 y3 hy3, nb_setCap _ _ _ hb1.2 y3 hy3⟩
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out hy3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, hy4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at hy4
  have hb4 := (sln_retypeRegionWith_p objBitsApi frame 1 0 _ false y3.2 (fun q hq => by
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    have hq' : q = frame := by rw [hq]; simp [ptrAdd]
    subst hq'; exact hn3) hb3 y4 hy4).1
  refine sln_ik (?_ : SLK I K _) (?_ : NBK _) y4.2 hb4 y hy
  · sl_auto
  · nb_auto

end

end Fl4Proofs.P3.SInvL
