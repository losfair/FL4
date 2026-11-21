/-
P3 (DESIGN.md §9), invariant line G1 (rd8n): **`Rdy` across retype / detype**:
the Untyped perform (with or without reset) and ASIDControl's MakePool (spec
side only, outside the JAtZ cone; KENTRY-PLAN rd8j handoff 3, rd8h item 2).

Unlike `BlockedScActive` (rd8k's `bsa_detype`), `Rdy` is not kept by removing
objects: a queued thread or its SC removed breaks R1. What `Rdy` reads of the
heap is the bound TCBs with their SCs (R1 / R2 / R4 / R3 through `RdyT` /
`ActB`), the active SCs (`RV`) and the idle SC (`IdleHd`). So:

* `RF σ σ'`: every object of σ' is σ's or fresh (`FreshR`: an unbound TCB, an
  inactive SC), every bound TCB of σ with an SC keeps both objects, the idle SC
  is kept, queues / action / release queue / time / idle pointer unchanged.
  **`rdy_rf : Rdy σ → RF σ σ' → Rdy σ'`.**
* `rf_detype` (no bound TCB / its SC / the idle SC in the region), `rf_retype`
  (addresses holding no object, not the idle SC; `freshR_default`).
* **`bnd_out`**: sl's carried `ScLiveT (idleThread, idleSc)` (a live object —
  a bound TCB, an SC with a TCB — other than the idle thread / SC is named by a
  thread / SC cap) with ut's `UtInv''` puts no live object in a childless
  untyped's region (ctq15's `rnDet_of_live` argument); the idle thread and the
  idle SC are outside every cap's range (sg / vi3's `IdleOutV`, ut7 / vi3's
  `IdleScOutV`); the SC of a bound TCB is bound by sb2's `ScBackS`.
  `retPtrs_delR`: the retype addresses lie in the untyped's region.
* The reset's chunk loop runs `preemption_point`, which keeps `Rdy` only with
  `ValidMachineTime` (rd8f's `rdy_preemptionPoint`): the bundle `UB := Rdy ∧
  ValidMachineTime` (`ub_of`, `ub_preemptionPoint`, `ub_auto`).
* **`rd_fl4InvokeUntyped`**, **`rd_makePool`**, **`archOK_asid`** (rd8h's
  `ArchOK` for ASIDControl), from carried facts at the perform: `Rdy`,
  `ValidMachineTime`, `UtInv''`, `ScLiveT`, `IdleOutV`, `ScBackS`, `IdleScOutV` and the
  decode's `UtRetOK` / `MpOKN`.
-/
import Fl4Proofs.P3.SpecInvRd8hP
import Fl4Proofs.P3.SpecInvRd8fC
import Fl4Proofs.P3.SpecInvSbE
import Fl4Proofs.P3.SpecInvSlK
import Fl4Proofs.P3.SpecInvSgE
import Fl4Proofs.P3.SpecInvUtR
import Fl4Proofs.P3.SpecInvUtP1
import Fl4Proofs.P3.SpecInvUtP5
import Fl4Proofs.P3.SpecInvSlI6
import Fl4Proofs.P3.SpecInvValidMachineTimeGen
open Classical

namespace Fl4Proofs.P3.SInvR.B8n
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The frame -/

/-- What a fresh object may be, for `Rdy`: an unbound TCB, an inactive SC, or any other kind. -/
def FreshR (o : KernelObject) : Prop :=
  (∀ x, o = .tcb x → x.tcbSchedContext = none) ∧ (∀ y n, o = .schedContext y n → scActive y = false)

/-- **The heap frame `Rdy` needs** (module docstring). -/
structure RF (σ σ' : State Unit) : Prop where
  old : ∀ q o, σ'.kheap q = some o → σ.kheap q = some o ∨ FreshR o
  keep : ∀ q x c y n, σ.kheap q = some (.tcb x) → x.tcbSchedContext = some c →
    σ.kheap c = some (.schedContext y n) → σ'.kheap q = σ.kheap q ∧ σ'.kheap c = σ.kheap c
  idle : σ'.kheap σ.idleSc = σ.kheap σ.idleSc
  rq : σ'.readyQueues = σ.readyQueues
  act : σ'.schedulerAction = σ.schedulerAction
  rel : σ'.releaseQueue = σ.releaseQueue
  time : σ'.curTime = σ.curTime
  isc : σ'.idleSc = σ.idleSc

theorem rdyT_rf {σ σ' : State Unit} (hF : RF σ σ') {t : ObjRef} (h : RdyT σ t) : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha, hr⟩ := h
  obtain ⟨e1, e2⟩ := hF.keep t x c y n hx hc hy
  exact ⟨x, c, y, n, by rw [e1]; exact hx, hc, by rw [e2]; exact hy, ha, by rw [hF.time]; exact hr⟩

theorem actB_rf {σ σ' : State Unit} (hF : RF σ σ') {t : ObjRef} (h : ActB σ t) : ActB σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha⟩ := h
  obtain ⟨e1, e2⟩ := hF.keep t x c y n hx hc hy
  exact ⟨x, c, y, n, by rw [e1]; exact hx, hc, by rw [e2]; exact hy, ha⟩

/-- **`Rdy` along `RF`.** -/
theorem rdy_rf {σ σ' : State Unit} (h : Rdy σ) (hF : RF σ σ') : Rdy σ' := by
  obtain ⟨h1, h2, h3, hv, h4, hI⟩ := h
  refine ⟨fun d p t ht => rdyT_rf hF (h1 d p t (by rw [hF.rq] at ht; exact ht)),
    fun t ht => rdyT_rf hF (h2 t (by rw [hF.act] at ht; exact ht)), ?_, ?_,
    fun t ht => actB_rf hF (h4 t (by rw [hF.rel] at ht; exact ht)), ?_⟩
  · intro t x c hx hb hc
    rcases hF.old t _ hx with hx' | hfr
    · exact rdyT_rf hF (h3 t x c hx' hb hc)
    · rw [hfr.1 x rfl] at hc; cases hc
  · intro p y n hp ha
    rcases hF.old p _ hp with hp' | hfr
    · exact hv p y n hp' ha
    · rw [hfr.2 y n rfl] at ha; cases ha
  · intro y n hy
    have hy' : σ.kheap σ.idleSc = some (.schedContext y n) := by rw [← hF.idle, ← hF.isc]; exact hy
    rw [hF.time]; exact hI y n hy'

/-! ## Detype and retype -/

/-- **Removing a region** with no bound TCB, no SC of one, and not the idle SC. -/
theorem rf_detype (D : Set ObjRef) (σ : State Unit) (ms : MachineState)
    (hD : ∀ q x c y n, σ.kheap q = some (.tcb x) → x.tcbSchedContext = some c →
      σ.kheap c = some (.schedContext y n) → q ∉ D ∧ c ∉ D) (hI : σ.idleSc ∉ D) :
    RF σ (detype D { σ with machineState := ms }) where
  old q o h := by
    change (if q ∈ D then none else σ.kheap q) = _ at h
    split_ifs at h; exact Or.inl h
  keep q x c y n hx hc hy := by
    obtain ⟨h1, h2⟩ := hD q x c y n hx hc hy
    refine ⟨?_, ?_⟩
    · show (if q ∈ D then none else σ.kheap q) = σ.kheap q; rw [if_neg h1]
    · show (if c ∈ D then none else σ.kheap c) = σ.kheap c; rw [if_neg h2]
  idle := by show (if σ.idleSc ∈ D then none else σ.kheap σ.idleSc) = _; rw [if_neg hI]
  rq := rfl
  act := rfl
  rel := rfl
  time := rfl
  isc := rfl

theorem freshR_default {ty : ApiObjectType} (hty : ty ≠ .untyped) (dev : Bool) (n : Nat) (d : Domain) :
    FreshR (defaultObject ty dev n d) := by
  cases ty
  case untyped => exact absurd rfl hty
  all_goals
    refine ⟨fun y h => ?_, fun y m h => ?_⟩ <;> simp only [defaultObject] at h <;>
      first | (cases h; done) | (cases h; rfl) | (subst h; rfl) | (obtain ⟨rfl, -⟩ := h; rfl) | (cases h; decide) | (obtain ⟨rfl, -⟩ := h; decide)

/-- **Writing fresh objects** at addresses holding no object, not the idle SC. -/
theorem rf_retype (σ : State Unit) (ps : List ObjRef) (o : KernelObject) (ho : FreshR o)
    (hF : ∀ q ∈ ps, σ.kheap q = none) (hI : σ.idleSc ∉ ps) :
    RF σ { σ with kheap := ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap } where
  old q o' h := by
    change (ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap) q = _ at h
    rw [SInvU.foldr_upd] at h
    split_ifs at h with hq
    · cases h; exact Or.inr ho
    · exact Or.inl h
  keep q x c y n hx hc hy := by
    refine ⟨?_, ?_⟩
    · show (ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap) q = σ.kheap q
      rw [SInvU.foldr_upd, if_neg (fun hm => by rw [hF q hm] at hx; cases hx)]
    · show (ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap) c = σ.kheap c
      rw [SInvU.foldr_upd, if_neg (fun hm => by rw [hF c hm] at hy; cases hy)]
  idle := by
    show (ps.foldr (fun p kh => Function.update kh p (some o)) σ.kheap) σ.idleSc = _
    rw [SInvU.foldr_upd, if_neg hI]
  rq := rfl
  act := rfl
  rel := rfl
  time := rfl
  isc := rfl

/-! ## The region facts -/

/-- **No live object in a childless untyped's region** (sl's ScLiveT + UtInv''; the idle thread
and the idle SC by IdleOutV / IdleScOutV). -/
theorem bnd_out {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ)
    (hIt : SInvG.IdleOutV σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ)
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u)
    {p : ObjRef} {o : KernelObject} (hp : σ.kheap p = some o) (hl : SInvL.liveO o) : p ∉ SInvU.delR b n := by
  intro hm
  by_cases h1 : p = σ.idleThread
  · subst h1; exact hIt 0 u _ hc hm
  by_cases h2 : p = σ.idleSc
  · subst h2; exact hO 0 u _ hc hm
  obtain ⟨s, c, hs, hn⟩ := hL p o hp hl h1 h2
  exact SInvU.desc_noKids hk (hU.2.1 u dev b n fi hc s c p hs (SInvU.objRefs_sub_capRng c (SInvL.ncap_objRefs hn)) hm)

/-- The detype hypothesis of `rf_detype` from `bnd_out` and ScBackS. -/
theorem bnd_pair {σ : State Unit} (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ)
    (hIt : SInvG.IdleOutV σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hB : SInvB.ScBackS σ)
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠ some u) :
    ∀ q x c y m, σ.kheap q = some (.tcb x) → x.tcbSchedContext = some c →
      σ.kheap c = some (.schedContext y m) → q ∉ SInvU.delR b n ∧ c ∉ SInvU.delR b n := by
  intro q x c y m hx hcq _
  refine ⟨bnd_out hU hL hIt hO hc hk hx (show x.tcbSchedContext ≠ none by rw [hcq]; simp), ?_⟩
  obtain ⟨y', k', hy', ht', -⟩ := hB q x c hx hcq
  exact bnd_out hU hL hIt hO hc hk hy' (show SInvL.scLv y' from Or.inl (by rw [ht']; simp))

/-- The idle SC is outside every held untyped's region (`IdleScOutV`). -/
theorem idle_out {σ : State Unit} (hO : SInvU.IO (fun _ => σ.idleSc) σ)
    {u : CslotPtr} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ u = some (.untypedCap dev b n fi)) : σ.idleSc ∉ SInvU.delR b n :=
  hO 0 u _ hc

/-- **The retype addresses lie in the untyped's region.** -/
theorem retPtrs_delR {σ : State Unit} (hW : SInvU.UtWf σ) {srcSlot : CslotPtr} {reset : Bool}
    {base rb : ObjRef} {ty : ApiObjectType} {sz : Nat} {slots : List CslotPtr} {dev : Bool}
    (hok : SInvU.UtRetOK σ (.retype srcSlot reset base rb ty sz slots dev)) {bits fi : Nat}
    (hc : SInvU.capAt σ srcSlot = some (.untypedCap dev base bits fi)) :
    ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), q ∈ SInvU.delR base bits := by
  obtain ⟨bits', fi', hc', hfit, h1, -, h3⟩ := SInvU.utRet_region hW hok
  rw [hc] at hc'
  simp only [Option.some.injEq, Cap.untypedCap.injEq] at hc'
  obtain ⟨-, -, rfl, rfl⟩ := hc'
  intro q hq
  obtain ⟨hn, hfit'⟩ := hW.fit hc
  have hr := SInvU.retPtrs_rng hq (by omega)
  rw [SInvU.mem_delR_iff hn hfit']
  simp only [SInvU.utR, Set.mem_setOf_eq]
  have : base.toNat ≤ rb.toNat := by split at h1 <;> omega
  omega

/-! ## The reset's bundle -/

abbrev UB (s : State Unit) : Prop := Rdy s ∧ SInvV.ValidMachineTime s

theorem ub_of {α : Type} {m : NonDet (State Unit) α} (hR : RdK m) (hG : SInvV.GK m) : IK UB m :=
  fun σ h y hy => ⟨hR σ h.1 y hy, hG _ SInvV.wl_vmt σ h.2 y hy⟩

theorem ub_preemptionPoint : IKE UB (preemptionPoint (Z := Unit)) := by
  intro σ h y hy
  exact ⟨B8f.rdy_preemptionPoint σ h.1 h.2 hy, SInvV.gk_preemptionPoint _ SInvV.wl_vmt σ h.2 y hy⟩

/-- RdC's `rd_auto` (a second, naive `rd_auto` from SpecInvSbR is also in scope). -/
macro "rdn_auto" : tactic => `(tactic| repeat' (first | rd_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem ub_setCap (c : Cap) (sl : CslotPtr) : IK UB (setCap (Z := Unit) c sl) :=
  ub_of (rd_setCap c sl) (SInvV.gk_of_mtk (MachT.mtk_setCap c sl))

theorem ub_dmo {α : Type} (mop : NonDet MachineState α) (hm : SInvV.MaskT mop) : IK UB (doMachineOp (Z := Unit) mop) :=
  ub_of (ik_doMachineOp (fun _ _ h => h) _) (SInvV.gk_doMachineOp hm)

theorem ub_archPost (dev : Bool) (sz : Nat) : IK UB (archPostResetUntyped (Z := Unit) dev sz) :=
  ub_of (rd_archPostResetUntyped dev sz) (by unfold archPostResetUntyped; gk_auto)

macro "ub_auto" : tactic => `(tactic| repeat' (first
  | exact ub_preemptionPoint | exact ub_setCap _ _ | exact ub_dmo _ (SInvV.mt_clearMemory _ _)
  | exact ub_archPost _ _
  | (with_reducible refine ike_mapMEx (fun _ => ?_) _)
  | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

/-! ## The steps -/

theorem rd_deleteObjects_p (ptr : Word) (bits : Nat) (σ : State Unit) (hR : Rdy σ)
    (hD : ∀ q x c y n, σ.kheap q = some (.tcb x) → x.tcbSchedContext = some c →
      σ.kheap c = some (.schedContext y n) → q ∉ SInvU.delR ptr bits ∧ c ∉ SInvU.delR ptr bits)
    (hI : σ.idleSc ∉ SInvU.delR ptr bits) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits σ).1, Rdy y.2 := by
  intro y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  rw [e]
  exact rdy_rf hR (rf_detype _ σ ms hD hI)

/-- `retype_region` at addresses holding no object, not the idle SC. -/
theorem rd_retypeRegionWith_p (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n o : Nat)
    (ty : ApiObjectType) (dev : Bool) (σ : State Unit) (hR : Rdy σ)
    (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), σ.kheap q = none)
    (hI : σ.idleSc ∉ SInvU.retPtrs ptr n (bA ty o)) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1, Rdy y.2 := by
  intro y hy
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show Rdy z3.2
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
    exact rdy_rf hR (rf_retype σ _ _ (freshR_default hty _ _ _) hF hI)
  · rw [Set.mem_singleton_iff.1 h3]; exact hR

set_option maxHeartbeats 4000000 in
/-- `reset_untyped_cap` of a childless held untyped (`ValidMachineTime` for the chunk loop's preemption points). -/
theorem rd_resetUntypedCap (s : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev b n fi))
    (hD : ∀ q x c y m, σ.kheap q = some (.tcb x) → x.tcbSchedContext = some c →
      σ.kheap c = some (.schedContext y m) → q ∉ SInvU.delR b n ∧ c ∉ SInvU.delR b n)
    (hI : σ.idleSc ∉ SInvU.delR b n) (hR : Rdy σ) (hv : SInvV.ValidMachineTime σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, Rdy y.2 := by
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
    exact hR
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hz0 : Rdy z.2 := rd_deleteObjects_p b n σ hR hD hI z hz
    have hv0 : SInvV.ValidMachineTime z.2 := SInvV.gk_deleteObjects b n _ SInvV.wl_vmt σ hv z hz
    refine ((?_ : IKE UB _) z.2 ⟨hz0, hv0⟩ y hy).1
    try dsimp only
    ub_auto

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset, from a state where the retype addresses hold no object
and are not the idle SC. -/
theorem rd_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    (slots : List CslotPtr) (dev : Bool) (σ : State Unit) (hR : Rdy σ)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none)
    (hI : σ.idleSc ∉ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz)) :
    ∀ x ∈ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs) : NonDet (State Unit) _) σ |>.1, Rdy x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : Rdy x4.2 := rd_setCap _ _ σ hR x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  have hi4 : x4.2.idleSc = σ.idleSc := SInvL.isk_setCap (N := σ.idleSc) _ _ σ rfl x4 hx4
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := rd_retypeRegionWith_p fl4ObjBitsApi rb slots.length sz ty dev x4.2 hb4
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) (by rw [hi4]; exact hI) x5 hx5
  refine (?_ : RdK _) x5.2 hb5 _ hx
  rdn_auto

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps `Rdy`** (module docstring). -/
theorem rd_fl4InvokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hR : Rdy σ)
    (hv : SInvV.ValidMachineTime σ) (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hok : SInvU.UtRetOK σ ui) :
    ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, Rdy y.2 := by
  intro y hy
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok
  have hIn : σ.idleSc ∉ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz) :=
    fun hm => idle_out hO hc (retPtrs_delR hU.1.1.2.1 hok hc _ hm)
  cases reset
  · have hfr := SInvU.utRet_fresh hU.1.1 hok
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    exact rd_utBody s base rb ty sz slots dev σ hR hfr hIn x hx
  · simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := rd_resetUntypedCap s hc (bnd_pair hU hL hIt hO hB hc (hr rfl)) (idle_out hO hc) hR hv z hz
    have hfz := SInvU.utRet_fresh_after_reset hU.1.1 hok z hz
    have hiz : z.2.idleSc = σ.idleSc := SInvL.isk_resetUntypedCap (N := σ.idleSc) s σ rfl z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hbz)
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      exact rd_utBody s base rb ty sz slots dev s1 hbz hfz (by rw [hiz]; exact hIn) x hx

/-! ## MakePool -/

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `Rdy`** (the parent slot holds a childless page-sized untyped at the frame). -/
theorem rd_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hR : Rdy σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hok : SInvU.MpOKN (SInvU.uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, Rdy y.2 := by
  intro y hy
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hf : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc'
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  have hIf : σ.idleSc ≠ frame := fun e => idle_out hO hc' (e ▸ hf)
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := rd_deleteObjects_p frame page_bits σ hR (bnd_pair hU hL hIt hO hB hc' hk) (idle_out hO hc') y1 h1
  have hi1 : y1.2.idleSc = σ.idleSc := SInvL.isk_deleteObjects (N := σ.idleSc) _ _ σ rfl y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hf]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : Rdy y3.2 := rd_setCap _ _ y1.2 hb1 y3 h3
  have hi3 : y3.2.idleSc = σ.idleSc := (SInvL.isk_setCap (N := y1.2.idleSc) _ _ y1.2 rfl y3 h3).trans hi1
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hmem : ∀ q ∈ SInvU.retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0), q = frame := by
    intro q hq
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    rw [hq]; simp [ptrAdd]
  have hb4 := rd_retypeRegionWith_p objBitsApi frame 1 0 _ false y3.2 hb3
    (fun q hq => by rw [hmem q hq]; exact hn3) (fun hq => hIf (hi3 ▸ hmem _ hq)) y4 h4
  refine (?_ : RdK _) y4.2 hb4 y hy
  rdn_auto

/-- **rd8h's `ArchOK` for ASIDControl** from carried facts and the decode's `MpOKN`. -/
theorem archOK_asid (o : AsidControlInvocation) (σ : State Unit) (hR : Rdy σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hok : SInvU.MpOKN (SInvU.uV σ) o) :
    B8h.ArchOK σ (.spec (.invokeASIDControl o)) := by
  intro y hy
  cases o with
  | makePool frame slot parent base =>
    simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
    obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hy
    obtain ⟨z, hz, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
    exact rd_makePool frame slot parent base σ hR hU hL hIt hB hO hok z hz

end

end Fl4Proofs.P3.SInvR.B8n
