/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (a), (b)): **`PerfA`
for Untyped retype / reset and ASID control (MakePool)** (spec side only).

* **`DU σ0 q`**: the ct-bound case of rd14f C's `DW` with ct's TCB and cur_sc's
  SC present (ct bound to cur_sc throughout: the arms never unbind it). `DU.dw`.
  Every step keeps it from the scheduler view at ct and cur_sc, `cfS` and the
  action (`du_sv`); `Suff` likewise (rd14f C's `suff_cw`).
* The leaves: `ds_svcf` (an `SVS ∧ cfS` step), `ds_deleteObjects` (detype of a
  region holding neither ct nor cur_sc: rd8n's `bnd_pair`), `ds_retype`
  (`retype_region` at addresses holding no object), `ds_preemptionPoint`
  (rd14f C's `pf_preemptionPoint` / `suff_preemptionPoint`).
* The triple `HU σ0 m` (from `DU ∧ ValidMachineTime ∧ Suff`, every outcome `DU ∧
  ValidMachineTime`, every `ok` outcome `Suff`) and its combinators; **`hu_resetUntypedCap`**
  (the chunk loop's `mapMEx` with its preemption points), `ds_utBody`,
  **`du_fl4InvokeUntyped`**, **`ds_makePool`**.
* **`perfA_untyped`**: from rd14c's `RF` and rd8f's `RB` at the Restart state,
  rd8n's `UF`, IfLiveT with ct holding a thread cap (`SInv.IL [ct]`) and the
  decode's `UtRetOK`: `ok` outcomes end in `SS4` after the post (rd14f F's
  `ss4_dws`), `error` outcomes (the reset's preemption points) through rd14f
  B's `ss4_preemptionPath`, whose inputs are the existing whole-perform lemmas
  (rd8n's `rd_fl4InvokeUntyped`, nq3's `nq_invokeUntyped` with `NqDet` from
  IfLiveT, sb2's `sc_invokeUntyped`, ctq16's `ckx_fl4InvokeUntyped`, ctq's
  `eb_fl4InvokeUntyped`, rd8r's `hqx_fl4InvokeUntyped`).
  **`perfA_asidControl`** (MakePool never errors; `MpOKN`).
-/
import Fl4Proofs.P3.SpecInvRd14fH
import Fl4Proofs.P3.SpecInvRd8nB
import Fl4Proofs.P3.SpecInvCqM2
import Fl4Proofs.P3.SpecInvSbX4
import Fl4Proofs.P3.SpecInvCqHP
import Fl4Proofs.P3.SpecInvNtfnQLT
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The ct-bound walk invariant -/

/-- **ct bound to cur_sc** (rd14f C's `DW`, first case, with ct's TCB and cur_sc's SC present). -/
structure DU (σ0 q : State Unit) : Prop where
  cs : q.curSc = σ0.curSc
  ct : q.curThread = σ0.curThread
  it : q.idleThread = σ0.idleThread
  is : q.idleSc = σ0.idleSc
  nis : σ0.curSc ≠ σ0.idleSc
  bd : ∃ x, q.kheap σ0.curThread = some (.tcb x) ∧ x.tcbSchedContext = some σ0.curSc
  sc : ∃ y n, q.kheap σ0.curSc = some (.schedContext y n)
  cw : A8.CW σ0.curSc σ0 q
  off : Sched.OffReady q

theorem DU.dw {σ0 q : State Unit} (h : DU σ0 q) : DW σ0 q := by
  obtain ⟨x, hx, hb⟩ := h.bd
  refine ⟨h.cs, h.ct, h.it, h.is, h.nis, Or.inl ⟨fun p x' hx' he => ?_, h.sc⟩, Or.inl ⟨h.cw, h.off⟩⟩
  subst he
  rw [hx] at hx'
  cases hx'
  exact hb

abbrev DS (σ0 q : State Unit) : Prop := DU σ0 q ∧ Suff q

/-- **`DU` and `Suff` from the view at ct and cur_sc, `cfS` and the action.** -/
theorem ds_sv {σ0 s y : State Unit} (h : DU σ0 s)
    (h1 : SVK.sv (y.kheap σ0.curThread) = SVK.sv (s.kheap σ0.curThread))
    (h2 : SVK.sv (y.kheap σ0.curSc) = SVK.sv (s.kheap σ0.curSc)) (hc : cfS y = cfS s)
    (ha : y.schedulerAction = s.schedulerAction ∨ y.schedulerAction = .chooseNewThread) :
    DU σ0 y ∧ (Suff s → Suff y) := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨-, e2, e3, e4, e5, -⟩ := hc'
  obtain ⟨x, hx, hb⟩ := h.bd
  obtain ⟨y0, n0, hy0⟩ := h.sc
  rw [hx] at h1
  obtain ⟨x', hx', hb'⟩ := SVK.sv_tcb (a := x.tcbSchedContext) h1
  rw [hy0] at h2
  obtain ⟨y', hy', er, em, -⟩ := SVK.sv_sc (rf := y0.scRefills) (m := y0.scRefillMax) (t := y0.scTcb) h2
  have hw : A8.CW s.curSc s y := by
    rw [h.cs]
    refine ⟨fun z n hz => ?_, fun e => ?_⟩
    · rw [hy'] at hz
      cases hz
      exact ⟨y0, n0, hy0, er, em⟩
    · rcases ha with e' | e'
      · rw [← e']; exact e
      · rw [e'] at e; cases e
  have hw0 : A8.CW σ0.curSc s y := by rw [← h.cs]; exact hw
  refine ⟨⟨e2.trans h.cs, e3.trans h.ct, e4.trans h.it, e5.trans h.is, h.nis, ⟨x', hx', by rw [hb', hb]⟩,
    ⟨y', n0, hy'⟩, h.cw.trans hw0, offReady_cw h.off hw hc⟩, fun hS => suff_cw hS hw hc⟩

theorem ds_svs {σ0 s y : State Unit} (h : DS σ0 s) (hS : SVK.SVS s y) (hc : cfS y = cfS s) : DS σ0 y := by
  have r := ds_sv h.1 (hS.1 _) (hS.1 _) hc hS.2.2
  exact ⟨r.1, r.2 h.2⟩

theorem ds_svcf {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) :
    IK (DS σ0) m :=
  fun s hs y hy => ds_svs hs (h1 s y hy) (h2 s y hy)

/-- `DU` and `ValidMachineTime` (the walk's carried facts; `Suff` only at `ok` outcomes). -/
abbrev UD (σ0 q : State Unit) : Prop := DU σ0 q ∧ SInvV.ValidMachineTime q

abbrev UDS (σ0 q : State Unit) : Prop := UD σ0 q ∧ Suff q

theorem uds_svcf {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m)
    (h3 : SInvV.GK m) : IK (UDS σ0) m := by
  intro s hs y hy
  have r := ds_svcf (σ0 := σ0) h1 h2 s ⟨hs.1.1, hs.2⟩ y hy
  exact ⟨⟨r.1, h3 _ SInvV.wl_vmt s hs.1.2 y hy⟩, r.2⟩

theorem uds_setCap {σ0 : State Unit} (c : Cap) (sl : CslotPtr) : IK (UDS σ0) (setCap (Z := Unit) c sl) :=
  uds_svcf (SVK.sv_setCap c sl) (cfk_setCap c sl) (SInvV.gk_of_mtk (MachT.mtk_setCap c sl))

theorem uds_dmo {σ0 : State Unit} {α : Type} (mop : NonDet MachineState α) (hm : SInvV.MaskT mop) :
    IK (UDS σ0) (doMachineOp (Z := Unit) mop) := by
  intro s hs y hy
  have h1 := ik_doMachineOp (P := DS σ0) (fun _ _ h => ⟨⟨h.1.cs, h.1.ct, h.1.it, h.1.is, h.1.nis, h.1.bd, h.1.sc,
    ⟨h.1.cw.1, h.1.cw.2⟩, h.1.off⟩, h.2⟩) mop s ⟨hs.1.1, hs.2⟩ y hy
  exact ⟨⟨h1.1, SInvV.gk_doMachineOp hm _ SInvV.wl_vmt s hs.1.2 y hy⟩, h1.2⟩

/-! ## Detype and retype -/

theorem kh_detype {D : Set ObjRef} {s y : State Unit} {ms : MachineState}
    (e : y = detype D { s with machineState := ms }) {p : ObjRef} (hp : p ∉ D) : y.kheap p = s.kheap p := by
  rw [e]; show (if p ∈ D then none else s.kheap p) = _
  rw [if_neg hp]

/-- **`delete_objects` of a region holding neither ct nor cur_sc.** -/
theorem ds_deleteObjects (ptr : Word) (bits : Nat) {σ0 s : State Unit} (h : DS σ0 s)
    (hct : σ0.curThread ∉ SInvU.delR ptr bits) (hcs : σ0.curSc ∉ SInvU.delR ptr bits) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits s).1, DS σ0 y.2 := by
  intro y hy
  obtain ⟨ms, e⟩ := SInvU.deleteObjects_out hy
  have hc : cfS y.2 = cfS s := by rw [e]; rfl
  have ha : y.2.schedulerAction = s.schedulerAction := by rw [e]; rfl
  have r := ds_sv h.1 (by rw [kh_detype e hct]) (by rw [kh_detype e hcs]) hc (Or.inl ha)
  exact ⟨r.1, r.2 h.2⟩

theorem uds_deleteObjects (ptr : Word) (bits : Nat) {σ0 s : State Unit} (h : UDS σ0 s)
    (hct : σ0.curThread ∉ SInvU.delR ptr bits) (hcs : σ0.curSc ∉ SInvU.delR ptr bits) :
    ∀ y ∈ (deleteObjects (Z := Unit) ptr bits s).1, UDS σ0 y.2 := by
  intro y hy
  have r := ds_deleteObjects ptr bits ⟨h.1.1, h.2⟩ hct hcs y hy
  exact ⟨⟨r.1, SInvV.gk_deleteObjects ptr bits _ SInvV.wl_vmt s h.1.2 y hy⟩, r.2⟩

/-- `retype_region` writes fresh objects at its addresses, or nothing. -/
theorem retype_mem {bA : ApiObjectType → Nat → Nat} {ptr : ObjRef} {n o : Nat} {ty : ApiObjectType}
    {dev : Bool} {σ : State Unit} {y : List ObjRef × State Unit}
    (hy : y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev σ).1) :
    y.2 = σ ∨ ∃ ob : KernelObject,
      y.2 = { σ with kheap := (SInvU.retPtrs ptr n (bA ty o)).foldr (fun p kh => Function.update kh p (some ob)) σ.kheap } := by
  unfold retypeRegionWith at hy
  obtain ⟨z1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨z2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  show z3.2 = σ ∨ _
  unfold NonDet.when at h3
  split at h3
  · obtain ⟨w1, hw1, h3⟩ := h3
    rw [mem_gets hw1] at h3
    obtain ⟨w2, hw2, h3⟩ := h3
    rw [mem_gets hw2] at h3
    obtain ⟨w3, hw3, h3⟩ := h3
    rw [Set.mem_singleton_iff.1 hw3] at h3
    rw [Set.mem_singleton_iff.1 h3]
    exact Or.inr ⟨_, rfl⟩
  · rw [Set.mem_singleton_iff.1 h3]; exact Or.inl rfl

/-- **`retype_region` at addresses holding no object.** -/
theorem ds_retype {bA : ApiObjectType → Nat → Nat} {ptr : ObjRef} {n o : Nat} {ty : ApiObjectType}
    {dev : Bool} {σ0 s : State Unit} (h : DS σ0 s) (hF : ∀ q ∈ SInvU.retPtrs ptr n (bA ty o), s.kheap q = none) :
    ∀ y ∈ (retypeRegionWith (Z := Unit) bA ptr n o ty dev s).1, DS σ0 y.2 := by
  intro y hy
  rcases retype_mem hy with e | ⟨ob, e⟩
  · rw [e]; exact h
  · obtain ⟨x, hx, -⟩ := h.1.bd
    obtain ⟨y0, n0, hy0⟩ := h.1.sc
    have k : ∀ p o', s.kheap p = some o' → y.2.kheap p = s.kheap p := by
      intro p o' hp
      rw [e]
      show (List.foldr (fun p kh => Function.update kh p (some ob)) s.kheap (SInvU.retPtrs ptr n (bA ty o))) p = _
      rw [SInvU.foldr_upd, if_neg (fun hm => by rw [hF p hm] at hp; cases hp)]
    have r := ds_sv h.1 (by rw [k _ _ hx]) (by rw [k _ _ hy0]) (by rw [e]; rfl) (Or.inl (by rw [e]))
    exact ⟨r.1, r.2 h.2⟩

/-! ## The triple -/

/-- **From `UD ∧ Suff`, every outcome `UD`, every `ok` outcome `Suff`.** -/
def HU (σ0 : State Unit) {α : Type} (m : NonDetE (State Unit) Unit α) : Prop :=
  ∀ s, UDS σ0 s → ∀ y ∈ (m.run s).1, UD σ0 y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2)

variable {σ0 : State Unit}

theorem hu_bind {α β : Type} {m : NonDetE (State Unit) Unit α} {g : α → NonDetE (State Unit) Unit β}
    (hm : HU σ0 m) (hg : ∀ a, HU σ0 (g a)) : HU σ0 (m >>= g) := by
  intro s hs y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, rfl⟩⟩ := ft_mem_bindE hy
  · obtain ⟨h1, h2⟩ := hm s hs z hz
    exact hg a z.2 ⟨h1, h2 a ha⟩ y hy
  · exact ⟨(hm s hs z hz).1, fun a h => by simp at h⟩

theorem hu_lift {α : Type} {m : NonDet (State Unit) α} (h : IK (UDS σ0) m) : HU σ0 (NonDetE.liftE m) := by
  intro s hs y hy
  obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
  exact ⟨(h s hs x hx).1, fun _ _ => (h s hs x hx).2⟩

theorem hu_ret {α : Type} (a : α) : HU σ0 (NonDetE.returnOk a : NonDetE (State Unit) Unit α) := by
  intro s hs y hy
  rw [SInvU.mem_ret_ok hy]
  exact ⟨hs.1, fun _ _ => hs.2⟩

theorem hu_pure {α : Type} (a : α) : HU σ0 (pure a : NonDetE (State Unit) Unit α) := hu_ret a

theorem hu_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) Unit α} (h1 : HU σ0 m1)
    (h2 : HU σ0 m2) : HU σ0 (if P then m1 else m2) := by
  split <;> assumption

theorem hu_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) Unit γ} (h : ∀ a, HU σ0 (F a)) :
    ∀ xs : List α, HU σ0 (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact hu_pure ()
  | a :: l => by unfold NonDetE.mapMEx; exact hu_bind (h a) fun _ => hu_mapMEx h l

/-- **`preemption_point`.** -/
theorem hu_preemptionPoint : HU σ0 (preemptionPoint (Z := Unit)) := by
  intro s hs y hy
  obtain ⟨hk, ha, hc, ht, hit, his, hO, hv'⟩ :=
    pf_preemptionPoint s s ⟨rfl, rfl, rfl, rfl, rfl, rfl, id, hs.1.2⟩ y hy
  have hd := hs.1.1
  obtain ⟨x, hx, hb⟩ := hd.bd
  obtain ⟨y0, n0, hy0⟩ := hd.sc
  refine ⟨⟨⟨hc.trans hd.cs, ht.trans hd.ct, hit.trans hd.it, his.trans hd.is, hd.nis,
    ⟨x, by rw [hk]; exact hx, hb⟩, ⟨y0, n0, by rw [hk]; exact hy0⟩, ?_, hO hd.off⟩, hv'⟩,
    suff_preemptionPoint hs.2 hy⟩
  exact ⟨fun z n hz => hd.cw.1 z n (by rw [← hk]; exact hz), fun e => hd.cw.2 (by rw [← ha]; exact e)⟩

/-! ## The reset -/

theorem uds_archPost (dev : Bool) (sz : Nat) : IK (UDS σ0) (archPostResetUntyped (Z := Unit) dev sz) := by
  unfold archPostResetUntyped; exact ik_pure _

set_option maxHeartbeats 4000000 in
/-- **`reset_untyped_cap`** of a held untyped whose region holds neither ct nor cur_sc. -/
theorem hu_resetUntypedCap (sl : CslotPtr) {σ : State Unit} {dev : Bool} {b : ObjRef} {n fi : Nat}
    (hc : SInvU.capAt σ sl = some (.untypedCap dev b n fi))
    (hct : σ0.curThread ∉ SInvU.delR b n) (hcs : σ0.curSc ∉ SInvU.delR b n) (hU : UDS σ0 σ) :
    ∀ y ∈ (ExceptT.run (resetUntypedCap (Z := Unit) sl) σ).1, UD σ0 y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2) := by
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
    exact ⟨hU.1, fun _ _ => hU.2⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev b n fi) = 0 from h0)] at hy
    obtain ⟨z, hz, hy⟩ := SInvU.run_liftE_bind_mem hy
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz
    have hz0 : UDS σ0 z.2 := uds_deleteObjects b n hU hct hcs z hz
    refine (?_ : HU σ0 _) z.2 hz0 y hy
    try dsimp only
    refine hu_bind (hu_ret _) fun dv => ?_
    split
    · refine hu_bind (hu_lift ?_) fun _ => hu_lift (uds_archPost _ _)
      repeat' (first | exact uds_setCap _ _ | exact uds_dmo _ (SInvV.mt_clearMemory _ _) | ik_step0 | (unfold NonDet.unless) | (unfold NonDet.when))
    · refine hu_bind (hu_mapMEx (fun i => ?_) _) fun _ => hu_lift (uds_archPost _ _)
      exact hu_bind (hu_lift (uds_dmo _ (SInvV.mt_clearMemory _ _))) fun _ =>
        hu_bind (hu_lift (uds_setCap _ _)) fun _ => hu_preemptionPoint

/-! ## The retype's body -/

theorem sv14g_copyGlobalMappings (p : ObjRef) : SVK.SVM (copyGlobalMappings (Z := Unit) p) := by
  unfold copyGlobalMappings
  repeat' (first | exact A13b.sv13_storePml4e _ _ | sv_leaf | sv_step0)

theorem sv14g_initArchObjects (ty : ApiObjectType) (dev : Bool) (ptr : ObjRef) (n sz : Nat) (refs : List ObjRef) :
    SVK.SVM (initArchObjects (Z := Unit) ty dev ptr n sz refs) := by
  unfold initArchObjects
  repeat' (first | exact sv14g_copyGlobalMappings _ | sv_leaf | sv_step0)

theorem sv14g_createCap (ty : ApiObjectType) (bits : Nat) (u : CslotPtr) (dev : Bool) (d : CslotPtr × ObjRef) :
    SVK.SVM (createCap (Z := Unit) ty bits u dev d) := by
  unfold createCap setCdt
  sv_auto

set_option maxHeartbeats 4000000 in
/-- The retype's body after the reset, from a state where the retype addresses hold no object. -/
theorem ds_utBody (s : CslotPtr) (base rb : ObjRef) (ty : ApiObjectType) (sz : Nat)
    (slots : List CslotPtr) (dev : Bool) (σ : State Unit) (hD : DS σ0 σ)
    (hfr : ∀ q ∈ SInvU.retPtrs rb slots.length (fl4ObjBitsApi ty sz), σ.kheap q = none) :
    ∀ x ∈ (do
      let cap ← getCap (Z := Unit) s
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz)
      let freeRef ← pure (rb + totalObjectSize)
      setCap (.untypedCap dev base (Fl4Spec.bitsOf cap) (unat (freeRef - base))) s
      let orefs ← retypeRegionWith fl4ObjBitsApi rb slots.length sz ty dev
      initArchObjects ty dev rb slots.length sz orefs
      NonDet.mapMx (createCap ty sz s dev) (slots.zip orefs) : NonDet (State Unit) _) σ |>.1, DS σ0 x.2 := by
  intro x hx
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1; subst s1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  have hb4 : DS σ0 x4.2 := ds_svcf (SVK.sv_setCap _ _) (cfk_setCap _ _) σ hD x4 hx4
  have hk4 := (SInvU.setCap_out hx4).1
  obtain ⟨x5, hx5, hx⟩ := hx
  have hb5 := ds_retype (ty := ty) (dev := dev) hb4
    (fun q hq => by have := hk4 q; rw [hfr q hq] at this; simpa using this) x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hb6 := ds_svcf (sv14g_initArchObjects _ _ _ _ _ _) (cfk_initArchObjects' _ _ _ _ _ _) x5.2 hb5 x6 hx6
  exact ds_svcf (SVK.sv_mapMx (fun d => sv14g_createCap _ _ _ _ d) _) (by cfk_auto) x6.2 hb6 x hx

set_option maxHeartbeats 4000000 in
/-- **`invoke_untyped` keeps the walk invariant** (ct, cur_sc outside the reset's region: rd8n's
`bnd_pair`; the retype writes only addresses holding no object: ut1's `utRet_fresh*`). -/
theorem du_fl4InvokeUntyped (ui : UntypedInvocation) (σ : State Unit) (hU0 : UDS σ0 σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hok : SInvU.UtRetOK σ ui) :
    ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, DU σ0 y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2) := by
  intro y hy
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  obtain ⟨bits, fi, hc, -, -, -, -, hr⟩ := id hok
  cases reset
  · have hfr := SInvU.utRet_fresh hU.1.1 hok
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
    replace hy := SInvU.run_returnOk_bind_mem hy
    obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
    have h := ds_utBody s base rb ty sz slots dev σ ⟨hU0.1.1, hU0.2⟩ hfr x hx
    exact ⟨h.1, fun _ _ => h.2⟩
  · obtain ⟨xt, hxt, hbt⟩ := hU0.1.1.bd
    obtain ⟨yc, nc, hyc⟩ := hU0.1.1.sc
    obtain ⟨hct, hcs⟩ := B8n.bnd_pair hU hL hIt hO hB hc (hr rfl) _ xt _ yc nc hxt hbt hyc
    simp only [fl4InvokeUntyped, invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hbz := hu_resetUntypedCap s hc hct hcs hU0 z hz
    have hfz := SInvU.utRet_fresh_after_reset hU.1.1 hok z hz
    obtain ⟨r, s1⟩ := z
    cases r with
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨hbz.1.1, fun a h => by cases h⟩
    | ok u =>
      try dsimp only at hy
      obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hy
      have h := ds_utBody s base rb ty sz slots dev s1 ⟨hbz.1.1, hbz.2 u rfl⟩ hfz x hx
      exact ⟨h.1, fun _ _ => h.2⟩

/-! ## MakePool -/

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps the walk invariant** (the parent slot holds a childless page-sized untyped
at the frame: ct and cur_sc lie outside it). -/
theorem ds_makePool (frame : ObjRef) (slot parent : CslotPtr) (base : Asid) (σ : State Unit) (hD : DS σ0 σ)
    (hU : SInvU.UtInv'' σ) (hL : SInvL.ScLiveT (σ.idleThread, σ.idleSc) σ) (hIt : SInvG.IdleOutV σ)
    (hB : SInvB.ScBackS σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hok : SInvU.MpOKN (SInvU.uV σ) (.makePool frame slot parent base)) :
    ∀ y ∈ (performAsidControlInvocation (Z := Unit) (.makePool frame slot parent base) σ).1, DS σ0 y.2 := by
  intro y hy
  obtain ⟨⟨dev, fi, hc, hk⟩, -, -⟩ := hok
  have hc' : SInvU.capAt σ parent = some (.untypedCap dev frame page_bits fi) := hc
  have hf : frame ∈ SInvU.delR frame page_bits := by
    obtain ⟨hn, hfit⟩ := SInvU.UtWf.fit (σ := σ) hU.1.1.2.1 hc'
    exact (SInvU.mem_delR_iff hn hfit _).2 ⟨le_refl _, by have := Nat.two_pow_pos page_bits; omega⟩
  obtain ⟨xt, hxt, hbt⟩ := hD.1.bd
  obtain ⟨yc, nc, hyc⟩ := hD.1.sc
  obtain ⟨hct, hcs⟩ := B8n.bnd_pair hU hL hIt hO hB hc' hk _ xt _ yc nc hxt hbt hyc
  unfold performAsidControlInvocation at hy
  obtain ⟨y1, h1, hy⟩ := hy
  have hb1 := ds_deleteObjects frame page_bits hD hct hcs y1 h1
  have hn1 : y1.2.kheap frame = none := by
    obtain ⟨s1, -, e1⟩ := SInvB.deleteObjects_out' h1
    rw [e1]; show (if frame ∈ SInvU.delR frame page_bits then none else s1.kheap frame) = none
    rw [if_pos hf]
  obtain ⟨y2, h2, hy⟩ := hy
  obtain ⟨e2, -⟩ := SInvU.getCap_capAt h2
  obtain ⟨c2, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  have hb3 : DS σ0 y3.2 := ds_svcf (SVK.sv_setCap _ _) (cfk_setCap _ _) y1.2 hb1 y3 h3
  have hn3 : y3.2.kheap frame = none := by
    have := (SInvU.setCap_out h3).1 frame; rw [hn1] at this; simpa using this
  obtain ⟨y4, h4, hy⟩ := hy
  rw [← retypeRegionWith_objBitsApi] at h4
  have hmem : ∀ q ∈ SInvU.retPtrs frame 1 (objBitsApi (.archObject .asidPoolObj) 0), q = frame := by
    intro q hq
    simp only [SInvU.retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton] at hq
    rw [hq]; simp [ptrAdd]
  have hb4 := ds_retype (ty := .archObject .asidPoolObj) (dev := false) hb3
    (fun q hq => by rw [hmem q hq]; exact hn3) y4 h4
  refine (?_ : IK (DS σ0) _) y4.2 hb4 y hy
  repeat' (first | exact ds_svcf (SVK.sv_capInsert _ _ _) (by cfk_auto) | ik_step0 | ik_unfold | exact ds_svcf (by sv_auto) (by cfk_auto))

end

end Fl4Proofs.P3.SInvR.A14g
