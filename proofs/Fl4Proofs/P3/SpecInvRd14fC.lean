/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3): **the
deletion walk invariant `DW σ0`** and its step kit (spec side only).

* `Mx0 c s` (the SC at `c` has refill max 0) and **`DW σ0 q`**: cur_sc, ct,
  the idle thread and the idle SC are σ0's, cur_sc is not the idle SC, rd14b's
  `EB ct cur_sc` (ct bound to cur_sc, an SC; or unbound with no resume), and
  either cur_sc's refills / max are σ0's (rd8a's `CW`) with `OffReady`, or
  its max is 0 with ct unbound and no resume (rd14e's `EBN`: the finalised
  cur_sc). `DWS := DW ∧ Suff` (the facts at a non-preempted state). Unlike
  rd14d's `TT` / `TW`, `DW` carries `OffReady` itself, so the time stamps of
  the preemption points need no arithmetic (SInvO's `offReady_updateTimeStamp`).
* Steps: `offReady_cw`, `suff_cw` (a `CW ∧ cfS` step), **`dw_step`** (a step
  with rd14d's `EC` facts and `EBN` kept), **`dws_of`** (from rd14d's `EC`
  family and `EBN`), `nres_of_cp` (rd8a's `CP` keeps "no resume"),
  `ebn_of` (`CP` and a `QN` walk), **`dws_gen`** (`CFK`, `CP`, rd14b's `BL`
  and a `QN` walk), `dws_svcf`.
* **`dw_preemptionPoint`**: `preemption_point` from `DW ∧ Suff ∧
  ValidMachineTime`: every outcome `DW`, every `ok` outcome `Suff` (the
  point's own sufficiency check, or no time stamp). `PF` (the point's frame:
  heap, action, cur_sc / ct / idle kept, `OffReady` and `ValidMachineTime`
  carried across the time stamp), `pf_preemptionPoint`,
  `suff_preemptionPoint`.
-/
import Fl4Proofs.P3.SpecInvRd14fB
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- The SC at `c` has refill max 0. -/
abbrev Mx0 (c : ObjRef) (s : State Unit) : Prop :=
  ∀ y n, s.kheap c = some (.schedContext y n) → y.scRefillMax = 0

/-- **The deletion walk invariant** (module docstring). -/
structure DW (σ0 q : State Unit) : Prop where
  cs : q.curSc = σ0.curSc
  ct : q.curThread = σ0.curThread
  it : q.idleThread = σ0.idleThread
  is : q.idleSc = σ0.idleSc
  nis : σ0.curSc ≠ σ0.idleSc
  eb : A14b.EB σ0.curThread σ0.curSc q
  rf : (A8.CW σ0.curSc σ0 q ∧ Sched.OffReady q) ∨ (Mx0 σ0.curSc q ∧ A14e.EBN σ0.curThread q)

/-- `DW` at a non-preempted state. -/
abbrev DWS (σ0 q : State Unit) : Prop := DW σ0 q ∧ Suff q

/-! ## Steps -/

theorem offReady_cw {s y : State Unit} (hO : Sched.OffReady s) (hw : A8.CW s.curSc s y) (hc : cfS y = cfS s) :
    Sched.OffReady y := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, -, -, -, e6⟩ := hc'
  intro z n hz
  rw [e2] at hz
  obtain ⟨z0, n0, hz0, er, -⟩ := hw.1 z n hz
  have hh : refillHd z = refillHd z0 := by simp only [refillHd, er]
  rw [e1, e6, hh]; exact hO z0 n0 hz0

theorem suff_cw {s y : State Unit} (hS : Suff s) (hw : A8.CW s.curSc s y) (hc : cfS y = cfS s) : Suff y := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, -, -, e5, -⟩ := hc'
  intro z n hz ha hne
  rw [e2] at hz hne; rw [e5] at hne; rw [e1]
  obtain ⟨z0, n0, hz0, er, em⟩ := hw.1 z n hz
  have ha0 : scActive z0 = true := by simp only [scActive, ← em]; exact ha
  have := hS z0 n0 hz0 ha0 hne
  have hh : refillHd z = refillHd z0 := by simp only [refillHd, er]
  rw [hh]; exact this

/-- **One step of the walk**: rd14d's `EC s` at the outcome and `EBN` kept. -/
theorem dw_step {σ0 s y : State Unit} (h : DW σ0 s) (hc : cfS y = cfS s) (hw : A8.CW s.curSc s y)
    (he : A14b.EB s.curThread s.curSc y) (hn : A14e.EBN s.curThread s → A14e.EBN s.curThread y) : DW σ0 y := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨-, e2, e3, e4, e5, -⟩ := hc'
  refine ⟨e2.trans h.cs, e3.trans h.ct, e4.trans h.it, e5.trans h.is, h.nis, ?_, ?_⟩
  · rw [← h.ct, ← h.cs]; exact he
  · have hw' : A8.CW σ0.curSc s y := by rw [← h.cs]; exact hw
    rcases h.rf with ⟨hw0, hO⟩ | ⟨hm, hb⟩
    · exact Or.inl ⟨hw0.trans hw', offReady_cw hO hw hc⟩
    · refine Or.inr ⟨fun z n hz => ?_, ?_⟩
      · obtain ⟨z0, n0, hz0, -, em⟩ := hw'.1 z n hz
        rw [em]; exact hm z0 n0 hz0
      · rw [← h.ct]; exact hn (by rw [h.ct]; exact hb)

theorem ec_self {σ0 s : State Unit} (h : DW σ0 s) : A14d.EC s s :=
  ⟨rfl, A8.CW.refl _ _, by rw [h.ct, h.cs]; exact h.eb⟩

/-- **`DWS` from rd14d's `EC` family and `EBN`.** -/
theorem dws_of {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α}
    (he : ∀ σ1, IK (A14d.EC σ1) m) (hn : ∀ t, IK (A14e.EBN t) m) : IK (DWS σ0) m := by
  intro s hs y hy
  obtain ⟨hc, hw, hb⟩ := he s s (ec_self hs.1) y hy
  exact ⟨dw_step hs.1 hc hw hb fun hn' => hn _ s hn' y hy, suff_cw hs.2 hw hc⟩

/-- The pointwise form (a step with state preconditions). -/
theorem dws_pt {σ0 s : State Unit} (hs : DWS σ0 s) {α : Type} {m : NonDet (State Unit) α}
    (he : ∀ y ∈ (m s).1, A14d.EC s y.2) (hn : A14e.EBN s.curThread s → ∀ y ∈ (m s).1, A14e.EBN s.curThread y.2) :
    ∀ y ∈ (m s).1, DWS σ0 y.2 := by
  intro y hy
  obtain ⟨hc, hw, hb⟩ := he y hy
  exact ⟨dw_step hs.1 hc hw hb fun hn' => hn hn' y hy, suff_cw hs.2 hw hc⟩

/-- rd8a's `CP` keeps "no resume". -/
theorem nres_of_cp {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ1 c, IK (A8.CP σ1 c) m) : IK NRes m :=
  fun s hs y hy e => hs ((h s s.curSc s ⟨rfl, A8.CW.refl _ _⟩ y hy).2.2 e)

theorem ebn_of {α : Type} {m : NonDet (State Unit) α} (hp : ∀ σ1 c, IK (A8.CP σ1 c) m) {t : ObjRef}
    (hq : IK (TP (QN t)) m) : IK (A14e.EBN t) m :=
  fun s hs y hy => ⟨hq s hs.1 y hy, nres_of_cp hp s hs.2 y hy⟩

theorem qn_of_svm {α : Type} {m : NonDet (State Unit) α} (h : SVK.SVM m) (t : ObjRef) : IK (TP (QN t)) m :=
  fun s hs y hy => tp_svs (qn_stab t) (h s y hy) hs

/-- **`DWS` from `CFK`, `CP`, rd14b's `BL` and a `QN` walk.** -/
theorem dws_gen {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (hf : CFK m)
    (hp : ∀ σ1 c, IK (A8.CP σ1 c) m) (hb : ∀ t c, IK (BL t c) m) (hq : ∀ t, IK (TP (QN t)) m) :
    IK (DWS σ0) m :=
  dws_of (fun σ1 => A14d.ec_ik hf (hp σ1 σ1.curSc) fun s _ h =>
      ik_eb (hb _ _) (hq _) (nres_of_cp hp) s h)
    fun _ => ebn_of hp (hq _)

theorem dws_svcf {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) :
    IK (DWS σ0) m :=
  dws_of (fun _ => A14d.ec_svcf h1 h2) fun _ => A14e.ebn_svm h1

/-! ## `preemption_point` -/

/-- The frame of `preemption_point` from `s`. -/
abbrev PF (s t : State Unit) : Prop :=
  t.kheap = s.kheap ∧ t.schedulerAction = s.schedulerAction ∧ t.curSc = s.curSc ∧ t.curThread = s.curThread ∧
    t.idleThread = s.idleThread ∧ t.idleSc = s.idleSc ∧ (Sched.OffReady s → Sched.OffReady t) ∧
    SInvV.ValidMachineTime t

theorem pf_uts (s : State Unit) : IK (PF s) (updateTimeStamp (Z := Unit)) := by
  intro t h y hy
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨-, ea, -, ei⟩ := qa_updateTimeStamp t.readyQueues t.schedulerAction t.releaseQueue t.idleSc t
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp t.curThread t.idleThread t ⟨rfl, rfl⟩ y hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hv⟩ := h
  exact ⟨ek.trans h1, ea.trans h2, ec.trans h3, et.trans h4, eit.trans h5, ei.trans h6,
    fun hO => SInvO.offReady_updateTimeStamp hv (h7 hO) hy, SInvV.gk_updateTimeStamp _ SInvV.wl_vmt t hv y hy⟩

theorem pf_dmo (s : State Unit) {α : Type} (mop : NonDet MachineState α) (hm : SInvV.MaskT mop) :
    IK (PF s) (doMachineOp (Z := Unit) mop) := by
  intro t h y hy
  have h1 := ik_doMachineOp (P := fun t : State Unit => t.kheap = s.kheap ∧ t.schedulerAction = s.schedulerAction ∧
      t.curSc = s.curSc ∧ t.curThread = s.curThread ∧ t.idleThread = s.idleThread ∧ t.idleSc = s.idleSc ∧
      (Sched.OffReady s → Sched.OffReady t)) (fun _ _ h => h) mop t
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩ y hy
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2,
    SInvV.wl_vmt.msk mop hm t h.2.2.2.2.2.2.2 y hy⟩

theorem pf_preemptionPoint (s : State Unit) : IKE (PF s) (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE
  repeat' (first | exact pf_uts s | exact ik_doExtendedOp (fun _ _ h => h) _ |
    exact pf_dmo s _ (SInvV.mt_getActiveIRQ _) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDet.when))

/-- A lifted step followed by the rest. -/
theorem mem_liftE_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) Unit β}
    {s : State Unit} {y : Except Unit β × State Unit} (hy : y ∈ ((NonDetE.liftE m >>= f).run s).1) :
    ∃ x ∈ (m s).1, y ∈ ((f x.1).run x.2).1 := by
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy
  · obtain ⟨x, hx, rfl⟩ := ft_mem_liftE hz
    have e : x.1 = a := by simpa using ha
    subst e
    exact ⟨x, hx, hy⟩
  · obtain ⟨x, -, rfl⟩ := ft_mem_liftE hz
    simp at he

theorem readSuff_some {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {u : Ticks} {b : Bool}
    (h : readScRefillSufficient (Z := Unit) p u σ = some b) : b = refillSufficient u (refillHd y) := by
  have hm : (b, σ) ∈ (getScRefillSufficient (Z := Unit) p u σ).1 := by
    show (b, σ) ∈ (NonDet.getsThe _ σ).1
    unfold NonDet.getsThe
    rw [h]
    exact rfl
  exact congrArg Prod.fst (mem_getScRefillSufficient hk u hm)

/-- **Every `ok` outcome of `preemption_point` has `Suff`.** -/
theorem suff_preemptionPoint {s : State Unit} (hS : Suff s) {y : Except Unit Unit × State Unit}
    (hy : y ∈ ((preemptionPoint (Z := Unit)).run s).1) : ∀ a, y.1 = .ok a → Suff y.2 := by
  intro a ha
  unfold preemptionPoint orChoiceE at hy
  obtain ⟨x1, hx1, hy⟩ := mem_liftE_bind hy
  have hS1 : Suff x1.2 := ik_doExtendedOp (P := Suff) (fun _ _ h => h) _ s hS x1 hx1
  obtain ⟨x2, hx2, hy⟩ := mem_liftE_bind hy
  obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨⟨⟨rv, junk⟩, s3⟩, hx3, hy⟩ := mem_liftE_bind hy
  obtain ⟨-, e3⟩ := hx3
  simp only at e3
  subst e3
  dsimp only at hy
  split at hy
  · obtain ⟨x4, -, hy⟩ := mem_liftE_bind hy
    obtain ⟨x5, -, hy⟩ := mem_liftE_bind hy
    obtain ⟨x6, -, hy⟩ := mem_liftE_bind hy
    obtain ⟨x7, hx7, hy⟩ := mem_liftE_bind hy
    obtain rfl := Set.mem_singleton_iff.1 hx7
    obtain ⟨x8, hx8, hy⟩ := mem_liftE_bind hy
    obtain rfl := Set.mem_singleton_iff.1 hx8
    obtain ⟨x9, hx9, hy⟩ := mem_liftE_bind hy
    obtain rfl := Set.mem_singleton_iff.1 hx9
    obtain ⟨x10, hx10, hy⟩ := mem_liftE_bind hy
    obtain ⟨z, n, hk, rfl⟩ := SInvE.mem_getScActive hx10
    obtain ⟨x11, hx11, hy⟩ := mem_liftE_bind hy
    obtain rfl := Set.mem_singleton_iff.1 hx11
    dsimp only at hy
    unfold NonDetE.whenE at hy
    split at hy
    · unfold NonDetE.throwError at hy
      rw [ExceptT.run_throw] at hy
      rw [Set.mem_singleton_iff.1 hy] at ha
      cases ha
    · rename_i hc
      rw [SInvU.mem_ret_ok hy]
      (try dsimp only at hk); (try dsimp only at hc); (try dsimp only)
      simp only [not_or] at hc
      obtain ⟨-, -, hc⟩ := hc
      obtain ⟨-, hsf⟩ := not_not.mp hc
      intro z' n' hz' _ _
      rw [hk] at hz'
      cases hz'
      have e := readSuff_some hk hsf
      rw [← e]
  · rw [SInvU.mem_ret_ok hy]
    exact hS1

/-- **`preemption_point` from `DWS ∧ ValidMachineTime`**: every outcome `DW`, every `ok` outcome `Suff`. -/
theorem dw_preemptionPoint {σ0 s : State Unit} (h : DWS σ0 s) (hv : SInvV.ValidMachineTime s)
    {y : Except Unit Unit × State Unit} (hy : y ∈ ((preemptionPoint (Z := Unit)).run s).1) :
    DW σ0 y.2 ∧ SInvV.ValidMachineTime y.2 ∧ (∀ a, y.1 = .ok a → Suff y.2) := by
  obtain ⟨hk, ha, hc, ht, hit, his, hO, hv'⟩ :=
    pf_preemptionPoint s s ⟨rfl, rfl, rfl, rfl, rfl, rfl, id, hv⟩ y hy
  have hd := h.1
  refine ⟨⟨hc.trans hd.cs, ht.trans hd.ct, hit.trans hd.it, his.trans hd.is, hd.nis, ?_, ?_⟩, hv',
    suff_preemptionPoint h.2 hy⟩
  · have e := hd.eb
    unfold A14b.EB TP KS NRes at e ⊢
    rw [hk, ha]; exact e
  · rcases hd.rf with ⟨hw, hO0⟩ | ⟨hm, hb⟩
    · refine Or.inl ⟨⟨fun z n hz => ?_, fun e => hw.2 (by rw [← ha]; exact e)⟩, hO hO0⟩
      rw [hk] at hz; exact hw.1 z n hz
    · refine Or.inr ⟨fun z n hz => hm z n (by rw [← hk]; exact hz), ?_⟩
      unfold A14e.EBN TP NRes at hb ⊢
      rw [hk, ha]; exact hb

end

end Fl4Proofs.P3.SInvR.A14f
