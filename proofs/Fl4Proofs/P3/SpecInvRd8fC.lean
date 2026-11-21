/-
P3 (DESIGN.md §9), invariant line G1 (rd8f): **the deletion cone keeps `Rdy`**,
part 3: `preemption_point`, `rec_del` (least fixed point), `cap_delete`,
`cap_revoke` (spec side only, outside the JAtZ cone).

* **The carried bundle `RB C I := Rdy ∧ DK C ∧ T1 ∧ ScInv ∧ ValidMachineTime ∧
  IO (fun _ => I) ∧ idleSc = I`**: ctq14's `DK C` (`EB true`, `ct = C`,
  `Simple`, `NQ [C]`), ctq's `T1`, sb2's `ScInv`, invB's `ValidMachineTime`,
  ut7 / vi3's `IrqOutV` at the idle SC (`IdleScOutV`: no held cap covers the
  idle SC), the idle SC pointer (sl's `IdleScIs`). Each is a plain state
  invariant of every cone leaf (their own families: `dz_`, `q1_`, `sb_`/`si_`,
  `gk_`, `io_`, `isk_`); `Rdy` by parts 1-2 from `FH`.
* `preemption_point`: heap, queues, action, release queue and idle SC fixed,
  the time monotone (`ValidMachineTime` at the time stamp), so `rdy_later`.
* `rec_del`'s step follows ut7's `no_recDelF` (sg1): the finalised cap is read
  from its slot, so `IdleScOutV` says an SC cap's SC is not the idle SC
  (`rdf_finaliseCap`'s premise); the remainder written back is covered by the
  finalised cap (`finaliseCap_cov`), a reduced zombie by the zombie it replaces.
* **`rdCapDeleteH`**: every outcome of `cap_delete` (errors from a preemption
  point included) keeps `RB`; **`rb_capRevoke`** the same for `cap_revoke`.
-/
import Fl4Proofs.P3.SpecInvRd8fB
import Fl4Proofs.P3.SpecInvValidMachineTimeGen
import Fl4Proofs.P3.SpecInvUtO1
import Fl4Proofs.P3.SpecInvUtF4
import Fl4Proofs.P3.SpecInvUtR
import Fl4Proofs.P3.SpecInvUtN5
open Classical

namespace Fl4Proofs.P3.SInvR.B8f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `preemption_point` -/

/-- The frame of `preemption_point` from `σ0`, the time monotone. -/
abbrev PT (σ0 s : State Unit) : Prop :=
  (s.kheap = σ0.kheap ∧ s.readyQueues = σ0.readyQueues ∧ s.schedulerAction = σ0.schedulerAction ∧
    s.releaseQueue = σ0.releaseQueue ∧ s.idleSc = σ0.idleSc) ∧
  σ0.curTime.toNat ≤ s.curTime.toNat ∧ SInvV.ValidMachineTime s

theorem pt_uts (σ0 : State Unit) : IK (PT σ0) (updateTimeStamp (Z := Unit)) := by
  intro s h y hy
  obtain ⟨ek, -, et, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, ea, er, ei⟩ := qa_updateTimeStamp s.readyQueues s.schedulerAction s.releaseQueue s.idleSc s
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ht, hv⟩ := h
  refine ⟨⟨ek.trans h1, eq.trans h2, ea.trans h3, er.trans h4, ei.trans h5⟩, ?_,
    SInvV.gk_updateTimeStamp _ SInvV.wl_vmt s hv y hy⟩
  have a1 : s.curTime.toNat ≤ s.machineState.lastMachineTime.toNat := BitVec.le_def.mp hv.1
  have a2 : s.machineState.lastMachineTime.toNat ≤ SInvV.gctN s.machineState := by
    unfold SInvV.gctN; exact le_min hv.2 (Nat.le_add_right _ _)
  rw [et, SInvV.gctN_toNat]
  omega

theorem pt_dmo (σ0 : State Unit) {α : Type} (mop : NonDet MachineState α) (hm : SInvV.MaskT mop) :
    IK (PT σ0) (doMachineOp (Z := Unit) mop) := by
  intro s h y hy
  have h1 := ik_doMachineOp (P := fun s => (s.kheap = σ0.kheap ∧ s.readyQueues = σ0.readyQueues ∧
      s.schedulerAction = σ0.schedulerAction ∧ s.releaseQueue = σ0.releaseQueue ∧ s.idleSc = σ0.idleSc) ∧
      σ0.curTime.toNat ≤ s.curTime.toNat) (fun _ _ h => h) mop s ⟨h.1, h.2.1⟩ y hy
  exact ⟨h1.1, h1.2, SInvV.wl_vmt.msk mop hm s h.2.2 y hy⟩

theorem pt_preemptionPoint (σ0 : State Unit) : IKE (PT σ0) (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE
  repeat' (first | exact pt_uts σ0 | exact ik_doExtendedOp (fun _ _ h => h) _ | exact pt_dmo σ0 _ (SInvV.mt_getActiveIRQ _) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDet.when))

/-- **`preemption_point` keeps `Rdy`** (the clock is monotone by `ValidMachineTime`). -/
theorem rdy_preemptionPoint (σ : State Unit) (hR : Rdy σ) (hv : SInvV.ValidMachineTime σ)
    {y : Except Unit Unit × State Unit} (hy : y ∈ ((preemptionPoint (Z := Unit)).run σ).1) : Rdy y.2 := by
  have h := pt_preemptionPoint σ σ ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, le_refl _, hv⟩ y hy
  exact rdy_later hR h.1.1 h.1.2.1 h.1.2.2.1 h.2.1 h.1.2.2.2.1 h.1.2.2.2.2

/-! ## The bundle -/

/-- **The deletion cone's carried bundle** (module docstring). -/
def RB (C I : ObjRef) (s : State Unit) : Prop :=
  Rdy s ∧ P12.DK C s ∧ T1 s ∧ SInvB.ScInv s ∧ SInvV.ValidMachineTime s ∧ SInvU.IO (fun _ => I) s ∧
    s.idleSc = I

variable {C I : ObjRef}

theorem fh_of {s : State Unit} (h : RB C I s) : FH s :=
  ⟨h.1, ⟨h.2.1.2.2.2.1, fun _ h => by simp at h⟩, h.2.2.1, h.2.1.2.2.1, h.2.2.2.1⟩

theorem rb_of {α : Type} {m : NonDet (State Unit) α} (hR : ∀ σ, RB C I σ → ∀ y ∈ (m σ).1, Rdy y.2)
    (hD : IK (P12.DK C) m) (hQ : Q1K m) (hS : SInvB.SIK m) (hG : SInvV.GK m)
    (hO : IK (SInvU.IO (fun _ => I)) m) (hI : SInvL.IsK I m) : IK (RB C I) m :=
  fun σ h y hy => ⟨hR σ h y hy, hD σ h.2.1 y hy, hQ σ h.2.2.1 y hy, hS σ h.2.2.2.1 y hy,
    hG _ SInvV.wl_vmt σ h.2.2.2.2.1 y hy, hO σ h.2.2.2.2.2.1 y hy, hI σ h.2.2.2.2.2.2 y hy⟩

theorem rb_ro {α : Type} {m : NonDet (State Unit) α} (hm : ∀ σ0, IK (· = σ0) m) : IK (RB C I) m :=
  fun σ h y hy => (cq5_ro hm hy) ▸ h

theorem rb_getCap (sl : CslotPtr) : IK (RB C I) (getCap (Z := Unit) sl) :=
  rb_ro fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)

theorem rb_emptySlot (sl : CslotPtr) (ci : Cap) : IK (RB C I) (emptySlot (Z := Unit) sl ci) :=
  rb_of (fun σ h y hy => rd_emptySlot sl ci σ h.1 y hy) (R14.dz_emptySlot C sl ci) (q1_emptySlot sl ci)
    (fun σ h y hy => SInvB.sik_fin (fun _ => SInvB.sb_emptySlot sl ci) h hy) (SInvV.gk_emptySlot sl ci)
    (SInvU.io_emptySlot sl ci) (SInvL.isk_emptySlot sl ci)

theorem rb_capSwapForDelete (a b : CslotPtr) : IK (RB C I) (capSwapForDelete (Z := Unit) a b) :=
  rb_of (fun σ h y hy => rd_capSwapForDelete a b σ h.1 y hy) (R14.dz_capSwapForDelete C a b) (q1_capSwapForDelete a b)
    (fun σ h y hy => SInvB.sik_fin (fun _ => SInvB.sb_capSwapForDelete a b) h hy)
    (SInvV.gk_of_mtk (MachT.mtk_capSwapForDelete' a b)) (SInvU.io_capSwapForDelete a b)
    (SInvL.isk_capSwapForDelete a b)

/-- A cap write covered by the slot view keeps `RB`. -/
theorem rb_setCap_cov (c : Cap) (sl : CslotPtr) (s : State Unit) (hcov : SInvU.CovBy (SInvU.uV s).2.1 c)
    (h : RB C I s) {y : Unit × State Unit} (hy : y ∈ (setCap (Z := Unit) c sl s).1) : RB C I y.2 := by
  refine ⟨rd_setCap c sl s h.1 y hy, R14.dz_setCap C c sl s h.2.1 y hy, q1_setCap c sl s h.2.2.1 y hy,
    SInvB.sik_fin (fun _ => SInvB.sb_setCap c sl) h.2.2.2.1 hy,
    SInvV.gk_of_mtk (MachT.mtk_setCap c sl) _ SInvV.wl_vmt s h.2.2.2.2.1 y hy, ?_,
    SInvL.isk_setCap c sl s h.2.2.2.2.2.2 y hy⟩
  have hv := SInvU.hv_setCap c sl (SInvU.uV s) s rfl y hy
  show SInvU.IrqOutV (fun _ => I) (SInvU.uV y.2)
  rw [hv]
  exact SInvU.irqOut_vCap h.2.2.2.2.2.1 hcov sl

/-- **`finalise_cap` of a held cap keeps `RB`.** -/
theorem rb_finaliseCap (c : Cap) (fin : Bool) (s : State Unit) (sl : CslotPtr) (hc : SInvU.capAt s sl = some c)
    (h : RB C I s) {y : (Cap × Cap) × State Unit} (hy : y ∈ (finaliseCap (Z := Unit) c fin s).1) : RB C I y.2 := by
  have hI : ∀ p b, c = .schedContextCap p b → p ≠ s.idleSc := by
    intro p b e hp
    subst e
    rw [h.2.2.2.2.2.2] at hp
    subst hp
    exact h.2.2.2.2.2.1 0 sl _ hc (by simp [SInvU.covR, SInvU.capRng, objRefs])
  exact ⟨rdf_finaliseCap c fin s (fh_of h) hI y hy, R14.dz_finaliseCap C c fin s h.2.1 y hy,
    q1_finaliseCap c fin s h.2.2.1 y hy, SInvB.si_finaliseCap c fin s h.2.2.2.1 y hy,
    SInvV.gk_of_mtk (MachT.mtk_finaliseCap c fin) _ SInvV.wl_vmt s h.2.2.2.2.1 y hy,
    SInvU.io_finaliseCap c fin s h.2.2.2.2.2.1 y hy, SInvL.isk_finaliseCap c fin s h.2.2.2.2.2.2 y hy⟩

theorem rb_preemptionPoint : IKE (RB C I) (preemptionPoint (Z := Unit)) := by
  intro σ h y hy
  exact ⟨rdy_preemptionPoint σ h.1 h.2.2.2.2.1 hy, R14.dz_preemptionPoint C σ h.2.1 y hy,
    q1_preemptionPoint σ h.2.2.1 y hy,
    SInvB.sik_fin (fun _ => SInvB.sb_preemptionPoint) h.2.2.2.1 hy,
    SInvV.gk_preemptionPoint _ SInvV.wl_vmt σ h.2.2.2.2.1 y hy,
    SInvU.io_of_uk (fun _ => SInvU.uk_preemptionPoint) σ h.2.2.2.2.2.1 y hy,
    SInvL.isk_preemptionPoint σ h.2.2.2.2.2.2 y hy⟩

/-! ## `rec_del` -/

/-- **One step of `rec_del`**, its recursive calls keeping `RB` (ut7's `no_recDelF` skeleton). -/
theorem rb_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, IK (RB C I) (f k)) (k : RecDelCall) : IKE (RB C I) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (RB C I) (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall s e =>
    unfold recDelF withoutPreemption
    repeat' (first | exact hrec' _ | exact rb_emptySlot _ _ | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDet.when))
  | finaliseSlotCall sl e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := SInvU.mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := SInvU.getCap_capAt hx
    simp only at e1 hc
    subst e1
    try dsimp only at hy1
    split at hy1
    · rw [SInvU.mem_ret_ok hy1]; exact hσ
    · obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := SInvU.mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rem, cl⟩ := rc
      have hO3 : RB C I σ3 := rb_finaliseCap cap _ _ sl hc hσ hx3
      have hc3 : SInvU.capAt σ3 sl = some cap := SInvU.finaliseCap_keepAt hc _ _ hx3
      have hcov : SInvU.covR rem ⊆ SInvU.covR cap := SInvU.finaliseCap_cov cap _ _ _ hx3
      try dsimp only at hy3
      split at hy3
      · rw [SInvU.mem_ret_ok hy3]; exact hO3
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
            rw [SInvU.mem_ret_ok hy4]
            exact rb_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
          · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hO5 : RB C I σ4 := rb_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
          obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy4
          have hI5 : RB C I z.2 := hrec (.reduceZombieCall rem sl e) σ4 hO5 z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := SInvU.mem_bindE' hy5
            have hI6 : RB C I z6.2 := rb_preemptionPoint z.2 hI5 z6 hz6
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec (.finaliseSlotCall sl e) z6.2 hI6 y hy6
            · exact hI6
          · exact hI5
  | reduceZombieCall c s e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => intro σ _ y hy; exact (SInvU.rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          simp only [recDelF, withoutPreemption]
          repeat' (first | exact rb_capSwapForDelete _ _ | ik_step0 | ik_unfold)
        | true =>
          intro σ hσ y hy
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
          · obtain rfl := SInvU.mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
            have hp : RB C I z.2 := hrec (.cTEDeleteCall _ _) σ hσ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact hp
            obtain ⟨z2, hz2, ⟨nc, hnc, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
            swap
            · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz2
              rw [hx] at her; cases her
            obtain ⟨⟨nc', σ5⟩, hx5, rfl⟩ := SInvU.mem_liftE' hz2
            cases hnc
            obtain ⟨e5, hc5⟩ := SInvU.getCap_capAt hx5
            simp only at e5 hc5
            subst e5
            try dsimp only at hy
            split at hy
            · rename_i hnz
              subst hnz
              obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz3
                rw [SInvU.mem_ret_ok hy]
                exact rb_setCap_cov (.zombie ptr bits n) s z.2
                  (SInvU.covBy_of hc5 (fun q hq => by simpa [SInvU.covR, SInvU.capRng, objRefs] using hq)) hp hx
              · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [SInvU.mem_ret_ok hy]
                exact hp
              · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := SInvU.mem_ret_ok hz; cases her
    | _ => intro σ _ y hy; exact (SInvU.rz_fail rfl hy).elim

/-- **`rec_del` keeps `RB`** (every outcome, preemption errors included). -/
theorem rb_recDel (k : RecDelCall) : IKE (RB C I) (recDel (Z := Unit) k) := by
  unfold recDel
  exact ik_lfp (fun f hf k => rb_recDelF f hf k) k

theorem rb_capDelete (sl : CslotPtr) : IKE (RB C I) (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (rb_recDel _) fun _ => ike_returnOk _

/-- **The deletion cone's `cap_delete` keeps `Rdy`** with its carried bundle,
at every outcome (preemption errors included). -/
def RdCapDeleteH : Prop := ∀ C I sl, IKE (RB C I) (capDelete (Z := Unit) sl)

theorem rdCapDeleteH : RdCapDeleteH := fun _ _ sl => rb_capDelete sl

/-- One step of `cap_revoke`, its recursive calls keeping `RB`. -/
theorem rb_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (RB C I) (f k)) (sl : CslotPtr) : IKE (RB C I) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (RB C I) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first | exact rb_getCap _ | exact rb_capDelete _ | exact rb_preemptionPoint | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless))
  all_goals exact hrec' _

/-- **`cap_revoke` keeps `RB`** (every outcome). -/
theorem rb_capRevoke (sl : CslotPtr) : IKE (RB C I) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => rb_capRevokeF hf k) sl

/-- **`cap_delete_one` keeps `RB`.** -/
theorem rb_capDeleteOne (sl : CslotPtr) : IK (RB C I) (capDeleteOne (Z := Unit) sl) :=
  rb_of (fun σ h y hy => rdf_capDeleteOne sl σ (fh_of h) y hy) (R14.dz_capDeleteOne C sl) (q1_capDeleteOne sl)
    (SInvB.si_capDeleteOne sl) (SInvV.gk_of_mtk (MachT.mtk_capDeleteOne' sl)) (SInvU.io_capDeleteOne sl)
    (SInvL.isk_capDeleteOne sl)

/-- **`cancel_badged_sends` keeps `Rdy ∧ NQ []`** (re-export for the CNode perform). -/
theorem rq_cancelBadgedSends (e : ObjRef) (b : Badge) : IK RQ (cancelBadgedSends (Z := Unit) e b) :=
  rdq_cancelBadgedSends e b

end

end Fl4Proofs.P3.SInvR.B8f
