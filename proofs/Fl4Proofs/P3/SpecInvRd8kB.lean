/-
P3 (DESIGN.md §9), invariant line G1 (rd8k): **`Sched.BlockedScActive`
across the deletion cone** (spec side only, outside the JAtZ cone; KENTRY-PLAN
rd8i handoff 3, finalise_cap's SC arm).

* **`ba_finSc`**: a final SC cap's finalisation. sl3's chain
  (`scd1_unbindAllTcbs` / `scd2_unbindNtfn` / `scd3_unbindReply`, the yield
  unbind by `scb_auto`) leaves the SC with no bound TCB (it is not the idle SC)
  and an empty reply stack, so rd8i's `ba_schedContextSetInactive_p` applies.
* **`ba_finaliseCap c fin σ (hI : SC cap ⇒ not the idle SC)`** (every other
  arm by the generated family).
* **`KD I s := BSA s ∧ IO (fun _ => I) s ∧ idleSc = I`** (vi3 / ut7's
  `IdleScOutV`: no held cap covers the idle SC — rd8f's argument), `kd_of`,
  `kd_finaliseCap` (a held cap), `kd_setCap_cov`, `kd_preemptionPoint`,
  **`kd_recDelF`**, **`kd_recDel`**, **`kd_capDelete`**, **`kd_capRevoke`**
  (rd8f's `rb_*` skeleton, `RB` replaced by `KD`).
-/
import Fl4Proofs.P3.SpecInvRd8kA
import Fl4Proofs.P3.SpecInvRd8fC
open Classical

namespace Fl4Proofs.P3.SInvR.B8k
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8g
  Fl4Proofs.P3.SInvR.B8i

noncomputable section

set_option maxHeartbeats 1000000

/-- **A final SC cap's finalisation** (not the idle SC). -/
theorem ba_finSc (p : ObjRef) (σ : State Unit) (hI : p ≠ σ.idleSc)
    {z1 z2 z3 z4 y : Unit × State Unit}
    (hz1 : z1 ∈ (schedContextUnbindAllTcbs (Z := Unit) p σ).1)
    (hz2 : z2 ∈ (schedContextUnbindNtfn (Z := Unit) p z1.2).1)
    (hz3 : z3 ∈ (schedContextUnbindReply (Z := Unit) p z2.2).1)
    (hz4 : z4 ∈ (schedContextUnbindYieldFrom (Z := Unit) p z3.2).1)
    (hy : y ∈ (schedContextSetInactive (Z := Unit) p z4.2).1) (hb : BSA σ) : BSA y.2 := by
  have b1 := ba_schedContextUnbindAllTcbs p σ hb z1 hz1
  have b2 := ba_schedContextUnbindNtfn p z1.2 b1 z2 hz2
  have b3 := ba_schedContextUnbindReply p z2.2 b2 z3 hz3
  have b4 := ba_schedContextUnbindYieldFrom p z3.2 b3 z4 hz4
  have q1 := SInvL.scd1_unbindAllTcbs (I2 := σ.idleSc) (p := p) σ rfl z1 hz1
  have q2 := SInvL.scd2_unbindNtfn (I2 := σ.idleSc) (p := p) z1.2 q1 z2 hz2
  have q3 := SInvL.scd3_unbindReply (I2 := σ.idleSc) (p := p) z2.2 q2 z3 hz3
  have q4 : SInvL.ScB p (SInvL.QD σ.idleSc p) z4.2 :=
    (show IK (SInvL.ScB p (SInvL.QD σ.idleSc p)) (schedContextUnbindYieldFrom (Z := Unit) p) by
      unfold schedContextUnbindYieldFrom; scb_auto) z3.2 q3 z4 hz4
  obtain ⟨y4, n4, hk4, hq⟩ := q4
  obtain ⟨ht4, -, hr4⟩ := hq
  refine ba_schedContextSetInactive_p p z4.2 (fun y' n' hk => ?_) b4 y hy
  rw [hk4] at hk; cases hk
  refine ⟨fun t ht => ?_, hr4⟩
  rcases ht4 with h | h
  · rw [h] at ht; cases ht
  · exact absurd h hI

/-- **`finalise_cap`** keeps `BlockedScActive`, an SC cap's SC not the idle SC. -/
theorem ba_finaliseCap (c : Cap) (fin : Bool) (σ : State Unit)
    (hI : ∀ p b, c = .schedContextCap p b → p ≠ σ.idleSc) : IKp BSA σ (finaliseCap (Z := Unit) c fin) := by
  cases c
  case schedContextCap p b =>
    cases fin
    · simp only [finaliseCap, NonDet.when, Bool.false_eq_true, ↓reduceIte]
      intro hb y hy
      obtain ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩ := hy
      simp only [Set.mem_singleton_iff] at hz1 hz2 hz3 hz4 hz5 hy
      subst hz1 hz2 hz3 hz4 hz5 hy
      exact hb
    · simp only [finaliseCap, NonDet.when, ↓reduceIte]
      intro hb y ⟨z1, hz1, z2, hz2, z3, hz3, z4, hz4, z5, hz5, hy⟩
      rw [Set.mem_singleton_iff.1 hy]
      exact ba_finSc p σ (hI p b rfl) hz1 hz2 hz3 hz4 hz5 hb
  all_goals exact ikp_of_ik (by simp only [finaliseCap]; ba_auto) σ

/-! ## The deletion cone -/

/-- **The deletion cone's bundle for `BlockedScActive`.** -/
def KD (I : ObjRef) (s : State Unit) : Prop :=
  BSA s ∧ SInvU.IO (fun _ => I) s ∧ s.idleSc = I

variable {I : ObjRef}

theorem kd_of {α : Type} {m : NonDet (State Unit) α} (hB : BAK m)
    (hO : IK (SInvU.IO (fun _ => I)) m) (hI : SInvL.IsK I m) : IK (KD I) m :=
  fun σ h y hy => ⟨hB σ h.1 y hy, hO σ h.2.1 y hy, hI σ h.2.2 y hy⟩

theorem kd_ro {α : Type} {m : NonDet (State Unit) α} (hm : ∀ σ0, IK (· = σ0) m) : IK (KD I) m :=
  fun σ h y hy => (cq5_ro hm hy) ▸ h

theorem kd_getCap (sl : CslotPtr) : IK (KD I) (getCap (Z := Unit) sl) :=
  kd_ro fun _ => by unfold getCap; repeat' (first | ik_step0 | ik_unfold)

theorem kd_emptySlot (sl : CslotPtr) (ci : Cap) : IK (KD I) (emptySlot (Z := Unit) sl ci) :=
  kd_of (ba_emptySlot sl ci) (SInvU.io_emptySlot sl ci) (SInvL.isk_emptySlot sl ci)

theorem kd_capSwapForDelete (a b : CslotPtr) : IK (KD I) (capSwapForDelete (Z := Unit) a b) :=
  kd_of (ba_capSwapForDelete a b) (SInvU.io_capSwapForDelete a b) (SInvL.isk_capSwapForDelete a b)

/-- A cap write covered by the slot view keeps `KD`. -/
theorem kd_setCap_cov (c : Cap) (sl : CslotPtr) (s : State Unit) (hcov : SInvU.CovBy (SInvU.uV s).2.1 c)
    (h : KD I s) {y : Unit × State Unit} (hy : y ∈ (setCap (Z := Unit) c sl s).1) : KD I y.2 := by
  refine ⟨ba_setCap c sl s h.1 y hy, ?_, SInvL.isk_setCap c sl s h.2.2 y hy⟩
  have hv := SInvU.hv_setCap c sl (SInvU.uV s) s rfl y hy
  show SInvU.IrqOutV (fun _ => I) (SInvU.uV y.2)
  rw [hv]
  exact SInvU.irqOut_vCap h.2.1 hcov sl

/-- **`finalise_cap` of a held cap keeps `KD`.** -/
theorem kd_finaliseCap (c : Cap) (fin : Bool) (s : State Unit) (sl : CslotPtr) (hc : SInvU.capAt s sl = some c)
    (h : KD I s) {y : (Cap × Cap) × State Unit} (hy : y ∈ (finaliseCap (Z := Unit) c fin s).1) : KD I y.2 := by
  have hI : ∀ p b, c = .schedContextCap p b → p ≠ s.idleSc := by
    intro p b e hp
    subst e
    rw [h.2.2] at hp
    subst hp
    exact h.2.1 0 sl _ hc (by simp [SInvU.covR, SInvU.capRng, objRefs])
  exact ⟨ba_finaliseCap c fin s hI h.1 y hy, SInvU.io_finaliseCap c fin s h.2.1 y hy,
    SInvL.isk_finaliseCap c fin s h.2.2 y hy⟩

theorem kd_preemptionPoint : IKE (KD I) (preemptionPoint (Z := Unit)) := by
  intro σ h y hy
  exact ⟨ba_preemptionPoint σ h.1 y hy, SInvU.io_of_uk (fun _ => SInvU.uk_preemptionPoint) σ h.2.1 y hy,
    SInvL.isk_preemptionPoint σ h.2.2 y hy⟩
/-- **One step of `rec_del`**, its recursive calls keeping `KD` (ut7's `no_recDelF` skeleton). -/
theorem kd_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, IK (KD I) (f k)) (k : RecDelCall) : IKE (KD I) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (KD I) (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall s e =>
    unfold recDelF withoutPreemption
    repeat' (first | exact hrec' _ | exact kd_emptySlot _ _ | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDet.when))
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
      have hO3 : KD I σ3 := kd_finaliseCap cap _ _ sl hc hσ hx3
      have hc3 : SInvU.capAt σ3 sl = some cap := SInvU.finaliseCap_keepAt hc _ _ hx3
      have hcov : SInvU.covR rem ⊆ SInvU.covR cap := SInvU.finaliseCap_cov cap _ _ _ hx3
      try dsimp only at hy3
      split at hy3
      · rw [SInvU.mem_ret_ok hy3]; exact hO3
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
            rw [SInvU.mem_ret_ok hy4]
            exact kd_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
          · obtain ⟨x, -, hx⟩ := SInvU.mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := SInvU.mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hO5 : KD I σ4 := kd_setCap_cov rem sl σ3 (SInvU.covBy_of hc3 hcov) hO3 hx4
          obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy4
          have hI5 : KD I z.2 := hrec (.reduceZombieCall rem sl e) σ4 hO5 z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := SInvU.mem_bindE' hy5
            have hI6 : KD I z6.2 := kd_preemptionPoint z.2 hI5 z6 hz6
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
          repeat' (first | exact kd_capSwapForDelete _ _ | ik_step0 | ik_unfold)
        | true =>
          intro σ hσ y hy
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := SInvU.mem_bindE' hy
          · obtain rfl := SInvU.mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := SInvU.mem_bindE' hy
            have hp : KD I z.2 := hrec (.cTEDeleteCall _ _) σ hσ z hz
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
                exact kd_setCap_cov (.zombie ptr bits n) s z.2
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

/-- **`rec_del` keeps `KD`** (every outcome, preemption errors included). -/
theorem kd_recDel (k : RecDelCall) : IKE (KD I) (recDel (Z := Unit) k) := by
  unfold recDel
  exact ik_lfp (fun f hf k => kd_recDelF f hf k) k

theorem kd_capDelete (sl : CslotPtr) : IKE (KD I) (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (kd_recDel _) fun _ => ike_returnOk _

/-- One step of `cap_revoke`, its recursive calls keeping `KD`. -/
theorem kd_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (KD I) (f k)) (sl : CslotPtr) : IKE (KD I) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (KD I) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first | exact kd_getCap _ | exact kd_capDelete _ | exact kd_preemptionPoint | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless))
  all_goals exact hrec' _

/-- **`cap_revoke` keeps `KD`** (every outcome). -/
theorem kd_capRevoke (sl : CslotPtr) : IKE (KD I) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => kd_capRevokeF hf k) sl

end

end Fl4Proofs.P3.SInvR.B8k
