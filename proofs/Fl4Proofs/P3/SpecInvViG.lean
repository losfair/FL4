/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, vi2): `VI N S b`, part G: **deletion**
(vi1's handoff step 4).

`finalise_cap` writes an idle-relevant field only in its thread-cap arm (`unbind_from_sc`,
`suspend` of the cap's thread); the SC arm's `sched_context_unbind_all_tcbs` is guarded by
`sc_ptr ≠ idle_sc`, the reply arm reads the thread's state. So `vi_finaliseCap` needs only
`hc`: the cap is not a thread cap to `N`. Inside `rec_del` the finalised cap is read from its
slot, so `hc` follows from the IRQ-node-style fact `IO (fun _ => N)` (ut7's `IrqOutV` at the
constant map `N`: no cap's `covR` holds `N`, sg1's `IdleOutV`), carried along with `VI`:
**`VO N S b σ := VI N S b σ ∧ IO (fun _ => N) σ`**. `vo_recDelF` is ut7's `io_recDelF` with
`VI` added at each step (`IO` from the same io lemmas), then `rec_del`, `cap_delete`,
`cap_revoke` (both `ik_lfp`), the TCB cap installs and `invoke_cnode`.
-/
import Fl4Proofs.P3.SpecInvViF
import Fl4Proofs.P3.SpecInvUtO1
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N S T : ObjRef} {b : Bool}

/-! ## Fast finalisation and `finalise_cap` -/

theorem vi_fastFinalise (c : Cap) (fin : Bool) : IK (VI N S b) (fastFinalise (Z := Unit) c fin) := by
  cases c
  case replyCap r g =>
    simp only [fastFinalise]
    refine vi_when _ fun _ => ik_bind (by vi_auto) fun tptr => ?_
    cases tptr
    case none => exact ik_pure _
    case some tp =>
      refine vi_gts_bind tp fun st hst => ?_
      cases st
      all_goals (try dsimp only)
      all_goals first | exact vi_cancelIpc tp | exact vi_replyRemove tp _ (fun e => by cases hst e)
  all_goals simp only [fastFinalise]; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fastFinalise _ _)

theorem vi_capDeleteOne (sl : CslotPtr) : IK (VI N S b) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_capDeleteOne _)

theorem vi_deletingIrqHandler (irq : Irq) : IK (VI N S b) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_deletingIrqHandler _)

/-- **`finalise_cap`** of a cap that is no thread cap to `N`. -/
theorem vi_finaliseCap (c : Cap) (fin : Bool) (hc : ∀ r, c = .threadCap r → r ≠ N) :
    IK (VI N S b) (finaliseCap (Z := Unit) c fin) := by
  cases c
  case replyCap r g =>
    simp only [finaliseCap]
    refine ik_liftM _ (vi_when _ fun _ => ik_bind (by vi_auto) fun tptr => ?_)
    cases tptr
    case none => exact ik_pure _
    case some tp =>
      refine vi_gts_bind tp fun st hst => ?_
      cases st
      all_goals (try dsimp only)
      all_goals first | exact vi_cancelIpc tp | exact vi_replyRemove tp _ (fun e => by cases hst e)
  case threadCap r =>
    have hr : r ≠ N := hc r rfl
    simp only [finaliseCap]; vi_auto
  all_goals simp only [finaliseCap]; vi_auto

/-! ## The carried pair -/

/-- `VI` with the constant-map IRQ-node fact (no cap covers `N`). -/
def VO (N S : ObjRef) (b : Bool) (σ : State Unit) : Prop := VI N S b σ ∧ IO (fun _ => N) σ

theorem vo_of {α : Type} {m : NonDet (State Unit) α} (h1 : IK (VI N S b) m) (h2 : IK (IO (fun _ => N)) m) :
    IK (VO N S b) m :=
  fun σ hσ y hy => ⟨h1 σ hσ.1 y hy, h2 σ hσ.2 y hy⟩

/-- A cap held in a slot of a `VO` state is not a thread cap to `N`. -/
theorem vo_notIdleCap {σ : State Unit} (h : VO N S b σ) {sl : CslotPtr} {c : Cap} (hc : SInvU.capAt σ sl = some c) :
    ∀ r, c = .threadCap r → r ≠ N := by
  rintro r rfl rfl
  exact h.2 0 sl _ hc (by simp [covR, capRng, objRefs])

/-! ## `rec_del` -/

set_option maxHeartbeats 4000000 in
theorem vo_recDelF (f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hrec : ∀ k, IK (VO N S b) (f k)) (k : RecDelCall) :
    IKE (VO N S b) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (ε := Unit) (VO N S b) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall s e =>
    unfold recDelF withoutPreemption
    repeat' (first
      | exact hrec' _
      | (exact vo_of (vi_emptySlot _ _) (io_emptySlot _ _))
      | ik_step0 | (unfold NonDet.when))
  | finaliseSlotCall sl e =>
    intro σ hσ y hy
    simp only [recDelF, withoutPreemption] at hy
    obtain ⟨z, hz, H⟩ := mem_bindE' hy
    obtain ⟨⟨cap, σ1⟩, hx, rfl⟩ := mem_liftE' hz
    obtain ⟨a, ha, hy1⟩ | ⟨er, her, -⟩ := H
    swap
    · cases her
    injection ha with ha'
    subst ha'
    obtain ⟨e1, hc⟩ := getCap_capAt hx
    simp only at e1 hc
    subst e1
    try dsimp only at hy1
    split at hy1
    · rw [mem_ret_ok hy1]; exact hσ
    · obtain ⟨z, hz, H⟩ := mem_bindE' hy1
      obtain ⟨⟨fin, σ2⟩, hx2, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy2⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hx2)
      try dsimp only at hy2
      obtain ⟨z, hz, H⟩ := mem_bindE' hy2
      obtain ⟨⟨rc, σ3⟩, hx3, rfl⟩ := mem_liftE' hz
      obtain ⟨a, ha, hy3⟩ | ⟨er, her, -⟩ := H
      swap
      · cases her
      injection ha with ha'
      subst ha'
      obtain ⟨rem, cl⟩ := rc
      have hV3 : VI N S b σ3 := vi_finaliseCap cap _ (vo_notIdleCap hσ hc) _ hσ.1 _ hx3
      have hO3 : IO (fun _ => N) σ3 := io_finaliseCap cap _ _ hσ.2 _ hx3
      have hc3 : SInvU.capAt σ3 sl = some cap := finaliseCap_keepAt hc _ _ hx3
      have hcov : covR rem ⊆ covR cap := finaliseCap_cov cap _ _ _ hx3
      have hO4 : IrqOutV (fun _ => N) (vCap sl rem (uV σ3)) := irqOut_vCap hO3 (covBy_of hc3 hcov) sl
      try dsimp only at hy3
      split at hy3
      · rw [mem_ret_ok hy3]; exact ⟨hV3, hO3⟩
      · split at hy3
        · obtain ⟨z, hz, ⟨u, -, hy4⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy3
          · obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
            rw [mem_ret_ok hy4]
            have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
            refine ⟨vi_setCap rem sl σ3 hV3 _ hx4, ?_⟩
            show IrqOutV (fun _ => N) (uV σ4); rw [hv4]; exact hO4
          · obtain ⟨x, -, hx⟩ := mem_liftE' hz
            rw [hx] at her; cases her
        · obtain ⟨z, hz, H⟩ := mem_bindE' hy3
          obtain ⟨⟨u', σ4⟩, hx4, rfl⟩ := mem_liftE' hz
          obtain ⟨a, -, hy4⟩ | ⟨er, her, -⟩ := H
          swap
          · cases her
          have hv4 : uV σ4 = vCap sl rem (uV σ3) := hv_setCap rem sl (uV σ3) σ3 rfl _ hx4
          have hO5 : VO N S b σ4 := ⟨vi_setCap rem sl σ3 hV3 _ hx4, by
            show IrqOutV (fun _ => N) (uV σ4); rw [hv4]; exact hO4⟩
          obtain ⟨z, hz, H⟩ := mem_bindE' hy4
          have hI5 : VO N S b z.2 := hrec _ σ4 hO5 z hz
          obtain ⟨a, -, hy5⟩ | ⟨er, -, rfl⟩ := H
          · obtain ⟨z6, hz6, H⟩ := mem_bindE' hy5
            have hv6 : uV z6.2 = uV z.2 := uk_preemptionPoint (uvw := uV z.2) z.2 rfl z6 hz6
            have hI6 : VO N S b z6.2 := ⟨vi_preemptionPoint z.2 hI5.1 z6 hz6, by
              show IrqOutV (fun _ => N) (uV z6.2); rw [hv6]; exact hI5.2⟩
            obtain ⟨a, -, hy6⟩ | ⟨er, -, rfl⟩ := H
            · exact hrec _ z6.2 hI6 y hy6
            · exact hI6
          · exact hI5
  | reduceZombieCall c s e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => intro σ _ y hy; exact (rz_fail rfl hy).elim
      | succ n =>
        cases e with
        | false =>
          simp only [recDelF, withoutPreemption]
          exact vo_of (by vi_auto) (by io0_auto)
        | true =>
          intro σ hσ y hy
          simp only [recDelF, withoutPreemption] at hy
          obtain ⟨z, hz, ⟨es, hes, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
          · obtain rfl := mem_ret_ok hz
            cases hes
            try dsimp only at hy
            obtain ⟨z, hz, H⟩ := mem_bindE' hy
            have hp : VO N S b z.2 := hrec _ σ hσ z hz
            rcases H with ⟨a, ha, hy⟩ | ⟨er, -, rfl⟩
            swap
            · exact hp
            obtain ⟨z2, hz2, ⟨nc, hnc, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
            swap
            · obtain ⟨x, -, hx⟩ := mem_liftE' hz2
              rw [hx] at her; cases her
            obtain ⟨⟨nc', σ5⟩, hx5, rfl⟩ := mem_liftE' hz2
            cases hnc
            obtain ⟨e5, hc5⟩ := getCap_capAt hx5
            simp only at e5 hc5
            subst e5
            try dsimp only at hy
            split at hy
            · rename_i hnz
              subst hnz
              obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                rw [mem_ret_ok hy]
                have hv := hv_setCap (.zombie ptr bits n) s (uV z.2) z.2 rfl _ hx
                refine ⟨vi_setCap _ s z.2 hp.1 _ hx, ?_⟩
                show IrqOutV (fun _ => N) (uV x.2)
                rw [hv]
                exact irqOut_vCap hp.2 (covBy_of hc5 (fun q hq => by simpa [covR, capRng, objRefs] using hq)) s
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
            · obtain ⟨z3, hz3, ⟨u, -, hy⟩ | ⟨er, her, rfl⟩⟩ := mem_bindE' hy
              · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz3
                obtain ⟨-, rfl⟩ := hx
                rw [mem_ret_ok hy]
                exact hp
              · obtain ⟨x, -, hx⟩ := mem_liftE' hz3
                rw [hx] at her; cases her
          · obtain rfl := mem_ret_ok hz; cases her
    | _ => intro σ _ y hy; exact (rz_fail rfl hy).elim

/-- **`rec_del` keeps `VO`.** -/
theorem vo_recDel (c : RecDelCall) : IKE (VO N S b) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => vo_recDelF f hf k) c

theorem vo_capDelete (slot : CslotPtr) : IKE (VO N S b) (capDelete (Z := Unit) slot) := by
  unfold capDelete
  exact ike_bind (vo_recDel _) fun _ => ike_returnOk _

theorem vo_getCap (sl : CslotPtr) : IK (VO N S b) (getCap (Z := Unit) sl) :=
  ik_of_eq fun _ _ hx => (getCap_capAt hx).1

theorem vo_preemptionPoint : IKE (VO N S b) (preemptionPoint (Z := Unit)) :=
  vo_of vi_preemptionPoint (io_of_uk fun _ => uk_preemptionPoint)

theorem vo_selectExt {D : Type} (a : State DetExt → D) (S' : Set D) : IK (VO N S b) (selectExt (Z := Unit) a S') :=
  vo_of (vi_selectExt a S') (by unfold selectExt; repeat' ik_step0)

theorem vo_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (VO N S b) (f k)) (sl : CslotPtr) : IKE (VO N S b) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (VO N S b) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption
  repeat' (first
    | exact hrec' _
    | exact vo_capDelete _
    | exact vo_getCap _ | exact vo_preemptionPoint | exact vo_selectExt _ _
    | (refine vo_of ?_ ?_; focus (vi_auto; done); focus (io0_auto; done))
    | ik_step0 | (unfold NonDetE.whenE))

theorem vo_capRevoke (sl : CslotPtr) : IKE (VO N S b) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => vo_capRevokeF hf k) sl

/-! ## TCB cap installs and CNode invocations -/

theorem vo_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) :
    IKE (VO N S b) (installTcbCap (Z := Unit) target slot n slotOpt) := by
  cases slotOpt with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨c, src⟩ := p
    simp only [installTcbCap]
    refine ike_bind (vo_capDelete _) fun _ => ?_
    unfold NonDetE.unlessE
    split
    · exact ike_returnOk _
    · exact ike_liftE (vo_of (by vi_auto) (io_checkCapAt_ins c src _ slot _))

theorem vo_installTcbFrameCap (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (VO N S b) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  cases buffer with
  | none => exact ike_returnOk _
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    simp only [installTcbFrameCap]
    refine ike_bind (vo_capDelete _) fun _ => ?_
    refine ike_bind (ike_liftE (vo_of (by vi_auto) (by io0_auto))) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · cases frame with
      | none => exact vo_of (ik_pure _) (ik_pure _)
      | some q =>
        obtain ⟨c, src⟩ := q
        exact vo_of (by vi_auto) (io_checkCapAt_ins c src _ slot _)
    · exact ike_bind (ike_liftE (vo_of (ik_gets _) (ik_gets _))) fun _ =>
        ike_liftE (vo_of (by vi_auto) (by io0_auto))

end

end Fl4Proofs.P3.SInvI
