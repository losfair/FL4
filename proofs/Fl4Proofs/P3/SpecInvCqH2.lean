/-
P3 (DESIGN.md §9), invariant line G1 (ctq14): **the deletion cone keeps
`DK C`**, part 2: `finalise_cap`, `rec_del` (least fixed point, `ik_lfp`),
`cap_delete`, `cap_revoke` (spec side only, outside the JAtZ cone).

* `dz_suspend`: `suspend t` keeps `EB true` since `Simple` gives `NSw t`
  (ctq12's `eb_suspend_p`); `t` may be the current thread (its own TCB cap
  deleted): `RBk true` only asks ct to be in no ready queue, not the switch
  target and not released, which suspend keeps.
* `dz_finaliseCap`: every cap kind (the endpoint / notification / reply arms
  by part 1, the IRQ handler by `dz_capDeleteOne`).
* Every outcome of `rec_del` / `cap_delete` / `cap_revoke` (errors from a
  preemption point included) has `DK C` (`dz_recDel`, `dz_capDelete`,
  `dz_capRevoke`: `IKE (DK C)`), hence the discharged ctq12 hypotheses
  **`ebCapDeleteH : EbCapDeleteH`** and **`ebCapRevokeH : EbCapRevokeH`**.
-/
import Fl4Proofs.P3.SpecInvCqH1
open Classical

namespace Fl4Proofs.P3.SInvQ.R14
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `finalise_cap` -/

theorem dz_suspend (C t : ObjRef) : IK (DK C) (suspend (Z := Unit) t) := by
  intro σ hσ y hy
  exact ⟨eb_suspend_p t σ (hσ.2.2.1 t) hσ.1 y hy, SInv.ct_suspend (cq := C) t σ hσ.2.1 y hy,
    fun u => (show IK (NSw u) (suspend (Z := Unit) t) by unfold suspend; p12_nsw_auto) σ (hσ.2.2.1 u) y hy,
    SInv.nq_suspend (Kq := [C]) t σ hσ.2.2.2 y hy⟩

theorem dz_unbindNotification (C t : ObjRef) : IK (DK C) (unbindNotification (Z := Unit) t) :=
  dk_of (by eb_auto) (SInv.ct_unbindNotification _) (fun _ => by unfold unbindNotification; p12_nsw_auto)
    (SInv.nq_unbindNotification _)

theorem dz_unbindFromSc (C t : ObjRef) : IK (DK C) (unbindFromSc (Z := Unit) t) :=
  dk_of (by eb_auto) (SInv.ct_unbindFromSc _) (fun _ => by unfold unbindFromSc; p12_nsw_auto)
    (SInv.nq_unbindFromSc _)

theorem dz_prepareThreadDelete (C t : ObjRef) : IK (DK C) (prepareThreadDelete (Z := Unit) t) :=
  dk_of (by eb_auto) (SInv.ct_prepareThreadDelete _) (fun _ => by unfold prepareThreadDelete; p12_nsw_auto)
    (SInv.nq_prepareThreadDelete _)

theorem dz_schedContextUnbindAllTcbs (C sc : ObjRef) : IK (DK C) (schedContextUnbindAllTcbs (Z := Unit) sc) :=
  dk_of (by eb_auto) (SInv.ct_schedContextUnbindAllTcbs _)
    (fun _ => by unfold schedContextUnbindAllTcbs; p12_nsw_auto) (SInv.nq_schedContextUnbindAllTcbs _)

theorem dz_schedContextUnbindNtfn (C sc : ObjRef) : IK (DK C) (schedContextUnbindNtfn (Z := Unit) sc) :=
  dk_of (by eb_auto) (SInv.ct_schedContextUnbindNtfn _)
    (fun _ => by unfold schedContextUnbindNtfn; p12_nsw_auto) (SInv.nq_schedContextUnbindNtfn _)

theorem dz_schedContextUnbindReply (C sc : ObjRef) : IK (DK C) (schedContextUnbindReply (Z := Unit) sc) :=
  dk_of (by eb_auto) (SInv.ct_schedContextUnbindReply _)
    (fun _ => by unfold schedContextUnbindReply; p12_nsw_auto) (SInv.nq_schedContextUnbindReply _)

theorem dz_schedContextUnbindYieldFrom (C sc : ObjRef) :
    IK (DK C) (schedContextUnbindYieldFrom (Z := Unit) sc) :=
  dk_of (by eb_auto) (SInv.ct_schedContextUnbindYieldFrom _)
    (fun _ => by unfold schedContextUnbindYieldFrom; p12_nsw_auto) (SInv.nq_schedContextUnbindYieldFrom _)

theorem dz_schedContextSetInactive (C sc : ObjRef) : IK (DK C) (schedContextSetInactive (Z := Unit) sc) :=
  dk_of (by eb_auto) (SInv.ct_schedContextSetInactive _)
    (fun _ => by unfold schedContextSetInactive; p12_nsw_auto) (SInv.nq_schedContextSetInactive _)

theorem dz_archFinaliseCap (C : ObjRef) (a : ArchCap) (b : Bool) : IK (DK C) (archFinaliseCap (Z := Unit) a b) :=
  dk_of (by eb_auto) (SInv.ct_archFinaliseCap _ _) (fun _ => by unfold archFinaliseCap; p12_nsw_auto)
    (SInv.nq_archFinaliseCap _ _)

theorem dz_deletingIrqHandler (C : ObjRef) (irq : Irq) : IK (DK C) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact ik_bind (ik_gets _) fun sl => dz_capDeleteOne C sl

theorem dz_finaliseCap (C : ObjRef) (c : Cap) (final : Bool) : IK (DK C) (finaliseCap (Z := Unit) c final) := by
  cases c
  case replyCap r _ =>
    simp only [finaliseCap]
    refine ik_liftM _ ?_
    refine ik_when _ ?_
    refine ik_bind (by dz_rd) fun tp => ?_
    split
    · exact ik_pure _
    · dz_reply_arm
  case endpointCap r _ _ =>
    simp only [finaliseCap]
    exact ik_liftM _ (ik_when _ (dz_cancelAllIpc C r))
  case notificationCap r _ _ =>
    simp only [finaliseCap]
    refine ik_liftM _ (ik_when _ ?_)
    exact ik_bind (dz_schedContextMaybeUnbindNtfn C r) fun _ =>
      ik_bind (dz_unbindMaybeNotification C r) fun _ => dz_cancelAllSignals C r
  case threadCap r =>
    simp only [finaliseCap]
    exact ik_bind (ik_when _ (dz_unbindNotification C r)) fun _ =>
      ik_bind (ik_when _ (dz_unbindFromSc C r)) fun _ =>
      ik_bind (ik_when _ (dz_suspend C r)) fun _ =>
      ik_bind (ik_when _ (dz_prepareThreadDelete C r)) fun _ => ik_pure _
  case schedContextCap sc _ =>
    simp only [finaliseCap]
    exact ik_bind (ik_when _ (dz_schedContextUnbindAllTcbs C sc)) fun _ =>
      ik_bind (ik_when _ (dz_schedContextUnbindNtfn C sc)) fun _ =>
      ik_bind (ik_when _ (dz_schedContextUnbindReply C sc)) fun _ =>
      ik_bind (ik_when _ (dz_schedContextUnbindYieldFrom C sc)) fun _ =>
      ik_bind (ik_when _ (dz_schedContextSetInactive C sc)) fun _ => ik_pure _
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · exact ik_bind (dz_deletingIrqHandler C irq) fun _ => ik_pure _
    · exact ik_pure _
  case archObjectCap a =>
    simp only [finaliseCap]
    exact dz_archFinaliseCap C a final
  all_goals (simp only [finaliseCap]; dz_rd)

/-! ## `rec_del`, `cap_delete`, `cap_revoke` -/

theorem dz_setCap (C : ObjRef) (c : Cap) (sl : CslotPtr) : IK (DK C) (setCap (Z := Unit) c sl) :=
  dk_of (by eb_auto) (SInv.ct_setCap _ _) (fun _ => by unfold setCap; p12_nsw_auto) (SInv.nq_setCap _ _)

theorem dz_capSwapForDelete (C : ObjRef) (a b : CslotPtr) : IK (DK C) (capSwapForDelete (Z := Unit) a b) :=
  dk_of (by eb_auto) (SInv.ct_capSwapForDelete _ _) (fun _ => by unfold capSwapForDelete; p12_nsw_auto)
    (SInv.nq_capSwapForDelete _ _)

theorem dz_getCap (C : ObjRef) (sl : CslotPtr) : IK (DK C) (getCap (Z := Unit) sl) := by
  unfold getCap; dz_rd

theorem dz_preemptionPoint (C : ObjRef) : IKE (DK C) (preemptionPoint (Z := Unit)) := by
  intro σ hσ y hy
  exact ⟨⟨⟨⟨tq_preemptionPoint σ hσ.1.1.1.1 y hy, sa_preemptionPoint σ hσ.1.1.1.2 y hy⟩,
      q4_preemptionPoint σ hσ.1.1.2 y hy⟩, rb_preemptionPoint σ hσ.1.2 y hy⟩,
    SInv.ct_preemptionPoint (cq := C) σ hσ.2.1 y hy,
    fun u => (show IKE (NSw u) (preemptionPoint (Z := Unit)) by unfold preemptionPoint orChoiceE; p12_nsw_auto)
      σ (hσ.2.2.1 u) y hy,
    SInv.nq_preemptionPoint (Kq := [C]) σ hσ.2.2.2 y hy⟩

syntax "dz_leaf" : tactic
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_getCap _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_isFinalCap _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_finaliseCap _ _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_setCap _ _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_emptySlot _ _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_capSwapForDelete _ _ _)
macro_rules | `(tactic| dz_leaf) => `(tactic| with_reducible exact dz_preemptionPoint _)

macro "dz_auto" : tactic => `(tactic| repeat' (first | dz_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-- One step of `rec_del`, its recursive calls keeping `DK C`. -/
theorem dz_recDelF (C : ObjRef) {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IK (DK C) (f k)) (k : RecDelCall) : IKE (DK C) (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE (DK C) (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; dz_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; dz_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> dz_auto
    all_goals exact hrec' _

theorem dz_recDel (C : ObjRef) (c : RecDelCall) : IKE (DK C) (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => dz_recDelF C hf k) c

theorem dz_capDelete (C : ObjRef) (sl : CslotPtr) : IKE (DK C) (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (dz_recDel C _) fun _ => ike_returnOk _

theorem dz_capRevokeF (C : ObjRef) {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (DK C) (f k)) (sl : CslotPtr) : IKE (DK C) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (DK C) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first | dz_leaf | (with_reducible exact dz_capDelete _ _) | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless))
  all_goals exact hrec' _

theorem dz_capRevoke (C : ObjRef) (sl : CslotPtr) : IKE (DK C) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => dz_capRevokeF C hf k) sl

/-- Every outcome with `DK C` gives the result-sensitive triple. -/
theorem dz_hker {ε α : Type} {C : ObjRef} {m : NonDetE (State Unit) ε α} (h : IKE (DK C) m) :
    HKEr (DK C) (DK C) m :=
  fun σ hσ y hy => ⟨dk_eb (h σ hσ y hy), fun _ _ => h σ hσ y hy⟩

/-- **ctq12's `EbCapDeleteH`, discharged.** -/
theorem ebCapDeleteH : EbCapDeleteH := fun C slot => dz_hker (dz_capDelete C slot)

/-- **ctq12's `EbCapRevokeH`, discharged.** -/
theorem ebCapRevokeH : EbCapRevokeH := fun C slot => dz_hker (dz_capRevoke C slot)

end

end Fl4Proofs.P3.SInvQ.R14
