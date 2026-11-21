/-
P3 (DESIGN.md §9), invariant line G1 (ctq12): **EB across the performs**,
part 4: ThreadControlCaps (spec side only, outside the JAtZ cone).
Each `install_tcb_cap` / `install_tcb_frame_cap` is a `cap_delete`
(`EbCapDeleteH`, ctq11) followed by checked cap inserts, a TCB field write
and `reschedule_required`, which keep `DK C`.
-/
import Fl4Proofs.P3.SpecInvCqC3
open Classical

namespace Fl4Proofs.P3.SInvQ.P12
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- The checked insert of `install_tcb_cap` / `install_tcb_frame_cap` keeps `DK C`. -/
theorem dk_checkedInsert (C : ObjRef) (nc : Cap) (ss : CslotPtr) (target : ObjRef) (slot d : CslotPtr) :
    IK (DK C) (checkCapAt (Z := Unit) nc ss (checkCapAt (.threadCap target) slot (capInsert nc ss d))) :=
  dk_of (by eb_auto)
    (SInv.ct_checkCapAt _ _ _ (SInv.ct_checkCapAt _ _ _ (SInv.ct_capInsert _ _ _))) (fun _ => by p12_nsw_auto)
    (SInv.nq_checkCapAt _ _ _ (SInv.nq_checkCapAt _ _ _ (SInv.nq_capInsert _ _ _)))

theorem dk_ipcBufferSet (C : ObjRef) (ptr : VSpaceRef) (target : ObjRef) :
    IK (DK C) (threadSet (Z := Unit) (fun t => { t with tcbIpcBuffer := ptr }) target) :=
  dk_of (by eb_auto) (SInv.ct_threadSet _ _) (fun _ => by p12_nsw_auto) (SInv.nq_threadSet _ _ fun _ => rfl)

theorem dk_whenResched (C : ObjRef) (b : Prop) [Decidable b] :
    IK (DK C) (NonDet.when b (rescheduleRequired (Z := Unit))) := by
  refine dk_of (by eb_auto) ?_ (fun _ => ?_) ?_
  · unfold NonDet.when; split
    · exact SInv.ct_rescheduleRequired
    · ct_auto
  · p12_nsw_auto
  · unfold NonDet.when; split
    · exact SInv.nq_rescheduleRequired
    · nq2_auto

theorem hke_returnOk {P : State Unit → Prop} {ε α : Type} (r : α) :
    HKE P P (NonDetE.returnOk (ε := ε) (σ := State Unit) r) := by
  intro σ hσ y hy
  first
    | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hσ)
    | (dsimp only [NonDetE.returnOk] at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hσ)

theorem dk_installTcbCap (hD : EbCapDeleteH) (C target : ObjRef) (slot : CslotPtr) (n : Nat)
    (o : Option (Cap × CslotPtr)) : HKEr (DK C) (DK C) (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => simp only [installTcbCap]; exact hker_ret _ fun _ => dk_eb
  | some p =>
    obtain ⟨nc, ss⟩ := p
    simp only [installTcbCap]
    refine hker_bind (hD C _) fun _ => hker_of ?_ fun _ => dk_eb
    unfold NonDetE.unlessE
    split
    · exact hke_returnOk _
    · exact hk_liftE (dk_checkedInsert C nc ss target slot _)

theorem dk_installTcbFrameCap (hD : EbCapDeleteH) (C target : ObjRef) (slot : CslotPtr)
    (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    HKEr (DK C) (DK C) (installTcbFrameCap (Z := Unit) target slot b) := by
  rcases b with _ | ⟨ptr, _ | ⟨nc, ss⟩⟩
  · simp only [installTcbFrameCap]; exact hker_ret _ fun _ => dk_eb
  all_goals
    simp only [installTcbFrameCap]
    refine hker_bind (hD C _) fun _ => ?_
    refine hker_bind (hker_of (hk_liftE (dk_ipcBufferSet C ptr target)) fun _ => dk_eb) fun _ => ?_
    refine hker_bind (R := DK C) (hker_of (P := DK C) (Q := DK C) (hk_liftE (?_ : IK (DK C) _)) fun _ => dk_eb)
      fun _ => ?_
    · first
        | exact dk_checkedInsert C _ _ target slot _
        | p12_dk_auto
    refine hker_bind (R := DK C) (hker_of (P := DK C) (Q := DK C) (hk_liftE (?_ : IK (DK C) _)) fun _ => dk_eb)
      fun cur => ?_
    · p12_dk_auto
    exact hker_of (hk_liftE (dk_whenResched C _)) fun _ => dk_eb

/-- **ThreadControlCaps** (`EbCapDeleteH` for its five cap deletions). -/
theorem eb_perfTcbCaps (hD : EbCapDeleteH) (C : ObjRef) (bl call don : Bool) (target : Word) (slot : CslotPtr)
    (fh th cr vr : Option (Cap × CslotPtr)) (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    HKEr (DK C) (DK C)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.threadControlCaps target slot fh th cr vr buf))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hker_bind (dk_installTcbCap hD C _ _ _ _) fun _ => ?_
  refine hker_bind (dk_installTcbCap hD C _ _ _ _) fun _ => ?_
  refine hker_bind (dk_installTcbCap hD C _ _ _ _) fun _ => ?_
  refine hker_bind (dk_installTcbCap hD C _ _ _ _) fun _ => ?_
  refine hker_bind (dk_installTcbFrameCap hD C _ _ _) fun _ => ?_
  exact hker_ret _ fun _ => dk_eb

end

end Fl4Proofs.P3.SInvQ.P12
