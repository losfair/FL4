/-
P3 (DESIGN.md §9), invariant line G1 (ctq18, ctq16 handoff 1 (b)-(c)): **`EB
true` at every error (preemption) outcome of `fl4_perform_invocation`** (spec
side only, outside the JAtZ cone).

* `EBR P m`: from a `P` state, every error outcome has `EB true`. Combinators as
  ctq16's `CKX` (`ebr_of_ne`, `ebr_bind_ike`, `ebr_bind_ne`, `ebr_mono`).
* Only three arms reach a preemption point (ctq16): CNode Revoke / Delete
  (ctq14's `dz_capRevoke` / `dz_capDelete`: `IKE (DK C)`, every outcome),
  ThreadControlCaps / ThreadControlSched (`install_tcb_cap` /
  `install_tcb_frame_cap` keep `DK C` on every outcome: **`dk_installTcbCapI`**,
  **`dk_installTcbFrameCapI`**, ctq14's `dz_capDelete` then ctq12's checked
  inserts / buffer write / `reschedule_required` leaves; the binding writers of
  ThreadControlSched follow the last preemption point and never error) and
  Untyped (`reset_untyped_cap`: ctq15's `eb_perfUntyped` at `k = true` keeps
  `EB true` on every outcome, from `UtInv''`, `IfLiveTN` and the decode's
  `UtRetOK`: detype of a childless untyped's region removes no runnable /
  queued TCB). Every other arm is ctq16's `NE`.
* **`ebr_fl4PerformInvocation C blk call don inv : EBR (PFE C inv) …`** with
  `PFE C inv := DK C ∧ UtInv'' ∧ IfLiveTN ∧ GapOKN (uV s) inv`.
* `sm_updateTimeStamp` (the front's `Simple` leaf not in SpecInvCqEr0).
-/
import Fl4Proofs.P3.SpecInvCqEr0
import Fl4Proofs.P3.SpecInvCqH3
import Fl4Proofs.P3.SpecInvCqHP
import Fl4Proofs.P3.SpecInvCqM2
open Classical

namespace Fl4Proofs.P3.SInvQ.R18
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.R14
  Fl4Proofs.P3.SInvQ.R16 Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

theorem sm_updateTimeStamp : SMK (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; sm0_auto

macro_rules | `(tactic| sm_leaf) => `(tactic| with_reducible exact sm_updateTimeStamp)

/-! ## The triple -/

/-- From a `P` state, every error outcome has `EB true`. -/
def EBR (P : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, P σ → ∀ y ∈ (m.run σ).1, ∀ e, y.1 = .error e → EB true y.2

theorem ebr_of_ne {P : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NE m) : EBR P m :=
  fun σ _ y hy e he => absurd he (h σ y hy e)

theorem ebr_of_ike {P : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : IKE P m)
    (hp : ∀ s, P s → EB true s) : EBR P m :=
  fun σ hσ y hy _ _ => hp _ (h σ hσ y hy)

theorem ebr_mono {P P' : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : EBR P m)
    (hp : ∀ s, P' s → P s) : EBR P' m :=
  fun σ hσ => h σ (hp σ hσ)

theorem ebr_bind_ike {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : IKE P m) (hp : ∀ s, P s → EB true s) (hg : ∀ a, EBR P (g a)) :
    EBR P (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 (hm σ hσ z hz) y hy e he
  · exact hp _ (hm σ hσ z hz)

theorem ebr_bind_ne {P : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : EBR P m) (hg : ∀ a, NE (g a)) : EBR P (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
  · exact absurd he (hg a z.2 y hy e)
  · exact hm σ hσ z hz e' he'

theorem dk_ebt {C : ObjRef} (s : State Unit) (h : DK C s) : EB true s := h.1

/-! ## `install_tcb_cap` / `install_tcb_frame_cap`, every outcome -/

/-- **`install_tcb_cap` keeps `DK C`** (every outcome, errors included). -/
theorem dk_installTcbCapI (C target : ObjRef) (slot : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    IKE (DK C) (installTcbCap (Z := Unit) target slot n o) := by
  cases o with
  | none => simp only [installTcbCap]; exact ike_returnOk _
  | some p =>
    obtain ⟨nc, ss⟩ := p
    simp only [installTcbCap]
    refine ike_bind (dz_capDelete C _) fun _ => ?_
    exact ike_unlessE _ (ike_liftE (dk_checkedInsert C nc ss target slot _))

/-- **`install_tcb_frame_cap` keeps `DK C`** (every outcome, errors included). -/
theorem dk_installTcbFrameCapI (C target : ObjRef) (slot : CslotPtr)
    (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (DK C) (installTcbFrameCap (Z := Unit) target slot b) := by
  rcases b with _ | ⟨ptr, _ | ⟨nc, ss⟩⟩
  · simp only [installTcbFrameCap]; exact ike_returnOk _
  all_goals
    simp only [installTcbFrameCap]
    refine ike_bind (dz_capDelete C _) fun _ => ?_
    refine ike_bind (ike_liftE (dk_ipcBufferSet C ptr target)) fun _ => ?_
    refine ike_bind (ike_liftE (?_ : IK (DK C) _)) fun _ => ?_
    · first
        | exact dk_checkedInsert C _ _ target slot _
        | exact ik_pure _
        | p12_dk_auto
    refine ike_bind (ike_liftE (ik_gets _)) fun _ => ?_
    exact ike_liftE (dk_whenResched C _)

/-! ## The arms -/

theorem ebr_invokeTcb (C : ObjRef) (i : TcbInvocation) : EBR (DK C) (invokeTcb (Z := Unit) i) := by
  cases i
  case threadControlCaps target slot fh th cr vr buf =>
    simp only [invokeTcb]
    refine ebr_of_ike ?_ dk_ebt
    refine ike_bind (dk_installTcbCapI C _ _ _ _) fun _ => ?_
    refine ike_bind (dk_installTcbCapI C _ _ _ _) fun _ => ?_
    refine ike_bind (dk_installTcbCapI C _ _ _ _) fun _ => ?_
    refine ike_bind (dk_installTcbCapI C _ _ _ _) fun _ => ?_
    exact ike_bind (dk_installTcbFrameCapI C _ _ _) fun _ => ike_returnOk _
  case threadControlSched target slot fh mcp prio sc =>
    simp only [invokeTcb]
    exact ebr_bind_ike (dk_installTcbCapI C _ _ _ _) dk_ebt fun _ => ebr_of_ne (by ne_auto)
  case notificationControl t o =>
    cases o <;> (simp only [invokeTcb]; exact ebr_of_ne (ne_liftE _))
  all_goals (simp only [invokeTcb]; exact ebr_of_ne (ne_liftE _))

theorem ebr_invokeCnode (C : ObjRef) (i : CnodeInvocation) : EBR (DK C) (invokeCnode (Z := Unit) i) := by
  cases i
  case revokeCall sl => simp only [invokeCnode]; exact ebr_of_ike (dz_capRevoke C sl) dk_ebt
  case deleteCall sl => simp only [invokeCnode]; exact ebr_of_ike (dz_capDelete C sl) dk_ebt
  case cancelBadgedSendsCall c =>
    cases c <;> (simp only [invokeCnode]; first | exact ebr_of_ne (ne_withoutPreemption _) | exact ebr_of_ne (ne_liftE _))
  all_goals (simp only [invokeCnode]; exact ebr_of_ne (ne_withoutPreemption _))

/-- The perform state's facts the error outcomes need. -/
abbrev PFE (C : ObjRef) (inv : Fl4Invocation) (s : State Unit) : Prop :=
  DK C s ∧ UtInv'' s ∧ IfLiveTN s ∧ GapOKN (uV s) inv

/-- **Every error outcome of `fl4_perform_invocation` from a `PFE C inv` state has `EB true`.** -/
theorem ebr_fl4PerformInvocation (C : ObjRef) (blk call don : Bool) (inv : Fl4Invocation) :
    EBR (PFE C inv) (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv
  case invokeUntyped ui =>
    intro σ hσ y hy _ _
    exact P15.eb_perfUntyped true blk call don ui σ
      ⟨hσ.1.1, hσ.2.1, hσ.2.2.1, utRetOK_of_V hσ.2.2.2.1⟩ y hy
  case invokeTCB i =>
    simp only [fl4PerformInvocation]
    exact ebr_mono (ebr_invokeTcb C i) fun _ h => h.1
  case invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact ebr_mono (ebr_bind_ne (ebr_invokeCnode C i) fun _ => ne_returnOk _) fun _ h => h.1
  case invokeFl4TCB i => simp only [fl4PerformInvocation]; exact ebr_of_ne (ne_invokeFl4Tcb i)
  case invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact ebr_of_ne (ne_bind (ne_invokeFl4IrqControl i) fun _ => ne_returnOk _)
  case invokeArchObject i => simp only [fl4PerformInvocation]; exact ebr_of_ne (ne_fl4ArchPerformInvocation i)
  all_goals (simp only [fl4PerformInvocation]; exact ebr_of_ne (by ne_auto))

end

end Fl4Proofs.P3.SInvQ.R18
