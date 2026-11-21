/-
P3 (DESIGN.md §9), invariant line G1 (ctq16, item 5 (b)): **`CKN` at every
error (preemption) outcome of `fl4_perform_invocation`** (spec side only,
outside the JAtZ cone).

* `NE m`: no outcome of `m` is an error (every `liftE` / `withoutPreemption` /
  `returnOk`); `CKX C m`: from a `CKC C` state, every error outcome has `CKN`
  (ctq14's CK and ct not BlockedOnReply). `ckx_bind_ike` (an `IKE (CKC C)`
  prefix), `ckx_bind_ne` (a tail that never errors).
* Only three perform arms reach a preemption point: Untyped
  (`reset_untyped_cap`, SpecInvCqHF3's `ck_resetUntypedCap`), TCB
  ThreadControlCaps / ThreadControlSched (`install_tcb_cap` /
  `install_tcb_frame_cap`: ctq14's `ck_capDelete`, then checked inserts) and
  CNode Revoke / Delete (`ck_capRevoke` / `ck_capDelete`). ThreadControlSched's
  binding writers (`set_mcpriority`, `set_priority`, SC bind / unbind of the
  target) follow its last preemption point inside `liftE`, so they never
  produce an error outcome; NBSendRecv's donation is in `handle_recv`, after
  the perform. Every other arm is `NE`.
* **`ckx_fl4PerformInvocation`**: every arm.
-/
import Fl4Proofs.P3.SpecInvCqHF3
open Classical

namespace Fl4Proofs.P3.SInvQ.R16
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.R14

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The triples -/

/-- No outcome is an error. -/
def NE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, ∀ y ∈ (m.run σ).1, ∀ e, y.1 ≠ .error e

/-- From a `CKC C` state, every error outcome has `CKN`. -/
def CKX (C : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, CKC C σ → ∀ y ∈ (m.run σ).1, ∀ e, y.1 = .error e → CKN y.2

theorem ne_liftE {ε α : Type} (m : NonDet (State Unit) α) : NE (NonDetE.liftE (ε := ε) m) := by
  intro σ y hy e he
  obtain ⟨x, -, rfl⟩ := ft_mem_liftE hy
  cases he

theorem ne_withoutPreemption {α : Type} (m : NonDet (State Unit) α) : NE (withoutPreemption (Z := Unit) m) :=
  ne_liftE m

theorem ne_returnOk {ε α : Type} (a : α) : NE (NonDetE.returnOk (ε := ε) (σ := State Unit) a) := by
  intro σ y hy e he
  first
    | (obtain rfl := Set.mem_singleton_iff.1 hy; cases he)
    | (dsimp only [NonDetE.returnOk] at hy; obtain rfl := Set.mem_singleton_iff.1 hy; cases he)

theorem ne_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : NE m) (hg : ∀ a, NE (g a)) : NE (m >>= g) := by
  intro σ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', he', -⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 y hy e he
  · exact hm σ z hz e' he'

theorem ne_ite {ε α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : NE m1) (h2 : NE m2) :
    NE (if P then m1 else m2) := by
  by_cases h : P
  · rw [if_pos h]; exact h1
  · rw [if_neg h]; exact h2

theorem ckx_of_ne {C : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : NE m) : CKX C m :=
  fun σ _ y hy e he => absurd he (h σ y hy e)

theorem ckx_of_ike {C : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : IKE (CKC C) m) : CKX C m :=
  fun σ hσ y hy _ _ => (h σ hσ y hy).1

theorem ckx_bind_ike {C : ObjRef} {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKE (CKC C) m) (hg : ∀ a, CKX C (g a)) : CKX C (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 (hm σ hσ z hz) y hy e he
  · exact (hm σ hσ z hz).1

theorem ckx_bind_ne {C : ObjRef} {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : CKX C m) (hg : ∀ a, NE (g a)) : CKX C (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
  · exact absurd he (hg a z.2 y hy e)
  · exact hm σ hσ z hz e' he'

/-- `CKC C` from its two halves (exception monad). -/
theorem ckc_ofE {C : ObjRef} {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : CKKE m) (h2 : CTKE C m) :
    IKE (CKC C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

/-! ## Never-erroring arms -/

macro "ne_auto" : tactic => `(tactic| repeat' (first
  | exact ne_liftE _ | exact ne_withoutPreemption _ | exact ne_returnOk _
  | (refine ne_bind ?_ (fun _ => ?_)) | (refine ne_ite _ ?_ ?_)))

theorem ne_invokeFl4Tcb (i : Fl4TcbInvocation) : NE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> simp only [invokeFl4Tcb] <;> ne_auto

theorem ne_invokeFl4IrqControl (i : Fl4IrqControlInvocation) : NE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i with
  | spec i =>
    simp only [invokeFl4IrqControl]
    cases i with
    | irqControl irq h c => simp only [invokeIrqControl]; exact ne_liftE _
    | archIRQControl a =>
      simp only [invokeIrqControl]
      cases a <;> simp only [archInvokeIrqControl] <;> exact ne_withoutPreemption _
  | _ => simp only [invokeFl4IrqControl]; exact ne_withoutPreemption _

theorem ne_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : NE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i <;> simp only [fl4ArchPerformInvocation] <;> first | exact ne_liftE _ | (unfold archPerformInvocation; exact ne_liftE _)

/-! ## The preemptible arms -/

/-- `check_cap_at` around a `CKC C`-keeping body. -/
theorem ckc_checkCapAt (C : ObjRef) (c : Cap) (sl : CslotPtr) {m : NonDet (State Unit) Unit} (h : IK (CKC C) m) :
    IK (CKC C) (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt
  exact ik_bind (by ckc_leaf) fun _ => ik_when _ h

theorem ckc_capInsert (C : ObjRef) (c : Cap) (src dst : CslotPtr) : IK (CKC C) (capInsert (Z := Unit) c src dst) := by
  ckc_leaf

/-- **`install_tcb_cap` keeps `CKC C`** (every outcome). -/
theorem ckc_installTcbCap (C target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr)) :
    IKE (CKC C) (installTcbCap (Z := Unit) target slot n so) := by
  unfold installTcbCap
  split
  · exact ike_returnOk _
  · refine ike_bind (ck_capDelete C _) fun _ => ?_
    exact ike_unlessE _ (ike_liftE (ckc_checkCapAt C _ _ (ckc_checkCapAt C _ _ (ckc_capInsert C _ _ _))))

/-- **`install_tcb_frame_cap` keeps `CKC C`** (every outcome). -/
theorem ckc_installTcbFrameCap (C target : ObjRef) (slot : CslotPtr)
    (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE (CKC C) (installTcbFrameCap (Z := Unit) target slot buf) := by
  unfold installTcbFrameCap
  split
  · exact ike_returnOk _
  · refine ike_bind (ck_capDelete C _) fun _ => ?_
    refine ike_bind (ike_liftE (by ckc_leaf)) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · split
      · exact ik_pure _
      · exact ckc_checkCapAt C _ _ (ckc_checkCapAt C _ _ (ckc_capInsert C _ _ _))
    refine ike_bind (ike_liftE (ik_gets _)) fun _ => ?_
    exact ike_liftE (ik_when _ (by ckc_leaf))

/-- **`reset_untyped_cap` keeps `CKC C`** (every outcome). -/
theorem ckc_resetUntypedCap (C : ObjRef) (sl : CslotPtr) : IKE (CKC C) (resetUntypedCap (Z := Unit) sl) :=
  ckc_ofE (ck_resetUntypedCap sl) (by ct_leaf)

theorem ckx_fl4InvokeUntyped (C : ObjRef) (i : UntypedInvocation) : CKX C (fl4InvokeUntyped (Z := Unit) i) := by
  cases i
  simp only [fl4InvokeUntyped, invokeUntypedWith]
  exact ckx_bind_ne (ckx_of_ike (ike_whenE _ (ckc_resetUntypedCap C _))) fun _ => ne_liftE _

theorem ckx_invokeTcb (C : ObjRef) (i : TcbInvocation) : CKX C (invokeTcb (Z := Unit) i) := by
  cases i
  case threadControlCaps target slot fh th cr vr buf =>
    simp only [invokeTcb]
    refine ckx_of_ike ?_
    refine ike_bind (ckc_installTcbCap C _ _ _ _) fun _ => ?_
    refine ike_bind (ckc_installTcbCap C _ _ _ _) fun _ => ?_
    refine ike_bind (ckc_installTcbCap C _ _ _ _) fun _ => ?_
    refine ike_bind (ckc_installTcbCap C _ _ _ _) fun _ => ?_
    exact ike_bind (ckc_installTcbFrameCap C _ _ _) fun _ => ike_returnOk _
  case threadControlSched target slot fh mcp prio sc =>
    simp only [invokeTcb]
    exact ckx_bind_ike (ckc_installTcbCap C _ _ _ _) fun _ => ckx_of_ne (by ne_auto)
  case notificationControl t o =>
    cases o <;> (simp only [invokeTcb]; exact ckx_of_ne (ne_liftE _))
  all_goals (simp only [invokeTcb]; exact ckx_of_ne (ne_liftE _))

theorem ckx_invokeCnode (C : ObjRef) (i : CnodeInvocation) : CKX C (invokeCnode (Z := Unit) i) := by
  cases i
  case revokeCall sl => simp only [invokeCnode]; exact ckx_of_ike (ck_capRevoke C sl)
  case deleteCall sl => simp only [invokeCnode]; exact ckx_of_ike (ck_capDelete C sl)
  case cancelBadgedSendsCall c =>
    cases c <;> (simp only [invokeCnode]; first | exact ckx_of_ne (ne_withoutPreemption _) | exact ckx_of_ne (ne_liftE _))
  all_goals (simp only [invokeCnode]; exact ckx_of_ne (ne_withoutPreemption _))

/-- **Every error outcome of `fl4_perform_invocation` from a `CKC C` state has `CKN`.** -/
theorem ckx_fl4PerformInvocation (C : ObjRef) (blk call don : Bool) (inv : Fl4Invocation) :
    CKX C (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv
  case invokeUntyped i =>
    simp only [fl4PerformInvocation]
    exact ckx_bind_ne (ckx_fl4InvokeUntyped C i) fun _ => ne_returnOk _
  case invokeTCB i => simp only [fl4PerformInvocation]; exact ckx_invokeTcb C i
  case invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact ckx_bind_ne (ckx_invokeCnode C i) fun _ => ne_returnOk _
  case invokeFl4TCB i => simp only [fl4PerformInvocation]; exact ckx_of_ne (ne_invokeFl4Tcb i)
  case invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact ckx_of_ne (ne_bind (ne_invokeFl4IrqControl i) fun _ => ne_returnOk _)
  case invokeArchObject i => simp only [fl4PerformInvocation]; exact ckx_of_ne (ne_fl4ArchPerformInvocation i)
  all_goals (simp only [fl4PerformInvocation]; exact ckx_of_ne (by ne_auto))

end

end Fl4Proofs.P3.SInvQ.R16
