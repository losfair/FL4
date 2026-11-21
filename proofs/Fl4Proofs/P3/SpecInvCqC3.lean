/-
P3 (DESIGN.md §9), invariant line G1 (ctq12): **EB across the performs**,
part 3: the result-sensitive triple, the deletion-cone hypotheses, and the
CNode / IRQ handler / Endpoint / Notification / Reply arms (spec side only,
outside the JAtZ cone).

* `HKEr P Q m`: every outcome has `EB false` (what the tail needs), and an
  `ok` outcome has `Q`. ReplyRecv / NBSendRecv / NBSendWait run
  `handle_recv` only after an `ok` invocation (`fl4HandleSyscall`), and only
  there is `EB true` needed; a preempted deletion / reset may have charged
  the budget (`preemption_path`, ctq8's `ebx_preemptionPath_p`: EB false).
* `DK C := EB true ∧ ct = C ∧ Simple ∧ NQ [C]`: what the deletion cone keeps.
* **Hypotheses for ctq11's deletion-cone lemmas** (named after them; to be
  discharged by ctq11, not premises of the final tops): `EbCapDeleteH`,
  `EbCapRevokeH`, `EbCapDeleteOneH`, `EbCancelBadgedSendsH` — `cap_delete`,
  `cap_revoke`, `cap_delete_one`, `cancel_badged_sends` keep `DK C` (ok
  outcomes) and give `EB false` (every outcome). Why each holds (ctq5 /
  ctq7 handoff 4): woken queue members are `≠ ct` by `NQ [ct]`; every
  `possible_switch_to` in the cone is followed by `reschedule_required`
  (so `Simple` again); `suspend` of a TCB runs with no switch pending
  (`Simple`, SpecInvCqC2's `sa_suspend_p`).
-/
import Fl4Proofs.P3.SpecInvCqC2
open Classical

namespace Fl4Proofs.P3.SInvQ.P12
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- Every outcome has `EB false`; an `ok` outcome has `Q`. -/
def HKEr (P Q : State Unit → Prop) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, P σ → ∀ y ∈ (m.run σ).1, EB false y.2 ∧ (∀ a, y.1 = .ok a → Q y.2)

theorem hker_of {P Q : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : HKE P Q m)
    (hw : ∀ s, Q s → EB false s) : HKEr P Q m :=
  fun σ hσ y hy => ⟨hw _ (h σ hσ y hy), fun _ _ => h σ hσ y hy⟩

theorem hker_bind {P R Q : State Unit → Prop} {ε α β : Type} {m : NonDetE (State Unit) ε α}
    {g : α → NonDetE (State Unit) ε β} (hm : HKEr P R m) (hg : ∀ a, HKEr R Q (g a)) : HKEr P Q (m >>= g) := by
  intro σ hσ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 ((hm σ hσ z hz).2 a ha) y hy
  · exact ⟨(hm σ hσ z hz).1, fun _ h => by cases h⟩

theorem hker_ret {Q : State Unit → Prop} {ε α : Type} (r : α) (hw : ∀ s, Q s → EB false s) :
    HKEr Q Q (NonDetE.returnOk (ε := ε) (σ := State Unit) r) := by
  intro σ hσ y hy
  first
    | (obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨hw _ hσ, fun _ _ => hσ⟩)
    | (dsimp only [NonDetE.returnOk] at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨hw _ hσ, fun _ _ => hσ⟩)

theorem hker_weak {P Q Q' : State Unit → Prop} {ε α : Type} {m : NonDetE (State Unit) ε α} (h : HKEr P Q m)
    (hq : ∀ s, Q s → Q' s) : HKEr P Q' m :=
  fun σ hσ y hy => ⟨(h σ hσ y hy).1, fun a ha => hq _ ((h σ hσ y hy).2 a ha)⟩

/-- What the deletion cone keeps. -/
abbrev DK (C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ Simple s ∧ NQ [C] s

theorem dk_eb {C : ObjRef} {s : State Unit} (h : DK C s) : EB false s := eb_weak h.1

theorem dk_of {α : Type} {C : ObjRef} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : CTK C m)
    (h3 : ∀ t, IK (NSw t) m) (h4 : NQK [C] m) : IK (DK C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, fun t => h3 t σ (h.2.2.1 t) y hy, h4 σ h.2.2.2 y hy⟩

macro "p12_dk_auto" : tactic => `(tactic| (refine dk_of ?_ ?_ (fun _ => ?_) ?_; (eb_auto; done); (ct_auto; done); (p12_nsw_auto; done); (nq2_auto; done)))

/-! ## The deletion-cone hypotheses (ctq11) -/

/-- **Hypothesis for ctq11's `cap_delete` lemma.** -/
def EbCapDeleteH : Prop := ∀ (C : ObjRef) (slot : CslotPtr), HKEr (DK C) (DK C) (capDelete (Z := Unit) slot)

/-- **Hypothesis for ctq11's `cap_revoke` lemma.** -/
def EbCapRevokeH : Prop := ∀ (C : ObjRef) (slot : CslotPtr), HKEr (DK C) (DK C) (capRevoke (Z := Unit) slot)

/-- **Hypothesis for ctq11's `cap_delete_one` lemma** (IRQ handler set / clear). -/
def EbCapDeleteOneH : Prop := ∀ (C : ObjRef) (slot : CslotPtr), HK (DK C) (DK C) (capDeleteOne (Z := Unit) slot)

/-- **Hypothesis for ctq11's `cancel_badged_sends` lemma.** -/
def EbCancelBadgedSendsH : Prop :=
  ∀ (C : ObjRef) (ep : ObjRef) (b : Badge), HK (DK C) (DK C) (cancelBadgedSends (Z := Unit) ep b)

/-! ## CNode -/

theorem dk_invokeCnode (hD : EbCapDeleteH) (hR : EbCapRevokeH) (hB : EbCancelBadgedSendsH) (C : ObjRef)
    (i : CnodeInvocation) : HKEr (DK C) (DK C) (invokeCnode (Z := Unit) i) := by
  cases i
  case revokeCall s => exact hR C s
  case deleteCall s => exact hD C s
  case cancelBadgedSendsCall cap =>
    cases cap
    case endpointCap ep b r =>
      simp only [invokeCnode, withoutPreemption]
      refine hker_of (hk_liftE ?_) fun _ => dk_eb
      intro σ hσ y hy
      unfold NonDet.when at hy
      split at hy
      · exact hB C ep b σ hσ y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hσ
    all_goals
      simp only [invokeCnode]
      refine hker_of (hk_liftE ?_) fun _ => dk_eb
      intro σ _ y hy
      exact absurd hy (by simp [NonDet.fail])
  all_goals
    refine hker_of (fun σ hσ y hy => dk_of ?_ (ct_invokeCnode _) (fun _ => ?_) (nq_invokeCnode _) σ hσ y hy)
      fun _ => dk_eb
    · simp only [invokeCnode, withoutPreemption]
      eb_auto
    · simp only [invokeCnode, withoutPreemption]
      p12_nsw_auto

theorem eb_perfCnode (hD : EbCapDeleteH) (hR : EbCapRevokeH) (hB : EbCancelBadgedSendsH) (C : ObjRef)
    (bl call don : Bool) (i : CnodeInvocation) :
    HKEr (DK C) (DK C) (fl4PerformInvocation (Z := Unit) bl call don (.invokeCNode i)) := by
  simp only [fl4PerformInvocation]
  exact hker_bind (dk_invokeCnode hD hR hB C i) fun _ => hker_ret _ fun _ => dk_eb

/-! ## IRQ handler -/

theorem dk_invokeIrqHandler (hO : EbCapDeleteOneH) (C : ObjRef) (i : IrqHandlerInvocation) :
    HK (DK C) (DK C) (invokeIrqHandler (Z := Unit) i) := by
  cases i
  case aCKIrq irq =>
    refine fun σ hσ y hy => dk_of ?_ (ct_invokeIrqHandler _) (fun _ => ?_) (nq_invokeIrqHandler _) σ hσ y hy
    · simp only [invokeIrqHandler]
      eb_auto
    · simp only [invokeIrqHandler]
      p12_nsw_auto
  case setIRQHandler irq cap slot =>
    simp only [invokeIrqHandler]
    intro σ hσ y ⟨z1, h1, z2, h2, hy⟩
    rw [mem_gets h1] at h2 hy
    have hz2 := hO C _ σ hσ z2 h2
    refine dk_of ?_ (ct_capInsert _ _ _) (fun _ => ?_) (nq_capInsert _ _ _) z2.2 hz2 y hy
    · eb_auto
    · p12_nsw_auto
  case clearIRQHandler irq =>
    simp only [invokeIrqHandler]
    intro σ hσ y ⟨z1, h1, hy⟩
    rw [mem_gets h1] at hy
    exact hO C _ σ hσ y hy

theorem eb_perfIrqHandler (hO : EbCapDeleteOneH) (C : ObjRef) (bl call don : Bool) (i : IrqHandlerInvocation) :
    HKEr (DK C) (DK C) (fl4PerformInvocation (Z := Unit) bl call don (.invokeIRQHandler i)) := by
  simp only [fl4PerformInvocation]
  exact hker_bind (hker_of (hk_liftE (dk_invokeIrqHandler hO C i)) fun _ => dk_eb) fun _ =>
    hker_ret _ fun _ => dk_eb

/-! ## Endpoint, Notification, Reply -/

/-- The perform's precondition (beyond `DK`): ScInv (sb2), the current
thread runnable (the shell's Restart write), the idle thread in its idle
state (ValidIdle). -/
abbrev PE (C : ObjRef) (s : State Unit) : Prop :=
  DK C s ∧ SInvB.ScInv s ∧ RnH C s.kheap ∧ (∀ x, s.kheap s.idleThread = some (.tcb x) → x.tcbState = .idleThreadState)

theorem eb_perfEndpoint (C : ObjRef) (bl call don : Bool) (ep : ObjRef) (bd : Badge) (g gr : Bool) :
    HKE (PE C) (EB true) (fl4PerformInvocation (Z := Unit) bl call don (.invokeEndpoint ep bd g gr)) := by
  simp only [fl4PerformInvocation, withoutPreemption]
  refine hk_liftE ?_
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  have hc : σ.curThread ∈ [C] := by rw [hσ.1.2.1]; exact List.mem_singleton_self _
  exact eb_sendIpc_q bl call bd g gr don σ.curThread ep σ (npq_ct hσ.1.1) (qe_of_nq hσ.1.2.2.2 hc) hσ.1.1 y2 h2

theorem eb_perfNtfn (C : ObjRef) (bl call don : Bool) (n : ObjRef) (bd : Badge) :
    HKEr (PE C) (EB true) (fl4PerformInvocation (Z := Unit) bl call don (.invokeNotification n bd)) := by
  simp only [fl4PerformInvocation, withoutPreemption]
  refine hker_bind (R := EB true) (hker_of (hk_liftE ?_) fun _ => eb_weak) fun _ => hker_ret _ fun _ => eb_weak
  intro σ hσ y hy
  have hR : RnH σ.curThread σ.kheap := by rw [hσ.1.2.1]; exact hσ.2.2.1
  exact eb_sendSignal_p n bd σ hσ.1.2.2.2.1.1 hσ.2.2.2 (fun _ => hR) hσ.1.1 y hy

theorem eb_perfReply (C : ObjRef) (bl call don : Bool) (r : ObjRef) (g : Bool) :
    HKE (PE C) (EB true) (fl4PerformInvocation (Z := Unit) bl call don (.invokeReply r g)) := by
  simp only [fl4PerformInvocation]
  refine hk_liftE ?_
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  have hR : RnH σ.curThread σ.kheap := by rw [hσ.1.2.1]; exact hσ.2.2.1
  have hN : NQ [σ.curThread] σ := by rw [hσ.1.2.1]; exact hσ.1.2.2.2
  exact eb_doReplyTransfer_ct σ.curThread r g σ hσ.1.1 hN hσ.2.1 hR y2 h2

end

end Fl4Proofs.P3.SInvQ.P12
