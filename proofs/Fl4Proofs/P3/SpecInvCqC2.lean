/-
P3 (DESIGN.md §9), invariant line G1 (ctq12): **EB across the performs**,
part 2: `suspend` (spec side only, outside the JAtZ cone).

`suspend t` keeps SA when `t` is not the switch target (`NSw t`): its
`set_thread_state t Inactive` runs after `tcb_release_remove t`, so `t` is
then neither the switch target nor released (`SAU t`). At the perform the
action is `Simple` (ctq5's EX at the entry, kept by the front and the
shell's Restart write), so `NSw t` holds for every `t`: the Suspend arm
and ReadRegisters' source suspend keep `EB k` (tq/q4/rb by ctq3 / q4 / ctq6).
-/
import Fl4Proofs.P3.SpecInvCqC1
open Classical

namespace Fl4Proofs.P3.SInvQ.P12
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000
variable {k : Bool}

/-- `t` is not the switch target. -/
abbrev NSw (t : ObjRef) (s : State Unit) : Prop := s.schedulerAction ≠ .switchThread t

theorem nsw_setCn (t : ObjRef) : IK (NSw t) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ _ e => by cases e

syntax "p12_nsw_leaf" : tactic
macro_rules | `(tactic| p12_nsw_leaf) => `(tactic| with_reducible exact nsw_setCn _)

macro "p12_nsw_auto" : tactic => `(tactic| repeat' (first | p12_nsw_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem nsw_cancelIpc (t u : ObjRef) : IK (NSw t) (cancelIpc (Z := Unit) u) := by
  unfold cancelIpc; p12_nsw_auto

theorem nsw_simple {s : State Unit} (h : Simple s) (t : ObjRef) : NSw t s := h t

abbrev SNw (t : ObjRef) (s : State Unit) : Prop := SA s ∧ NSw t s

theorem snw_of {α : Type} {t : ObjRef} {m : NonDet (State Unit) α} (h1 : SAK m) (h2 : IK (NSw t) m) :
    IK (SNw t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

/-- `tcb_release_remove t` leaves `t` released by no one: `SNw t` becomes `SAU t`. -/
theorem sau_tcbReleaseRemove (t : ObjRef) : HK1 (SNw t) (SAU t) (tcbReleaseRemove (Z := Unit) t) := by
  intro σ0 hσ0 y0 hy0
  have hsa := sa_tcbReleaseRemove t σ0 hσ0.1 y0 hy0
  unfold tcbReleaseRemove setReleaseQueue at hy0
  obtain ⟨y1, h1, hy⟩ := hy0
  rw [mem_gets h1] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : z.2.schedulerAction = σ0.schedulerAction := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]
    · rw [Set.mem_singleton_iff.1 hz]
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  rw [Set.mem_singleton_iff.1 hy] at hsa ⊢
  refine ⟨hsa, ?_, ?_⟩
  · show z.2.schedulerAction ≠ _
    rw [hz']; exact hσ0.2
  · intro hu
    have := (List.mem_filter.1 hu).2
    simp at this

/-- **`suspend t` keeps SA when `t` is not the switch target.** -/
theorem sa_suspend_p (t : ObjRef) (σ : State Unit) (hS : NSw t σ) : IKp SA σ (suspend (Z := Unit) t) := by
  have H : HK1 (SNw t) SA (suspend (Z := Unit) t) := by
    unfold suspend
    refine hk1_bind (hk1_of_ik' (snw_of (sa_cancelIpc t) (nsw_cancelIpc t t))) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (snw_of (by sa_auto) (by p12_nsw_auto))) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (snw_of (by sa_auto) (by p12_nsw_auto))) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (snw_of (sa_dequeue t) (by p12_nsw_auto))) fun _ => ?_
    refine hk1_bind (sau_tcbReleaseRemove t) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (by sau_auto)) fun _ => ?_
    exact fun σ h y hy => (sau_setThreadState t .inactive σ h y hy).1
  exact fun hσ y hy => H σ ⟨hσ, hS⟩ y hy

/-- **`suspend t` keeps `EB k`** when `t` is not the switch target. -/
theorem eb_suspend_p (t : ObjRef) (σ : State Unit) (hS : NSw t σ) : IKp (EB k) σ (suspend (Z := Unit) t) :=
  fun hσ y hy => ⟨⟨⟨tq_suspend t σ hσ.1.1.1 y hy, sa_suspend_p t σ hS hσ.1.1.2 y hy⟩,
    q4_suspend t σ hσ.1.2 y hy⟩, rb_suspend t σ hσ.2 y hy⟩

/-- The perform's scheduler precondition: `EB k` and no switch pending. -/
abbrev EBS (k : Bool) (s : State Unit) : Prop := EB k s ∧ Simple s

theorem eb_perfSuspend (bl call don : Bool) (t : ObjRef) :
    HKE (EBS k) (EB k) (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.suspend t))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hk_liftE ?_
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]
  exact eb_suspend_p t σ (hσ.2 t) hσ.1 z hz

/-- `when b (suspend t)` keeps `EB k` from `EBS k`. -/
theorem eb_whenSuspend (b : Bool) (t : ObjRef) (σ : State Unit) (hσ : EBS k σ) {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (b = true) (suspend (Z := Unit) t) σ).1) : EB k z.2 := by
  unfold NonDet.when at hz
  split at hz
  · exact eb_suspend_p t σ (hσ.2 t) hσ.1 z hz
  · rw [Set.mem_singleton_iff.1 hz]; exact hσ.1

theorem eb_perfReadRegisters (bl call don : Bool) (t : Word) (b : Bool) (n : Word) (a : ArchCopyRegisterSets) :
    HKE (EBS k) (EB k) (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.readRegisters t b n a))) := by
  simp only [fl4PerformInvocation, invokeTcb]
  refine hk_liftE ?_
  intro σ hσ y ⟨z, hz, hy⟩
  refine (?_ : EBK k _) z.2 (eb_whenSuspend b t σ hσ hz) y hy
  eb_auto

end

end Fl4Proofs.P3.SInvQ.P12
