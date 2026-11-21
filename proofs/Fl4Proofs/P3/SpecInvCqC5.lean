/-
P3 (DESIGN.md §9), invariant line G1 (ctq12): **EB across the performs**,
part 5: `set_priority`, `set_domain` and the Domain arm (spec side only,
outside the JAtZ cone).

These run only with `firstPhase = false` (thread / domain caps are rejected
in the first phase of ReplyRecv / NBSendRecv), so after them only `EB false`
is needed. `set_priority t` / `set_domain t` may enqueue the current thread
(Restart during the perform) under `resume_cur_thread`, which breaks
`CtNQR` until the `reschedule_required` right after it; that one ends at
`choose_new_thread` with heap and release queue unchanged, so `RR` before
gives `SA` after (`sa_rescheduleRequired_rr`), as `RDq` before gives
`RBk false` after (ctq6's `rq_rescheduleRequired`). The enqueued thread is
not released: read from a ready queue (RDq), the current thread (`NP ct`
from `EB true` at the perform), or `schedulable`.
-/
import Fl4Proofs.P3.SpecInvCqC4
import Fl4Proofs.P3.SpecInvQDom
open Classical

namespace Fl4Proofs.P3.SInvQ.P12
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ
open Fl4Proofs.P3.SInvDom (DomInvOK)

noncomputable section

set_option maxHeartbeats 1000000

/-- **`reschedule_required` from `RR` alone** gives `SA`: it ends at
`choose_new_thread` (RA, CtNQR vacuous) with heap and release queue unchanged. -/
theorem sa_rescheduleRequired_rr : HK1 RR SA (rescheduleRequired (Z := Unit)) :=
  fun σ h y hy => (rr_rescheduleRequired σ h y hy).1

/-! ## `set_priority` -/

/-- **`set_priority` keeps SA** (no premise). -/
theorem sa_setPriority (t : ObjRef) (prio : Priority) : SAK (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState threadSetPriority getTcbQueue
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨w, hw, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    dsimp only at hy
    split at hy
    · obtain ⟨z1, hz1, hy⟩ := hy
      have h1 := sa_dequeue t σ hσ z1 hz1
      obtain ⟨z2, hz2, hy⟩ := hy
      have h2 := sa_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ h => h) z1.2 h1 z2 hz2
      obtain ⟨z3, hz3, hy⟩ := hy
      have h3 : RR z3.2 := by obtain ⟨_, -, e⟩ := q1_tsa_out hz3; rw [e]; exact h2.2.1
      exact sa_rescheduleRequired_rr _ h3 y hy
    · exact sa_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ h => h) σ hσ y hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    have h1 := sa_threadSet (fun tcb => { tcb with tcbPriority := prio }) t (fun _ h => h) σ hσ z1 hz1
    refine (?_ : SAK _) z1.2 h1 y hy
    sa_auto

/-- **`set_priority t` keeps `RBk false`** when `t`, if current, is not released. -/
theorem rb_setPriority_p (t : ObjRef) (prio : Priority) (σ : State Unit)
    (hc : t = σ.curThread → t ∉ σ.releaseQueue) : IKp (RBk false) σ (setPriority (Z := Unit) t prio) := by
  unfold setPriority getThreadState threadSetPriority getTcbQueue
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x1, hx1, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz
    obtain ⟨z, ⟨w, hw, hz⟩, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨w, hw, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw
    dsimp only at hy
    split at hy
    · rename_i hq
      have hrel : t ∉ σ.releaseQueue := by
        rcases hq with hq | hq
        · exact hσ.1.1.1 _ _ t hq
        · exact hc hq
      obtain ⟨z1, hz1, hy⟩ := hy
      have h1 := rb_dequeue (k := false) t σ hσ z1 hz1
      have e1 : z1.2.releaseQueue = σ.releaseQueue := by
        obtain ⟨_, -, e⟩ := q1_tsa_out hz1; rw [e]
      obtain ⟨z2, hz2, hy⟩ := hy
      have h2 := rb_threadSetPriority (k := false) t prio z1.2 h1 z2 hz2
      have e2 : z2.2.releaseQueue = σ.releaseQueue := by
        obtain ⟨_, -, e⟩ := SInv.mem_threadSet hz2; rw [e, e1]
      obtain ⟨z3, hz3, hy⟩ := hy
      have h3 := rbe_enq (k := false) _ t (q1_enq t) z2.2 ⟨⟨h2.1, by rw [e2]; exact hrel, fun h => by cases h⟩, h2.2⟩
        z3 hz3
      exact rq_rescheduleRequired _ h3.1.1.1 y hy
    · exact rb_threadSetPriority (k := false) t prio σ hσ y hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    have h1 := rb_threadSetPriority (k := false) t prio σ hσ z1 hz1
    refine (?_ : RBK false _) z1.2 h1 y hy
    rb_auto

/-- **`set_priority t` keeps `EB false`** when `t`, if current, is not released
(at the perform: `NP ct` from `EB true`). -/
theorem eb_setPriority_p (t : ObjRef) (prio : Priority) (σ : State Unit)
    (hc : t = σ.curThread → t ∉ σ.releaseQueue) : IKp (EB false) σ (setPriority (Z := Unit) t prio) :=
  fun hσ y hy => ⟨⟨⟨tq_setPriority t prio σ hσ.1.1.1 y hy, sa_setPriority t prio σ hσ.1.1.2 y hy⟩,
    q4_setPriority t prio σ hσ.1.2 y hy⟩, rb_setPriority_p t prio σ hc hσ.2 y hy⟩

theorem eb_setPriority_t (t : ObjRef) (prio : Priority) (σ : State Unit) (hσ : EB true σ) {y : Unit × State Unit}
    (hy : y ∈ (setPriority (Z := Unit) t prio σ).1) : EB false y.2 :=
  eb_setPriority_p t prio σ (fun e => by rw [e]; exact (npq_ct hσ).1.2) (eb_weak hσ) y hy

/-! ## `set_domain` -/

theorem sa_setDomain (t : ObjRef) (dom : Domain) : SAK (setDomain (Z := Unit) t dom) := by
  unfold setDomain threadSetDomain
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z1, hz1, hy⟩
  have h1 := sa_dequeue t σ hσ z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have h2 := sa_threadSet (fun tcb => { tcb with tcbDomain := dom }) t (fun _ h => h) z1.2 h1 z2 hz2
  have hc2 : z2.2.curThread = σ.curThread := by
    obtain ⟨_, -, e1⟩ := q1_tsa_out hz1
    obtain ⟨_, -, e2⟩ := SInv.mem_threadSet hz2
    rw [e2, e1]
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have h4 : RR z4.2 ∧ (t ≠ σ.curThread → SA z4.2) := by
    unfold NonDet.when at hz4
    split at hz4
    · refine ⟨by obtain ⟨_, -, e⟩ := q1_tsa_out hz4; rw [e]; exact h2.2.1, fun hn => ?_⟩
      exact sa_enq_p _ t z2.2 (q1_enq t) (Or.inr (by rw [hc2]; exact hn)) h2 z4 hz4
    · obtain rfl := Set.mem_singleton_iff.1 hz4; exact ⟨h2.2.1, fun _ => h2⟩
  unfold NonDet.when at hy
  split at hy
  · exact sa_rescheduleRequired_rr _ h4.1 y hy
  · rename_i hn
    obtain rfl := Set.mem_singleton_iff.1 hy; exact h4.2 hn

theorem rb_setDomain (t : ObjRef) (dom : Domain) : RBK false (setDomain (Z := Unit) t dom) := by
  unfold setDomain threadSetDomain
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z1, hz1, hy⟩
  have h1 := rb_dequeue (k := false) t σ hσ z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have h2 := rb_threadSetDomain (k := false) t dom z1.2 h1 z2 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have h4 : RBk false z4.2 := by
    unfold NonDet.when at hz4
    split at hz4
    · rename_i hs
      have hrel : t ∉ z2.2.releaseQueue := by
        unfold schedulable at hs
        exact (of_decide_eq_true hs).2.2
      have h := rbe_enq (k := false) _ t (q1_enq t) z2.2 ⟨⟨h2.1, hrel, fun h => by cases h⟩, h2.2⟩ z4 hz4
      exact ⟨h.1.1, h.2⟩
    · obtain rfl := Set.mem_singleton_iff.1 hz4; exact h2
  unfold NonDet.when at hy
  split at hy
  · exact rb_rescheduleRequired _ h4 y hy
  · obtain rfl := Set.mem_singleton_iff.1 hy; exact h4

theorem tq_invokeDomain' (i : DomainInvocation) : TQK (invokeDomain (Z := Unit) i) := by
  cases i
  case invokeDomainSet t d => exact tq_invokeSetDomain t d
  case invokeDomainScheduleSetStart n =>
    unfold invokeDomain domainSetStart
    repeat' (first | (with_reducible exact tq_rescheduleRequired) | (exact ik_modify fun _ h => h) | ik_step0 | ik_unfold)
  case invokeDomainScheduleConfigure n d u => exact tq_domainScheduleConfigure _ _ _

theorem sa_invokeDomain' (i : DomainInvocation) : SAK (invokeDomain (Z := Unit) i) := by
  cases i
  case invokeDomainSet t d =>
    unfold invokeDomain invokeSetDomain
    exact ik_bind (by sa_auto) fun _ => sa_setDomain t d
  case invokeDomainScheduleSetStart n =>
    unfold invokeDomain domainSetStart
    repeat' (first | (with_reducible exact sa_rescheduleRequired') | (exact ik_modify fun _ h => h) | ik_step0 | ik_unfold)
  case invokeDomainScheduleConfigure n d u => exact sa_domainScheduleConfigure _ _ _

theorem rb_invokeDomain' (i : DomainInvocation) : RBK false (invokeDomain (Z := Unit) i) := by
  cases i
  case invokeDomainSet t d =>
    unfold invokeDomain invokeSetDomain
    exact ik_bind (by rb_auto) fun _ => rb_setDomain t d
  case invokeDomainScheduleSetStart n =>
    unfold invokeDomain domainSetStart
    repeat' (first | (with_reducible exact rb_rescheduleRequired) | (exact ik_modify fun _ h => h) | ik_step0 | ik_unfold)
  case invokeDomainScheduleConfigure n d u => exact rb_domainScheduleConfigure _ _ _

/-- **`invoke_domain` keeps `EB false`**, from the decode's checks
(`DomInvOK`, `SetDom0`: SpecInvQDom's T4 premises). -/
theorem eb_invokeDomain (i : DomainInvocation) (σ : State Unit) (hi : DomInvOK σ (.invokeDomain i))
    (h0 : SetDom0 (.invokeDomain i)) : IKp (EB false) σ (invokeDomain (Z := Unit) i) :=
  fun hσ y hy => ⟨⟨⟨tq_invokeDomain' i σ hσ.1.1.1 y hy, sa_invokeDomain' i σ hσ.1.1.2 y hy⟩,
    q4_invokeDomain i σ hi h0 hσ.1.2 y hy⟩, rb_invokeDomain' i σ hσ.2 y hy⟩

/-- **The Domain arm** keeps `EB false` (decode facts `DomInvOK`, `SetDom0`). -/
theorem eb_perfDomain (bl call don : Bool) (i : DomainInvocation) (h0 : SetDom0 (.invokeDomain i)) :
    HKE (fun σ => EB false σ ∧ DomInvOK σ (.invokeDomain i)) (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeDomain i)) := by
  simp only [fl4PerformInvocation]
  refine hk_liftE ?_
  intro σ hσ y ⟨z, hz, hy⟩
  rw [Set.mem_singleton_iff.1 hy]
  exact eb_invokeDomain i σ hσ.2 h0 hσ.1 z hz

end

end Fl4Proofs.P3.SInvQ.P12
