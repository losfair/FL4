/-
P3 (DESIGN.md §9), invariant line G1 (ctq13): **EB across the performs**,
part 8: SchedControl configure (spec side only, outside the JAtZ cone).
SchedControl caps are rejected in the first phase, so `EB false` after it
is what is needed; at the perform there is no switch pending (`Simple`).

`invoke_sched_control_configure_flags sc …` reads the SC (bound thread `t`
if any), removes `t` from the release and ready queues, may commit time,
refills (`refill_new` / `refill_update`), then `sched_context_resume sc`
and either `reschedule_required` (`t` = ct) or `possible_switch_to t`
(`t` read runnable), and two SC field writes. Up to the resume every step
keeps `KC C h0 := EB false ∧ Simple ∧ ct = C ∧ BRs h0` (generated leaves;
ct via ScTK's NKT), so every thread bound to `sc` is still `t` (ctq8's `BP`).
* `t ≠ ct`: `AN t` (Simple), so ctq8's `rbf_schedContextResume_p` keeps
  `EB false`, then `eb_possibleSwitchTo_p` (`t` read runnable).
* `t = ct` (configuring the current thread's own SC, possibly under
  `resume_cur_thread`): `sched_context_resume` may postpone ct, breaking the
  resume clause of `HB` until the `reschedule_required` right after; `SQ4`
  and `RDq` are kept (`rdq_schedContextResume_s`: no switch pending), which
  is ctq7's `ET`, and `et_rescheduleRequired` gives `EB false`.
-/
import Fl4Proofs.P3.SpecInvCqD2
open Classical

namespace Fl4Proofs.P3.SInvQ.P13
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

set_option maxHeartbeats 1000000

/-- `sched_context_resume` for RD alone, with no switch pending. -/
theorem rdq_schedContextResume_s (sc : ObjRef) (σ : State Unit) (hT : TQ σ) (hS : Simple σ) :
    IKp RDq σ (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  revert hy
  refine ikp_gets_bind ?_ hσ y
  refine ikp_when _ fun _ => ?_
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_when _ fun hc => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  exact rdq_postpone_p sc σ hT fun _ _ t' _ _ => hS t'

/-! ## The carried facts up to the resume -/

abbrev KC (C : ObjRef) (h0 : KHeap) (s : State Unit) : Prop :=
  EB false s ∧ Simple s ∧ CTh C s ∧ SInvB.BRs h0 s

theorem kc_of {C : ObjRef} {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK false m)
    (h2 : ∀ u, IK (NSw u) m) (h3 : Sched.NKT m) (h4 : SInvB.SBK h0 m) : IK (KC C h0) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, fun u => h2 u σ (h.2.1 u) y hy, (h3 σ y hy).ct.trans h.2.2.1, h4 σ h.2.2.2 y hy⟩

theorem kc_ro {C : ObjRef} {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ σ0 : State Unit, IK (fun s => s = σ0) m) : IK (KC C h0) m := ik_of_ro h

theorem kc_refillNew (C : ObjRef) (h0 : KHeap) (p : ObjRef) (mr : Nat) (b per : Ticks) :
    IK (KC C h0) (refillNew (Z := Unit) p mr b per) :=
  kc_of (eb_of (tq_refillNew _ _ _ _) (sa_refillNew _ _ _ _) (q4_refillNew _ _ _ _) (rb_refillNew _ _ _ _))
    (fun _ => by unfold refillNew; p12_nsw_auto) (Sched.nkt_refillNew _ _ _ _) (SInvB.sb_refillNew _ _ _ _)

theorem kc_refillUpdate (C : ObjRef) (h0 : KHeap) (p : ObjRef) (np nb : Ticks) (nm : Nat) :
    IK (KC C h0) (refillUpdate (Z := Unit) p np nb nm) :=
  kc_of (eb_of (tq_refillUpdate _ _ _ _) (sa_refillUpdate _ _ _ _) (q4_refillUpdate _ _ _ _) (rb_refillUpdate _ _ _ _))
    (fun _ => by unfold refillUpdate; p12_nsw_auto) (Sched.nkt_refillUpdate _ _ _ _) (SInvB.sb_refillUpdate _ _ _ _)

theorem kc_front (C : ObjRef) (h0 : KHeap) (t sc : ObjRef) :
    IK (KC C h0) (do
      tcbReleaseRemove (Z := Unit) t
      tcbSchedAction (Z := Unit) tcbSchedDequeue t
      let curSc ← NonDet.gets fun s : State Unit => s.curSc
      NonDet.when (curSc = sc) (commitTime (Z := Unit))) :=
  kc_of (by eb_auto) (fun _ => by p12_nsw_auto)
    (Sched.nkt_bind (Sched.nkt_tcbReleaseRemove t) fun _ => Sched.nkt_bind (Sched.nkt_tcbSchedAction _ t) fun _ =>
      Sched.nkt_bind (Sched.nkt_gets _) fun _ => Sched.nkt_when _ Sched.nkt_commitTime) (by sb_auto)

/-- The configure tail: resume, reschedule or switch, the two SC field writes. -/
theorem eb_configureTail (scPtr : ObjRef) (scv : SchedContext) (badge : Badge) (flag : Data) (σ : State Unit)
    (n : Nat) (hk : σ.kheap scPtr = some (.schedContext scv n)) (s : State Unit) (k2 : KC σ.curThread σ.kheap s) :
    ∀ y ∈ ((do
      NonDet.when (scv.scTcb ≠ none) (do
        schedContextResume (Z := Unit) scPtr
        let tcbPtr ← NonDet.assertOpt scv.scTcb
        let st ← getThreadState (Z := Unit) tcbPtr
        let ct ← NonDet.gets fun s : State Unit => s.curThread
        if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
      setScObjRef (Z := Unit) scBadgeUpdate scPtr badge
      setScObjRef (Z := Unit) scSporadicUpdate scPtr (testBit flag scSporadicFlag)) s).1, EB false y.2 := by
  intro y hy
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : EB false z3.2 := by
    unfold NonDet.when at hz3
    split at hz3
    · rename_i hne
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hne
      have bp2 : BP t scPtr s := by
        refine bp_of_br (s := σ) (fun y' n' u hk' hu => ?_) k2.2.2.2
        rw [hk] at hk'; cases hk'
        rw [ht] at hu; cases hu; rfl
      obtain ⟨z4, hz4, hz3⟩ := hz3
      have c4 : z4.2.curThread = σ.curThread :=
        (Sched.nkt_schedContextResume scPtr s z4 hz4).ct.trans k2.2.2.1
      have s4 : SQ4 z4.2 := sq4_of (tq_schedContextResume scPtr) (sa_schedContextResume scPtr)
        (q4_schedContextResume scPtr) s k2.1.1 z4 hz4
      obtain ⟨a, ha, hz3⟩ := hz3
      obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
      obtain ⟨tp, a2⟩ := a
      simp only at ha1 ha2; subst a2
      rw [ht] at ha1; cases ha1
      obtain ⟨b, hb, hz3⟩ := hz3
      unfold getThreadState at hb
      obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hb
      obtain ⟨c, hc, hz3⟩ := hz3
      rw [mem_gets hc] at hz3
      dsimp only at hz3
      by_cases htc : t = σ.curThread
      · rw [if_pos (htc.trans c4.symm)] at hz3
        have r4 : RDq z4.2 := rdq_schedContextResume_s scPtr s k2.1.1.1.1 k2.2.1 k2.1.2.1.1 z4 hz4
        exact et_rescheduleRequired _ ⟨s4.1.1, s4.1.2.2.1, s4.2, r4⟩ z3 hz3
      · rw [if_neg (fun h => htc (h.trans c4))] at hz3
        have hA : AN t s := ⟨k2.2.1 t, fun _ e => htc (e.trans k2.2.2.1)⟩
        have e4 : EB false z4.2 := ⟨s4, rbf_schedContextResume_p scPtr s k2.1.1.1.1
          (fun y' n' u hk' hu => by rw [bp2 y' n' u hk' hu]; exact hA) k2.1.2 z4 hz4⟩
        split at hz3
        · rename_i hr
          exact eb_possibleSwitchTo_p t z4.2 ⟨x, hx, hr⟩ (fun h => by cases h) e4 z3 hz3
        · rw [Set.mem_singleton_iff.1 hz3]; exact e4
    · rw [Set.mem_singleton_iff.1 hz3]; exact k2.1
  refine (?_ : EBK false _) z3.2 e3 y hy
  eb_auto

/-- **SchedControl configure keeps `EB false`** (no switch pending at the perform). -/
theorem eb_schedControlConfigure (scPtr : ObjRef) (budget period : Ticks) (mr : Nat) (badge : Badge) (flag : Data)
    (σ : State Unit) (hS : Simple σ) :
    IKp (EB false) σ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags scPtr budget period mr badge flag)) := by
  intro hσ y hy
  unfold invokeSchedControlConfigureFlags at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz0
  obtain ⟨scv, z2⟩ := z0
  simp only at e hk; subst z2
  have k0 : KC σ.curThread σ.kheap σ := ⟨hσ, hS, rfl, SInvB.BR.refl _⟩
  obtain ⟨z1, hz1, hy⟩ := hy
  have k1 : KC σ.curThread σ.kheap z1.2 := by
    unfold NonDet.when at hz1
    split at hz1
    · obtain ⟨a, ha, hz1⟩ := hz1
      obtain ⟨-, ha2⟩ := cq5_mem_assertOpt ha
      rw [ha2] at hz1
      exact kc_front _ _ _ _ σ k0 z1 hz1
    · rw [Set.mem_singleton_iff.1 hz1]; exact k0
  have T := eb_configureTail scPtr scv badge flag σ n hk
  dsimp only at hy
  split at hy
  · obtain ⟨z2, hz2, hy⟩ := hy
    exact T z2.2 (kc_refillNew _ _ _ _ _ _ z1.2 k1 z2 hz2) y hy
  · obtain ⟨z2, hz2, hy⟩ := hy
    have k2 : KC σ.curThread σ.kheap z2.2 :=
      (kc_ro (fun _ => by unfold getScActive; repeat' (first | ik_step0 | ik_unfold)) : IK (KC σ.curThread σ.kheap)
        (getScActive (Z := Unit) scPtr)) z1.2 k1 z2 hz2
    dsimp only at hy
    split at hy
    · obtain ⟨z3, hz3, hy⟩ := hy
      have k3 : KC σ.curThread σ.kheap z3.2 := (kc_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) :
        IK (KC σ.curThread σ.kheap) (NonDet.assertOpt (σ := State Unit) scv.scTcb)) z2.2 k2 z3 hz3
      obtain ⟨z4, hz4, hy⟩ := hy
      have k4 : KC σ.curThread σ.kheap z4.2 := (kc_ro (fun _ => by unfold getThreadState; repeat' (first | ik_step0 | ik_unfold)) :
        IK (KC σ.curThread σ.kheap) (getThreadState (Z := Unit) z3.1)) z3.2 k3 z4 hz4
      dsimp only at hy
      split at hy
      · obtain ⟨z5, hz5, hy⟩ := hy
        exact T z5.2 (kc_refillUpdate _ _ _ _ _ _ z4.2 k4 z5 hz5) y hy
      · obtain ⟨z5, hz5, hy⟩ := hy
        exact T z5.2 (kc_refillNew _ _ _ _ _ _ z4.2 k4 z5 hz5) y hy
    · obtain ⟨z3, hz3, hy⟩ := hy
      exact T z3.2 (kc_refillNew _ _ _ _ _ _ z2.2 k2 z3 hz3) y hy

/-- **The SchedControl arm** keeps `EB false`. -/
theorem eb_perfSchedControl (bl call don : Bool) (i : SchedControlInvocation) :
    HKEr (fun σ => EB false σ ∧ Simple σ) (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedControl i)) := by
  cases i
  simp only [fl4PerformInvocation]
  refine hker_bind (R := EB false) (hker_of (hk_liftE ?_) fun _ h => h) fun _ => hker_ret _ fun _ h => h
  intro σ hσ y hy
  exact eb_schedControlConfigure _ _ _ _ _ _ σ hσ.2 hσ.1 y hy

end

end Fl4Proofs.P3.SInvQ.P13
