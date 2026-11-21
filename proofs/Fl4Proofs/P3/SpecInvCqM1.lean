/-
P3 (DESIGN.md §9), invariant line G1 (ctq15): **EB across the performs**,
part 9: SC YieldTo (spec side only, outside the JAtZ cone). SchedContext caps
are rejected in the first phase, so `EB false` after it is what is needed.

`sched_context_yield_to sc`:
* `complete_yield_to` of the SC's yield-from thread (if any) keeps `EB true`
  (generated leaves), no switch pending (`Simple`), the current thread `C`,
  sb2's binding frame `BRs` and "`C` is a runnable TCB": the reply of the
  consumed time writes user memory and registers, so ScTK's `NKT` does not
  apply; sch11's `KF C` (MidRun: the current thread and `C`'s state and
  fault kept) does (`KY`).
* `sched_context_resume sc` keeps `EB true` by ctq7's `rb_schedContextResume_p`
  with `k = true`: the SC's bound thread `u` is not the current thread (the
  decode's check `sc_tcb ≠ some ct`, carried as `YT sc` along `BRs`) and not
  the switch target (`Simple`).
* `u` read `schedulable`: if its priority is below ct's, dequeue + enqueue of
  `u` (`u ≠ ct`, `u` runnable and not released) gives `EB false`; otherwise
  ct's `tcbYieldTo` and the SC's `yieldFrom` are written, `u` is dequeued, ct
  and `u` are enqueued (ctq7's `ET`: both runnable and not released, ct by
  `NP ct` of `EB true`), and `reschedule_required` gives `EB false`
  (`et_rescheduleRequired`). `return_consumed` by `eb_auto`.
-/
import Fl4Proofs.P3.SpecInvCqD3
import Fl4Proofs.P3.XTopJointMidRunK
open Classical

namespace Fl4Proofs.P3.SInvQ.P15
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Frames -/

/-- The decode's check `sc_tcb ≠ some ct` (decode_sched_context_yield_to). -/
abbrev YT (C sc : ObjRef) (k : ObjRef → Option KernelObject) : Prop :=
  ∀ y n u, k sc = some (.schedContext y n) → y.scTcb = some u → u ≠ C

theorem yt_of_br {C sc : ObjRef} {k k' : KHeap} (h : YT C sc k) (hb : SInvB.BR k k') : YT C sc k' := by
  intro y' n' u hk hu
  obtain ⟨y, n, hy⟩ := hb.sc' sc y' n' hk
  obtain ⟨y2, n2, hy2, hkp⟩ := hb.sc sc y n hy
  rw [hk] at hy2; cases hy2
  exact h y n u hy (by rw [← hkp.1]; exact hu)

/-- `t`'s state kept (sch11's `tsV`) keeps "`t` is a runnable TCB". -/
theorem rnH_tsV {k k' : ObjRef → Option KernelObject} {t : ObjRef}
    (e : MidRun.tsV (k' t) = MidRun.tsV (k t)) (h : RnH t k) : RnH t k' := by
  obtain ⟨x, hx, hr⟩ := h
  rw [hx] at e
  cases h' : k' t with
  | none => rw [h'] at e; simp [MidRun.tsV] at e
  | some o =>
    rw [h'] at e
    cases o <;> simp [MidRun.tsV] at e
    exact ⟨_, h', by rw [e.1]; exact hr⟩

theorem rnH_kf {t : ObjRef} {σ σ' : State Unit} (e : MidRun.ctV t σ' = MidRun.ctV t σ) (h : RnH t σ.kheap) :
    RnH t σ'.kheap := by
  unfold MidRun.ctV at e
  exact rnH_tsV (Prod.mk.inj e).2 h

theorem ct_kf {t : ObjRef} {σ σ' : State Unit} (e : MidRun.ctV t σ' = MidRun.ctV t σ) :
    σ'.curThread = σ.curThread := by
  unfold MidRun.ctV at e
  exact (Prod.mk.inj e).1

theorem rq_threadSet (R : List ObjRef) (f : Tcb → Tcb) (t : ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | ik_step0 | ik_unfold)

theorem rq_updateSchedContext (R : List ObjRef) (p : ObjRef) (f : SchedContext → SchedContext) :
    IK (fun s : State Unit => s.releaseQueue = R) (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext; repeat' (first | ik_step0 | ik_unfold)

/-! ## Up to the resume -/

/-- The carried facts up to `sched_context_resume`. -/
abbrev KY (C : ObjRef) (h0 : KHeap) (s : State Unit) : Prop :=
  EB true s ∧ Simple s ∧ CTh C s ∧ SInvB.BRs h0 s ∧ RnH C s.kheap

theorem ky_of {C : ObjRef} {h0 : KHeap} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK true m)
    (h2 : ∀ u, IK (NSw u) m) (h3 : MidRun.KF C m) (h4 : SInvB.SBK h0 m) : IK (KY C h0) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, fun u => h2 u σ (h.2.1 u) y hy, (ct_kf (h3 σ y hy)).trans h.2.2.1,
    h4 σ h.2.2.2.1 y hy, rnH_kf (h3 σ y hy) h.2.2.2.2⟩

theorem nsw_completeYieldTo (u t : ObjRef) : IK (NSw u) (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; p12_nsw_auto

theorem ky_completeYieldTo (C : ObjRef) (h0 : KHeap) (t : ObjRef) : IK (KY C h0) (completeYieldTo (Z := Unit) t) :=
  ky_of (eb_of (tq_completeYieldTo t) (sa_completeYieldTo t) (q4_completeYieldTo t) (rb_completeYieldTo t))
    (fun u => nsw_completeYieldTo u t) (MidRun.kf_completeYieldTo' t) (SInvB.sb_completeYieldTo t)

/-- The yield-from part. -/
theorem ky_yieldFrom (C : ObjRef) (h0 : KHeap) (sc : ObjRef) (o : Option ObjRef) :
    IK (KY C h0) (NonDet.when (o ≠ none) (do
      completeYieldTo (Z := Unit) (the o)
      let scYfOpt ← getScObjRef (Z := Unit) SchedContext.scYieldFrom sc
      NonDet.assert (scYfOpt = none))) := by
  unfold NonDet.when
  split
  · refine ik_bind (ky_completeYieldTo C h0 _) fun _ => ?_
    exact ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold)
  · exact ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold)

/-! ## The second arm: ct's yield-to, both enqueues, the reschedule -/

/-- Facts about the SC's thread `u` and the current thread `C` along the second arm. -/
abbrev UF (C u : ObjRef) (s : State Unit) : Prop :=
  s.curThread = C ∧ RnH C s.kheap ∧ RnH u s.kheap ∧ u ∉ s.releaseQueue

theorem uf_tsa {C u : ObjRef} (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) {s : State Unit}
    {w : Unit × State Unit} (hw : w ∈ (tcbSchedAction (Z := Unit) act t s).1) (h : UF C u s) : UF C u w.2 := by
  obtain ⟨_, -, e⟩ := q1_tsa_out hw
  rw [e]; exact h

theorem uf_threadSet {C u : ObjRef} (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault) {s : State Unit}
    {w : Unit × State Unit} (hw : w ∈ (threadSet (Z := Unit) f t s).1) (h : UF C u s) : UF C u w.2 := by
  have e1 := MidRun.kf_threadSet (ct := C) f t hf s w hw
  have e2 := MidRun.kf_threadSet (ct := u) f t hf s w hw
  have e3 := rq_threadSet s.releaseQueue f t s rfl w hw
  exact ⟨(ct_kf e1).trans h.1, rnH_kf e1 h.2.1, rnH_kf e2 h.2.2.1, by rw [e3]; exact h.2.2.2⟩

theorem uf_updateSchedContext {C u : ObjRef} (p : ObjRef) (f : SchedContext → SchedContext) {s : State Unit}
    {w : Unit × State Unit} (hw : w ∈ (updateSchedContext (Z := Unit) p f s).1) (h : UF C u s) : UF C u w.2 := by
  have e1 := MidRun.kf_updateSchedContext' (ct := C) p f s w hw
  have e2 := MidRun.kf_updateSchedContext' (ct := u) p f s w hw
  have e3 := rq_updateSchedContext s.releaseQueue p f s rfl w hw
  exact ⟨(ct_kf e1).trans h.1, rnH_kf e1 h.2.1, rnH_kf e2 h.2.2.1, by rw [e3]; exact h.2.2.2⟩

/-- An enqueue of a runnable, unreleased thread keeps `ET`. -/
theorem et_enq (t : ObjRef) (s : State Unit) (hr : RnH t s.kheap) (hq : t ∉ s.releaseQueue) (h : ET s) :
    ∀ w ∈ (tcbSchedAction (Z := Unit) tcbSchedEnqueue t s).1, ET w.2 := by
  intro w hw
  refine ⟨tq_enq_p _ t s (q1_enq t) hr h.1 w hw, ?_, q4_tcbSchedAction _ t s h.2.2.1 w hw,
    (rde_enq _ t (q1_enq t) s ⟨h.2.2.2, hq⟩ w hw).1⟩
  obtain ⟨_, -, e⟩ := q1_tsa_out hw
  rw [e]; exact h.2.1

theorem eb_yieldToSecond (sc u : ObjRef) (s : State Unit) (C : ObjRef) (hE : EB true s) (hU : UF C u s) :
    ∀ y ∈ ((do
      setTcbObjRef (Z := Unit) tcbYieldToUpdate C (some sc)
      setScObjRef (Z := Unit) scYieldFromUpdate sc (some C)
      tcbSchedAction (Z := Unit) tcbSchedDequeue u
      tcbSchedAction (Z := Unit) tcbSchedEnqueue C
      tcbSchedAction (Z := Unit) tcbSchedEnqueue u
      rescheduleRequired (Z := Unit)
      pure false : SMonad Unit Bool) s).1, EB false y.2 := by
  intro y hy
  obtain ⟨w1, hw1, hy⟩ := hy
  have e1 : EB true w1.2 := eb_threadSet (tcbYieldToUpdate fun _ => some sc) C (fun _ => ⟨rfl, rfl, rfl⟩)
    (fun _ h => h) s hE w1 hw1
  have u1 : UF C u w1.2 := uf_threadSet (tcbYieldToUpdate fun _ => some sc) C (fun _ => ⟨rfl, rfl⟩) hw1 hU
  obtain ⟨w2, hw2, hy⟩ := hy
  have e2 : EB true w2.2 := eb_of (tq_updateSchedContext _ _) (sa_updateSchedContext _ _)
    (q4_updateSchedContext _ _) (rb_updateSchedContext _ _) w1.2 e1 w2 hw2
  have u2 : UF C u w2.2 := uf_updateSchedContext _ _ hw2 u1
  obtain ⟨w3, hw3, hy⟩ := hy
  have e3 : EB true w3.2 := eb_of (tq_dequeue u) (sa_dequeue u) (q4_tcbSchedAction _ u) (rb_dequeue u) w2.2 e2 w3 hw3
  have u3 : UF C u w3.2 := uf_tsa _ u hw3 u2
  obtain ⟨w4, hw4, hy⟩ := hy
  have hq3 : C ∉ w3.2.releaseQueue := by rw [← u3.1]; exact (e3.2.1.2.1 rfl).2.2
  have t4 : ET w4.2 := et_enq C w3.2 u3.2.1 hq3 (et_of_eb e3) w4 hw4
  have u4 : UF C u w4.2 := uf_tsa _ C hw4 u3
  obtain ⟨w5, hw5, hy⟩ := hy
  have t5 : ET w5.2 := et_enq u w4.2 u4.2.2.1 u4.2.2.2 t4 w5 hw5
  obtain ⟨w6, hw6, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  exact et_rescheduleRequired w5.2 t5 w6 hw6

/-! ## `sched_context_yield_to` -/

/-- **`sched_context_yield_to sc` takes `EB true` to `EB false`** when no
switch is pending, the current thread is a runnable TCB, and the SC's bound
thread is not the current thread (the decode's check). -/
theorem eb_schedContextYieldTo (sc : ObjRef) (σ : State Unit) (hS : Simple σ) (hR : RnH σ.curThread σ.kheap)
    (hY : YT σ.curThread sc σ.kheap) (hσ : EB true σ) :
    ∀ y ∈ (schedContextYieldTo (Z := Unit) sc σ).1, EB false y.2 := by
  intro y hy
  unfold schedContextYieldTo at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain ⟨e0, -⟩ := cq5_mem_getScObjRef hz0
  have k0 : KY σ.curThread σ.kheap z0.2 := by
    rw [e0]; exact ⟨hσ, hS, rfl, SInvB.BR.refl _, hR⟩
  obtain ⟨z1, hz1, hy⟩ := hy
  have k1 : KY σ.curThread σ.kheap z1.2 := ky_yieldFrom σ.curThread σ.kheap sc z0.1 z0.2 k0 z1 hz1
  have y1 : YT σ.curThread sc z1.2.kheap := yt_of_br hY k1.2.2.2.1
  obtain ⟨z2, hz2, hy⟩ := hy
  have e2 : EB true z2.2 := by
    refine ⟨sq4_of (tq_schedContextResume sc) (sa_schedContextResume sc) (q4_schedContextResume sc) z1.2
      k1.1.1 z2 hz2, ?_⟩
    refine rb_schedContextResume_p (k := true) sc z1.2 k1.1.1.1.1 (fun y' n' u hk hu => ?_) k1.1.2 z2 hz2
    have hne : u ≠ z1.2.curThread := fun e => y1 y' n' u hk hu (e.trans k1.2.2.1)
    exact ⟨⟨k1.2.1 u, fun _ => hne⟩, fun _ => hne⟩
  have ef2 := MidRun.kf_schedContextResume' (ct := σ.curThread) sc z1.2 z2 hz2
  have c2 : z2.2.curThread = σ.curThread := (ct_kf ef2).trans k1.2.2.1
  have r2 : RnH σ.curThread z2.2.kheap := rnH_kf ef2 k1.2.2.2.2
  have y2 : YT σ.curThread sc z2.2.kheap :=
    yt_of_br hY (SInvB.sb_schedContextResume (h0 := σ.kheap) sc z1.2 k1.2.2.2.1 z2 hz2)
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : EB false z3.2 := by
    obtain ⟨a, ha, hz3⟩ := hz3
    obtain ⟨ea, scv, n, hk, hv⟩ := cq5_mem_getScObjRef ha
    obtain ⟨a1, a2⟩ := a
    simp only at ea hv; subst ea
    obtain ⟨b, hb, hz3⟩ := hz3
    obtain ⟨hb1, hb2⟩ := cq5_mem_assertOpt hb
    obtain ⟨u, b2⟩ := b
    simp only at hb1 hb2; subst hb2
    have hu : u ≠ σ.curThread := y2 scv n u hk (by rw [← hv]; exact hb1)
    obtain ⟨c, hc, hz3⟩ := hz3
    rw [mem_gets hc] at hz3
    dsimp only at hz3
    split at hz3
    · rename_i hs
      have hrq : u ∉ z2.2.releaseQueue := by
        have hs' := hs
        unfold schedulable at hs'
        exact (of_decide_eq_true hs').2.2
      obtain ⟨d, hd, hz3⟩ := hz3
      rw [mem_gets hd] at hz3
      dsimp only at hz3
      obtain ⟨p1, hp1, hz3⟩ := hz3
      obtain ⟨x1, -, rfl⟩ := q1_mem_threadGet hp1
      obtain ⟨p2, hp2, hz3⟩ := hz3
      obtain ⟨x2, -, rfl⟩ := q1_mem_threadGet hp2
      dsimp only at hz3
      split at hz3
      · obtain ⟨w1, hw1, hz3⟩ := hz3
        have e4 : EB true w1.2 :=
          eb_of (tq_dequeue u) (sa_dequeue u) (q4_tcbSchedAction _ u) (rb_dequeue u) z2.2 e2 w1 hw1
        have u4 : UF σ.curThread u w1.2 := uf_tsa _ u hw1 ⟨c2, r2, schedulable_rn hs, hrq⟩
        obtain ⟨w2, hw2, hz3⟩ := hz3
        rw [Set.mem_singleton_iff.1 hz3]
        have hR := rbe_enq (k := false) _ u (q1_enq u) w1.2
          ⟨⟨(rbk_weak e4.2).1, u4.2.2.2, fun h => by cases h⟩, e4.2.2⟩ w2 hw2
        refine ⟨⟨⟨tq_enq_p _ u w1.2 (q1_enq u) u4.2.2.1 e4.1.1.1 w2 hw2,
          sa_enq_p _ u w1.2 (q1_enq u) (Or.inr (by rw [u4.1]; exact hu)) e4.1.1.2 w2 hw2⟩,
          q4_tcbSchedAction _ u w1.2 e4.1.2 w2 hw2⟩, hR.1.1, hR.2⟩
      · rw [c2] at hz3
        exact eb_yieldToSecond sc u z2.2 σ.curThread e2 ⟨c2, r2, schedulable_rn hs, hrq⟩ z3 hz3
    · rw [Set.mem_singleton_iff.1 hz3]; exact eb_weak e2
  dsimp only at hy
  split at hy
  · exact (eb_of (tq_returnConsumed sc) (sa_returnConsumed sc) (q4_returnConsumed sc) (rb_returnConsumed sc) :
      EBK false _) z3.2 e3 y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact e3

/-- **The SC YieldTo arm** takes `EB true` to `EB false` (no switch pending,
ct a runnable TCB, the SC's thread not ct: the decode's check). -/
theorem eb_perfScYieldTo (bl call don : Bool) (sc : ObjRef) :
    HKE (fun σ => EB true σ ∧ Simple σ ∧ RnH σ.curThread σ.kheap ∧ YT σ.curThread sc σ.kheap) (EB false)
      (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedContext (.invokeSchedContextYieldTo sc))) := by
  simp only [fl4PerformInvocation, withoutPreemption, invokeSchedContext]
  refine hk_liftE ?_
  intro σ hσ y hy
  exact eb_schedContextYieldTo sc σ hσ.2.1 hσ.2.2.1 hσ.2.2.2 hσ.1 y hy

end

end Fl4Proofs.P3.SInvQ.P15
