/-
P3 (DESIGN.md §9), invariant line G1 (rd8h): **`invoke_set_domain` keeps
`Rdy`** from rd's `SR t` (the target, if schedulable, is `RdyT`) at its start
(spec side only, outside the JAtZ cone).

`set_domain` re-enqueues its target whenever it is `schedulable` (not only
when it was queued, unlike `set_priority`), so `Rdy` needs the target `RdyT`
when schedulable: l4v's `valid_blocked` (a schedulable thread that is not the
current thread or the switch target is in a ready queue) with `valid_ready_qs`
(R1) and the current thread's readiness. Not derivable from `Rdy` alone.

* `sr_frame`: `SR t` along a step keeping every TCB's state / fault / SC (rd8d's
  `TV`), every object's scheduler view (`SVS`) and the release queue
  (`schedulable_inv` / `schedulable_of`).
* `SF σ0`, `sf_of`, `sf_archPrepareSetDomain`, `sf_dequeue`,
  `sf_threadSetDomain`.
* **`rd_invokeSetDomain t d σ (hR : Rdy σ) (hSR : SR t σ)`**.
-/
import Fl4Proofs.P3.SpecInvRd8hC
open Classical

namespace Fl4Proofs.P3.SInvR.B8h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

/-- `SR t` along a step keeping `TV`, `SVS` and the release queue. -/
theorem sr_frame {s s' : State Unit} {t : ObjRef} (h : SR t s) (hT : B8d.TV (B8d.TVv s) s')
    (hS : SVK.SVS s s') (hq : s'.releaseQueue = s.releaseQueue) : SR t s' := by
  intro hs'
  obtain ⟨x', scp, y', n, hx', hsc', hr', hy', ha', hq'⟩ := Sched.schedulable_inv hs'
  have e1 := hS.1 t
  rw [hx'] at e1
  obtain ⟨x, hx, hxs⟩ := SVK.sv_tcb (o := s.kheap t) e1.symm
  have ev := congrFun hT t
  unfold B8d.TVv at ev
  rw [hx', hx] at ev
  simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
  have e2 := hS.1 scp
  rw [hy'] at e2
  obtain ⟨y, hy, -, hrm, -⟩ := SVK.sv_sc (o := s.kheap scp) e2.symm
  have hs : schedulable t s = true :=
    Sched.schedulable_of hx (hxs.trans hsc') (by rw [← ev.1]; exact hr') hy
      (by show activeSc y.scRefillMax = true; rw [hrm]; exact ha') (by rw [← hq]; exact hq')
  exact rdyT_svs (h hs) hS

/-- The frame of `sr_frame` from a fixed start. -/
abbrev SF (σ0 s : State Unit) : Prop :=
  B8d.TV (B8d.TVv σ0) s ∧ SVK.SVS σ0 s ∧ s.releaseQueue = σ0.releaseQueue

theorem sf_of {σ0 : State Unit} {α : Type} {m : NonDet (State Unit) α} (hT : ∀ V, B8d.TVK V m)
    (hS : SVK.SVM m) (hR : ∀ R, IK (fun s : State Unit => s.releaseQueue = R) m) : IK (SF σ0) m :=
  fun s h y hy => ⟨hT _ s h.1 y hy, h.2.1.trans (hS s y hy), (hR _ s rfl y hy).trans h.2.2⟩

theorem sf_archPrepareSetDomain {σ0 : State Unit} (t : ObjRef) (d : Domain) :
    IK (SF σ0) (archPrepareSetDomain (Z := Unit) t d) := by
  refine sf_of (fun V => ?_) ?_ (fun R => ?_)
  · unfold archPrepareSetDomain fpuRelease switchLocalFpuOwner saveFpuState loadFpuState setX64CurrentFpuOwner
    tv_auto
  · unfold archPrepareSetDomain fpuRelease switchLocalFpuOwner saveFpuState loadFpuState setX64CurrentFpuOwner
    sv_auto
  · unfold archPrepareSetDomain
    repeat' (first | ik_step0 | ik_unfold)

theorem sf_dequeue {σ0 : State Unit} (t : ObjRef) :
    IK (SF σ0) (tcbSchedAction (Z := Unit) tcbSchedDequeue t) := by
  refine sf_of (fun V => ?_) (SVK.sv_tcbSchedAction' _ _) (fun R => ?_)
  · unfold tcbSchedAction; tv_auto
  · unfold tcbSchedAction
    repeat' (first | ik_step0 | ik_unfold)

theorem sf_threadSetDomain {σ0 : State Unit} (t : ObjRef) (d : Domain) :
    IK (SF σ0) (threadSetDomain (Z := Unit) t d) := by
  unfold threadSetDomain
  refine sf_of (fun V => B8d.tv_threadSet (fun tcb => { tcb with tcbDomain := d }) t fun _ => ⟨rfl, rfl, rfl⟩)
    (SVK.sv_threadSet' (fun tcb => { tcb with tcbDomain := d }) (fun _ => rfl) t) (fun R => ?_)
  repeat' (first | ik_step0 | ik_unfold)

/-- **`invoke_set_domain t d`** keeps `Rdy` when `t`, if schedulable, is
`RdyT` at its start. -/
theorem rd_invokeSetDomain (t : ObjRef) (d : Domain) (σ : State Unit) (hR : Rdy σ) (hSR : SR t σ) :
    ∀ y ∈ (invokeSetDomain (Z := Unit) t d σ).1, Rdy y.2 := by
  intro y hy
  unfold invokeSetDomain at hy
  obtain ⟨z1, h1, hy⟩ := hy
  have r1 : Rdy z1.2 := rd_archPrepareSetDomain t d σ hR z1 h1
  have f1 : SF σ z1.2 := sf_archPrepareSetDomain t d σ ⟨rfl, SVK.SVS.refl σ, rfl⟩ z1 h1
  unfold setDomain at hy
  obtain ⟨z2, h2, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 h2
  obtain ⟨z3, h3, hy⟩ := hy
  have r3 : Rdy z3.2 := rd_dequeue t z1.2 r1 z3 h3
  have f3 : SF σ z3.2 := sf_dequeue t z1.2 f1 z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have r4 : Rdy z4.2 :=
    rd_threadSet (fun tcb => { tcb with tcbDomain := d }) t (fun _ => ⟨rfl, rfl, rfl⟩) z3.2 r3 z4 h4
  have f4 : SF σ z4.2 := sf_threadSetDomain t d z3.2 f3 z4 h4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 h5
  obtain ⟨z6, h6, hy⟩ := hy
  have r6 : Rdy z6.2 := by
    dsimp only at h6
    unfold NonDet.when at h6
    split_ifs at h6 with hs
    · exact rd_tsa_p _ t z4.2
        (fun q u hu => (SInvQ.q1_enq t q u hu).imp id fun e => ⟨e, sr_frame hSR f4.1 f4.2.1 f4.2.2 hs⟩) r4 z6 h6
    · rw [Set.mem_singleton_iff.1 h6]; exact r4
  exact ik_when _ rd_rescheduleRequired z6.2 r6 y hy

end

end Fl4Proofs.P3.SInvR.B8h
