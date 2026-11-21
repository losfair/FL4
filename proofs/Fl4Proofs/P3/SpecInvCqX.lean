/-
P3 (DESIGN.md §9), invariant line G1 (ctq5): **the scheduler facts every
kernel exit leaves** (spec side only, outside the JAtZ cone), the entry
facts the event part of SchedQ needs (KENTRY-PLAN ctq4 handoff 2):

* `schedule` ends at `resume_cur_thread` (`rs_schedule`: the resume branch
  keeps it, the others end in `set_scheduler_action resume_cur_thread`;
  `sc_and_timer` keeps it);
* `activate_thread` at most sets `choose_new_thread` (its
  `set_thread_state`), so the exit's action is **`Simple`** (no
  `switch_thread`, l4v `simple_sched_action`);
* with SchedQ at `resume_cur_thread` the current thread is in no ready queue
  (CtNQR), and `activate_thread` writes neither the ready queues nor the
  current thread: **`CtQ`** (l4v `ct_not_in_q`, unconditional at the exit).
* **`sq_tailX : HK1 (SQ4 ∧ ValidIdle) EX (fl4Awaken; schedule;
  activate_thread)`**, `EX := SchedQ ∧ CtQ ∧ Simple ∧ CurScT`.
-/
import Fl4Proofs.P3.SpecInvCqW
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- No switch is pending (l4v `simple_sched_action`). -/
abbrev Simple (s : State Unit) : Prop := ∀ t, s.schedulerAction ≠ .switchThread t

/-- The action is `resume_cur_thread`. -/
abbrev RS (s : State Unit) : Prop := s.schedulerAction = .resumeCurThread

theorem simple_setCn : IK Simple (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ _ t e => by cases e

/-- `setObject` keeps a predicate that does not read the heap. -/
theorem ik_setObject_k {P : State Unit → Prop} (hP : ∀ σ (kh : ObjRef → Option KernelObject), P σ → P { σ with kheap := kh })
    (p : ObjRef) (o : KernelObject) : IK P (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨-, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hs; subst y2
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hP _ _ hσ

macro "fr_auto" : tactic => `(tactic| repeat' (first | ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h) | ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h) | ((with_reducible refine ik_setObject_k ?_ _ _); intro _ _ h; exact h) | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem simple_activateThread : IK Simple (activateThread (Z := Unit)) := by
  unfold activateThread
  repeat' (first | (with_reducible exact simple_setCn) | ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h) | ((with_reducible refine ik_setObject_k ?_ _ _); intro _ _ h; exact h) | ik_step0 | ik_unfold)

theorem rs_unblock (o : Option ObjRef) (a b : Option Bool) : IK RS (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; fr_auto

theorem rs_commitTime : IK RS (commitTime (Z := Unit)) := by
  unfold commitTime; fr_auto

theorem rs_setNextInterrupt : IK RS (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; fr_auto

theorem rs_switchSchedContext : IK RS (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext
  repeat' (first | (with_reducible exact rs_unblock _ _ _) | (with_reducible exact rs_commitTime) | ik_step0 | ik_unfold)

theorem rs_scAndTimer : IK RS (scAndTimer (Z := Unit)) := by
  unfold scAndTimer
  repeat' (first | (with_reducible exact rs_switchSchedContext) | (with_reducible exact rs_setNextInterrupt) | ik_step0)

theorem ctq_activateThread : IK CtQ (activateThread (Z := Unit)) := by
  unfold activateThread; fr_auto

theorem rs_chooseNew : PostK RS (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  exact post_bind fun _ => post_bind fun _ => post_bind fun _ => post_set _

/-- **`schedule` ends at `resume_cur_thread`.** -/
theorem rs_schedule : HK1 (fun _ => True) RS (schedule (Z := Unit)) := by
  unfold schedule
  refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
  refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
  intro σ
  show HKp (fun _ => True) RS σ _
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  try dsimp only
  split
  · rename_i heq
    exact fun _ y hy => rs_scAndTimer σ heq y hy
  · refine hkp_bind (R := fun _ => True) (fun _ _ _ => trivial) fun _ => ?_
    exact hk1_bind (R := RS) (fun s _ => rs_chooseNew s) fun _ => hk1_of_ik' rs_scAndTimer
  · refine hkp_bind (R := RS) ?_ fun _ => hk1_of_ik' rs_scAndTimer
    unfold scheduleSwitchThreadBranch
    refine hkp_bind (R := fun _ => True) (fun _ _ _ => trivial) fun _ => ?_
    refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
    refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
    dsimp only
    split <;> refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
    all_goals
      refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
      refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
      refine hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => ?_
      refine hk1_ite _ ?_ (hk1_ite _ ?_ ?_)
      · exact hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ =>
          hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => fun s _ => rs_chooseNew s
      · exact hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ =>
          hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => fun s _ => rs_chooseNew s
      · exact hk1_bind (R := fun _ => True) (fun _ _ _ _ => trivial) fun _ => fun s _ => post_set _ s

/-- The exit's facts. -/
abbrev EX (s : State Unit) : Prop := SchedQ s ∧ CtQ s ∧ Simple s ∧ CurScT s

theorem ctq_of_rs {s : State Unit} (h : SchedQ s) (hr : RS s) : CtQ s := h.2.2.2 hr

/-- **The kernel exit** gives `EX`. -/
theorem ex_exit : HK1 AW EX (schedule (Z := Unit) >>= fun _ => activateThread) := by
  intro σ h y ⟨z, hz, hy⟩
  have h1 := sq_schedule σ h z hz
  have h2 := rs_schedule σ trivial z hz
  refine ⟨⟨tq_activateThread z.2 h1.1 y hy, sa_activateThread z.2 h1.2 y hy⟩,
    ctq_activateThread z.2 (ctq_of_rs h1 h2) y hy,
    simple_activateThread z.2 (fun t e => by rw [h2] at e; cases e) y hy, ?_⟩
  exact (post_bind_ik curScT_schedule fun _ => cs_activateThread _) σ y ⟨z, hz, hy⟩

/-- **The tail of every kernel entry** with the exit's facts. -/
theorem sq_tailX : HK1 (fun s => SQ4 s ∧ SInvI.ValidIdle s) EX
    (fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) := by
  intro σ h y ⟨z, hz, hy⟩
  have h1 := sq4_fl4Awaken σ h.1 z hz
  have h2 := validIdle_of_vi (SInvI.vi_fl4Awaken (N := σ.idleThread) (S := σ.idleSc) (b := false) σ h.2 z hz)
  exact ex_exit z.2 (aw_of h1.1 h1.2 h2) y hy

end

end Fl4Proofs.P3.SInvQ
