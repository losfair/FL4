/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd3): **`Rdy` across
`schedule` up to `sc_and_timer`** (spec side only, outside the `JAtZ` cone;
KENTRY-PLAN rd2 handoff 1).

* Leaves: `switch_to_thread` / `switch_to_idle_thread` / `guarded_switch_to` /
  `choose_thread` / `schedule_choose_new_thread` (dequeues and reads only).
* **`CtR σ`**: the current thread, when runnable, `ActB` and not released
  (i.e. `schedulable`), is `RdyT`. (Runnability matters: after
  `end_timeslice`'s `handle_timeout ct` the current thread is blocked with a
  timeout fault, bound to `cur_sc`, outside the release queue, and its head
  may lie in the future.)
  This is what `schedule`'s two enqueues of the current thread under
  `schedulable` need. It is the mid-entry form of `OffReady ∧ CurScT` (ct
  bound to `cur_sc`, whose head is ready): `ctR_of` below. `awaken` keeps it
  (a thread it releases is `RdyT` at its release), `check_domain_time` keeps it.
* `scheduleSwitchThreadBranch`: the candidate is the switch target, `RdyT` by
  `R2` at the state it is enqueued / appended in.
* **`rd_schedule_via`**: `schedule` from `Rdy ∧ RNE ∧ CtR` ends in
  `sc_and_timer` started at a state where `Rdy` holds (any post `Q` of
  `sc_and_timer` from `Rdy` states lifts to `schedule`).
-/
import Fl4Proofs.P3.SpecInvRdE
import Fl4Proofs.P3.SpecInvRdF5
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Leaves -/

theorem rd_switchToThread (t : ObjRef) : RdK (switchToThread (Z := Unit) t) := by
  unfold switchToThread; rd_auto
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_switchToThread _)

theorem rd_switchToIdleThread : RdK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; rd_auto
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_switchToIdleThread)

theorem rd_guardedSwitchTo (t : ObjRef) : RdK (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo; rd_auto
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_guardedSwitchTo _)

theorem rd_chooseThread : RdK (chooseThread (Z := Unit)) := by
  unfold chooseThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ?_
  split
  · exact rd_switchToIdleThread
  · exact rd_guardedSwitchTo _
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_chooseThread)

theorem rd_scheduleChooseNewThread : RdK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (ik_bind (by rd_auto) fun _ => by rd_auto)) fun _ => ?_
  exact ik_bind rd_chooseThread fun _ => rd_setSchedulerAction_ns _ fun _ h => by cases h
macro_rules | `(tactic| rd_leaf) => `(tactic| with_reducible exact rd_scheduleChooseNewThread)

/-! ## The current thread's readiness -/

/-- **`CtR`** (module docstring). -/
def CtR (σ : State Unit) : Prop :=
  ∀ x, σ.kheap σ.curThread = some (.tcb x) → runnable x.tcbState = true → ActB σ σ.curThread →
    σ.curThread ∉ σ.releaseQueue → RdyT σ σ.curThread

/-- Heap, time, release queue and current thread, fixed. -/
abbrev KTC (K : ObjRef → Option KernelObject) (T : Time) (R : List ObjRef) (c : ObjRef) (σ : State Unit) : Prop :=
  σ.kheap = K ∧ σ.curTime = T ∧ σ.releaseQueue = R ∧ σ.curThread = c

theorem ctR_congr {σ σ' : State Unit} (h : CtR σ) (hk : σ'.kheap = σ.kheap) (ht : σ'.curTime = σ.curTime)
    (hr : σ'.releaseQueue = σ.releaseQueue) (hc : σ'.curThread = σ.curThread) : CtR σ' := by
  intro x hx hrun hA hn
  rw [hc] at hx hA hn ⊢
  rw [hr] at hn
  rw [hk] at hx
  exact rdyT_kt (h x hx hrun (actB_congr hk.symm hA) hn) hk ht

theorem ktc_rescheduleRequired (K : ObjRef → Option KernelObject) (T : Time) (R : List ObjRef) (c : ObjRef) :
    IK (KTC K T R c) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  repeat' (first | ik_step0 | ik_unfold)

theorem ktc_possibleSwitchTo (K : ObjRef → Option KernelObject) (T : Time) (R : List ObjRef) (c : ObjRef)
    (t : ObjRef) : IK (KTC K T R c) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo
  repeat' (first | (with_reducible exact ktc_rescheduleRequired _ _ _ _) | ik_step0 | ik_unfold)

theorem ktc_checkDomainTime (K : ObjRef → Option KernelObject) (T : Time) (R : List ObjRef) (c : ObjRef) :
    IK (KTC K T R c) (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime
  repeat' (first | (with_reducible exact ktc_rescheduleRequired _ _ _ _) | ik_step0 | ik_unfold)

theorem mem_tcbReleaseRemove {t : ObjRef} {σ : State Unit} {r : Unit × State Unit}
    (hr : r ∈ (tcbReleaseRemove (Z := Unit) t σ).1) :
    r.2.kheap = σ.kheap ∧ r.2.curTime = σ.curTime ∧ r.2.curThread = σ.curThread ∧
      r.2.releaseQueue = tcbSchedDequeue t σ.releaseQueue := by
  unfold tcbReleaseRemove setReleaseQueue at hr
  obtain ⟨z, hz, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hz] at hr
  obtain ⟨z, hz, hr⟩ := hr
  have hz' : z.2.kheap = σ.kheap ∧ z.2.curTime = σ.curTime ∧ z.2.curThread = σ.curThread := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨w, hw, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hw] at hr
  rw [Set.mem_singleton_iff.1 hr]
  exact ⟨hz'.1, hz'.2.1, hz'.2.2, rfl⟩

/-- One round of `awaken`: heap, time and current thread kept, the head gone
from the release queue. -/
theorem mem_tcbReleaseDequeue {σ : State Unit} {h : ObjRef} {rest : List ObjRef}
    (hq : σ.releaseQueue = h :: rest) {r : Unit × State Unit} (hr : r ∈ (tcbReleaseDequeue (Z := Unit) σ).1) :
    r.2.kheap = σ.kheap ∧ r.2.curTime = σ.curTime ∧ r.2.curThread = σ.curThread ∧
      r.2.releaseQueue = tcbSchedDequeue h σ.releaseQueue := by
  unfold tcbReleaseDequeue at hr
  obtain ⟨z, hz, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hz] at hr
  obtain ⟨z2, hz2, hr⟩ := hr
  have e2 : z2.2 = σ := cq5_ro (fun _ => by repeat' ik_step0) hz2
  obtain ⟨u2, s2⟩ := z2
  simp only at e2; subst e2
  obtain ⟨z3, hz3, hr⟩ := hr
  simp only [hq, List.head?_cons, Sched.the_some] at hz3 hr
  obtain ⟨a1, a2, a3, a4⟩ := mem_tcbReleaseRemove hz3
  obtain ⟨b1, b2, b3, b4⟩ := ktc_possibleSwitchTo _ _ _ _ h z3.2 ⟨rfl, rfl, rfl, rfl⟩ r hr
  exact ⟨b1.trans a1, b2.trans a2, b4.trans a3, b3.trans a4⟩

/-- **`awaken` keeps `Rdy ∧ RNE ∧ CtR`.** -/
theorem rd_awakenC (σ : State Unit) (hσ : Rdy σ) (hR : SInvB.RNE σ) (hC : CtR σ) {r : Unit × State Unit}
    (hr : r ∈ (awaken (Z := Unit) σ).1) : Rdy r.2 ∧ SInvB.RNE r.2 ∧ CtR r.2 := by
  unfold awaken at hr
  refine wl_inv (fun s => Rdy s ∧ SInvB.RNE s ∧ CtR s) (fun a s hs hc y hy => ?_) ⟨hσ, hR, hC⟩ hr
  obtain ⟨h, rest, hq, hT⟩ := rdyT_relHead hs.1 hs.2.1 hc
  obtain ⟨e1, e2, e3, e4⟩ := mem_tcbReleaseDequeue hq hy
  refine ⟨rd_tcbReleaseDequeue_p s hs.2.1 hc hs.1 y hy, fun p z n hz => hs.2.1 p z n (e1 ▸ hz), ?_⟩
  intro x hx hrun hA hn
  rw [e3] at hx hA hn ⊢
  rw [e1] at hx
  by_cases e : s.curThread = h
  · rw [e]; exact rdyT_kt hT e1 e2
  · have hn' : s.curThread ∉ s.releaseQueue := by
      intro hm
      rw [hq] at hm
      rcases List.mem_cons.1 hm with hm | hm
      · exact e hm
      · refine hn ?_
        rw [e4, hq]
        exact List.mem_filter.2 ⟨List.mem_cons_of_mem _ hm, by simpa using Ne.symm e⟩
    exact rdyT_kt (hs.2.2 x hx hrun (actB_congr e1.symm hA) hn') e1 e2


/-! ## `schedule`'s branches -/

/-- The scheduler action, fixed. -/
abbrev AF (A : SchedulerAction) (σ : State Unit) : Prop := σ.schedulerAction = A

theorem rd_enqCt_p (σ : State Unit) (hC : CtR σ) :
    IKp Rdy σ (NonDet.when (schedulable σ.curThread σ = true)
      (tcbSchedAction (Z := Unit) tcbSchedEnqueue σ.curThread)) := by
  refine ikp_when _ fun hs => ?_
  obtain ⟨x, -, -, -, hx, -, hrun, -, -, hn⟩ := Sched.schedulable_inv hs
  exact rd_enqueue_p _ σ (hC x hx hrun (actB_of_schedulable hs) hn)

theorem af_enq (A : SchedulerAction) (c : Prop) [Decidable c] (t : ObjRef) :
    IK (AF A) (NonDet.when c (tcbSchedAction (Z := Unit) tcbSchedEnqueue t)) := by
  repeat' (first | ik_step0 | ik_unfold)

/-- **`schedule_switch_thread_branch`** with the candidate as the switch target. -/
theorem rd_sstb_p (c : ObjRef) (σ : State Unit) (hC : CtR σ) (ha : σ.schedulerAction = .switchThread c) :
    IKp Rdy σ (scheduleSwitchThreadBranch (Z := Unit) c σ.curThread (schedulable σ.curThread σ)) := by
  intro hσ r ⟨w, hw, hr⟩
  have hw1 := rd_enqCt_p σ hC hσ w hw
  have hwa : w.2.schedulerAction = .switchThread c := by
    rw [← ha]; exact af_enq σ.schedulerAction _ σ.curThread σ rfl w hw
  have hRc : RdyT w.2 c := hw1.2.1 c hwa
  refine (?_ : IKp Rdy w.2 _) hw1 r hr
  try dsimp only
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  try dsimp only
  split <;> refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  all_goals
    refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    split
    · exact ikp_bind (rd_enqueue_p c w.2 hRc) fun _ =>
        ik_bind (rd_setSchedulerAction_ns _ fun _ h => by cases h) fun _ => rd_scheduleChooseNewThread
    · split
      · exact ikp_bind (rd_append_p c w.2 hRc) fun _ =>
          ik_bind (rd_setSchedulerAction_ns _ fun _ h => by cases h) fun _ => rd_scheduleChooseNewThread
      · exact ikp_of_ik (ik_bind (rd_guardedSwitchTo c) fun _ => rd_setSchedulerAction_ns _ fun _ h => by cases h) _

/-- Every outcome from `σ` satisfies `Q`. -/
def PostP (Q : State Unit → Prop) (σ : State Unit) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ r ∈ (m σ).1, Q r.2

theorem pp_bind_of {Q : State Unit → Prop} {σ : State Unit} {α β : Type} {m : NonDet (State Unit) α}
    {k : α → NonDet (State Unit) β} (h : ∀ y ∈ (m σ).1, PostP Q y.2 (k y.1)) : PostP Q σ (m >>= k) := by
  intro r ⟨y, hy, hr⟩
  exact h y hy r hr

theorem pp_gets_bind {Q : State Unit → Prop} {σ : State Unit} {α β : Type} {g : State Unit → α}
    {k : α → NonDet (State Unit) β} (h : PostP Q σ (k (g σ))) : PostP Q σ (NonDet.gets g >>= k) :=
  pp_bind_of fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h

/-- **`schedule`, up to `sc_and_timer`** (module docstring). -/
theorem rd_schedule_via {Q : State Unit → Prop}
    (hT : ∀ s, Rdy s → ∀ r ∈ (scAndTimer (Z := Unit) s).1, Q r.2) (σ : State Unit) (hσ : Rdy σ)
    (hR : SInvB.RNE σ) (hC : CtR σ) : ∀ r ∈ (schedule (Z := Unit) σ).1, Q r.2 := by
  show PostP Q σ _
  unfold schedule
  refine pp_bind_of fun z1 hz1 => ?_
  obtain ⟨a1, -, a3⟩ := rd_awakenC σ hσ hR hC hz1
  refine pp_bind_of fun z2 hz2 => ?_
  have b1 := rd_checkDomainTime z1.2 a1 z2 hz2
  obtain ⟨k1, k2, k3, k4⟩ := ktc_checkDomainTime _ _ _ _ z1.2 ⟨rfl, rfl, rfl, rfl⟩ z2 hz2
  have b3 : CtR z2.2 := ctR_congr a3 k1 k2 k3 k4
  refine pp_gets_bind (pp_gets_bind (pp_gets_bind ?_))
  try dsimp only
  split
  · exact fun r hr => hT _ b1 r hr
  · refine pp_bind_of fun w hw => ?_
    have hw1 := rd_enqCt_p z2.2 b3 b1 w hw
    exact pp_bind_of fun v hv => fun r hr => hT _ (rd_scheduleChooseNewThread w.2 hw1 v hv) r hr
  · rename_i c hc
    exact pp_bind_of fun w hw => fun r hr => hT _ (rd_sstb_p c z2.2 b3 hc b1 w hw) r hr

end

end Fl4Proofs.P3.SInvR
