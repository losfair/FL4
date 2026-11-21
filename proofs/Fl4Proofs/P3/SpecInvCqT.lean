/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ctq4): **SchedQ across
the kernel exit: `schedule` and `activate_thread`** (spec side only, outside
the JAtZ cone; KENTRY-PLAN ctq3 (a), (b)).

* `AW σ := SchedQ σ ∧ DomEq σ ∧ IdleNR σ`, where `DomEq`: every TCB is of
  `cur_domain` (T4's `TI dom0 ∧ cur_domain = 0`, ctnq1), and `IdleNR`: the
  idle thread's TCB is not runnable (ValidIdle's `vi_idle`, vi2).
* `awaken`: each released head is runnable by RR, of the current domain by
  `DomEq` (so `possible_switch_to`'s other-domain enqueue is dead), and the
  loop keeps the heap, the domain and the idle pointer (`KH`).
* `schedule`'s branches: the current thread is enqueued only when
  `schedulable` read it (runnable); in the switch branch the candidate is
  runnable by RA while the action is `switch_thread candidate` (`P1`); the
  action stays off `resume_cur_thread` until the final
  `set_scheduler_action resume_cur_thread`, which follows a switch:
  `switch_to_thread t` dequeues `t` (in no queue after, T1) and
  `switch_to_idle_thread` picks the idle thread, in no queue by `IdleNR` and
  "queued ⇒ runnable" (`IQ`, kept by the arch steps and `next_domain`: `FF`).
* **`sq_schedule : HK1 AW SchedQ schedule`**, **`sq_exit : HK1 AW SchedQ
  (schedule >>= fun _ => activate_thread)`**.
-/
import Fl4Proofs.P3.SpecInvCqSF5
import Fl4Proofs.P3.SpecInvCqRF5
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Pre/post helpers -/

theorem hk1_of_ik' {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HK1 P P m :=
  fun σ hσ x hx => h σ hσ x hx

theorem hk1_ite {P Q : State Unit → Prop} {α : Type} (c : Prop) [Decidable c] {m1 m2 : NonDet (State Unit) α}
    (h1 : HK1 P Q m1) (h2 : HK1 P Q m2) : HK1 P Q (if c then m1 else m2) := by
  split <;> assumption

/-- `HK1` at one start state. -/
def HKp (P Q : State Unit → Prop) (σ : State Unit) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  P σ → ∀ x, x ∈ (m σ).1 → Q x.2

theorem hkp_bind {P R Q : State Unit → Prop} {α γ : Type} {σ : State Unit} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) γ} (hm : HKp P R σ m) (hg : ∀ a, HK1 R Q (g a)) : HKp P Q σ (m >>= g) := by
  intro hσ x ⟨y, hy, hx⟩
  exact hg y.1 y.2 (hm hσ y hy) x hx

theorem hkp_gets_bind {P Q : State Unit → Prop} {α β : Type} {σ : State Unit} {g : State Unit → α}
    {k : α → NonDet (State Unit) β} (h : HKp P Q σ (k (g σ))) : HKp P Q σ (NonDet.gets g >>= k) := by
  intro hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h hσ x hx

theorem hkp_when {P Q : State Unit → Prop} {σ : State Unit} (c : Prop) [Decidable c] {m : NonDet (State Unit) Unit}
    (h1 : c → HKp P Q σ m) (h2 : ¬c → P σ → Q σ) : HKp P Q σ (NonDet.when c m) := by
  unfold NonDet.when
  split
  · exact h1 ‹c›
  · rename_i hc
    intro hσ x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact h2 hc hσ

/-! ## Field frames -/

/-- The heap, the current domain and the idle pointer are kept. -/
abbrev KH (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) (s : State Unit) : Prop :=
  s.kheap = K ∧ s.curDomain = D ∧ s.idleThread = I

/-- The ready queues, the idle pointer and the scheduler action are kept. -/
abbrev FF (Q : Domain → Priority → ReadyQueue) (I : ObjRef) (A : SchedulerAction) (s : State Unit) : Prop :=
  s.readyQueues = Q ∧ s.idleThread = I ∧ s.schedulerAction = A

theorem kh_tcbReleaseRemove (t : ObjRef) (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) :
    IK (KH K D I) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; repeat' (first | ik_step0 | ik_unfold)

theorem kh_rescheduleRequired (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) :
    IK (KH K D I) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; repeat' (first | ik_step0 | ik_unfold)

theorem kh_possibleSwitchTo (t : ObjRef) (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) :
    IK (KH K D I) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo
  repeat' (first | (with_reducible exact kh_rescheduleRequired _ _ _) | ik_step0 | ik_unfold)

theorem kh_checkDomainTime (K : ObjRef → Option KernelObject) (D : Domain) (I : ObjRef) :
    IK (KH K D I) (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime
  repeat' (first | (with_reducible exact kh_rescheduleRequired _ _ _) | ik_step0 | ik_unfold)

theorem ff_archSwitchToThread (t : ObjRef) (Q : Domain → Priority → ReadyQueue) (I : ObjRef) (A : SchedulerAction) :
    IK (FF Q I A) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; repeat' (first | ik_step0 | ik_unfold)

theorem ff_archSwitchToIdleThread (Q : Domain → Priority → ReadyQueue) (I : ObjRef) (A : SchedulerAction) :
    IK (FF Q I A) (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; repeat' (first | ik_step0 | ik_unfold)

theorem ff_archPrepareNextDomain (Q : Domain → Priority → ReadyQueue) (I : ObjRef) (A : SchedulerAction) :
    IK (FF Q I A) (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; repeat' (first | ik_step0 | ik_unfold)

theorem ff_nextDomain (Q : Domain → Priority → ReadyQueue) (I : ObjRef) (A : SchedulerAction) :
    IK (FF Q I A) (nextDomain (Z := Unit)) := by
  unfold nextDomain; repeat' (first | ik_step0 | ik_unfold)

/-! ## `awaken` -/

/-- Every TCB is of the current domain (T4 with one domain). -/
abbrev DomEq (s : State Unit) : Prop := ∀ t x, s.kheap t = some (.tcb x) → x.tcbDomain = s.curDomain

/-- The idle thread's TCB is not runnable (ValidIdle). -/
abbrev IdleNR (s : State Unit) : Prop := ∀ x, s.kheap s.idleThread = some (.tcb x) → runnable x.tcbState = false

/-- The invariant at `schedule`'s entry. -/
abbrev AW (s : State Unit) : Prop := SchedQ s ∧ DomEq s ∧ IdleNR s

theorem aw_of_kh {σ s : State Unit} (h : AW σ) (hq : SchedQ s) (hk : KH σ.kheap σ.curDomain σ.idleThread s) :
    AW s := by
  obtain ⟨-, h2, h3⟩ := h
  obtain ⟨e1, e2, e3⟩ := hk
  refine ⟨hq, fun t x hx => ?_, fun x hx => ?_⟩
  · rw [e2]; exact h2 t x (by rw [← e1]; exact hx)
  · exact h3 x (by rw [← e1, ← e3]; exact hx)

theorem the_head_mem {l : List ObjRef} (h : l ≠ []) : the l.head? ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp [the]

theorem aw_tcbReleaseDequeue : IK AW (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue
  refine ik_gets_bind fun σ => ?_
  intro hσ y hy
  obtain ⟨z, ⟨hne, rfl⟩, hy⟩ := hy
  obtain ⟨w, hw, hy⟩ := hy
  have hk := kh_tcbReleaseRemove _ σ.kheap σ.curDomain σ.idleThread σ ⟨rfl, rfl, rfl⟩ w hw
  have hq : SchedQ w.2 := ⟨tq_tcbReleaseRemove _ σ hσ.1.1 w hw, sa_tcbReleaseRemove _ σ hσ.1.2 w hw⟩
  have hw' : AW w.2 := aw_of_kh hσ hq hk
  obtain ⟨x, hx, hr⟩ := hσ.1.2.2.1 _ (the_head_mem hne)
  have hx' : w.2.kheap (the σ.releaseQueue.head?) = some (.tcb x) := by rw [hk.1]; exact hx
  have hq2 := sq_possibleSwitchTo_p _ w.2 ⟨x, hx', hr⟩ (fun x0 hx0 => Or.inl (hw'.2.1 _ x0 hx0)) hw'.1 y hy
  have hk2 := kh_possibleSwitchTo _ w.2.kheap w.2.curDomain w.2.idleThread w.2 ⟨rfl, rfl, rfl⟩ y hy
  exact aw_of_kh hw' hq2 hk2

theorem aw_awaken : IK AW (awaken (Z := Unit)) := by
  unfold awaken; exact ik_whileLoop (fun _ => aw_tcbReleaseDequeue) ()

theorem aw_checkDomainTime : IK AW (checkDomainTime (Z := Unit)) := fun σ h y hy =>
  aw_of_kh h ⟨tq_checkDomainTime σ h.1.1 y hy, sa_checkDomainTime σ h.1.2 y hy⟩
    (kh_checkDomainTime _ _ _ σ ⟨rfl, rfl, rfl⟩ y hy)

/-! ## Switching -/

/-- The current thread is in no ready queue. -/
abbrev CtQ (s : State Unit) : Prop := ∀ d p, s.curThread ∉ s.readyQueues d p

/-- The idle thread is in no ready queue. -/
abbrev IQ (s : State Unit) : Prop := ∀ d p, s.idleThread ∉ s.readyQueues d p

/-- SchedQ off `resume_cur_thread`. -/
abbrev SQn (s : State Unit) : Prop := SchedQ s ∧ s.schedulerAction ≠ .resumeCurThread

abbrev SQI (s : State Unit) : Prop := SQn s ∧ IQ s

abbrev SQC (s : State Unit) : Prop := SQn s ∧ CtQ s

theorem iq_of {s : State Unit} (hR : RQd s) (hI : IdleNR s) : IQ s := fun d p hm => by
  obtain ⟨x, hx, -, -, hr⟩ := hR d p _ hm
  rw [hI x hx] at hr; cases hr

theorem sqi_of_ff {α : Type} {m : NonDet (State Unit) α} (h1 : TQK m) (h2 : SAK m)
    (hf : ∀ Q I A, IK (FF Q I A) m) : IK SQI m := by
  intro σ hσ y hy
  have hf' := hf σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ y hy
  refine ⟨⟨⟨h1 σ hσ.1.1.1 y hy, h2 σ hσ.1.1.2 y hy⟩, by rw [hf'.2.2]; exact hσ.1.2⟩, fun d p => ?_⟩
  rw [hf'.1, hf'.2.1]; exact hσ.2 d p

theorem ik_threadGet_any (P : State Unit → Prop) {β : Type} (f : Tcb → β) (t : ObjRef) :
    IK P (threadGet (Z := Unit) f t) := fun σ h y hy => by
  obtain ⟨x, -, rfl⟩ := q1_mem_threadGet hy; exact h

theorem ik_fastfail (P : State Unit → Prop) (ct it : ObjRef) (p q : Priority) :
    IK P (scheduleSwitchThreadFastfail (Z := Unit) ct it p q) := fun σ h y hy => by
  unfold scheduleSwitchThreadFastfail at hy; rw [Set.mem_singleton_iff.1 hy]; exact h

theorem sqc_switchToThread (t : ObjRef) : HK1 SQn SQC (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨w, hw, hy⟩ := hy
  have hw1 : SchedQ w.2 := ⟨tq_archSwitchToThread t σ hσ.1.1 w hw, sa_archSwitchToThread t σ hσ.1.2 w hw⟩
  have hf := ff_archSwitchToThread t σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ w hw
  obtain ⟨v, hv, hy⟩ := hy
  have hv1 := tq_dequeue_noQ t w.2 hw1.1 v hv
  have hv2 := sa_dequeue t w.2 hw1.2 v hv
  have hva : v.2.schedulerAction = w.2.schedulerAction := by
    obtain ⟨x, -, e⟩ := q1_tsa_out hv; rw [e]
  rw [Set.mem_singleton_iff.1 hy]
  have hn : v.2.schedulerAction ≠ .resumeCurThread := by rw [hva, hf.2.2]; exact hσ.2
  exact ⟨⟨⟨⟨hv1.1, trivial⟩, ⟨hv2.1, hv2.2.1, fun hs => absurd hs hn⟩⟩, hn⟩, hv1.2⟩

theorem sqc_guardedSwitchTo (t : ObjRef) : HK1 SQn SQC (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assertOpt _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assert _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assert _)) fun _ => ?_
  exact sqc_switchToThread t

theorem sqc_switchToIdleThread : HK1 SQI SQC (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  have hw1 : SchedQ w.2 := ⟨tq_archSwitchToIdleThread σ hσ.1.1.1 w hw, sa_archSwitchToIdleThread σ hσ.1.1.2 w hw⟩
  have hf := ff_archSwitchToIdleThread σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ w hw
  rw [Set.mem_singleton_iff.1 hy]
  have hn : w.2.schedulerAction ≠ .resumeCurThread := by rw [hf.2.2]; exact hσ.1.2
  refine ⟨⟨⟨⟨hw1.1.1, trivial⟩, ⟨hw1.2.1, hw1.2.2.1, fun hs => absurd hs hn⟩⟩, hn⟩, fun d p => ?_⟩
  show σ.idleThread ∉ w.2.readyQueues d p
  rw [hf.1]; exact hσ.2 d p

theorem sqc_chooseThread : HK1 SQI SQC (chooseThread (Z := Unit)) := by
  unfold chooseThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  dsimp only at hy
  split at hy
  · exact sqc_switchToIdleThread σ hσ y hy
  · exact sqc_guardedSwitchTo _ σ hσ.1 y hy

theorem sq_setResume : HK1 SQC SchedQ (setSchedulerAction (Z := Unit) .resumeCurThread) := by
  intro s hs y hy
  unfold setSchedulerAction at hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨hs.1.1.1, fun t ht => absurd ht (by simp), hs.1.1.2.2.1, fun _ => hs.2⟩

theorem sq_scheduleChooseNewThread : HK1 SQI SchedQ (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine hk1_bind (R := SQI) (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (R := SQI) (hk1_of_ik' ?_) fun _ => ?_
  · exact ik_when _ (ik_bind (sqi_of_ff tq_archPrepareNextDomain sa_archPrepareNextDomain ff_archPrepareNextDomain)
      fun _ => sqi_of_ff tq_nextDomain sa_nextDomain ff_nextDomain)
  exact hk1_bind sqc_chooseThread fun _ => sq_setResume

/-! ## `schedule` -/

/-- The switch branch's invariant: the action is `switch_thread c`. -/
abbrev P1 (c : ObjRef) (s : State Unit) : Prop :=
  SchedQ s ∧ IdleNR s ∧ s.schedulerAction = .switchThread c

theorem p1_tsa (c : ObjRef) (act : ObjRef → List ObjRef → List ObjRef)
    (hact : ∀ q u, u ∈ act c q → u ∈ q ∨ u = c) : HK1 (P1 c) (P1 c) (tcbSchedAction (Z := Unit) act c) := by
  intro s hs y hy
  obtain ⟨x, hx, hr⟩ := hs.1.2.1 c hs.2.2
  have h1 := tq_enq_p act c s hact ⟨x, hx, hr⟩ hs.1.1 y hy
  have h2 := sa_enq_p act c s hact (Or.inl (by rw [hs.2.2]; exact fun e => absurd e (by simp))) hs.1.2 y hy
  obtain ⟨x', -, e⟩ := q1_tsa_out hy
  exact ⟨⟨h1, h2⟩, by rw [e]; exact hs.2.1, by rw [e]; exact hs.2.2⟩

theorem p1_setCn (c : ObjRef) : HK1 (P1 c) SQI (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  intro s hs y hy
  unfold setSchedulerAction at hy
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨⟨⟨hs.1.1, fun t ht => absurd ht (by simp), hs.1.2.2.1, fun h => absurd h (by simp)⟩, by simp⟩,
    iq_of hs.1.1.1 hs.2.1⟩

theorem p1_guarded (c : ObjRef) : HK1 (P1 c) SQC (guardedSwitchTo (Z := Unit) c) :=
  fun s hs => sqc_guardedSwitchTo c s ⟨hs.1, by rw [hs.2.2]; exact fun e => absurd e (by simp)⟩

/-- The current thread enqueued after `schedulable` read it, off `resume_cur_thread`. -/
theorem aw_enq_ct (σ : State Unit) (act : ObjRef → List ObjRef → List ObjRef)
    (hact : ∀ q u, u ∈ act σ.curThread q → u ∈ q ∨ u = σ.curThread)
    (hs : schedulable σ.curThread σ = true) (hn : σ.schedulerAction ≠ .resumeCurThread)
    (Q : State Unit → Prop) (hQ : ∀ s, SchedQ s → IdleNR s → s.schedulerAction = σ.schedulerAction → Q s) :
    HKp AW Q σ (tcbSchedAction (Z := Unit) act σ.curThread) := by
  intro h y hy
  have h1 := tq_enq_p act _ σ hact (schedulable_rn hs) h.1.1 y hy
  have h2 := sa_enq_p act _ σ hact (Or.inl hn) h.1.2 y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  exact hQ _ ⟨h1, h2⟩ (by rw [e]; exact h.2.2) (by rw [e])

theorem sq_scAndTimer : HK1 SchedQ SchedQ (scAndTimer (Z := Unit)) :=
  fun σ h y hy => ⟨tq_scAndTimer σ h.1 y hy, sa_scAndTimer σ h.2 y hy⟩

/-- **`schedule`** keeps SchedQ (from `AW`). -/
theorem sq_schedule : HK1 AW SchedQ (schedule (Z := Unit)) := by
  unfold schedule
  refine hk1_bind (R := AW) (hk1_of_ik' aw_awaken) fun _ => ?_
  refine hk1_bind (R := AW) (hk1_of_ik' aw_checkDomainTime) fun _ => ?_
  intro σ
  show HKp AW SchedQ σ _
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  try dsimp only
  split
  · -- resume
    exact fun h y hy => sq_scAndTimer σ h.1 y hy
  · -- choose_new_thread
    rename_i heq
    refine hkp_bind (R := SQI) ?_ fun _ => hk1_bind sq_scheduleChooseNewThread fun _ => sq_scAndTimer
    have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [heq]; exact fun e => absurd e (by simp)
    refine hkp_when _ (fun hs => aw_enq_ct σ _ (q1_enq _) hs hn SQI fun s h1 h2 h3 =>
      ⟨⟨h1, by rw [h3]; exact hn⟩, iq_of h1.1.1 h2⟩) fun _ h => ⟨⟨h.1, hn⟩, iq_of h.1.1.1 h.2.2⟩
  · -- switch_thread candidate
    rename_i c heq
    have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [heq]; exact fun e => absurd e (by simp)
    refine hkp_bind (R := SchedQ) ?_ fun _ => sq_scAndTimer
    unfold scheduleSwitchThreadBranch
    refine hkp_bind (R := P1 c) ?_ fun _ => ?_
    · exact hkp_when _ (fun hs => aw_enq_ct σ _ (q1_enq _) hs hn (P1 c) fun s h1 h2 h3 => ⟨h1, h2, h3.trans heq⟩)
        fun _ h => ⟨h.1, h.2.2, heq⟩
    refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
    -- the `ct_prio` read is a join point: zeta-reduce it, then the same tail in both arms
    dsimp only
    split <;> refine hk1_bind (hk1_of_ik' (by first | exact ik_threadGet_any _ _ _ | exact ik_pure _)) fun _ => ?_
    all_goals
      refine hk1_bind (hk1_of_ik' (ik_fastfail _ _ _ _ _)) fun _ => ?_
      refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
      refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
      refine hk1_ite _ ?_ (hk1_ite _ ?_ ?_)
      · exact hk1_bind (p1_tsa c _ (q1_enq c)) fun _ => hk1_bind (p1_setCn c) fun _ => sq_scheduleChooseNewThread
      · exact hk1_bind (p1_tsa c _ (q1_app c)) fun _ => hk1_bind (p1_setCn c) fun _ => sq_scheduleChooseNewThread
      · exact hk1_bind (p1_guarded c) fun _ => sq_setResume

/-- **The kernel exit**: `schedule`, then `activate_thread`. -/
theorem sq_exit : HK1 AW SchedQ (schedule (Z := Unit) >>= fun _ => activateThread) :=
  hk1_bind sq_schedule fun _ σ h y hy => ⟨tq_activateThread σ h.1 y hy, sa_activateThread σ h.2 y hy⟩

end

end Fl4Proofs.P3.SInvQ
