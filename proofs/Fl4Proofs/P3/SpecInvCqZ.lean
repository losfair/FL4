/-
P3 (DESIGN.md §9), invariant line G1 (ctq6): **the kernel exit carries RD
and gives the current thread not released** (spec side only, outside the
JAtZ cone; KENTRY-PLAN ctq5 handoff 1).

* `schedule` keeps `RBk false` (RD; under `resume_cur_thread` ct not
  released and a runnable TCB or idle) from `AW`: the current thread is
  enqueued only after `schedulable` read it (not released), the candidate is
  the switch target (not released by RD), the switch picks a queued thread
  (RD: not released; TQ: runnable) or the switch target (RD, SA) or the idle
  thread (in no release queue: RR + IdleNR at `schedule`'s entry, and
  `schedule` only removes from the release queue).
* At the exit's `resume_cur_thread` that is `RB` (with CtNQR: ct in no ready
  queue), kept by `activate_thread`: **`rb_exit : HK1 (AW ∧ RBk false) RB
  (schedule; activate_thread)`**, **`exR_exit : HK1 (AW ∧ RBk false) (EX ∧
  RB)`**.
-/
import Fl4Proofs.P3.SpecInvCqYF5
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The idle thread is not released -/

/-- The idle thread is not in the release queue. -/
abbrev IR (s : State Unit) : Prop := s.idleThread ∉ s.releaseQueue

theorem ir_of_aw {s : State Unit} (h : AW s) : IR s := fun hm => by
  obtain ⟨x, hx, hr⟩ := h.1.2.2.1 _ hm
  rw [h.2.2 x hx] at hr; cases hr

theorem ir_tcbReleaseRemove (t : ObjRef) : IK IR (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  refine ik_gets_bind fun σ => ?_
  intro hσ y ⟨z, hz, hy⟩
  have hz' : z.2.idleThread = σ.idleThread ∧ z.2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl⟩
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  rw [Set.mem_singleton_iff.1 hy]
  intro hm
  show False
  have hm' : z.2.idleThread ∈ tcbSchedDequeue t σ.releaseQueue := hm
  rw [hz'.1] at hm'
  exact hσ (List.mem_filter.1 hm').1

theorem ir_possibleSwitchTo (t : ObjRef) : IK IR (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; repeat' (first | ik_step0 | ik_unfold)

theorem ir_checkDomainTime : IK IR (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; repeat' (first | ik_step0 | ik_unfold)

theorem ir_archSwitchToThread (t : ObjRef) : IK IR (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; repeat' (first | ik_step0 | ik_unfold)

theorem ir_archSwitchToIdleThread : IK IR (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; repeat' (first | ik_step0 | ik_unfold)

theorem ir_archPrepareNextDomain : IK IR (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; repeat' (first | ik_step0 | ik_unfold)

theorem ir_nextDomain : IK IR (nextDomain (Z := Unit)) := by
  unfold nextDomain; repeat' (first | ik_step0 | ik_unfold)

theorem ir_tsa (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    IK IR (tcbSchedAction (Z := Unit) act t) := by
  intro σ h y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  rw [e]; exact h

/-! ## `awaken` -/

/-- The bundle at `schedule`'s entry. -/
abbrev AX (s : State Unit) : Prop := AW s ∧ RBk false s ∧ IR s

theorem rbf_tcbReleaseDequeue : RBK false (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_assert _) fun _ => ik_bind (rb_tcbReleaseRemove _) fun _ => ?_
  intro σ h y hy
  exact rb_possibleSwitchTo_p _ σ (fun e => by cases e) h y hy

theorem ax_awaken : IK AX (awaken (Z := Unit)) := by
  intro σ h y hy
  refine ⟨aw_awaken σ h.1 y hy, ?_, ?_⟩
  · unfold awaken at hy
    exact ik_whileLoop (fun _ => rbf_tcbReleaseDequeue) () σ h.2.1 y hy
  · unfold awaken at hy
    refine ik_whileLoop (fun _ => ?_) () σ h.2.2 y hy
    unfold tcbReleaseDequeue
    refine ik_bind (ik_gets _) fun _ => ik_bind (ik_assert _) fun _ =>
      ik_bind (ir_tcbReleaseRemove _) fun _ => ir_possibleSwitchTo _

theorem ax_checkDomainTime : IK AX (checkDomainTime (Z := Unit)) := fun σ h y hy =>
  ⟨aw_checkDomainTime σ h.1 y hy, rb_checkDomainTime σ h.2.1 y hy, ir_checkDomainTime σ h.2.2 y hy⟩

/-! ## Switching -/

/-- After a switch, before `resume_cur_thread`: the new current thread is not
released and is a runnable TCB or idle. -/
abbrev CT (s : State Unit) : Prop :=
  RBk false s ∧ s.schedulerAction ≠ .resumeCurThread ∧ s.curThread ∉ s.releaseQueue ∧
    (RnH s.curThread s.kheap ∨ s.curThread = s.idleThread)

/-- `RBk false` with a new current thread off `resume_cur_thread`. -/
theorem rbf_ct {s : State Unit} (h : RBk false s) (hn : s.schedulerAction ≠ .resumeCurThread) (c : ObjRef) :
    RBk false { s with curThread := c } :=
  ⟨⟨h.1.1, (fun e => by cases e), fun hs => absurd hs hn⟩, fun hs => absurd hs hn⟩

/-- The switch's precondition: a queued thread or the switch target. -/
abbrev SW (t : ObjRef) (s : State Unit) : Prop :=
  SchedQ s ∧ RBk false s ∧ s.schedulerAction ≠ .resumeCurThread ∧
    ((∃ d p, t ∈ s.readyQueues d p) ∨ s.schedulerAction = .switchThread t)

theorem ct_switchToThread (t : ObjRef) : HK1 (SW t) CT (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨hq, hb, hn, hm⟩ := hσ
  have hw1 : SchedQ w.2 := ⟨tq_archSwitchToThread t σ hq.1 w hw, sa_archSwitchToThread t σ hq.2 w hw⟩
  have hw2 : RBk false w.2 := rb_archSwitchToThread t σ hb w hw
  have hf := ff_archSwitchToThread t σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ w hw
  -- the thread is a runnable TCB and not released at `w`
  have hT : RnH t w.2.kheap ∧ t ∉ w.2.releaseQueue := by
    rcases hm with ⟨d, p, hm⟩ | hs
    · have hm' : t ∈ w.2.readyQueues d p := by rw [hf.1]; exact hm
      obtain ⟨x, hx, -, -, hr⟩ := hw1.1.1 d p t hm'
      exact ⟨⟨x, hx, hr⟩, hw2.1.1.1 d p t hm'⟩
    · have hs' : w.2.schedulerAction = .switchThread t := by rw [hf.2.2]; exact hs
      exact ⟨hw1.2.1 t hs', hw2.1.1.2 t hs'⟩
  obtain ⟨v, hv, hy⟩ := hy
  have hv2 := rb_dequeue t w.2 hw2 v hv
  obtain ⟨x, -, ev⟩ := q1_tsa_out hv
  rw [Set.mem_singleton_iff.1 hy]
  have hn' : v.2.schedulerAction ≠ .resumeCurThread := by rw [ev, hf.2.2]; exact hn
  refine ⟨rbf_ct hv2 hn' t, hn', ?_, Or.inl ?_⟩
  · show t ∉ v.2.releaseQueue
    rw [ev]; exact hT.2
  · show RnH t v.2.kheap
    rw [ev]; exact hT.1

theorem ct_guardedSwitchTo (t : ObjRef) : HK1 (SW t) CT (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assertOpt _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assert _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_assert _)) fun _ => ?_
  exact ct_switchToThread t

theorem ct_switchToIdleThread :
    HK1 (fun s => RBk false s ∧ s.schedulerAction ≠ .resumeCurThread ∧ IR s) CT (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨hb, hn, hi⟩ := hσ
  have hw2 : RBk false w.2 := rb_archSwitchToIdleThread σ hb w hw
  have hw3 : IR w.2 := ir_archSwitchToIdleThread σ hi w hw
  have hf := ff_archSwitchToIdleThread σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ w hw
  rw [Set.mem_singleton_iff.1 hy]
  have hn' : w.2.schedulerAction ≠ .resumeCurThread := by rw [hf.2.2]; exact hn
  refine ⟨rbf_ct hw2 hn' σ.idleThread, hn', ?_, Or.inr ?_⟩
  · show σ.idleThread ∉ w.2.releaseQueue
    rw [← hf.2.1]; exact hw3
  · show σ.idleThread = w.2.idleThread
    exact hf.2.1.symm

/-- `set_max` of a nonempty set of priorities is in the set. -/
theorem setMax_mem8 {S : Set Priority} (h : ∃ x, x ∈ S) : setMax S ∈ S := by
  obtain ⟨x, hx⟩ := h
  let P : ℕ → Prop := fun n => ∃ y ∈ S, y.toNat = n
  have hlt : ∀ y : Priority, y.toNat ≤ 255 := fun y => by
    have : y.toNat < 256 := y.isLt
    omega
  have hP : P (Nat.findGreatest P 255) := Nat.findGreatest_spec (P := P) (m := x.toNat) (hlt x) ⟨x, hx, rfl⟩
  obtain ⟨m, hm, hmn⟩ := hP
  have hle : ∀ y ∈ S, y ≤ m := fun y hy => by
    rw [BitVec.le_def, hmn]
    exact Nat.le_findGreatest (hlt y) ⟨y, hy, rfl⟩
  have hu : ∃! z, z ∈ S ∧ ∀ y ∈ S, y ≤ z :=
    ⟨m, ⟨hm, hle⟩, fun z hz => BitVec.le_antisymm (hle z hz.1) (hz.2 m hm)⟩
  unfold setMax The
  rw [dif_pos hu]
  exact (Classical.choose_spec hu).1.1

theorem ct_chooseThread :
    HK1 (fun s => SchedQ s ∧ RBk false s ∧ s.schedulerAction ≠ .resumeCurThread ∧ IR s) CT
      (chooseThread (Z := Unit)) := by
  unfold chooseThread
  intro σ hσ y hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  dsimp only at hy
  split at hy
  · exact ct_switchToIdleThread σ ⟨hσ.2.1, hσ.2.2.1, hσ.2.2.2⟩ y hy
  · rename_i hne
    refine ct_guardedSwitchTo _ σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, Or.inl ⟨σ.curDomain, setMax {prio | σ.readyQueues σ.curDomain prio ≠ []}, ?_⟩⟩ y hy
    unfold maxNonEmptyQueue
    have hS : setMax {prio | σ.readyQueues σ.curDomain prio ≠ []} ∈ {prio | σ.readyQueues σ.curDomain prio ≠ []} := by
      refine setMax_mem8 ?_
      by_contra hc
      exact hne fun p => by
        by_contra hp; exact hc ⟨p, hp⟩
    exact the_head_mem hS

theorem rbf_setResume : HK1 CT (RBk false) (setSchedulerAction (Z := Unit) .resumeCurThread) := by
  intro s hs y hy
  unfold setSchedulerAction at hy
  rw [Set.mem_singleton_iff.1 hy]
  obtain ⟨hb, -, h3, h4⟩ := hs
  exact ⟨⟨⟨hb.1.1.1, (fun t ht => by cases ht)⟩, (fun e => by cases e), fun _ => h3⟩, fun _ => h4⟩

/-- `schedule_choose_new_thread` from SchedQ off `resume_cur_thread`. -/
abbrev SN (s : State Unit) : Prop :=
  SchedQ s ∧ RBk false s ∧ s.schedulerAction ≠ .resumeCurThread ∧ IR s

theorem sn_of {α : Type} {m : NonDet (State Unit) α} (h1 : TQK m) (h2 : SAK m) (h3 : RBK false m) (h4 : IK IR m)
    (hf : ∀ Q I A, IK (FF Q I A) m) : IK SN m := by
  intro σ hσ y hy
  have hf' := hf σ.readyQueues σ.idleThread σ.schedulerAction σ ⟨rfl, rfl, rfl⟩ y hy
  exact ⟨⟨h1 σ hσ.1.1 y hy, h2 σ hσ.1.2 y hy⟩, h3 σ hσ.2.1 y hy, by rw [hf'.2.2]; exact hσ.2.2.1,
    h4 σ hσ.2.2.2 y hy⟩

theorem rbf_scheduleChooseNewThread : HK1 SN (RBk false) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine hk1_bind (R := SN) (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (R := SN) (hk1_of_ik' ?_) fun _ => ?_
  · exact ik_when _ (ik_bind (sn_of tq_archPrepareNextDomain sa_archPrepareNextDomain rb_archPrepareNextDomain
      ir_archPrepareNextDomain ff_archPrepareNextDomain)
      fun _ => sn_of tq_nextDomain sa_nextDomain rb_nextDomain ir_nextDomain ff_nextDomain)
  exact hk1_bind ct_chooseThread fun _ => rbf_setResume

/-! ## `schedule` -/

/-- The current thread enqueued after `schedulable` read it. -/
theorem ax_enq_ct (σ : State Unit) (act : ObjRef → List ObjRef → List ObjRef)
    (hact : ∀ q u, u ∈ act σ.curThread q → u ∈ q ∨ u = σ.curThread)
    (hs : schedulable σ.curThread σ = true) (hn : σ.schedulerAction ≠ .resumeCurThread)
    (Q : State Unit → Prop)
    (hQ : ∀ s, SchedQ s → IdleNR s → RBk false s → IR s → s.schedulerAction = σ.schedulerAction → Q s) :
    HKp AX Q σ (tcbSchedAction (Z := Unit) act σ.curThread) := by
  intro h y hy
  have h1 := tq_enq_p act _ σ hact (schedulable_rn hs) h.1.1.1 y hy
  have h2 := sa_enq_p act _ σ hact (Or.inl hn) h.1.1.2 y hy
  have hr : σ.curThread ∉ σ.releaseQueue := by unfold schedulable at hs; exact (of_decide_eq_true hs).2.2
  have h3 := rbe_enq (k := false) act _ hact σ ⟨⟨h.2.1.1, hr, fun e => by cases e⟩, h.2.1.2⟩ y hy
  obtain ⟨x, -, e⟩ := q1_tsa_out hy
  exact hQ _ ⟨h1, h2⟩ (by rw [e]; exact h.1.2.2) ⟨h3.1.1, h3.2⟩ (by rw [e]; exact h.2.2) (by rw [e])

/-- The switch branch's invariant. -/
abbrev PX (c : ObjRef) (s : State Unit) : Prop :=
  SchedQ s ∧ IdleNR s ∧ s.schedulerAction = .switchThread c ∧ RBk false s ∧ IR s

/-- The candidate (the switch target: not released) enqueued / appended. -/
theorem px_tsa (c : ObjRef) (act : ObjRef → List ObjRef → List ObjRef)
    (hact : ∀ q u, u ∈ act c q → u ∈ q ∨ u = c) : HK1 (PX c) (PX c) (tcbSchedAction (Z := Unit) act c) := by
  intro s hs y hy
  obtain ⟨hq, hi, ha, hb, hr⟩ := hs
  have h1 := p1_tsa c act hact s ⟨hq, hi, ha⟩ y hy
  have h3 := rbe_enq (k := false) act c hact s ⟨⟨hb.1, hb.1.1.2 c ha, fun e => by cases e⟩, hb.2⟩ y hy
  exact ⟨h1.1, h1.2.1, h1.2.2, ⟨h3.1.1, h3.2⟩, ir_tsa act c s hr y hy⟩

theorem px_setCn (c : ObjRef) : HK1 (PX c) SN (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  intro s hs y hy
  have h1 := p1_setCn c s ⟨hs.1, hs.2.1, hs.2.2.1⟩ y hy
  have h2 := rb_setCn (k := false) s hs.2.2.2.1 y hy
  unfold setSchedulerAction at hy
  rw [Set.mem_singleton_iff.1 hy] at h1 h2 ⊢
  exact ⟨h1.1.1, h2, h1.1.2, hs.2.2.2.2⟩

theorem px_guarded (c : ObjRef) : HK1 (PX c) CT (guardedSwitchTo (Z := Unit) c) :=
  fun s hs => ct_guardedSwitchTo c s ⟨hs.1, hs.2.2.2.1, (by rw [hs.2.2.1]; exact fun e => by cases e),
    Or.inr hs.2.2.1⟩

/-- **`schedule` keeps `RBk false`** (from `AW`). -/
theorem rbf_schedule : HK1 AX (RBk false) (schedule (Z := Unit)) := by
  unfold schedule
  refine hk1_bind (R := AX) (hk1_of_ik' ax_awaken) fun _ => ?_
  refine hk1_bind (R := AX) (hk1_of_ik' ax_checkDomainTime) fun _ => ?_
  intro σ
  show HKp AX (RBk false) σ _
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  refine hkp_gets_bind ?_
  try dsimp only
  split
  · -- resume
    exact fun h y hy => rb_scAndTimer σ h.2.1 y hy
  · -- choose_new_thread
    rename_i heq
    refine hkp_bind (R := SN) ?_ fun _ => hk1_bind rbf_scheduleChooseNewThread fun _ => rb_scAndTimer
    have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [heq]; exact fun e => absurd e (by simp)
    refine hkp_when _ (fun hs => ax_enq_ct σ _ (q1_enq _) hs hn SN fun s h1 _ h3 h4 h5 =>
      ⟨h1, h3, by rw [h5]; exact hn, h4⟩) fun _ h => ⟨h.1.1, h.2.1, hn, h.2.2⟩
  · -- switch_thread candidate
    rename_i c heq
    have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [heq]; exact fun e => absurd e (by simp)
    refine hkp_bind (R := RBk false) ?_ fun _ => rb_scAndTimer
    unfold scheduleSwitchThreadBranch
    refine hkp_bind (R := PX c) ?_ fun _ => ?_
    · exact hkp_when _ (fun hs => ax_enq_ct σ _ (q1_enq _) hs hn (PX c) fun s h1 h2 h3 h4 h5 =>
        ⟨h1, h2, h5.trans heq, h3, h4⟩) fun _ h => ⟨h.1.1, h.1.2.2, heq, h.2.1, h.2.2⟩
    refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
    refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
    dsimp only
    split <;> refine hk1_bind (hk1_of_ik' (by first | exact ik_threadGet_any _ _ _ | exact ik_pure _)) fun _ => ?_
    all_goals
      refine hk1_bind (hk1_of_ik' (ik_fastfail _ _ _ _ _)) fun _ => ?_
      refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
      refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
      refine hk1_ite _ ?_ (hk1_ite _ ?_ ?_)
      · exact hk1_bind (px_tsa c _ (q1_enq c)) fun _ => hk1_bind (px_setCn c) fun _ => rbf_scheduleChooseNewThread
      · exact hk1_bind (px_tsa c _ (q1_app c)) fun _ => hk1_bind (px_setCn c) fun _ => rbf_scheduleChooseNewThread
      · exact hk1_bind (px_guarded c) fun _ => rbf_setResume

/-- At `resume_cur_thread`, with SchedQ, `RBk false` is `RB`. -/
theorem rb_of_rs {s : State Unit} (h : RBk false s) (hq : SchedQ s) (hr : RS s) : RB s :=
  ⟨⟨h.1.1, fun _ => ⟨ctq_of_rs hq hr, (fun e => by rw [hr] at e; cases e), h.1.2.2 hr⟩, h.1.2.2⟩, h.2⟩

/-- **The kernel exit gives `RB`** (from `AW` and `RBk false`). -/
theorem rb_exit : HK1 (fun s => AW s ∧ RBk false s) RB (schedule (Z := Unit) >>= fun _ => activateThread) := by
  intro σ h y ⟨z, hz, hy⟩
  have hx : AX σ := ⟨h.1, h.2, ir_of_aw h.1⟩
  have h1 := rbf_schedule σ hx z hz
  have h2 := rs_schedule σ trivial z hz
  have h3 := sq_schedule σ h.1 z hz
  exact rb_activateThread z.2 (rb_of_rs h1 h3 h2) y hy

/-- **The kernel exit**: EX and RB. -/
theorem exR_exit : HK1 (fun s => AW s ∧ RBk false s) (fun s => EX s ∧ RB s)
    (schedule (Z := Unit) >>= fun _ => activateThread) :=
  fun σ h y hy => ⟨ex_exit σ h.1 y hy, rb_exit σ h y hy⟩

end

end Fl4Proofs.P3.SInvQ
