/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd4): **the exit glue:
`Rdy ∧ OffReady` after `schedule`** (spec side only, outside the `JAtZ` cone;
KENTRY-PLAN rd3 handoff 1-2).

* `FK`: the heap with the TCB arch fields erased (`HV`), the current SC,
  consumed time, time and idle pointers, fixed. `schedule`'s body up to
  `sc_and_timer` writes only TCB arch fields (`lazy_fpu_restore`'s owner
  flags, `as_user`), the queues, the action, the current thread and the domain
  fields: `fk_awaken`, `fk_checkDomainTime`, `fk_scheduleChooseNewThread`,
  `fk_scheduleSwitchThreadBranch`, `fk_tcbSchedAction`.
* `NR`: the action is not `resume_cur_thread`; `awaken` / `check_domain_time`
  keep it (they set only `switch_thread` / `choose_new_thread`), so the resume
  branch of `schedule` was taken at a state whose action was already resume.
* **`IdleHd σ`** (a state fact; l4v: the idle SC is created with refills at time
  0 and is never charged, `commit_time` skips it): the idle SC has refills and
  its head is not in the future.
* **`SE σ s`**: the facts at `sc_and_timer`'s start: `FK` w.r.t. `σ`, `Rdy`,
  `SchedQ`, action resume, and the new current thread is idle, or `RdyT` and
  runnable (a queue head by R1 / RQd, or the switch target by R2 / RA), or the
  old current thread with the old action resume.
* **`rd_exitSE`**: `SE σ s` with the state facts at `σ` (`ScBackS`, `RNE`,
  `ValidIdle`, `IdleHd`, the current SC an SC, ct bound to `cur_sc` when the
  action is resume, and the **overrun disjunct** `(OffReady ∧ Suff) ∨
  (consumed = 0 ∧ action ≠ resume)`) gives `Rdy ∧ OffReady` after `sc_and_timer`
  (rd1's `sw_out`, generalised in SpecInvRdB to the overrun case). With
  consumed time 0 and `OffReady` false, no `RdyT` thread and not the idle
  thread can be bound to `cur_sc`, so the switch changes SC.
* **`rd_scheduleOff`**: `schedule` from `Rdy ∧ RNE ∧ CtR ∧ AW` and the state
  facts above ends with `Rdy ∧ OffReady`.
-/
import Fl4Proofs.P3.SpecInvRdX
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The heap view without TCB arch fields -/

/-- A TCB with its arch field erased. -/
def hvT (x : Tcb) : Tcb := { x with tcbArch := default }

/-- An object with a TCB's arch field erased. -/
def hvK : KernelObject → KernelObject
  | .tcb x => .tcb (hvT x)
  | k => k

/-- The heap view. -/
def HV (o : Option KernelObject) : Option KernelObject := o.map hvK

theorem hv_tcb {o : Option KernelObject} {x : Tcb} (h : HV o = HV (some (.tcb x))) :
    ∃ x', o = some (.tcb x') ∧ hvT x' = hvT x := by
  rcases o with _ | k
  · cases h
  · cases k with
    | tcb x' => exact ⟨x', rfl, by injection h with h; injection h⟩
    | _ => injection h with h; cases h

theorem hv_nt {o : Option KernelObject} {k : KernelObject} (hk : ∀ x, k ≠ .tcb x) (h : HV o = HV (some k)) :
    o = some k := by
  rcases o with _ | k'
  · cases h
  · have e : hvK k' = hvK k := by injection h
    cases k with
    | tcb x => exact absurd rfl (hk x)
    | _ =>
      cases k' with
      | tcb x' => cases e
      | _ => cases e <;> rfl

theorem hvT_sc {x x' : Tcb} (h : hvT x' = hvT x) : x'.tcbSchedContext = x.tcbSchedContext := by
  have e := congrArg Tcb.tcbSchedContext h; exact e

theorem hvT_st {x x' : Tcb} (h : hvT x' = hvT x) : x'.tcbState = x.tcbState := by
  have e := congrArg Tcb.tcbState h; exact e

/-- An SC object is read the same through equal views. -/
theorem hv_sc {o o' : Option KernelObject} (h : HV o' = HV o) {y : SchedContext} {n : Nat} :
    o' = some (.schedContext y n) ↔ o = some (.schedContext y n) := by
  constructor
  · intro e; rw [e] at h; exact hv_nt (fun _ e => by cases e) h.symm
  · intro e; rw [e] at h; exact hv_nt (fun _ e => by cases e) h

/-- Heap view, current SC, consumed time, time, idle pointers fixed. -/
abbrev FK (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef)
    (s : State Unit) : Prop :=
  (∀ q, HV (s.kheap q) = HV (K q)) ∧ s.curSc = c ∧ s.consumedTime = u ∧ s.curTime = T ∧
    s.idleThread = I ∧ s.idleSc = S

/-- `FK` at its own state. -/
theorem fk_self (s : State Unit) : FK s.kheap s.curSc s.consumedTime s.curTime s.idleThread s.idleSc s :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fk_trans {K : ObjRef → Option KernelObject} {c : ObjRef} {u : Ticks} {T : Time} {I S : ObjRef}
    {s s' : State Unit} (h : FK K c u T I S s)
    (h' : FK s.kheap s.curSc s.consumedTime s.curTime s.idleThread s.idleSc s') : FK K c u T I S s' :=
  ⟨fun q => (h'.1 q).trans (h.1 q), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

section Leaves
variable (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef)

theorem fk_setTcb (p : ObjRef) (x y : Tcb) (σ : State Unit) (hx : σ.kheap p = some (.tcb x))
    (hy : hvT y = hvT x) : IKp (FK K c u T I S) σ (setObject (Z := Unit) p (.tcb y)) := by
  unfold setObject
  intro hσ r ⟨z, hz, hr⟩
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨z1, z2⟩ := z
  simp only at hk hs; subst hs
  obtain ⟨w, ⟨-, rfl⟩, hr⟩ := hr
  obtain ⟨v, hv, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hv] at hr
  rw [Set.mem_singleton_iff.1 hr]
  refine ⟨fun q => ?_, hσ.2⟩
  by_cases e : q = p
  · subst e
    try dsimp only
    rw [Function.update_self, ← hσ.1 q, hx]
    show some (KernelObject.tcb (hvT y)) = some (.tcb (hvT x))
    rw [hy]
  · try dsimp only
    rw [Function.update_of_ne e]; exact hσ.1 q

theorem fk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) :
    IK (FK K c u T I S) (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact ik_getsThe_bind fun x σ hx => fk_setTcb K c u T I S _ x _ σ (getTcb_kheap hx) rfl

theorem fk_asUser {α : Type} (t : ObjRef) (m : UserMonad α) : IK (FK K c u T I S) (asUser (Z := Unit) t m) := by
  unfold asUser
  refine ik_getsThe_bind fun x σ hx => ?_
  refine ikp_keep (fun y hy => by rw [Set.mem_singleton_iff.1 hy]) fun uc => ?_
  refine ikp_keep (fun y hy => hy.2) fun r => ?_
  obtain ⟨a, uc'⟩ := r
  dsimp only
  refine ikp_pure_bind ?_
  exact ikp_bind (fk_setTcb K c u T I S _ x _ σ (getTcb_kheap hx) rfl) fun _ => ik_pure _

end Leaves

macro "fk_auto" : tactic => `(tactic| repeat' (first | (with_reducible exact fk_archThreadSet _ _ _ _ _ _ _ _) | (with_reducible exact fk_asUser _ _ _ _ _ _ _ _) | ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h) | ((with_reducible refine ik_doExtendedOp ?_ _); intro _ _ h; exact h) | ik_step0 | ik_unfold))

section Frames
variable (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef)

theorem fk_archSwitchToThread (t : ObjRef) : IK (FK K c u T I S) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; fk_auto

theorem fk_archSwitchToIdleThread : IK (FK K c u T I S) (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; fk_auto

theorem fk_archPrepareNextDomain : IK (FK K c u T I S) (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; fk_auto

theorem fk_nextDomain : IK (FK K c u T I S) (nextDomain (Z := Unit)) := by
  unfold nextDomain; fk_auto

theorem fk_tcbSchedAction (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    IK (FK K c u T I S) (tcbSchedAction (Z := Unit) act t) := by
  unfold tcbSchedAction; fk_auto

theorem fk_rescheduleRequired : IK (FK K c u T I S) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  repeat' (first | (with_reducible exact fk_tcbSchedAction _ _ _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_possibleSwitchTo (t : ObjRef) : IK (FK K c u T I S) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo
  repeat' (first | (with_reducible exact fk_tcbSchedAction _ _ _ _ _ _ _ _) | (with_reducible exact fk_rescheduleRequired _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_tcbReleaseRemove (t : ObjRef) : IK (FK K c u T I S) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; fk_auto

theorem fk_awaken : IK (FK K c u T I S) (awaken (Z := Unit)) := by
  unfold awaken
  refine ik_whileLoop (fun _ => ?_) _
  unfold tcbReleaseDequeue
  repeat' (first | (with_reducible exact fk_tcbReleaseRemove _ _ _ _ _ _ _) | (with_reducible exact fk_possibleSwitchTo _ _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_checkDomainTime : IK (FK K c u T I S) (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime
  repeat' (first | (with_reducible exact fk_rescheduleRequired _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_switchToThread (t : ObjRef) : IK (FK K c u T I S) (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  repeat' (first | (with_reducible exact fk_archSwitchToThread _ _ _ _ _ _ _) | (with_reducible exact fk_tcbSchedAction _ _ _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_switchToIdleThread : IK (FK K c u T I S) (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  repeat' (first | (with_reducible exact fk_archSwitchToIdleThread _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_guardedSwitchTo (t : ObjRef) : IK (FK K c u T I S) (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  repeat' (first | (with_reducible exact fk_switchToThread _ _ _ _ _ _ _) | ik_step0 | ik_unfold)

theorem fk_chooseThread : IK (FK K c u T I S) (chooseThread (Z := Unit)) := by
  unfold chooseThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_gets _) fun _ => ?_
  split
  · exact fk_switchToIdleThread _ _ _ _ _ _
  · exact fk_guardedSwitchTo _ _ _ _ _ _ _

theorem fk_scheduleChooseNewThread : IK (FK K c u T I S) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (ik_bind (fk_archPrepareNextDomain _ _ _ _ _ _)
    fun _ => fk_nextDomain _ _ _ _ _ _)) fun _ => ik_bind (fk_chooseThread _ _ _ _ _ _) fun _ => ?_
  unfold setSchedulerAction; exact ik_modify fun _ h => h

end Frames

/-! ## The action is not resume -/

abbrev NR (s : State Unit) : Prop := s.schedulerAction ≠ .resumeCurThread

theorem nr_set (a : SchedulerAction) (ha : a ≠ .resumeCurThread) : IK NR (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact ik_modify fun _ _ => ha

theorem nr_tcbSchedAction (act : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    IK NR (tcbSchedAction (Z := Unit) act t) := by
  unfold tcbSchedAction; repeat' (first | ik_step0 | ik_unfold)

theorem nr_rescheduleRequired : IK NR (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  repeat' (first | ((with_reducible refine nr_set _ ?_); exact fun e => by cases e) | (with_reducible exact nr_tcbSchedAction _ _) | ik_step0 | ik_unfold)

theorem nr_possibleSwitchTo (t : ObjRef) : IK NR (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo
  repeat' (first | ((with_reducible refine nr_set _ ?_); exact fun e => by cases e) | (with_reducible exact nr_tcbSchedAction _ _) | (with_reducible exact nr_rescheduleRequired) | ik_step0 | ik_unfold)

theorem nr_awaken : IK NR (awaken (Z := Unit)) := by
  unfold awaken
  refine ik_whileLoop (fun _ => ?_) _
  unfold tcbReleaseDequeue tcbReleaseRemove
  repeat' (first | (with_reducible exact nr_possibleSwitchTo _) | ik_step0 | ik_unfold)

theorem nr_checkDomainTime : IK NR (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime
  repeat' (first | (with_reducible exact nr_rescheduleRequired) | ik_step0 | ik_unfold)

/-! ## The new current thread -/

theorem ct_switchToThread (t : ObjRef) (s : State Unit) {y : Unit × State Unit}
    (hy : y ∈ (switchToThread (Z := Unit) t s).1) : y.2.curThread = t := by
  unfold switchToThread at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨w, -, hy⟩ := hy
  obtain ⟨v, -, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]

theorem ct_guardedSwitchTo (t : ObjRef) (s : State Unit) {y : Unit × State Unit}
    (hy : y ∈ (guardedSwitchTo (Z := Unit) t s).1) : y.2.curThread = t := by
  unfold guardedSwitchTo at hy
  obtain ⟨z1, -, hy⟩ := hy
  obtain ⟨z2, -, hy⟩ := hy
  obtain ⟨z3, -, hy⟩ := hy
  obtain ⟨z4, -, hy⟩ := hy
  obtain ⟨z5, -, hy⟩ := hy
  obtain ⟨z6, -, hy⟩ := hy
  obtain ⟨z7, -, hy⟩ := hy
  exact ct_switchToThread t _ hy

theorem ct_switchToIdleThread (s : State Unit) {y : Unit × State Unit}
    (hy : y ∈ (switchToIdleThread (Z := Unit) s).1) : y.2.curThread = s.idleThread := by
  unfold switchToIdleThread at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨w, -, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]

theorem ofNat_toNat8 (x : Priority) : BitVec.ofNat 8 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt)

/-- A non-empty ready-queue family's maximal queue is non-empty. -/
theorem mneq_ne {queues : Priority → ReadyQueue} (h : ¬ ∀ prio, queues prio = []) :
    maxNonEmptyQueue queues ≠ [] := by
  push_neg at h
  obtain ⟨q, hq⟩ := h
  have mem : ∀ x : Priority, queues x ≠ [] →
      x.toNat ∈ (Finset.range 256).filter (fun i => queues (BitVec.ofNat 8 i) ≠ []) := fun x hx =>
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_lt_of_eq x.isLt (by norm_num)), by rw [ofNat_toNat8]; exact hx⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image ((Finset.range 256).filter fun i => queues (BitVec.ofNat 8 i) ≠ [])
    id ⟨q.toNat, mem q hq⟩
  obtain ⟨hi1, hm'⟩ := Finset.mem_filter.1 hi
  have hit : (BitVec.ofNat 8 i).toNat = i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (Finset.mem_range.1 hi1) (by norm_num))
  unfold maxNonEmptyQueue
  rw [Sched.setMax_eq (S := {prio | queues prio ≠ []}) (m := BitVec.ofNat 8 i) hm' (fun x hx => by
    rw [BitVec.le_def, hit]; exact hmax _ (mem x hx))]
  exact hm'

/-- RdyT and runnability through equal heap views and equal time. -/
theorem rdyT_hv {s s' : State Unit} (hk : ∀ q, HV (s'.kheap q) = HV (s.kheap q)) (ht : s'.curTime = s.curTime)
    {t : ObjRef} (h : RdyT s t) : RdyT s' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha, hr⟩ := h
  obtain ⟨x', hx', ex⟩ := hv_tcb (by rw [hk t, hx])
  exact ⟨x', c, y, n, hx', by rw [hvT_sc ex]; exact hc, (hv_sc (hk c)).2 hy, ha, by rw [ht]; exact hr⟩

theorem rnH_hv {s s' : State Unit} (hk : ∀ q, HV (s'.kheap q) = HV (s.kheap q)) {t : ObjRef}
    (h : RnH t s.kheap) : RnH t s'.kheap := by
  obtain ⟨x, hx, hr⟩ := h
  obtain ⟨x', hx', ex⟩ := hv_tcb (by rw [hk t, hx])
  exact ⟨x', hx', by rw [hvT_st ex]; exact hr⟩

/-- **`schedule_choose_new_thread`**: the new current thread is idle, or a
queue head (`RdyT` by R1, runnable by RQd); the action is resume. -/
theorem se_chooseNew (w : State Unit) (hR : Rdy w) (hQ : RQd w) {v : Unit × State Unit}
    (hv : v ∈ (scheduleChooseNewThread (Z := Unit) w).1) :
    v.2.schedulerAction = .resumeCurThread ∧
      (v.2.curThread = v.2.idleThread ∨ (RdyT v.2 v.2.curThread ∧ RnH v.2.curThread v.2.kheap)) := by
  unfold scheduleChooseNewThread at hv
  obtain ⟨z, hz, hv⟩ := hv
  rw [Set.mem_singleton_iff.1 hz] at hv
  obtain ⟨u1, hu1, hv⟩ := hv
  -- the domain step keeps Rdy and RQd
  have hu : Rdy u1.2 ∧ RQd u1.2 := by
    refine ⟨(?_ : RdK _) w hR u1 hu1, ((?_ : TQK _) w ⟨hQ, trivial⟩ u1 hu1).1⟩
    · exact ik_when _ (ik_bind (by rd_auto) fun _ => by rd_auto)
    · exact ik_when _ (ik_bind tq_archPrepareNextDomain fun _ => tq_nextDomain)
  obtain ⟨u2, hu2, hv⟩ := hv
  rw [Set.mem_singleton_iff.1 hv]
  refine ⟨rfl, ?_⟩
  show u2.2.curThread = u2.2.idleThread ∨ (RdyT u2.2 u2.2.curThread ∧ RnH u2.2.curThread u2.2.kheap)
  have hF := fk_chooseThread _ _ _ _ _ _ u1.2 (fk_self u1.2) u2 hu2
  unfold chooseThread at hu2
  obtain ⟨y1, hy1, hu2⟩ := hu2
  rw [Set.mem_singleton_iff.1 hy1] at hu2
  obtain ⟨y2, hy2, hu2⟩ := hu2
  rw [Set.mem_singleton_iff.1 hy2] at hu2
  dsimp only at hu2
  split at hu2
  · left; rw [ct_switchToIdleThread _ hu2, hF.2.2.2.2.1]
  · rename_i hne
    right
    rw [ct_guardedSwitchTo _ _ hu2]
    have hm : the (maxNonEmptyQueue (u1.2.readyQueues u1.2.curDomain)).head? ∈
        u1.2.readyQueues u1.2.curDomain (setMax {prio | u1.2.readyQueues u1.2.curDomain prio ≠ []}) :=
      SInvQ.the_head_mem (mneq_ne hne)
    obtain ⟨x, hx, -, -, hrn⟩ := hu.2 _ _ _ hm
    exact ⟨rdyT_hv hF.1 hF.2.2.2.1 (hu.1.1 _ _ _ hm), rnH_hv hF.1 ⟨x, hx, hrn⟩⟩

/-! ## The current thread is kept by `awaken` -/

abbrev CTK (c : ObjRef) (s : State Unit) : Prop := s.curThread = c

theorem ctk_awaken (c : ObjRef) : IK (CTK c) (awaken (Z := Unit)) := by
  unfold awaken
  refine ik_whileLoop (fun _ => ?_) _
  unfold tcbReleaseDequeue
  repeat' (first | ik_step0 | ik_unfold)

/-! ## The state at `sc_and_timer` -/

/-- `IdleHd` (defined in SpecInvRdA since rd5, `Rdy`'s sixth conjunct) at boot (non-vacuity). -/
theorem boot_idleHd : IdleHd (initASt (Z := Unit)) := boot_rdy.2.2.2.2.2

/-- **The facts at `sc_and_timer`'s start** (module docstring). -/
def SE (σ s : State Unit) : Prop :=
  FK σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc s ∧ Rdy s ∧ SchedQ s ∧
    s.schedulerAction = .resumeCurThread ∧
    (s.curThread = s.idleThread ∨ (RdyT s s.curThread ∧ RnH s.curThread s.kheap) ∨
      (s.curThread = σ.curThread ∧ σ.schedulerAction = .resumeCurThread))

theorem blkR_nr {ts : ThreadState} {f : Option Fault} (h : BlkR ts f) : runnable ts = false := by
  rcases h with ⟨n, rfl⟩ | ⟨e, d, rfl, -⟩ | ⟨e, r, d, rfl⟩ <;> rfl

theorem nblk_idle {f : Option Fault} : ¬ BlkR .idleThreadState f := by
  rintro (⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩) <;> cases h

theorem ready_nat {T : Time} {r : Refill} (h : refillReady T r = true) : r.rTime.toNat ≤ T.toNat := by
  have : r.rTime ≤ T := by simpa [refillReady'] using h
  exact BitVec.le_def.mp this

theorem sat_bound {s : State Unit} {r : Unit × State Unit} (hr : r ∈ (scAndTimer (Z := Unit) s).1) :
    ∃ xt p, s.kheap s.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some p := by
  unfold scAndTimer at hr
  obtain ⟨z, hz, -⟩ := hr
  unfold switchSchedContext at hz
  rw [Notif.nd_gets_bind, Notif.nd_gets_bind] at hz
  obtain ⟨w, hw, hz⟩ := hz
  obtain ⟨xt, hxt, rfl⟩ := q1_mem_threadGet hw
  obtain ⟨v, hv, -⟩ := hz
  obtain ⟨e, -⟩ := cq5_mem_assertOpt hv
  exact ⟨xt, v.1, hxt, e⟩

/-- **The third mid-entry disjunct** (rd14e's FINDING, lead option (a)): the
current SC (not the idle SC) is inactive — its last cap was deleted — and the
action is not resume. `commit_time` then skips it and zeroes the consumed time
(SpecInvRdB's `commit_inactive`), and the new current thread's SC is another
one. -/
def OI (σ : State Unit) : Prop :=
  σ.curSc ≠ σ.idleSc ∧ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → scActive y = false) ∧
    σ.schedulerAction ≠ .resumeCurThread

theorem offReady_fk {σ s : State Unit} (h : Sched.OffReady σ)
    (hF : FK σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc s) : Sched.OffReady s := by
  obtain ⟨hk, hc, hu, ht, -, -⟩ := hF
  intro z k hz
  rw [hc] at hz; rw [hu, ht]
  exact h z k ((hv_sc (hk _)).1 hz)

theorem suff_fk {σ s : State Unit} (h : Suff σ)
    (hF : FK σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc s) : Suff s := by
  obtain ⟨hk, hc, hu, ht, -, hS⟩ := hF
  intro z k hz ha hne
  rw [hc] at hz hne; rw [hS] at hne; rw [hu]
  exact h z k ((hv_sc (hk _)).1 hz) ha hne

/-- **The exit**: `sc_and_timer` from `SE` (module docstring). -/
theorem rd_exitSE {σ s : State Unit} {x : SchedContext} {n : Nat} (hS : SE σ s)
    (hk0 : σ.kheap σ.curSc = some (.schedContext x n))
    (hOS0 : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ σ.schedulerAction ≠ .resumeCurThread) ∨ OI σ)
    (hB : SInvB.ScBackS σ) (hRN : SInvB.RNE σ) (hV : SInvI.ValidIdle σ) (hIH : IdleHd σ)
    (hRC : σ.schedulerAction = .resumeCurThread → ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      x.tcbSchedContext = some σ.curSc)
    {r : Unit × State Unit} (hr : r ∈ (scAndTimer (Z := Unit) s).1) : Rdy r.2 ∧ Sched.OffReady r.2 := by
  obtain ⟨hF, hR, hQ, ha, hN⟩ := hS
  obtain ⟨hFk, hc, hu, ht, hI, hIS⟩ := hF
  obtain ⟨xt, p, hct, hsc⟩ := sat_bound hr
  obtain ⟨x0, hx0, ex0⟩ := hv_tcb ((hFk _).symm.trans (congrArg HV hct))
  have hsc0 : x0.tcbSchedContext = some p := (hvT_sc ex0).trans hsc
  obtain ⟨y, m, hy0, hyT, hyR⟩ := hB _ x0 p hx0 hsc0
  have hy : s.kheap p = some (.schedContext y m) := (hv_sc (hFk p)).2 hy0
  have hk : s.kheap s.curSc = some (.schedContext x n) := by rw [hc]; exact (hv_sc (hFk _)).2 hk0
  -- the three kinds of new current thread
  have HP : (σ.schedulerAction = .resumeCurThread ∧ p = s.curSc) ∨
      (y.scRefills ≠ [] ∧ (refillHd y).rTime.toNat ≤ s.curTime.toNat ∧ ¬ BlkR xt.tcbState xt.tcbFault) := by
    rcases hN with e | ⟨hT, hrn⟩ | ⟨e, hres⟩
    · right
      have hob := SInvI.vi_obj hV hx0
      simp only [SInvI.ObjOK] at hob
      obtain ⟨h1, h2, h3, h4⟩ := hob.1 (by rw [e, hI])
      have hp : p = σ.idleSc := Option.some.inj (hsc0.symm.trans h3)
      rw [hp] at hy0
      obtain ⟨i1, i2⟩ := hIH y m hy0
      refine ⟨i1, by rw [ht]; exact i2, ?_⟩
      rw [← hvT_st ex0, h1]; exact nblk_idle
    · right
      obtain ⟨x1, c1, y1, n1, hx1, hc1, hy1, ha1, hr1⟩ := hT
      rw [hct] at hx1
      cases hx1
      have e1 : c1 = p := Option.some.inj (hc1.symm.trans hsc)
      rw [e1, hy] at hy1
      cases hy1
      obtain ⟨x2, hx2, hr2⟩ := hrn
      rw [hct] at hx2
      cases hx2
      exact ⟨hyR (Or.inr ha1), ready_nat hr1, fun hb => by rw [blkR_nr hb] at hr2; cases hr2⟩
    · left
      refine ⟨hres, ?_⟩
      have := hRC hres x0 (by rw [← e]; exact hx0)
      rw [hc]; exact Option.some.inj (hsc0.symm.trans this)
  have hOS : (Sched.OffReady s ∧ Suff s) ∨ (s.consumedTime = 0 ∧ (p = s.curSc → Sched.OffReady s)) ∨
      (scActive x = false ∧ p ≠ s.curSc) := by
    have hFs : FK σ.kheap σ.curSc σ.consumedTime σ.curTime σ.idleThread σ.idleSc s := ⟨hFk, hc, hu, ht, hI, hIS⟩
    rcases hOS0 with ⟨hO, hSf⟩ | ⟨h0, hna⟩ | ⟨hid, hin, hna⟩
    · exact Or.inl ⟨offReady_fk hO hFs, suff_fk hSf hFs⟩
    · rcases HP with ⟨hres, -⟩ | ⟨-, hrt, -⟩
      · exact absurd hres hna
      · refine Or.inr (Or.inl ⟨hu.trans h0, fun e => ?_⟩)
        intro z k hz
        rw [← e, hy] at hz
        cases hz
        rw [hu, h0]
        simpa using hrt
    · refine Or.inr (Or.inr ⟨hin x n hk0, fun epc => ?_⟩)
      rcases hN with e | ⟨hT, hrn⟩ | ⟨e, hres⟩
      · have hob := SInvI.vi_obj hV hx0
        simp only [SInvI.ObjOK] at hob
        obtain ⟨-, -, h3, -⟩ := hob.1 (by rw [e, hI])
        have hp : p = σ.idleSc := Option.some.inj (hsc0.symm.trans h3)
        exact hid ((hc.symm.trans epc.symm).trans hp)
      · obtain ⟨x1, c1, y1, n1, hx1, hc1, hy1, ha1, -⟩ := hT
        rw [hct] at hx1
        cases hx1
        have e1 : c1 = p := Option.some.inj (hc1.symm.trans hsc)
        rw [e1, hy] at hy1
        cases hy1
        have e2 : some (KernelObject.schedContext y m) = some (.schedContext x n) := by rw [← hy, epc, hk]
        have e3 : y = x := by injection e2 with e; injection e
        rw [e3, hin x n hk0] at ha1
        exact Bool.false_ne_true ha1
      · exact hna hres
  have hne : scActive x = true → x.scRefills ≠ [] := fun h => hRN _ x n hk0 (Or.inr h)
  have hnp : p ≠ s.curSc → y.scRefills ≠ [] := fun hpc => by
    rcases HP with ⟨-, e⟩ | ⟨h1, -, -⟩
    · exact absurd e hpc
    · exact h1
  have hHR : p ≠ s.curSc → (refillHd y).rTime.toNat ≤ s.curTime.toNat := fun hpc => by
    rcases HP with ⟨-, e⟩ | ⟨-, h2, -⟩
    · exact absurd e hpc
    · exact h2
  have hX : p ≠ s.curSc → Excl s p := fun hpc => by
    have hbl : ¬ BlkR xt.tcbState xt.tcbFault := by
      rcases HP with ⟨-, e⟩ | ⟨-, -, h3⟩
      · exact absurd e hpc
      · exact h3
    intro t xx hxx hxp
    obtain ⟨x2, hx2, ex2⟩ := hv_tcb ((hFk t).symm.trans (congrArg HV hxx))
    obtain ⟨y', m', hy', hyT', -⟩ := hB t x2 p hx2 ((hvT_sc ex2).trans hxp)
    rw [hy0] at hy'
    cases hy'
    have et : t = s.curThread := Option.some.inj (hyT'.symm.trans hyT)
    subst et
    rw [hct] at hxx
    cases hxx
    exact ⟨fun d q => hQ.2.2.2 ha d q, (by rw [ha]; exact fun e => by cases e), hbl⟩
  obtain ⟨z1, z2, -⟩ := rd_scAndTimer hR hk hOS hne hct hsc hy hnp hHR hX hr
  exact ⟨z1, z2⟩

/-! ## `schedule`'s branches -/

theorem pp_keep {Q : State Unit → Prop} {σ : State Unit} {α β : Type} {m : NonDet (State Unit) α}
    {k : α → NonDet (State Unit) β} (hm : ∀ y ∈ (m σ).1, y.2 = σ) (h : ∀ a, PostP Q σ (k a)) :
    PostP Q σ (m >>= k) :=
  pp_bind_of fun y hy => by
    have e := hm y hy
    obtain ⟨a, s⟩ := y
    simp only at e
    subst s
    exact h a

/-- The action / current-thread part of `SE` after the switch branch. -/
abbrev AC (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread ∧
    (s.curThread = s.idleThread ∨ (RdyT s s.curThread ∧ RnH s.curThread s.kheap))

theorem ac_chooseAfter {c : ObjRef} (act : ObjRef → List ObjRef → List ObjRef) (hact : ∀ q u, u ∈ act c q → u ∈ q ∨ u = c)
    (w : State Unit) (hR : Rdy w) (hQ : TQ w) (hRc : RdyT w c) (hRn : RnH c w.kheap)
    (hRd : IKp Rdy w (tcbSchedAction (Z := Unit) act c)) :
    PostP AC w (tcbSchedAction (Z := Unit) act c >>= fun _ =>
      setSchedulerAction (Z := Unit) .chooseNewThread >>= fun _ => scheduleChooseNewThread) := by
  refine pp_bind_of fun v1 hv1 => pp_bind_of fun v2 hv2 => fun r hr => ?_
  have rv1 := hRd hR v1 hv1
  have qv1 := tq_enq_p act c w hact hRn hQ v1 hv1
  have rv2 : Rdy v2.2 := rd_setSchedulerAction_ns _ (fun _ h => by cases h) v1.2 rv1 v2 hv2
  have qv2 : RQd v2.2 := by
    unfold setSchedulerAction at hv2; rw [Set.mem_singleton_iff.1 hv2]; exact qv1.1
  exact se_chooseNew v2.2 rv2 qv2 hr

/-- **`schedule_switch_thread_branch`**: the action is resume and the new
current thread idle, or `RdyT` and runnable. -/
theorem ac_sstb (c : ObjRef) (σ : State Unit) (hC : CtR σ) (ha : σ.schedulerAction = .switchThread c)
    (hR : Rdy σ) (hAW : AW σ) :
    PostP AC σ (scheduleSwitchThreadBranch (Z := Unit) c σ.curThread (schedulable σ.curThread σ)) := by
  have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [ha]; exact fun e => absurd e (by simp)
  refine pp_bind_of fun w hw => ?_
  have hw1 := rd_enqCt_p σ hC hR w hw
  have hwa : w.2.schedulerAction = .switchThread c := by
    rw [← ha]; exact af_enq σ.schedulerAction _ σ.curThread σ rfl w hw
  have hP1 : P1 c w.2 := (hkp_when _ (fun hs => aw_enq_ct σ _ (q1_enq _) hs hn (P1 c)
      fun s h1 h2 h3 => ⟨h1, h2, h3.trans ha⟩) (fun _ h => ⟨h.1, h.2.2, ha⟩) : SInvQ.HKp AW (P1 c) σ _) hAW w hw
  have hRc : RdyT w.2 c := hw1.2.1 c hwa
  have hRn : RnH c w.2.kheap := hP1.1.2.1 c hP1.2.2
  have hQ : TQ w.2 := hP1.1.1
  try dsimp only
  refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  try dsimp only
  split <;> refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  all_goals
    refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    refine pp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
    split
    · exact ac_chooseAfter _ (q1_enq c) w.2 hw1 hQ hRc hRn (rd_enqueue_p c w.2 hRc)
    · split
      · exact ac_chooseAfter _ (q1_app c) w.2 hw1 hQ hRc hRn (rd_append_p c w.2 hRc)
      · refine pp_bind_of fun v1 hv1 => fun r hr => ?_
        have hct := ct_guardedSwitchTo c w.2 hv1
        have hf := fk_guardedSwitchTo _ _ _ _ _ _ c w.2 (fk_self w.2) v1 hv1
        unfold setSchedulerAction at hr
        rw [Set.mem_singleton_iff.1 hr]
        refine ⟨rfl, Or.inr ?_⟩
        show RdyT v1.2 v1.2.curThread ∧ RnH v1.2.curThread v1.2.kheap
        rw [hct]
        exact ⟨rdyT_hv hf.1 hf.2.2.2.1 hRc, rnH_hv hf.1 hRn⟩

/-- SchedQ after the switch branch (`sq_schedule`'s arm). -/
theorem sq_sstb (c : ObjRef) (σ : State Unit) (ha : σ.schedulerAction = .switchThread c) :
    SInvQ.HKp AW SchedQ σ (scheduleSwitchThreadBranch (Z := Unit) c σ.curThread (schedulable σ.curThread σ)) := by
  have hn : σ.schedulerAction ≠ .resumeCurThread := by rw [ha]; exact fun e => absurd e (by simp)
  unfold scheduleSwitchThreadBranch
  refine hkp_bind (R := P1 c) ?_ fun _ => ?_
  · exact hkp_when _ (fun hs => aw_enq_ct σ _ (q1_enq _) hs hn (P1 c) fun s h1 h2 h3 => ⟨h1, h2, h3.trans ha⟩)
      fun _ h => ⟨h.1, h.2.2, ha⟩
  refine hk1_bind (hk1_of_ik' (ik_gets _)) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (ik_threadGet_any _ _ _)) fun _ => ?_
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

theorem fk_sstb (K : ObjRef → Option KernelObject) (c0 : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef)
    (c ct : ObjRef) (b : Bool) : IK (FK K c0 u T I S) (scheduleSwitchThreadBranch (Z := Unit) c ct b) := by
  unfold scheduleSwitchThreadBranch
  repeat' (first | (with_reducible exact fk_tcbSchedAction _ _ _ _ _ _ _ _) | (with_reducible exact fk_scheduleChooseNewThread _ _ _ _ _ _) | (with_reducible exact fk_guardedSwitchTo _ _ _ _ _ _ _) | (with_reducible exact ik_fastfail _ _ _ _ _) | ik_step0 | ik_unfold)

/-- **`schedule`, up to `sc_and_timer`, with the exit facts** (module docstring). -/
theorem rd_scheduleSE {Q : State Unit → Prop} (σ : State Unit)
    (hT : ∀ s, SE σ s → ∀ r ∈ (scAndTimer (Z := Unit) s).1, Q r.2) (hσ : Rdy σ)
    (hRN : SInvB.RNE σ) (hC : CtR σ) (hAW : AW σ) : ∀ r ∈ (schedule (Z := Unit) σ).1, Q r.2 := by
  show PostP Q σ _
  unfold schedule
  refine pp_bind_of fun z1 hz1 => ?_
  obtain ⟨a1, -, a3⟩ := rd_awakenC σ hσ hRN hC hz1
  have f1 := fk_awaken _ _ _ _ _ _ σ (fk_self σ) z1 hz1
  have w1 := aw_awaken σ hAW z1 hz1
  have c1 : z1.2.curThread = σ.curThread := ctk_awaken σ.curThread σ rfl z1 hz1
  refine pp_bind_of fun z2 hz2 => ?_
  have b1 := rd_checkDomainTime z1.2 a1 z2 hz2
  obtain ⟨k1, k2, k3, k4⟩ := ktc_checkDomainTime _ _ _ _ z1.2 ⟨rfl, rfl, rfl, rfl⟩ z2 hz2
  have b3 : CtR z2.2 := ctR_congr a3 k1 k2 k3 k4
  have f2 := fk_trans f1 (fk_checkDomainTime _ _ _ _ _ _ z1.2 (fk_self _) z2 hz2)
  have w2 := aw_checkDomainTime z1.2 w1 z2 hz2
  have c2 : z2.2.curThread = σ.curThread := k4.trans c1
  have r2 : z2.2.schedulerAction = .resumeCurThread → σ.schedulerAction = .resumeCurThread := fun h => by
    by_contra hn; exact nr_checkDomainTime z1.2 (nr_awaken σ hn z1 hz1) z2 hz2 h
  refine pp_gets_bind (pp_gets_bind (pp_gets_bind ?_))
  try dsimp only
  split
  · rename_i heq
    exact fun r hr => hT _ ⟨f2, b1, w2.1, heq, Or.inr (Or.inr ⟨c2, r2 heq⟩)⟩ r hr
  · rename_i heq
    have hn : z2.2.schedulerAction ≠ .resumeCurThread := by rw [heq]; exact fun e => absurd e (by simp)
    refine pp_bind_of fun w hw => ?_
    have hw1 := rd_enqCt_p z2.2 b3 b1 w hw
    have fw := fk_trans f2 ((ik_when _ (fk_tcbSchedAction _ _ _ _ _ _ _ _)) z2.2 (fk_self _) w hw)
    have qw : SQI w.2 := (hkp_when _ (fun hs => aw_enq_ct z2.2 _ (q1_enq _) hs hn SQI fun s h1 h2 h3 =>
      ⟨⟨h1, by rw [h3]; exact hn⟩, iq_of h1.1.1 h2⟩) (fun _ h => ⟨⟨h.1, hn⟩, iq_of h.1.1.1 h.2.2⟩) :
        SInvQ.HKp AW SQI z2.2 _) w2 w hw
    refine pp_bind_of fun v hv => fun r hr => hT _ ?_ r hr
    have fv := fk_trans fw (fk_scheduleChooseNewThread _ _ _ _ _ _ w.2 (fk_self _) v hv)
    have rv := rd_scheduleChooseNewThread w.2 hw1 v hv
    have qv := sq_scheduleChooseNewThread w.2 qw v hv
    obtain ⟨av, nv⟩ := se_chooseNew w.2 hw1 qw.1.1.1.1 hv
    exact ⟨fv, rv, qv, av, nv.elim Or.inl fun h => Or.inr (Or.inl h)⟩
  · rename_i c heq
    refine pp_bind_of fun w hw => fun r hr => hT _ ?_ r hr
    have fw := fk_trans f2 (fk_sstb _ _ _ _ _ _ c _ _ z2.2 (fk_self _) w hw)
    have rw' := rd_sstb_p c z2.2 b3 heq b1 w hw
    have qw := sq_sstb c z2.2 heq w2 w hw
    obtain ⟨aw, nw⟩ := ac_sstb c z2.2 b3 heq b1 w2 w hw
    exact ⟨fw, rw', qw, aw, nw.elim Or.inl fun h => Or.inr (Or.inl h)⟩

/-- **`schedule` ends with `Rdy ∧ OffReady`** (module docstring). -/
theorem rd_scheduleOff (σ : State Unit) {x : SchedContext} {n : Nat} (hσ : Rdy σ) (hRN : SInvB.RNE σ)
    (hC : CtR σ) (hAW : AW σ) (hk0 : σ.kheap σ.curSc = some (.schedContext x n))
    (hOS0 : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ σ.schedulerAction ≠ .resumeCurThread) ∨ OI σ)
    (hB : SInvB.ScBackS σ) (hV : SInvI.ValidIdle σ) (hIH : IdleHd σ)
    (hRC : σ.schedulerAction = .resumeCurThread → ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      x.tcbSchedContext = some σ.curSc) :
    ∀ r ∈ (schedule (Z := Unit) σ).1, Rdy r.2 ∧ Sched.OffReady r.2 :=
  rd_scheduleSE (Q := fun s => Rdy s ∧ Sched.OffReady s) σ (fun _ hs _ hr => rd_exitSE hs hk0 hOS0 hB hRN hV hIH hRC hr) hσ hRN hC hAW

end

end Fl4Proofs.P3.SInvR
