/-
P3 (DESIGN.md §9), invariant line G1 (rd8a, KENTRY-PLAN rd7 handoff 1(a)):
**`OS` and `Rdy` across FL4's TCB timer step `fl4Awaken`** (spec side only,
outside the JAtZ cone).

* `CW c σ σ'`: the SC at the fixed pointer `c` keeps its refills and refill
  max (if it is an SC afterwards, it was one before with the same refills /
  max), and `resume_cur_thread` is not set. Reflexive, transitive;
  `cw_of_svs`: SVK's scheduler view `SVS` implies it.
* `CP σ0 c s := s.curSc = c ∧ CW c σ0 s`, a pinned predicate for the `IK`
  kit; leaves: every `SVM ∧ CFK` function (`ik_cp`, the generic `cp_leaf`
  rule tries SVK's `sv_leaf` and RdP's `cfk_leaf`), `cp_threadSet`,
  `cp_setSchedulerAction` (to anything but resume), `cp_updateSchedContext`
  (refills / max kept); by hand `cp_schedContextDonate`,
  `cp_schedContextResume`, `cp_maybeDonateSc`, `cp_possibleSwitchTo`,
  `cp_refillUnblockCheck_ne` (an SC other than `c`), `cp_ifCondTest`
  (the `scp ≠ cur_sc` test guards of `if_cond_refill_unblock_check`),
  `cp_wake` (send_signal's wake tail).
* **`cw_sendSignal`**: from `Rdy` (only to get `SVS` across the cancel_ipc of
  the receive-blocked bound thread, RdL's `rs_cancelIpc_recv`), every outcome
  of `send_signal` is `CW cur_sc`; **`os_sendSignal`**: `OS` kept (with RdP's
  `cfk_sendSignal'`).
* **`ro_fl4Awaken`**: `Rdy ∧ OS ∧ NQ []` kept by `fl4Awaken`
  (`fl4TimerFires` induction: RdL's `rd_sendSignal` with nq's
  `nq_sendSignal` for the NtfnQB at every intermediate state; the reprogram
  flag is read by none of them).
-/
import Fl4Proofs.P3.SpecInvRdK
import Fl4Proofs.P3.SpecInvRdL
import Fl4Proofs.P3.SpecInvNtfnQG
import Fl4Proofs.P3.IpcWakeDon
open Classical

namespace Fl4Proofs.P3.SInvR.A8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The relation -/

/-- The SC at `c` keeps refills and refill max; resume is not set. -/
def CW (c : ObjRef) (σ σ' : State Unit) : Prop :=
  (∀ y n, σ'.kheap c = some (.schedContext y n) → ∃ y0 n0, σ.kheap c = some (.schedContext y0 n0) ∧
      y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax) ∧
  (σ'.schedulerAction = .resumeCurThread → σ.schedulerAction = .resumeCurThread)

theorem CW.refl (c : ObjRef) (σ : State Unit) : CW c σ σ := ⟨fun y n h => ⟨y, n, h, rfl, rfl⟩, id⟩

theorem CW.trans {c : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : CW c σ1 σ2) (h2 : CW c σ2 σ3) : CW c σ1 σ3 := by
  refine ⟨fun y n h => ?_, fun e => h1.2 (h2.2 e)⟩
  obtain ⟨y1, n1, h1', e1, e2⟩ := h2.1 y n h
  obtain ⟨y0, n0, h0, e3, e4⟩ := h1.1 y1 n1 h1'
  exact ⟨y0, n0, h0, e1.trans e3, e2.trans e4⟩

theorem cw_of_svs {c : ObjRef} {σ σ' : State Unit} (h : SVK.SVS σ σ') : CW c σ σ' := by
  refine ⟨fun y n hy => ?_, fun e => ?_⟩
  · have e1 := h.1 c
    rw [hy] at e1
    obtain ⟨y0, h0, r1, r2, -⟩ := SVK.sv_sc (o := σ.kheap c) e1.symm
    exact ⟨y0, n, h0, r1.symm, r2.symm⟩
  · rcases h.2.2 with e' | e'
    · exact e'.symm.trans e
    · rw [e'] at e; cases e

/-- The pinned predicate: `cur_sc = c` and `CW c` from `σ0`. -/
abbrev CP (σ0 : State Unit) (c : ObjRef) (s : State Unit) : Prop := s.curSc = c ∧ CW c σ0 s

theorem ik_cp {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) (σ0 : State Unit)
    (c : ObjRef) : IK (CP σ0 c) m := by
  intro s hs y hy
  have e := h2 s y hy
  have ec : y.2.curSc = s.curSc := congrArg (fun p => p.2.1) e
  exact ⟨ec.trans hs.1, hs.2.trans (cw_of_svs (h1 s y hy))⟩

/-- A `CP` lemma of a spec function. -/
syntax "cp_leaf" : tactic
macro_rules | `(tactic| cp_leaf) => `(tactic| fail "no cp_leaf")
macro_rules | `(tactic| cp_leaf) => `(tactic|
  (refine ik_cp ?_ ?_ _ _ <;> first | (sv_auto; done) | (cfk_auto; done)))

macro "cp_auto" : tactic => `(tactic| repeat' (first | cp_leaf | ik_step0))

theorem cp_threadSet (f : Tcb → Tcb) (t : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (threadSet (Z := Unit) f t) := by
  intro s hs y hy
  obtain ⟨x, -, e⟩ := SInv.mem_threadSet hy
  rw [e]
  refine ⟨hs.1, hs.2.trans ⟨fun z n hz => ?_, id⟩⟩
  dsimp only at hz
  by_cases ec : c = t
  · subst ec; rw [Function.update_self] at hz; cases hz
  · rw [Function.update_of_ne ec] at hz; exact ⟨z, n, hz, rfl, rfl⟩
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_threadSet _ _ _ _)

theorem cp_setSchedulerAction (a : SchedulerAction) (ha : a ≠ .resumeCurThread) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction
  refine ik_modify fun s hs => ⟨hs.1, hs.2.trans ⟨fun y n h => ⟨y, n, h, rfl, rfl⟩, fun e => absurd e ha⟩⟩
macro_rules | `(tactic| cp_leaf) => `(tactic| exact cp_setSchedulerAction _ (by simp) _ _)

theorem cp_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  refine ⟨hs.1, hs.2.trans ⟨fun z n hz => ?_, id⟩⟩
  dsimp only at hz
  by_cases ec : c = q
  · subst ec; rw [Function.update_self] at hz; cases hz
    exact ⟨y0, n0, hk, (hf y0).1, (hf y0).2⟩
  · rw [Function.update_of_ne ec] at hz; exact ⟨z, n, hz, rfl, rfl⟩
macro_rules | `(tactic| cp_leaf) => `(tactic|
  (refine cp_updateSchedContext _ _ ?_ _ _; intro _; exact ⟨rfl, rfl⟩))

theorem cp_rescheduleRequired (σ0 : State Unit) (c : ObjRef) : IK (CP σ0 c) (rescheduleRequired (Z := Unit)) :=
  ik_cp SVK.sv_rescheduleRequired' (by cfk_leaf) σ0 c
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_rescheduleRequired _ _)

theorem cp_testReschedule (t : ObjRef) (σ0 : State Unit) (c : ObjRef) : IK (CP σ0 c) (testReschedule (Z := Unit) t) :=
  ik_cp (SVK.sv_testReschedule' t) (by cfk_leaf) σ0 c
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_testReschedule _ _ _)

theorem cp_tcbNtfnDequeue (t n : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (tcbNtfnDequeue (Z := Unit) t n) :=
  ik_cp (sv_tcbNtfnDequeue t n) (by cfk_leaf) σ0 c
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_tcbNtfnDequeue _ _ _ _)

theorem cp_setNotification (n : ObjRef) (nt : Notification) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (setNotification (Z := Unit) n nt) :=
  ik_cp (by sv_auto) (by cfk_leaf) σ0 c

/-! ## The send_signal writers -/

theorem cp_postpone (p : ObjRef) (σ0 : State Unit) (c : ObjRef) : IK (CP σ0 c) (postpone (Z := Unit) p) := by
  unfold postpone tcbReleaseEnqueue readyTimesAppend orderedInsert; cp_auto
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_postpone _ _ _)

theorem cp_schedContextResume (p : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume; cp_auto
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_schedContextResume _ _ _)

theorem cp_schedContextDonate (p t : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate; cp_auto
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_schedContextDonate _ _ _ _)

theorem cp_maybeDonateSc (t n : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc; cp_auto
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_maybeDonateSc _ _ _ _)

theorem cp_possibleSwitchTo (t : ObjRef) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; cp_auto
macro_rules | `(tactic| cp_leaf) => `(tactic| with_reducible exact cp_possibleSwitchTo _ _ _)

/-- An SC write at `q ≠ c`. -/
theorem cp_updateSchedContext_ne (q : ObjRef) (f : SchedContext → SchedContext) {c : ObjRef} (hq : q ≠ c)
    (σ0 : State Unit) : IK (CP σ0 c) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  refine ⟨hs.1, hs.2.trans ⟨fun z n hz => ?_, id⟩⟩
  dsimp only at hz
  rw [Function.update_of_ne (Ne.symm hq)] at hz; exact ⟨z, n, hz, rfl, rfl⟩

/-- `refill_unblock_check` of an SC other than `c`. -/
theorem cp_refillUnblockCheck_ne (p : ObjRef) {c : ObjRef} (hp : p ≠ c) (σ0 : State Unit) :
    IK (CP σ0 c) (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead updateRefillHd isRoundRobin
    getRefillHead
  repeat' (first | exact cp_updateSchedContext_ne _ _ hp _ | cp_leaf | ik_step0)

/-- The guards of `if_cond_refill_unblock_check` that test `scp ≠ cur_sc`. -/
theorem cp_ifCondTest (o : Option ObjRef) (a : Option Bool) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (ifCondRefillUnblockCheck (Z := Unit) o a (some false)) := by
  unfold ifCondRefillUnblockCheck
  refine ik_maybeM (fun p => ?_) o
  refine ik_bind (by cp_leaf) fun sc => ?_
  intro s hs y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  obtain ⟨w, hw, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hw
  dsimp only at hy
  unfold NonDet.when at hy
  split_ifs at hy with h1 h2
  · exact cp_refillUnblockCheck_ne p (fun e => h1.2 rfl (e.trans hs.1.symm)) σ0 s hs y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hs
  · rw [Set.mem_singleton_iff.1 hy]; exact hs

/-- send_signal's wake tail (RdL's `rd_wake` shape). -/
theorem cp_wake (t n : ObjRef) (b : Badge) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (do
      setThreadState (Z := Unit) t .running
      asUser (Z := Unit) t <| setRegister badge_register b
      maybeDonateSc (Z := Unit) t n
      let sched ← NonDet.gets (schedulable t)
      NonDet.when sched <| possibleSwitchTo (Z := Unit) t
      let scopt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) := by
  refine ik_bind (by cp_leaf) fun _ => ik_bind (by cp_leaf) fun _ => ik_bind (cp_maybeDonateSc t n σ0 c) fun _ => ?_
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (cp_possibleSwitchTo t σ0 c)) fun _ => ?_
  exact ik_bind (by cp_leaf) fun _ => cp_ifCondTest _ _ σ0 c

theorem cp_updateWaitingNtfn (n : ObjRef) (q : List ObjRef) (b : Badge) (σ0 : State Unit) (c : ObjRef) :
    IK (CP σ0 c) (updateWaitingNtfn (Z := Unit) n q b) := by
  unfold updateWaitingNtfn
  refine ik_bind (ik_assert _) fun _ => ik_bind (by cp_leaf) fun _ => ik_bind (by cp_leaf) fun _ => ?_
  exact cp_wake _ n b σ0 c

/-- **`send_signal` keeps the SC at `cur_sc` and sets no resume.** -/
theorem cw_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (hR : Rdy σ) :
    ∀ y ∈ (sendSignal (Z := Unit) n b σ).1, CP σ σ.curSc y.2 := by
  intro y hy
  have h0 : CP σ σ.curSc σ := ⟨rfl, CW.refl _ σ⟩
  unfold sendSignal at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, e⟩ := SInv.mem_getSimpleKo hz
  obtain ⟨nt, z2⟩ := z
  simp only at hk e; subst z2
  dsimp only at hy
  cases h1 : nt.ntfnObj with
  | idleNtfn =>
    cases h2 : nt.ntfnBoundTcb with
    | none =>
      rw [h1, h2] at hy
      exact cp_setNotification n _ σ σ.curSc σ h0 y hy
    | some tcb =>
      rw [h1, h2] at hy
      obtain ⟨w, hw, hy⟩ := hy
      unfold getThreadState at hw
      obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
      dsimp only at hy
      split at hy
      · rename_i hrb
        obtain ⟨c1, hc1, hy⟩ := hy
        obtain ⟨-, hS1⟩ := rs_cancelIpc_recv tcb σ hR hx hrb hc1
        have ec : c1.2.curSc = σ.curSc := congrArg (fun p => p.2.1) (cfk_cancelIpc' tcb σ c1 hc1)
        exact cp_wake tcb n b σ σ.curSc c1.2 ⟨ec, cw_of_svs hS1⟩ y hy
      · exact cp_setNotification n _ σ σ.curSc σ h0 y hy
  | waitingNtfn queue =>
    rw [h1] at hy
    exact cp_updateWaitingNtfn n queue b σ σ.curSc σ h0 y hy
  | activeNtfn badge' =>
    rw [h1] at hy
    exact cp_setNotification n _ σ σ.curSc σ h0 y hy

/-- **`send_signal` keeps `OS`.** -/
theorem os_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (hR : Rdy σ) (hO : OS σ) :
    ∀ y ∈ (sendSignal (Z := Unit) n b σ).1, OS y.2 := by
  intro y hy
  have hc := cfk_sendSignal' n b σ y hy
  obtain ⟨ec, hw1, hw2⟩ := cw_sendSignal n b σ hR y hy
  refine os_frame hO ⟨hc, fun z m hz => ?_, hw2⟩
  rw [ec] at hz
  exact hw1 z m hz

/-! ## `fl4Awaken` -/

/-- What the timer step carries. -/
abbrev RO (s : State Unit) : Prop := Rdy s ∧ OS s ∧ NQ [] s

theorem ro_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (h : RO σ) :
    ∀ y ∈ (sendSignal (Z := Unit) n b σ).1, RO y.2 := by
  intro y hy
  have hN : SInv.NtfnQB σ := ((nq_nil_iff σ).1 h.2.2).1
  exact ⟨rd_sendSignal n b σ h.1 hN y hy, os_sendSignal n b σ h.1 h.2.1 y hy, nq_sendSignal n b σ h.2.2 y hy⟩

/-- **`Rdy ∧ OS ∧ NQ []` kept by `fl4Awaken`** (rd7 handoff 1(a)). -/
theorem ro_fl4Awaken : IK RO (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact ro_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)

end

end Fl4Proofs.P3.SInvR.A8
