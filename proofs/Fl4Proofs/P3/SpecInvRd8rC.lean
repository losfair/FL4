/-
P3 (DESIGN.md §9), invariant line G1 (rd8r, KENTRY-PLAN rd8p handoff 1):
**`HO ∧ NQ []` across the deletion cone and the preemptible perform arms**
(spec side only, outside the JAtZ cone).

* `HQ s := HO s ∧ NQ [] s`. Every callee outside the hand tier has its
  generated `ho_` lemma (SpecInvRd8rF*) and nq2's `nq_` lemma (`hq_of`).
* **The restart helpers** (`hq_removeAndRestartEpQueuedThread`, `…Badged…`,
  `…NtfnQueuedThread`): the woken thread is in the queue at its dequeue (the
  dequeue asserts it), so nq2's `EpQB` / `NtfnQB` give an endpoint / notification
  block there, and `HO` says no such thread is bound to `cur_sc` (`NH t`). `NH t`
  rides along the dequeue and `reply_unlink_tcb` (`SVS`: the TCB's SC kept;
  `CFK`: `cur_sc` kept) to the Restart write (`ho_setThreadState_nh`).
* **`reply_remove`** of a caller read BlockedOnReply: its donation binds the caller
  (to `cur_sc`, possibly) while it is still BlockedOnReply, a quiet state (`QT`); the
  caller keeps that state across `reply_unlink_sc` and the donation's prefix
  (IpcStK's backward state frame `OSK p`, `p` the SC: the caller is a TCB, so `≠ p`),
  then `reply_unlink_tcb` makes it Inactive. NQ: nq3's `nq_consR` puts the caller in
  `K` for `nq_replyRemove`.
* `fast_finalise`, `cap_delete_one`, `finalise_cap`, `rec_del` (`ik_lfp`),
  `cap_delete`, `cap_revoke`, `install_tcb_cap`, `install_tcb_frame_cap`: `HQ` at every
  outcome (errors from a preemption point included), as ctq14's `CKC` (SpecInvCqHC).
* **`hqx_fl4PerformInvocation`**: from `HQ`, every error outcome of the perform has
  `HO` (ctq16's arm split: Untyped reset keeps `HO` alone, `ho_resetUntypedCap`;
  ThreadControlCaps / Sched and CNode Revoke / Delete by the `HQ` lemmas; every other
  arm never errors, ctq16's `NE`).
-/
import Fl4Proofs.P3.SpecInvRd8rF3
import Fl4Proofs.P3.IpcStK
import Fl4Proofs.P3.SpecInvSlW
open Classical

namespace Fl4Proofs.P3.SInvR.B8r
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The joint invariant -/

abbrev HQ (s : State Unit) : Prop := HO s ∧ NQ [] s

theorem hq_of {α : Type} {m : NonDet (State Unit) α} (h1 : HOK m) (h2 : NQK [] m) : IK HQ m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

theorem hq_ofE {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : HOKE m) (h2 : NQKE [] m) : IKE HQ m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

syntax "hq_leaf" : tactic
macro_rules | `(tactic| hq_leaf) => `(tactic| ((with_reducible refine hq_of ?_ ?_); ho_leaf; nq_leaf))

macro "hq_auto" : tactic => `(tactic| repeat' (first | hq_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

/-! ## `NH` and the restart -/

theorem nh_of_cf {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) (t : ObjRef) :
    IK (NH t) m := by
  intro s hs y hy x hx hc
  have ec : y.2.curSc = s.curSc := congrArg (fun p => p.2.1) (h2 s y hy)
  have e := (h1 s y hy).1 t
  rw [hx] at e
  obtain ⟨y0, hy0, hyc⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  exact hs y0 hy0 (by rw [hyc, hc, ec])

theorem nh_of_blk {s : State Unit} (h : HO s) {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    (hb : ∀ b, ¬ HS b x.tcbState) : NH t s := fun x' hx' hc => by
  rw [hx] at hx'; cases hx'
  exact hb _ (h t x hx hc)

theorem hs_of_epBlocked {ts : ThreadState} {e : ObjRef} (h : epBlocked ts = some e) (b : Prop) : ¬ HS b ts := by
  cases ts
  all_goals first | (intro h'; exact h') | cases h

/-- Restart, the refill check, `possible_switch_to`, of a thread not bound to `cur_sc`. -/
theorem ho_restartTail (t : ObjRef) (s : State Unit) (hO : HO s) (hn : NH t s) {y : Unit × State Unit}
    (hy : y ∈ ((do
      setThreadState (Z := Unit) t .restart
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scOpt
      possibleSwitchTo (Z := Unit) t) s).1) : HO y.2 := by
  obtain ⟨z, hz, hy⟩ := hy
  have h1 : HO z.2 := ho_setThreadState_nh t .restart s hn hO z hz
  exact (show HOK (do
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scOpt
      possibleSwitchTo (Z := Unit) t) by ho_auto) z.2 h1 y hy

/-- **`restart_thread_if_no_fault`** of a thread not bound to `cur_sc`. -/
theorem ho_restartThreadIfNoFault (t : ObjRef) (s : State Unit) (hO : HO s) (hn : NH t s)
    {y : Unit × State Unit} (hy : y ∈ (restartThreadIfNoFault (Z := Unit) t s).1) : HO y.2 := by
  unfold restartThreadIfNoFault at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · exact ho_restartTail t s hO hn hy
  · exact ho_setThreadState t .inactive trivial s hO y hy

/-! ## The wake steps and loops -/

theorem hq_removeAndRestartEpQueuedThread (t e : ObjRef) :
    IK HQ (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartEpQueuedThread (Kq := []) t e σ hσ.2 y hy⟩
  unfold removeAndRestartEpQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨ep, ep', hk, hq, -, -⟩ := Sched.tcbEpDequeue_out hz1
  obtain ⟨x, hx, hb⟩ := hσ.2.1.2 e ep t hk hq
  have hn0 : NH t σ := nh_of_blk hσ.1 hx (hs_of_epBlocked hb)
  have h1 : HO z1.2 := ho_tcbEpDequeue t e σ hσ.1 z1 hz1
  have hn1 : NH t z1.2 := nh_of_cf (sv_tcbEpDequeue t e) (cfk_tcbEpDequeue' t e) t σ hn0 z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  unfold getThreadState at hz2
  obtain ⟨x2, -, rfl⟩ := q1_mem_threadGet hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz3] at hy
  obtain ⟨z4, hz4, hy⟩ := hy
  dsimp only at hz4 hy
  have h4 : HO z4.2 ∧ NH t z4.2 := by
    revert hz4
    cases (if isBlockedOnReceive x2.tcbState then replyObject x2.tcbState else none) with
    | none => intro h; rw [Set.mem_singleton_iff.1 h]; exact ⟨h1, hn1⟩
    | some r =>
      intro h
      exact ⟨ho_replyUnlinkTcb t r z1.2 h1 z4 h,
        nh_of_cf (SVK.sv_replyUnlinkTcb t r) (cfk_replyUnlinkTcb' t r) t z1.2 hn1 z4 h⟩
  exact ho_restartThreadIfNoFault t z4.2 h4.1 h4.2 hy

theorem hq_removeAndRestartBadgedThread (t e : ObjRef) (b : Badge) :
    IK HQ (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartBadgedThread (Kq := []) t e b σ hσ.2 y hy⟩
  unfold removeAndRestartBadgedThread getThreadState at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain ⟨x0, -, rfl⟩ := q1_mem_threadGet hz0
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨ep, ep', hk, hq, -, -⟩ := Sched.tcbEpDequeue_out hz1
    obtain ⟨x, hx, hb⟩ := hσ.2.1.2 e ep t hk hq
    have hn0 : NH t σ := nh_of_blk hσ.1 hx (hs_of_epBlocked hb)
    have h1 : HO z1.2 := ho_tcbEpDequeue t e σ hσ.1 z1 hz1
    have hn1 : NH t z1.2 := nh_of_cf (sv_tcbEpDequeue t e) (cfk_tcbEpDequeue' t e) t σ hn0 z1 hz1
    exact ho_restartThreadIfNoFault t z1.2 h1 hn1 hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

theorem hq_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    IK HQ (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartNtfnQueuedThread (Kq := []) t n σ hσ.2 y hy⟩
  unfold removeAndRestartNtfnQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨xn, hk, hq⟩ := R14.dz_tcbNtfnDequeue_mem hz1
  obtain ⟨x, hx, hs⟩ := hσ.2.1.1 n xn t hk hq
  have hn0 : NH t σ := nh_of_blk hσ.1 hx (fun b h => by rw [hs] at h; exact h)
  have h1 : HO z1.2 := ho_tcbNtfnDequeue t n σ hσ.1 z1 hz1
  have hn1 : NH t z1.2 := nh_of_cf (sv_tcbNtfnDequeue t n) (by cfk_leaf) t σ hn0 z1 hz1
  exact ho_restartTail t z1.2 h1 hn1 hy

theorem hq_cancelAllIpc (e : ObjRef) : IK HQ (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ik_pure _
  · refine ik_pure_bind ?_
    exact ik_bind (ik_mapMx (fun t => hq_removeAndRestartEpQueuedThread t e) _) fun _ => by hq_leaf

theorem hq_cancelBadgedSends (e : ObjRef) (b : Badge) : IK HQ (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ik_bind (ik_mapMx (fun t => hq_removeAndRestartBadgedThread t e b) _) fun _ => by hq_leaf
  · exact ik_pure _

theorem hq_cancelAllSignals (n : ObjRef) : IK HQ (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ntfn => ?_
  split
  · exact ik_bind (ik_mapMx (fun t => hq_removeAndRestartNtfnQueuedThread t n) _) fun _ => by hq_leaf
  · exact ik_pure _

macro_rules | `(tactic| hq_leaf) => `(tactic| with_reducible exact hq_cancelAllIpc _)
macro_rules | `(tactic| hq_leaf) => `(tactic| with_reducible exact hq_cancelBadgedSends _ _)
macro_rules | `(tactic| hq_leaf) => `(tactic| with_reducible exact hq_cancelAllSignals _)

/-! ## The donation -/

section St
open StK

theorem st_threadSet_keepR {t0 : ObjRef} (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbState = x.tcbState) (t : ObjRef) :
    STK t0 (threadSet (Z := Unit) f t) := by
  intro σ x hx
  by_cases hT : ∃ y0, σ.kheap t = some (.tcb y0)
  · obtain ⟨y0, hy0⟩ := hT
    rw [Notif.threadSet_eq f hy0] at hx
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨fun p z _ hz => ?_, rfl⟩
    by_cases hp : p = t
    · subst hp; simp [Notif.updK] at hz; subst hz; exact ⟨y0, hy0, hf y0⟩
    · exact ⟨z, by simpa [Notif.updK, hp] using hz, rfl⟩
  · have hg : getTcb (Z := Unit) t σ = none := by
      unfold getTcb readObject
      cases hk : σ.kheap t with
      | none => rfl
      | some k => cases k <;> first | rfl | exact absurd ⟨_, hk⟩ hT
    unfold threadSet at hx; obtain ⟨y, hy, -⟩ := hx
    unfold NonDet.getsThe at hy; rw [hg] at hy; exact hy.elim

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbSchedAction _ _)
local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbReleaseRemove _)

theorem st_rescheduleRequiredR {t0 : ObjRef} : STK t0 (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  st_auto

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_rescheduleRequiredR)

theorem st_testRescheduleR {t0 : ObjRef} (f : ObjRef) : STK t0 (testReschedule (Z := Unit) f) := by
  unfold testReschedule
  refine st_bind (st_gets _) fun _ => st_bind (st_gets _) fun _ => st_bind (st_pure _) fun _ => ?_
  apply st_when
  exact st_rescheduleRequiredR

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_testRescheduleR _)

theorem st_getScObjRefR {t0 : ObjRef} (f : SchedContext → Option ObjRef) (p : ObjRef) :
    STK t0 (getScObjRef (Z := Unit) f p) := by
  unfold getScObjRef getSchedContext; st_auto

local macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getScObjRefR _ _)

theorem st_schedContextDonateR {t0 : ObjRef} (sc t : ObjRef) : STK t0 (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; st_auto
  all_goals (refine st_threadSet_keepR _ ?_ _; intro; rfl)

theorem st_donatePre {t0 : ObjRef} (sc : ObjRef) (fo : Option ObjRef) :
    STK t0 (NonDet.when (fo ≠ none) (do
      let fromTptr ← NonDet.assertOpt fo
      tcbSchedAction (Z := Unit) tcbSchedDequeue fromTptr
      tcbReleaseRemove (Z := Unit) fromTptr
      setTcbObjRef (Z := Unit) tcbSchedContextUpdate fromTptr none
      testReschedule (Z := Unit) fromTptr)) := by
  st_auto
  all_goals (refine st_threadSet_keepR _ ?_ _; intro; rfl)

theorem st_replyUnlinkScR {t0 : ObjRef} (p r : ObjRef) : STK t0 (replyUnlinkSc (Z := Unit) p r) := by
  unfold replyUnlinkSc; st_auto

end St

/-- The caller's state is quiet. -/
def QT (t : ObjRef) (s : State Unit) : Prop := ∀ y, s.kheap t = some (.tcb y) → HS False y.tcbState

theorem qt_of_osk {t0 t : ObjRef} {σ σ' : State Unit} (h : StK.OSK t0 σ σ') (hne : t ≠ t0) (hq : QT t σ) :
    QT t σ' := by
  intro y hy
  obtain ⟨y0, hy0, e⟩ := h.1 t y hne hy
  rw [e]; exact hq y0 hy0

abbrev HQT (t : ObjRef) (s : State Unit) : Prop := HO s ∧ QT t s

theorem hqt_of {α : Type} {m : NonDet (State Unit) α} {t p : ObjRef} (hne : t ≠ p) (h1 : HOK m)
    (h2 : StK.STK p m) : IK (HQT t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, qt_of_osk (h2 σ y hy) hne h.2⟩

/-- A TCB update keeping the state of a thread whose state is quiet. -/
theorem ho_threadSet_q (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit)
    (hs : ∀ x, (f x).tcbState = x.tcbState) (hq : QT t σ) : IKp HO σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ y ⟨z, hz, hy⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    have hk := getTcb_kheap e
    refine ho_setObject_p t _ σ (fun x hx _ y' ey _ => ?_) hσ y hy
    rw [hk] at hx; cases hx; cases ey
    rw [hs a]
    exact HS.mono (hq a hk)

/-- **`sched_context_donate p t`** to a thread in a quiet state (`t ≠ p`). -/
theorem hqt_schedContextDonate (p t : ObjRef) (hne : t ≠ p) : IK (HQT t) (schedContextDonate (Z := Unit) p t) := by
  intro σ hσ y hy
  refine ⟨?_, qt_of_osk (st_schedContextDonateR p t σ y hy) hne hσ.2⟩
  unfold schedContextDonate at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have a1 : HQT t z1.2 := hqt_of hne (by ho_auto) (st_getScObjRefR _ _) σ hσ z1 hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have a2 : HQT t z2.2 := hqt_of hne (by ho_auto) (st_donatePre p z1.1) z1.2 a1 z2 hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have a3 : HQT t z3.2 := hqt_of hne (by ho_auto) (StK.st_updateSchedContext _ _) z2.2 a2 z3 hz3
  exact ho_threadSet_q (tcbSchedContextUpdate fun _ => some p) t z3.2 (fun _ => rfl) a3.2 a3.1 y hy

/-! ## `reply_remove` -/

/-- **`reply_remove t r`** of a thread read BlockedOnReply. -/
theorem hq_replyRemove_r (t r r' : ObjRef) (σ : State Unit) (x : Tcb) (hx : σ.kheap t = some (.tcb x))
    (hs : x.tcbState = .blockedOnReply r') : IKp HQ σ (replyRemove (Z := Unit) t r) := by
  intro hσ y hy
  have hN : NQ [t] σ := nq_consR hσ.2 hx (by rw [hs]; exact fun h => h) (by rw [hs]; rfl)
  refine ⟨?_, nq_weak_nil _ (SInv.nq_replyRemove (Kq := [t]) t r (List.mem_cons_self ..) σ hN y hy)⟩
  have hq0 : QT t σ := fun y hy => by rw [hx] at hy; cases hy; rw [hs]; trivial
  unfold replyRemove at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have e1 : z1.2 = σ := cq5_ro (fun _ => by unfold getReply; repeat' (first | ik_step0 | ik_unfold | split)) hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  have e2 : z2.2 = z1.2 := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz3] at hy
  dsimp only at hy
  rw [e2, e1] at hy
  rcases hw : scWithReply r σ with _ | p
  · rw [hw] at hy
    exact ho_replyUnlinkTcb t r σ hσ.1 y hy
  · rw [hw] at hy
    try dsimp only at hy
    obtain ⟨sy, sn, hsk, -⟩ := SInvL.scWithReply_memL hw
    have hne : t ≠ p := by rintro rfl; rw [hx] at hsk; cases hsk
    obtain ⟨w1, hw1, hy⟩ := hy
    have a1 : HQT t w1.2 := hqt_of hne (by ho_auto) (by st_auto) σ ⟨hσ.1, hq0⟩ w1 hw1
    obtain ⟨w2, hw2, hy⟩ := hy
    have a2 : HQT t w2.2 := hqt_of hne (by ho_auto) (by unfold getTcbObjRef; st_auto) w1.2 a1 w2 hw2
    obtain ⟨w3, hw3, hy⟩ := hy
    have a3 : HQT t w3.2 := hqt_of hne (by ho_auto) (st_replyUnlinkScR _ _) w2.2 a2 w3 hw3
    obtain ⟨w4, hw4, hy⟩ := hy
    have a4 : HQT t w4.2 := ik_when _ (hqt_schedContextDonate p t hne) w3.2 a3 w4 hw4
    exact ho_replyUnlinkTcb t r w4.2 a4.1 y hy

/-! ## Finalisation and deletion -/

/-- The reply arm of `fast_finalise` / `finalise_cap` after the TCB read. -/
macro "hq_reply_arm" : tactic => `(tactic| (
  unfold getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState <;> dsimp only
  all_goals first
    | exact hq_replyRemove_r _ _ _ σ x hx hs
    | exact ikp_of_ik (by hq_leaf) σ))

theorem hq_fastFinalise (c : Cap) (final : Bool) : IK HQ (fastFinalise (Z := Unit) c final) := by
  cases c
  case nullCap => exact ik_pure _
  case replyCap r _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    refine ik_bind (by hq_auto) fun tp => ?_
    split
    · exact ik_pure _
    · hq_reply_arm
  case endpointCap r _ _ =>
    simp only [fastFinalise]
    exact ik_when _ (by hq_leaf)
  case notificationCap r _ _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    exact ik_bind (by hq_leaf) fun _ => ik_bind (by hq_leaf) fun _ => by hq_leaf
  all_goals (simp only [fastFinalise]; exact ik_fail)

/-- **`cap_delete_one` keeps `HQ`.** -/
theorem hq_capDeleteOne (slot : CslotPtr) : IK HQ (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  refine ik_bind (by hq_leaf) fun cap => ?_
  refine ik_unless _ ?_
  exact ik_bind (by hq_leaf) fun fin => ik_bind (hq_fastFinalise cap fin) fun _ => by hq_leaf

theorem hq_deletingIrqHandler (irq : Irq) : IK HQ (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact ik_bind (ik_gets _) fun sl => hq_capDeleteOne sl

theorem hq_finaliseCap (c : Cap) (final : Bool) : IK HQ (finaliseCap (Z := Unit) c final) := by
  cases c
  case replyCap r _ =>
    simp only [finaliseCap]
    refine ik_liftM _ ?_
    refine ik_when _ ?_
    refine ik_bind (by hq_auto) fun tp => ?_
    split
    · exact ik_pure _
    · hq_reply_arm
  case irqHandlerCap irq =>
    simp only [finaliseCap]
    split
    · exact ik_bind (hq_deletingIrqHandler irq) fun _ => ik_pure _
    · exact ik_pure _
  all_goals (simp only [finaliseCap]; hq_auto)

syntax "hqh_leaf" : tactic
macro_rules | `(tactic| hqh_leaf) => `(tactic| with_reducible exact hq_finaliseCap _ _)
macro_rules | `(tactic| hqh_leaf) => `(tactic| hq_leaf)

macro "hqh_auto" : tactic => `(tactic| repeat' (first | hqh_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem hq_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, IK HQ (f k)) (k : RecDelCall) : IKE HQ (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, IKE HQ (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; hqh_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; hqh_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> hqh_auto
    all_goals exact hrec' _

theorem hq_recDel (c : RecDelCall) : IKE HQ (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => hq_recDelF hf k) c

/-- **`cap_delete`: every outcome has `HQ`.** -/
theorem hq_capDelete (sl : CslotPtr) : IKE HQ (capDelete (Z := Unit) sl) := by
  unfold capDelete
  exact ike_bind (hq_recDel _) fun _ => ike_returnOk _

theorem hq_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK HQ (f k)) (sl : CslotPtr) : IKE HQ (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE HQ (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  repeat' (first | (with_reducible exact hq_capDelete _) | hqh_leaf | ik_step0 | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless))
  all_goals exact hrec' _

/-- **`cap_revoke`: every outcome has `HQ`.** -/
theorem hq_capRevoke (sl : CslotPtr) : IKE HQ (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => hq_capRevokeF hf k) sl

/-! ## The preemptible perform arms -/

theorem hq_checkCapAt (c : Cap) (sl : CslotPtr) {m : NonDet (State Unit) Unit} (h : IK HQ m) :
    IK HQ (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt
  exact ik_bind (by hq_leaf) fun _ => ik_when _ h

/-- **`install_tcb_cap` keeps `HQ`** (every outcome). -/
theorem hq_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr)) :
    IKE HQ (installTcbCap (Z := Unit) target slot n so) := by
  unfold installTcbCap
  split
  · exact ike_returnOk _
  · refine ike_bind (hq_capDelete _) fun _ => ?_
    exact ike_unlessE _ (ike_liftE (hq_checkCapAt _ _ (hq_checkCapAt _ _ (by hq_leaf))))

/-- **`install_tcb_frame_cap` keeps `HQ`** (every outcome). -/
theorem hq_installTcbFrameCap (target : ObjRef) (slot : CslotPtr)
    (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    IKE HQ (installTcbFrameCap (Z := Unit) target slot buf) := by
  unfold installTcbFrameCap
  split
  · exact ike_returnOk _
  · refine ike_bind (hq_capDelete _) fun _ => ?_
    refine ike_bind (ike_liftE (by hq_leaf)) fun _ => ?_
    refine ike_bind (ike_liftE ?_) fun _ => ?_
    · split
      · exact ik_pure _
      · exact hq_checkCapAt _ _ (hq_checkCapAt _ _ (by hq_leaf))
    refine ike_bind (ike_liftE (ik_gets _)) fun _ => ?_
    exact ike_liftE (ik_when _ (by hq_leaf))

/-- From `HQ`, every error outcome has `HO`. -/
def HQX {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ σ, HQ σ → ∀ y ∈ (m.run σ).1, ∀ e, y.1 = .error e → HO y.2

theorem hqx_of_ne {ε α : Type} {m : NonDetE (State Unit) ε α} (h : R16.NE m) : HQX m :=
  fun σ _ y hy e he => absurd he (h σ y hy e)

theorem hqx_of_ike {ε α : Type} {m : NonDetE (State Unit) ε α} (h : IKE HQ m) : HQX m :=
  fun σ hσ y hy _ _ => (h σ hσ y hy).1

theorem hqx_of_hoke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : HOKE m) : HQX m :=
  fun σ hσ y hy _ _ => h σ hσ.1 y hy

theorem hqx_bind_ike {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKE HQ m) (hg : ∀ a, HQX (g a)) : HQX (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a z.2 (hm σ hσ z hz) y hy e he
  · exact (hm σ hσ z hz).1

theorem hqx_bind_ne {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : HQX m) (hg : ∀ a, R16.NE (g a)) : HQX (m >>= g) := by
  intro σ hσ y hy e he
  obtain ⟨z, hz, ⟨a, -, hy⟩ | ⟨e', he', rfl⟩⟩ := ft_mem_bindE hy
  · exact absurd he (hg a z.2 y hy e)
  · exact hm σ hσ z hz e' he'

theorem hqx_fl4InvokeUntyped (i : UntypedInvocation) : HQX (fl4InvokeUntyped (Z := Unit) i) := by
  cases i
  simp only [fl4InvokeUntyped, invokeUntypedWith]
  exact hqx_bind_ne (hqx_of_hoke (ike_whenE _ (ho_resetUntypedCap _))) fun _ => R16.ne_liftE _

theorem hqx_invokeTcb (i : TcbInvocation) : HQX (invokeTcb (Z := Unit) i) := by
  cases i
  case threadControlCaps target slot fh th cr vr buf =>
    simp only [invokeTcb]
    refine hqx_of_ike ?_
    refine ike_bind (hq_installTcbCap _ _ _ _) fun _ => ?_
    refine ike_bind (hq_installTcbCap _ _ _ _) fun _ => ?_
    refine ike_bind (hq_installTcbCap _ _ _ _) fun _ => ?_
    refine ike_bind (hq_installTcbCap _ _ _ _) fun _ => ?_
    exact ike_bind (hq_installTcbFrameCap _ _ _) fun _ => ike_returnOk _
  case threadControlSched target slot fh mcp prio sc =>
    simp only [invokeTcb]
    exact hqx_bind_ike (hq_installTcbCap _ _ _ _) fun _ => hqx_of_ne (by ne_auto)
  case notificationControl t o =>
    cases o <;> (simp only [invokeTcb]; exact hqx_of_ne (R16.ne_liftE _))
  all_goals (simp only [invokeTcb]; exact hqx_of_ne (R16.ne_liftE _))

theorem hqx_invokeCnode (i : CnodeInvocation) : HQX (invokeCnode (Z := Unit) i) := by
  cases i
  case revokeCall sl => simp only [invokeCnode]; exact hqx_of_ike (hq_capRevoke sl)
  case deleteCall sl => simp only [invokeCnode]; exact hqx_of_ike (hq_capDelete sl)
  case cancelBadgedSendsCall c =>
    cases c <;> (simp only [invokeCnode]; first | exact hqx_of_ne (R16.ne_withoutPreemption _) | exact hqx_of_ne (R16.ne_liftE _))
  all_goals (simp only [invokeCnode]; exact hqx_of_ne (R16.ne_withoutPreemption _))

/-- **Every error outcome of `fl4_perform_invocation` from an `HQ` state has `HO`.** -/
theorem hqx_fl4PerformInvocation (blk call don : Bool) (inv : Fl4Invocation) :
    HQX (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv
  case invokeUntyped i =>
    simp only [fl4PerformInvocation]
    exact hqx_bind_ne (hqx_fl4InvokeUntyped i) fun _ => R16.ne_returnOk _
  case invokeTCB i => simp only [fl4PerformInvocation]; exact hqx_invokeTcb i
  case invokeCNode i =>
    simp only [fl4PerformInvocation]
    exact hqx_bind_ne (hqx_invokeCnode i) fun _ => R16.ne_returnOk _
  case invokeFl4TCB i => simp only [fl4PerformInvocation]; exact hqx_of_ne (R16.ne_invokeFl4Tcb i)
  case invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact hqx_of_ne (R16.ne_bind (R16.ne_invokeFl4IrqControl i) fun _ => R16.ne_returnOk _)
  case invokeArchObject i => simp only [fl4PerformInvocation]; exact hqx_of_ne (R16.ne_fl4ArchPerformInvocation i)
  all_goals (simp only [fl4PerformInvocation]; exact hqx_of_ne (by ne_auto))

end

end Fl4Proofs.P3.SInvR.B8r
