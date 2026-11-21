/-
P3 (DESIGN.md §9), invariant line G1 (ctq14): **the deletion cone keeps
`DK C`**, part 1: the wake loops, `fast_finalise`, `cap_delete_one`,
`cancel_badged_sends` (spec side only, outside the JAtZ cone).

`DK C := EB true ∧ ct = C ∧ Simple ∧ NQ [C]` (ctq12's SpecInvCqC3). Every
function of the cone keeps it as a plain state invariant (all outcomes): the
only writers that break a conjunct are the wake-ups of `cancel_all_ipc` /
`cancel_badged_sends` / `cancel_all_signals`, whose `possible_switch_to` may
leave a switch pending (not `Simple`) — each loop ends in
`reschedule_required` (`choose_new_thread`, `Simple` again).

* The loop invariant **`DZJ C := EB true ∧ ct = C ∧ NQ [C]`**. A woken thread
  `t` is `≠ C` *at its own step*: `tcb_ep_dequeue` / `tcb_ntfn_dequeue` assert
  `t` is in the endpoint / notification queue at that state, and `NQ [C]`
  says `C` is in no such queue (no distinctness of the read queue needed).
  So `possible_switch_to t` keeps `EB true` (`eb_possibleSwitchTo_p`).
* `restart_thread_if_no_fault`'s Inactive arm: the dequeued thread was
  BlockedOnSend / BlockedOnReceive at the dequeue (nq2's EpQB), so `NPQ t`
  there (`npq_nr`), carried by `DZW t C` through the dequeue, the state read
  and `reply_unlink_tcb` (np / tq leaves), then `eb_setThreadState_p`.
* `dz_cancelAllIpc`, `dz_cancelBadgedSends`, `dz_cancelAllSignals`:
  `IK (DK C)`; `dz_fastFinalise`, **`dz_capDeleteOne`**, and the discharged
  ctq12 hypotheses **`ebCapDeleteOneH : EbCapDeleteOneH`**,
  **`ebCancelBadgedSendsH : EbCancelBadgedSendsH`**.
-/
import Fl4Proofs.P3.SpecInvCqC3
open Classical

namespace Fl4Proofs.P3.SInvQ.R14
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.P12

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Combinators -/

/-- The loop invariant of the wake loops. -/
abbrev DZJ (C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ NQ [C] s

/-- Inside one wake step: `t` (the dequeued thread) has `NPQ`. -/
abbrev DZW (t C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ NPQ t s

theorem dz_w_of {α : Type} {t C : ObjRef} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : CTK C m)
    (h3 : IK (NP t) m) (h4 : IK (TQU t) m) : IK (DZW t C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2.1 y hy, (h4 σ ⟨h.1.1.1.1.1, h.2.2.2⟩ y hy).2⟩

theorem dz_j_of {α : Type} {C : ObjRef} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : CTK C m)
    (h4 : NQK [C] m) : IK (DZJ C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h4 σ h.2.2 y hy⟩

theorem dz_ik_hk1 {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HK1 P P m :=
  fun σ hσ x hx => h σ hσ x hx

/-- `reschedule_required` ends a wake loop: `DZJ C` becomes `DK C`. -/
theorem dz_rescheduleRequired (C : ObjRef) : HK1 (DZJ C) (DK C) (rescheduleRequired (Z := Unit)) := by
  intro σ h y hy
  refine ⟨eb_rescheduleRequired σ h.1 y hy, SInv.ct_rescheduleRequired (cq := C) σ h.2.1 y hy, fun t => ?_,
    SInv.nq_rescheduleRequired (Kq := [C]) σ h.2.2 y hy⟩
  have hc : y.2.schedulerAction = .chooseNewThread := rescheduleRequired_cn σ y hy
  rw [hc]; intro e; cases e

/-! ## The wake steps -/

/-- `tcb_ntfn_dequeue` asserts the thread is in the notification's queue. -/
theorem dz_tcbNtfnDequeue_mem {t n : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (tcbNtfnDequeue (Z := Unit) t n σ).1) :
    ∃ x, σ.kheap n = some (.notification x) ∧ t ∈ x.ntfnObj.ntfnQueue := by
  unfold tcbNtfnDequeue at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  obtain ⟨hk, e1⟩ := mem_getSimpleKo hy1
  obtain ⟨a, s1⟩ := y1
  simp only at hk e1; subst e1
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz] at hy
  obtain ⟨z, ⟨hq, rfl⟩, hy⟩ := hy
  exact ⟨a, hk, hq⟩

/-- Restart, the refill check, `possible_switch_to` of a thread `≠ C`. -/
theorem dz_restartTail (t C : ObjRef) (hne : t ≠ C) (σ : State Unit) (hE : EB true σ) (hC : CTh C σ)
    (y : Unit × State Unit)
    (hy : y ∈ ((do
      setThreadState (Z := Unit) t .restart
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scOpt
      possibleSwitchTo (Z := Unit) t) σ).1) : EB true y.2 := by
  obtain ⟨z, hz, hy⟩ := hy
  have e1 : EB true z.2 := eb_setThreadState_r t .restart rfl σ hE z hz
  have r1 : RnH t z.2.kheap := (tqc_setThreadState_r t .restart rfl σ z hE.1.1.1 hz).2
  have c1 : z.2.curThread = C := ct_setThreadState C t .restart σ hC z hz
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : EB true z3.2 :=
    (show EBK true (ifCondRefillUnblockCheck (Z := Unit) x2.tcbSchedContext (some false) (some true)) by eb_auto)
      z.2 e1 z3 hz3
  have hw := Sched.nkt_ifCondRefillUnblockCheck _ _ _ z.2 z3 hz3
  have r3 := rnH_of_tkw hw r1
  have c3 : z3.2.curThread = C := hw.ct.trans c1
  exact eb_possibleSwitchTo_p t z3.2 r3 (fun _ => by rw [c3]; exact hne) e3 y hy

/-- `restart_thread_if_no_fault t`, `t ≠ C` with `NPQ t`. -/
theorem dz_restartThreadIfNoFault (t C : ObjRef) (hne : t ≠ C) :
    HK1 (DZW t C) (EB true) (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault
  intro σ hσ y ⟨z, hz, hy⟩
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · exact dz_restartTail t C hne σ hσ.1 hσ.2.1 y hy
  · exact eb_setThreadState_p t .inactive σ (Or.inr hσ.2.2) hσ.1 y hy

/-- The dequeued thread of an endpoint: `≠ C` and `NPQ` (EpQB, NQ [C]). -/
theorem dz_epDequeued {C t e : ObjRef} {σ : State Unit} (hσ : DZJ C σ) {y : Unit × State Unit}
    (hy : y ∈ (tcbEpDequeue (Z := Unit) t e σ).1) : t ≠ C ∧ NPQ t σ := by
  obtain ⟨x, hk, hq⟩ := tcbEpDequeue_mem hy
  obtain ⟨yt, hyt, hbt⟩ := hσ.2.2.1.2 e x t hk hq
  have hr : runnable yt.tcbState = false := by
    revert hbt; cases yt.tcbState <;> simp [epBlocked, runnable]
  refine ⟨?_, npq_nr hσ.1.1 hyt hr⟩
  rintro rfl
  exact (hσ.2.2.2 t (List.mem_singleton_self _)).2.2 ⟨e, x, hk, hq⟩

theorem dz_w_tcbEpDequeue (t C e : ObjRef) : IK (DZW t C) (tcbEpDequeue (Z := Unit) t e) :=
  dz_w_of (by eb_auto) (SInv.ct_tcbEpDequeue _ _) (by np_auto) (by tq_auto)

/-- **`remove_and_restart_ep_queued_thread`** keeps the loop invariant. -/
theorem dz_removeAndRestartEpQueuedThread (C t e : ObjRef) :
    IK (DZJ C) (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  intro σ hσ y hy
  have hN := SInv.nq_removeAndRestartEpQueuedThread (Kq := [C]) t e σ hσ.2.2 y hy
  have hT := SInv.ct_removeAndRestartEpQueuedThread (cq := C) t e σ hσ.2.1 y hy
  refine ⟨?_, hT, hN⟩
  unfold removeAndRestartEpQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨hne, hP⟩ := dz_epDequeued hσ hz1
  have h1 : DZW t C z1.2 := dz_w_tcbEpDequeue t C e σ ⟨hσ.1, hσ.2.1, hP⟩ z1 hz1
  refine (?_ : HK1 (DZW t C) (EB true) _) z1.2 h1 y hy
  unfold getThreadState
  refine hk1_bind (dz_ik_hk1 (dz_w_of (by eb_auto) (by ct_auto) (by np_auto) (by tq_auto))) fun st => ?_
  refine hk1_bind (dz_ik_hk1 (ik_pure _)) fun ro => ?_
  refine hk1_bind (dz_ik_hk1 (dz_w_of (by eb_auto) (by ct_auto) (by np_auto) (by tq_auto))) fun _ => ?_
  exact dz_restartThreadIfNoFault t C hne

/-- **`remove_and_restart_badged_thread`** keeps the loop invariant. -/
theorem dz_removeAndRestartBadgedThread (C t e : ObjRef) (b : Badge) :
    IK (DZJ C) (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  intro σ hσ y hy
  have hN := SInv.nq_removeAndRestartBadgedThread (Kq := [C]) t e b σ hσ.2.2 y hy
  have hT := SInv.ct_removeAndRestartBadgedThread (cq := C) t e b σ hσ.2.1 y hy
  refine ⟨?_, hT, hN⟩
  unfold removeAndRestartBadgedThread getThreadState at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain ⟨x0, hx0, rfl⟩ := q1_mem_threadGet hz0
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨hne, hP⟩ := dz_epDequeued hσ hz1
    have h1 : DZW t C z1.2 := dz_w_tcbEpDequeue t C e σ ⟨hσ.1, hσ.2.1, hP⟩ z1 hz1
    exact dz_restartThreadIfNoFault t C hne z1.2 h1 y hy
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

/-- **`remove_and_restart_ntfn_queued_thread`** keeps the loop invariant. -/
theorem dz_removeAndRestartNtfnQueuedThread (C t n : ObjRef) :
    IK (DZJ C) (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  intro σ hσ y hy
  have hN := SInv.nq_removeAndRestartNtfnQueuedThread (Kq := [C]) t n σ hσ.2.2 y hy
  have hT := SInv.ct_removeAndRestartNtfnQueuedThread (cq := C) t n σ hσ.2.1 y hy
  refine ⟨?_, hT, hN⟩
  unfold removeAndRestartNtfnQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  have hne : t ≠ C := by
    obtain ⟨x, hk, hq⟩ := dz_tcbNtfnDequeue_mem hz1
    rintro rfl
    exact (hσ.2.2.2 t (List.mem_singleton_self _)).1 ⟨n, x, hk, hq⟩
  have e1 : EB true z1.2 := (show EBK true (tcbNtfnDequeue (Z := Unit) t n) by eb_auto) σ hσ.1 z1 hz1
  have c1 : CTh C z1.2 := SInv.ct_tcbNtfnDequeue (cq := C) t n σ hσ.2.1 z1 hz1
  exact dz_restartTail t C hne z1.2 e1 c1 y hy

/-! ## The loops -/

theorem dz_cancelAllIpc (C e : ObjRef) : IK (DK C) (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ik_pure _
  · refine ik_pure_bind ?_
    intro σ hσ y ⟨z, hz, hy⟩
    have hz' : DZJ C z.2 :=
      ik_mapMx (fun t => dz_removeAndRestartEpQueuedThread C t e) _ σ ⟨hσ.1, hσ.2.1, hσ.2.2.2⟩ z hz
    exact dz_rescheduleRequired C z.2 hz' y hy

theorem dz_cancelBadgedSends (C e : ObjRef) (b : Badge) : IK (DK C) (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · intro σ hσ y ⟨z, hz, hy⟩
    have hz' : DZJ C z.2 :=
      ik_mapMx (fun t => dz_removeAndRestartBadgedThread C t e b) _ σ ⟨hσ.1, hσ.2.1, hσ.2.2.2⟩ z hz
    exact dz_rescheduleRequired C z.2 hz' y hy
  · exact ik_pure _

theorem dz_cancelAllSignals (C n : ObjRef) : IK (DK C) (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ntfn => ?_
  split
  · intro σ hσ y ⟨z, hz, hy⟩
    have hz' : DZJ C z.2 :=
      ik_mapMx (fun t => dz_removeAndRestartNtfnQueuedThread C t n) _ σ ⟨hσ.1, hσ.2.1, hσ.2.2.2⟩ z hz
    exact dz_rescheduleRequired C z.2 hz' y hy
  · exact ik_pure _

/-! ## `fast_finalise`, `cap_delete_one` -/

/-- `reply_remove` of a thread read BlockedOnReply (it joins `K`: nq3's `nq_consR`). -/
theorem dz_replyRemove_p (C t r r' : ObjRef) (σ : State Unit) (x : Tcb) (hx : σ.kheap t = some (.tcb x))
    (hs : x.tcbState = .blockedOnReply r') : IKp (DK C) σ (replyRemove (Z := Unit) t r) := by
  intro hσ y hy
  have hN : NQ [t, C] σ := nq_consR hσ.2.2.2 hx (by rw [hs]; exact fun h => h) (by rw [hs]; rfl)
  exact ⟨(show EBK true (replyRemove (Z := Unit) t r) by eb_auto) σ hσ.1 y hy,
    SInv.ct_replyRemove (cq := C) t r σ hσ.2.1 y hy,
    fun u => (show IK (NSw u) (replyRemove (Z := Unit) t r) by unfold replyRemove; p12_nsw_auto) σ (hσ.2.2.1 u) y hy,
    nq_tail (SInv.nq_replyRemove (Kq := [t, C]) t r (List.mem_cons_self ..) σ hN y hy)⟩

theorem dz_cancelIpc (C t : ObjRef) : IK (DK C) (cancelIpc (Z := Unit) t) :=
  dk_of (by eb_auto) (SInv.ct_cancelIpc _) (fun u => nsw_cancelIpc u t) (SInv.nq_cancelIpc _)

theorem dz_schedContextMaybeUnbindNtfn (C n : ObjRef) : IK (DK C) (schedContextMaybeUnbindNtfn (Z := Unit) n) :=
  dk_of (by eb_auto) (SInv.ct_schedContextMaybeUnbindNtfn _) (fun _ => by unfold schedContextMaybeUnbindNtfn; p12_nsw_auto)
    (SInv.nq_schedContextMaybeUnbindNtfn _)

theorem dz_unbindMaybeNotification (C n : ObjRef) : IK (DK C) (unbindMaybeNotification (Z := Unit) n) :=
  dk_of (by eb_auto) (SInv.ct_unbindMaybeNotification _) (fun _ => by unfold unbindMaybeNotification; p12_nsw_auto)
    (SInv.nq_unbindMaybeNotification _)

/-- The reply arm of `fast_finalise` / `finalise_cap` after the TCB read. -/
macro "dz_reply_arm" : tactic => `(tactic| (
  unfold getThreadState
  refine ikq_threadGet_bind fun σ x hx => ?_
  cases hs : x.tcbState <;> dsimp only
  all_goals first
    | exact dz_replyRemove_p _ _ _ _ σ x hx hs
    | exact ikp_of_ik (dz_cancelIpc _ _) σ))

/-- Reads keep anything. -/
macro "dz_rd" : tactic => `(tactic| repeat' (first | ik_step0 | ik_unfold))

theorem dz_fastFinalise (C : ObjRef) (c : Cap) (final : Bool) : IK (DK C) (fastFinalise (Z := Unit) c final) := by
  cases c
  case nullCap => exact ik_pure _
  case replyCap r _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    refine ik_bind (by dz_rd) fun tp => ?_
    split
    · exact ik_pure _
    · dz_reply_arm
  case endpointCap r _ _ =>
    simp only [fastFinalise]
    exact ik_when _ (dz_cancelAllIpc C r)
  case notificationCap r _ _ =>
    simp only [fastFinalise]
    refine ik_when _ ?_
    exact ik_bind (dz_schedContextMaybeUnbindNtfn C r) fun _ =>
      ik_bind (dz_unbindMaybeNotification C r) fun _ => dz_cancelAllSignals C r
  all_goals (simp only [fastFinalise]; exact ik_fail)

theorem dz_emptySlot (C : ObjRef) (slot : CslotPtr) (ci : Cap) : IK (DK C) (emptySlot (Z := Unit) slot ci) :=
  dk_of (by eb_auto) (SInv.ct_emptySlot _ _) (fun _ => by unfold emptySlot; p12_nsw_auto) (SInv.nq_emptySlot _ _)

theorem dz_isFinalCap (C : ObjRef) (c : Cap) : IK (DK C) (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; dz_rd

/-- **`cap_delete_one` keeps `DK C`.** -/
theorem dz_capDeleteOne (C : ObjRef) (slot : CslotPtr) : IK (DK C) (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne
  refine ik_bind (by dz_rd) fun cap => ?_
  refine ik_unless _ ?_
  exact ik_bind (dz_isFinalCap C cap) fun fin => ik_bind (dz_fastFinalise C cap fin) fun _ => dz_emptySlot C slot _

/-- **ctq12's `EbCapDeleteOneH`, discharged.** -/
theorem ebCapDeleteOneH : EbCapDeleteOneH := fun C slot => dz_capDeleteOne C slot

/-- **ctq12's `EbCancelBadgedSendsH`, discharged.** -/
theorem ebCancelBadgedSendsH : EbCancelBadgedSendsH := fun C ep b => dz_cancelBadgedSends C ep b

end

end Fl4Proofs.P3.SInvQ.R14
