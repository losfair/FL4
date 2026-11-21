/-
P3 (DESIGN.md §9), invariant line G1 (rd8f): **the deletion cone keeps `Rdy`**,
part 1: the wake loops and `cancel_ipc` (spec side only, outside the JAtZ cone).

* The wake steps (`remove_and_restart_ep_queued_thread`,
  `…_badged_thread`, `…_ntfn_queued_thread`) keep `Rdy ∧ NQ []`: the woken
  thread is in the endpoint / notification queue at its dequeue (the dequeue
  asserts it), so by nq2's `EpQB` / `NtfnQB` it is BlockedOnSend /
  BlockedOnReceive / BlockedOnNotification there; `restart_thread_if_no_fault`
  restarts it only with no fault, so it is `BlkR` at the dequeue and R3 gives
  `RT` (rd8d: `RdyT` if bound). `RT` rides along `SVS` (the dequeue, the state
  read, `reply_unlink_tcb`, Restart) and rd_ifCond's `UK` to
  `possible_switch_to` (`rd_possibleSwitchTo_q`). A sender with a fault keeps
  its fault to the read (no reply unlink for a sender: the state read is
  BlockedOnSend), so it is set Inactive. `rdq_cancelAllIpc`,
  `rdq_cancelBadgedSends`, `rdq_cancelAllSignals`.
* **`rd_cancelIpc` (every thread state)**: the fault clear of a
  BlockedOnSend thread with a timeout fault makes it `BlkR` for one step (R3
  may fail there), so the send arm is proved on the outcome state directly
  (`rd_cancelIpc_send`): the end state equals the start with the thread
  Inactive (fault none) and the endpoint rewritten, both `OK1` writes. Every
  other arm: the fault clear keeps `Rdy` (`rdy_clrFault`: a non-sender's
  `BlkR` does not read the fault), then rd7's `rs_blockedCancelIpc`, the
  leaves of `cancel_signal`, rd's `rd_replyRemoveTcb`.
* `rd_suspend`: `cancel_ipc`, then leaves.
-/
import Fl4Proofs.P3.SpecInvRd8dC
import Fl4Proofs.P3.SpecInvCqH2
open Classical

namespace Fl4Proofs.P3.SInvR.B8f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `RT` along the frames -/

theorem rT_uk {s s' : State Unit} {t : ObjRef} (h : B8d.RT s t) (hU : UK s s') : B8d.RT s' t :=
  fun x c hx hc => hU.2.1 t (h x c (hU.2.2 t x hx) hc)

/-- An endpoint-queued thread with no fault, or receive-blocked, is `RT` (R3). -/
theorem rT_epq {s : State Unit} (hR : Rdy s) {t : ObjRef} {x : Tcb} (hx : s.kheap t = some (.tcb x))
    {e : ObjRef} (hb : epBlocked x.tcbState = some e)
    (hf : x.tcbFault = none ∨ receiveBlocked x.tcbState = true) : B8d.RT s t := by
  intro x' c hx' hc
  rw [hx] at hx'; cases hx'
  have key : ∀ ts, epBlocked ts = some e → (x.tcbFault = none ∨ receiveBlocked ts = true) →
      BlkR ts x.tcbFault := by
    intro ts hb hf
    cases ts
    case blockedOnSend e' d =>
      refine Or.inr (Or.inl ⟨e', d, rfl, fun b h => ?_⟩)
      rcases hf with hf | hf
      · rw [hf] at h; cases h
      · simp [receiveBlocked] at hf
    case blockedOnReceive e' r d => exact Or.inr (Or.inr ⟨e', r, d, rfl⟩)
    all_goals simp [epBlocked] at hb
  exact hR.2.2.1 t x c hx (key _ hb hf) hc

/-! ## The restart -/

/-- Restart, the refill check, `possible_switch_to`, from `RT`. -/
theorem rd_restartTail (t : ObjRef) (s : State Unit) (hR : Rdy s) (hT : B8d.RT s t)
    {y : Unit × State Unit}
    (hy : y ∈ ((do
      setThreadState (Z := Unit) t .restart
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scOpt
      possibleSwitchTo (Z := Unit) t) s).1) : Rdy y.2 := by
  obtain ⟨z, hz, hy⟩ := hy
  have r1 : Rdy z.2 := rd_setThreadState t .restart trivial s hR z hz
  have t1 : B8d.RT z.2 t := B8d.rT_svs hT (SVK.sv_setThreadState' t .restart s z hz)
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨x2, -, rfl⟩ := q1_mem_threadGet hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have u3 := rd_ifCond x2.tcbSchedContext (some false) (some true) z.2 r1 hz3
  exact rd_possibleSwitchTo_q t z3.2 (rT_uk t1 u3) u3.1 y hy

/-- **`restart_thread_if_no_fault`** from `RT` of a fault-free thread. -/
theorem rd_restartThreadIfNoFault (t : ObjRef) (s : State Unit) (hR : Rdy s)
    (hF : ∀ x, s.kheap t = some (.tcb x) → x.tcbFault = none → B8d.RT s t)
    {y : Unit × State Unit} (hy : y ∈ (restartThreadIfNoFault (Z := Unit) t s).1) : Rdy y.2 := by
  unfold restartThreadIfNoFault at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  dsimp only at hy
  split at hy
  · rename_i hf
    exact rd_restartTail t s hR (hF x hx hf) hy
  · exact rd_setThreadState t .inactive trivial s hR y hy

/-! ## The wake steps -/

abbrev RQ (s : State Unit) : Prop := Rdy s ∧ NQ [] s

theorem replyOpt_send {ts : ThreadState} {e : ObjRef} (hb : epBlocked ts = some e)
    (hr : receiveBlocked ts = false) :
    (if isBlockedOnReceive ts then replyObject ts else none) = none := by
  cases ts <;> simp_all [epBlocked, receiveBlocked, replyObject]

/-- **`remove_and_restart_ep_queued_thread`** keeps `Rdy ∧ NQ []`. -/
theorem rdq_removeAndRestartEpQueuedThread (t e : ObjRef) :
    IK RQ (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartEpQueuedThread (Kq := []) t e σ hσ.2 y hy⟩
  unfold removeAndRestartEpQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨ep, ep', hk, hq, -, e1⟩ := Sched.tcbEpDequeue_out hz1
  obtain ⟨x, hx, hb⟩ := hσ.2.1.2 e ep t hk hq
  have r1 : Rdy z1.2 := rd_tcbEpDequeue t e σ hσ.1 z1 hz1
  have hS1 : SVK.SVS σ z1.2 := sv_tcbEpDequeue t e σ z1 hz1
  have hne : t ≠ e := fun h => by rw [h, hk] at hx; cases hx
  have hx1 : z1.2.kheap t = some (.tcb x) := by
    rw [e1]; show Function.update σ.kheap e _ t = _; rw [Function.update_of_ne hne]; exact hx
  obtain ⟨z2, hz2, hy⟩ := hy
  unfold getThreadState at hz2
  obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz2
  rw [hx1] at hx2; cases hx2
  obtain ⟨z3, hz3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz3] at hy
  obtain ⟨z4, hz4, hy⟩ := hy
  dsimp only at hz4 hy
  by_cases hrcv : receiveBlocked x.tcbState = true
  · have hT : B8d.RT σ t := rT_epq hσ.1 hx hb (Or.inr hrcv)
    have h4 : Rdy z4.2 ∧ SVK.SVS z1.2 z4.2 := by
      revert hz4
      cases (if isBlockedOnReceive x.tcbState then replyObject x.tcbState else none) with
      | none => intro h; rw [Set.mem_singleton_iff.1 h]; exact ⟨r1, SVK.SVS.refl _⟩
      | some r => intro h; exact ⟨rd_replyUnlinkTcb t r z1.2 r1 z4 h, SVK.sv_replyUnlinkTcb t r z1.2 z4 h⟩
    exact rd_restartThreadIfNoFault t z4.2 h4.1 (fun _ _ _ => B8d.rT_svs hT (hS1.trans h4.2)) hy
  · rw [replyOpt_send hb (by simpa using hrcv)] at hz4
    obtain rfl : z4 = ((), z1.2) := Set.mem_singleton_iff.1 hz4
    refine rd_restartThreadIfNoFault t z1.2 r1 (fun x' hx' hf => ?_) hy
    rw [hx1] at hx'; cases hx'
    exact B8d.rT_svs (rT_epq hσ.1 hx hb (Or.inl hf)) hS1

/-- **`remove_and_restart_badged_thread`** keeps `Rdy ∧ NQ []`. -/
theorem rdq_removeAndRestartBadgedThread (t e : ObjRef) (b : Badge) :
    IK RQ (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartBadgedThread (Kq := []) t e b σ hσ.2 y hy⟩
  unfold removeAndRestartBadgedThread getThreadState at hy
  obtain ⟨z0, hz0, hy⟩ := hy
  obtain ⟨x0, -, rfl⟩ := q1_mem_threadGet hz0
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨ep, ep', hk, hq, -, e1⟩ := Sched.tcbEpDequeue_out hz1
    obtain ⟨x, hx, hb⟩ := hσ.2.1.2 e ep t hk hq
    have r1 : Rdy z1.2 := rd_tcbEpDequeue t e σ hσ.1 z1 hz1
    have hS1 : SVK.SVS σ z1.2 := sv_tcbEpDequeue t e σ z1 hz1
    have hne : t ≠ e := fun h => by rw [h, hk] at hx; cases hx
    have hx1 : z1.2.kheap t = some (.tcb x) := by
      rw [e1]; show Function.update σ.kheap e _ t = _; rw [Function.update_of_ne hne]; exact hx
    refine rd_restartThreadIfNoFault t z1.2 r1 (fun x' hx' hf => ?_) hy
    rw [hx1] at hx'; cases hx'
    exact B8d.rT_svs (rT_epq hσ.1 hx hb (Or.inl hf)) hS1
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

/-- **`remove_and_restart_ntfn_queued_thread`** keeps `Rdy ∧ NQ []`. -/
theorem rdq_removeAndRestartNtfnQueuedThread (t n : ObjRef) :
    IK RQ (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  intro σ hσ y hy
  refine ⟨?_, nq_removeAndRestartNtfnQueuedThread (Kq := []) t n σ hσ.2 y hy⟩
  unfold removeAndRestartNtfnQueuedThread at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨xn, hk, hq⟩ := R14.dz_tcbNtfnDequeue_mem hz1
  obtain ⟨x, hx, hs⟩ := hσ.2.1.1 n xn t hk hq
  have hT : B8d.RT σ t := fun x' c hx' hc => by
    rw [hx] at hx'; cases hx'
    exact hσ.1.2.2.1 t x c hx (Or.inl ⟨n, hs⟩) hc
  exact rd_restartTail t z1.2 (rd_tcbNtfnDequeue t n σ hσ.1 z1 hz1)
    (B8d.rT_svs hT (sv_tcbNtfnDequeue t n σ z1 hz1)) hy

theorem rdq_rescheduleRequired : IK RQ (rescheduleRequired (Z := Unit)) :=
  fun σ hσ y hy => ⟨rd_rescheduleRequired σ hσ.1 y hy, nq_rescheduleRequired (Kq := []) σ hσ.2 y hy⟩

/-! ## The loops -/

theorem rdq_cancelAllIpc (e : ObjRef) : IK RQ (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ik_pure _
  · refine ik_pure_bind ?_
    exact ik_bind (ik_mapMx (fun t => rdq_removeAndRestartEpQueuedThread t e) _) fun _ => rdq_rescheduleRequired

theorem rdq_cancelBadgedSends (e : ObjRef) (b : Badge) : IK RQ (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ep => ?_
  split
  · exact ik_bind (ik_mapMx (fun t => rdq_removeAndRestartBadgedThread t e b) _) fun _ => rdq_rescheduleRequired
  · exact ik_pure _

theorem rdq_cancelAllSignals (n : ObjRef) : IK RQ (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun ntfn => ?_
  split
  · exact ik_bind (ik_mapMx (fun t => rdq_removeAndRestartNtfnQueuedThread t n) _) fun _ => rdq_rescheduleRequired
  · exact ik_pure _

/-! ## `cancel_ipc` -/

/-- The fault clear of a TCB not BlockedOnSend keeps `Rdy`. -/
theorem rdy_clrFault {σ : State Unit} (hR : Rdy σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d) :
    Rdy { σ with kheap := Function.update σ.kheap t (some (.tcb { x with tcbFault := none })) } := by
  refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h hb _ => ?_, by rw [hx]; rfl⟩
  · rw [hx] at h; cases h; exact ⟨_, rfl, rfl⟩
  · cases h
    refine ⟨x, hx, rfl, ?_⟩
    rcases hb with ⟨n, hn⟩ | ⟨e, d, hs, -⟩ | ⟨e, r, d, hr⟩
    · exact Or.inl ⟨n, hn⟩
    · exact absurd hs (hns e d)
    · exact Or.inr (Or.inr ⟨e, r, d, hr⟩)

/-- **`cancel_ipc`'s send arm**: the outcome is the start with the thread
Inactive (fault cleared) and the endpoint rewritten. -/
theorem rd_cancelIpc_send {σ : State Unit} (hR : Rdy σ) {t : ObjRef} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) {e : ObjRef} {d : SenderPayload} {y : Unit × State Unit}
    (hy : y ∈ (blockedCancelIpc (Z := Unit) (.blockedOnSend e d) t none
      { σ with kheap := Function.update σ.kheap t (some (.tcb { x with tcbFault := none })) }).1) :
    Rdy y.2 := by
  unfold blockedCancelIpc getBlockingObject at hy
  obtain ⟨⟨ep0, s0⟩, hz0, hy⟩ := hy
  have e0 : s0 = { σ with kheap := Function.update σ.kheap t (some (.tcb { x with tcbFault := none })) } :=
    cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz0
  subst e0
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨ep, ep', hk, -, -, e1⟩ := Sched.tcbEpDequeue_out hz1
  dsimp only at hy
  unfold setThreadState at hy
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain ⟨x3, hx3, e3⟩ := SInv.mem_threadSet hz3
  have hne : t ≠ ep0 := by
    intro h; subst h
    have : Function.update σ.kheap t (some (.tcb { x with tcbFault := none })) t = some (.endpoint ep) := hk
    rw [Function.update_self] at this; cases this
  have hx3' : x3 = { x with tcbFault := none } := by
    rw [e1] at hx3
    have h' : Function.update (Function.update σ.kheap t (some (.tcb { x with tcbFault := none })))
        ep0 (some (.endpoint ep')) t = some (.tcb x3) := hx3
    rw [Function.update_of_ne hne, Function.update_self] at h'
    cases h'; rfl
  subst hx3'
  have hRc : Rdy { σ with kheap :=
      (Function.update σ.kheap t (some (.tcb { ({ x with tcbFault := none } : Tcb) with tcbState := .inactive }))) } := by
    refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h hb _ => ?_, by rw [hx]; rfl⟩
    · rw [hx] at h; cases h; exact ⟨_, rfl, rfl⟩
    · cases h
      exact absurd hb (nb_blk (ts := .inactive) trivial _)
  have hk0 : σ.kheap ep0 = some (.endpoint ep) := by
    have : Function.update σ.kheap t (some (.tcb { x with tcbFault := none })) ep0 = some (.endpoint ep) := hk
    rwa [Function.update_of_ne (Ne.symm hne)] at this
  have hRe := rdy_upd hRc ep0 (.endpoint ep')
    (ok1_of_none (fun x0 h => by
        have : Function.update σ.kheap t (some (.tcb { ({ x with tcbFault := none } : Tcb) with tcbState := .inactive }))
          ep0 = some (.tcb x0) := h
        rw [Function.update_of_ne (Ne.symm hne), hk0] at this; cases this)
      (by show SV (Function.update σ.kheap t _ ep0) = none; rw [Function.update_of_ne (Ne.symm hne), hk0]; rfl)
      (fun _ h => by cases h) rfl)
  refine rd_setThreadStateAct t z3.2 (rdy_congr hRe ?_ ?_ ?_ ?_ ?_ ?_) y hy
  · rw [e3, e1]
    dsimp only
    funext q
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  all_goals (rw [e3, e1]; try first | rfl | exact fun _ h => h)

/-- **`cancel_ipc` keeps `Rdy`** (every thread state). -/
theorem rd_cancelIpc (t : ObjRef) : IK Rdy (cancelIpc (Z := Unit) t) := by
  intro σ hR y hy
  unfold cancelIpc at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold getThreadState at hz
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨x2, hx2, e2⟩ := SInv.mem_threadSet hz2
  rw [hx] at hx2; cases hx2
  dsimp only at hy
  by_cases hsnd : ∃ e d, x.tcbState = .blockedOnSend e d
  · obtain ⟨e, d, hs⟩ := hsnd
    rw [hs] at hy
    rw [e2] at hy
    exact rd_cancelIpc_send hR hx hy
  · have hns : ∀ e d, x.tcbState ≠ .blockedOnSend e d := fun e d h => hsnd ⟨e, d, h⟩
    have hR2 : Rdy z2.2 := by rw [e2]; exact rdy_clrFault hR hx hns
    revert hy
    cases hst : x.tcbState
    case blockedOnSend e d => exact absurd hst (hns e d)
    case blockedOnReceive e r d =>
      intro hy
      exact (rs_blockedCancelIpc z2.2 _ t r z2.2 ⟨hR2, SVK.SVS.refl _⟩ y hy).1
    case blockedOnNotification n =>
      intro hy
      exact (show IK Rdy (cancelSignal (Z := Unit) t n) by unfold cancelSignal; exact ik_bind (rd_tcbNtfnDequeue t n) fun _ => rd_setThreadState t .inactive trivial) z2.2 hR2 y hy
    case blockedOnReply r =>
      intro hy
      exact rd_replyRemoveTcb t r z2.2 hR2 y hy
    all_goals (intro hy; exact (ik_pure' () : IK Rdy (NonDet.pure () : NonDet (State Unit) Unit)) z2.2 hR2 y hy)

/-- **`suspend` keeps `Rdy`.** -/
theorem rd_suspend (t : ObjRef) : IK Rdy (suspend (Z := Unit) t) := by
  unfold suspend
  refine ik_bind (rd_cancelIpc t) fun _ => ?_
  unfold getThreadState
  refine ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun st => ?_
  refine ik_bind (ik_when _ (rd_updateRestartPc t)) fun _ => ?_
  refine ik_bind (rd_dequeue t) fun _ => ?_
  refine ik_bind (rd_tcbReleaseRemove t) fun _ => ?_
  refine ik_bind (rd_schedContextCancelYieldTo t) fun _ => ?_
  exact rd_setThreadState t .inactive trivial

end

end Fl4Proofs.P3.SInvR.B8f
