/-
P3 (DESIGN.md §9), invariant line G1 (ctq7): **`send_ipc` carries the
event bundle `EB k`** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq7).

* `NC t C s`: `t` has `NPQ` (neither switch target nor released, in no ready
  queue) and the current thread is `C`. Kept by the reads, the endpoint
  dequeue, `do_ipc_transfer` (the generated FX frames, SpecInvCqFX) and
  `reply_unlink_tcb` (it sets at most `choose_new_thread`).
* `eb_wakeDest`: the woken receiver is set Running and switched to; it is
  not current when `k` (read from the endpoint's receive queue, which by
  the caller's fact does not hold the current thread).
* **`eb_sendIpc_p`**: from `EB k`, `NPQ thread` (the sender may block: for
  the current thread under `EB true` this is `npq_ct`) and, when `k`, "the
  current thread is in no queue of the endpoint" (nq3's `NQ [ct]`).
-/
import Fl4Proofs.P3.SpecInvCqFX
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The sender's facts -/

/-- `t` has `NPQ` and the current thread is `C`. -/
abbrev NC (t C : ObjRef) (s : State Unit) : Prop := NPQ t s ∧ s.curThread = C

theorem nc_of_fx {α : Type} {m : NonDet (State Unit) α} (h : ∀ A R Q C, FXK A R Q C m) (t C : ObjRef) :
    IK (NC t C) m := by
  intro σ hσ y hy
  obtain ⟨e1, e2, e3, e4⟩ := h σ.schedulerAction σ.releaseQueue σ.readyQueues σ.curThread σ ⟨rfl, rfl, rfl, rfl⟩ y hy
  exact ⟨⟨⟨by rw [e1]; exact hσ.1.1.1, by rw [e2]; exact hσ.1.1.2⟩, by rw [e3]; exact hσ.1.2⟩, by rw [e4]; exact hσ.2⟩

theorem nc_setCn (t C : ObjRef) : IK (NC t C) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ h => ⟨⟨⟨(fun e => by cases e), h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem nc_doIpcTransfer (t C sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) :
    IK (NC t C) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) :=
  nc_of_fx (fun _ _ _ _ => fx_doIpcTransfer _ _ _ _ _) t C

syntax "nc_leaf" : tactic
macro_rules | `(tactic| nc_leaf) => `(tactic| with_reducible exact nc_setCn _ _)
macro_rules | `(tactic| nc_leaf) => `(tactic| with_reducible exact nc_doIpcTransfer _ _ _ _ _ _ _)

macro "nc_auto" : tactic => `(tactic| repeat' (first | nc_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem nc_tcbEpDequeue (t C d e : ObjRef) : IK (NC t C) (tcbEpDequeue (Z := Unit) d e) := by
  unfold tcbEpDequeue; nc_auto

theorem nc_replyUnlinkTcb (t C u r : ObjRef) : IK (NC t C) (replyUnlinkTcb (Z := Unit) u r) := by
  unfold replyUnlinkTcb; nc_auto

/-- The current thread is `C`. -/
abbrev CTh (C : ObjRef) (s : State Unit) : Prop := s.curThread = C

theorem ct_replyPush (C caller callee replyPtr : ObjRef) (canDonate : Bool) :
    IK (CTh C) (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem ct_setThreadState (C t : ObjRef) (ts : ThreadState) : IK (CTh C) (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState; repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem ct_schedContextDonate (C p t : ObjRef) : IK (CTh C) (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate; repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when))

/-! ## The woken receiver -/

/-- **The receiver's wake-up** (`send_ipc`'s tail): Running, the refill
check, `possible_switch_to`. -/
theorem eb_wakeDest {k : Bool} (dest : ObjRef) (σ : State Unit) (hne : k = true → dest ≠ σ.curThread) :
    IKp (EB k) σ (setThreadState (Z := Unit) dest .running >>= fun _ =>
      getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest >>= fun destSc =>
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc >>= fun _ => possibleSwitchTo (Z := Unit) dest) := by
  intro hσ y ⟨z, hz, hy⟩
  have e1 : EB k z.2 := eb_setThreadState_r dest .running rfl σ hσ z hz
  have r1 : RnH dest z.2.kheap := (tqc_setThreadState_r dest .running rfl σ z hσ.1.1.1 hz).2
  have c1 : z.2.curThread = σ.curThread := ct_setThreadState σ.curThread dest .running σ rfl z hz
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz2
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : EB k z3.2 :=
    (show EBK k (ifCondRefillUnblockCheck (Z := Unit) x2.tcbSchedContext (some false) (some false)) by eb_auto)
      z.2 e1 z3 hz3
  have hw := Sched.nkt_ifCondRefillUnblockCheck _ _ _ z.2 z3 hz3
  have r3 := rnH_of_tkw hw r1
  have c3 : z3.2.curThread = σ.curThread := hw.ct.trans c1
  exact eb_possibleSwitchTo_p dest z3.2 r3 (fun hk => by rw [c3]; exact hne hk) e3 y hy

/-! ## `send_ipc` -/

/-- The receiver arm after the receiver's state read (forward, on the
membership: the non-terminal `if`s are join points). -/
theorem eb_sendArm {k : Bool} (call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr dest : ObjRef)
    (reply : Option ObjRef) (C : ObjRef) (s : State Unit) (hN : NC thread C s) (hne : k = true → dest ≠ C)
    (hs : EB k s) (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) thread (some epptr) badge cg dest
      NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      let fault ← threadGet (Z := Unit) Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (cg ∨ cgr) ∧ reply ≠ none then
          replyPush (Z := Unit) thread dest (the reply) cd
        else
          setThreadState (Z := Unit) thread .inactive
      else NonDet.when (cd ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
        schedContextDonate (Z := Unit) (the threadSc) dest
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
      possibleSwitchTo (Z := Unit) dest) s).1) : EB k y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : EB k z3.2 := (show EBK k (doIpcTransfer (Z := Unit) thread (some epptr) badge cg dest) by eb_auto) s hs z3 h3
  have n3 := nc_doIpcTransfer thread C thread (some epptr) badge cg dest s hN z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have e4 : EB k z4.2 := (show EBK k (NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply) by eb_auto) z3.2 e3 z4 h4
  have n4 : NC thread C z4.2 := (show IK (NC thread C) (NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply) from
      ik_maybeM (fun r => nc_replyUnlinkTcb thread C dest r) reply) z3.2 n3 z4 h4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨x5, -, rfl⟩ := q1_mem_threadGet h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := q1_mem_threadGet h6
  dsimp only at hy
  have hw : ∀ s7 : State Unit, EB k s7 → s7.curThread = C → ∀ y' : Unit × State Unit,
      y' ∈ ((do
        setThreadState (Z := Unit) dest .running
        let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
        ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
        possibleSwitchTo (Z := Unit) dest) s7).1 → EB k y'.2 := fun s7 e7 c7 y' hy' =>
    eb_wakeDest dest s7 (fun hk => by rw [c7]; exact hne hk) e7 y' hy'
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact hw z7.2 (eb_replyPush_p thread dest _ cd z4.2 n4.1 e4 z7 h7)
        ((ct_replyPush C thread dest _ cd z4.2 n4.2 z7 h7)) y hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact hw z7.2 (eb_setThreadState_p thread .inactive z4.2 (Or.inr n4.1) e4 z7 h7)
        ((ct_setThreadState C thread .inactive z4.2 n4.2 z7 h7)) y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    have e7 : EB k z7.2 := (show EBK k (NonDet.when (cd = true ∧ x5.tcbSchedContext = none) (do
        let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
        schedContextDonate (Z := Unit) (the threadSc) dest)) by eb_auto) z4.2 e4 z7 h7
    have c7 : z7.2.curThread = C := (show IK (CTh C) (NonDet.when (cd = true ∧ x5.tcbSchedContext = none) (do
        let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
        schedContextDonate (Z := Unit) (the threadSc) dest)) from
      ik_when _ (ik_bind (by repeat' (first | ik_step0 | ik_unfold)) fun _ => ct_schedContextDonate _ _ _)) z4.2 n4.2 z7 h7
    exact hw z7.2 e7 c7 y hy

/-- **`send_ipc`** keeps `EB k`: the sender has `NPQ` (it may block or get
a reply / Inactive state), and when `k` the current thread is in no queue
of the endpoint (so the woken receiver is not current). -/
theorem eb_sendIpc_p {k : Bool} (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hT : NPQ thread σ)
    (hd : k = true → ∀ x, σ.kheap epptr = some (.endpoint x) → σ.curThread ∉ x.epQueue) :
    IKp (EB k) σ (sendIpc (Z := Unit) block call badge cg cgr cd thread epptr) := by
  unfold sendIpc
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, ez⟩ := SInvI.mem_getSimpleKo hz
  obtain ⟨ep, z2⟩ := z
  simp only at hk ez; subst z2
  revert hy
  refine (show IKp (EB k) σ _ from ?_) hσ y
  cases ep with
  | idleEP =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · exact eb_sendIpcBlocked_p _ _ _ _ _ _ σ hT
  | sendEP q =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · exact eb_sendIpcBlocked_p _ _ _ _ _ _ σ hT
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact ikp_of_ik ik_fail σ
    | cons dest q =>
      have hne : k = true → dest ≠ σ.curThread := fun hk' e =>
        hd hk' _ hk (by rw [← e]; exact List.mem_cons_self ..)
      cases block
      all_goals
        intro h0 y hy
        obtain ⟨⟨z1a, z1⟩, h1, hy⟩ := hy
        have e1 : EB k z1 := (show EBK k (tcbEpDequeue (Z := Unit) dest epptr) by eb_auto) σ h0 _ h1
        have n1 : NC thread σ.curThread z1 := nc_tcbEpDequeue _ _ _ _ σ ⟨hT, rfl⟩ _ h1
        obtain ⟨z2, h2, hy⟩ := hy
        obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet h2
        dsimp only at hy
        revert hy
        cases x.tcbState with
        | blockedOnReceive _ r _ =>
          intro hy
          dsimp only at hy
          obtain ⟨z3, h3, hy⟩ := hy
          rw [Set.mem_singleton_iff.1 h3] at hy
          exact eb_sendArm call badge cg cgr cd thread epptr dest r σ.curThread z1 n1 hne e1 y hy
        | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)

end

end Fl4Proofs.P3.SInvQ
