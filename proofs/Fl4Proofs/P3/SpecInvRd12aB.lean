/-
P3 (DESIGN.md §9), invariant line G1 (rd12a, KENTRY-PLAN rd11a handoff 2):
**`receive_ipc` of the current thread** for `OsBody` (spec side only).

* `KR σ0 s := KP σ0 s ∧ (CB0 s ∨ NRun ct s ∨ RT s ct)` (the end of a receive
  arm; CtR by A1's `ctR_kp` / `ctR_nrun` or **`ctR_rt`**), **`ss4_of_kr`**.
* `cx_maybeReturnSc` (it can only unbind its thread), `kp_tcbEpAppend`,
  **`kr_rcvBlocked`** (blocking: ct not runnable, rd9's `no_sts` + the `fg_*`
  family; non-blocking: SVS).
* **`kr_recvTail`**: complete_signal (A's `ke_completeSignal`), or
  maybe_return_sc (A1's `kp_maybeReturnSc`, `CX` kept) then the sender arm at
  the dequeue state (A's `kp_recvSender` / `ce_recvSender`, with rd8e's
  `Rdy` / T1 / ScInv / Simple carry to the dequeue state) or the blocked arm.
* **`kr_receiveIpc σ0 h0 cap blk rc s (KP σ0 s) (ct bound to cur_sc) (RcvS s ct)
  (RBk true s)`**: the reply-cap prefix (`kp_cancelIpc`, rd8e's `rcv_when`).
-/
import Fl4Proofs.P3.SpecInvRd12aA
open Classical

namespace Fl4Proofs.P3.SInvR.A12a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.A11

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The end of a receive arm -/

/-- The end of a receive arm: `KP`, and ct unbound / bound to cur_sc, not
runnable, or `RT` (it got a released sender's SC). -/
abbrev KR (σ0 s : State Unit) : Prop :=
  KP σ0 s ∧ (CB0 s ∨ A8.NRun s.curThread s ∨ B8d.RT s s.curThread)

/-- CtR when ct is `RT`. -/
theorem ctR_rt {s : State Unit} (h : B8d.RT s s.curThread) : CtR s := by
  intro x hx _ hA _
  obtain ⟨x', c, -, -, hx', hc, -⟩ := hA
  exact h x' c hx' hc

theorem ss4_of_kr {σ0 s : State Unit} (h : A10.BS σ0) (hs : Suff σ0) (hK : KR σ0 s) : A10.SS4 s :=
  ss4_of_kp h hs hK.1 (hK.2.elim (ctR_kp h hK.1) fun h' => h'.elim ctR_nrun ctR_rt)

theorem kr_of_ke {σ0 s : State Unit} (h : KE σ0 s) : KR σ0 s :=
  ⟨h.1, h.2.elim Or.inl fun h' => Or.inr (Or.inl h')⟩

theorem cb0_of_cx {σ0 s : State Unit} (hK : KP σ0 s) (h : CX σ0.curThread s) : CB0 s := by
  intro x hx
  rw [kp_curThread hK] at hx
  obtain ⟨x', hx', hb⟩ := h
  rw [hx] at hx'; cases hx'; exact hb

/-! ## Callees -/

/-- **`maybe_return_sc n t`** keeps `CX t` (it can only unbind `t`). -/
theorem cx_maybeReturnSc (n t : ObjRef) (s : State Unit) (hC : CX t s) {y : Unit × State Unit}
    (hy : y ∈ (maybeReturnSc (Z := Unit) n t s).1) : CX t y.2 := by
  unfold maybeReturnSc at hy
  obtain ⟨⟨a1, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨⟨a2, s2⟩, h2, hy⟩ := hy
  have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
  subst s2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨⟨scp, s3⟩, h3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
    subst s3
    obtain ⟨z4, h4, hy⟩ := hy
    obtain ⟨x4, -, e4⟩ := SInv.mem_threadSet h4
    obtain ⟨z5, h5, hy⟩ := hy
    obtain ⟨y5, n5, hk5, e5⟩ := SInvB.mem_updateSchedContext h5
    have hpt : scp ≠ t := fun h => by rw [h, e4] at hk5; simp at hk5
    have ht5 : z5.2.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x4)) := by
      rw [e5, e4]; simp [Function.update_of_ne (Ne.symm hpt)]
    have hk : y.2.kheap = z5.2.kheap :=
      B8e.kt_of (fun K T => by
        repeat' (first | (with_reducible exact kt_rescheduleRequired _ _) | ik_step0 | ik_unfold)) hy
    exact ⟨_, by rw [hk, ht5], Or.inl rfl⟩
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hC

theorem kp_tcbEpAppend (t e : ObjRef) (b : Bool) (σ0 : State Unit) :
    IK (KP σ0) (tcbEpAppend (Z := Unit) t e b) :=
  ik_kp (A11b.sv_tcbEpAppend t e b) (cfk_tcbEpAppend' t e b) σ0

/-- **`receive_ipc_blocked` of the current thread** from `KP` and `CX ct`. -/
theorem kr_rcvBlocked (σ0 : State Unit) (blk : Bool) (epptr : ObjRef) (reply : Option ObjRef) (s : State Unit)
    (hK : KP σ0 s) (hC : CX σ0.curThread s) {y : Unit × State Unit}
    (hy : y ∈ (receiveIpcBlocked (Z := Unit) blk σ0.curThread epptr reply s).1) : KR σ0 y.2 := by
  unfold receiveIpcBlocked at hy
  split at hy
  · have hy0 := hy
    obtain ⟨z1, h1, hy'⟩ := hy0
    obtain ⟨z2, h2, hy'⟩ := hy'
    have k1 : KP σ0 z1.2 := ik_kp (SVK.sv_setThreadState' _ _) (cfk_setThreadState' _ _) σ0 s hK z1 h1
    have k2 : KP σ0 z2.2 := by
      cases reply with
      | none =>
        obtain rfl := Set.mem_singleton_iff.1 h2
        exact k1
      | some r =>
        exact ik_kp (B8d.sv_setReplyObjRef' _ _ _) (by cfk_auto) σ0 z1.2 k1 z2 h2
    have ky : KP σ0 y.2 := kp_tcbEpAppend _ _ _ σ0 z2.2 k2 y hy'
    have hn := A9.no_bind (fun z hz => A9.no_sts σ0.curThread _ rfl hz)
      (fun _ => by fg_auto) y hy
    refine ⟨ky, Or.inr (Or.inl ?_)⟩
    rw [kp_curThread ky]; exact A9.nrun_of_no hn
  · unfold doNbrecvFailedTransfer at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    have v3 := SVK.sv_asUser' _ _ s z3 h3
    have c3 : cfS z3.2 = cfS s := cfk_asUser' _ _ s z3 h3
    have k3 : KP σ0 z3.2 := ik_kp (SVK.sv_asUser' _ _) (cfk_asUser' _ _) σ0 s hK z3 h3
    exact ⟨k3, Or.inl (cb0_of_cx k3 (cx_svcf hC v3 c3))⟩

/-! ## `receive_ipc` -/

/-- **`receive_ipc` of ct after the endpoint and notification reads.** -/
theorem kr_recvTail (σ0 : State Unit) (h0 : B0 σ0) (epptr : ObjRef) (isBlocking : Bool)
    (reply ntfnptr : Option ObjRef) (ntfn : Notification) (ep : Endpoint) (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hS : B8e.RcvS s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ ((if ntfnptr ≠ none ∧ isActive ntfn
    then
      completeSignal (the ntfnptr) σ0.curThread
    else do
      NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) σ0.curThread
      match ep with
      | .sendEP q => do
        NonDet.assert (q ≠ [])
        let sender ← pure (the q.head?)
        tcbEpDequeue sender epptr
        let senderState ← getThreadState sender
        let data ← match senderState with
          | .blockedOnSend _ref data => pure data
          | _ => NonDet.fail
        doIpcTransfer sender (some epptr)
          data.senderBadge data.senderCanGrant
          σ0.curThread
        let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
        ifSporadicCurScAssertRefillUnblockCheck scPtr
        let fault ← threadGet Tcb.tcbFault sender
        if data.senderIsCall ∨ fault ≠ none
        then
          if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
          then do
            let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
            let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
            replyPush sender σ0.curThread (the reply) donate
          else setThreadState sender .inactive
        else do
          setThreadState sender .running
          possibleSwitchTo sender
      | _ => receiveIpcBlocked isBlocking σ0.curThread epptr reply) s).1) : KR σ0 y.2 := by
  have hC : CX σ0.curThread s := by
    obtain ⟨-, -, -, -, -, -, ⟨x, hx, -⟩, -⟩ := hS
    exact ⟨x, hx, Or.inr (hb x (by rw [kp_curThread hK]; exact hx))⟩
  obtain ⟨hR, h1, hI, hA, hq, hrq, -, -⟩ := hS
  split_ifs at hy with hc
  · exact kr_of_ke (ke_completeSignal σ0 _ s hK hb hy)
  · obtain ⟨z4, h4, hy⟩ := hy
    have F4 : KP σ0 z4.2 ∧ CX σ0.curThread z4.2 ∧ Rdy z4.2 ∧ SInvQ.T1 z4.2 ∧ SInvB.ScInv z4.2 ∧
        SInvQ.Simple z4.2 := by
      unfold NonDet.when at h4
      split at h4
      · exact ⟨kp_maybeReturnSc _ σ0 s hK z4 h4, cx_maybeReturnSc _ _ s hC h4,
          rd_maybeReturnSc_p _ _ s hq (hA _) hrq hR z4 h4,
          SInvQ.q1_maybeReturnSc _ _ s h1 z4 h4, SInvB.sik_maybeReturnSc _ _ s hI z4 h4,
          B8e.simple_of_nsw (fun t => B8e.nsw_maybeReturnSc t _ _) s hA z4 h4⟩
      · obtain rfl := Set.mem_singleton_iff.1 h4
        exact ⟨hK, hC, hR, h1, hI, hA⟩
    obtain ⟨k4, c4, e4, q4, i4, a4⟩ := F4
    cases ep
    case sendEP q =>
      dsimp only at hy
      obtain ⟨⟨u5, s5⟩, h5, hy⟩ := hy
      have e5 : s5 = z4.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h5
      subst s5
      obtain ⟨⟨sender, s6⟩, h6, hy⟩ := hy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h6)
      obtain ⟨z7, h7, hy⟩ := hy
      have e7 : Rdy z7.2 := rd_tcbEpDequeue _ epptr z4.2 e4 z7 h7
      have q7 : SInvQ.T1 z7.2 := SInvQ.q1_tcbEpDequeue _ epptr z4.2 q4 z7 h7
      have i7 : SInvB.ScInv z7.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_tcbEpDequeue _ epptr) z4.2 i4 z7 h7
      have a7 : SInvQ.Simple z7.2 := B8e.simple_of_nsw (fun t => B8e.nsw_tcbEpDequeue t _ epptr) z4.2 a4 z7 h7
      have v7 := sv_tcbEpDequeue _ epptr z4.2 z7 h7
      have f7 := cfk_tcbEpDequeue' _ epptr z4.2 z7 h7
      have k7 : KP σ0 z7.2 := ik_kp (sv_tcbEpDequeue _ epptr) (cfk_tcbEpDequeue' _ epptr) σ0 z4.2 k4 z7 h7
      have c7 : CX σ0.curThread z7.2 := cx_svcf c4 v7 f7
      obtain ⟨⟨st, s8⟩, h8, hy⟩ := hy
      unfold getThreadState at h8
      obtain ⟨x8, hx8, e8⟩ := SInvQ.q1_mem_threadGet h8
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e8
      cases hst : x8.tcbState
      all_goals first
        | (rw [hst] at hy; dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)
        | skip
      rename_i e d
      rw [hst] at hy
      dsimp only at hy
      obtain ⟨⟨d', s9⟩, h9, hy⟩ := hy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h9)
      have hKy := kp_recvSender h0 _ epptr reply _ z7.2 k7 y hy
      rcases ce_recvSender _ σ0.curThread epptr e reply _ z7.2 e7 q7 a7 i7.fwd hx8 hst c7 y hy with hc' | hr
      · exact ⟨hKy, Or.inl (cb0_of_cx hKy hc')⟩
      · exact ⟨hKy, Or.inr (Or.inr (by rw [kp_curThread hKy]; exact hr))⟩
    all_goals (dsimp only at hy; exact kr_rcvBlocked σ0 isBlocking epptr reply z4.2 k4 c4 hy)

/-- **`receive_ipc` of ct from the endpoint read on.** -/
theorem kr_recvRest (σ0 : State Unit) (h0 : B0 σ0) (epptr : ObjRef) (isBlocking : Bool) (reply : Option ObjRef)
    (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hS : B8e.RcvS s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ ((do
      let ep ← getEndpoint (Z := Unit) epptr
      let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification σ0.curThread
      let ntfn ← match ntfnptr with
        | none => pure defaultNotification
        | some p => getNotification p
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (the ntfnptr) σ0.curThread
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) σ0.curThread
        match ep with
        | .sendEP q => do
          NonDet.assert (q ≠ [])
          let sender ← pure (the q.head?)
          tcbEpDequeue sender epptr
          let senderState ← getThreadState sender
          let data ← match senderState with
            | .blockedOnSend _ref data => pure data
            | _ => NonDet.fail
          doIpcTransfer sender (some epptr)
            data.senderBadge data.senderCanGrant
            σ0.curThread
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender σ0.curThread (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking σ0.curThread epptr reply) s).1) : KR σ0 y.2 := by
  obtain ⟨⟨ep, s1⟩, hz1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  obtain ⟨⟨ntfnptr, s2⟩, hz2, hy⟩ := hy
  have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz2
  subst s2
  dsimp only at hy
  cases ntfnptr with
  | none =>
    obtain ⟨⟨ntfn, s3⟩, hz3, hy⟩ := hy
    obtain ⟨rfl, e3⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hz3)
    subst s3
    exact kr_recvTail σ0 h0 epptr isBlocking reply none _ ep s hK hb hS hy
  | some p =>
    obtain ⟨⟨ntfn, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    exact kr_recvTail σ0 h0 epptr isBlocking reply (some p) ntfn ep s hK hb hS hy

/-- The reply-cap prefix: `KP`, ct's binding and `RcvS` kept. -/
theorem kr_when (tptr : Option ObjRef) (σ0 s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hS : B8e.RcvS s σ0.curThread) (hRB : SInvQ.RBk true s) {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (tptr ≠ none ∧ the tptr ≠ σ0.curThread) (cancelIpc (Z := Unit) (the tptr)) s).1) :
    KP σ0 z.2 ∧ (∀ x, z.2.kheap z.2.curThread = some (.tcb x) → x.tcbSchedContext = some z.2.curSc) ∧
      B8e.RcvS z.2 σ0.curThread := by
  have hS' := B8e.rcv_when tptr σ0.curThread s hS hRB (kp_curThread hK) hz
  unfold NonDet.when at hz
  split at hz
  · exact ⟨kp_cancelIpc _ σ0 s hK z hz,
      (A8.keep_svcf (B8e.sv_cancelIpc' _ s z hz) (cfk_cancelIpc' _ s z hz)).2.2 hb, hS'⟩
  · obtain rfl := Set.mem_singleton_iff.1 hz
    exact ⟨hK, hb, hS⟩

/-- **`receive_ipc ct cap blk replyCap`** from `KP σ0 s` with ct bound to
cur_sc, rd8e's `RcvS` and ctq's `RBk true` at `s`: every outcome is `KR σ0`. -/
theorem kr_receiveIpc (σ0 : State Unit) (h0 : B0 σ0) (cap : Cap) (isBlocking : Bool) (replyCap : Cap)
    (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    (hS : B8e.RcvS s σ0.curThread) (hRB : SInvQ.RBk true s) {y : Unit × State Unit}
    (hy : y ∈ (receiveIpc (Z := Unit) σ0.curThread cap isBlocking replyCap s).1) : KR σ0 y.2 := by
  unfold receiveIpc at hy
  cases cap
  case endpointCap epptr bd rights =>
    obtain ⟨⟨pr, s1⟩, h1, hy⟩ := hy
    obtain ⟨rfl, e1⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
    subst s1
    dsimp only at hy
    cases replyCap
    case replyCap r b =>
      dsimp only at hy
      obtain ⟨⟨tptr, s2⟩, h2, hy⟩ := hy
      have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
      subst s2
      try dsimp only at hy
      obtain ⟨z4, h4, hy⟩ := hy
      obtain ⟨k4, b4, S4⟩ := kr_when tptr σ0 s hK hb hS hRB h4
      try dsimp only at hy
      obtain ⟨⟨rp, s5⟩, h5, hy⟩ := hy
      obtain ⟨rfl, e5⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
      subst s5
      exact kr_recvRest σ0 h0 epptr isBlocking (some r) z4.2 k4 b4 S4 hy
    case nullCap =>
      dsimp only at hy
      obtain ⟨⟨reply, s2⟩, h2, hy⟩ := hy
      obtain ⟨rfl, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
      subst s2
      exact kr_recvRest σ0 h0 epptr isBlocking none s hK hb hS hy
    all_goals (dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)

end

end Fl4Proofs.P3.SInvR.A12a
