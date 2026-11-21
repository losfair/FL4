/-
P3 (DESIGN.md §9), invariant line G1 (rd8e): **`receive_ipc` keeps `Rdy`**
(spec side only, outside the JAtZ cone; KENTRY-PLAN rd8d handoff 1).

The receiver (at `handle_recv`: the current thread) is a TCB in no ready
queue (ctq's `CtQ` inside `RB`), not released, in a state no fault makes
`BlkR` (it is running), and `RdyT` when bound (rd8c's `CtRdy`). The prefix:
the reply's old TCB is cancelled (rd8eA's general `rd_cancelIpc`; `CtQ` by
ctq's `rb_cancelIpc`, the release queue by `rq_cancelIpc'`, the receiver's
state by `StK.st_cancelIpc`, its binding by `sv_cancelIpc'`, `T1` / `Simple`
/ `ScInv` by ctq's / sb2's families). Then either `complete_signal`
(`rd_completeSignal`), or `maybe_return_sc` (RdU's `rd_maybeReturnSc_p`, the
receiver `RT` afterwards: `rt_maybeReturnSc`) followed by the sender arm
(rd8d's `rd_recvSender` at the dequeue state) or `receive_ipc_blocked`
(`rd_receiveIpcBlocked`).

* `nsw_maybeReturnSc`, `nsw_tcbEpDequeue`, `kt_of`, `rt_maybeReturnSc`.
* `RcvS s thread` (the receiver's facts at a state), `rcvS_cancelIpc`.
* **`rd_recvRest`** (from the endpoint read on), **`rd_receiveIpc`**.
-/
import Fl4Proofs.P3.SpecInvRd8eA
open Classical

namespace Fl4Proofs.P3.SInvR.B8e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d

noncomputable section

set_option maxHeartbeats 1000000

theorem nsw_maybeReturnSc (t n u : ObjRef) : IK (SInvQ.P12.NSw t) (maybeReturnSc (Z := Unit) n u) := by
  unfold maybeReturnSc; p12_nsw_auto

theorem nsw_tcbEpDequeue (t u e : ObjRef) : IK (SInvQ.P12.NSw t) (tcbEpDequeue (Z := Unit) u e) := by
  unfold tcbEpDequeue; p12_nsw_auto

theorem simple_of_nsw {α : Type} {m : NonDet (State Unit) α} (h : ∀ t, IK (SInvQ.P12.NSw t) m) :
    IK SInvQ.Simple m := fun σ hσ y hy t => h t σ (hσ t) y hy

theorem kt_of {α : Type} {m : NonDet (State Unit) α} (h : ∀ K T, IK (KT K T) m) {σ : State Unit}
    {y : α × State Unit} (hy : y ∈ (m σ).1) : y.2.kheap = σ.kheap :=
  (h σ.kheap σ.curTime σ ⟨rfl, rfl⟩ y hy).1

/-- **`maybe_return_sc`** keeps `RT` of its thread (it can only unbind it). -/
theorem rt_maybeReturnSc (n t : ObjRef) (σ : State Unit) (hT : RT σ t) {y : Unit × State Unit}
    (hy : y ∈ (maybeReturnSc (Z := Unit) n t σ).1) : RT y.2 t := by
  unfold maybeReturnSc at hy
  obtain ⟨⟨a1, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨⟨a2, s2⟩, h2, hy⟩ := hy
  have e2 : s2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
  subst s2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨⟨scp, s3⟩, h3, hy⟩ := hy
    have e3 : s3 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
    subst s3
    obtain ⟨z4, h4, hy⟩ := hy
    obtain ⟨x4, -, e4⟩ := SInv.mem_threadSet h4
    obtain ⟨z5, h5, hy⟩ := hy
    obtain ⟨y5, n5, hk5, e5⟩ := SInvB.mem_updateSchedContext h5
    have hpt : scp ≠ t := fun h => by rw [h, e4] at hk5; simp at hk5
    have ht5 : z5.2.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => none) x4)) := by
      rw [e5, e4]; simp [Function.update_of_ne (Ne.symm hpt)]
    have hk : y.2.kheap = z5.2.kheap :=
      kt_of (fun K T => by repeat' (first | (with_reducible exact kt_rescheduleRequired _ _) | ik_step0 | ik_unfold)) hy
    intro x c hx hc
    rw [hk, ht5] at hx
    cases hx
    cases hc
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hT

/-- The receiver's facts at a state of `receive_ipc`. -/
def RcvS (s : State Unit) (thread : ObjRef) : Prop :=
  Rdy s ∧ SInvQ.T1 s ∧ SInvB.ScInv s ∧ SInvQ.Simple s ∧ (∀ d p, thread ∉ s.readyQueues d p) ∧
    thread ∉ s.releaseQueue ∧ (∃ x, s.kheap thread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧ RT s thread

/-- **`receive_ipc` after the endpoint and notification reads.** -/
theorem rd_recvTail (thread epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef)
    (ntfn : Notification) (ep : Endpoint) (s : State Unit) (hS : RcvS s thread) {y : Unit × State Unit}
    (hy : y ∈ ((if ntfnptr ≠ none ∧ isActive ntfn
    then
      completeSignal (the ntfnptr) thread
    else do
      NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) thread
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
          thread
        let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
        ifSporadicCurScAssertRefillUnblockCheck scPtr
        let fault ← threadGet Tcb.tcbFault sender
        if data.senderIsCall ∨ fault ≠ none
        then
          if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
          then do
            let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
            let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
            replyPush sender thread (the reply) donate
          else setThreadState sender .inactive
        else do
          setThreadState sender .running
          possibleSwitchTo sender
      | _ => receiveIpcBlocked isBlocking thread epptr reply) s).1) : Rdy y.2 := by
  obtain ⟨hR, h1, hI, hA, hq, hrq, ⟨x, hx, hnb⟩, hT⟩ := hS
  split_ifs at hy with hc
  · exact rd_completeSignal _ thread s hR hx (hnb _) hT hy
  · obtain ⟨z4, h4, hy⟩ := hy
    have F4 : Rdy z4.2 ∧ SInvQ.T1 z4.2 ∧ SInvB.ScInv z4.2 ∧ SInvQ.Simple z4.2 ∧ RT z4.2 thread := by
      unfold NonDet.when at h4
      split at h4
      · exact ⟨rd_maybeReturnSc_p _ thread s hq (hA thread) hrq hR z4 h4,
          SInvQ.q1_maybeReturnSc _ _ s h1 z4 h4, SInvB.sik_maybeReturnSc _ _ s hI z4 h4,
          simple_of_nsw (fun t => nsw_maybeReturnSc t _ _) s hA z4 h4, rt_maybeReturnSc _ thread s hT h4⟩
      · obtain rfl := Set.mem_singleton_iff.1 h4
        exact ⟨hR, h1, hI, hA, hT⟩
    obtain ⟨e4, q4, i4, a4, t4⟩ := F4
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
      have a7 : SInvQ.Simple z7.2 := simple_of_nsw (fun t => nsw_tcbEpDequeue t _ epptr) z4.2 a4 z7 h7
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
      exact rd_recvSender _ thread epptr e reply _ z7.2 e7 q7 a7 i7.fwd hx8 hst y hy
    all_goals (dsimp only at hy; exact rd_receiveIpcBlocked isBlocking thread epptr reply z4.2 t4 e4 y hy)


/-- **`receive_ipc` from the endpoint read on.** -/
theorem rd_recvRest (thread epptr : ObjRef) (isBlocking : Bool) (reply : Option ObjRef) (s : State Unit)
    (hS : RcvS s thread) {y : Unit × State Unit}
    (hy : y ∈ ((do
      let ep ← getEndpoint (Z := Unit) epptr
      let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification thread
      let ntfn ← match ntfnptr with
        | none => pure defaultNotification
        | some p => getNotification p
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (the ntfnptr) thread
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) thread
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
            thread
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender thread (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking thread epptr reply) s).1) : Rdy y.2 := by
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
    exact rd_recvTail thread epptr isBlocking reply none _ ep s hS hy
  | some p =>
    obtain ⟨⟨ntfn, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    exact rd_recvTail thread epptr isBlocking reply (some p) ntfn ep s hS hy

/-- The receiver's facts across `cancel_ipc` of another thread (`CtQ` from ctq's `RB`). -/
theorem rcvS_cancelIpc (u thread : ObjRef) (s : State Unit) (hS : RcvS s thread) (hRB : SInvQ.RBk true s)
    (hct : s.curThread = thread) (hut : u ≠ thread) {y : Unit × State Unit}
    (hy : y ∈ (cancelIpc (Z := Unit) u s).1) : RcvS y.2 thread := by
  obtain ⟨hR, h1, hI, hA, -, hrq, ⟨x, hx, hnb⟩, hT⟩ := hS
  have hB := SInvQ.rb_cancelIpc u s hRB y hy
  have hO := StK.st_cancelIpc (t0 := u) s y hy
  have hV := sv_cancelIpc' u s y hy
  have hct' : y.2.curThread = thread := hO.2.trans hct
  have e := hV.1 thread
  rw [hx] at e
  obtain ⟨x', hx', -⟩ := SVK.sv_tcb (o := y.2.kheap thread) e
  obtain ⟨y0, hy0, es⟩ := hO.1 thread x' (Ne.symm hut) hx'
  rw [hx] at hy0; cases hy0
  refine ⟨rd_cancelIpc u s hR y hy, SInvQ.q1_cancelIpc u s h1 y hy,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_cancelIpc u) s hI y hy,
    simple_of_nsw (fun t => SInvQ.P12.nsw_cancelIpc t u) s hA y hy, fun d p => ?_,
    fun h => hrq (rq_cancelIpc' u s y hy thread h), ⟨x', hx', fun f => by rw [es]; exact hnb f⟩, rT_svs hT hV⟩
  have hq := ((hB.1.2.1 rfl).1 d p)
  rw [hct'] at hq
  exact hq

/-- The reply-cap prefix of `receive_ipc` (the reply's old TCB cancelled). -/
theorem rcv_when (tptr : Option ObjRef) (thread : ObjRef) (σ : State Unit) (hS : RcvS σ thread)
    (hRB : SInvQ.RBk true σ) (hct : σ.curThread = thread) {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) (cancelIpc (Z := Unit) (the tptr)) σ).1) :
    RcvS z.2 thread := by
  unfold NonDet.when at hz
  split at hz
  · rename_i hc
    exact rcvS_cancelIpc _ thread σ hS hRB hct hc.2 hz
  · obtain rfl := Set.mem_singleton_iff.1 hz
    exact hS

/-- **`receive_ipc thread cap isBlocking replyCap`** keeps `Rdy` (at `handle_recv`:
thread = ct; `RcvS` from the carried facts, `RB` from ctq). -/
theorem rd_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (σ : State Unit)
    (hS : RcvS σ thread) (hRB : SInvQ.RBk true σ) (hct : σ.curThread = thread) {y : Unit × State Unit}
    (hy : y ∈ (receiveIpc (Z := Unit) thread cap isBlocking replyCap σ).1) : Rdy y.2 := by
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
      have e2 : s2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
      subst s2
      try dsimp only at hy
      obtain ⟨z4, h4, hy⟩ := hy
      have hS4 := rcv_when tptr thread σ hS hRB hct h4
      try dsimp only at hy
      obtain ⟨⟨rp, s5⟩, h5, hy⟩ := hy
      obtain ⟨rfl, e5⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
      subst s5
      exact rd_recvRest thread epptr isBlocking (some r) z4.2 hS4 hy
    case nullCap =>
      dsimp only at hy
      obtain ⟨⟨reply, s2⟩, h2, hy⟩ := hy
      obtain ⟨rfl, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
      subst s2
      exact rd_recvRest thread epptr isBlocking none σ hS hy
    all_goals (dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)

end

end Fl4Proofs.P3.SInvR.B8e
