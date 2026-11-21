/-
P3 (DESIGN.md §9), invariant line G1 (rd8m, KENTRY-PLAN rd8j handoff 1,
rd14a FINDING): **`handle_recv` keeps `Rdy` without `Simple`** (spec side only,
outside the JAtZ cone).

rd8e's `RcvS` contains `Simple`, FALSE at reachable first-phase outcomes of
ReplyRecv / NBSendRecv / NBSendWait (rd14a). Its two uses are (a) rd's
`rd_maybeReturnSc_p` (needs only `NSw thread`) and (b) the donation of the
sender's SC in receive_ipc's sender arm (needs: the sender is not the switch
target; the sender is BlockedOnSend and ctq's `RA` makes the switch target
runnable, `np_of_nr`). So:

* `RcvN s t` = `RcvS` with `Simple` replaced by `NSw t ∧ SA` (ctq's scheduler
  slices, carried by its `sa_*` leaves).
* `rd_recvSenderN` (SA / ScInv carried over the transfer and the unblock
  check; `NSwT sender` by `nswT_of`), `rd_recvTailN`, `rd_recvRestN`,
  `rcvN_cancelIpc`, `rcvN_when`, **`rd_receiveIpcN`**;
  `rd_receiveSignalBlockedN`, **`rd_receiveSignalN`** (`NSw thread` only).
* `RHN C := RcvN C ∧ RBk true ∧ ct = C` (no `RdyT C`, no `Simple`),
  **`rd_handleRecvN`** (lookup fault: rd8m-B's `rd_hfN` with `NSwT ct` from
  `NSw ct ∧ ScInv`), **`rhn_of`** (`RHN ct` from `Rdy`, `ScInv`, ct a TCB not
  BlkR, `RT ct` and ctq's `EB true`: rd14a's `RcvR'` facts).
-/
import Fl4Proofs.P3.SpecInvRd8mB
open Classical

namespace Fl4Proofs.P3.SInvR.B8m

noncomputable section

set_option maxHeartbeats 1000000

open Fl4Spec in
/-- rd8e's `RcvS` with `Simple` replaced by `NSw thread ∧ SA`. -/
def RcvN (s : State Unit) (thread : Fl4Spec.ObjRef) : Prop :=
  Rdy s ∧ SInvQ.T1 s ∧ SInvB.ScInv s ∧ (SInvQ.P12.NSw thread s ∧ SInvQ.SA s) ∧
    (∀ d p, thread ∉ s.readyQueues d p) ∧ thread ∉ s.releaseQueue ∧
    (∃ x, s.kheap thread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧ B8d.RT s thread

theorem nsw_svs {s s' : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (h : SInvQ.P12.NSw t s) (hS : SVK.SVS s s') :
    SInvQ.P12.NSw t s' := by
  intro e
  rcases hS.2.2 with e' | e' <;> rw [e'] at e
  · exact h e
  · cases e

theorem nsw_tcbNtfnAppend (t u n : Fl4Spec.ObjRef) :
    SInv.IK (SInvQ.P12.NSw t) (Fl4Spec.tcbNtfnAppend (Z := Unit) u n) := by
  unfold Fl4Spec.tcbNtfnAppend; p12_nsw_auto

section E
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e

theorem rd_recvSenderN (sender thread epptr e : ObjRef) (reply : Option ObjRef) (data : SenderPayload)
    (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : SInvQ.SA s) (hI : SInvB.ScInv s)
    {x : Tcb} (hx : s.kheap sender = some (.tcb x)) (hxs : x.tcbState = .blockedOnSend e data)
    (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) sender (some epptr) data.senderBadge data.senderCanGrant thread
      let scPtr ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scPtr
      let fault ← threadGet (Z := Unit) Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush (Z := Unit) sender thread (the reply) donate
        else setThreadState (Z := Unit) sender .inactive
      else do
        setThreadState (Z := Unit) sender .running
        possibleSwitchTo (Z := Unit) sender) s).1) : Rdy y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer sender (some epptr) _ _ thread s hs z3 h3
  have q3 : SInvQ.T1 z3.2 := SInvQ.q1_doIpcTransfer sender (some epptr) _ _ thread s h1 z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' sender (some epptr) _ _ thread s z3 h3
  have sa3 : SInvQ.SA z3.2 := SInvQ.sa_doIpcTransfer _ _ _ _ _ s hA z3 h3
  have i3 : SInvB.ScInv z3.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_doIpcTransfer _ _ _ _ _) s hI z3 h3
  have t3 : TV (TVv s) z3.2 := tv_doIpcTransfer sender (some epptr) _ _ thread s rfl z3 h3
  -- the sender is still a TCB BlockedOnSend after the transfer
  have hx3 : ∃ x3, z3.2.kheap sender = some (.tcb x3) ∧ x3.tcbState = .blockedOnSend e data := by
    have ev := congrFun t3 sender
    unfold TVv at ev
    rw [hx] at ev
    cases hk : z3.2.kheap sender with
    | none => rw [hk] at ev; simp [B8c.tcbV] at ev
    | some o =>
      rw [hk] at ev
      cases o with
      | tcb x3 =>
        simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
        exact ⟨x3, rfl, ev.1.trans hxs⟩
      | _ => simp [B8c.tcbV] at ev
  obtain ⟨x3, hx3, hxs3⟩ := hx3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain ⟨x4, -, rfl⟩ := SInvQ.q1_mem_threadGet h4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨e5, -, -⟩ := rd_ifCond x4.tcbSchedContext (some false) (some true) z3.2 e3 h5
  have f5 := sf_ifCond x4.tcbSchedContext (some false) (some true) z3.2 h5
  have q5 : SInvQ.T1 z5.2 := SInvQ.q1_ifCondRefillUnblockCheck _ _ _ z3.2 q3 z5 h5
  have sa5 : SInvQ.SA z5.2 := SInvQ.sa_ifCondRefillUnblockCheck _ _ _ z3.2 sa3 z5 h5
  have i5 : SInvB.ScInv z5.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_ifCondRefillUnblockCheck _ _ _) z3.2 i3 z5 h5
  have hF5 := i5.fwd
  have hx5 := f5.2.2 sender x3 hx3
  -- the sender is BlockedOnSend, the switch target runnable (ctq's RA): not the holder's switch
  have hA5 : NSwT sender z5.2 := nswT_of i5 (SInvQ.np_of_nr sa5 (fun ⟨x', hx', hr⟩ => by
    rw [hx5] at hx'; cases hx'; rw [hxs3] at hr; simp [runnable] at hr)).1
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
  rw [hx5] at hx6
  cases hx6
  dsimp only at hy
  -- the sender is BlkR at z5 unless it holds a timeout fault
  have hRT : (∀ b, x3.tcbFault ≠ some (.timeout b)) → RT z5.2 sender := fun hnt x' c hx' hc => by
    rw [hx5] at hx'; cases hx'
    exact e5.2.2.1 sender x3 c hx5 (Or.inr (Or.inl ⟨e, data, hxs3, hnt⟩)) hc
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      refine (rd_replyPush_dN sender thread _ _ z5.2 e5 q5 hA5 hF5 (fun hd => hRT fun b hb => ?_) hy).1
      have hd' := of_decide_eq_true hd
      apply hd'.2
      rw [hb]; rfl
    · exact rd_setThreadState sender .inactive trivial z5.2 e5 y hy
  · rename_i hn
    have hf : x3.tcbFault = none := by
      by_contra hc; exact hn (Or.inr hc)
    obtain ⟨z7, h7, hy⟩ := hy
    have e7 : Rdy z7.2 := rd_setThreadState sender .running trivial z5.2 e5 z7 h7
    have v7 : SVK.SVS z5.2 z7.2 := SVK.sv_setThreadState' sender .running z5.2 z7 h7
    have hT7 := rT_svs (hRT fun b hb => by rw [hf] at hb; cases hb) v7
    exact rd_possibleSwitchTo_q sender z7.2 hT7 e7 y hy


theorem rd_recvTailN (thread epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef)
    (ntfn : Notification) (ep : Endpoint) (s : State Unit) (hS : RcvN s thread) {y : Unit × State Unit}
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
  obtain ⟨hR, h1, hI, ⟨hA, hSA⟩, hq, hrq, ⟨x, hx, hnb⟩, hT⟩ := hS
  split_ifs at hy with hc
  · exact rd_completeSignal _ thread s hR hx (hnb _) hT hy
  · obtain ⟨z4, h4, hy⟩ := hy
    have F4 : Rdy z4.2 ∧ SInvQ.T1 z4.2 ∧ SInvB.ScInv z4.2 ∧ (SInvQ.P12.NSw thread z4.2 ∧ SInvQ.SA z4.2) ∧ RT z4.2 thread := by
      unfold NonDet.when at h4
      split at h4
      · exact ⟨rd_maybeReturnSc_p _ thread s hq hA hrq hR z4 h4,
          SInvQ.q1_maybeReturnSc _ _ s h1 z4 h4, SInvB.sik_maybeReturnSc _ _ s hI z4 h4,
          ⟨B8e.nsw_maybeReturnSc thread _ _ s hA z4 h4, SInvQ.sa_maybeReturnSc _ _ s hSA z4 h4⟩, rt_maybeReturnSc _ thread s hT h4⟩
      · obtain rfl := Set.mem_singleton_iff.1 h4
        exact ⟨hR, h1, hI, ⟨hA, hSA⟩, hT⟩
    obtain ⟨e4, q4, i4, ⟨a4, sa4⟩, t4⟩ := F4
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
      have sa7 : SInvQ.SA z7.2 := SInvQ.sa_tcbEpDequeue _ epptr z4.2 sa4 z7 h7
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
      exact rd_recvSenderN _ thread epptr e reply _ z7.2 e7 q7 sa7 i7 hx8 hst y hy
    all_goals (dsimp only at hy; exact rd_receiveIpcBlocked isBlocking thread epptr reply z4.2 t4 e4 y hy)


/-- **`receive_ipc` from the endpoint read on.** -/
theorem rd_recvRestN (thread epptr : ObjRef) (isBlocking : Bool) (reply : Option ObjRef) (s : State Unit)
    (hS : RcvN s thread) {y : Unit × State Unit}
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
    exact rd_recvTailN thread epptr isBlocking reply none _ ep s hS hy
  | some p =>
    obtain ⟨⟨ntfn, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    exact rd_recvTailN thread epptr isBlocking reply (some p) ntfn ep s hS hy

/-- The receiver's facts across `cancel_ipc` of another thread (`CtQ` from ctq's `RB`). -/
theorem rcvN_cancelIpc (u thread : ObjRef) (s : State Unit) (hS : RcvN s thread) (hRB : SInvQ.RBk true s)
    (hct : s.curThread = thread) (hut : u ≠ thread) {y : Unit × State Unit}
    (hy : y ∈ (cancelIpc (Z := Unit) u s).1) : RcvN y.2 thread := by
  obtain ⟨hR, h1, hI, ⟨hA, hSA⟩, -, hrq, ⟨x, hx, hnb⟩, hT⟩ := hS
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
    ⟨SInvQ.P12.nsw_cancelIpc thread u s hA y hy, SInvQ.sa_cancelIpc u s hSA y hy⟩, fun d p => ?_,
    fun h => hrq (rq_cancelIpc' u s y hy thread h), ⟨x', hx', fun f => by rw [es]; exact hnb f⟩, rT_svs hT hV⟩
  have hq := ((hB.1.2.1 rfl).1 d p)
  rw [hct'] at hq
  exact hq

/-- The reply-cap prefix of `receive_ipc` (the reply's old TCB cancelled). -/

theorem rcvN_when (tptr : Option ObjRef) (thread : ObjRef) (σ : State Unit) (hS : RcvN σ thread)
    (hRB : SInvQ.RBk true σ) (hct : σ.curThread = thread) {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) (cancelIpc (Z := Unit) (the tptr)) σ).1) :
    RcvN z.2 thread := by
  unfold NonDet.when at hz
  split at hz
  · rename_i hc
    exact rcvN_cancelIpc _ thread σ hS hRB hct hc.2 hz
  · obtain rfl := Set.mem_singleton_iff.1 hz
    exact hS

/-- **`receive_ipc thread cap isBlocking replyCap`** keeps `Rdy` (at `handle_recv`:
thread = ct; `RcvN` from the carried facts, `RB` from ctq). -/
theorem rd_receiveIpcN (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (σ : State Unit)
    (hS : RcvN σ thread) (hRB : SInvQ.RBk true σ) (hct : σ.curThread = thread) {y : Unit × State Unit}
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
      have hS4 := rcvN_when tptr thread σ hS hRB hct h4
      try dsimp only at hy
      obtain ⟨⟨rp, s5⟩, h5, hy⟩ := hy
      obtain ⟨rfl, e5⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
      subst s5
      exact rd_recvRestN thread epptr isBlocking (some r) z4.2 hS4 hy
    case nullCap =>
      dsimp only at hy
      obtain ⟨⟨reply, s2⟩, h2, hy⟩ := hy
      obtain ⟨rfl, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
      subst s2
      exact rd_recvRestN thread epptr isBlocking none σ hS hy
    all_goals (dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)


end E

section H
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8h

theorem rd_receiveSignalBlockedN (thread n : ObjRef) (blk : Bool) (s : State Unit) (hR : Rdy s)
    (hT : B8d.RT s thread) (hq : QC thread s) (hA : SInvQ.P12.NSw thread s) :
    ∀ y ∈ (receiveSignalBlocked (Z := Unit) thread n blk s).1, Rdy y.2 := by
  intro y hy
  unfold receiveSignalBlocked at hy
  cases blk with
  | false => exact rd_doNbrecvFailedTransfer thread s hR y hy
  | true =>
    rw [if_pos (rfl : true = true)] at hy
    obtain ⟨z1, h1, hy⟩ := hy
    have e1 : Rdy z1.2 := B8e.rd_setThreadState_rt thread _ s hT hR z1 h1
    have q1 : QC thread z1.2 := qc_setThreadState thread thread _ s hq z1 h1
    have a1 : SInvQ.P12.NSw thread z1.2 := nsw_svs hA (SVK.sv_setThreadState' thread _ s z1 h1)
    obtain ⟨z2, h2, hy⟩ := hy
    have e2 : Rdy z2.2 := rd_tcbNtfnAppend thread n z1.2 e1 z2 h2
    have q2 : QC thread z2.2 := qc_tcbNtfnAppend thread thread n z1.2 q1 z2 h2
    have a2 : SInvQ.P12.NSw thread z2.2 := nsw_tcbNtfnAppend thread thread n z1.2 a1 z2 h2
    exact rd_maybeReturnSc_p n thread z2.2 q2.1 a2 q2.2 e2 y hy

/-- **`receive_signal`** of a non-`BlkR` thread, `RdyT` when bound, outside
the queues. -/

theorem rd_receiveSignalN (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (s : State Unit) (hR : Rdy s)
    {x : Tcb} (hx : s.kheap thread = some (.tcb x)) (hnb : ∀ f, ¬ BlkR x.tcbState f)
    (hT : B8d.RT s thread) (hq : QC thread s) (hA : SInvQ.P12.NSw thread s) {y : Unit × State Unit}
    (hy : y ∈ (receiveSignal (Z := Unit) thread cap isBlocking s).1) : Rdy y.2 := by
  unfold receiveSignal at hy
  cases cap
  case notificationCap p b r =>
    dsimp only at hy
    obtain ⟨w0, hw0, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hw0
    obtain ⟨⟨ntfn, s1⟩, hz1, hy⟩ := hy
    have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
    subst s1
    dsimp only at hy
    cases hn : ntfn.ntfnObj
    case activeNtfn badge =>
      rw [hn] at hy
      dsimp only at hy
      obtain ⟨z2, hz2, hy⟩ := hy
      have e2 : Rdy z2.2 := rd_asUser thread _ s hR z2 hz2
      have v2 : SVK.SVS s z2.2 := SVK.sv_asUser' thread _ s z2 hz2
      have t2 : B8d.TV (B8d.TVv s) z2.2 := B8d.tv_asUser thread _ s rfl z2 hz2
      obtain ⟨z3, hz3, hy⟩ := hy
      have e3 : Rdy z3.2 := rd_setSimpleKo _ _ _ z2.2 e2 z3 hz3
      have v3 : SVK.SVS z2.2 z3.2 :=
        SVK.sv_setSimpleKo' KernelObject.notification _ _ (SVK.so_ntfn _) z2.2 z3 hz3
      have t3 : B8d.TV (B8d.TVv s) z3.2 := B8e.tv_setNotification _ _ z2.2 t2 z3 hz3
      obtain ⟨x3, hx3, es, ef⟩ := tcb_tv hx t3
      have hT3 : B8d.RT z3.2 thread := B8d.rT_svs hT (v2.trans v3)
      obtain ⟨z4, hz4, hy⟩ := hy
      obtain ⟨e4, -⟩ := rd_maybeDonateSc_sr thread p z3.2 e3 hx3 (by rw [es]; exact hnb _)
        (fun c hc => hT3 x3 c hx3 hc) hz4
      obtain ⟨z5, hz5, hy⟩ := hy
      obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet hz5
      exact (rd_ifCond x5.tcbSchedContext (some false) (some false) z4.2 e4 hy).1
    all_goals (rw [hn] at hy; dsimp only at hy; exact rd_receiveSignalBlockedN thread p isBlocking s hR hT hq hA y hy)
  all_goals (dsimp only at hy; obtain ⟨w, hw, -⟩ := hy; exact hw.elim)


/-- The receiver's facts at a state of `handle_recv` without `RdyT C` and
without `Simple`. -/
def RHN (C : ObjRef) (s : State Unit) : Prop :=
  RcvN s C ∧ SInvQ.RBk true s ∧ s.curThread = C

theorem rhn_asUser (C t : ObjRef) (r : Register) : IK (RHN C) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  obtain ⟨⟨hR, h1, hI, ⟨hA, hSA⟩, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, hB, hc⟩ := hs
  have v := SVK.sv_asUser' t _ s z hz
  have qc : (QC C z.2 ∧ z.2.curThread = C) :=
    (show IK (fun s : State Unit => QC C s ∧ s.curThread = C) (asUser (Z := Unit) t (getRegister r)) by
      unfold asUser; repeat' (first | ik_step0 | ik_unfold)) s ⟨⟨hq, hrq⟩, hc⟩ z hz
  obtain ⟨x', hx', hs', -⟩ := tcb_tv hx (B8d.tv_asUser t _ s rfl z hz)
  exact ⟨⟨rd_asUser t _ s hR z hz, q1_asUser t _ s h1 z hz,
    SInvB.sik_of_sbk (fun _ => SInvB.sb_asUser _ _) s hI z hz, ⟨nsw_svs hA v, SInvQ.sa_asUser t _ s hSA z hz⟩, qc.1.1, qc.1.2,
    ⟨x', hx', by rw [hs']; exact hnb⟩, B8d.rT_svs hT v⟩, SInvQ.rb_asUser t _ s hB z hz, qc.2⟩

theorem rhn_lookupReply (C : ObjRef) : IKE (RHN C) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact rhn_asUser _ _ _) |
    (with_reducible exact SInvQ.pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv` keeps `Rdy`** from `RHN C` (ct possibly unbound). -/
theorem rd_handleRecvN (C : ObjRef) (blk canReply : Bool) :
    SInv.HK (RHN C) Rdy (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RHN C) m := fun h => SInvQ.ik_of_ro h
  have hRIP : ∀ cp rc, SInv.HK (RHN C) Rdy (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs y hy => rd_receiveIpcN C cp blk rc s hs.1 hs.2.1 hs.2.2 hy
  have hRS : ∀ cp, SInv.HK (RHN C) Rdy (receiveSignal (Z := Unit) C cp blk) := by
    intro cp s hs y hy
    obtain ⟨⟨hR, -, -, ⟨hA, -⟩, hq, hrq, ⟨x, hx, hnb⟩, hT⟩, -, -⟩ := hs
    exact rd_receiveSignalN C cp blk s hR hx hnb hT ⟨hq, hrq⟩ hA hy
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.2.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : RHN C y2.2 := (?_ : IK (RHN C) _) σ hσ y2 h2
  · refine hk_catch (I := RHN C) (Q0 := Rdy) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (rhn_lookupReply C) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (ike_returnOk _) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (hro fun _ => by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · intro s hs z hz
      obtain ⟨⟨hR, h1, hI, ⟨hA, -⟩, -, -, -, hT⟩, -, -⟩ := hs
      exact rd_hfN C e s ⟨hR, hT, h1, nswT_of hI hA, hI⟩ z hz
  · repeat' (first | exact rhn_asUser C _ _ | ik_step0)


/-- **`RHN ct`** from rd14a's `RcvR'` facts and ctq's `EB true`. -/
theorem rhn_of {s : State Unit} (hR : Rdy s) (hI : SInvB.ScInv s)
    (hb : ∃ x, s.kheap s.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) (hT : B8d.RT s s.curThread)
    (hE : SInvQ.EB true s) : RHN s.curThread s :=
  ⟨⟨hR, SInvQ.tq_t1 hE.1.1.1.1, hI, ⟨(hE.2.1.2.1 rfl).2.1, hE.1.1.2⟩, (hE.2.1.2.1 rfl).1,
    (hE.2.1.2.1 rfl).2.2, hb, hT⟩, hE.2, rfl⟩

end H

end

end Fl4Proofs.P3.SInvR.B8m
