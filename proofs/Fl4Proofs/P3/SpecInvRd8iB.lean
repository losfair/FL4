/-
P3 (DESIGN.md §9), invariant line G1 (rd8i): **`Sched.BlockedScActive`
across `receive_ipc` and `receive_signal`** (spec side only, outside the
JAtZ cone).

* `ta_of_q` / `cba_of_q`: an ipc-queued thread's SCs are active by `BSA`
  itself, and its own SC (bound back by sb2's `ScBackS`) too.
* `nq_maybeReturnSc`, `ta_maybeReturnSc` (it only clears a binding).
* **`ba_recvSender`** (the sender arm from the dequeue state: the sender is
  still `BlockedOnSend` at its `reply_push`, rd8d's `TV` / `SF` frames; sb2's
  family keeps `ScInv`).
* **`ba_receiveIpc_p thread … σ (hI : ScInv σ) (hN : NotQ thread σ)
  (hT : TA thread σ)`** (the receiver is not ipc-queued: `complete_signal`'s
  donation; its SCs are active: the blocking arm).
* **`ba_receiveSignal_p`** (same two facts).
-/
import Fl4Proofs.P3.SpecInvRd8iA
open Classical

namespace Fl4Proofs.P3.SInvR.B8i
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g

noncomputable section

set_option maxHeartbeats 1000000

theorem ta_of_q {s : State Unit} {t : ObjRef} {x : Tcb} (h : BSA s) (hx : s.kheap t = some (.tcb x))
    (hq : ipcQueuedThreadState x.tcbState = true) : TA t s :=
  fun q y n hq' hy => h.tcb q y n t x hq' hy hx hq

theorem cba_of_q {s : State Unit} {t : ObjRef} {x : Tcb} (h : BSA s) (hB : SInvB.ScBackS s)
    (hx : s.kheap t = some (.tcb x)) (hq : ipcQueuedThreadState x.tcbState = true) : CBa t s := by
  intro x' c hx' hc
  rw [hx] at hx'; cases hx'
  obtain ⟨y, k, hk, hy, -⟩ := hB t x c hx hc
  exact ⟨y, k, hk, h.tcb c y k t x hk hy hx hq⟩

/-! ## `maybe_return_sc` frames -/

theorem nq_updateSchedContext (t p : ObjRef) (f : SchedContext → SchedContext) :
    IK (NotQ t) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, -, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]; exact nq_updN hσ fun _ h => by cases h

theorem nq_threadSetK (t u : ObjRef) (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbState = x.tcbState) :
    IK (NotQ t) (threadSet (Z := Unit) f u) := fun σ => nq_threadSet t u f hf σ

theorem nq_maybeReturnSc (t n u : ObjRef) : IK (NotQ t) (maybeReturnSc (Z := Unit) n u) := by
  unfold maybeReturnSc
  repeat' (first
    | (with_reducible exact nq_updateSchedContext _ _ _)
    | ((with_reducible refine nq_threadSetK _ _ _ ?_); intro _; rfl)
    | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem ta_updateSchedContext (t p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, ((f y).scTcb = y.scTcb ∨ (f y).scTcb = none) ∧ (f y).scRefillMax = y.scRefillMax) :
    IK (TA t) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨y, n, hk, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  intro q y' n' hq hy
  change Function.update σ.kheap p _ q = _ at hq
  by_cases eq : q = p
  · rw [eq, Function.update_self] at hq; cases hq
    rcases (hf y).1 with e1 | e1
    · have := hσ p y n hk (e1.symm.trans hy)
      show activeSc _ = true; rw [(hf y).2]; exact this
    · rw [e1] at hy; cases hy
  · rw [Function.update_of_ne eq] at hq; exact hσ q y' n' hq hy

theorem ta_threadSet (t u : ObjRef) (f : Tcb → Tcb) : IK (TA t) (threadSet (Z := Unit) f u) := by
  intro σ hσ x hx
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hx
  rw [e]
  intro q y n hq hy
  change Function.update σ.kheap u _ q = _ at hq
  by_cases eq : q = u
  · rw [eq, Function.update_self] at hq; cases hq
  · rw [Function.update_of_ne eq] at hq; exact hσ q y n hq hy

theorem ta_maybeReturnSc (t n u : ObjRef) : IK (TA t) (maybeReturnSc (Z := Unit) n u) := by
  unfold maybeReturnSc
  repeat' (first
    | (with_reducible exact ta_updateSchedContext _ _ _ fun _ => ⟨Or.inr rfl, rfl⟩)
    | (with_reducible exact ta_threadSet _ _ _)
    | ik_step0 | ik_unfold | (unfold NonDet.when))

/-! ## The sender arm -/

theorem sik_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) :
    SInvB.SIK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) :=
  SInvB.sik_of_sbk fun _ => by sb_auto

theorem sik_ifCond (scOpt : Option ObjRef) (a b : Option Bool) :
    SInvB.SIK (ifCondRefillUnblockCheck (Z := Unit) scOpt a b) :=
  SInvB.sik_of_sbk fun _ => by sb_auto

/-- **`receive_ipc`'s sender arm** from the dequeue state `s` (the sender a TCB
`BlockedOnSend` there): `BSA` kept, with any call-stack push and donation. -/
theorem ba_recvSender (sender thread epptr e : ObjRef) (reply : Option ObjRef) (data : SenderPayload)
    (s : State Unit) (hs : BSA s) (hI : SInvB.ScInv s)
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
        possibleSwitchTo (Z := Unit) sender) s).1) : BSA y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have b3 : BSA z3.2 := ba_doIpcTransfer sender (some epptr) _ _ thread s hs z3 h3
  have i3 : SInvB.ScInv z3.2 := sik_doIpcTransfer sender (some epptr) _ _ thread s hI z3 h3
  have t3 : TV (TVv s) z3.2 := tv_doIpcTransfer sender (some epptr) _ _ thread s rfl z3 h3
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
  have b5 : BSA z5.2 := ba_ifCondRefillUnblockCheck _ _ _ z3.2 b3 z5 h5
  have i5 : SInvB.ScInv z5.2 := sik_ifCond _ _ _ z3.2 i3 z5 h5
  have hx5 : z5.2.kheap sender = some (.tcb x3) :=
    (sf_ifCond x4.tcbSchedContext (some false) (some true) z3.2 h5).2.2 sender x3 hx3
  have hq5 : ipcQueuedThreadState x3.tcbState = true := by rw [hxs3]; rfl
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, -, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      exact ba_replyPush_p sender thread _ _ z5.2 (ta_of_q b5 hx5 hq5) (fun _ => cba_of_q b5 i5.back hx5 hq5) b5 y hy
    · exact ba_setThreadState sender .inactive rfl z5.2 b5 y hy
  · exact (by ba_auto : BAK _) z5.2 b5 y hy

/-! ## `receive_ipc` -/

theorem nq_cancelIpc {t u : ObjRef} (hne : u ≠ t) {σ : State Unit} (h : NotQ t σ) {z : Unit × State Unit}
    (hz : z ∈ (cancelIpc (Z := Unit) u σ).1) : NotQ t z.2 := by
  intro x hx
  obtain ⟨y0, hy0, e⟩ := (StK.st_cancelIpc (t0 := u) σ z hz).1 t x (Ne.symm hne) hx
  rw [e]; exact h y0 hy0

/-- The facts carried through `receive_ipc`. -/
def RF (t : ObjRef) (s : State Unit) : Prop := BSA s ∧ SInvB.ScInv s ∧ NotQ t s ∧ TA t s

theorem ba_recvRest (thread : ObjRef) (isBlocking : Bool) (epptr : ObjRef) (reply : Option ObjRef)
    (s : State Unit) (hF : RF thread s) (y : Unit × State Unit)
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
        | _ => receiveIpcBlocked isBlocking thread epptr reply) s).1) : BSA y.2 := by
  obtain ⟨hb, hi, hn, ht⟩ := hF
  obtain ⟨⟨ep, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨⟨ntfnptr, s2⟩, h2, hy⟩ := hy
  have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
  subst s2
  cases ntfnptr with
  | none =>
    dsimp only at hy
    obtain ⟨⟨ntfn, s3⟩, h3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
    subst s3
    dsimp only at hy
    split at hy
    · rename_i hc; exact absurd rfl hc.1
    obtain ⟨z4, h4, hy⟩ := hy
    unfold NonDet.when at h4
    rw [if_neg (fun hc => hc.1 rfl)] at h4
    obtain rfl := Set.mem_singleton_iff.1 h4
    split at hy
    · obtain ⟨z5, h5, hy⟩ := hy
      have e5 : z5.2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h5
      obtain ⟨z6, h6, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h6
      obtain ⟨z7, h7, hy⟩ := hy
      rw [e5] at h7
      have b7 := ba_tcbEpDequeue _ _ s hb z7 h7
      have i7 : SInvB.ScInv z7.2 := (SInvB.sik_of_sbk fun _ => by sb_auto) s hi z7 h7
      obtain ⟨⟨st, s8⟩, h8, hy⟩ := hy
      obtain ⟨x8, hx8, e8⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbState) h8
      simp only [Prod.mk.injEq] at e8; obtain ⟨rfl, e8⟩ := e8; subst s8
      cases hs : x8.tcbState
      case blockedOnSend e data =>
        rw [hs] at hy; dsimp only at hy
        obtain ⟨z9, h9, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 h9
        exact ba_recvSender _ thread epptr e reply data z7.2 b7 i7 hx8 hs y hy
      all_goals (rw [hs] at hy; dsimp only at hy; obtain ⟨z9, h9, -⟩ := hy; exact h9.elim)
    · exact ba_receiveIpcBlocked_p _ _ _ _ s ht hb y hy
  | some p =>
    dsimp only at hy
    obtain ⟨⟨ntfn, s3⟩, h3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
    subst s3
    dsimp only at hy
    split at hy
    · exact ba_completeSignal_p _ thread s hn hb y hy
    obtain ⟨z4, h4, hy⟩ := hy
    have hF4 : RF thread z4.2 := by
      unfold NonDet.when at h4
      split at h4
      · exact ⟨ba_maybeReturnSc _ _ s hb z4 h4, SInvB.sik_maybeReturnSc _ _ s hi z4 h4,
          nq_maybeReturnSc _ _ _ s hn z4 h4, ta_maybeReturnSc _ _ _ s ht z4 h4⟩
      · obtain rfl := Set.mem_singleton_iff.1 h4; exact ⟨hb, hi, hn, ht⟩
    obtain ⟨hb4, hi4, -, ht4⟩ := hF4
    split at hy
    · obtain ⟨z5, h5, hy⟩ := hy
      have e5 : z5.2 = z4.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h5
      obtain ⟨z6, h6, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h6
      obtain ⟨z7, h7, hy⟩ := hy
      rw [e5] at h7
      have b7 := ba_tcbEpDequeue _ _ z4.2 hb4 z7 h7
      have i7 : SInvB.ScInv z7.2 := (SInvB.sik_of_sbk fun _ => by sb_auto) z4.2 hi4 z7 h7
      obtain ⟨⟨st, s8⟩, h8, hy⟩ := hy
      obtain ⟨x8, hx8, e8⟩ := SInvQ.q1_mem_threadGet (f := Tcb.tcbState) h8
      simp only [Prod.mk.injEq] at e8; obtain ⟨rfl, e8⟩ := e8; subst s8
      cases hs : x8.tcbState
      case blockedOnSend e data =>
        rw [hs] at hy; dsimp only at hy
        obtain ⟨z9, h9, hy⟩ := hy
        obtain rfl := Set.mem_singleton_iff.1 h9
        exact ba_recvSender _ thread epptr e reply data z7.2 b7 i7 hx8 hs y hy
      all_goals (rw [hs] at hy; dsimp only at hy; obtain ⟨z9, h9, -⟩ := hy; exact h9.elim)
    · exact ba_receiveIpcBlocked_p _ _ _ _ z4.2 ht4 hb4 y hy

/-- **`receive_ipc thread …`**: the receiver not ipc-queued, its SCs active; sb2's `ScInv`. -/
theorem ba_receiveIpc_p (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (σ : State Unit)
    (hI : SInvB.ScInv σ) (hN : NotQ thread σ) (hT : TA thread σ) :
    IKp BSA σ (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc
  intro hσ y hy
  cases cap
  case endpointCap epptr bd rights =>
    obtain ⟨z0, h0, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 h0
    dsimp only at hy
    cases replyCap
    case replyCap r b =>
      dsimp only at hy
      obtain ⟨⟨tptr, s1⟩, h1, hy⟩ := hy
      have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
      subst s1
      obtain ⟨z2, h2, hy⟩ := hy
      have hF : RF thread z2.2 := by
        unfold NonDet.when at h2
        split at h2
        · rename_i hc
          exact ⟨ba_cancelIpc _ σ hσ z2 h2, (SInvB.sik_of_sbk fun _ => by sb_auto) σ hI z2 h2,
            nq_cancelIpc hc.2 hN h2, ta_sv hT (sv_cancelIpc' _ σ z2 h2)⟩
        · obtain rfl := Set.mem_singleton_iff.1 h2; exact ⟨hσ, hI, hN, hT⟩
      obtain ⟨z3, h3, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h3
      exact ba_recvRest thread isBlocking epptr (some r) z2.2 hF y hy
    case nullCap =>
      dsimp only at hy
      obtain ⟨z3, h3, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h3
      exact ba_recvRest thread isBlocking epptr none σ ⟨hσ, hI, hN, hT⟩ y hy
    all_goals (dsimp only at hy; obtain ⟨z3, h3, -⟩ := hy; exact h3.elim)
  all_goals (obtain ⟨z0, h0, -⟩ := hy; exact h0.elim)

/-- **`receive_signal thread …`**: the receiver not ipc-queued, its SCs active. -/
theorem ba_receiveSignal_p (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (σ : State Unit)
    (hN : NotQ thread σ) (hT : TA thread σ) :
    IKp BSA σ (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal
  intro hσ y hy
  cases cap
  case notificationCap np bd rs =>
    dsimp only at hy
    obtain ⟨z0, h0, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 h0
    dsimp only at hy
    obtain ⟨⟨nt, s1⟩, h1, hy⟩ := hy
    have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
    subst s1
    dsimp only at hy
    cases hs : nt.ntfnObj
    case activeNtfn badge =>
      rw [hs] at hy; dsimp only at hy
      refine (ikp_bind_q (Q := NotQ thread) (ikp_of_ik (ba_asUser _ _) σ) (fun y hy => nq_asUser _ _ _ σ hN y hy)
        fun _ s hq => ?_) hσ y hy
      refine ikp_bind_q (Q := NotQ thread) (ikp_of_ik (ba_setSimpleKo _ _ _) s)
        (fun y hy => nq_setSimpleKo _ _ _ _ s hq y hy) fun _ s hq => ?_
      refine ikp_bind (ba_maybeDonateSc_p _ _ s hq) fun _ => ?_
      ba_auto
    all_goals (rw [hs] at hy; dsimp only at hy; exact ba_receiveSignalBlocked_p _ _ _ σ hT hσ y hy)
  all_goals (dsimp only at hy; obtain ⟨z0, h0, -⟩ := hy; exact h0.elim)

end

end Fl4Proofs.P3.SInvR.B8i
