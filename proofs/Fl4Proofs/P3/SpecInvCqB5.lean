/-
P3 (DESIGN.md §9), invariant line G1 (ctq10): **the receive side from ctq8's
`RSq ct`** instead of CurScT (spec side only, outside the JAtZ cone).

ReplyRecv runs `handle_recv` after `do_reply_transfer`, whose `reply_remove`
may give the current thread's SC back to its caller
(`sched_context_donate`). Then CurScT is gone, but the donation's
`test_reschedule ct` has set `choose_new_thread`, so ctq8's
`RSq ct := (∃ c, ct's SC field = some c) ∨ AN ct` still holds. Every use of
CurScT on the receive side is a `maybe_donate_sc ct` (in `complete_signal`
and in `receive_signal`'s active arm), and both work from `RSq ct`
(`eb_completeSignal_ct` already takes it).

* `eb_receiveSignal_rs (hD : RSq ct σ) : HKp (EB true) (EB false) σ
  (receive_signal ct cap b)`.
* `RVs C := EB true ∧ ct = C ∧ RSq C` (kept by the reply cancel via
  `rs_cancelIpc` and by the reads), `eb_receiveIpc_rs`.
* `HRs C := RVs C ∧ NQ [C]`, **`eb_handleRecv_rs (hD : RSq ct σ) (hN : NQ [ct]
  σ) : HKp (EB true) (EB false) σ (handle_recv b r)`**.
-/
import Fl4Proofs.P3.SpecInvCqB3
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem rs_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : ∀ c, IK (CS (fun _ => some c)) m)
    (h2 : IK (AN t) m) : IK (RSq t) m := by
  intro σ h y hy
  rcases h with ⟨c, hc⟩ | ha
  · exact Or.inl ⟨c, h1 c σ hc y hy⟩
  · exact Or.inr (h2 σ ha y hy)

/-- **`receive_signal` of the current thread** from `RSq ct` (`EB true` to
`EB false`). -/
theorem eb_receiveSignal_rs (cap : Cap) (isBlocking : Bool) (σ : State Unit) (hD : RSq σ.curThread σ) :
    HKp (EB true) (EB false) σ (receiveSignal (Z := Unit) σ.curThread cap isBlocking) := by
  unfold receiveSignal
  intro hσ y hy
  try dsimp only at hy
  split at hy
  swap
  · obtain ⟨z, hz, -⟩ := hy
    exact hz.elim
  obtain ⟨z, hz, hy⟩ := hy
  have ez : z.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz
  obtain ⟨np, s1⟩ := z
  simp only at ez; subst s1
  obtain ⟨w, hw, hy⟩ := hy
  have ew : w.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw
  obtain ⟨ntfn, s2⟩ := w
  simp only at ew; subst s2
  cases hn : ntfn.ntfnObj with
  | idleNtfn =>
    simp only [hn] at hy
    exact eb_weak (eb_receiveSignalBlocked_p _ _ _ σ (npq_ct hσ) hσ y hy)
  | waitingNtfn q =>
    simp only [hn] at hy
    exact eb_weak (eb_receiveSignalBlocked_p _ _ _ σ (npq_ct hσ) hσ y hy)
  | activeNtfn bd =>
    simp only [hn] at hy
    obtain ⟨u1, hu1, hy⟩ := hy
    have hE1 : EB true u1.2 := by
      refine (?_ : EBK true _) σ hσ u1 hu1
      eb_auto
    have hT1 : CTh σ.curThread u1.2 := ct_asUser _ _ _ σ rfl u1 hu1
    have hD1 : RSq σ.curThread u1.2 := rs_of (fun c => cs_asUser _ _) (an_asUser _ _ _) σ hD u1 hu1
    obtain ⟨u2, hu2, hy⟩ := hy
    have hE2 : EB true u2.2 := by
      refine (?_ : EBK true _) u1.2 hE1 u2 hu2
      eb_auto
    have hT2 : CTh σ.curThread u2.2 := by
      refine (?_ : IK (CTh σ.curThread) _) u1.2 hT1 u2 hu2
      repeat' (first | ik_step0 | ik_unfold)
    have hD2 : RSq σ.curThread u2.2 := by
      refine rs_of (fun c => ?_) ?_ u1.2 hD1 u2 hu2
      · cs_auto
      · an_auto
    obtain ⟨u3, hu3, hy⟩ := hy
    have h3 : EB false u3.2 := by
      rcases hD2 with ⟨c, hc⟩ | ha
      · have e3 : u3.2 = u2.2 := md_skip _ _ u2.2 (fun x hx => by
          have hT2' : u2.2.curThread = σ.curThread := hT2
          rw [← hT2'] at hx
          rw [hc x hx]; simp) hu3
        rw [e3]; exact eb_weak hE2
      · exact ⟨sq4_of (tq_maybeDonateSc _ _) (sa_maybeDonateSc _ _) (q4_maybeDonateSc _ _) u2.2 hE2.1 u3 hu3,
          mdk_maybeDonateSc (k := false) _ _ u2.2 ⟨rbk_weak hE2.2, hE2.1.1.1, ha, fun e => by cases e⟩ u3 hu3⟩
    refine (?_ : EBK false _) u3.2 h3 y hy
    eb_auto

/-! ## `receive_ipc` -/

/-- `EB true`, the current thread `C`, and `RSq C`. -/
abbrev RVs (C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ RSq C s

theorem rvs_of {C : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : IK (CTh C) m)
    (h3 : IK (RSq C) m) : IK (RVs C) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2 y hy⟩

theorem eb_recvTail_rs (C epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef) (ntfn : Notification)
    (ep : Endpoint) :
    HK1 (RVs C) (EB false) (
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (Z := Unit) (the ntfnptr) C
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) C
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
            C
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender C (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking C epptr reply) := by
  split
  · intro s hs y hy
    obtain ⟨h1, rfl, h3⟩ := hs
    exact eb_completeSignal_ct _ s h3 h1 y hy
  · refine hk1_bind (P := RVs C) (R := ETq C) (fun s hs y hy => ?_) fun _ => ?_
    · have hm : IK (ETq C) (NonDet.when (ntfnptr ≠ none ∧ isBlocking = true) <|
          maybeReturnSc (Z := Unit) (the ntfnptr) C) := by
        refine ik_when _ fun σ h y hy => ⟨?_, ?_⟩
        · exact (show EBK true (maybeReturnSc (Z := Unit) (the ntfnptr) C) by eb_auto) σ h.1 y hy
        · exact (show IK (CTh C) (maybeReturnSc (Z := Unit) (the ntfnptr) C) by
            unfold maybeReturnSc
            repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless))) σ h.2 y hy
      exact hm s ⟨hs.1, hs.2.1⟩ y hy
    cases ep with
    | sendEP q => exact fun s hs => eb_recvSender C epptr reply q s (eb_weak hs.1)
    | idleEP =>
      intro s hs y hy
      obtain ⟨h1, rfl⟩ := hs
      exact eb_weak (eb_receiveIpcBlocked_p (k := true) _ _ _ _ s (npq_ct h1) h1 y hy)
    | recvEP q =>
      intro s hs y hy
      obtain ⟨h1, rfl⟩ := hs
      exact eb_weak (eb_receiveIpcBlocked_p (k := true) _ _ _ _ s (npq_ct h1) h1 y hy)

/-- `receive_ipc` from `RVs C`. -/
theorem eb_receiveIpc_rs (C : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    HK1 (RVs C) (EB false) (receiveIpc (Z := Unit) C cap isBlocking replyCap) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RVs C) m := fun h => ik_of_ro h
  have hrest : ∀ (epptr : ObjRef) (reply : Option ObjRef), HK1 (RVs C) (EB false) (do
      let ep ← getEndpoint (Z := Unit) epptr
      let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification C
      let ntfn ← match ntfnptr with
        | none => pure defaultNotification
        | some p => getNotification p
      if ntfnptr ≠ none ∧ isActive ntfn
      then
        completeSignal (the ntfnptr) C
      else do
        NonDet.when (ntfnptr ≠ none ∧ isBlocking) <| maybeReturnSc (the ntfnptr) C
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
            C
          let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
          ifSporadicCurScAssertRefillUnblockCheck scPtr
          let fault ← threadGet Tcb.tcbFault sender
          if data.senderIsCall ∨ fault ≠ none
          then
            if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
            then do
              let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
              let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
              replyPush sender C (the reply) donate
            else setThreadState sender .inactive
          else do
            setThreadState sender .running
            possibleSwitchTo sender
        | _ => receiveIpcBlocked isBlocking C epptr reply) := by
    intro epptr reply
    refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun ep => ?_
    refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun ntfnptr => ?_
    cases ntfnptr with
    | none =>
      exact hk1_bind (hk1_ik (ik_pure _)) fun ntfn => eb_recvTail_rs C epptr isBlocking reply none ntfn ep
    | some p =>
      exact hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun ntfn =>
        eb_recvTail_rs C epptr isBlocking reply (some p) ntfn ep
  unfold receiveIpc
  cases cap
  case endpointCap epptr bd rights =>
    refine hk1_bind (hk1_ik (ik_pure _)) fun p => ?_
    obtain ⟨epptr', rights'⟩ := p
    cases replyCap
    case replyCap r b =>
      refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun tptr => ?_
      refine hk1_bind (hk1_ik ?_) fun _ => ?_
      · refine ik_when _ (rvs_of (by eb_auto) (ct_auto_cancelIpc _ _) (rs_cancelIpc _ _))
      first
        | exact hrest epptr' (some r)
        | exact hk1_bind (hk1_ik (ik_pure _)) fun reply => hrest epptr' reply
    case nullCap =>
      exact hk1_bind (hk1_ik (ik_pure _)) fun reply => hrest epptr' reply
    all_goals exact hk1_fail_bind'
  all_goals exact hk1_fail_bind'

/-! ## `handle_recv` -/

/-- The `handle_recv` carry from `RSq`. -/
abbrev HRs (C : ObjRef) (s : State Unit) : Prop := RVs C s ∧ NQ [C] s

theorem hrs_asUser (C t : ObjRef) (r : Register) : IK (HRs C) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  refine ⟨rvs_of (by eb_auto) (ct_asUser _ _ _) (rs_of (fun c => cs_asUser _ _) (an_asUser _ _ _)) s hs.1 z hz, ?_⟩
  exact (show NQK [C] (asUser (Z := Unit) t (getRegister r)) by nq_auto) s hs.2 z hz

theorem hrs_lookupReply (C : ObjRef) : IKE (HRs C) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact hrs_asUser _ _ _) | (with_reducible exact pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv`** from `HRs C`. -/
theorem eb_handleRecv_hrs (C : ObjRef) (blk canReply : Bool) :
    HK (HRs C) (EB false) (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (HRs C) m := fun h => ik_of_ro h
  have hRIP : ∀ cp rc, HK (HRs C) (EB false) (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs => eb_receiveIpc_rs C cp blk rc s hs.1
  have hRS : ∀ cp, HK (HRs C) (EB false) (receiveSignal (Z := Unit) C cp blk) := by
    intro cp s hs y hy
    obtain ⟨⟨h1, rfl, h3⟩, -⟩ := hs
    exact eb_receiveSignal_rs cp blk s h3 h1 y hy
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.1.2.1
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : HRs C y2.2 := (?_ : IK (HRs C) _) σ hσ y2 h2
  · refine hk_catch (I := HRs C) (Q0 := EB false) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (hrs_lookupReply C) (fun rc => ?_)
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
      obtain ⟨⟨h1, rfl, -⟩, h4⟩ := hs
      exact eb_weak (eb_handleFault_p (k := true) s.curThread e s (npq_ct h1) h4
        (List.mem_singleton_self _) h1 z hz)
  · repeat' (first | exact hrs_asUser C _ _ | ik_step0)

/-- **`handle_recv` of the current thread from `RSq ct`**: `EB true` to `EB
false`, given ctq8's `RSq ct` and nq3's `NQ [ct]` at its start. -/
theorem eb_handleRecv_rs (blk canReply : Bool) (σ : State Unit) (hD : RSq σ.curThread σ)
    (hN : NQ [σ.curThread] σ) :
    ∀ y, EB true σ → y ∈ (handleRecv (Z := Unit) blk canReply σ).1 → EB false y.2 :=
  fun y hσ hy => eb_handleRecv_hrs σ.curThread blk canReply σ ⟨⟨hσ, rfl, hD⟩, hN⟩ y hy

/-- CurScT gives `RSq ct`. -/
theorem rsq_of_curScT {σ : State Unit} (hC : CurScT σ) : RSq σ.curThread σ :=
  Or.inl ⟨σ.curSc, fun x hx => hC x hx⟩

/-! ## The stepwise fact behind `RSq ct` (handoff) -/

/-- **`ResSc`**: under `resume_cur_thread` the current thread (if a TCB) has
an SC (the l4v fact that a resumed current thread is schedulable, SC side).
Only `schedule` sets `resume_cur_thread`; every writer that strips the
current thread's SC (`sched_context_donate`'s `test_reschedule`,
`sched_context_unbind_tcb`, `maybe_return_sc`) reschedules. Not yet carried
(KENTRY-PLAN ctq10 handoff). -/
abbrev ResSc (s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread → ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext ≠ none

theorem resSc_of_curScT {σ : State Unit} (hC : CurScT σ) : ResSc σ :=
  fun _ x hx => by rw [hC x hx]; simp

/-- `EB true` (which gives `action ≠ switch ct`) and `ResSc` give `RSq ct`. -/
theorem rsq_of_resSc {s : State Unit} (hE : EB true s) (hR : ResSc s) : RSq s.curThread s := by
  by_cases ha : s.schedulerAction = .resumeCurThread
  · left
    by_cases hx : ∃ x, s.kheap s.curThread = some (.tcb x)
    · obtain ⟨x, hx⟩ := hx
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (hR ha x hx)
      exact ⟨c, fun x' hx' => by rw [hx] at hx'; cases hx'; exact hc⟩
    · exact ⟨s.curSc, fun x hx' => absurd ⟨x, hx'⟩ hx⟩
  · exact Or.inr ⟨(npq_ct hE).1.1, fun h => absurd h ha⟩

/-- **`handle_recv` from `ResSc`** (the form ReplyRecv / NBSendRecv /
NBSendWait need after their send phase). -/
theorem eb_handleRecv_res (blk canReply : Bool) (σ : State Unit) (hR : ResSc σ) (hN : NQ [σ.curThread] σ) :
    ∀ y, EB true σ → y ∈ (handleRecv (Z := Unit) blk canReply σ).1 → EB false y.2 :=
  fun y hσ hy => eb_handleRecv_rs blk canReply σ (rsq_of_resSc hσ hR) hN y hσ hy

end

end Fl4Proofs.P3.SInvQ
