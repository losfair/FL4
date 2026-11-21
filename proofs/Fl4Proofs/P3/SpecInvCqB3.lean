/-
P3 (DESIGN.md §9), invariant line G1 (ctq9): **the receive side, part 2:
`receive_ipc` of the current thread** (KENTRY-PLAN ctq8 handoff 1-2; spec
side only, outside the JAtZ cone); ctq8 handoff 3 (`handle_recv`).

* **`cs_cancelIpc : IK (CS g) (cancel_ipc u)`** for every `u`: this spec's
  `cancel_ipc` never writes a TCB's SC field (its BlockedOnReply arm is
  `reply_remove_tcb`, which edits the SC's reply list and the reply only, as
  l4v's `reply_remove_tcb`; no `sched_context_donate`). So ctq8's `hD` (left
  disjunct: the current thread keeps its SC) survives receive_ipc's reply
  cancel outright; `rs_cancelIpc` states ctq8's `RS` form. (ctq8's design
  note named `reply_remove → sched_context_donate`: that is `reply_remove`,
  reached from do_reply_transfer / the deletion cone, not from cancel_ipc.)
* `RV C c := EB true ∧ ct = C ∧ ct's SC = some c`, kept by the reply cancel
  and the reads; `ETq C := EB true ∧ ct = C` after `maybe_return_sc`.
* The sender arm `eb_recvSender : HK1 (EB false) (EB false)` (the sender was
  read BlockedOnSend, so it has `NPQ` by SchedQ; `do_ipc_transfer`, the reads
  and the refill unblock check keep the scheduler action and both queues;
  `possible_switch_to sender` at `k = false` needs no "sender ≠ ct").
* **`eb_receiveIpc_ct (hC : CurScT σ) : HKp (EB true) (EB false) σ
  (receive_ipc ct cap b rc)`**: the active bound notification is
  `eb_completeSignal_ct` with the left disjunct; the blocked arm is
  `eb_receiveIpcBlocked_p` with `npq_ct`.
* Item 3: `pk_*` (the cap lookups keep every predicate: `resolveAddressBits'`
  by FX's well-founded recursion), `hr_asUser` / `hr_lookupReply`, and
  **`eb_handleRecv_ct (hC : CurScT σ) (hN : NQ [ct] σ) : HKp (EB true) (EB
  false) σ (handle_recv b r)`** (carry `HR C c := RV C c ∧ NQ [C] ∧ cur_sc =
  c`; endpoint → `eb_receiveIpc_rv`, notification → `eb_receiveSignal_ct`,
  lookup fault → `eb_handleFault_p` with `npq_ct`).
-/
import Fl4Proofs.P3.SpecInvCqB2
import Fl4Proofs.P3.SpecInvFaultTcbsH8
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Item 1: `cancel_ipc` keeps every TCB's SC field -/

theorem cs_cancelIpc (g : ObjRef → Option ObjRef) (u : ObjRef) : IK (CS g) (cancelIpc (Z := Unit) u) := by
  unfold cancelIpc; cs_auto

/-- ctq8's `RSq t`: the current thread keeps an SC, or `t` is read blocked. -/
abbrev RSq (t : ObjRef) (s : State Unit) : Prop := (∃ c, CS (fun _ => some c) s) ∨ AN t s

theorem rs_cancelIpc (t u : ObjRef) : IK (RSq t) (cancelIpc (Z := Unit) u) := by
  intro σ h y hy
  rcases h with ⟨c, hc⟩ | ha
  · exact Or.inl ⟨c, cs_cancelIpc _ u σ hc y hy⟩
  · exact Or.inr (an_cancelIpc t u σ ha y hy)

/-! ## The carried facts -/

/-- A read keeps any predicate. -/
theorem ik_of_ro {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ σ0 : State Unit, IK (fun s => s = σ0) m) : IK P m := by
  intro σ hσ y hy
  rw [cq5_ro h hy]; exact hσ

/-- `EB true`, the current thread `C`, bound to `c`. -/
abbrev RV (C c : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ CS (fun _ => some c) s

theorem rv_of {C c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK true m) (h2 : IK (CTh C) m)
    (h3 : IK (CS (fun _ => some c)) m) : IK (RV C c) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2 y hy⟩

/-- `EB true` and the current thread `C`. -/
abbrev ETq (C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s

/-- `EB false` and `t` with `NPQ`. -/
abbrev ES (t : ObjRef) (s : State Unit) : Prop := EB false s ∧ NPQ t s

theorem es_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK false m) (h2 : IK (NPQ t) m) :
    IK (ES t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2 y hy⟩

theorem npq_doIpcTransfer (t sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) :
    IK (NPQ t) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) :=
  fun σ h y hy => (nc_doIpcTransfer t σ.curThread sender ep badge grant receiver σ ⟨h, rfl⟩ y hy).1

theorem npq_refillCheck (t : ObjRef) (o : Option ObjRef) (a b : Option Bool) :
    IK (NPQ t) (ifCondRefillUnblockCheck (Z := Unit) o a b) :=
  npq_frame t fun _ _ _ => by unfold ifCondRefillUnblockCheck; repeat' (first | ik_step0 | ik_unfold)

theorem hk1_getThreadState_bind {Q : State Unit → Prop} {β : Type} {t : ObjRef}
    {k : ThreadState → NonDet (State Unit) β}
    (h : ∀ s x, s.kheap t = some (.tcb x) → EB false s → ∀ y, y ∈ (k x.tcbState s).1 → Q y.2) :
    HK1 (EB false) Q (getThreadState (Z := Unit) t >>= k) := by
  intro s hs y ⟨z, hz, hy⟩
  unfold getThreadState at hz
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  exact h s x hx hs y hy

/-! ## The sender arm -/

/-- The tail of the sender arm, from the sender's facts. -/
theorem eb_recvSenderTail (thread epptr sender : ObjRef) (reply : Option ObjRef) (data : SenderPayload) :
    HK1 (ES sender) (EB false) (do
      doIpcTransfer (Z := Unit) sender (some epptr)
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
        possibleSwitchTo sender) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (ES sender) m := fun h => ik_of_ro h
  refine hk1_bind (hk1_ik (es_of (by eb_auto) (npq_doIpcTransfer _ _ _ _ _ _))) fun _ => ?_
  refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun scPtr => ?_
  refine hk1_bind (hk1_ik (es_of (by eb_auto) (npq_refillCheck _ _ _ _))) fun _ => ?_
  refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun fault => ?_
  split
  · split
    · refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun _ => ?_
      refine hk1_bind (hk1_ik (ik_pure _)) fun d => ?_
      exact fun s hs => eb_replyPush_p _ _ _ _ s hs.2 hs.1
    · exact fun s hs => eb_setThreadState_p _ _ s (Or.inr hs.2) hs.1
  · intro s hs y ⟨z, hz, hy⟩
    have e1 : EB false z.2 := eb_setThreadState_r sender .running rfl s hs.1 z hz
    have r1 : RnH sender z.2.kheap := (tqc_setThreadState_r sender .running rfl s z hs.1.1.1.1 hz).2
    exact eb_possibleSwitchTo_p sender z.2 r1 (fun h => by cases h) e1 y hy

/-- **The sender arm of `receive_ipc`** (`EB false` throughout). -/
theorem eb_recvSender (thread epptr : ObjRef) (reply : Option ObjRef) (q : List ObjRef) :
    HK1 (EB false) (EB false) (do
      NonDet.assert (q ≠ [])
      let sender ← pure (the q.head?)
      tcbEpDequeue (Z := Unit) sender epptr
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
        possibleSwitchTo sender) := by
  refine hk1_bind (hk1_ik (ik_assert _)) fun _ => ?_
  refine hk1_bind (hk1_ik (ik_pure _)) fun sender => ?_
  refine hk1_bind (hk1_ik (by eb_auto)) fun _ => ?_
  refine hk1_getThreadState_bind fun s x hx hs y hy => ?_
  revert hy
  cases h : x.tcbState with
  | blockedOnSend r data =>
    intro hy
    have hn : NPQ sender s := npq_nr hs.1 hx (by rw [h]; rfl)
    obtain ⟨z, hz, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hz] at hy
    exact eb_recvSenderTail thread epptr sender reply data s ⟨hs, hn⟩ y hy
  | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)

/-! ## The tail and `receive_ipc` -/

/-- The `if` of `receive_ipc` after the endpoint and notification reads. -/
theorem eb_recvTail (C c epptr : ObjRef) (isBlocking : Bool) (reply ntfnptr : Option ObjRef) (ntfn : Notification)
    (ep : Endpoint) :
    HK1 (RV C c) (EB false) (
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
    exact eb_completeSignal_ct _ s (Or.inl ⟨c, h3⟩) h1 y hy
  · refine hk1_bind (P := RV C c) (R := ETq C) (fun s hs y hy => ?_) fun _ => ?_
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

theorem hk1_fail_bind' {P Q : State Unit → Prop} {α β : Type} {g : α → NonDet (State Unit) β} :
    HK1 P Q ((NonDet.fail : NonDet (State Unit) α) >>= g) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

/-- `receive_ipc` from `RV C c`. -/
theorem eb_receiveIpc_rv (C c : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    HK1 (RV C c) (EB false) (receiveIpc (Z := Unit) C cap isBlocking replyCap) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RV C c) m := fun h => ik_of_ro h
  have hrest : ∀ (epptr : ObjRef) (reply : Option ObjRef), HK1 (RV C c) (EB false) (do
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
      exact hk1_bind (hk1_ik (ik_pure _)) fun ntfn => eb_recvTail C c epptr isBlocking reply none ntfn ep
    | some p =>
      exact hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun ntfn =>
        eb_recvTail C c epptr isBlocking reply (some p) ntfn ep
  unfold receiveIpc
  cases cap
  case endpointCap epptr bd rights =>
    refine hk1_bind (hk1_ik (ik_pure _)) fun p => ?_
    obtain ⟨epptr', rights'⟩ := p
    cases replyCap
    case replyCap r b =>
      refine hk1_bind (hk1_ik (hro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun tptr => ?_
      refine hk1_bind (hk1_ik ?_) fun _ => ?_
      · refine ik_when _ (rv_of (by eb_auto) (ct_auto_cancelIpc _ _) (cs_cancelIpc _ _))
      first
        | exact hrest epptr' (some r)
        | exact hk1_bind (hk1_ik (ik_pure _)) fun reply => hrest epptr' reply
    case nullCap =>
      exact hk1_bind (hk1_ik (ik_pure _)) fun reply => hrest epptr' reply
    all_goals exact hk1_fail_bind'
  all_goals exact hk1_fail_bind'

/-- **`receive_ipc` of the current thread**: `EB true` to `EB false`, given
CurScT at its start (ctq8 handoff 2). -/
theorem eb_receiveIpc_ct (cap : Cap) (isBlocking : Bool) (replyCap : Cap) (σ : State Unit) (hC : CurScT σ) :
    HKp (EB true) (EB false) σ (receiveIpc (Z := Unit) σ.curThread cap isBlocking replyCap) :=
  fun hσ y hy => eb_receiveIpc_rv σ.curThread σ.curSc cap isBlocking replyCap σ ⟨hσ, rfl, hC⟩ y hy


/-! ## Item 3: `handle_recv` -/

/-! ### The cap lookups are reads (any predicate; FX's lfp proof) -/

section PK
variable {P : State Unit → Prop}

theorem pk_resolveAddressBits' (p : Cap × CapRef) : IKE P (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by repeat' (first | ik_step0 | ik_unfold))) fun nc => ?_
        split
        · exact pk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

theorem pk_lookupCap (thread : ObjRef) (ref : CapRef) : IKE P (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap lookupSlotForThread resolveAddressBits
  repeat' (first | (with_reducible exact pk_resolveAddressBits' _) | ik_step0 | ik_unfold)

theorem pk_capFaultLookupCap (cp : ObjRef) (rp : Bool) (thread : ObjRef) (ref : CapRef) :
    IKE P (capFaultOnFailure (Z := Unit) cp rp (lookupCap thread ref)) := by
  unfold capFaultOnFailure
  repeat' (first | (with_reducible exact pk_lookupCap _ _) | ik_step0 | ik_unfold)

end PK

/-- The `handle_recv` carry: `RV`, nq3's `NQ [C]` and `cur_sc = c`. -/
abbrev HR (C c : ObjRef) (s : State Unit) : Prop := RV C c s ∧ NQ [C] s ∧ s.curSc = c

theorem hr_asUser (C c t : ObjRef) (r : Register) : IK (HR C c) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  refine ⟨rv_of (by eb_auto) (ct_asUser _ _ _) (cs_asUser _ _) s hs.1 z hz, ?_, ?_⟩
  · exact (show NQK [C] (asUser (Z := Unit) t (getRegister r)) by nq_auto) s hs.2.1 z hz
  · exact (show IK (fun s => s.curSc = c) (asUser (Z := Unit) t (getRegister r)) by
      unfold asUser; repeat' (first | ik_step0 | ik_unfold)) s hs.2.2 z hz

theorem hr_lookupReply (C c : ObjRef) : IKE (HR C c) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact hr_asUser _ _ _ _) | (with_reducible exact pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv`** from `HR C c`: endpoint → `receive_ipc` (item 2),
notification → ctq8's `eb_receiveSignal_ct`, a lookup fault → ctq7's
`eb_handleFault_p` with `npq_ct` and `NQ [ct]`. -/
theorem eb_handleRecv_hr (C c : ObjRef) (blk canReply : Bool) :
    HK (HR C c) (EB false) (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (HR C c) m := fun h => ik_of_ro h
  have hRIP : ∀ cp rc, HK (HR C c) (EB false) (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs => eb_receiveIpc_rv C c cp blk rc s hs.1
  have hRS : ∀ cp, HK (HR C c) (EB false) (receiveSignal (Z := Unit) C cp blk) := by
    intro cp s hs y hy
    obtain ⟨⟨h1, rfl, h3⟩, -, h5⟩ := hs
    exact eb_weak (eb_receiveSignal_ct cp blk s (fun x hx => by rw [h3 x hx, h5]) h1 y hy)
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.1.2.1
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : HR C c y2.2 := (?_ : IK (HR C c) _) σ hσ y2 h2
  · refine hk_catch (I := HR C c) (Q0 := EB false) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (hr_lookupReply C c) (fun rc => ?_)
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
      obtain ⟨⟨h1, rfl, -⟩, h4, -⟩ := hs
      exact eb_weak (eb_handleFault_p (k := true) s.curThread e s (npq_ct h1) h4
        (List.mem_singleton_self _) h1 z hz)
  · repeat' (first | exact hr_asUser C c _ _ | ik_step0)

/-- **`handle_recv` of the current thread**: `EB true` to `EB false` from
CurScT and nq3's `NQ [ct]` at its start. -/
theorem eb_handleRecv_ct (blk canReply : Bool) (σ : State Unit) (hC : CurScT σ) (hN : NQ [σ.curThread] σ) :
    HKp (EB true) (EB false) σ (handleRecv (Z := Unit) blk canReply) :=
  fun hσ y hy => eb_handleRecv_hr σ.curThread σ.curSc blk canReply σ ⟨⟨hσ, rfl, hC⟩, hN, rfl⟩ y hy

end

end Fl4Proofs.P3.SInvQ
