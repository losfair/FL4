/-
P3 (DESIGN.md §9), invariant line G1 (rd9, KENTRY-PLAN rd8a handoff 1):
**`TmoNR`: after `handle_timeout t` of a runnable `t`, `t` is not runnable**
(spec side only, outside the JAtZ cone). True in every state: no premise.

* The reads of `is_valid_timeout_handler` and the second `get_cap` keep the
  state and read the same slot (`SInvU.getCap_capAt`), so the assert makes
  the handler cap an endpoint cap and `send_fault_ipc` takes its endpoint arm.
* After the fault write, `QR t` (t's fault is set and t is runnable, a `TP`
  predicate) holds and survives the endpoint dequeue; the dequeued receiver is
  read `BlockedOnReceive`, so it is not `t`.
* `do_ipc_transfer` and `reply_unlink_tcb` of the receiver keep `QF t` (t's
  fault is set: no TCB write of theirs touches a fault), so `send_ipc` reads a
  fault and takes the call arm: `reply_push` (t BlockedOnReply) or t Inactive.
  With no receiver, t is BlockedOnSend.
* From there `NRun t` is the `OPG` instance of the FaultTcbs frame
  `nrF t` (`R p _ s := p = t → ¬ runnable s`, closed under fault clears,
  Inactive writes and fresh TCBs), carried by the generated `fg_*` lemmas;
  the receiver's Running write is allowed since it is not `t`.
* **`tmoNR : A8.TmoNR`**, and the rd8a tops without it:
  **`kcall_rdyOff9` / `kentry_rdyOff9`**.
-/
import Fl4Proofs.P3.SpecInvRd8A4
import Fl4Proofs.P3.SpecInvUtR
open Classical

namespace Fl4Proofs.P3.SInvR.A9
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `NRun t` as a FaultTcbs frame instance -/

/-- `t` is not runnable, as an `FQ`. -/
def nrF (t : ObjRef) : FQ where
  R p _ s := p = t → runnable s = false
  clr _ _ _ h := h
  st _ _ _ _ _ := rfl
  dflt _ _ := rfl

abbrev NO (t : ObjRef) : State Unit → Prop := OPG (nrF t) Set.univ (fun _ => True)

theorem no_of_nrun {t : ObjRef} {s : State Unit} (h : A8.NRun t s) : NO t s := by
  refine ⟨fun p o hp => ?_, trivial⟩
  cases o with
  | tcb x => exact fun e => by subst e; exact h x hp
  | notification n => exact fun _ _ => Set.mem_univ _
  | _ => trivial

theorem nrun_of_no {t : ObjRef} {s : State Unit} (h : NO t s) : A8.NRun t s :=
  fun x hx => h.1 t _ hx rfl

/-- A non-runnable state write of `t` gives `NO t`, from any state. -/
theorem no_sts (t : ObjRef) (ts : ThreadState) (h : runnable ts = false) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) t ts σ).1) : NO t y.2 :=
  no_of_nrun fun x hx => by rw [sts_post hy x hx]; exact h

theorem no_bind {t : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} {σ : State Unit}
    (hm : ∀ y ∈ (m σ).1, NO t y.2) (hg : ∀ a, IK (NO t) (g a)) : ∀ y ∈ ((m >>= g) σ).1, NO t y.2 := by
  intro y ⟨z, hz, hy⟩
  exact hg z.1 z.2 (hm z hz) y hy

/-! ## The TCB-predicate walk (`TP`) -/

/-- `t`'s fault is set. -/
def QF (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → x.tcbFault ≠ none

/-- `t`'s fault is set and `t` is runnable. -/
def QR (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → x.tcbFault ≠ none ∧ runnable x.tcbState = true

/-- The writers that keep every TCB's fault and state. -/
macro "tq_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine tp_asUser _ _ ?_); intro _ _ h; exact h)
  | ((with_reducible refine tp_setMrs _ _ _ ?_); intro _ _ h; exact h)
  | ((with_reducible refine tp_archThreadSet _ _ ?_); intro _ _ h; exact h)
  | (with_reducible exact tp_setSimpleKo _ _ _)
  | ((with_reducible refine tp_setObject _ _ ?_); intro _ h; cases h; done)
  | ik_step0 | ik_unfold))

theorem qf_setThreadState (t u : ObjRef) (ts : ThreadState) : IK (TP (QF t)) (setThreadState (Z := Unit) u ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun _ h => h) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; repeat' ik_step0

theorem qr_tcbEpDequeue (t d e : ObjRef) : IK (TP (QR t)) (tcbEpDequeue (Z := Unit) d e) := by
  unfold tcbEpDequeue; tq_auto

theorem qf_lookupIpcBuffer (t : ObjRef) (b : Bool) (r : ObjRef) : IK (TP (QF t)) (lookupIpcBuffer (Z := Unit) b r) := by
  unfold lookupIpcBuffer; tq_auto

theorem qf_doFaultTransfer (t : ObjRef) (bd : Data) (snd rcv : ObjRef) (buf : Option ObjRef) :
    IK (TP (QF t)) (doFaultTransfer (Z := Unit) bd snd rcv buf) := by
  unfold doFaultTransfer; tq_auto

/-- The sender's fault is set, so the fault arm runs. -/
theorem qf_doIpcTransfer (t : ObjRef) (ep : Option ObjRef) (bd : Badge) (g : Bool) (rcv : ObjRef) :
    IK (TP (QF t)) (doIpcTransfer (Z := Unit) t ep bd g rcv) := by
  unfold doIpcTransfer
  refine ik_bind (qf_lookupIpcBuffer t _ _) fun _ => ?_
  refine ik_threadGet_bind fun σ x hx => ?_
  cases hf : x.tcbFault with
  | none => intro hσ; exact absurd hf (hσ t x hx rfl)
  | some f => exact ikp_of_ik (qf_doFaultTransfer t _ _ _ _) σ

theorem qf_replyUnlinkTcb (t d r : ObjRef) : IK (TP (QF t)) (replyUnlinkTcb (Z := Unit) d r) := by
  unfold replyUnlinkTcb
  refine ik_bind (by tq_auto) fun _ => ik_bind (ik_assert _) fun _ => ik_bind (by tq_auto) fun _ =>
    ik_bind (ik_assert _) fun _ => ik_bind (by tq_auto) fun _ => qf_setThreadState t _ _

/-! ## `send_ipc` of a faulted runnable sender -/

/-- The tail after the receiver's wake: `NO t` kept (the receiver is not `t`). -/
theorem no_wakeTail (t dest : ObjRef) (hne : dest ≠ t) : IK (NO t) (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  refine ik_bind (fg_setThreadState _ _ fun _ _ _ e => absurd e hne) fun _ =>
    ik_bind (fg_getTcbObjRef _ _) fun _ => ik_bind (fg_ifCondRefillUnblockCheck _ _ _) fun _ => fg_possibleSwitchTo _

theorem no_replyPush (t dest r : ObjRef) (d : Bool) (σ : State Unit) :
    ∀ y ∈ (replyPush (Z := Unit) t dest r d σ).1, NO t y.2 := by
  unfold replyPush
  intro y y'
  obtain ⟨z1, -, y'⟩ := y'
  obtain ⟨z2, -, y'⟩ := y'
  obtain ⟨z3, -, y'⟩ := y'
  obtain ⟨z4, hz4, y'⟩ := y'
  have h4 : NO t z4.2 := no_sts t _ (by rfl) hz4
  refine (?_ : IK (NO t) _) _ h4 y y'
  unfold NonDet.when
  split
  · exact ik_bind (fg_bindScReply _ _) fun _ => fg_schedContextDonate _ _
  · exact ik_pure _

theorem no_sendIpcBlocked (t ep : ObjRef) (bd : Badge) (g gr c : Bool) (σ : State Unit) :
    ∀ y ∈ (sendIpcBlocked (Z := Unit) t ep bd g gr c σ).1, NO t y.2 := by
  unfold sendIpcBlocked
  exact no_bind (fun z hz => no_sts t _ (by rfl) hz) fun _ => fg_tcbEpAppend _ _ _

/-- **`send_ipc` (blocking, not call, no donation) of a faulted runnable sender** leaves it not runnable. -/
theorem no_sendIpc (t ep : ObjRef) (bd : Badge) (g gr : Bool) (σ : State Unit) (hσ : TP (QR t) σ) :
    ∀ y ∈ (sendIpc (Z := Unit) true false bd g gr false t ep σ).1, NO t y.2 := by
  unfold sendIpc
  intro y ⟨e, he, hy⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo he
  obtain ⟨ev, σ1⟩ := e
  simp only at hk hs; subst hs
  cases ev with
  | idleEP => exact no_sendIpcBlocked t ep bd g gr false _ y hy
  | sendEP q => exact no_sendIpcBlocked t ep bd g gr false _ y hy
  | recvEP l =>
    cases l with
    | nil => exact hy.elim
    | cons dest q =>
      obtain ⟨z1, hz1, hy⟩ := hy
      have hQ1 : TP (QR t) z1.2 := qr_tcbEpDequeue t dest ep σ1 hσ z1 hz1
      obtain ⟨z2, hz2, hy⟩ := hy
      unfold getThreadState at hz2
      obtain ⟨xd, hxd, rfl⟩ := mem_threadGet hz2
      dsimp only at hy
      have hQF1 : TP (QF t) z1.2 := fun p x hp e => (hQ1 p x hp e).1
      cases hst : xd.tcbState with
      | blockedOnReceive ep' reply dd =>
        have hne : dest ≠ t := by
          intro e; subst e
          have h2 := (hQ1 dest xd hxd rfl).2
          rw [hst] at h2; exact absurd h2 (by simp [runnable])
        rw [hst] at hy
        obtain ⟨z3, hz3, hy⟩ := hy
        rw [Set.mem_singleton_iff.1 hz3] at hy
        obtain ⟨z4, hz4, hy⟩ := hy
        have hQ4 := qf_doIpcTransfer t (some ep) bd g dest z1.2 hQF1 z4 hz4
        obtain ⟨z5, hz5, hy⟩ := hy
        have hQ5 : TP (QF t) z5.2 :=
          (ik_maybeM (fun r => qf_replyUnlinkTcb t dest r) reply) z4.2 hQ4 z5 hz5
        obtain ⟨z6, hz6, hy⟩ := hy
        unfold getTcbObjRef at hz6
        obtain ⟨x6, -, rfl⟩ := mem_threadGet hz6
        obtain ⟨z7, hz7, hy⟩ := hy
        obtain ⟨xt, hxt, rfl⟩ := mem_threadGet hz7
        have hF : xt.tcbFault ≠ none := hQ5 t xt hxt rfl
        dsimp only at hy
        split at hy
        · split at hy
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact no_wakeTail t dest hne z8.2 (no_replyPush t dest _ false _ z8 hz8) y hy
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact no_wakeTail t dest hne z8.2 (no_sts t _ (by rfl) hz8) y hy
        · rename_i hc; exact absurd (Or.inr hF) hc
      | _ => rw [hst] at hy; obtain ⟨_, h, _⟩ := hy; exact h.elim

/-! ## `handle_timeout` -/

theorem mem_isValidTimeoutHandler {t : ObjRef} {σ : State Unit} {y : Bool × State Unit}
    (h : y ∈ (isValidTimeoutHandler (Z := Unit) t σ).1) :
    y.2 = σ ∧ ∃ c, SInvU.capAt σ (getTcbTimeoutHandlerPtr t) = some c ∧ y.1 = isEpCap c := by
  unfold isValidTimeoutHandler at h
  obtain ⟨z1, hz1, h⟩ := h
  rw [Set.mem_singleton_iff.1 hz1] at h
  obtain ⟨z2, hz2, h⟩ := h
  obtain ⟨e2, ec⟩ := SInvU.getCap_capAt hz2
  rw [Set.mem_singleton_iff.1 h]
  exact ⟨e2, z2.1, ec, rfl⟩

/-- **`TmoNR`** (rd8a's remaining fact of 1(d)): no premise. -/
theorem tmoNR : A8.TmoNR := by
  intro s t b ⟨x0, hx0, hr0⟩ w hw
  unfold handleTimeout at hw
  obtain ⟨y1, h1, hw⟩ := hw
  obtain ⟨e1, c1, hc1, hv1⟩ := mem_isValidTimeoutHandler h1
  obtain ⟨y2, h2, hw⟩ := hw
  obtain ⟨hA, rfl⟩ := h2
  obtain ⟨y3, h3, hw⟩ := hw
  rw [Set.mem_singleton_iff.1 h3] at hw
  obtain ⟨y4, h4, hw⟩ := hw
  obtain ⟨cap, s4⟩ := y4
  obtain ⟨e4, hc4⟩ := SInvU.getCap_capAt h4
  dsimp only at e4 hc4 hw ⊢
  have hs4 : s4 = s := by rw [e4]; exact e1
  have hc4' : SInvU.capAt s (getTcbTimeoutHandlerPtr t) = some cap := by rw [← e1]; exact hc4
  rw [hc1] at hc4'
  have hcap : cap = c1 := (Option.some.inj hc4').symm
  have hep : isEpCap cap = true := by rw [hcap, ← hv1]; exact hA
  obtain ⟨y5, h5, hw⟩ := hw
  rw [Set.mem_singleton_iff.1 hw]
  clear hcap hc4' hc4
  cases cap with
  | endpointCap r bd rights =>
    simp only [sendFaultIpc] at h5
    obtain ⟨y6, h6, h5⟩ := h5
    obtain ⟨xf, hxf, e6⟩ := SInv.mem_threadSet h6
    rw [hs4] at hxf; rw [hx0] at hxf; cases hxf
    have hQ6 : TP (QR t) y6.2 := by
      intro p x hp ept; subst ept
      rw [e6] at hp; dsimp only at hp; rw [Function.update_self] at hp
      cases hp
      exact ⟨by simp, hr0⟩
    obtain ⟨y7, h7, h5⟩ := h5
    have := no_sendIpc t _ _ _ _ y6.2 hQ6 y7 h7
    rw [Set.mem_singleton_iff.1 h5]
    exact nrun_of_no this
  | _ => exact absurd hep (by simp [isEpCap])

/-! ## The rd8a tops without `TmoNR` -/

theorem kcall_rdyOff9 (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1,
      A8.SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
      A8.RCA y2.2 ∧ CtR y2.2 ∧ A8.HRC y2.2)
    (hX : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, A8.XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A8.kcall_rdyOff' rep ev σ hEF tmoNR hBody hEvO hAw hX

theorem kentry_rdyOff9 (rep : Bool) (c : Syscall) (σ : State Unit) (h : A8.EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ v ∈ (A8.front w.2).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1, A8.SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        A8.RCA y2.2 ∧ CtR y2.2 ∧ A8.HRC y2.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, A8.XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A8.kentry_rdyOff' rep c σ h tmoNR hW

end

end Fl4Proofs.P3.SInvR.A9
