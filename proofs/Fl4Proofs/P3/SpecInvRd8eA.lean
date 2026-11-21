/-
P3 (DESIGN.md §9), invariant line G1 (rd8e): **`Rdy` across a general
`cancel_ipc`, `complete_signal` and `receive_ipc_blocked`** (spec side only,
outside the JAtZ cone; KENTRY-PLAN rd8d handoff 1, receive_ipc's prefix).

`cancel_ipc t` first clears `t`'s fault. For every thread but a send-blocked
one holding a timeout fault this keeps `BlkR`-ness (or makes `t` non-`BlkR`),
so `rdy_upd` applies and the arm lemmas (rd7's `rs_blockedCancelIpc`,
`cancel_signal`, `reply_remove_tcb`) finish. A send-blocked thread with a
timeout fault becomes `BlkR` with its (possibly unreleased) SC for one
intermediate state; there the whole arm is read off its outcome (`tcbEpDequeue_out`,
two `thread_set`s) and `rdy_of_view` relates the start to the state where `t`
is `Inactive` (`rdy_cancelSend`); `set_thread_state_act` finishes.

* **`rd_cancelIpc t : RdK (cancel_ipc t)`** (no hypothesis), `sv_cancelIpc'`
  (SVK's scheduler view kept), `rq_cancelIpc'` (no thread released).
* `rd_setThreadState_rt` (rd's `rd_setThreadState_r` for `RT`: an unbound
  thread may enter any state), **`rd_receiveIpcBlocked`** (from `RT thread`).
* **`rd_completeSignal`** (the receiver a non-`BlkR` TCB, `RT`): `as_user`,
  the notification write, rd7's `rd_maybeDonateSc_sr`, the sporadic unblock
  check of the receiver's SC.
-/
import Fl4Proofs.P3.SpecInvRd8dC
import Fl4Proofs.P3.IpcRelQ
import Fl4Proofs.P3.IpcStK
import Fl4Proofs.P3.SpecInvCqC2
import Fl4Proofs.P3.SpecInvCqYF2
import Fl4Proofs.P3.SpecInvSbW
import Fl4Proofs.P3.SpecInvSbP
open Classical

namespace Fl4Proofs.P3.SInvR.B8e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `cancel_ipc` -/

/-- The state where a send-blocked `t` was dequeued from `e` and made
`Inactive` (its fault cleared first), from `Rdy` at the start. -/
theorem rdy_cancelSend {σ : State Unit} (hR : Rdy σ) {t e : ObjRef} {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) {ep : Endpoint} (hke : σ.kheap e = some (.endpoint ep))
    (x1 : Tcb) (ep' : Endpoint) (y : Tcb) (hy : y.tcbSchedContext = x.tcbSchedContext)
    (hy2 : y.tcbState = .inactive) :
    Rdy { σ with kheap := Function.update (Function.update (Function.update σ.kheap t (some (.tcb x1)))
      e (some (.endpoint ep'))) t (some (.tcb y)) } := by
  have het : e ≠ t := fun h => by rw [h, hx] at hke; cases hke
  refine rdy_of_view hR (fun u x0 hx0 => ?_) (fun u x' hx' hb hc => ?_) (fun p => ?_) rfl rfl
    (fun d p u hm => Or.inl hm) (fun u h => Or.inl h) (fun u hm => Or.inl hm)
  · by_cases hu : u = t
    · subst hu
      rw [hx] at hx0; cases hx0
      exact ⟨y, by simp, hy⟩
    · have hue : u ≠ e := fun h => by rw [h, hke] at hx0; cases hx0
      exact ⟨x0, by simp [Function.update_of_ne hu, Function.update_of_ne hue, hx0], rfl⟩
  · by_cases hu : u = t
    · subst hu
      have e' : y = x' := by simpa using hx'
      subst e'
      rw [hy2] at hb
      exfalso
      rcases hb with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ <;> cases h
    · by_cases hue : u = e
      · subst hue
        simp [Function.update_of_ne hu] at hx'
      · have hx'' : σ.kheap u = some (.tcb x') := by
          simpa [Function.update_of_ne hu, Function.update_of_ne hue] using hx'
        exact ⟨x', hx'', rfl, hb⟩
  · by_cases hp : p = t
    · subst hp
      simp [hx, SV]
    · by_cases hpe : p = e
      · subst hpe
        simp [Function.update_of_ne hp, hke, SV]
      · simp [Function.update_of_ne hp, Function.update_of_ne hpe]

/-- **`cancel_ipc t`** keeps `Rdy` (any thread, any state). -/
theorem rd_cancelIpc (t : ObjRef) : RdK (cancelIpc (Z := Unit) t) := by
  intro σ hR r hr
  unfold cancelIpc at hr
  obtain ⟨z, hz, hr⟩ := hr
  unfold getThreadState at hz
  obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hz
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain ⟨x2, hx2, e2⟩ := SInv.mem_threadSet hz2
  rw [hx] at hx2; cases hx2
  dsimp only at hr
  by_cases hb : BlkR x.tcbState x.tcbFault ∨ ¬ BlkR x.tcbState none
  · have hR2 : Rdy z2.2 := by
      rw [e2]
      refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h hb' hc => ?_, by rw [hx]; rfl⟩
      · rw [hx] at h; cases h; exact ⟨_, rfl, rfl⟩
      · cases h
        refine ⟨x, hx, rfl, ?_⟩
        rcases hb with hb | hb
        · exact hb
        · exact absurd hb' hb
    have K : ∀ (st : ThreadState) (rp : Option ObjRef),
        r ∈ (blockedCancelIpc (Z := Unit) st t rp z2.2).1 → Rdy r.2 :=
      fun st rp h => (rs_blockedCancelIpc z2.2 st t rp z2.2 ⟨hR2, SVK.SVS.refl _⟩ r h).1
    cases hst : x.tcbState <;> rw [hst] at hr <;> dsimp only at hr
    all_goals first
      | exact K _ _ hr
      | (unfold cancelSignal at hr
         exact ik_bind (rd_tcbNtfnDequeue t _) (fun _ => rd_setThreadState t .inactive trivial) z2.2 hR2 r hr)
      | exact rd_replyRemoveTcb t _ z2.2 hR2 r hr
      | (obtain rfl := Set.mem_singleton_iff.1 hr; exact hR2)
      | (obtain rfl : r = ((), z2.2) := hr; exact hR2)
  · rw [not_or, not_not] at hb
    obtain ⟨hnb, hb0⟩ := hb
    obtain ⟨e, d, hs⟩ : ∃ e d, x.tcbState = .blockedOnSend e d := by
      rcases hb0 with ⟨n, h⟩ | ⟨e, d, h, -⟩ | ⟨e, rp, d, h⟩
      · exact absurd (Or.inl ⟨n, h⟩) hnb
      · exact ⟨e, d, h⟩
      · exact absurd (Or.inr (Or.inr ⟨e, rp, d, h⟩)) hnb
    rw [hs] at hr
    dsimp only at hr
    unfold blockedCancelIpc getBlockingObject at hr
    obtain ⟨z3, hz3, hr⟩ := hr
    obtain rfl : z3 = (e, z2.2) := hz3
    obtain ⟨z4, hz4, hr⟩ := hr
    obtain ⟨ep, ep', hke, -, -, e4⟩ := Sched.tcbEpDequeue_out hz4
    have het : e ≠ t := fun h => by
      rw [h, e2] at hke; simp at hke
    have hke0 : σ.kheap e = some (.endpoint ep) := by
      rw [e2] at hke; simpa [Function.update_of_ne het] using hke
    obtain ⟨z6, hz6, hr⟩ := hr
    obtain ⟨x6, hx6, e6⟩ := SInv.mem_threadSet hz6
    have hx6' : x6 = { x with tcbFault := none } := by
      rw [e4, e2] at hx6
      simp [Function.update_of_ne (Ne.symm het)] at hx6
      exact hx6.symm
    subst hx6'
    refine rd_setThreadStateAct t z6.2 ?_ r hr
    rw [e6, e4, e2]
    exact rdy_cancelSend hR hx hke0 _ ep' _ rfl rfl

theorem sv_cancelIpc' (t : ObjRef) : SVK.SVM (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc blockedCancelIpc cancelSignal replyRemoveTcb getBlockingObject
  sv_auto
  all_goals first
    | exact sv_tcbEpDequeue _ _
    | exact sv_tcbNtfnDequeue _ _
    | exact SVK.sv_replyUnlinkTcb _ _

theorem rq_cancelIpc' (t : ObjRef) : RelQ.RQ (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc blockedCancelIpc cancelSignal replyRemoveTcb replyUnlinkTcb getBlockingObject
    tcbEpDequeue tcbNtfnDequeue
  rq_auto

/-! ## `set_thread_state` of an `RT` thread; `receive_ipc_blocked` -/

/-- **`set_thread_state t ts`** for `t` `RdyT` when bound (an unbound thread
may enter any state). -/
theorem rd_setThreadState_rt (t : ObjRef) (ts : ThreadState) (σ : State Unit) (hT : RT σ t) :
    IKp Rdy σ (setThreadState (Z := Unit) t ts) := by
  intro hR r hr
  by_cases hb : ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c
  · obtain ⟨x, c, hx, hc⟩ := hb
    exact rd_setThreadState_r t ts σ (hT x c hx hc) hR r hr
  · unfold setThreadState at hr
    obtain ⟨z, hz, hr⟩ := hr
    obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hz
    have hn : x.tcbSchedContext = none := by
      cases h : x.tcbSchedContext with
      | none => rfl
      | some c => exact absurd ⟨x, c, hx, h⟩ hb
    refine rd_setThreadStateAct t z.2 ?_ r hr
    rw [e]
    refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h _ hc => ?_, by rw [hx]; rfl⟩
    · rw [hx] at h; cases h; exact ⟨_, rfl, rfl⟩
    · cases h; exact absurd hn hc

/-- **`receive_ipc_blocked`** from `RT thread`. -/
theorem rd_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef)
    (σ : State Unit) (hT : RT σ thread) :
    IKp Rdy σ (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked
  cases isBlocking with
  | false => exact ikp_of_ik (rd_doNbrecvFailedTransfer thread) σ
  | true =>
    rw [if_pos (rfl : true = true)]
    refine ikp_bind (rd_setThreadState_rt thread _ σ hT) fun _ => ?_
    exact ik_bind (ik_maybeM (fun r => rd_setReplyObjRef' _ r _) reply) fun _ => rd_tcbEpAppend thread epptr true

/-! ## `complete_signal` -/

theorem tv_setNotification {V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)} (p : ObjRef)
    (n : Notification) : TVK V (setNotification (Z := Unit) p n) := by
  show TVK V (setSimpleKo (Z := Unit) KernelObject.notification p n)
  unfold setSimpleKo; tv_auto

/-- **`complete_signal ntfn tptr`** for a non-`BlkR` receiver, `RdyT` when bound. -/
theorem rd_completeSignal (ntfnptr tptr : ObjRef) (σ : State Unit) (hR : Rdy σ) {x : Tcb}
    (hx : σ.kheap tptr = some (.tcb x)) (hnb : ¬ BlkR x.tcbState x.tcbFault) (hT : RT σ tptr)
    {r : Unit × State Unit} (hr : r ∈ (completeSignal (Z := Unit) ntfnptr tptr σ).1) : Rdy r.2 := by
  unfold completeSignal at hr
  obtain ⟨⟨ntfn, s1⟩, hz1, hr⟩ := hr
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  dsimp only at hr
  cases hn : ntfn.ntfnObj
  case activeNtfn badge =>
    rw [hn] at hr
    dsimp only at hr
    obtain ⟨z2, hz2, hr⟩ := hr
    have e2 : Rdy z2.2 := rd_asUser tptr _ σ hR z2 hz2
    have v2 : SVK.SVS σ z2.2 := SVK.sv_asUser' tptr _ σ z2 hz2
    have t2 : TV (TVv σ) z2.2 := tv_asUser tptr _ σ rfl z2 hz2
    obtain ⟨z3, hz3, hr⟩ := hr
    have e3 : Rdy z3.2 := rd_setSimpleKo _ _ _ z2.2 e2 z3 hz3
    have v3 : SVK.SVS z2.2 z3.2 :=
      SVK.sv_setSimpleKo' KernelObject.notification _ _ (SVK.so_ntfn _) z2.2 z3 hz3
    have t3 : TV (TVv σ) z3.2 := tv_setNotification _ _ z2.2 t2 z3 hz3
    have hx3 : ∃ x3, z3.2.kheap tptr = some (.tcb x3) ∧ x3.tcbState = x.tcbState ∧
        x3.tcbFault = x.tcbFault := by
      have ev := congrFun t3 tptr
      unfold TVv at ev
      rw [hx] at ev
      cases hk : z3.2.kheap tptr with
      | none => rw [hk] at ev; simp [B8c.tcbV] at ev
      | some o =>
        rw [hk] at ev
        cases o with
        | tcb x3 =>
          simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
          exact ⟨x3, rfl, ev.1, ev.2.1⟩
        | _ => simp [B8c.tcbV] at ev
    obtain ⟨x3, hx3, es, ef⟩ := hx3
    have hT3 : RT z3.2 tptr := rT_svs hT (v2.trans v3)
    obtain ⟨z4, hz4, hr⟩ := hr
    obtain ⟨e4, -⟩ := rd_maybeDonateSc_sr tptr ntfnptr z3.2 e3 hx3 (by rw [es, ef]; exact hnb)
      (fun c hc => hT3 x3 c hx3 hc) hz4
    obtain ⟨z5, hz5, hr⟩ := hr
    obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    cases hsc : x5.tcbSchedContext with
    | none =>
      rw [hsc] at hr
      obtain rfl := Set.mem_singleton_iff.1 hr
      exact e4
    | some scp =>
      rw [hsc] at hr
      dsimp only [NonDet.maybeM] at hr
      obtain ⟨z6, hz6, hr⟩ := hr
      obtain ⟨⟨n6, hk6⟩, e6⟩ := SInvI.mem_getSchedContext_vi hz6
      obtain ⟨w1, w2⟩ := z6
      simp only at e6 hk6 hr
      subst w2
      unfold NonDet.when at hr
      split at hr
      · obtain ⟨⟨a7, s7⟩, hz7, hr⟩ := hr
        have e7 : s7 = z4.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz7
        subst s7
        dsimp only at hr
        rw [Notif.nd_gets_bind] at hr
        try dsimp only at hr
        split at hr
        · exact (rd_refillUnblockCheck e4 hk6 hr).1
        · obtain rfl := Set.mem_singleton_iff.1 hr
          exact e4
      · obtain rfl := Set.mem_singleton_iff.1 hr
        exact e4
  all_goals (rw [hn] at hr; exact hr.elim)

end

end Fl4Proofs.P3.SInvR.B8e
