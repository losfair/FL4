/-
P3 (DESIGN.md §9), invariant line G1 (rd14a, KENTRY-PLAN rd13a handoff 1-2):
**the receive tail anchored at the invocation outcome** (spec side only).

rd13a's `RecvA` asked, at an `ok` first-phase invocation outcome `t`, for
rd11a's frame `KP σ0 t` from the body start σ0 with ct still bound to cur_sc,
or (the open disjunct) the receive tail's `CB → SS4` directly. Here the tail
is anchored at `t` itself (rd11a's frame `KP t ·`), so it needs only `SS4 t`
(which rd12b's shell gives at every `ok` outcome from `InvR`, with ctq's `CB`)
and carried facts (`Rdy`, `ScInv`, ct not blocked, `RT ct`); ct may be unbound (passive server after
ReplyRecv's reply, NBSendRecv's donation) or bound to any SC.

* `B0R σ0` (under resume σ0's ct is a TCB bound to cur_sc: from `HRC σ0`);
  `nores'`, `kp_ruc'`, `kp_ifCondA'`, `kp_ifCondT'`, `kp_replyPush'`,
  `kp_recvSender'`: rd12a's leaves with `B0R` in place of `B0` (resume
  case: rd12a's lemma; otherwise CW alone).
* `KT σ0 s := KP σ0 s ∧ (SR ct s ∨ NRun ct s)` (the end of a receive arm),
  `ctR_sr`, `kp_bind'`, **`ss4_of_kt`** (`SS4 σ0 ∧ KT σ0 s ⇒ SS4 s`).
* RT / SR leaves: `rt_kt`, `sr_of_rt`, `rt_uk`, `mb_ruc`, `sr_ruc`,
  `rt_maybeReturnSc`, **`rt_recvSender`** (rd12a's `ce_recvSender` walk
  carrying rd8d's `RT` of the receiver).
* **`kt_completeSignal`** / **`kt_receiveSignal`**: ct unbound
  (maybe_donate_sc donates the notification's SC, then
  sched_context_resume: rd's `rd_maybeDonateSc_sr` gives `SR ct`; no resume
  since ct is unbound) or bound (no donation; the sporadic unblock check of
  ct's SC keeps `SR` by `sr_ruc` / rd9's `sr_ifCond`).
* `kt_rcvBlocked`, `kt_recvTail`, `kt_recvRest`, **`kt_receiveIpc`**
  (`RcvW` carried, RT of ct along the walk).
* `RcvW` (rd8e's `RcvS` without `Simple` / `T1`: `Simple` is false after a
  send half that woke a thread — possible_switch_to sets `switch_thread`),
  `rcvW_cancelIpc` / `rcvW_when`, `rdyT_donate` / `rt_replyPush` (rd8d's
  donation, `RT` half only: needs `ScFwd`, not `Rdy` / `T1` / `Simple`).
* **`ss4_handleRecvT`**: from `SS4 t`, `RcvW t ct`, ctq's `EB true t`,
  `NQ [ct] t`, ct ≠ idle: every `handle_recv` outcome has `SS4`.
-/
import Fl4Proofs.P3.SpecInvRd13aA
open Classical

namespace Fl4Proofs.P3.SInvR.A14a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.A11 Fl4Proofs.P3.SInvR.A12a

noncomputable section

set_option maxHeartbeats 1000000

/-! ## No resume once ct is unbound, from the anchor's `HRC` -/

/-- Under resume, the anchor's ct is a TCB bound to cur_sc. -/
abbrev B0R (σ0 : State Unit) : Prop := σ0.schedulerAction = .resumeCurThread → B0 σ0

theorem nores' {σ0 s : State Unit} (h0 : B0R σ0) (hK : KP σ0 s) {x : Tcb}
    (hx : s.kheap σ0.curThread = some (.tcb x)) (hn : x.tcbSchedContext = none) :
    s.schedulerAction ≠ .resumeCurThread := fun hr =>
  nores_of_unbound (h0 (hK.2.1.2 hr)) hK hx hn hr

theorem kp_ruc' {σ0 s : State Unit} (h0 : B0R σ0) (hK : KP σ0 s) {p : ObjRef} (hp : p ≠ σ0.curSc)
    {y0 : SchedContext} {n : Nat} (hk : s.kheap p = some (.schedContext y0 n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p s).1) : KP σ0 r.2 := by
  by_cases hres : s.schedulerAction = .resumeCurThread
  · exact kp_ruc (h0 (hK.2.1.2 hres)) hK hp hk hr
  · exact kp_nores hK hres (cfk_refillUnblockCheck' p s r hr)
      (A8.cp_refillUnblockCheck_ne p (c := s.curSc) (by rw [kp_curSc hK]; exact hp) s s
        ⟨rfl, A8.CW.refl _ _⟩ r hr).2

/-- The assert-form unblock check keeps `KP` (rd12a's `kp_ifCondA` with `B0R`). -/
theorem kp_ifCondA' (o : Option ObjRef) {σ0 : State Unit} (h0 : B0R σ0) :
    IK (KP σ0) (ifCondRefillUnblockCheck (Z := Unit) o (some false) (some true)) := by
  intro s hs y hy
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hy
  cases o with
  | none =>
    obtain rfl : y = ((), s) := hy
    exact hs
  | some p =>
    dsimp only at hy
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hy
    subst w2
    rw [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hy
    unfold NonDet.when at hy
    split_ifs at hy with h1 h2
    · have h2' : p ≠ s.curSc := by first | exact h2 rfl | exact h2
      exact kp_ruc' h0 hs (fun e => h2' (e.trans (kp_curSc hs).symm)) hk hy
    all_goals (obtain rfl : y = ((), _) := hy; exact hs)

/-- The test-form unblock check (receive_signal's) keeps `KP`. -/
theorem kp_ifCondT' (o : Option ObjRef) {σ0 : State Unit} (h0 : B0R σ0) :
    IK (KP σ0) (ifCondRefillUnblockCheck (Z := Unit) o (some false) (some false)) := by
  intro s hs y hy
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hy
  cases o with
  | none =>
    obtain rfl : y = ((), s) := hy
    exact hs
  | some p =>
    dsimp only at hy
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hy
    subst w2
    rw [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hy
    unfold NonDet.when at hy
    split_ifs at hy with h1 h2
    · have h2' : p ≠ s.curSc := by
        first | exact h1.2 rfl | exact h1.2 | exact h2 rfl | exact h2
      exact kp_ruc' h0 hs (fun e => h2' (e.trans (kp_curSc hs).symm)) hk hy
    all_goals (obtain rfl : y = ((), _) := hy; exact hs)

theorem kp_replyPush' {σ0 : State Unit} (h0 : B0R σ0) (a r : ObjRef) (d : Bool) (s : State Unit)
    (hK : KP σ0 s) {y : Unit × State Unit} (hy : y ∈ (replyPush (Z := Unit) a σ0.curThread r d s).1) :
    KP σ0 y.2 := by
  by_cases hr : s.schedulerAction = .resumeCurThread
  · exact kp_replyPush (h0 (hK.2.1.2 hr)) a r d s hK hy
  · exact kp_nores hK hr (cfk_replyPush' a σ0.curThread r d s y hy)
      (cw_of_cp (A11b.cp_replyPush a σ0.curThread r d) hy)

/-- **`KP` across `receive_ipc`'s sender arm** (rd12a's `kp_recvSender` with `B0R`). -/
theorem kp_recvSender' {σ0 : State Unit} (h0 : B0R σ0) (sender epptr : ObjRef) (reply : Option ObjRef)
    (data : SenderPayload) (s : State Unit) (hK : KP σ0 s) (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) sender (some epptr) data.senderBadge data.senderCanGrant σ0.curThread
      let scPtr ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scPtr
      let fault ← threadGet (Z := Unit) Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush (Z := Unit) sender σ0.curThread (the reply) donate
        else setThreadState (Z := Unit) sender .inactive
      else do
        setThreadState (Z := Unit) sender .running
        possibleSwitchTo (Z := Unit) sender) s).1) : KP σ0 y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have k3 : KP σ0 z3.2 := ik_kp (SVK.sv_doIpcTransfer' _ _ _ _ _) (cfk_doIpcTransfer' _ _ _ _ _) σ0 s hK z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain ⟨x4, -, rfl⟩ := SInvQ.q1_mem_threadGet h4
  obtain ⟨z5, h5, hy⟩ := hy
  have k5 : KP σ0 z5.2 := kp_ifCondA' _ h0 z3.2 k3 z5 h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, -, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      exact kp_replyPush' h0 _ _ _ z5.2 k5 hy
    · exact ik_kp (SVK.sv_setThreadState' _ _) (cfk_setThreadState' _ _) σ0 z5.2 k5 y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    have k7 : KP σ0 z7.2 := ik_kp (SVK.sv_setThreadState' _ _) (cfk_setThreadState' _ _) σ0 z5.2 k5 z7 h7
    exact kp_possibleSwitchTo _ σ0 z7.2 k7 y hy

/-! ## The end of a receive arm -/

/-- The end of a receive arm, anchored at σ0: rd11a's frame, and ct `SR`
(released when schedulable) or not runnable. -/
abbrev KT (σ0 s : State Unit) : Prop := KP σ0 s ∧ (SR s.curThread s ∨ A8.NRun s.curThread s)

theorem ctR_sr {s : State Unit} (h : SR s.curThread s) : CtR s := by
  intro x hx hrun hA hn
  obtain ⟨x', c, y, n, hx', hc, hy, ha⟩ := hA
  rw [hx] at hx'; cases hx'
  exact h (Sched.schedulable_of hx hc hrun hy ha hn)

theorem kp_bind' {σ0 s : State Unit} (h0 : B0R σ0) (hK : KP σ0 s) (hr : s.schedulerAction = .resumeCurThread) :
    ∃ x, s.kheap s.curThread = some (.tcb x) ∧ x.tcbSchedContext = some s.curSc := by
  obtain ⟨xt, hct, hb⟩ := h0 (hK.2.1.2 hr)
  have e := (hK.2.2 hr).1
  rw [hct] at e
  simp only [SVK.sv, hb] at e
  obtain ⟨x, hx, hxb⟩ := SVK.sv_tcb e
  rw [kp_curThread hK, kp_curSc hK]
  exact ⟨x, hx, hxb⟩

/-- **`SS4` at the end of a receive arm** from `SS4` at the anchor. -/
theorem ss4_of_kt {σ0 s : State Unit} (hS4 : A10.SS4 σ0) (h0 : B0R σ0) (hni : σ0.curThread ≠ σ0.idleThread)
    (hK : KT σ0 s) : A10.SS4 s := by
  refine ⟨os_frame hS4.1 ⟨hK.1.1, fun y n hy => ?_, hK.1.2.1.2⟩, fun hr _ => ?_, hK.2.elim ctR_sr ctR_nrun,
    fun hr x hx => ?_⟩
  · rw [kp_curSc hK.1] at hy; exact hK.1.2.1.1 y n hy
  · have hr0 := hK.1.2.1.2 hr
    obtain ⟨x, hx, hxb⟩ := kp_bind' h0 hK.1 hr
    obtain ⟨xa, c0, z, n, hxa, hca, hkz, hact⟩ := hS4.2.1 hr0 hni
    obtain ⟨xt, hct, hb⟩ := h0 hr0
    rw [hct] at hxa; cases hxa
    rw [hb] at hca; cases hca
    have e := (hK.1.2.2 hr).2
    rw [hkz] at e
    obtain ⟨z', hz', -, hm, -⟩ := SVK.sv_sc (o := s.kheap σ0.curSc) e
    refine ⟨x, s.curSc, z', n, hx, hxb, by rw [kp_curSc hK.1]; exact hz', ?_⟩
    simp only [scActive, hm]; exact hact
  · obtain ⟨x', hx', hxb⟩ := kp_bind' h0 hK.1 hr
    rw [hx] at hx'; cases hx'; exact hxb

/-! ## RT / SR leaves -/

theorem rt_kt {s s' : State Unit} {t : ObjRef} (h : B8d.RT s t) (hk : s'.kheap = s.kheap)
    (ht : s'.curTime = s.curTime) : B8d.RT s' t := by
  intro x c hx hc
  rw [hk] at hx
  obtain ⟨x', c', y, n, h1, h2, h3, h4, h5⟩ := h x c hx hc
  exact ⟨x', c', y, n, by rw [hk]; exact h1, h2, by rw [hk]; exact h3, h4, by rw [ht]; exact h5⟩

theorem sr_of_rt {s : State Unit} {t : ObjRef} (h : B8d.RT s t) : SR t s := fun hs => by
  obtain ⟨x, c, -, -, hx, hc, -⟩ := Sched.schedulable_inv hs
  exact h x c hx hc

theorem rt_uk {s s' : State Unit} {t : ObjRef} (h : B8d.RT s t) (hU : UK s s') : B8d.RT s' t :=
  fun x c hx hc => hU.2.1 t (h x c (hU.2.2 t x hx) hc)

theorem mb_ruc (p : ObjRef) (K : ObjRef → Option KernelObject) :
    IK (A9.MB K) (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead
    updateRefillHd isRoundRobin getRefillHead
  repeat' (first | (refine A9.mb_updSc _ _ ?_ K; intro _; rfl) | ik_step0 | ik_unfold)

/-- `refill_unblock_check p` keeps `SR t` (rd9's `sr_ifCond` for the bare check). -/
theorem sr_ruc (p t : ObjRef) (s : State Unit) (hR : Rdy s) {y0 : SchedContext} {n0 : Nat}
    (hk : s.kheap p = some (.schedContext y0 n0)) (h : SR t s) :
    ∀ y ∈ (refillUnblockCheck (Z := Unit) p s).1, SR t y.2 := by
  intro y hy hsch
  obtain ⟨-, hfw, hbw⟩ := rd_refillUnblockCheck hR hk hy
  obtain ⟨x, c, z, n, hx, hc, hrun, hz, ha, hq⟩ := A9.of_sched hsch
  have hq0 : t ∉ s.releaseQueue := by
    rw [← A9.rq_walk_refillUnblockCheck p s.releaseQueue s rfl y hy]; exact hq
  obtain ⟨z0, hz0, hm⟩ := mb_ruc p s.kheap s (fun q z n h => ⟨z, h, rfl⟩) y hy c z n hz
  have ha0 : scActive z0 = true := by simp only [scActive] at ha ⊢; rw [hm]; exact ha
  exact hfw t (h (Sched.schedulable_of (hbw t x hx) hc hrun hz0 ha0 hq0))

/-- **`maybe_return_sc n t`** keeps `RT t` (it only unbinds `t`). -/
theorem rt_maybeReturnSc (n t : ObjRef) (s : State Unit) (hT : B8d.RT s t) {y : Unit × State Unit}
    (hy : y ∈ (maybeReturnSc (Z := Unit) n t s).1) : B8d.RT y.2 t := by
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
    intro x c hx hc
    rw [hk, ht5] at hx
    cases hx
    simp [tcbSchedContextUpdate] at hc
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hT

/-! ## The receiver's facts without `Simple` -/

/-- rd8e's `RcvS` without `Simple` and `T1`: after a send half that woke a
thread the action can be `switch_thread` (possible_switch_to), so `Simple` is
false there; only "the receiver is not the switch target" (ctq's `NP ct`) is
used. -/
def RcvW (s : State Unit) (thread : ObjRef) : Prop :=
  Rdy s ∧ SInvB.ScInv s ∧ s.schedulerAction ≠ .switchThread thread ∧ (∀ d p, thread ∉ s.readyQueues d p) ∧
    thread ∉ s.releaseQueue ∧ (∃ x, s.kheap thread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧
    B8d.RT s thread

/-- The receiver's facts across `cancel_ipc` of another thread (rd8e's
`rcvS_cancelIpc` without `Simple`). -/
theorem rcvW_cancelIpc (u thread : ObjRef) (s : State Unit) (hS : RcvW s thread) (hRB : SInvQ.RBk true s)
    (hct : s.curThread = thread) (hut : u ≠ thread) {y : Unit × State Unit}
    (hy : y ∈ (cancelIpc (Z := Unit) u s).1) : RcvW y.2 thread := by
  obtain ⟨hR, hI, hA, -, hrq, ⟨x, hx, hnb⟩, hT⟩ := hS
  have hB := SInvQ.rb_cancelIpc u s hRB y hy
  have hO := StK.st_cancelIpc (t0 := u) s y hy
  have hV := B8e.sv_cancelIpc' u s y hy
  have hct' : y.2.curThread = thread := hO.2.trans hct
  have e := hV.1 thread
  rw [hx] at e
  obtain ⟨x', hx', -⟩ := SVK.sv_tcb (o := y.2.kheap thread) e
  obtain ⟨y0, hy0, es⟩ := hO.1 thread x' (Ne.symm hut) hx'
  rw [hx] at hy0; cases hy0
  refine ⟨B8e.rd_cancelIpc u s hR y hy, SInvB.sik_of_sbk (fun _ => SInvB.sb_cancelIpc u) s hI y hy,
    SInvQ.P12.nsw_cancelIpc thread u s hA y hy, fun d p => ?_,
    fun h => hrq (B8e.rq_cancelIpc' u s y hy thread h), ⟨x', hx', fun f => by rw [es]; exact hnb f⟩,
    B8d.rT_svs hT hV⟩
  have hq := ((hB.1.2.1 rfl).1 d p)
  rw [hct'] at hq
  exact hq

theorem rcvW_when (tptr : Option ObjRef) (thread : ObjRef) (σ : State Unit) (hS : RcvW σ thread)
    (hRB : SInvQ.RBk true σ) (hct : σ.curThread = thread) {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (tptr ≠ none ∧ the tptr ≠ thread) (cancelIpc (Z := Unit) (the tptr)) σ).1) :
    RcvW z.2 thread := by
  unfold NonDet.when at hz
  split at hz
  · rename_i hc
    exact rcvW_cancelIpc _ thread σ hS hRB hct hc.2 hz
  · obtain rfl := Set.mem_singleton_iff.1 hz
    exact hS

/-- **`sched_context_donate p t`** of a released SC to an unbound `t`: `t`
ends `RdyT` (rd8d's `rd_schedContextDonate_relT`, its `RdyT` half: only
`ScFwd` is needed). -/
theorem rdyT_donate (p t : ObjRef) (σ : State Unit) (hF : SInvB.ScFwd σ) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hn : x.tcbSchedContext = none)
    (hrel : ∀ y n, σ.kheap p = some (.schedContext y n) →
      scActive y = true ∧ refillReady σ.curTime (refillHd y) = true)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) : RdyT r.2 t := by
  unfold schedContextDonate at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨e, sc, n, hk, hv⟩ := SInvQ.cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  obtain ⟨w, hw, hr⟩ := hr
  have hW : w.2.kheap p = some (.schedContext sc n) ∧ w.2.kheap t = some (.tcb x) ∧
      w.2.curTime = σ.curTime := by
    unfold NonDet.when at hw
    split at hw
    · obtain ⟨a, ha, hw⟩ := hw
      obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
      obtain ⟨u, a2⟩ := a
      simp only at ha1 ha2; subst a2
      have hsu : sc.scTcb = some u := hv.symm.trans ha1
      obtain ⟨xu, hxu, hxup⟩ := hF p sc n u hk hsu
      have hup : u ≠ p := by rintro rfl; rw [hk] at hxu; cases hxu
      have hut : u ≠ t := by rintro rfl; rw [hx] at hxu; cases hxu; rw [hn] at hxup; cases hxup
      obtain ⟨v, hv1, hw⟩ := hw
      obtain ⟨xv, -, ev⟩ := SInvQ.q1_tsa_out hv1
      obtain ⟨u', hu', hw⟩ := hw
      obtain ⟨ek, et, -, er⟩ := mem_tcbReleaseRemove hu'
      obtain ⟨s, hs, hw⟩ := hw
      obtain ⟨xs, -, es⟩ := SInv.mem_threadSet hs
      have hkw := B8c.kt_testReschedule s.2.kheap s.2.curTime u s.2 ⟨rfl, rfl⟩ w hw
      refine ⟨?_, ?_, ?_⟩
      · rw [hkw.1, es]
        show Function.update u'.2.kheap u _ p = _
        rw [Function.update_of_ne (Ne.symm hup), ek, ev]; exact hk
      · rw [hkw.1, es]
        show Function.update u'.2.kheap u _ t = _
        rw [Function.update_of_ne (Ne.symm hut), ek, ev]; exact hx
      · rw [hkw.2, es]
        show u'.2.curTime = _
        rw [et, ev]
    · obtain rfl := Set.mem_singleton_iff.1 hw
      exact ⟨hk, hx, rfl⟩
  obtain ⟨hkw, hxw, htw⟩ := hW
  obtain ⟨w2, hw2, hr⟩ := hr
  obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext hw2
  rw [hkw] at hk2; cases hk2
  have hpt : p ≠ t := fun e => by rw [e, hx] at hk; cases hk
  have hx2 : w2.2.kheap t = some (.tcb x) := by rw [e2]; simp [Function.update_of_ne (Ne.symm hpt), hxw]
  have hkp2 : w2.2.kheap p = some (.schedContext (scTcbUpdate (fun _ => some t) sc) n) := by rw [e2]; simp
  have ht2 : w2.2.curTime = σ.curTime := by rw [e2]; exact htw
  obtain ⟨x3, hx3, e3⟩ := SInv.mem_threadSet hr
  rw [hx2] at hx3; cases hx3
  obtain ⟨hya, hyr⟩ := hrel sc n hk
  rw [e3]
  refine ⟨_, p, scTcbUpdate (fun _ => some t) sc, n, Function.update_self .., rfl, ?_, hya, ?_⟩
  · show Function.update w2.2.kheap t _ p = _
    rw [Function.update_of_ne hpt, hkp2]
  · show refillReady w2.2.curTime _ = true
    rw [ht2]; exact hyr

/-- **`reply_push caller callee`** keeps `RT callee` (rd8d's `rd_replyPush_d`,
its `RT` half: no `Rdy`, `T1` or `Simple`). -/
theorem rt_replyPush (caller callee rp : ObjRef) (cd : Bool) (s : State Unit) (hF : SInvB.ScFwd s)
    (hc : cd = true → B8d.RT s caller) (hT : B8d.RT s callee) {y : Unit × State Unit}
    (hy : y ∈ (replyPush (Z := Unit) caller callee rp cd s).1) : B8d.RT y.2 callee := by
  unfold replyPush at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨xc, hxc, rfl⟩ := SInvQ.q1_mem_threadGet hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨xe, hxe, rfl⟩ := SInvQ.q1_mem_threadGet hz2
  dsimp only at hy
  obtain ⟨z3, hz3, hy⟩ := hy
  have v3 : SVK.SVS s z3.2 := B8d.sv_setReplyObjRef' _ _ _ s z3 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have v4 : SVK.SVS s z4.2 := v3.trans (SVK.sv_setThreadState' caller _ z3.2 z4 hz4)
  unfold NonDet.when at hy
  split at hy
  · rename_i hg
    obtain ⟨c, hcc⟩ := Option.ne_none_iff_exists'.mp hg.1
    rw [hcc] at hy
    obtain ⟨z5, hz5, hy⟩ := hy
    have v5 : SVK.SVS s z5.2 := v4.trans (SVK.sv_bindScReply' c rp z4.2 z5 hz5)
    have hxe5 := v5.1 callee
    rw [hxe] at hxe5
    obtain ⟨xe5, hk5, hb5⟩ := SVK.sv_tcb (o := z5.2.kheap callee) hxe5
    have hxc5 := v5.1 caller
    rw [hxc] at hxc5
    obtain ⟨xc5, hkc5, hbc5⟩ := SVK.sv_tcb (o := z5.2.kheap caller) hxc5
    exact B8d.rT_of_rdyT (rdyT_donate c callee z5.2 (fwd_svs hF v5) hk5 (hb5.trans hg.2.1)
      (B8d.rel_of_rdyT (rdyT_svs (hc hg.2.2 xc c hxc hcc) v5) hkc5 (hbc5.trans hcc)) hy)
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact B8d.rT_svs hT v4

/-- **`receive_ipc`'s sender arm** (rd12a's `ce_recvSender` walk) from the
dequeue state carries rd8d's `RT` of the receiver. -/
theorem rt_recvSender (sender thread epptr e : ObjRef) (reply : Option ObjRef) (data : SenderPayload)
    (s : State Unit) (hs : Rdy s) (hF : SInvB.ScFwd s)
    {x : Tcb} (hx : s.kheap sender = some (.tcb x)) (hxs : x.tcbState = .blockedOnSend e data)
    (hT : B8d.RT s thread) (y : Unit × State Unit)
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
        possibleSwitchTo (Z := Unit) sender) s).1) : B8d.RT y.2 thread := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer sender (some epptr) _ _ thread s hs z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' sender (some epptr) _ _ thread s z3 h3
  have t3 : B8d.TV (B8d.TVv s) z3.2 := B8d.tv_doIpcTransfer sender (some epptr) _ _ thread s rfl z3 h3
  have T3 : B8d.RT z3.2 thread := B8d.rT_svs hT v3
  have hx3 : ∃ x3, z3.2.kheap sender = some (.tcb x3) ∧ x3.tcbState = .blockedOnSend e data := by
    have ev := congrFun t3 sender
    unfold B8d.TVv at ev
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
  have U5 := rd_ifCond x4.tcbSchedContext (some false) (some true) z3.2 e3 h5
  have e5 : Rdy z5.2 := U5.1
  have f5 := B8d.sf_ifCond x4.tcbSchedContext (some false) (some true) z3.2 h5
  have hF5 := f5.2.1 (fwd_svs hF v3)
  have hx5 := f5.2.2 sender x3 hx3
  have T5 : B8d.RT z5.2 thread := rt_uk T3 U5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
  rw [hx5] at hx6
  cases hx6
  dsimp only at hy
  have hRT : (∀ b, x3.tcbFault ≠ some (.timeout b)) → B8d.RT z5.2 sender := fun hnt x' c hx' hc => by
    rw [hx5] at hx'; cases hx'
    exact e5.2.2.1 sender x3 c hx5 (Or.inr (Or.inl ⟨e, data, hxs3, hnt⟩)) hc
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      refine rt_replyPush sender thread _ _ z5.2 hF5 (fun hd => hRT fun b hb => ?_) T5 hy
      have hd' := of_decide_eq_true hd
      apply hd'.2
      rw [hb]; rfl
    · exact B8d.rT_svs T5 (SVK.sv_setThreadState' sender .inactive z5.2 y hy)
  · obtain ⟨z7, h7, hy⟩ := hy
    have T7 := B8d.rT_svs T5 (SVK.sv_setThreadState' sender .running z5.2 z7 h7)
    obtain ⟨ek, et, -, -⟩ := ktc_possibleSwitchTo z7.2.kheap z7.2.curTime z7.2.releaseQueue z7.2.curThread sender z7.2
      ⟨rfl, rfl, rfl, rfl⟩ y hy
    exact rt_kt T7 ek et

/-! ## `complete_signal` / `receive_signal` of ct, any binding -/

/-- The common prefix: the badge write and the notification write keep `KP`,
`Rdy`, `RT ct` and ct's state / fault. -/
theorem pre_sig (σ0 : State Unit) {s : State Unit} (hK : KP σ0 s) (hR : Rdy s) {x : Tcb}
    (hx : s.kheap σ0.curThread = some (.tcb x)) (hT : B8d.RT s σ0.curThread)
    {z3 : Unit × State Unit} {u : UserMonad Unit} (h3 : z3 ∈ (asUser (Z := Unit) σ0.curThread u s).1)
    {np : ObjRef} {nt : Notification} {z4 : Unit × State Unit}
    (h4 : z4 ∈ (setNotification (Z := Unit) np nt z3.2).1) :
    KP σ0 z4.2 ∧ Rdy z4.2 ∧ B8d.RT z4.2 σ0.curThread ∧
      ∃ x4, z4.2.kheap σ0.curThread = some (.tcb x4) ∧ x4.tcbState = x.tcbState ∧ x4.tcbFault = x.tcbFault := by
  have v3 := SVK.sv_asUser' _ _ s z3 h3
  have c3 : cfS z3.2 = cfS s := cfk_asUser' _ _ s z3 h3
  have r3 : Rdy z3.2 := rd_asUser _ _ s hR z3 h3
  have t3 : B8d.TV (B8d.TVv s) z3.2 := B8d.tv_asUser _ _ s rfl z3 h3
  have v4 : SVK.SVS z3.2 z4.2 := by refine (?_ : SVK.SVM _) z3.2 z4 h4; sv_auto
  have c4 : cfS z4.2 = cfS z3.2 := by refine (?_ : CFK _) z3.2 z4 h4; cfk_auto
  have r4 : Rdy z4.2 := rd_setSimpleKo _ _ _ z3.2 r3 z4 h4
  have t4 : B8d.TV (B8d.TVv s) z4.2 := B8e.tv_setNotification _ _ z3.2 t3 z4 h4
  have v34 := v3.trans v4
  refine ⟨kp_step hK (c4.trans c3) (A8.cw_of_svs v34) fun _ => ⟨v34.1 _, v34.1 _⟩, r4, B8d.rT_svs hT v34, ?_⟩
  have ev := congrFun t4 σ0.curThread
  unfold B8d.TVv at ev
  rw [hx] at ev
  cases hk : z4.2.kheap σ0.curThread with
  | none => rw [hk] at ev; simp [B8c.tcbV] at ev
  | some o =>
    rw [hk] at ev
    cases o with
    | tcb x4 =>
      simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
      exact ⟨x4, rfl, ev.1, ev.2.1⟩
    | _ => simp [B8c.tcbV] at ev

/-- `maybe_donate_sc ct n`: `KP` (no donation to a bound ct; an unbound ct rules
out resume), `Rdy` and `SR ct` (rd's `rd_maybeDonateSc_sr`). -/
theorem kt_maybeDonateSc (σ0 : State Unit) (h0 : B0R σ0) (n : ObjRef) (s : State Unit) (hK : KP σ0 s)
    (hR : Rdy s) {x : Tcb} (hx : s.kheap σ0.curThread = some (.tcb x)) (hnb : ¬ BlkR x.tcbState x.tcbFault)
    (hT : B8d.RT s σ0.curThread) {z : Unit × State Unit} (hz : z ∈ (maybeDonateSc (Z := Unit) σ0.curThread n s).1) :
    KP σ0 z.2 ∧ Rdy z.2 ∧ SR σ0.curThread z.2 := by
  obtain ⟨r5, sr5⟩ := rd_maybeDonateSc_sr σ0.curThread n s hR hx hnb (fun c hc => hT x c hx hc) hz
  refine ⟨?_, r5, sr5⟩
  cases hb : x.tcbSchedContext with
  | some c =>
    rw [md_ro (fun x' hx' => by rw [hx] at hx'; cases hx'; rw [hb]; simp) hz]; exact hK
  | none =>
    exact kp_nores hK (nores' h0 hK hx hb) (cfk_maybeDonateSc' _ _ s z hz)
      (cw_of_cp (fun σ1 c => A8.cp_maybeDonateSc σ0.curThread n σ1 c) hz)

/-- **`complete_signal ntfn ct`** for ct unbound or bound to any SC: `KP` and `SR ct`. -/
theorem kt_completeSignal (σ0 : State Unit) (h0 : B0R σ0) (ntfnptr : ObjRef) (s : State Unit) (hK : KP σ0 s)
    (hR : Rdy s) {x : Tcb} (hx : s.kheap σ0.curThread = some (.tcb x)) (hnb : ¬ BlkR x.tcbState x.tcbFault)
    (hT : B8d.RT s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ (completeSignal (Z := Unit) ntfnptr σ0.curThread s).1) : KP σ0 y.2 ∧ SR σ0.curThread y.2 := by
  unfold completeSignal at hy
  obtain ⟨⟨nt, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  dsimp only at hy
  cases hob : nt.ntfnObj with
  | activeNtfn bdg =>
    simp only [hob] at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain ⟨z4, h4, hy⟩ := hy
    obtain ⟨z5, h5, hy⟩ := hy
    obtain ⟨k4, r4, T4, x4, hx4, es, ef⟩ := pre_sig σ0 hK hR hx hT h3 h4
    obtain ⟨k5, r5, sr5⟩ := kt_maybeDonateSc σ0 h0 ntfnptr z4.2 k4 r4 hx4 (by rw [es, ef]; exact hnb) T4 h5
    obtain ⟨z6, h6, hy⟩ := hy
    obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
    cases hsc : x6.tcbSchedContext with
    | none =>
      rw [hsc] at hy
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨k5, sr5⟩
    | some scp =>
      rw [hsc] at hy
      dsimp only [NonDet.maybeM] at hy
      obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨⟨n7, hk7⟩, e7⟩ := SInvI.mem_getSchedContext_vi h7
      obtain ⟨w1, w2⟩ := z7
      simp only at e7 hk7 hy
      subst w2
      unfold NonDet.when at hy
      split at hy
      · obtain ⟨⟨a8, s8⟩, h8, hy⟩ := hy
        have e8 : s8 = z5.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h8
        subst s8
        dsimp only at hy
        rw [Notif.nd_gets_bind] at hy
        try dsimp only at hy
        split at hy
        · rename_i hg
          refine ⟨kp_ruc' h0 k5 ?_ hk7 hy, sr_ruc scp _ z5.2 r5 hk7 sr5 y hy⟩
          rw [← kp_curSc k5]; exact hg.2
        · obtain rfl := Set.mem_singleton_iff.1 hy
          exact ⟨k5, sr5⟩
      · obtain rfl := Set.mem_singleton_iff.1 hy
        exact ⟨k5, sr5⟩
  | _ =>
    simp only [hob] at hy
    first | exact (hy : False).elim | (obtain ⟨_, h, -⟩ := hy; exact h.elim) | simp [NonDet.fail] at hy

/-- `receive_signal_blocked` of ct (any binding). -/
theorem kt_rsBlocked (σ0 : State Unit) (np : ObjRef) (blk : Bool) (s : State Unit) (hK : KP σ0 s)
    (hT : B8d.RT s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ (receiveSignalBlocked (Z := Unit) σ0.curThread np blk s).1) : KT σ0 y.2 := by
  unfold receiveSignalBlocked at hy
  split at hy
  · have hK' : KP σ0 y.2 := by
      refine (?_ : IK (KP σ0) _) s hK y hy
      repeat' (first | exact kp_maybeReturnSc _ _ | exact kp_tcbNtfnAppend _ _ _ | kp_leaf | ik_step0)
    refine ⟨hK', Or.inr ?_⟩
    have hn := A9.no_bind (fun z hz => A9.no_sts σ0.curThread _ rfl hz)
      (fun _ => ik_bind (by unfold tcbNtfnAppend; fg_auto) fun _ => fg_maybeReturnSc _ _) y hy
    rw [kp_curThread hK']; exact A9.nrun_of_no hn
  · unfold doNbrecvFailedTransfer at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    have k3 : KP σ0 z3.2 := ik_kp (SVK.sv_asUser' _ _) (cfk_asUser' _ _) σ0 s hK z3 h3
    refine ⟨k3, Or.inl ?_⟩
    rw [kp_curThread k3]; exact sr_of_rt (B8d.rT_svs hT (SVK.sv_asUser' _ _ s z3 h3))

/-- **`receive_signal ct cap blk`** for ct unbound or bound to any SC. -/
theorem kt_receiveSignal (σ0 : State Unit) (h0 : B0R σ0) (cap : Cap) (blk : Bool) (s : State Unit)
    (hK : KP σ0 s) (hR : Rdy s) {x : Tcb} (hx : s.kheap σ0.curThread = some (.tcb x))
    (hnb : ¬ BlkR x.tcbState x.tcbFault) (hT : B8d.RT s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ (receiveSignal (Z := Unit) σ0.curThread cap blk s).1) : KT σ0 y.2 := by
  unfold receiveSignal at hy
  cases cap
  case notificationCap np bd rt =>
    obtain ⟨⟨n1, s1⟩, h1, hy⟩ := hy
    obtain ⟨rfl, e1⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
    subst s1
    obtain ⟨⟨nt, s2⟩, h2, hy⟩ := hy
    have e2 : s2 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
    subst s2
    dsimp only at hy
    cases hob : nt.ntfnObj with
    | idleNtfn => simp only [hob] at hy; exact kt_rsBlocked σ0 _ blk s hK hT hy
    | waitingNtfn q => simp only [hob] at hy; exact kt_rsBlocked σ0 _ blk s hK hT hy
    | activeNtfn bdg =>
      simp only [hob] at hy
      obtain ⟨z3, h3, hy⟩ := hy
      obtain ⟨z4, h4, hy⟩ := hy
      obtain ⟨z5, h5, hy⟩ := hy
      obtain ⟨k4, r4, T4, x4, hx4, es, ef⟩ := pre_sig σ0 hK hR hx hT h3 h4
      obtain ⟨k5, r5, sr5⟩ := kt_maybeDonateSc σ0 h0 _ z4.2 k4 r4 hx4 (by rw [es, ef]; exact hnb) T4 h5
      obtain ⟨z6, h6, hy⟩ := hy
      obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
      have ky : KP σ0 y.2 := kp_ifCondT' _ h0 z5.2 k5 y hy
      refine ⟨ky, Or.inl ?_⟩
      rw [kp_curThread ky]
      exact A9.sr_ifCond _ _ _ σ0.curThread z5.2 r5 sr5 y hy
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)

/-! ## `receive_ipc` of ct, any binding -/

/-- `receive_ipc_blocked` of ct. -/
theorem kt_rcvBlocked (σ0 : State Unit) (blk : Bool) (epptr : ObjRef) (reply : Option ObjRef) (s : State Unit)
    (hK : KP σ0 s) (hT : B8d.RT s σ0.curThread) {y : Unit × State Unit}
    (hy : y ∈ (receiveIpcBlocked (Z := Unit) blk σ0.curThread epptr reply s).1) : KT σ0 y.2 := by
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
    refine ⟨ky, Or.inr ?_⟩
    rw [kp_curThread ky]; exact A9.nrun_of_no hn
  · unfold doNbrecvFailedTransfer at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    have k3 : KP σ0 z3.2 := ik_kp (SVK.sv_asUser' _ _) (cfk_asUser' _ _) σ0 s hK z3 h3
    refine ⟨k3, Or.inl ?_⟩
    rw [kp_curThread k3]; exact sr_of_rt (B8d.rT_svs hT (SVK.sv_asUser' _ _ s z3 h3))

/-- **`receive_ipc` of ct after the endpoint and notification reads**, any binding. -/
theorem kt_recvTail (σ0 : State Unit) (h0 : B0R σ0) (epptr : ObjRef) (isBlocking : Bool)
    (reply ntfnptr : Option ObjRef) (ntfn : Notification) (ep : Endpoint) (s : State Unit) (hK : KP σ0 s)
    (hS : RcvW s σ0.curThread) {y : Unit × State Unit}
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
      | _ => receiveIpcBlocked isBlocking σ0.curThread epptr reply) s).1) : KT σ0 y.2 := by
  obtain ⟨hR, hI, hA, hq, hrq, ⟨x, hx, hbk⟩, hT⟩ := hS
  split_ifs at hy with hc
  · obtain ⟨ky, sy⟩ := kt_completeSignal σ0 h0 _ s hK hR hx (hbk x.tcbFault) hT hy
    exact ⟨ky, Or.inl (by rw [kp_curThread ky]; exact sy)⟩
  · obtain ⟨z4, h4, hy⟩ := hy
    have F4 : KP σ0 z4.2 ∧ B8d.RT z4.2 σ0.curThread ∧ Rdy z4.2 ∧ SInvB.ScInv z4.2 := by
      unfold NonDet.when at h4
      split at h4
      · exact ⟨kp_maybeReturnSc _ σ0 s hK z4 h4, rt_maybeReturnSc _ _ s hT h4,
          rd_maybeReturnSc_p _ _ s hq hA hrq hR z4 h4, SInvB.sik_maybeReturnSc _ _ s hI z4 h4⟩
      · obtain rfl := Set.mem_singleton_iff.1 h4
        exact ⟨hK, hT, hR, hI⟩
    obtain ⟨k4, T4, e4, i4⟩ := F4
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
      have i7 : SInvB.ScInv z7.2 := SInvB.sik_of_sbk (fun _ => SInvB.sb_tcbEpDequeue _ epptr) z4.2 i4 z7 h7
      have v7 := sv_tcbEpDequeue _ epptr z4.2 z7 h7
      have k7 : KP σ0 z7.2 := ik_kp (sv_tcbEpDequeue _ epptr) (cfk_tcbEpDequeue' _ epptr) σ0 z4.2 k4 z7 h7
      have T7 : B8d.RT z7.2 σ0.curThread := B8d.rT_svs T4 v7
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
      have hKy := kp_recvSender' h0 _ epptr reply _ z7.2 k7 y hy
      have hTy := rt_recvSender _ σ0.curThread epptr e reply _ z7.2 e7 i7.fwd hx8 hst T7 y hy
      exact ⟨hKy, Or.inl (by rw [kp_curThread hKy]; exact sr_of_rt hTy)⟩
    all_goals (dsimp only at hy; exact kt_rcvBlocked σ0 isBlocking epptr reply z4.2 k4 T4 hy)

/-- **`receive_ipc` of ct from the endpoint read on.** -/
theorem kt_recvRest (σ0 : State Unit) (h0 : B0R σ0) (epptr : ObjRef) (isBlocking : Bool) (reply : Option ObjRef)
    (s : State Unit) (hK : KP σ0 s) (hS : RcvW s σ0.curThread) {y : Unit × State Unit}
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
        | _ => receiveIpcBlocked isBlocking σ0.curThread epptr reply) s).1) : KT σ0 y.2 := by
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
    exact kt_recvTail σ0 h0 epptr isBlocking reply none _ ep s hK hS hy
  | some p =>
    obtain ⟨⟨ntfn, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    exact kt_recvTail σ0 h0 epptr isBlocking reply (some p) ntfn ep s hK hS hy

/-- **`receive_ipc ct cap blk replyCap`** from `KP σ0 s`, rd8e's `RcvS` and
ctq's `RBk true` at `s` (ct's binding arbitrary): every outcome is `KT σ0`. -/
theorem kt_receiveIpc (σ0 : State Unit) (h0 : B0R σ0) (cap : Cap) (isBlocking : Bool) (replyCap : Cap)
    (s : State Unit) (hK : KP σ0 s) (hS : RcvW s σ0.curThread) (hRB : SInvQ.RBk true s)
    {y : Unit × State Unit}
    (hy : y ∈ (receiveIpc (Z := Unit) σ0.curThread cap isBlocking replyCap s).1) : KT σ0 y.2 := by
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
      have S4 := rcvW_when tptr σ0.curThread s hS hRB (kp_curThread hK) h4
      have k4 : KP σ0 z4.2 := by
        unfold NonDet.when at h4
        split at h4
        · exact kp_cancelIpc _ σ0 s hK z4 h4
        · obtain rfl := Set.mem_singleton_iff.1 h4; exact hK
      try dsimp only at hy
      obtain ⟨⟨rp, s5⟩, h5, hy⟩ := hy
      obtain ⟨rfl, e5⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
      subst s5
      exact kt_recvRest σ0 h0 epptr isBlocking (some r) z4.2 k4 S4 hy
    case nullCap =>
      dsimp only at hy
      obtain ⟨⟨reply, s2⟩, h2, hy⟩ := hy
      obtain ⟨rfl, e2⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h2)
      subst s2
      exact kt_recvRest σ0 h0 epptr isBlocking none s hK hS hy
    all_goals (dsimp only at hy; obtain ⟨_, h, -⟩ := hy; exact h.elim)
  all_goals (obtain ⟨_, h, -⟩ := hy; exact h.elim)

/-! ## `handle_recv` anchored at its start -/

/-- **`SS4` after `handle_recv` from `SS4` at its start** (ct's binding
arbitrary): rd13a's `ss4_handleRecvK` anchored at `t` itself. -/
theorem ss4_handleRecvT (blk cr : Bool) (t : State Unit) (hS4 : A10.SS4 t) (hS : RcvW t t.curThread)
    (hE : SInvQ.EB true t) (hN : NQ [t.curThread] t) (hni : t.curThread ≠ t.idleThread) :
    ∀ y ∈ (handleRecv (Z := Unit) blk cr t).1, A10.SS4 y.2 := by
  obtain ⟨xt, hxt, hbk⟩ := hS.2.2.2.2.2.1
  have h0 : B0R t := fun hr => ⟨xt, hxt, hS4.2.2.2 hr xt hxt⟩
  have hOS : OS t := hS4.1
  have hNB : TP (A11b.NB0 t.curThread) t := by
    intro p x' hp ep e r d hx'
    subst ep
    rw [hxt] at hp; cases hp
    exact hbk none (by unfold BlkR; exact Or.inr (Or.inr ⟨e, r, d, hx'⟩))
  have hRIP : ∀ cp rc, HK (fun s' => s' = t) A10.SS4 (receiveIpc (Z := Unit) t.curThread cp blk rc) := by
    intro cp rc s' hs' y hy
    rw [hs'] at hy
    exact ss4_of_kt hS4 h0 hni (kt_receiveIpc t h0 cp blk rc t (KP.refl t) hS hE.2 hy)
  have hRS : ∀ cp, HK (fun s' => s' = t) A10.SS4 (receiveSignal (Z := Unit) t.curThread cp blk) := by
    intro cp s' hs' y hy
    rw [hs'] at hy
    exact ss4_of_kt hS4 h0 hni
      (kt_receiveSignal t h0 cp blk t (KP.refl t) hS.1 hxt (hbk xt.tcbFault) hS.2.2.2.2.2.2 hy)
  have hHF : ∀ e, HK (fun s' => s' = t) A10.SS4 (handleFault (Z := Unit) t.curThread e) := by
    intro e s' hs' z hz
    rw [hs'] at hz
    have hE1 := SInvQ.eb_handleFault_p (k := true) t.curThread e t (SInvQ.npq_ct hE) hN
      (List.mem_singleton_self _) hE z hz
    exact A11b.ss4_end hOS (A11b.cp_handleFault _ e t t.curSc t ⟨rfl, A8.CW.refl _ _⟩ z hz)
      (A11b.cfk_handleFault _ e t z hz) (A11b.nr_handleFault _ e t hNB z hz) hE1.2.2 hni
  unfold handleRecv
  intro y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  (try dsimp only at hy)
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = t := by
    refine (?_ : IK (fun s' => s' = t) _) t rfl y2 h2
    unfold NonDet.liftM
    exact ik_bind (ik_asUserGet _ _ t) fun _ => ik_pure _
  rw [e2] at hy
  refine hk_catch (I := fun s' => s' = t) (Q0 := A10.SS4) ?_ hHF t rfl y hy
  refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
  split
  · (try dsimp only)
    split
    · (try dsimp only)
      split
      · refine hkr_bind (ik_lookupReply t) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
      · refine hkr_bind (ik_pure _) (fun rc => ?_)
        exact hkr_liftE (hRIP _ rc)
    · exact hkr_throw _
  · (try dsimp only)
    split
    · refine hkr_bind (by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
      split
      · exact hkr_liftE (hRS _)
      · exact hkr_throw _
    · exact hkr_throw _
  · exact hkr_throw _

end

end Fl4Proofs.P3.SInvR.A14a
