/-
P3 (DESIGN.md §9), invariant line G1 (ctq7): **faults, timeouts and
signals carry `EB k`** (spec side only, outside the JAtZ cone; KENTRY-PLAN
ctq7).

* `QE k s`: when `k`, the current thread is in no endpoint queue (nq3's `NQ
  K` with the current thread in `K`: `qe_of_nq`).
* `eb_sendFaultIpc_p`, `eb_handleTimeout_p`, **`eb_handleFault_p`**: the
  faulting thread has `NPQ` (the current thread under `EB true`: `npq_ct`;
  a reply receiver: read blocked, then Running), `NQ K` with the current
  thread in `K` (nq3) for the woken handler-side receiver. When no handler
  cap is there, `send_fault_ipc` returns `false` without a state change and
  `handle_no_fault` makes the thread Inactive (`NPQ`).
* `send_signal` for both `k` (ctq6's `rbf_sendSignal` generalised): the
  woken thread was read blocked, so when `k` and the current thread is a
  runnable TCB (the perform runs under Restart) it is not current (`AK`,
  `ak_of`); **`eb_sendSignal_p`**.
-/
import Fl4Proofs.P3.SpecInvCqE2
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Faults and timeouts -/

/-- When `k`, the current thread is in no endpoint queue. -/
abbrev QE (k : Bool) (s : State Unit) : Prop := k = true → ¬ queuedE s s.curThread

theorem qe_of_nq {k : Bool} {K : List ObjRef} {s : State Unit} (h : NQ K s) (hc : s.curThread ∈ K) : QE k s :=
  fun _ => (h.2 _ hc).2.2

theorem eb_sendIpc_q {k : Bool} (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hT : NPQ thread σ) (hq : QE k σ) :
    IKp (EB k) σ (sendIpc (Z := Unit) block call badge cg cgr cd thread epptr) :=
  eb_sendIpc_p block call badge cg cgr cd thread epptr σ hT (fun hk x hx hm => hq hk ⟨epptr, x, hx, hm⟩)

theorem ct_threadSet (C : ObjRef) (f : Tcb → Tcb) (t : ObjRef) : IK (CTh C) (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | ik_step0 | ik_unfold)

theorem eb_threadSet {k : Bool} (f : Tcb → Tcb) (t : ObjRef)
    (h : ∀ x, (f x).tcbDomain = x.tcbDomain ∧ (f x).tcbPriority = x.tcbPriority ∧ (f x).tcbState = x.tcbState)
    (hd : ∀ x, dom0 x → dom0 (f x)) : EBK k (threadSet (Z := Unit) f t) :=
  eb_of (tqx_threadSet f t h) (sa_threadSet f t fun x hr => by rw [(h x).2.2]; exact hr) (q4_threadSet f t hd)
    (rb_threadSet f t fun x hr => by rw [(h x).2.2]; exact hr)

theorem npq_threadSet (u : ObjRef) (f : Tcb → Tcb) (t : ObjRef) : IK (NPQ u) (threadSet (Z := Unit) f t) :=
  npq_frame u fun A R Q => by unfold threadSet; repeat' (first | ik_step0 | ik_unfold)

theorem eb_sendFaultIpc_p {k : Bool} {K : List ObjRef} (tptr : ObjRef) (handlerCap : Cap) (fault : Fault)
    (cd : Bool) (σ : State Unit) (hT : NPQ tptr σ) (hN : NQ K σ) (hc : σ.curThread ∈ K) :
    IKp (EB k) σ (sendFaultIpc (Z := Unit) tptr handlerCap fault cd) := by
  unfold sendFaultIpc
  split
  · intro hσ y ⟨z, hz, hy⟩
    have e1 : EB k z.2 := eb_threadSet _ tptr (fun _ => by exact ⟨rfl, rfl, rfl⟩) (fun _ h => by exact h) σ hσ z hz
    have n1 : NPQ tptr z.2 := npq_threadSet tptr _ tptr σ hT z hz
    have q1 : NQ K z.2 := nq_threadSet _ tptr (fun _ => by rfl) σ hN z hz
    have c1 : z.2.curThread = σ.curThread := ct_threadSet σ.curThread _ tptr σ rfl z hz
    obtain ⟨w, hw, hy⟩ := hy
    have e2 := eb_sendIpc_q _ _ _ _ _ _ _ _ z.2 n1 (qe_of_nq q1 (by rw [c1]; exact hc)) e1 w hw
    rw [Set.mem_singleton_iff.1 hy]; exact e2
  · exact ikp_of_ik (ik_pure _) σ
  · exact ikp_of_ik ik_fail σ

/-- `send_fault_ipc` returning `false` changed nothing. -/
theorem sfi_false {tptr : ObjRef} {handlerCap : Cap} {fault : Fault} {cd : Bool} {σ : State Unit}
    {y : Bool × State Unit} (hy : y ∈ (sendFaultIpc (Z := Unit) tptr handlerCap fault cd σ).1) (h : y.1 = false) :
    y.2 = σ := by
  unfold sendFaultIpc at hy
  split at hy
  · obtain ⟨z, -, hy⟩ := hy
    obtain ⟨w, -, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy] at h; cases h
  · rw [Set.mem_singleton_iff.1 hy]
  · exact hy.elim

theorem eb_handleTimeout_p {k : Bool} {K : List ObjRef} (tptr : ObjRef) (ex : Fault) (σ : State Unit)
    (hT : NPQ tptr σ) (hN : NQ K σ) (hc : σ.curThread ∈ K) :
    IKp (EB k) σ (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by unfold isValidTimeoutHandler; repeat' (first | ik_step0 | ik_unfold)) hy) fun v => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_pure_bind ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun cap => ?_
  exact ikp_bind (eb_sendFaultIpc_p _ _ _ _ σ hT hN hc) fun _ => ik_pure _

/-- **`handle_fault`**: the faulting thread has `NPQ`; the woken receiver
of the handler endpoint is not current (`NQ K`, current thread in `K`). -/
theorem eb_handleFault_p {k : Bool} {K : List ObjRef} (thread : ObjRef) (ex : Fault) (σ : State Unit)
    (hT : NPQ thread σ) (hN : NQ K σ) (hc : σ.curThread ∈ K) :
    IKp (EB k) σ (handleFault (Z := Unit) thread ex) := by
  unfold handleFault
  refine ikp_pure_bind ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun cap => ?_
  refine ikp_keep (fun y hy => by obtain ⟨_, -, rfl⟩ := q1_mem_threadGet hy; rfl) fun sc => ?_
  intro hσ y ⟨z, hz, hy⟩
  have e1 := eb_sendFaultIpc_p thread cap ex _ σ hT hN hc hσ z hz
  obtain ⟨w, hw, hy⟩ := hy
  have hw' : EB k w.2 := by
    unfold NonDet.unless at hw
    split at hw
    · rw [Set.mem_singleton_iff.1 hw]; exact e1
    · rename_i hz1
      have ez := sfi_false hz (by simpa using hz1)
      unfold handleNoFault at hw
      rw [ez] at hw
      exact eb_setThreadState_p thread .inactive σ (Or.inr hT) hσ w hw
  rw [Set.mem_singleton_iff.1 hy]; exact hw'

/-! ## `send_signal` for both `k` -/

/-- `t` is not the switch target, not current under `resume_cur_thread`,
and not current when `k`. -/
abbrev AK (k : Bool) (t : ObjRef) (s : State Unit) : Prop := AN t s ∧ (k = true → t ≠ s.curThread)

theorem ak_of {k : Bool} {σ : State Unit} (hS : SA σ) (hc : CB σ)
    (hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState)
    (hk : k = true → RnH σ.curThread σ.kheap)
    {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x)) (hr : runnable x.tcbState = false)
    (hn : x.tcbState ≠ .idleThreadState) : AK k t σ := by
  refine ⟨an_of hS hc hI hx hr hn, fun hk' e => ?_⟩
  obtain ⟨y, hy, hry⟩ := hk hk'
  rw [← e, hx] at hy; cases hy; rw [hr] at hry; cases hry

theorem ak_mk {k : Bool} {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : IK (AN t) m)
    (h2 : ∀ C, IK (CTh C) m) : IK (AK k t) m := by
  intro σ h y hy
  have e : y.2.curThread = σ.curThread := h2 σ.curThread σ rfl y hy
  exact ⟨h1 σ h.1 y hy, fun hk => by rw [e]; exact h.2 hk⟩

theorem ct_auto_cancelIpc (C t : ObjRef) : IK (CTh C) (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc; repeat' (first | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless))

theorem ct_asUser {α : Type} (C t : ObjRef) (u : UserMonad α) : IK (CTh C) (asUser (Z := Unit) t u) := by
  unfold asUser; repeat' (first | ik_step0 | ik_unfold)

theorem ct_tcbNtfnDequeue (C t n : ObjRef) : IK (CTh C) (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; repeat' (first | ik_step0 | ik_unfold)

theorem ct_getTcbObjRef (C : ObjRef) (f : Tcb → Option ObjRef) (t : ObjRef) : IK (CTh C) (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; repeat' (first | ik_step0 | ik_unfold)

theorem ct_maybeDonateSc (C t n : ObjRef) : IK (CTh C) (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  repeat' (first | (with_reducible exact ct_schedContextDonate _ _ _) | ik_step0 | ik_unfold | (unfold NonDet.when) | (unfold NonDet.unless))

/-- `RBk k`, TQ, and the thread read blocked. -/
abbrev MDk (k : Bool) (t : ObjRef) (s : State Unit) : Prop := RBk k s ∧ TQ s ∧ AK k t s

theorem mdk_of {k : Bool} {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : RBK k m) (h2 : TQK m)
    (h3 : IK (AK k t) m) : IK (MDk k t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2 y hy⟩

/-- `sched_context_resume` of an SC whose bound thread has `AK k`. -/
theorem rb_schedContextResume_p {k : Bool} (sc : ObjRef) (σ : State Unit) (hT : TQ σ)
    (h : ∀ y n u, σ.kheap sc = some (.schedContext y n) → y.scTcb = some u → AK k u σ) :
    IKp (RBk k) σ (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨e, n, hk⟩ := cq5_mem_getSc hz
  obtain ⟨scv, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨a, ha, hy⟩ := hy
  obtain ⟨ha1, ha2⟩ := cq5_mem_assertOpt ha
  obtain ⟨t, a2⟩ := a
  simp only at ha1 ha2; subst a2
  revert hy
  refine ikp_gets_bind ?_ hσ y
  refine ikp_when _ fun _ => ?_
  refine ikp_threadGet_bind fun x hx => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_when _ fun hc => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' ik_step0) hy) fun _ => ?_
  refine rb_postpone_p sc σ hT fun y' n' t' hk' ht' => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := h y' n' t' hk' ht'
  exact ⟨fun hc' => hc'.elim (fun hk => h3 hk) (fun hr => h2 hr), h1⟩

theorem ak_getTcbObjRef {k : Bool} (t : ObjRef) (f : Tcb → Option ObjRef) (u : ObjRef) :
    IK (AK k t) (getTcbObjRef (Z := Unit) f u) :=
  ak_mk (an_getTcbObjRef _ _ _) fun C => ct_getTcbObjRef C _ _

theorem ak_schedContextDonate {k : Bool} (t p u : ObjRef) : IK (AK k t) (schedContextDonate (Z := Unit) p u) :=
  ak_mk (an_schedContextDonate _ _ _) fun C => ct_schedContextDonate C _ _

/-- **`maybe_donate_sc t n`** with `t` read blocked, both `k`. -/
theorem mdk_maybeDonateSc {k : Bool} (t n : ObjRef) : HK1 (MDk k t) (RBk k) (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  refine hk1_bind (R := MDk k t)
    (hk1_of_ik' (mdk_of (rb_getTcbObjRef _ _) (tq_getTcbObjRef _ _) (ak_getTcbObjRef _ _ _))) fun scOpt => ?_
  intro σ hσ y hy
  unfold NonDet.when at hy
  split at hy
  · obtain ⟨z, hz, hy⟩ := hy
    have hz' : z.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz
    rw [hz'] at hy
    cases hz1 : z.1 with
    | none =>
      rw [hz1] at hy
      unfold NonDet.maybeM at hy
      rw [Set.mem_singleton_iff.1 hy]; exact hσ.1
    | some p =>
      rw [hz1] at hy
      unfold NonDet.maybeM at hy
      obtain ⟨w, hw, hy⟩ := hy
      obtain ⟨ew, scv, n', hk, hv⟩ := cq5_mem_getScObjRef hw
      rw [ew] at hy
      dsimp only at hy
      split at hy
      · obtain ⟨v, hv1, hy⟩ := hy
        have hvm : MDk k t v.2 :=
          mdk_of (rb_schedContextDonate _ _) (tq_schedContextDonate _ _) (ak_schedContextDonate _ _ _) σ hσ v hv1
        have hvb : BP t p v.2 := bp_donate p t σ v hv1
        exact rb_schedContextResume_p p v.2 hvm.2.1
          (fun y' n'' u hk' hu => by rw [hvb y' n'' u hk' hu]; exact hvm.2.2) hvm.1 y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

/-- The wake-up's tail after `maybe_donate_sc`, for a thread not current when `k`. -/
theorem rb_wakeTail_p {k : Bool} (t : ObjRef) (σ : State Unit) (hc : k = true → t ≠ σ.curThread) :
    IKp (RBk k) σ (NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= fun _ =>
      getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun scopt =>
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) := by
  refine ikp_gets_bind ?_
  refine ikp_bind (ikp_when _ fun _ => rb_possibleSwitchTo_p t σ hc) fun _ => ik_bind (rb_getTcbObjRef _ _) fun _ => ?_
  unfold ifSporadicCurScTestRefillUnblockCheck; rb_auto

/-- A blocked thread is woken, both `k`. -/
theorem mdk_wake {k : Bool} (t n : ObjRef) (b : Badge) (m : NonDet (State Unit) Unit) (hm : IK (MDk k t) m) :
    HK1 (MDk k t) (RBk k) (m >>= fun _ => setThreadState (Z := Unit) t .running >>= fun _ =>
      asUser (Z := Unit) t (setRegister badge_register b) >>= fun _ => maybeDonateSc (Z := Unit) t n >>= fun _ =>
      NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= fun _ =>
      getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun scopt =>
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) := by
  refine hk1_bind (hk1_of_ik' hm) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (mdk_of (rb_setThreadState _ _) (tqx_setThreadState_r _ _ rfl)
    (ak_mk (an_setThreadState _ _ _) fun C => ct_setThreadState C _ _))) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (mdk_of (rb_asUser _ _) (tqx_asUser _ _)
    (ak_mk (an_asUser _ _ _) fun C => ct_asUser C _ _))) fun _ => ?_
  intro σ hσ y ⟨z, hz, hy⟩
  have h1 := mdk_maybeDonateSc t n σ hσ z hz
  have c1 : z.2.curThread = σ.curThread := ct_maybeDonateSc σ.curThread t n σ rfl z hz
  exact rb_wakeTail_p t z.2 (fun hk => by rw [c1]; exact hσ.2.2.2 hk) h1 y hy

/-- **`send_signal`** keeps `RBk k` (with SQ4, NtfnQB, idle in its idle
state, and when `k` the current thread a runnable TCB). -/
theorem rb_sendSignal_p {k : Bool} (n : ObjRef) (b : Badge) (σ : State Unit) (hq : SQ4 σ) (hN : NtfnQB σ)
    (hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState)
    (hk : k = true → RnH σ.curThread σ.kheap) :
    IKp (RBk k) σ (sendSignal (Z := Unit) n b) := by
  unfold sendSignal
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hk0, ez⟩ := SInvI.mem_getSimpleKo hz
  obtain ⟨ntfn, z2⟩ := z
  simp only at hk0 ez; subst z2
  revert hy
  refine (show IKp (RBk k) σ _ from ?_) hσ y
  dsimp only
  cases hO : ntfn.ntfnObj with
  | idleNtfn =>
    cases hB : ntfn.ntfnBoundTcb with
    | none => dsimp only; exact ikp_of_ik (by rb_auto) σ
    | some tcb =>
      dsimp only
      unfold getThreadState
      refine ikp_threadGet_bind fun x hx => ?_
      split
      · rename_i hrb
        obtain ⟨hr, hni⟩ := cq6_rnb hrb
        intro h0 y hy
        have hA : AK k tcb σ := ak_of hq.1.2 h0.2 hI hk hx hr hni
        exact mdk_wake tcb n b _ (mdk_of (rb_cancelIpc _) (tq_cancelIpc _)
          (ak_mk (an_cancelIpc _ _) fun C => ct_auto_cancelIpc C _)) σ ⟨h0, hq.1.1, hA⟩ y hy
      · exact ikp_of_ik (by rb_auto) σ
  | waitingNtfn q =>
    dsimp only
    unfold updateWaitingNtfn
    intro h0 y hy
    obtain ⟨z, ⟨hne, ez⟩, hy⟩ := hy
    subst ez
    obtain ⟨w, hw, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hw] at hy
    have hm : the q.head? ∈ ntfn.ntfnObj.ntfnQueue := by rw [hO]; exact the_head_mem hne
    obtain ⟨x, hx, hs⟩ := hN n ntfn _ hk0 hm
    have hA : AK k (the q.head?) σ :=
      ak_of hq.1.2 h0.2 hI hk hx (by rw [hs]; rfl) (by rw [hs]; exact fun e => by cases e)
    exact mdk_wake _ n b _ (mdk_of (rb_tcbNtfnDequeue _ _) (tq_tcbNtfnDequeue _ _)
      (ak_mk (an_tcbNtfnDequeue _ _ _) fun C => ct_tcbNtfnDequeue C _ _)) σ ⟨h0, hq.1.1, hA⟩ y hy
  | activeNtfn b' => dsimp only; exact ikp_of_ik (by rb_auto) σ

/-- **`send_signal`** keeps `EB k`. -/
theorem eb_sendSignal_p {k : Bool} (n : ObjRef) (b : Badge) (σ : State Unit) (hN : NtfnQB σ)
    (hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState)
    (hk : k = true → RnH σ.curThread σ.kheap) :
    IKp (EB k) σ (sendSignal (Z := Unit) n b) :=
  fun hσ y hy => ⟨sq4_sendSignal n b σ hσ.1 y hy, rb_sendSignal_p n b σ hσ.1 hN hI hk hσ.2 y hy⟩

end

end Fl4Proofs.P3.SInvQ
