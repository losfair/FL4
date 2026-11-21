/-
P3 (DESIGN.md §9), invariant line G1 (rd8g): **`Sched.BlockedScActive`,
the pinned writers** (spec side only, outside the JAtZ cone).

* **`TA t σ`**: every SC bound to `t` (`scTcb = some t`) is active. Then a
  TCB write at `t` may put `t` in ANY state (`bsa_updT`, `ta_updT`), so
  **`ba_setThreadState_p`** (blocking a thread whose SCs are active: l4v
  `active_if_bound_sc_tcb_at` at the blocking sites, the blocker's SC being
  the active `cur_sc`).
* **`ba_updateSchedContext_p`**: an SC write leaving the SC active (the
  pushes of `bind_sc_reply`, the binding of `sched_context_donate`).
* **`ba_schedContextDonate`** (rd8e's `PA p σ`: the donated SC active).
* **`ba_replyRemove`** (no hypothesis: the donated SC is a reply-stack SC).
* `ba_sendIpcBlocked_p`, `ba_receiveIpcBlocked_p`, `ba_receiveSignalBlocked_p` (given `TA` of the blocker).
-/
import Fl4Proofs.P3.SpecInvRd8gF5
import Fl4Proofs.P3.SpecInvRd8eC
open Classical

namespace Fl4Proofs.P3.SInvR.B8g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e

noncomputable section

set_option maxHeartbeats 1000000

/-- Every SC bound to `t` is active. -/
def TA (t : ObjRef) (σ : State Unit) : Prop :=
  ∀ q y n, σ.kheap q = some (.schedContext y n) → y.scTcb = some t → scActive y = true

theorem upd_sc_ne {σ : State Unit} {p q : ObjRef} {w : Tcb} {y : SchedContext} {n : Nat}
    (hq : (Function.update σ.kheap p (some (.tcb w))) q = some (.schedContext y n)) : q ≠ p := by
  rintro rfl; rw [Function.update_self] at hq; cases hq

/-- **A TCB write at `t` in any state**, given `TA t`. -/
theorem bsa_updT {σ : State Unit} {p : ObjRef} (h : BSA σ) (hT : TA p σ) (w : Tcb) :
    BSA { σ with kheap := Function.update σ.kheap p (some (.tcb w)) } := by
  constructor
  · intro q y n t x hq hy ht hst
    have eq := upd_sc_ne (σ := σ) hq
    change Function.update σ.kheap p (some (KernelObject.tcb w)) q = _ at hq
    rw [Function.update_of_ne eq] at hq
    by_cases etp : t = p
    · subst etp; exact hT q y n hq hy
    · change Function.update σ.kheap p (some (KernelObject.tcb w)) t = _ at ht
      rw [Function.update_of_ne etp] at ht; exact h.tcb q y n t x hq hy ht hst
  · intro q y n hq hr
    have eq := upd_sc_ne (σ := σ) hq
    change Function.update σ.kheap p (some (KernelObject.tcb w)) q = _ at hq
    rw [Function.update_of_ne eq] at hq; exact h.replies q y n hq hr

theorem ta_updT {σ : State Unit} {p : ObjRef} (hT : TA p σ) (w : Tcb) :
    TA p { σ with kheap := Function.update σ.kheap p (some (.tcb w)) } := by
  intro q y n hq hy
  have eq := upd_sc_ne (σ := σ) hq
  change Function.update σ.kheap p (some (KernelObject.tcb w)) q = _ at hq
  rw [Function.update_of_ne eq] at hq; exact hT q y n hq hy

theorem ba_setObject_ta (p : ObjRef) (w : Tcb) (σ : State Unit) :
    IKp (fun s => BSA s ∧ TA p s) σ (setObject (Z := Unit) p (.tcb w)) := by
  unfold setObject
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨y1, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hx⟩ := hx
  obtain ⟨v, hv, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hv] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨bsa_updT hσ.1 hσ.2 w, ta_updT hσ.2 w⟩

theorem ba_threadSet_ta (f : Tcb → Tcb) (t : ObjRef) :
    IK (fun s => BSA s ∧ TA t s) (threadSet (Z := Unit) f t) := by
  unfold threadSet
  exact ik_getsThe_bind fun x σ _ => ba_setObject_ta t _ σ

/-- **`set_thread_state t ts`, any `ts`, given `TA t`.** -/
theorem ba_setThreadState_p (t : ObjRef) (ts : ThreadState) (σ : State Unit) (hT : TA t σ) :
    IKp BSA σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ikp_bind ?_ fun _ => ba_setThreadStateAct t
  intro hσ r hr
  exact (ba_threadSet_ta _ t σ ⟨hσ, hT⟩ r hr).1

/-- **An SC write leaving the SC active.** -/
theorem ba_updateSchedContext_p (p : ObjRef) (f : SchedContext → SchedContext) (σ : State Unit)
    (hA : ∀ y n, σ.kheap p = some (.schedContext y n) → scActive (f y) = true) :
    IKp BSA σ (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  intro hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨obj, y2⟩ := y
  simp only at hk hs; subst hs
  dsimp only at hx
  split at hx
  · rename_i sc n
    refine ba_setObject_p _ _ _ ?_ hσ x hx
    rw [hk]; exact okb_act (hA sc n hk)
  · exact hx.elim

/-- **`sched_context_donate p t`** of an active SC (rd8e's `PA`). -/
theorem ba_schedContextDonate (p t : ObjRef) (σ : State Unit) (hp : PA p σ) :
    IKp BSA σ (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate
  intro hσ r hr
  obtain ⟨⟨fo, s1⟩, h1, hr⟩ := hr
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨z2, h2, hr⟩ := hr
  have bp2 : BSA z2.2 ∧ PA p z2.2 := by
    unfold NonDet.when at h2
    split at h2
    · obtain ⟨⟨ft, s3⟩, h3, h2⟩ := h2
      have e3 : s3 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
      subst s3
      obtain ⟨z4, h4, h2⟩ := h2
      obtain ⟨x4, -, e4⟩ := SInvQ.q1_tsa_out h4
      obtain ⟨z5, h5, h2⟩ := h2
      have k5 := (kt_tcbReleaseRemove _ _ ft z4.2 ⟨rfl, rfl⟩ z5 h5).1
      obtain ⟨z6, h6, h2⟩ := h2
      obtain ⟨x6, hx6, e6⟩ := SInv.mem_threadSet h6
      have k7 := (kt_testReschedule _ _ ft z6.2 ⟨rfl, rfl⟩ z2 h2).1
      obtain ⟨y0, n0, hk0, ha0⟩ := hp
      have hk5 : z5.2.kheap = σ.kheap := by rw [k5, e4]
      have hfp : ft ≠ p := fun h => by rw [h, hk5, hk0] at hx6; cases hx6
      have b5 : BSA z5.2 := bsa_kh hσ hk5
      have b6 : BSA z6.2 := by rw [e6]; exact bsa_upd b5 ft _ (by rw [hx6]; exact okb_tcb rfl)
      refine ⟨bsa_kh b6 k7, y0, n0, ?_, ha0⟩
      rw [k7, e6]
      simp only [Function.update_of_ne (Ne.symm hfp)]
      rw [hk5]; exact hk0
    · obtain rfl := Set.mem_singleton_iff.1 h2
      exact ⟨hσ, hp⟩
  obtain ⟨b2, p2⟩ := bp2
  obtain ⟨z7, h7, hr⟩ := hr
  obtain ⟨y2, n2, hk2, ha2⟩ := p2
  have b7 : BSA z7.2 := ba_updateSchedContext_p p _ z2.2 (fun y n hy => by
    rw [hk2] at hy; cases hy; exact ha2) b2 z7 h7
  -- the SC side of the binding (`scTcb := some t`) was the pinned active-SC write above; the TCB side
  -- (`tcbSchedContext := some p`) keeps the state, and BSA does not read `tcbSchedContext`
  exact ba_threadSet (tcbSchedContextUpdate fun _ => some p) t (fun _ => rfl) z7.2 b7 r hr

/-- **`reply_remove caller r`** (no hypothesis): the SC it may donate holds
`r` on its reply stack, so it is active by `BSA.replies`, and
`reply_unlink_sc` keeps its refill max (rd8e's `SVK.SVS`). -/
theorem ba_replyRemove (caller r : ObjRef) : BAK (replyRemove (Z := Unit) caller r) := by
  intro σ hσ y hy
  unfold replyRemove at hy
  obtain ⟨⟨a1, s1⟩, hz1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  obtain ⟨⟨a2, s2⟩, hz2, hy⟩ := hy
  have e2 : s2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz2
  subst s2
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  dsimp only at hy
  rcases hw : scWithReply r σ with _ | scPtr
  · simp only [hw] at hy
    first
    | exact ba_replyUnlinkTcb caller r σ hσ y hy
    | (obtain ⟨z, hz, hy⟩ := hy
       obtain rfl := Set.mem_singleton_iff.1 hz
       exact ba_replyUnlinkTcb caller r _ hσ y hy)
  · simp only [hw] at hy
    obtain ⟨⟨a4, s4⟩, hz4, hy⟩ := hy
    have e4 : s4 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz4
    subst s4
    obtain ⟨z5, hz5, hy⟩ := hy
    obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    have v6 : SVK.SVS σ z6.2 := SVK.sv_replyUnlinkSc' scPtr r σ z6 hz6
    have b6 : BSA z6.2 := ba_replyUnlinkSc scPtr r σ hσ z6 hz6
    obtain ⟨z7, hz7, hy⟩ := hy
    have b7 : BSA z7.2 := by
      unfold NonDet.when at hz7
      split at hz7
      · obtain ⟨ys, ns, hks, hrm⟩ := Sched.scWithReply_mem' hw
        have ha := hσ.replies scPtr ys ns hks (List.ne_nil_of_mem hrm)
        have e := v6.1 scPtr
        rw [hks] at e
        obtain ⟨y', hy', -, hm', -⟩ := SVK.sv_sc (o := z6.2.kheap scPtr) e
        have hpa : PA scPtr z6.2 := ⟨y', ns, hy', by show activeSc _ = true; rw [hm']; exact ha⟩
        exact ba_schedContextDonate scPtr caller z6.2 hpa b6 z7 hz7
      · obtain rfl := Set.mem_singleton_iff.1 hz7
        exact b6
    exact ba_replyUnlinkTcb caller r z7.2 b7 y hy

/-! ## The blocking writers, given `TA` of the blocker -/

/-- **`send_ipc_blocked`** (the sender's SCs active). -/
theorem ba_sendIpcBlocked_p (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool)
    (σ : State Unit) (hT : TA thread σ) :
    IKp BSA σ (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked
  exact ikp_bind (ba_setThreadState_p _ _ σ hT) fun _ => ba_tcbEpAppend _ _ _

/-- **`receive_ipc_blocked`** (the receiver's SCs active). -/
theorem ba_receiveIpcBlocked_p (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef)
    (σ : State Unit) (hT : TA thread σ) :
    IKp BSA σ (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked
  split
  · refine ikp_bind (ba_setThreadState_p _ _ σ hT) fun _ => ?_
    refine ik_bind ?_ fun _ => ba_tcbEpAppend _ _ _
    ba_auto
  · exact fun h => ba_doNbrecvFailedTransfer thread σ h

/-- **`receive_signal_blocked`** (the receiver's SCs active). -/
theorem ba_receiveSignalBlocked_p (thread ntfnptr : ObjRef) (isBlocking : Bool) (σ : State Unit)
    (hT : TA thread σ) : IKp BSA σ (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked
  split
  · refine ikp_bind (ba_setThreadState_p _ _ σ hT) fun _ => ?_
    exact ik_bind (ba_tcbNtfnAppend _ _) fun _ => ba_maybeReturnSc _ _
  · exact fun h => ba_doNbrecvFailedTransfer thread σ h

end

end Fl4Proofs.P3.SInvR.B8g
