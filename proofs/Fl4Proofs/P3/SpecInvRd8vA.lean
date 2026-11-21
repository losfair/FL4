/-
P3 (DESIGN.md §9), invariant line G1 (rd8v): **`VE` across `do_reply_transfer`** (KENTRY-PLAN rd8s
handoff 1; spec side only, outside the JAtZ cone).

The receiver `r` is unlinked by `reply_remove` (rd8s's `ve_replyRemoveV`: left Inactive), then set
Running / Restart / Inactive, so it is exempt (`VE (E ∪ {r})`) from there to the final
`when (sc ≠ none ∧ runnable)`:

* not taken: `r` is unbound or not runnable, hence not schedulable (`ve_drop`);
* ready and sufficient: `possible_switch_to r` (`ht_possibleSwitchTo`);
* `handle_timeout r`: rd9's **`A9.tmoNR`** (no premise: the fault set by `send_fault_ipc` survives
  the endpoint dequeue / `do_ipc_transfer` / `reply_unlink_tcb`, so `send_ipc` blocks `r`) makes
  `r` not runnable at every outcome (`ve_drop`);
* `postpone sc`: `sc.scTcb = r` by sb2's `ScBackS` (carried `ScInv`, read at the binding of `r`),
  so `r` is dequeued and release-enqueued (**`ht_postpone_self`**).

Top: **`ht_doReplyTransfer : HT (VE E ∧ ScInv) (VE E)`**; `ht_pair` / `ht_fst` pair a `VEK` /
`SIK` step with the carried `ScInv`.
-/
import Fl4Proofs.P3.SpecInvRd8sD
open Classical

namespace Fl4Proofs.P3.SInvR.B8v
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q Fl4Proofs.P3.SInvR.B8s

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

/-- `VE` paired with sb2's `ScInv`. -/
abbrev VS (E : ObjRef → Prop) (s : State Unit) : Prop := VE E s ∧ SInvB.ScInv s

theorem ht_pair {E' : ObjRef → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HT (VE E) (VE E') m)
    (hs : SInvB.SIK m) : HT (VS E) (VS E') m :=
  fun σ hσ x hx => ⟨h σ hσ.1 x hx, hs σ hσ.2 x hx⟩

/-- sb2's `ScInv` across any thread-state write. -/
theorem si_sts (t : ObjRef) (ts : ThreadState) : SInvB.SIK (setThreadState (Z := Unit) t ts) :=
  SInvB.sik_of_sbk fun _ => SInvB.sb_setThreadState t ts

theorem ht_vs {α : Type} {m : NonDet (State Unit) α} (h : VEK E m) (hs : SInvB.SIK m) : HT (VS E) (VS E) m :=
  ht_pair (ht_ik h) hs

theorem ht_fst {Q : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HT (VS E) (VS E) m)
    (hQ : ∀ s, VE E s → Q s) : HT (VS E) Q m :=
  ht_conseq (fun _ h => h) (fun s h => hQ s h.1) h

/-- The reads of `get_sc_obj_ref`. -/
theorem mem_getScObjRef {f : SchedContext → Option ObjRef} {p : ObjRef} {σ : State Unit}
    {y : Option ObjRef × State Unit} (h : y ∈ (getScObjRef (Z := Unit) f p σ).1) :
    y.2 = σ ∧ ∃ sc n, σ.kheap p = some (.schedContext sc n) ∧ y.1 = f sc := by
  unfold getScObjRef at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨e, n, hk⟩ := SInvB.mem_getSchedContext' hz
  rw [Set.mem_singleton_iff.1 h]
  exact ⟨e, z.1, n, hk, rfl⟩

/-- **`postpone p`** of an SC whose `scTcb` is `r`: `r` is dequeued and release-enqueued, so it
leaves the exception set. -/
theorem ht_postpone_self (r p : ObjRef) :
    HT (fun s => VE (Ins E r) s ∧ ∃ sc n, s.kheap p = some (.schedContext sc n) ∧ sc.scTcb = some r) (VE E)
      (postpone (Z := Unit) p) := by
  unfold postpone
  intro σ ⟨hv, sc, n, hk, hr⟩ x ⟨y, hy, hx⟩
  obtain ⟨e1, sc', n', hk', e2⟩ := mem_getScObjRef hy
  rw [hk] at hk'
  injection hk' with hk'
  injection hk' with hk' _
  subst hk'
  rw [e2, hr, e1] at hx
  refine ht_assertOpt_bind (fun u hu => ?_) σ hv x hx
  cases hu
  refine ht_bind (ht_conseq (fun _ h => h) (fun _ h => ve_mono (fun v hv => hv.elim id Or.inr) h)
    (ht_dequeue (E := Ins E r) r)) fun _ => ?_
  refine ht_bind (ht_tcbReleaseEnqueue_x (E := E) r) fun _ => ?_
  exact ht_ik (by ve_auto)

/-- A thread that is not runnable is not schedulable. -/
theorem nsched_of_nr {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hn : runnable x.tcbState = false) : schedulable t σ = true → False := by
  intro hs
  obtain ⟨x0, -, -, -, hk0, -, hrn, -⟩ := Sched.schedulable_inv hs
  rw [hk] at hk0
  injection hk0 with hk0
  injection hk0 with hk0
  subst hk0
  rw [hn] at hrn
  cases hrn

/-- An unbound thread is not schedulable. -/
theorem nsched_of_ub {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none) : schedulable t σ = true → False := by
  intro hs
  obtain ⟨x0, scp, y0, n0, hk0, hsc, -⟩ := Sched.schedulable_inv hs
  rw [hk] at hk0
  injection hk0 with hk0
  injection hk0 with hk0
  subst hk0
  rw [hn] at hsc
  cases hsc

set_option maxHeartbeats 4000000 in
/-- **`do_reply_transfer` keeps `VE E`** (from carried `ScInv`; module docstring). -/
theorem ht_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    HT (VS E) (VE E) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun recvOpt => ?_
  rcases recvOpt with _ | r
  · dsimp only [NonDet.maybeM]
    intro σ h x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact h.1
  dsimp only [NonDet.maybeM]
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun st => ?_
  split
  rotate_left
  · exact ht_fst (ht_vs (by ve_auto) (by si_auto)) fun _ h => h
  try dsimp only [letFun]
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun fault => ?_
  split
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_pair (ht_setThreadState_x r _) (si_sts r _)) fun _ => ?_
  rotate_left
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_vs (by ve_auto) (by si_auto)) fun _ => ?_
  refine ht_bind (ht_pair (ht_setThreadState_x r _) (si_sts r _)) fun _ => ?_
  all_goals
    -- the tail, from `VE (E ∪ {r}) ∧ ScInv`
    intro σ ⟨hv, hsi⟩ x ⟨y1, h1, hx⟩
    obtain ⟨x1, hk1, rfl⟩ := SInvQ.q1_mem_threadGet (by exact h1)
    obtain ⟨y2, h2, hx⟩ := hx
    obtain ⟨x2, hk2, rfl⟩ := SInvQ.q1_mem_threadGet (by exact h2)
    rw [hk1] at hk2
    injection hk2 with hk2
    injection hk2 with hk2
    subst hk2
    try dsimp only at hx
    unfold NonDet.when at hx
    split at hx
    · rename_i hc
      obtain ⟨⟨p3, s3⟩, h3, hx⟩ := hx
      obtain ⟨e3, e3'⟩ := SInvB.mem_assertOpt' h3
      dsimp only at e3 e3' hx
      subst e3'
      obtain ⟨⟨sc, s4⟩, h4, hx⟩ := hx
      obtain ⟨e4, n4, hk4⟩ := SInvB.mem_getSchedContext' h4
      dsimp only at e4 hk4 hx
      subst e4
      obtain ⟨y5, h5, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 h5] at hx
      try dsimp only at hx
      split at hx
      · exact ht_possibleSwitchTo r s4 hv x hx
      · obtain ⟨⟨tcb, s6⟩, h6, hx⟩ := hx
        unfold NonDet.getsThe at h6
        obtain ⟨-, e6'⟩ := SInvB.mem_assertOpt' h6
        dsimp only at e6' hx
        subst e6'
        split at hx
        · have hve : VE (Ins E r) x.2 := ve_handleTimeout (E := E) r _ s6 hv x hx
          have hnr : A8.NRun r x.2 := A9.tmoNR s6 r sc.scBadge ⟨x1, hk1, hc.2⟩ x hx
          refine ve_drop hve fun hs => (?_ : False).elim
          obtain ⟨x0, -, -, -, hk0, -, hrn, -⟩ := Sched.schedulable_inv hs
          rw [hnr x0 hk0] at hrn
          cases hrn
        · refine ht_postpone_self r p3 s6 ⟨hv, ?_⟩ x hx
          obtain ⟨y', k', hy', hb', -⟩ := SInvB.ScInv.back hsi r x1 p3 hk1 e3
          rw [hk4] at hy'
          injection hy' with hy'
          injection hy' with hy' _
          subst hy'
          exact ⟨sc, n4, hk4, hb'⟩
    · rename_i hc
      rw [Set.mem_singleton_iff.1 hx]
      refine ve_drop hv fun hs => (?_ : False).elim
      by_cases hb : x1.tcbSchedContext = none
      · exact nsched_of_ub hk1 hb hs
      · have hn : runnable x1.tcbState = false := by
          cases e : runnable x1.tcbState
          · rfl
          · exact absurd ⟨hb, e⟩ hc
        exact nsched_of_nr hk1 hn hs

end

end Fl4Proofs.P3.SInvR.B8v
