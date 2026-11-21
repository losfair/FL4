/-
P3 (DESIGN.md §9), invariant line G1 (ctq6): **the tail of every kernel
entry carries RD** (spec side only, outside the JAtZ cone; KENTRY-PLAN ctq5
handoff 1).

* FL4's timer step (`send_signal`s) keeps `RBk false`: the woken thread `t`
  was read blocked (receive-blocked, or queued on the notification: nq1's
  NtfnQB), so it is not the switch target (SA) and, under
  `resume_cur_thread`, not the current thread (`CB`: ct is runnable or idle,
  and idle is in its idle state by ValidIdle): `AN t`. `AN t` is kept up to
  `maybe_donate_sc` (writes set at most `choose_new_thread`), whose
  `sched_context_donate p t` binds `p` to `t` (`BP t p`, `bp_donate`), so the
  `postpone` in `sched_context_resume p` is of `t` (`rb_postpone_p`).
* **`rb_tail : HK1 (SQ4 ∧ ValidIdle ∧ NQ [] ∧ RBk false) (EX ∧ RB)
  (fl4Awaken; schedule; activate_thread)`**.
-/
import Fl4Proofs.P3.SpecInvCqZ
import Fl4Proofs.P3.SpecInvNtfnQG
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## A thread read blocked -/

/-- `t` is not the switch target, and not current under `resume_cur_thread`. -/
abbrev AN (t : ObjRef) (s : State Unit) : Prop :=
  s.schedulerAction ≠ .switchThread t ∧ (s.schedulerAction = .resumeCurThread → t ≠ s.curThread)

theorem an_of {σ : State Unit} (hS : SA σ) (hc : CB σ)
    (hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState)
    {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x)) (hr : runnable x.tcbState = false)
    (hn : x.tcbState ≠ .idleThreadState) : AN t σ := by
  refine ⟨(np_of_tcb_nr hS hx hr).1, fun hs e => ?_⟩
  rcases hc hs with ⟨y, hy, hry⟩ | hi
  · rw [← e, hx] at hy; cases hy; rw [hr] at hry; cases hry
  · rw [e, hi] at hx; exact hn (hI x hx)

theorem an_setCn (t : ObjRef) : IK (AN t) (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  exact ik_modify fun _ _ => ⟨(fun e => by cases e), (fun e => by cases e)⟩

syntax "an_leaf" : tactic
macro_rules | `(tactic| an_leaf) => `(tactic| with_reducible exact an_setCn _)

macro "an_auto" : tactic => `(tactic| repeat' (first | an_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem an_cancelIpc (t u : ObjRef) : IK (AN t) (cancelIpc (Z := Unit) u) := by
  unfold cancelIpc; an_auto

theorem an_setThreadState (t u : ObjRef) (ts : ThreadState) : IK (AN t) (setThreadState (Z := Unit) u ts) := by
  unfold setThreadState; an_auto

theorem an_asUser {α : Type} (t u : ObjRef) (m : UserMonad α) : IK (AN t) (asUser (Z := Unit) u m) := by
  unfold asUser; an_auto

theorem an_tcbNtfnDequeue (t u n : ObjRef) : IK (AN t) (tcbNtfnDequeue (Z := Unit) u n) := by
  unfold tcbNtfnDequeue; an_auto

theorem an_getTcbObjRef (t : ObjRef) (f : Tcb → Option ObjRef) (u : ObjRef) :
    IK (AN t) (getTcbObjRef (Z := Unit) f u) := by
  unfold getTcbObjRef; an_auto

theorem an_schedContextDonate (t p u : ObjRef) : IK (AN t) (schedContextDonate (Z := Unit) p u) := by
  unfold schedContextDonate; an_auto

/-- `RBk false`, TQ, and the thread read blocked. -/
abbrev MD (t : ObjRef) (s : State Unit) : Prop := RBk false s ∧ TQ s ∧ AN t s

theorem md_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : RBK false m) (h2 : TQK m)
    (h3 : IK (AN t) m) : IK (MD t) m :=
  fun σ h y hy => ⟨h1 σ h.1 y hy, h2 σ h.2.1 y hy, h3 σ h.2.2 y hy⟩

/-! ## The binding of the donated SC -/

theorem cq6_setObject {p : ObjRef} {o : KernelObject} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (setObject (Z := Unit) p o σ).1) :
    y.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  unfold setObject at hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨-, hs⟩ := mem_getObject hw
  obtain ⟨w1, w2⟩ := w
  simp only at hs; subst hs
  obtain ⟨z, ⟨-, rfl⟩, hy⟩ := hy
  obtain ⟨v, hv, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hv] at hy
  rw [Set.mem_singleton_iff.1 hy]

/-- Every thread bound to `p` is `t`. -/
abbrev BP (t p : ObjRef) (s : State Unit) : Prop :=
  ∀ y n u, s.kheap p = some (.schedContext y n) → y.scTcb = some u → u = t

theorem bp_threadSet (f : Tcb → Tcb) (q t p : ObjRef) : IK (BP t p) (threadSet (Z := Unit) f q) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => ?_
  intro h y hy
  rw [cq6_setObject hy]
  intro y' n u hk hu
  dsimp only at hk
  rw [Function.update_apply] at hk
  split at hk
  · cases hk
  · exact h y' n u hk hu

theorem bp_updTcb (p t : ObjRef) :
    PostK (BP t p) (updateSchedContext (Z := Unit) p (scTcbUpdate fun _ => some t)) := by
  intro σ y hy
  unfold updateSchedContext at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨-, hs⟩ := mem_getObject hz
  obtain ⟨o, z2⟩ := z
  simp only at hs; subst hs
  dsimp only at hy
  split at hy
  · rename_i sc n
    rw [cq6_setObject hy]
    intro y' n' u hk hu
    dsimp only at hk
    rw [Function.update_apply, if_pos rfl] at hk
    cases hk
    have e : (scTcbUpdate (fun _ => some t) sc).scTcb = some t := rfl
    rw [e] at hu; cases hu; rfl
  · exact hy.elim

/-- **`sched_context_donate p t`** binds `p` to `t`. -/
theorem bp_donate (p t : ObjRef) : PostK (BP t p) (schedContextDonate (Z := Unit) p t) := by
  unfold schedContextDonate
  exact post_bind fun _ => post_bind fun _ => post_bind_ik (bp_updTcb p t) fun _ => bp_threadSet _ _ _ _

/-! ## `sched_context_resume`, `maybe_donate_sc` -/

/-- **`sched_context_resume`** of an SC whose bound thread was read blocked
(the postponed thread is that one; everything before `postpone` reads). -/
theorem rbf_schedContextResume_p (sc : ObjRef) (σ : State Unit) (hT : TQ σ)
    (h : ∀ y n u, σ.kheap sc = some (.schedContext y n) → y.scTcb = some u → AN u σ) :
    IKp (RBk false) σ (schedContextResume (Z := Unit) sc) := by
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
  obtain ⟨h1, h2⟩ := h y' n' t' hk' ht'
  exact ⟨fun hc' => h2 (hc'.resolve_left (fun e => by cases e)), h1⟩

/-- **`maybe_donate_sc t n`** with `t` read blocked. -/
theorem md_maybeDonateSc (t n : ObjRef) : HK1 (MD t) (RBk false) (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc
  refine hk1_bind (R := MD t)
    (hk1_of_ik' (md_of (rb_getTcbObjRef _ _) (tq_getTcbObjRef _ _) (an_getTcbObjRef _ _ _))) fun scOpt => ?_
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
        have hvm : MD t v.2 :=
          md_of (rb_schedContextDonate _ _) (tq_schedContextDonate _ _) (an_schedContextDonate _ _ _) σ hσ v hv1
        have hvb : BP t p v.2 := bp_donate p t σ v hv1
        exact rbf_schedContextResume_p p v.2 hvm.2.1
          (fun y' n'' u hk' hu => by rw [hvb y' n'' u hk' hu]; exact hvm.2.2) hvm.1 y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1
  · rw [Set.mem_singleton_iff.1 hy]; exact hσ.1

/-! ## `send_signal` -/

theorem rbf_possibleSwitchTo (t : ObjRef) : RBK false (possibleSwitchTo (Z := Unit) t) :=
  fun σ => rb_possibleSwitchTo_p t σ (fun e => by cases e)

/-- The wake-up's tail after `maybe_donate_sc`. -/
theorem rbf_wakeTail (t : ObjRef) :
    RBK false (NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= fun _ =>
      getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun scopt =>
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) := by
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (rbf_possibleSwitchTo t)) fun _ =>
    ik_bind (rb_getTcbObjRef _ _) fun _ => ?_
  unfold ifSporadicCurScTestRefillUnblockCheck; rb_auto

/-- A blocked thread is woken (cancel / dequeue, Running, badge, donation,
then `possible_switch_to`). -/
theorem md_wake (t n : ObjRef) (b : Badge) (m : NonDet (State Unit) Unit) (hm : IK (MD t) m) :
    HK1 (MD t) (RBk false) (m >>= fun _ => setThreadState (Z := Unit) t .running >>= fun _ =>
      asUser (Z := Unit) t (setRegister badge_register b) >>= fun _ => maybeDonateSc (Z := Unit) t n >>= fun _ =>
      NonDet.gets (schedulable (Z := Unit) t) >>= fun sched =>
      NonDet.when (sched = true) (possibleSwitchTo (Z := Unit) t) >>= fun _ =>
      getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun scopt =>
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt) := by
  refine hk1_bind (hk1_of_ik' hm) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (md_of (rb_setThreadState _ _) (tqx_setThreadState_r _ _ rfl)
    (an_setThreadState _ _ _))) fun _ => ?_
  refine hk1_bind (hk1_of_ik' (md_of (rb_asUser _ _) (tqx_asUser _ _) (an_asUser _ _ _))) fun _ => ?_
  exact hk1_bind (md_maybeDonateSc t n) fun _ => hk1_of_ik' (rbf_wakeTail t)

theorem cq6_rnb {st : ThreadState} (h : receiveBlocked st = true) :
    runnable st = false ∧ st ≠ .idleThreadState := by
  revert h; cases st <;> simp [receiveBlocked, runnable]

/-- **`send_signal`** keeps `RBk false` (with SQ4, NtfnQB, idle in its idle state). -/
theorem rbf_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (hq : SQ4 σ) (hN : NtfnQB σ)
    (hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState) :
    IKp (RBk false) σ (sendSignal (Z := Unit) n b) := by
  unfold sendSignal
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, ez⟩ := SInvI.mem_getSimpleKo hz
  obtain ⟨ntfn, z2⟩ := z
  simp only at hk ez; subst z2
  revert hy
  refine (show IKp (RBk false) σ _ from ?_) hσ y
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
        have hA : AN tcb σ := an_of hq.1.2 h0.2 hI hx hr hni
        exact md_wake tcb n b _ (md_of (rb_cancelIpc _) (tq_cancelIpc _) (an_cancelIpc _ _)) σ
          ⟨h0, hq.1.1, hA⟩ y hy
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
    obtain ⟨x, hx, hs⟩ := hN n ntfn _ hk hm
    have hA : AN (the q.head?) σ := an_of hq.1.2 h0.2 hI hx (by rw [hs]; rfl) (by rw [hs]; exact fun e => by cases e)
    exact md_wake _ n b _ (md_of (rb_tcbNtfnDequeue _ _) (tq_tcbNtfnDequeue _ _) (an_tcbNtfnDequeue _ _ _)) σ
      ⟨h0, hq.1.1, hA⟩ y hy
  | activeNtfn b' => dsimp only; exact ikp_of_ik (by rb_auto) σ

/-! ## FL4's timer step and the tail -/

/-- The tail's bundle. -/
abbrev TW (N S : ObjRef) (s : State Unit) : Prop := SQ4 s ∧ RBk false s ∧ NQ [] s ∧ SInvI.VI N S false s

theorem tw_sendSignal (N S n : ObjRef) (b : Badge) : IK (TW N S) (sendSignal (Z := Unit) n b) := by
  intro σ h y hy
  have hI : ∀ x, σ.kheap σ.idleThread = some (.tcb x) → x.tcbState = .idleThreadState := fun x hx => by
    obtain ⟨y0, hy0, hs, -⟩ := SInvI.vi_idle h.2.2.2
    rw [hy0] at hx; cases hx; exact hs
  have hN : NtfnQB σ := by have := h.2.2.1; unfold NQ at this; exact this.1.1
  exact ⟨sq4_sendSignal n b σ h.1 y hy, rbf_sendSignal n b σ h.1 hN hI h.2.1 y hy,
    nq_sendSignal (Kq := []) n b σ h.2.2.1 y hy, SInvI.vi_sendSignal n b σ h.2.2.2 y hy⟩

theorem tw_fl4Awaken (N S : ObjRef) : IK (TW N S) (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    have h1' : TW N S σ1 := by
      rcases h1 with rfl | ⟨n, bd, hs⟩
      · exact ih
      · exact tw_sendSignal N S n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
    exact h1'

/-- **The tail of every kernel entry** carries RD: from SQ4, ValidIdle, NQ
[] and `RBk false` at the event's end, the exit gives EX and RB. -/
theorem rb_tail : HK1 (fun s => SQ4 s ∧ SInvI.ValidIdle s ∧ NQ [] s ∧ RBk false s) (fun s => EX s ∧ RB s)
    (fl4Awaken (Z := Unit) >>= fun _ => schedule >>= fun _ => activateThread) := by
  intro σ h y ⟨z, hz, hy⟩
  have hw := tw_fl4Awaken σ.idleThread σ.idleSc σ ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩ z hz
  have hv := validIdle_of_vi hw.2.2.2
  exact exR_exit z.2 ⟨aw_of hw.1.1 hw.1.2 hv, hw.2.1⟩ y hy

end

end Fl4Proofs.P3.SInvQ
