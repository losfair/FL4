/-
P3 (DESIGN.md §9), invariant line G1 (rd14b, KENTRY-PLAN rd13b handoff 1):
**the Endpoint perform arm** (spec side only).

* `TU σ0 q` (σ0's `cfS`, `CW`, ct unbound, the action not `resume_cur_thread`)
  and **`ss4_tu`** (`SS4` without `CB`: OS by the frame, `RCA` / `HRC`
  vacuous, `CtR` vacuous since ct is bound to no SC), `tu_post`;
  **`perfA_tbn3`**: rd13b's `perfA_tbn` with `TU` as a third `ok` case (the
  donation of ct's SC in NBSendRecv's send half: ct unbound, rescheduled).
* `EB t c` (`t` bound to `c` and `c` an SC, or `t` unbound and no resume):
  kept by every `SVS` step (`eb_svs`), by send_ipc's wake tail
  (`eb_wakeTail`), and **`eb_donate`**: `sched_context_donate p u` (`u ≠ t`,
  `t` current) from `t` bound: either `t` stays bound (`sc_tcb ≠ t`) or `t`
  is unbound and `test_reschedule t` reschedules.
* **`ep_sendIpc`** (send_ipc of a runnable current `t` bound to `c`: every
  outcome has `t` not runnable — blocked, called, made inactive — or `EB`),
  **`perfA_endpoint`**.
-/
import Fl4Proofs.P3.SpecInvRd14bA2
open Classical

namespace Fl4Proofs.P3.SInvR.A14b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The third end case -/

/-- ct unbound and no resume, with σ0's `cfS` and `CW`. -/
abbrev TU (σ0 q : State Unit) : Prop :=
  cfS q = cfS σ0 ∧ A8.CW σ0.curSc σ0 q ∧
    (∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = none) ∧
    q.schedulerAction ≠ .resumeCurThread

/-- **`TU` gives `SS4`.** -/
theorem ss4_tu {σ0 q : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (h : TU σ0 q) : A10.SS4 q := by
  obtain ⟨hc, hw, hn, hr⟩ := h
  refine ⟨os_cw hB hS hc hw, fun e => absurd e hr, fun x hx _ hA _ => ?_, fun e => absurd e hr⟩
  obtain ⟨x', c, y, n, h1, h2, -, -⟩ := hA
  rw [cf_curThread hc] at hx h1
  have ex : x' = x := KernelObject.tcb.inj (Option.some.inj (h1.symm.trans hx))
  subst ex
  rw [hn _ hx] at h2; cases h2

theorem tu_svcf {σ0 s s' : State Unit} (h : TU σ0 s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : TU σ0 s' := by
  refine ⟨hc.trans h.1, h.2.1.trans (A8.cw_of_svs hS), fun x hx => ?_, ?_⟩
  · have e := hS.1 σ0.curThread
    rw [hx] at e
    obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap σ0.curThread) (a := x.tcbSchedContext) e.symm
    rw [← hys]; exact h.2.2.1 y hy
  · rcases hS.2.2 with e | e
    · rw [e]; exact h.2.2.2
    · rw [e]; intro h'; cases h'

/-- **The post keeps `TU`.** -/
theorem tu_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : TU σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, TU σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := tu_svcf h (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    exact tu_svcf h1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-- **`perfA_tbn` with the third case `TU`.** -/
theorem perfA_tbn3 {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hS : Suff σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don oper).run s).1,
      (∀ a, y.1 = .ok a → TBN σ0 y.2 ∨ TU σ0 y.2) ∧
      (∀ e, y.1 = .error e → ∀ z ∈ (preemptionPath (Z := Unit) y.2).1, CB z.2 → A10.SS4 z.2)) :
    PerfA σ0 bl call don oper s := by
  intro y hy
  refine ⟨fun a ha => Or.inr fun q hq hc => ?_, (h y hy).2⟩
  rcases (h y hy).1 a ha with (ht | ⟨hc0, hw, hn⟩) | hu
  · exact ss4_tb hB hS (tb_post call a ht q hq) hc
  · rw [nr_post call a (cf_curThread hc0) hn q hq] at hc ⊢
    exact ss4_nrun hB hS hc0 hw hn hc
  · exact ss4_tu hB hS (tu_post call a hu q hq)

/-! ## Bound or unbound -/

/-- The TCB `t` is bound to no SC. -/
abbrev QN (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → x.tcbSchedContext = none

/-- The TCB `t` is runnable. -/
abbrev QRn (t : ObjRef) (p : ObjRef) (x : Tcb) : Prop := p = t → runnable x.tcbState = true

/-- The action is not `resume_cur_thread`. -/
abbrev NRes (s : State Unit) : Prop := s.schedulerAction ≠ .resumeCurThread

/-- `t` bound to `c` and `c` an SC, or `t` unbound and no resume. -/
abbrev EB (t c : ObjRef) (s : State Unit) : Prop :=
  (TP (QB t c) s ∧ KS c s) ∨ (TP (QN t) s ∧ NRes s)

theorem ebr_svs {t : ObjRef} {s s' : State Unit} (h : TP (QN t) s ∧ NRes s) (hS : SVK.SVS s s') :
    TP (QN t) s' ∧ NRes s' := by
  refine ⟨tp_svs (fun p x y e h' => by intro he; rw [← e]; exact h' he) hS h.1, ?_⟩
  unfold NRes
  rcases hS.2.2 with e | e
  · rw [e]; exact h.2
  · rw [e]; intro h'; cases h'

theorem eb_svs {t c : ObjRef} {s s' : State Unit} (h : EB t c s) (hS : SVK.SVS s s') : EB t c s' :=
  h.imp (fun h => bl_svs h hS) (fun h => ebr_svs h hS)

theorem eb_of_svm {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : SVK.SVM m) : IK (EB t c) m :=
  fun s hs y hy => eb_svs hs (h s y hy)

theorem ik_eb {t c : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : IK (BL t c) m)
    (h3 : IK (TP (QN t)) m) (h4 : IK NRes m) : IK (EB t c) m :=
  fun s hs y hy => hs.imp (fun h => h1 s h y hy) (fun h => ⟨h3 s h.1 y hy, h4 s h.2 y hy⟩)

theorem nres_setSchedulerAction (a : SchedulerAction) (ha : a ≠ .resumeCurThread) :
    IK NRes (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact ik_modify fun _ _ => ha

/-- The walk keeping `NRes` (every action written is not `resume_cur_thread`). -/
macro "nres_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine nres_setSchedulerAction _ ?_); intro h; cases h)
  | ik_step0 | ik_unfold))

theorem qn_stab (t : ObjRef) : ∀ p x y, y.tcbSchedContext = x.tcbSchedContext → QN t p y → QN t p x :=
  fun _ _ _ e h he => by rw [← e]; exact h he

theorem qn_of_fk {t : ObjRef} {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ K c u T I S, IK (SInvR.FK K c u T I S) m) : IK (TP (QN t)) m :=
  ik_of_fk (fun _ _ hk h' => tp_hv (qn_stab t) hk h') h

theorem qn_possibleSwitchTo (t u : ObjRef) : IK (TP (QN t)) (possibleSwitchTo (Z := Unit) u) :=
  qn_of_fk fun _ _ _ _ _ _ => SInvR.fk_possibleSwitchTo _ _ _ _ _ _ u

theorem nres_possibleSwitchTo (u : ObjRef) : IK NRes (possibleSwitchTo (Z := Unit) u) :=
  SInvR.nr_possibleSwitchTo u

theorem qn_ifCond (t : ObjRef) (o : Option ObjRef) :
    IK (TP (QN t)) (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) :=
  ik_of_nks (fun _ _ hk h' => tp_sok hk h') (nks_ifCond o)

/-- Every outcome keeps the scheduler action (VsDom's generic field family). -/
abbrev AK {α : Type} (m : NonDet (State Unit) α) : Prop := Vs.FK (fun s : State Unit => s.schedulerAction) m

theorem ak_setObject (p : ObjRef) (o : KernelObject) : AK (setObject (Z := Unit) p o) := by
  unfold setObject
  refine Vs.dk_bind (Vs.dk_getObject _) fun _ => Vs.dk_bind (Vs.dk_assert _) fun _ => ?_
  exact Vs.dk_get_put fun _ => rfl

theorem ak_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    AK (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  refine Vs.dk_bind (Vs.dk_getObject _) fun o => ?_
  cases o with
  | schedContext y n => exact ak_setObject _ _
  | _ => exact Vs.dk_fail

theorem ak_getSchedContext (p : ObjRef) : AK (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine Vs.dk_bind (Vs.dk_getObject _) fun o => ?_
  cases o <;> first | exact Vs.dk_pure _ | exact Vs.dk_fail

macro "ak_step" : tactic => `(tactic| first
  | exact ak_updateSchedContext _ _ | exact ak_getSchedContext _
  | exact Vs.dk_pure _ | exact Vs.dk_pure' _ | exact Vs.dk_fail | exact Vs.dk_gets _ | exact Vs.dk_get
  | exact Vs.dk_assert _ | exact Vs.dk_assertOpt _ | exact Vs.dk_getsThe _ | exact Vs.dk_getObject _
  | (apply Vs.dk_modify; intro _; rfl)
  | (apply Vs.dk_when) | (apply Vs.dk_ite)
  | (apply Vs.dk_whileLoop; intro _)
  | (refine Vs.dk_bind ?_ (fun _ => ?_))
  | split)

theorem ak_refillUnblockCheck (p : ObjRef) : AK (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead getRefillHead updateRefillHd
  repeat ak_step

theorem nres_ifCond (o : Option ObjRef) : IK NRes (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  have h : AK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
    unfold ifSporadicCurScTestRefillUnblockCheck ifCondRefillUnblockCheck
    cases o with
    | none => exact Vs.dk_pure' _
    | some p =>
      unfold NonDet.maybeM
      repeat (first | exact ak_refillUnblockCheck _ | ak_step)
  intro σ hσ x hx
  have e : x.2.schedulerAction = σ.schedulerAction := h σ x hx
  show x.2.schedulerAction ≠ _
  rw [e]; exact hσ

theorem qn_rescheduleRequired (t : ObjRef) : IK (TP (QN t)) (rescheduleRequired (Z := Unit)) :=
  qn_of_fk fun _ _ _ _ _ _ => SInvR.fk_rescheduleRequired _ _ _ _ _ _

theorem fk_testReschedule (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef)
    (t : ObjRef) : IK (SInvR.FK K c u T I S) (testReschedule (Z := Unit) t) := by
  unfold testReschedule
  repeat' (first | (with_reducible exact SInvR.fk_rescheduleRequired _ _ _ _ _ _) | ik_step0 | ik_unfold)

/-- send_ipc's wake tail keeps `EB`. -/
theorem eb_wakeTail (t c dest : ObjRef) : IK (EB t c) (do
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) :=
  ik_bind (eb_of_svm (SVK.sv_setThreadState' _ _)) fun _ =>
    ik_bind (eb_of_svm (by unfold getTcbObjRef; sv_auto)) fun o =>
      ik_bind (ik_eb (bl_ifCond t c o) (qn_ifCond t o) (nres_ifCond o)) fun _ =>
        ik_eb (bl_possibleSwitchTo t c dest) (qn_possibleSwitchTo t dest) (nres_possibleSwitchTo dest)

/-- `test_reschedule t` of the current `t`: unbound kept, rescheduled. -/
theorem qnr_testReschedule (t : ObjRef) (σ : State Unit) (hct : σ.curThread = t) (hq : TP (QN t) σ) :
    ∀ y ∈ (testReschedule (Z := Unit) t σ).1, TP (QN t) y.2 ∧ NRes y.2 := by
  unfold testReschedule
  intro y hy
  obtain ⟨z1, hz1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz1] at hy
  obtain ⟨z2, hz2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz2] at hy
  obtain ⟨z3, hz3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hz3] at hy
  dsimp only at hy
  unfold NonDet.when at hy
  rw [if_pos (Or.inl hct.symm)] at hy
  refine ⟨qn_rescheduleRequired t σ hq y hy, fun e => ?_⟩
  rw [rescheduleRequired_cn σ y hy] at e; cases e

set_option maxHeartbeats 2000000 in
/-- **`sched_context_donate p u`** (`u ≠ t`, `t` current and bound to `c`) ends in `EB`. -/
theorem eb_donate (t c p u : ObjRef) (σ : State Unit) (hne : u ≠ t) (hct : σ.curThread = t)
    (h : TP (QB t c) σ ∧ KS c σ) : ∀ y ∈ (schedContextDonate (Z := Unit) p u σ).1, EB t c y.2 := by
  intro y hy
  unfold schedContextDonate at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨ez, scv, n, hk, hv⟩ := cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at ez hv; subst z2; subst z1
  obtain ⟨w, hw, hy⟩ := hy
  have tail : IK (EB t c) (do
      setScObjRef (Z := Unit) scTcbUpdate p (some u)
      setTcbObjRef (Z := Unit) tcbSchedContextUpdate u (some p)) :=
    ik_eb (SInv.ik_and (ik_bind (by qb_auto) fun _ => tp_threadSet _ _ fun _ _ e => absurd e hne) (by ks_auto))
      (ik_bind (by qb_auto) fun _ => tp_threadSet _ _ fun _ _ e => absurd e hne) (by nres_auto)
  refine tail w.2 ?_ y hy
  unfold NonDet.when at hw
  split at hw
  · obtain ⟨a1, ha1, hw⟩ := hw
    obtain ⟨-, ea2⟩ := cq5_mem_assertOpt ha1
    rw [ea2] at hw
    obtain ⟨f, a12⟩ := a1
    dsimp only at hw
    by_cases hf : f = t
    · subst hf
      obtain ⟨a2, ha2, hw⟩ := hw
      obtain ⟨a3, ha3, hw⟩ := hw
      obtain ⟨a4, ha4, hw⟩ := hw
      have c2 : a2.2.curThread = f :=
        (congrArg (fun q => q.2.2) (Vs.dk_tcbSchedAction' tcbSchedDequeue f σ a2 ha2)).trans hct
      have c3 : a3.2.curThread = f :=
        (congrArg (fun q => q.2.2) (Vs.dk_tcbReleaseRemove' f a2.2 a3 ha3)).trans c2
      obtain ⟨x, -, e4⟩ := SInv.mem_threadSet ha4
      have c4 : a4.2.curThread = f := by rw [e4]; exact c3
      have hq4 : TP (QN f) a4.2 := by
        intro p x' hp ep
        subst ep
        rw [e4] at hp
        simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hp
        subst hp; rfl
      exact Or.inr (qnr_testReschedule f a4.2 c4 hq4 w hw)
    · obtain ⟨a2, ha2, hw⟩ := hw
      obtain ⟨a3, ha3, hw⟩ := hw
      obtain ⟨a4, ha4, hw⟩ := hw
      have b2 := bl_of_fk (t := t) (c := c) (fun _ _ _ _ _ _ => SInvR.fk_tcbSchedAction _ _ _ _ _ _ _ f)
        σ h a2 ha2
      have b3 := bl_of_fk (t := t) (c := c) (fun _ _ _ _ _ _ => SInvR.fk_tcbReleaseRemove _ _ _ _ _ _ f)
        a2.2 b2 a3 ha3
      have q4 := (tp_threadSet (Q := QB t c) (tcbSchedContextUpdate fun _ => none) f
        fun _ _ e => absurd e hf) a3.2 b3.1 a4 ha4
      have k4 := (by ks_auto : IK (KS c) (setTcbObjRef (Z := Unit) tcbSchedContextUpdate f none)) a3.2 b3.2 a4 ha4
      exact Or.inl (bl_of_fk (fun _ _ _ _ _ _ => fk_testReschedule _ _ _ _ _ _ f) a4.2 ⟨q4, k4⟩ w hw)
  · rw [Set.mem_singleton_iff.1 hw]; exact Or.inl h

/-! ## `send_ipc` -/

theorem sv_maybeUnlink (d : ObjRef) (r : Option ObjRef) :
    SVK.SVM (NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) r) := by
  cases r with
  | none => unfold NonDet.maybeM; sv_auto
  | some r => unfold NonDet.maybeM; exact SVK.sv_replyUnlinkTcb d r

theorem cfk_maybeUnlink (d : ObjRef) (r : Option ObjRef) :
    CFK (NonDet.maybeM (replyUnlinkTcb (Z := Unit) d) r) := by
  cases r with
  | none => unfold NonDet.maybeM; cfk_auto
  | some r => unfold NonDet.maybeM; exact cfk_replyUnlinkTcb' d r

/-- **`send_ipc` of the runnable current thread `t` bound to `c`**: every
outcome has `t` not runnable or `EB t c`. -/
theorem ep_sendIpc (bl cl : Bool) (bd : Badge) (g gr dn : Bool) (t c ep : ObjRef) (σ : State Unit)
    (hct : σ.curThread = t) (hr : TP (QRn t) σ) (hb : TP (QB t c) σ ∧ KS c σ) :
    ∀ y ∈ (sendIpc (Z := Unit) bl cl bd g gr dn t ep σ).1, A9.NO t y.2 ∨ EB t c y.2 := by
  unfold sendIpc
  intro y ⟨e, he, hy⟩
  obtain ⟨hk, hs⟩ := mem_getSimpleKo he
  obtain ⟨ev, σ1⟩ := e
  simp only at hk hs; subst hs
  cases ev with
  | idleEP =>
    cases bl with
    | true => exact Or.inl (A9.no_sendIpcBlocked t ep bd g gr cl _ y hy)
    | false =>
      have ey : y = ((), σ1) := hy
      subst ey; exact Or.inr (Or.inl hb)
  | sendEP q =>
    cases bl with
    | true => exact Or.inl (A9.no_sendIpcBlocked t ep bd g gr cl _ y hy)
    | false =>
      have ey : y = ((), σ1) := hy
      subst ey; exact Or.inr (Or.inl hb)
  | recvEP l =>
    cases l with
    | nil => exact hy.elim
    | cons dest q =>
      obtain ⟨z1, hz1, hy⟩ := hy
      have hS1 := sv_tcbEpDequeue dest ep σ1 z1 hz1
      have hc1 := cfk_tcbEpDequeue' dest ep σ1 z1 hz1
      have hR1 : TP (QRn t) z1.2 :=
        (by unfold tcbEpDequeue; qb_auto : IK (TP (QRn t)) (tcbEpDequeue (Z := Unit) dest ep)) σ1 hr z1 hz1
      obtain ⟨z2, hz2, hy⟩ := hy
      unfold getThreadState at hz2
      obtain ⟨xd, hxd, rfl⟩ := mem_threadGet hz2
      dsimp only at hy
      cases hst : xd.tcbState with
      | blockedOnReceive ep' reply dd =>
        have hne : dest ≠ t := by
          intro e; subst e
          have h2 := hR1 dest xd hxd rfl
          rw [hst] at h2; simp [runnable] at h2
        rw [hst] at hy
        obtain ⟨z3, hz3, hy⟩ := hy
        rw [Set.mem_singleton_iff.1 hz3] at hy
        obtain ⟨z4, hz4, hy⟩ := hy
        have hS4 := SVK.sv_doIpcTransfer' t (some ep) bd g dest z1.2 z4 hz4
        have hc4 := cfk_doIpcTransfer' t (some ep) bd g dest z1.2 z4 hz4
        obtain ⟨z5, hz5, hy⟩ := hy
        have hS5 := sv_maybeUnlink dest reply z4.2 z5 hz5
        have hc5' := cfk_maybeUnlink dest reply z4.2 z5 hz5
        have hc5 : z5.2.curThread = t := by rw [cf_curThread (hc5'.trans (hc4.trans hc1)), hct]
        have hL5 : TP (QB t c) z5.2 ∧ KS c z5.2 := bl_svs (bl_svs (bl_svs hb hS1) hS4) hS5
        obtain ⟨z6, hz6, hy⟩ := hy
        unfold getTcbObjRef at hz6
        obtain ⟨x6, -, rfl⟩ := mem_threadGet hz6
        obtain ⟨z7, hz7, hy⟩ := hy
        obtain ⟨xt, hxt, rfl⟩ := mem_threadGet hz7
        dsimp only at hy
        split at hy
        · split at hy
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact Or.inl (A9.no_wakeTail t dest hne z8.2 (A9.no_replyPush t dest _ dn _ z8 hz8) y hy)
          · obtain ⟨z8, hz8, hy⟩ := hy
            exact Or.inl (A9.no_wakeTail t dest hne z8.2 (A9.no_sts t _ (by rfl) hz8) y hy)
        · obtain ⟨z8, hz8, hy⟩ := hy
          refine Or.inr (eb_wakeTail t c dest z8.2 ?_ y hy)
          unfold NonDet.when at hz8
          split at hz8
          · obtain ⟨z9, hz9, hz8⟩ := hz8
            unfold getTcbObjRef at hz9
            obtain ⟨x9, -, rfl⟩ := mem_threadGet hz9
            exact eb_donate t c _ dest z5.2 hne hc5 hL5 z8 hz8
          · rw [Set.mem_singleton_iff.1 hz8]; exact Or.inl hL5
      | _ => rw [hst] at hy; obtain ⟨_, h, _⟩ := hy; exact h.elim

/-! ## The arm -/

/-- **The Endpoint arm** (every blocking / call / donation outcome). -/
theorem perfA_endpoint {σ0 s : State Unit} (ep : ObjRef) (badge : Word) (g gr : Bool) {bl call don : Bool}
    (hB : A10.BS σ0) (hS : Suff σ0) (hK : A11.KP σ0 s)
    (hbd : ∀ x, s.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc)
    (hsc : ∃ y n, s.kheap σ0.curSc = some (.schedContext y n))
    (hr : ∀ x, s.kheap σ0.curThread = some (.tcb x) → x.tcbState = .restart) :
    PerfA σ0 bl call don (.invokeEndpoint ep badge g gr) s := by
  refine perfA_tbn3 hB hS fun y hy => ?_
  have hy' : y ∈ ((withoutPreemption (do
      let thread ← NonDet.gets fun s : State Unit => s.curThread
      sendIpc (Z := Unit) bl call badge g gr don thread ep
      return ([] : List Data))).run s).1 := hy
  unfold withoutPreemption at hy'
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy'
  refine ⟨fun _ _ => ?_, fun _ h => by cases h⟩
  obtain ⟨g1, hg1, hw⟩ := hw
  obtain rfl := mem_gets hg1
  obtain ⟨w2, hw2, hw⟩ := hw
  have ew : w.2 = w2.2 := by rw [Set.mem_singleton_iff.1 hw]
  dsimp only at hw2
  have et : s.curThread = σ0.curThread := A11.kp_curThread hK
  rw [et] at hw2
  have hcf := (cfk_sendIpc' bl call badge g gr don σ0.curThread ep s w2 hw2).trans hK.1
  have hcw :=
    (A11b.cp_sendIpc bl call badge g gr don σ0.curThread ep σ0 σ0.curSc s ⟨A11.kp_curSc hK, hK.2.1⟩ w2 hw2).2
  dsimp only
  rw [ew]
  rcases ep_sendIpc bl call badge g gr don σ0.curThread σ0.curSc ep s et
      (fun p x hx e => by subst e; simp [hr x hx, runnable])
      ⟨fun p x hx e => by subst e; exact hbd x hx, hsc⟩ w2 hw2 with hn | (⟨hq, hk⟩ | ⟨hq, hna⟩)
  · exact Or.inl (Or.inr ⟨hcf, hcw, by rw [cf_curThread hcf]; exact A9.nrun_of_no hn⟩)
  · exact Or.inl (Or.inl ⟨hcf, hcw, fun x hx => hq _ x hx rfl, hk⟩)
  · exact Or.inr ⟨hcf, hcw, fun x hx => hq _ x hx rfl, hna⟩

end

end Fl4Proofs.P3.SInvR.A14b
