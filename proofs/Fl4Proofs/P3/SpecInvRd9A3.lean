/-
P3 (DESIGN.md §9), invariant line G1 (rd9, KENTRY-PLAN rd8a handoff 2, part 2):
**`aw_sendSignal`, `aw_fl4Awaken`** (rd8a's `hAw` proved) and the tops
`kcall_rdyOff9b` / `kentry_rdyOff9b` without it (spec side only).

The woken thread `t` of `send_signal` (the receive-blocked bound thread after
`cancel_ipc`, or the head of the notification queue) is either the current
thread `u` or not:
* `t = u`: `SR u` (RdL's `rd_maybeDonateSc_sr`) carried to the end
  (`sr_wake`), so `CtR`; under resume `u` was bound (HRC), so not donated to:
  its binding view is kept (`vw_wake` with `v ≠ some none`).
* `t ≠ u`: `u`'s binding view and, when bound to `c1`, `c1`'s refill view
  are kept (`vw_wake`; `NB t c1` from ScBackS: `c1`'s TCB is `u`), the
  release queue only grows, `u` is runnable afterwards only if it was before
  (`rnF`); so `CtR` transfers (`ctR_fin`).
RCA / HRC (`rh_fin`): resume afterwards ⇒ resume before (A1's `CW`), `u`'s
binding kept, `cur_sc` kept with its refill max (A1's `CW`), an SC by ScBackS
afterwards (sb's `si_sendSignal`).
-/
import Fl4Proofs.P3.SpecInvRd9A2
open Classical

namespace Fl4Proofs.P3.SInvR.A9
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-- send_signal's wake tail. -/
abbrev WT (t n : ObjRef) (b : Badge) : NonDet (State Unit) Unit := do
  setThreadState (Z := Unit) t .running
  asUser (Z := Unit) t <| setRegister badge_register b
  maybeDonateSc (Z := Unit) t n
  let sched ← NonDet.gets (schedulable t)
  NonDet.when sched <| possibleSwitchTo (Z := Unit) t
  let scopt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t
  ifSporadicCurScTestRefillUnblockCheck (Z := Unit) scopt

/-! ## The view along the wake tail -/

theorem vw_wake (t n : ObjRef) (b : Badge) (u c : ObjRef) (v : Option (Option ObjRef))
    (r : Option (List Refill × Nat × Option ObjRef)) (R0 : List ObjRef) (T0 : Time) (hv : t ≠ u ∨ v ≠ some none)
    (hr : r = none ∨ ∃ a m w, r = some (a, m, some w)) (s : State Unit) (hs : VW u c v r R0 T0 s)
    (hn : r = none ∨ NB t c s) : ∀ y ∈ (WT t n b s).1, VW u c v r R0 T0 y.2 := by
  intro y hy
  obtain ⟨z1, h1, hy⟩ := hy
  have v1 := vw_of (u := u) (c := c) (v := v) (r := r) (R0 := R0) (T0 := T0) (SVK.sv_setThreadState' t .running)
    (fun R => A8.rq_setThreadState R t .running) s hs z1 h1
  have n1 : r = none ∨ NB t c z1.2 := hn.imp id fun h => nb_of_sv (SVK.sv_setThreadState' t .running) t c s h z1 h1
  obtain ⟨z2, h2, hy⟩ := hy
  have v2 := vw_of (u := u) (c := c) (v := v) (r := r) (R0 := R0) (T0 := T0) (SVK.sv_asUser' t _)
    (fun R => rq_walk_asUser t _ R) z1.2 v1 z2 h2
  have n2 : r = none ∨ NB t c z2.2 := n1.imp id fun h => nb_of_sv (SVK.sv_asUser' t _) t c z1.2 h z2 h2
  obtain ⟨z3, h3, hy⟩ := hy
  obtain ⟨v3, nk3⟩ := vw_md t n u c v r R0 T0 hv hr z2.2 v2 z3 h3
  have n3 : r = none ∨ NB t c z3.2 := n2.imp id nk3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 h4
  obtain ⟨z5, h5, hy⟩ := hy
  have hk5 : VW u c v r R0 T0 z5.2 ∧ (r = none ∨ NB t c z5.2) := by
    revert h5; unfold NonDet.when; split_ifs
    · intro h5; exact ⟨vw_ktc t _ v3 z5 h5, n3.imp id fun h => nb_ktc t t c _ h z5 h5⟩
    · intro h5; rw [Set.mem_singleton_iff.1 h5]; exact ⟨v3, n3⟩
  obtain ⟨v5, n5⟩ := hk5
  obtain ⟨z6, h6, hy⟩ := hy
  unfold getTcbObjRef at h6
  obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
  exact vw_ifCond x6.tcbSchedContext _ _ u c v r R0 T0 (n5.symm.imp (fun h => h x6 hx6) id) z5.2 v5 y hy

/-! ## `u`'s runnability -/

/-- `u` runnable only if `Q`. -/
def rnF (u : ObjRef) (Q : Prop) : FQ where
  R p _ s := p = u → runnable s = true → Q
  clr _ _ _ h := h
  st _ _ _ _ _ h := by simp [runnable] at h
  dflt _ _ h := by simp [runnable] at h

abbrev RN (u : ObjRef) (Q : Prop) : State Unit → Prop := OPG (rnF u Q) Set.univ (fun _ => True)

theorem rn_init (u : ObjRef) (σ : State Unit) :
    RN u (∃ x, σ.kheap u = some (.tcb x) ∧ runnable x.tcbState = true) σ := by
  refine ⟨fun p o hp => ?_, trivial⟩
  cases o with
  | tcb x => exact fun e hr => by subst e; exact ⟨x, hp, hr⟩
  | notification nt => exact fun _ _ => Set.mem_univ _
  | _ => trivial

theorem rn_get {u : ObjRef} {Q : Prop} {s : State Unit} (h : RN u Q s) {x : Tcb} (hx : s.kheap u = some (.tcb x))
    (hr : runnable x.tcbState = true) : Q :=
  h.1 u _ hx rfl hr

theorem rn_wake (t n : ObjRef) (b : Badge) (u : ObjRef) (Q : Prop) (htu : t ≠ u) : IK (RN u Q) (WT t n b) := by
  refine ik_bind (fg_setThreadState _ _ fun _ _ _ e => absurd e htu) fun _ => ik_bind (fg_asUser _ _) fun _ =>
    ik_bind (fg_maybeDonateSc _ _) fun _ => ik_bind (ik_gets _) fun _ =>
    ik_bind (ik_when _ (fg_possibleSwitchTo _)) fun _ => ik_bind (fg_getTcbObjRef _ _) fun _ =>
    fg_ifCondRefillUnblockCheck _ _ _

/-! ## `SR` along the wake tail (the woken thread) -/

theorem of_sched {σ : State Unit} {t : ObjRef} (h : schedulable t σ = true) :
    ∃ x c y n, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c ∧ runnable x.tcbState = true ∧
      σ.kheap c = some (.schedContext y n) ∧ scActive y = true ∧ t ∉ σ.releaseQueue := by
  unfold schedulable at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rcases hk : σ.kheap t with _ | o
  · simp [optPred, optMapSome, tcbsOfKh, optMap, hk] at h1
  cases o
  case tcb x =>
    simp [optPred, optMapSome, tcbsOfKh, optMap, tcbOf, hk] at h1
    rcases hc : x.tcbSchedContext with _ | c
    · simp [optPred, optMap, tcbsOfKh, tcbOf, hk, hc] at h2
    rcases hkc : σ.kheap c with _ | o2
    · simp [optPred, optMap, tcbsOfKh, tcbOf, hk, hc, scsOfKh, hkc] at h2
    cases o2
    case schedContext y n =>
      simp [optPred, optMap, tcbsOfKh, tcbOf, hk, hc, scsOfKh, scOf, hkc] at h2
      exact ⟨x, c, y, n, rfl, hc, h1, hkc, h2, h3⟩
    all_goals simp [optPred, optMap, tcbsOfKh, tcbOf, hk, hc, scsOfKh, scOf, hkc] at h2
  all_goals simp [optPred, optMapSome, tcbsOfKh, optMap, tcbOf, hk] at h1

theorem sr_ktc (t' t : ObjRef) : IK (SR t) (possibleSwitchTo (Z := Unit) t') := by
  intro s hs y hy hsch
  obtain ⟨ek, et, er, -⟩ := ktc_possibleSwitchTo s.kheap s.curTime s.releaseQueue s.curThread t' s
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨x, c, z, n, hx, hc, hrun, hz, ha, hq⟩ := of_sched hsch
  rw [ek] at hx hz; rw [er] at hq
  obtain ⟨x', c', z', n', h1, h2, h3, h4, h5⟩ := hs (schedulable_of hx hc hrun hz ha hq)
  exact ⟨x', c', z', n', by rw [ek]; exact h1, h2, by rw [ek]; exact h3, h4, by rw [et]; exact h5⟩

/-- The SCs' refill max, backwards to `K`. -/
abbrev MB (K : ObjRef → Option KernelObject) (s : State Unit) : Prop :=
  ∀ q z n, s.kheap q = some (.schedContext z n) → ∃ z0, K q = some (.schedContext z0 n) ∧ z0.scRefillMax = z.scRefillMax

theorem mb_updSc (q : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, (f y).scRefillMax = y.scRefillMax)
    (K : ObjRef → Option KernelObject) : IK (MB K) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  intro p z n hz
  dsimp only at hz
  by_cases ep : p = q
  · subst ep; rw [Function.update_self] at hz; cases hz
    obtain ⟨z0, h0, hm⟩ := hs p y0 n0 hk
    exact ⟨z0, h0, hm.trans (hf y0).symm⟩
  · rw [Function.update_of_ne ep] at hz; exact hs p z n hz

theorem mb_ifCond (o : Option ObjRef) (a b : Option Bool) (K : ObjRef → Option KernelObject) :
    IK (MB K) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead
    updateRefillHd isRoundRobin getRefillHead
  repeat' (first | (refine mb_updSc _ _ ?_ K; intro _; rfl) | ik_step0 | ik_unfold)

theorem rq_ifCond (o : Option ObjRef) (a b : Option Bool) (R : List ObjRef) :
    IK (fun s : State Unit => s.releaseQueue = R) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  repeat' (first | (with_reducible exact rq_walk_refillUnblockCheck _ _) | ik_step0 | ik_unfold)

theorem sr_ifCond (o : Option ObjRef) (a b : Option Bool) (t : ObjRef) (s : State Unit) (hR : Rdy s) (h : SR t s) :
    ∀ y ∈ (ifCondRefillUnblockCheck (Z := Unit) o a b s).1, SR t y.2 := by
  intro y hy hsch
  obtain ⟨-, hfw, hbw⟩ := rd_ifCond o a b s hR hy
  obtain ⟨x, c, z, n, hx, hc, hrun, hz, ha, hq⟩ := of_sched hsch
  have hq0 : t ∉ s.releaseQueue := by rw [← rq_ifCond o a b s.releaseQueue s rfl y hy]; exact hq
  obtain ⟨z0, hz0, hm⟩ := mb_ifCond o a b s.kheap s (fun q z n h => ⟨z, h, rfl⟩) y hy c z n hz
  have ha0 : scActive z0 = true := by simp only [scActive] at ha ⊢; rw [hm]; exact ha
  exact hfw t (h (schedulable_of (hbw t x hx) hc hrun hz0 ha0 hq0))

/-- **The woken thread** ends `SR` (rd_wake's walk). -/
theorem sr_wake (t n : ObjRef) (b : Badge) (s : State Unit) (hs : Rdy s) {x : Tcb}
    (hx : s.kheap t = some (.tcb x)) (hRT : ∀ c, x.tcbSchedContext = some c → RdyT s t) :
    ∀ y ∈ (WT t n b s).1, SR t y.2 := by
  intro y hy
  obtain ⟨z1, h1, hy⟩ := hy
  have e1 : Rdy z1.2 := rd_setThreadState t .running trivial s hs z1 h1
  have v1 : SVK.SVS s z1.2 := SVK.sv_setThreadState' t .running s z1 h1
  have k1 := tcb_setThreadState hx h1
  obtain ⟨z2, h2, hy⟩ := hy
  have e2 : Rdy z2.2 := rd_asUser t _ z1.2 e1 z2 h2
  have v2 : SVK.SVS s z2.2 := v1.trans (SVK.sv_asUser' t _ z1.2 z2 h2)
  obtain ⟨hv2, -⟩ := fk_asUser (K := z1.2.kheap) (c := z1.2.curSc) (u := z1.2.consumedTime)
    (T := z1.2.curTime) (I := z1.2.idleThread) (S := z1.2.idleSc) t _ z1.2 (fk_self z1.2) z2 h2
  have hv := hv2 t
  rw [k1] at hv
  obtain ⟨x2, hx2, ex2⟩ := hv_tcb hv
  have hst2 : x2.tcbState = .running := hvT_st (x := { x with tcbState := .running }) ex2
  have hsc2 : x2.tcbSchedContext = x.tcbSchedContext := hvT_sc (x := { x with tcbState := .running }) ex2
  have hRT2 : ∀ c, x2.tcbSchedContext = some c → RdyT z2.2 t := fun c hc =>
    rdyT_svs (hRT c (hsc2 ▸ hc)) v2
  have hnb2 : ¬ BlkR x2.tcbState x2.tcbFault := not_blkR_run (Or.inl hst2)
  obtain ⟨z3, h3, hy⟩ := hy
  obtain ⟨e3, sr3⟩ := rd_maybeDonateSc_sr t n z2.2 e2 hx2 hnb2 hRT2 h3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 h4
  obtain ⟨z5, h5, hy⟩ := hy
  have k5 : Rdy z5.2 ∧ SR t z5.2 := by
    revert h5
    unfold NonDet.when
    split_ifs with hsch
    · intro h5
      exact ⟨rd_possibleSwitchTo_q t z3.2 (fun _ _ _ _ => sr3 hsch) e3 z5 h5, sr_ktc t t z3.2 sr3 z5 h5⟩
    · intro h5; rw [Set.mem_singleton_iff.1 h5]; exact ⟨e3, sr3⟩
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  exact sr_ifCond x6.tcbSchedContext (some false) (some false) t z5.2 k5.1 k5.2 y hy

/-! ## The core: one wake -/

/-- `CtR` for a fixed thread. -/
abbrev CtRf (u : ObjRef) (s : State Unit) : Prop :=
  ∀ x, s.kheap u = some (.tcb x) → runnable x.tcbState = true → ActB s u → u ∉ s.releaseQueue → RdyT s u

theorem ctRf_of_sr {u : ObjRef} {s : State Unit} (h : SR u s) : CtRf u s := by
  intro x hx hrun hA hn
  obtain ⟨x', c, y, n, h1, h2, h3, h4⟩ := hA
  rw [hx] at h1; cases h1
  exact h (schedulable_of hx h2 hrun h3 h4 hn)

/-- The wake of `t` from `z` (after the prefix), relative to `σ`. -/
theorem core (σ z : State Unit) (u t n : ObjRef) (b : Badge) (hR : Rdy z) (hS : SInvB.ScInv σ) (hSV : SVK.SVS σ z)
    (hrq : z.releaseQueue = σ.releaseQueue)
    (hRN : RN u (∃ x, σ.kheap u = some (.tcb x) ∧ runnable x.tcbState = true) z)
    (hC : CtRf u σ)
    (hH : σ.schedulerAction = .resumeCurThread → ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some σ.curSc)
    {x : Tcb} (hx : z.kheap t = some (.tcb x)) (hRT : ∀ c, x.tcbSchedContext = some c → RdyT z t) :
    ∀ y ∈ (WT t n b z).1, (σ.schedulerAction = .resumeCurThread →
      tvw (y.2.kheap u) = tvw (σ.kheap u)) ∧ CtRf u y.2 := by
  intro y hy
  have htz : tvw (z.kheap u) = tvw (σ.kheap u) := (vw_sv (hSV.1 u)).1
  have hxσ : ∃ x0, σ.kheap t = some (.tcb x0) ∧ x0.tcbSchedContext = x.tcbSchedContext := by
    have e := hSV.1 t; rw [hx] at e
    obtain ⟨x0, h0, e0⟩ := SVK.sv_tcb (o := σ.kheap t) e.symm
    exact ⟨x0, h0, e0⟩
  have hVt : VW u t (tvw (σ.kheap u)) none z.releaseQueue z.curTime z :=
    ⟨htz, by rw [hx]; rfl, fun _ h => h, rfl⟩
  by_cases htu : t = u
  · -- the woken thread is the current one
    subst u
    refine ⟨fun hres => ?_, ctRf_of_sr (sr_wake _ n b z hR hx hRT y hy)⟩
    have hv : tvw (σ.kheap t) ≠ some none := by
      obtain ⟨x0, h0, e0⟩ := hxσ
      rw [h0]; intro e; simp only [tvw, Option.some.injEq] at e
      rw [hH hres x0 h0] at e; cases e
    exact (vw_wake _ n b _ _ _ none _ _ (Or.inr hv) (Or.inl rfl) z hVt (Or.inl rfl) y hy).1
  · refine ⟨fun _ => (vw_wake t n b u t _ none _ _ (Or.inl htu) (Or.inl rfl) z hVt (Or.inl rfl) y hy).1, ?_⟩
    have hRNy := rn_wake t n b u _ htu z hRN y hy
    intro xy hxy hrun hA hn
    obtain ⟨x0, hx0, hr0⟩ := rn_get hRNy hxy hrun
    by_cases hb : ∃ c1, x0.tcbSchedContext = some c1
    · obtain ⟨c1, hc1⟩ := hb
      obtain ⟨y1, k1, hk1, hb1, -⟩ := hS.1.1 u x0 c1 hx0 hc1
      have hVc : VW u c1 (tvw (σ.kheap u)) (some (y1.scRefills, y1.scRefillMax, y1.scTcb)) σ.releaseQueue σ.curTime z :=
        ⟨htz, by rw [(vw_sv (hSV.1 c1)).2, hk1]; rfl, fun _ h => by rw [hrq]; exact h, hSV.2.1⟩
      have hNB : NB t c1 z := by
        intro x' hx' e
        rw [hx] at hx'; cases hx'
        obtain ⟨x0t, h0t, e0t⟩ := hxσ
        obtain ⟨y2, k2, hk2, hb2, -⟩ := hS.1.1 t x0t c1 h0t (e0t.trans e)
        rw [hk1] at hk2; cases hk2
        rw [hb1] at hb2; cases hb2; exact htu rfl
      obtain ⟨vt, vr, vq, vt'⟩ := vw_wake t n b u c1 _ _ _ _ (Or.inl htu) (Or.inr ⟨_, _, _, by rw [hb1]⟩) z hVc
        (Or.inr hNB) y hy
      -- the binding and the SC at the end
      rw [hxy, hx0] at vt; simp only [tvw, Option.some.injEq] at vt
      obtain ⟨xa, ca, za, na, ha1, ha2, ha3, ha4⟩ := hA
      rw [hxy] at ha1; cases ha1
      rw [vt, hc1] at ha2; cases ha2
      rw [ha3] at vr; simp only [rvw, Option.some.injEq, Prod.mk.injEq] at vr
      obtain ⟨er, em, -⟩ := vr
      have hA0 : ActB σ u := ⟨x0, c1, y1, k1, hx0, hc1, hk1, by simp only [scActive] at ha4 ⊢; rw [← em]; exact ha4⟩
      have hn0 : u ∉ σ.releaseQueue := fun h => hn (vq _ h)
      obtain ⟨x3, c3, y3, n3, h31, h32, h33, h34, h35⟩ := hC x0 hx0 hr0 hA0 hn0
      have ex : x0 = x3 := KernelObject.tcb.inj (Option.some.inj (hx0.symm.trans h31))
      have ec : c1 = c3 := Option.some.inj (hc1.symm.trans (ex ▸ h32))
      subst ec
      have ey : y1 = y3 := by
        rw [hk1] at h33; injection h33 with h; injection h with a _
      subst ey
      refine ⟨xy, c1, za, na, hxy, by rw [vt, hc1], ha3, ha4, ?_⟩
      rw [vt']; simp only [refillHd] at h35 ⊢; rw [er]; exact h35
    · obtain ⟨vt, -⟩ := vw_wake t n b u t _ none _ _ (Or.inl htu) (Or.inl rfl) z hVt (Or.inl rfl) y hy
      rw [hxy, hx0] at vt; simp only [tvw, Option.some.injEq] at vt
      obtain ⟨xa, ca, za, na, ha1, ha2, -⟩ := hA
      rw [hxy] at ha1; cases ha1
      exact absurd ⟨ca, vt ▸ ha2⟩ hb

/-! ## `send_signal` -/

/-- A step keeping the scheduler view, `cfS`, the release queue and every
TCB's runnability keeps RCA / CtR / HRC. -/
theorem aw_simple {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m)
    (h3 : ∀ R, IK (fun s : State Unit => s.releaseQueue = R) m) (h4 : ∀ u Q, IK (RN u Q) m)
    (σ : State Unit) (hA : A8.RCA σ) (hC : CtR σ) (hH : A8.HRC σ) :
    ∀ y ∈ (m σ).1, A8.RCA y.2 ∧ CtR y.2 ∧ A8.HRC y.2 := by
  intro y hy
  have hS := h1 σ y hy
  have hc := h2 σ y hy
  obtain ⟨m1, m2, -⟩ := A8.keep_svcf hS hc
  refine ⟨m1 hA, ?_, m2 hH⟩
  have et : y.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
  have hq := h3 σ.releaseQueue σ rfl y hy
  have hRN := h4 σ.curThread _ σ (rn_init σ.curThread σ) y hy
  intro x hx hrun hA' hn
  rw [et] at hx hA' hn ⊢
  obtain ⟨x0, hx0, hr0⟩ := rn_get hRN hx hrun
  rw [hq] at hn
  exact rdyT_svs (hC x0 hx0 hr0 (A8.actB_svs_back hA' hS) hn) hS

theorem rn_setNotification (n : ObjRef) (nt : Notification) (u : ObjRef) (Q : Prop) :
    IK (RN u Q) (setNotification (Z := Unit) n nt) :=
  fg_setSimpleKo _ _ _ fun _ _ => Set.mem_univ _

/-- RCA / HRC at the end of `send_signal`. -/
theorem rh_fin {σ y : State Unit} (hcf : cfS y = cfS σ) (hcw : A8.CP σ σ.curSc y) (hSy : SInvB.ScInv y)
    (hA : A8.RCA σ) (hH : A8.HRC σ)
    (htv : σ.schedulerAction = .resumeCurThread → tvw (y.kheap σ.curThread) = tvw (σ.kheap σ.curThread)) :
    A8.RCA y ∧ A8.HRC y := by
  have ec : y.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hcf
  have ei : y.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) hcf
  have ecs : y.curSc = σ.curSc := hcw.1
  refine ⟨fun hres hni => ?_, fun hres x hx => ?_⟩
  · have hres0 := hcw.2.2 hres
    rw [ec, ei] at hni
    obtain ⟨x0, c0, z0, n0, hx0, hc0, hz0, ha0⟩ := hA hres0 hni
    have hc0' : some c0 = some σ.curSc := hc0.symm.trans (hH hres0 x0 hx0)
    cases hc0'
    have e : tvw (y.kheap σ.curThread) = some x0.tcbSchedContext := by rw [htv hres0, hx0]; rfl
    obtain ⟨x, hx, hxs⟩ := tvw_tcb e
    rw [hc0] at hxs
    obtain ⟨z, k, hz, -, -⟩ := hSy.1.1 _ x _ hx hxs
    obtain ⟨z1, k1, hz1, -, hm⟩ := hcw.2.1 z k hz
    rw [hz0] at hz1; cases hz1
    rw [ec]
    exact ⟨x, σ.curSc, z, k, hx, hxs, hz, by simp only [scActive] at ha0 ⊢; rw [hm]; exact ha0⟩
  · have hres0 := hcw.2.2 hres
    rw [ec] at hx
    have e : some x.tcbSchedContext = tvw (σ.kheap σ.curThread) := by rw [← htv hres0, hx]; rfl
    obtain ⟨x0, hx0, hxs0⟩ := tvw_tcb e.symm
    rw [ecs, ← hxs0]; exact hH hres0 x0 hx0

theorem rq_cancelIpc_recv (t : ObjRef) (σ : State Unit) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) (hrb : receiveBlocked x.tcbState = true)
    {r : Unit × State Unit} (hr : r ∈ (cancelIpc (Z := Unit) t σ).1) : r.2.releaseQueue = σ.releaseQueue := by
  unfold cancelIpc at hr
  obtain ⟨z, hz, hr⟩ := hr
  unfold getThreadState at hz
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet hz
  rw [hx] at hx1; cases hx1
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain ⟨x2, -, e2⟩ := SInv.mem_threadSet hz2
  dsimp only at hr
  unfold receiveBlocked at hrb
  split at hrb
  · rename_i e rp d hst
    rw [hst] at hr
    have := rq_walk_blockedCancelIpc _ t rp z2.2.releaseQueue z2.2 rfl r hr
    rw [this, e2]
  · cases hrb

/-- **`send_signal` keeps `RCA ∧ CtR ∧ HRC`** (module docstring). -/
theorem aw_sendSignal (n : ObjRef) (b : Badge) (σ : State Unit) (hR : Rdy σ) (hN : SInv.NtfnQB σ)
    (hS : SInvB.ScInv σ) (hA : A8.RCA σ) (hC : CtR σ) (hH : A8.HRC σ) :
    ∀ y ∈ (sendSignal (Z := Unit) n b σ).1, A8.RCA y.2 ∧ CtR y.2 ∧ A8.HRC y.2 := by
  intro y hy
  have hcw := A8.cw_sendSignal n b σ hR y hy
  have hcf := cfk_sendSignal' n b σ y hy
  have hSy := SInvB.si_sendSignal n b σ hS y hy
  have ec : y.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hcf
  -- a wake from `z`: the core and the finish
  have fin : ∀ (z : State Unit) (t : ObjRef) (x : Tcb), Rdy z → SVK.SVS σ z → z.releaseQueue = σ.releaseQueue →
      RN σ.curThread (∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ runnable x.tcbState = true) z →
      z.kheap t = some (.tcb x) → (∀ c, x.tcbSchedContext = some c → RdyT z t) →
      y ∈ (WT t n b z).1 → A8.RCA y.2 ∧ CtR y.2 ∧ A8.HRC y.2 := by
    intro z t x hRz hSV hrq hRN hx hRT hyz
    obtain ⟨htv, hct⟩ := core σ z σ.curThread t n b hRz hS hSV hrq hRN hC hH hx hRT y hyz
    obtain ⟨h1, h2⟩ := rh_fin hcf hcw hSy hA hH htv
    refine ⟨h1, ?_, h2⟩
    show CtRf y.2.curThread y.2
    rw [ec]; exact hct
  have hsimple : ∀ nt, y ∈ (setNotification (Z := Unit) n nt σ).1 → A8.RCA y.2 ∧ CtR y.2 ∧ A8.HRC y.2 :=
    fun nt h => aw_simple (by sv_auto) (by cfk_leaf) (fun R => rq_walk_setNotification n nt R)
      (fun u Q => rn_setNotification n nt u Q) σ hA hC hH y h
  unfold sendSignal at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, e⟩ := SInv.mem_getSimpleKo hz
  obtain ⟨nt, z2⟩ := z
  simp only at hk e; subst z2
  dsimp only at hy
  cases h1 : nt.ntfnObj with
  | idleNtfn =>
    cases h2 : nt.ntfnBoundTcb with
    | none =>
      rw [h1, h2] at hy
      exact hsimple _ hy
    | some tcb =>
      rw [h1, h2] at hy
      obtain ⟨w, hw, hy⟩ := hy
      unfold getThreadState at hw
      obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hw
      dsimp only at hy
      split at hy
      · rename_i hrb
        obtain ⟨c1, hc1, hy⟩ := hy
        obtain ⟨hR1, hS1⟩ := rs_cancelIpc_recv tcb σ hR hx hrb hc1
        have hq1 := rq_cancelIpc_recv tcb σ hx hrb hc1
        have hRN1 := (fg_cancelIpc tcb : IK (RN σ.curThread _) _) σ (rn_init σ.curThread σ) c1 hc1
        have hblk : BlkR x.tcbState x.tcbFault := by
          unfold receiveBlocked at hrb
          split at hrb
          · rename_i e r d h; exact Or.inr (Or.inr ⟨e, r, d, h⟩)
          · cases hrb
        obtain ⟨x', hx', hRT'⟩ := rdyT_blk hR hx hblk hS1
        exact fin c1.2 tcb x' hR1 hS1 hq1 hRN1 hx' hRT' hy
      · exact hsimple _ hy
  | waitingNtfn queue =>
    rw [h1] at hy
    unfold updateWaitingNtfn at hy
    obtain ⟨z, ⟨hne, rfl⟩, hy⟩ := hy
    obtain ⟨z1, hz1, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 hz1
    obtain ⟨z2, hz2, hy⟩ := hy
    have hR2 := rd_tcbNtfnDequeue _ _ σ hR z2 hz2
    have hS2 := sv_tcbNtfnDequeue _ _ σ z2 hz2
    have hq2 := rq_walk_tcbNtfnDequeue _ _ σ.releaseQueue σ rfl z2 hz2
    have hRN2 := (fg_tcbNtfnDequeue _ _ : IK (RN σ.curThread _) _) σ (rn_init σ.curThread σ) z2 hz2
    have hmem : the queue.head? ∈ queue := by
      cases queue with
      | nil => exact absurd rfl hne
      | cons a l => exact List.mem_cons_self
    obtain ⟨x, hx, hst⟩ := hN n nt _ hk (by rw [h1]; exact hmem)
    obtain ⟨x2, hx2, hRT2⟩ := rdyT_blk hR hx (Or.inl ⟨n, hst⟩) hS2
    exact fin z2.2 _ x2 hR2 hS2 hq2 hRN2 hx2 hRT2 hy
  | activeNtfn badge' =>
    rw [h1] at hy
    exact hsimple _ hy

/-! ## `fl4Awaken` -/

/-- What the timer step carries, with this line's facts. -/
abbrev AW9 (s : State Unit) : Prop := A8.RO s ∧ SInvB.ScInv s ∧ A8.RCA s ∧ CtR s ∧ A8.HRC s

/-- **`RCA ∧ CtR ∧ HRC` (with `RO`, ScInv) kept by `fl4Awaken`** (rd8a's `hAw`). -/
theorem aw_fl4Awaken : IK AW9 (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | @tail b0 c0 _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · have hm : ((), σ1) ∈ (sendSignal (Z := Unit) n bd b0).1 := by rw [hs]; exact Set.mem_singleton _
      obtain ⟨hRO, hSc, hA, hC, hH⟩ := ih
      have hN : SInv.NtfnQB b0 := ((nq_nil_iff b0).1 hRO.2.2).1
      obtain ⟨a1, a2, a3⟩ := aw_sendSignal n bd b0 hRO.1 hN hSc hA hC hH ((), σ1) hm
      have r1 := A8.ro_sendSignal n bd b0 hRO ((), σ1) hm
      have r2 := SInvB.si_sendSignal n bd b0 hSc ((), σ1) hm
      exact ⟨r1, r2, a1, a2, a3⟩

/-! ## The tops without `hAw` -/

/-- rd8a's top with `TmoNR` (rd9) and `hAw` (rd9) discharged; `hSc`: sb2's
ScInv after the event part (the `hX` wiring's ScInv, KENTRY-PLAN rd9). -/
theorem kcall_rdyOff9b (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1,
      A8.SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hSc : ∀ y ∈ (A8.evRun rep ev σ).1, SInvB.ScInv y.2)
    (hX : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, A8.XS y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have hE : ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2 := by
    by_cases hs : ∃ c, ev = .syscallEvent c
    · obtain ⟨c, rfl⟩ := hs
      exact A8.ev_sys rep c σ (hEF c rfl) (A8.hCtRc_of (hEF c rfl) tmoNR) (hBody c rfl)
    · exact hEvO fun c e => hs ⟨c, e⟩
  refine A8.kcall_of_ev rep ev σ hE (fun y hy y2 hy2 => ?_) hX
  obtain ⟨⟨hR, hO, hA, hC, hH⟩, hN⟩ := hE y hy
  obtain ⟨-, -, a1, a2, a3⟩ := aw_fl4Awaken y.2 ⟨⟨hR, hO, hN⟩, hSc y hy, hA, hC, hH⟩ y2 hy2
  exact ⟨a1, a2, a3⟩

theorem kentry_rdyOff9b (rep : Bool) (c : Syscall) (σ : State Unit) (h : A8.EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ v ∈ (A8.front w.2).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1, A8.SS y.2 ∧ NQ [] y.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SInvB.ScInv y.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, A8.XS y2.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r ⟨y1, h1, hr⟩
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨hB, hSc, hX⟩ := hW w hw
  exact kcall_rdyOff9b rep _ w.2 (fun _ e => by cases e; exact A8.ef_fip h w hw) (fun _ e => by cases e; exact hB)
    (fun hne => absurd rfl (hne c)) hSc hX r hr

end

end Fl4Proofs.P3.SInvR.A9
