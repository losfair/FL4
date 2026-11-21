/-
P3 (DESIGN.md §9), invariant line G1 (rd11a, KENTRY-PLAN rd10 handoff 1):
**the pinned body frame `KP`** for `OsBody` (spec side only).

* **`KP σ0 s`** (σ0 = the body's start): `cfS` kept, rd8a's `CW` at
  `σ0.curSc` (its refills / refill max kept, resume not set), and **`RS`**:
  under resume the scheduler views (`SVK.sv`) of `σ0.curThread` and
  `σ0.curSc` are those of σ0 (a writer of ct's binding or of cur_sc's TCB
  reschedules first: maybe_return_sc of ct, the donation of ct's SC).
* Kit: `kp_step` (one step from its three facts), **`ik_kp`** (any
  `SVM ∧ CFK` step), `kp_leaf` / `kp_auto` (rd8a's `cp_leaf` shape),
  hand leaves `kp_possibleSwitchTo`, `kp_maybeReturnSc` (the thread is
  `σ0.curThread`), `kp_cancelIpc` (rd8e's `sv_cancelIpc'`; rd13a: the
  duplicate `sv_cancelIpc` dropped, `rescheduleRequired_cnA` (ScAwaken) in
  place of ScMidCur's, so this module is outside the JointAt cone).
* The end: **`offReady_kp`**, **`ss4_of_kp`** (`BS σ0 ∧ Suff σ0 ∧ KP σ0 s ∧
  CtR s ⇒ SS4 s`), **`ctR_kp`** (ct unbound or bound to cur_sc ⇒ CtR).
-/
import Fl4Proofs.P3.SpecInvRd10A3
import Fl4Proofs.P3.SpecInvRd8eA
open Classical

namespace Fl4Proofs.P3.SInvR.A11
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The pinned frame -/

/-- Under resume, ct's and cur_sc's scheduler views are σ0's. -/
abbrev RS (σ0 s : State Unit) : Prop :=
  s.schedulerAction = .resumeCurThread →
    SVK.sv (s.kheap σ0.curThread) = SVK.sv (σ0.kheap σ0.curThread) ∧
      SVK.sv (s.kheap σ0.curSc) = SVK.sv (σ0.kheap σ0.curSc)

/-- **The body frame** pinned at the body's start σ0. -/
abbrev KP (σ0 s : State Unit) : Prop := cfS s = cfS σ0 ∧ A8.CW σ0.curSc σ0 s ∧ RS σ0 s

theorem KP.refl (σ0 : State Unit) : KP σ0 σ0 := ⟨rfl, A8.CW.refl _ _, fun _ => ⟨rfl, rfl⟩⟩

theorem kp_curSc {σ0 s : State Unit} (h : KP σ0 s) : s.curSc = σ0.curSc := congrArg (fun p => p.2.1) h.1

theorem kp_curThread {σ0 s : State Unit} (h : KP σ0 s) : s.curThread = σ0.curThread :=
  congrArg (fun p => p.2.2.1) h.1

/-- One step from its three facts. -/
theorem kp_step {σ0 s s' : State Unit} (h : KP σ0 s) (hc : cfS s' = cfS s) (hw : A8.CW s.curSc s s')
    (hv : s'.schedulerAction = .resumeCurThread → SVK.sv (s'.kheap σ0.curThread) = SVK.sv (s.kheap σ0.curThread) ∧
      SVK.sv (s'.kheap σ0.curSc) = SVK.sv (s.kheap σ0.curSc)) : KP σ0 s' := by
  rw [kp_curSc h] at hw
  refine ⟨hc.trans h.1, h.2.1.trans hw, fun e => ?_⟩
  obtain ⟨a, b⟩ := hv e
  obtain ⟨a', b'⟩ := h.2.2 (hw.2 e)
  exact ⟨a.trans a', b.trans b'⟩

/-- CW from a CP lemma (instantiated at the step's start). -/
theorem cw_of_cp {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ0 c, IK (A8.CP σ0 c) m) {s : State Unit}
    {y : α × State Unit} (hy : y ∈ (m s).1) : A8.CW s.curSc s y.2 :=
  (h s s.curSc s ⟨rfl, A8.CW.refl _ _⟩ y hy).2

/-- **Any `SVM ∧ CFK` step keeps `KP`.** -/
theorem ik_kp {α : Type} {m : NonDet (State Unit) α} (h1 : SVK.SVM m) (h2 : CFK m) (σ0 : State Unit) :
    IK (KP σ0) m := by
  intro s hs y hy
  have hS := h1 s y hy
  exact kp_step hs (h2 s y hy) (A8.cw_of_svs hS) fun _ => ⟨hS.1 _, hS.1 _⟩

syntax "kp_leaf" : tactic
macro_rules | `(tactic| kp_leaf) => `(tactic| fail "no kp_leaf")
macro_rules | `(tactic| kp_leaf) => `(tactic|
  (refine ik_kp ?_ ?_ _ <;> first | (sv_auto; done) | (cfk_auto; done)))

macro "kp_auto" : tactic => `(tactic| repeat' (first | kp_leaf | ik_step0))

/-! ## Hand leaves -/

theorem kp_possibleSwitchTo (t : ObjRef) (σ0 : State Unit) : IK (KP σ0) (possibleSwitchTo (Z := Unit) t) := by
  intro s hs y hy
  have ek := (ktc_possibleSwitchTo s.kheap s.curTime s.releaseQueue s.curThread t s ⟨rfl, rfl, rfl, rfl⟩ y hy).1
  exact kp_step hs (by refine (?_ : CFK _) s y hy; cfk_auto) (cw_of_cp (A8.cp_possibleSwitchTo t) hy) fun _ => by rw [ek]; exact ⟨rfl, rfl⟩
macro_rules | `(tactic| kp_leaf) => `(tactic| with_reducible exact kp_possibleSwitchTo _ _)

theorem kp_cancelIpc (t : ObjRef) (σ0 : State Unit) : IK (KP σ0) (cancelIpc (Z := Unit) t) :=
  ik_kp (B8e.sv_cancelIpc' t) (by cfk_leaf) σ0
macro_rules | `(tactic| kp_leaf) => `(tactic| with_reducible exact kp_cancelIpc _ _)

theorem cfk_maybeReturnSc (n t : ObjRef) : CFK (maybeReturnSc (Z := Unit) n t) := by
  unfold maybeReturnSc; cfk_auto

/-- **`maybe_return_sc` of the current thread**: unbinding it reschedules. -/
theorem kp_maybeReturnSc (n : ObjRef) (σ0 : State Unit) :
    IK (KP σ0) (maybeReturnSc (Z := Unit) n σ0.curThread) := by
  intro s hs y hy
  have hcp : ∀ σ1 c, IK (A8.CP σ1 c) (maybeReturnSc (Z := Unit) n σ0.curThread) := by
    intro σ1 c; unfold maybeReturnSc; cp_auto
  refine kp_step hs (cfk_maybeReturnSc n _ s y hy) (cw_of_cp hcp hy) fun hres => ?_
  have hc := cfk_maybeReturnSc n _ s y hy
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
  · exfalso
    obtain ⟨z3, h3, hy⟩ := hy
    obtain ⟨z4, h4, hy⟩ := hy
    obtain ⟨z5, h5, hy⟩ := hy
    obtain ⟨z6, h6, hy⟩ := hy
    obtain rfl := Set.mem_singleton_iff.1 h6
    dsimp only at hy
    have c3 : cfS z3.2 = cfS s := by refine (?_ : CFK _) s z3 h3; cfk_auto
    have c4 : cfS z4.2 = cfS z3.2 := by refine (?_ : CFK _) z3.2 z4 h4; cfk_auto
    have c5 : cfS z5.2 = cfS z4.2 := by refine (?_ : CFK _) z4.2 z5 h5; cfk_auto
    have et : z5.2.curThread = σ0.curThread := by
      have := congrArg (fun p => p.2.2.1) ((c5.trans c4).trans (c3.trans hs.1)); exact this
    rw [if_pos et.symm] at hy
    have := rescheduleRequired_cnA hy
    rw [this] at hres; cases hres
  · obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨rfl, rfl⟩

/-! ## The end of the body -/

theorem offReady_kp {σ0 s : State Unit} (hO : Sched.OffReady σ0) (hK : KP σ0 s) : Sched.OffReady s := by
  obtain ⟨hc, hw, -⟩ := hK
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨e1, e2, -, -, -, e6⟩ := hc
  intro y n hy
  rw [e2] at hy
  obtain ⟨y0, n0, hy0, er, -⟩ := hw.1 y n hy
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  rw [e1, e6, hh]; exact hO y0 n0 hy0

/-- ct's binding under resume (σ0's: bound to cur_sc by CurScT). -/
theorem kp_bind {σ0 s : State Unit} (h : A10.BS σ0) (hK : KP σ0 s) (hr : s.schedulerAction = .resumeCurThread) :
    ∃ x, s.kheap s.curThread = some (.tcb x) ∧ x.tcbSchedContext = some s.curSc := by
  obtain ⟨xt, hct, -⟩ := h.ct
  have hb := h.cs xt hct
  have e := (hK.2.2 hr).1
  rw [hct] at e
  simp only [SVK.sv, hb] at e
  obtain ⟨x, hx, hxb⟩ := SVK.sv_tcb e
  rw [kp_curThread hK, kp_curSc hK]
  exact ⟨x, hx, hxb⟩

/-- **`SS4` at a state of the body** from the body's start facts, `KP` and CtR. -/
theorem ss4_of_kp {σ0 s : State Unit} (h : A10.BS σ0) (hs : Suff σ0) (hK : KP σ0 s) (hC : CtR s) : A10.SS4 s := by
  refine ⟨os_frame (Or.inl ⟨h.off, hs⟩) ⟨hK.1, fun y n hy => ?_, hK.2.1.2⟩, fun hr hni => ?_, hC, fun hr x hx => ?_⟩
  · rw [kp_curSc hK] at hy; exact hK.2.1.1 y n hy
  · obtain ⟨x, hx, hxb⟩ := kp_bind h hK hr
    obtain ⟨xa, c0, z, n, hxa, hca, hkz, hact⟩ := h.ca h.ni
    obtain ⟨xt, hct, -⟩ := h.ct
    rw [hct] at hxa; cases hxa
    rw [h.cs xa hct] at hca; cases hca
    have e := (hK.2.2 hr).2
    rw [hkz] at e
    obtain ⟨z', hz', -, hm, -⟩ := SVK.sv_sc (o := s.kheap σ0.curSc) e
    refine ⟨x, s.curSc, z', n, hx, hxb, by rw [kp_curSc hK]; exact hz', ?_⟩
    simp only [scActive, hm]; exact hact
  · obtain ⟨x', hx', hxb⟩ := kp_bind h hK hr
    rw [hx] at hx'; cases hx'; exact hxb

/-- **CtR when ct is unbound or bound to cur_sc.** -/
theorem ctR_kp {σ0 s : State Unit} (h : A10.BS σ0) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = none ∨ x.tcbSchedContext = some s.curSc) :
    CtR s := by
  intro x hx hrun hA hn
  rcases hb x hx with e | e
  · obtain ⟨x', c, -, -, hx', hc, -⟩ := hA
    rw [hx] at hx'; cases hx'; rw [e] at hc; cases hc
  · exact A8.ctR_of_off (fun x' hx' => by rw [hx] at hx'; cases hx'; exact e) (offReady_kp h.off hK) x hx hrun hA hn

/-- CtR when ct is not runnable. -/
theorem ctR_nrun {s : State Unit} (h : A8.NRun s.curThread s) : CtR s := by
  intro x hx hrun _ _
  rw [h x hx] at hrun; cases hrun

end

end Fl4Proofs.P3.SInvR.A11
