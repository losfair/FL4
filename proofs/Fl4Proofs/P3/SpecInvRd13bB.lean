/-
P3 (DESIGN.md §9), invariant line G1 (rd13b, KENTRY-PLAN rd12b handoff 1):
**the end of an arm that leaves rd11a's frame** (spec side only): `PerfA`'s
second option (`CB → SS4` after the post) from facts that do not mention the
scheduler views of every object.

* **`ss4_nrun`**: from `BS σ0 ∧ Suff σ0`, a state with σ0's `cfS`, rd8a's
  `CW` at σ0's cur_sc and ct not runnable has `CB → SS4` (resume is excluded
  by `CB`: ct is neither runnable nor idle).
* `TB σ0 q` (σ0's `cfS`, `CW` at σ0's cur_sc, ct bound to cur_sc, cur_sc an
  SC) and **`ss4_tb`**: `TB` gives `CB → SS4` (OS by the frame, RCA from
  σ0's `CAx` through `CW`, CtR from `OffReady`, HRC from the binding).
* `tb_svcf` (`TB` across an `SVS ∧ cfS` step), **`tb_post`** (the post keeps
  `TB`), `nr_post` (after a non-runnable ct the post is the identity).
* **`perfA_tbn`**: an arm each of whose `ok` outcomes has `TB` or (σ0's
  `cfS`, `CW`, ct not runnable), and each of whose `error` outcomes has
  `CB → SS4` after the preemption path, has `PerfA`.
-/
import Fl4Proofs.P3.SpecInvRd13bA
open Classical

namespace Fl4Proofs.P3.SInvR.A13b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 1000000

theorem cf_curThread {σ0 q : State Unit} (h : cfS q = cfS σ0) : q.curThread = σ0.curThread :=
  congrArg (fun p => p.2.2.1) h

theorem cf_curSc {σ0 q : State Unit} (h : cfS q = cfS σ0) : q.curSc = σ0.curSc :=
  congrArg (fun p => p.2.1) h

theorem cf_idle {σ0 q : State Unit} (h : cfS q = cfS σ0) : q.idleThread = σ0.idleThread :=
  congrArg (fun p => p.2.2.2.1) h

theorem os_cw {σ0 q : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (hc : cfS q = cfS σ0)
    (hw : A8.CW σ0.curSc σ0 q) : OS q :=
  os_frame (Or.inl ⟨hB.off, hS⟩) ⟨hc, fun y n hy => by rw [cf_curSc hc] at hy; exact hw.1 y n hy, hw.2⟩

theorem offReady_cw {σ0 q : State Unit} (hO : Sched.OffReady σ0) (hc : cfS q = cfS σ0)
    (hw : A8.CW σ0.curSc σ0 q) : Sched.OffReady q := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, -, -, -, e6⟩ := hc'
  intro y n hy
  rw [e2] at hy
  obtain ⟨y0, n0, hy0, er, -⟩ := hw.1 y n hy
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  rw [e1, e6, hh]; exact hO y0 n0 hy0

/-- **ct not runnable**: `CB → SS4` from σ0's frame facts alone. -/
theorem ss4_nrun {σ0 q : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (hc : cfS q = cfS σ0)
    (hw : A8.CW σ0.curSc σ0 q) (hn : A8.NRun q.curThread q) (hcb : CB q) : A10.SS4 q := by
  have ni : q.curThread ≠ q.idleThread := by rw [cf_curThread hc, cf_idle hc]; exact hB.ni
  have hno : q.schedulerAction ≠ .resumeCurThread := by
    intro hr
    rcases hcb hr with ⟨x, hx, hrun⟩ | hi
    · rw [hn x hx] at hrun; cases hrun
    · exact ni hi
  exact ⟨os_cw hB hS hc hw, fun hr => absurd hr hno, A11.ctR_nrun hn, fun hr => absurd hr hno⟩

/-- The end facts of an arm that leaves rd11a's frame with ct still bound. -/
structure TB (σ0 q : State Unit) : Prop where
  cf : cfS q = cfS σ0
  cw : A8.CW σ0.curSc σ0 q
  bd : ∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc
  sc : ∃ y n, q.kheap σ0.curSc = some (.schedContext y n)

/-- **`TB` gives `CB → SS4`.** -/
theorem ss4_tb {σ0 q : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (h : TB σ0 q) (hcb : CB q) :
    A10.SS4 q := by
  have et := cf_curThread h.cf
  have ec := cf_curSc h.cf
  have ni : q.curThread ≠ q.idleThread := by rw [et, cf_idle h.cf]; exact hB.ni
  have hb' : ∀ x, q.kheap q.curThread = some (.tcb x) → x.tcbSchedContext = some q.curSc := by
    intro x hx; rw [et] at hx; rw [ec]; exact h.bd x hx
  refine ⟨os_cw hB hS h.cf h.cw, fun hr _ => ?_,
    A8.ctR_of_off hb' (offReady_cw hB.off h.cf h.cw), fun _ x hx => hb' x hx⟩
  rcases hcb hr with ⟨x, hx, -⟩ | hi
  · obtain ⟨y, n, hy⟩ := h.sc
    obtain ⟨y0, n0, hy0, -, hm⟩ := h.cw.1 y n hy
    obtain ⟨xa, c, z, m, hxa, hca, hkz, hact⟩ := hB.ca hB.ni
    rw [hB.cs xa hxa] at hca; cases hca
    rw [hkz] at hy0; cases hy0
    refine ⟨x, q.curSc, y, n, hx, hb' x hx, by rw [ec]; exact hy, ?_⟩
    simp only [scActive, hm]; exact hact
  · exact absurd hi ni

/-! ## The post -/

theorem tb_svcf {σ0 s s' : State Unit} (h : TB σ0 s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : TB σ0 s' := by
  refine ⟨hc.trans h.cf, h.cw.trans (A8.cw_of_svs hS), fun x hx => ?_, ?_⟩
  · have e := hS.1 σ0.curThread
    rw [hx] at e
    obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap σ0.curThread) (a := x.tcbSchedContext) e.symm
    rw [← hys]; exact h.bd y hy
  · obtain ⟨y, n, hy⟩ := h.sc
    have e := hS.1 σ0.curSc
    rw [hy] at e
    obtain ⟨y', hy', -⟩ := SVK.sv_sc (o := s'.kheap σ0.curSc) e
    exact ⟨y', n, hy'⟩

/-- **The post keeps `TB`.** -/
theorem tb_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : TB σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, TB σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := tb_svcf h (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    exact tb_svcf h1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-- After a non-runnable ct the post is the identity. -/
theorem nr_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (et : s.curThread = σ0.curThread)
    (hn : A8.NRun s.curThread s) : ∀ y ∈ (invPost calling σ0.curThread reply s).1, y.2 = s := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  rw [← et] at hx
  have hr := hn x hx
  dsimp only at hy
  revert hy; revert hr
  generalize x.tcbState = st
  cases st <;> intro hr hy
  case restart => simp [runnable] at hr
  all_goals (rw [Set.mem_singleton_iff.1 hy])

/-! ## The arm -/

/-- What an `ok` outcome of an arm that leaves rd11a's frame must give. -/
def TBN (σ0 q : State Unit) : Prop :=
  TB σ0 q ∨ (cfS q = cfS σ0 ∧ A8.CW σ0.curSc σ0 q ∧ A8.NRun q.curThread q)

/-- **An arm with `TB` or a non-runnable ct at every `ok` outcome.** -/
theorem perfA_tbn {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hS : Suff σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don oper).run s).1,
      (∀ a, y.1 = .ok a → TBN σ0 y.2) ∧
      (∀ e, y.1 = .error e → ∀ z ∈ (preemptionPath (Z := Unit) y.2).1, CB z.2 → A10.SS4 z.2)) :
    PerfA σ0 bl call don oper s := by
  intro y hy
  refine ⟨fun a ha => Or.inr fun q hq hc => ?_, (h y hy).2⟩
  rcases (h y hy).1 a ha with ht | ⟨hc0, hw, hn⟩
  · exact ss4_tb hB hS (tb_post call a ht q hq) hc
  · rw [nr_post call a (cf_curThread hc0) hn q hq] at hc ⊢
    exact ss4_nrun hB hS hc0 hw hn hc

end

end Fl4Proofs.P3.SInvR.A13b
