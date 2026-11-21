/-
P3 (DESIGN.md §9), invariant line G1 (rd14d, KENTRY-PLAN rd14c obstacles (a)
and (c)): **the end cases of the deletion / reset arms** (spec side only).

* `CWw c σ σ'` (rd8a's `CW` weakened: refills kept, refill max kept or 0) and
  **`TW σ0 q`** (rd14b's `TU` with `CWw` for `CW`: the deletion of cur_sc's last
  cap unbinds ct and zeroes cur_sc's refill max): **`ss4_tw`** (OffReady reads
  only the head; `Suff` vacuous at max 0; `RCA` / `HRC` vacuous: no resume;
  `CtR` vacuous: ct unbound), `tw_svcf`, **`tw_post`**.
* **`TT σ0 q`** (a non-preempting preemption point: cur_sc / ct / idle kept,
  the consumed time and the current time advanced by the same amount, rd8a's
  `CW`, ct bound to cur_sc (an SC), `Suff` — what the point's check gives):
  **`ss4_tt`** (OffReady by the equal advance, RCA from σ0's `CAx` through
  `CW`, `CtR` from `OffReady`), `tt_svcf`, **`tt_post`**.
* **`EndA σ0 q`** (rd13b's `TBN`, rd14b's `TU`, `TW`, rd14d's `TZ`, `TT`) and
  **`perfA_end`**: every `ok` outcome `EndA`, every `error` outcome `CB → SS4`
  after the preemption path ⇒ `PerfA`. The next arms (CNode revoke / delete,
  Untyped reset) only have to produce one of these.
-/
import Fl4Proofs.P3.SpecInvRd14dC
open Classical

namespace Fl4Proofs.P3.SInvR.A14d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c

noncomputable section

set_option maxHeartbeats 1000000

/-! ## (c): ct unbound, cur_sc's refill max possibly zeroed -/

/-- rd8a's `CW` weakened (rd14e, lead option (a)): refills and refill max
kept, or the refill max zeroed (the SC made inactive by its finalisation; the
refills may then be emptied). -/
abbrev CWw (c : ObjRef) (σ σ' : State Unit) : Prop :=
  ∀ y n, σ'.kheap c = some (.schedContext y n) → ∃ y0 n0, σ.kheap c = some (.schedContext y0 n0) ∧
    ((y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax) ∨ y.scRefillMax = 0)

theorem cWw_of_cw {c : ObjRef} {σ σ' : State Unit} (h : A8.CW c σ σ') : CWw c σ σ' := fun y n hy => by
  obtain ⟨y0, n0, h0, e1, e2⟩ := h.1 y n hy
  exact ⟨y0, n0, h0, Or.inl ⟨e1, e2⟩⟩

/-- rd14b's `TU` with `CWw`, and cur_sc not the idle SC. -/
abbrev TW (σ0 q : State Unit) : Prop :=
  cfS q = cfS σ0 ∧ CWw σ0.curSc σ0 q ∧
    (∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = none) ∧
    q.schedulerAction ≠ .resumeCurThread ∧ σ0.curSc ≠ σ0.idleSc

theorem tw_of_tu {σ0 q : State Unit} (h : TU σ0 q) (hid : σ0.curSc ≠ σ0.idleSc) : TW σ0 q :=
  ⟨h.1, cWw_of_cw h.2.1, h.2.2.1, h.2.2.2, hid⟩

/-- **`TW` gives `SS4`**: `OS` by its first disjunct when cur_sc's refills and
max are kept, by `OI` (rd14e) when its max is 0. -/
theorem ss4_tw {σ0 q : State Unit} (hB : A10.BS σ0) (hS : Suff σ0) (h : TW σ0 q) : A10.SS4 q := by
  obtain ⟨hc, hw, hn, hr, hid⟩ := h
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := hc'
  have hOS : OS q := by
    by_cases hP : ∃ y n, q.kheap q.curSc = some (.schedContext y n) ∧ y.scRefillMax = 0
    · obtain ⟨y, n, hy, hm⟩ := hP
      refine Or.inr (Or.inr ⟨by rw [e2, e5]; exact hid, fun y' n' hy' => ?_, hr⟩)
      rw [hy] at hy'
      obtain ⟨rfl, -⟩ : y = y' ∧ n = n' := by injection hy' with e; injection e with e7 e8; exact ⟨e7, e8⟩
      simp only [scActive, activeSc, hm, lt_self_iff_false, decide_false]
    · have hk : ∀ y n, q.kheap σ0.curSc = some (.schedContext y n) → ∃ y0 n0,
          σ0.kheap σ0.curSc = some (.schedContext y0 n0) ∧ y.scRefills = y0.scRefills ∧
            y.scRefillMax = y0.scRefillMax := by
        intro y n hy
        obtain ⟨y0, n0, hy0, hcase⟩ := hw y n hy
        rcases hcase with ⟨er, em⟩ | hm
        · exact ⟨y0, n0, hy0, er, em⟩
        · exact absurd ⟨y, n, by rw [e2]; exact hy, hm⟩ hP
      have hO : Sched.OffReady q := by
        intro y n hy
        rw [e2] at hy
        obtain ⟨y0, n0, hy0, er, -⟩ := hk y n hy
        have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
        rw [e1, e6, hh]; exact hB.off y0 n0 hy0
      have hSf : Suff q := by
        intro y n hy ha hne
        rw [e2] at hy hne; rw [e5] at hne; rw [e1]
        obtain ⟨y0, n0, hy0, er, em⟩ := hk y n hy
        have ha0 : scActive y0 = true := by simp only [scActive, ← em]; exact ha
        have := hS y0 n0 hy0 ha0 hne
        have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
        rw [hh]; exact this
      exact Or.inl ⟨hO, hSf⟩
  refine ⟨hOS, fun e => absurd e hr, fun x hx _ hA _ => ?_, fun e => absurd e hr⟩
  obtain ⟨x', c, y, n, h1, h2, -, -⟩ := hA
  rw [e3] at hx h1
  have ex : x' = x := KernelObject.tcb.inj (Option.some.inj (h1.symm.trans hx))
  subst ex
  rw [hn _ hx] at h2; cases h2

theorem tw_svcf {σ0 s s' : State Unit} (h : TW σ0 s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : TW σ0 s' := by
  refine ⟨hc.trans h.1, fun y n hy => ?_, fun x hx => ?_, nres_svs h.2.2.2.1 hS, h.2.2.2.2⟩
  · obtain ⟨y1, n1, hy1, e1, e2⟩ := (A8.cw_of_svs (c := σ0.curSc) hS).1 y n hy
    obtain ⟨y0, n0, hy0, e4⟩ := h.2.1 y1 n1 hy1
    refine ⟨y0, n0, hy0, ?_⟩
    rcases e4 with ⟨e3, e5⟩ | e5
    · exact Or.inl ⟨e1.trans e3, e2.trans e5⟩
    · exact Or.inr (e2.trans e5)
  · have e := hS.1 σ0.curThread
    rw [hx] at e
    obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap σ0.curThread) (a := x.tcbSchedContext) e.symm
    rw [← hys]; exact h.2.2.1 y hy

/-- **The post keeps `TW`.** -/
theorem tw_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : TW σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, TW σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := tw_svcf h (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    exact tw_svcf h1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-! ## (a): a non-preempting preemption point -/

/-- The end facts after a non-preempting `preemption_point` (time and consumed time advanced together). -/
structure TT (σ0 q : State Unit) : Prop where
  cs : q.curSc = σ0.curSc
  ct : q.curThread = σ0.curThread
  idle : q.idleThread = σ0.idleThread
  adv : q.consumedTime.toNat + σ0.curTime.toNat = σ0.consumedTime.toNat + q.curTime.toNat
  cw : A8.CW σ0.curSc σ0 q
  bd : ∀ x, q.kheap σ0.curThread = some (.tcb x) → x.tcbSchedContext = some σ0.curSc
  sc : ∃ y n, q.kheap σ0.curSc = some (.schedContext y n)
  suff : Suff q

theorem tt_of_tb {σ0 q : State Unit} (h : TB σ0 q) (hS : Suff σ0) : TT σ0 q := by
  have hc := h.cf
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hc
  refine ⟨e2, e3, e4, by rw [e1, e6]; try omega, h.cw, h.bd, h.sc, ?_⟩
  intro y n hy ha hne
  rw [e2] at hy hne; rw [e5] at hne; rw [e1]
  obtain ⟨y0, n0, hy0, er, em⟩ := h.cw.1 y n hy
  have ha0 : scActive y0 = true := by simp only [scActive, ← em]; exact ha
  have := hS y0 n0 hy0 ha0 hne
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  rw [hh]; exact this

theorem offReady_tt {σ0 q : State Unit} (hO : Sched.OffReady σ0) (h : TT σ0 q) : Sched.OffReady q := by
  intro y n hy
  rw [h.cs] at hy
  obtain ⟨y0, n0, hy0, er, -⟩ := h.cw.1 y n hy
  have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
  have h0 := hO y0 n0 hy0
  rw [hh]
  have := h.adv
  omega

/-- **`TT` gives `CB → SS4`.** -/
theorem ss4_tt {σ0 q : State Unit} (hB : A10.BS σ0) (h : TT σ0 q) (hcb : CB q) : A10.SS4 q := by
  have et := h.ct
  have ec := h.cs
  have ni : q.curThread ≠ q.idleThread := by rw [et, h.idle]; exact hB.ni
  have hb' : ∀ x, q.kheap q.curThread = some (.tcb x) → x.tcbSchedContext = some q.curSc := by
    intro x hx; rw [et] at hx; rw [ec]; exact h.bd x hx
  have hO := offReady_tt hB.off h
  refine ⟨Or.inl ⟨hO, h.suff⟩, fun hr _ => ?_, A8.ctR_of_off hb' hO, fun _ x hx => hb' x hx⟩
  rcases hcb hr with ⟨x, hx, -⟩ | hi
  · obtain ⟨y, n, hy⟩ := h.sc
    obtain ⟨y0, n0, hy0, -, hm⟩ := h.cw.1 y n hy
    obtain ⟨xa, c, z, m, hxa, hca, hkz, hact⟩ := hB.ca hB.ni
    rw [hB.cs xa hxa] at hca; cases hca
    rw [hkz] at hy0; cases hy0
    refine ⟨x, q.curSc, y, n, hx, hb' x hx, by rw [ec]; exact hy, ?_⟩
    simp only [scActive, hm]; exact hact
  · exact absurd hi ni

theorem tt_svcf {σ0 s s' : State Unit} (h : TT σ0 s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) : TT σ0 s' := by
  have hc' := hc
  simp only [cfS, Prod.mk.injEq] at hc'
  obtain ⟨e1, e2, e3, e4, -, e6⟩ := hc'
  refine ⟨e2.trans h.cs, e3.trans h.ct, e4.trans h.idle, by rw [e1, e6]; exact h.adv,
    h.cw.trans (A8.cw_of_svs hS), fun x hx => ?_, ?_, A10.suff_svcf h.suff hS hc⟩
  · have e := hS.1 σ0.curThread
    rw [hx] at e
    obtain ⟨y, hy, hys⟩ := SVK.sv_tcb (o := s.kheap σ0.curThread) (a := x.tcbSchedContext) e.symm
    rw [← hys]; exact h.bd y hy
  · obtain ⟨y, n, hy⟩ := h.sc
    have e := hS.1 σ0.curSc
    rw [hy] at e
    obtain ⟨y', hy', -⟩ := SVK.sv_sc (o := s'.kheap σ0.curSc) e
    exact ⟨y', n, hy'⟩

/-- **The post keeps `TT`.** -/
theorem tt_post (calling : Bool) (reply : List Data) {σ0 s : State Unit} (h : TT σ0 s) :
    ∀ y ∈ (invPost calling σ0.curThread reply s).1, TT σ0 y.2 := by
  intro y hy
  obtain ⟨w, hw, hy⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_threadGet hw
  dsimp only at hy
  revert hy
  generalize x.tcbState = st
  cases st <;> intro hy
  case restart =>
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := tt_svcf h (sv_whenReply calling _ _ s u hu) (cfk_whenReply calling _ _ s u hu)
    exact tt_svcf h1 (SVK.sv_setThreadState' _ _ u.2 y hy) (cfk_setThreadState' _ _ u.2 y hy)
  all_goals (rw [Set.mem_singleton_iff.1 hy]; exact h)

/-! ## Every end case -/

/-- What an `ok` outcome of an arm may end in. -/
def EndA (σ0 q : State Unit) : Prop := TBN σ0 q ∨ TU σ0 q ∨ TW σ0 q ∨ TZ σ0 q ∨ TT σ0 q

/-- **An arm with an `EndA` case at every `ok` outcome.** -/
theorem perfA_end {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation} (hB : A10.BS σ0)
    (hS : Suff σ0)
    (h : ∀ y ∈ ((fl4PerformInvocation (Z := Unit) bl call don oper).run s).1,
      (∀ a, y.1 = .ok a → EndA σ0 y.2) ∧
      (∀ e, y.1 = .error e → ∀ z ∈ (preemptionPath (Z := Unit) y.2).1, CB z.2 → A10.SS4 z.2)) :
    PerfA σ0 bl call don oper s := by
  intro y hy
  refine ⟨fun a ha => Or.inr fun q hq hc => ?_, (h y hy).2⟩
  rcases (h y hy).1 a ha with (ht | ⟨hc0, hw, hn⟩) | hu | hw | hz | htt
  · exact ss4_tb hB hS (tb_post call a ht q hq) hc
  · rw [nr_post call a (cf_curThread hc0) hn q hq] at hc ⊢
    exact ss4_nrun hB hS hc0 hw hn hc
  · exact ss4_tu hB hS (tu_post call a hu q hq)
  · exact ss4_tw hB hS (tw_post call a hw q hq)
  · exact ss4_tz (tz_post call a hz q hq)
  · exact ss4_tt hB (tt_post call a htt q hq) hc

end

end Fl4Proofs.P3.SInvR.A14d
