/-
P3 (DESIGN.md §9), invariant line G1 (rd8a, KENTRY-PLAN rd7 handoff 1(b),
the exit): **`CAx` (ct ≠ idle → ct bound to an active SC) at every kernel
exit** (spec side only, outside the JAtZ cone).

Where `CAx` holds: at every kernel ENTRY and EXIT (the state after
`schedule ; activate_thread`), not mid-entry: an unbind / donation away /
set-inactive of ct's SC breaks it, and each such writer leaves the action
≠ `resume_cur_thread` (reschedule_required), so mid-entry only the weaker
**`RCA s := action = resume → CAx s`** is carried, and `schedule` turns it
back into `CAx`:

* `AB t s := ActB s t`; leaves: an SC update keeping `REFILL_MAX`
  (`ab_updateSchedContext`), a thread set keeping the SC binding
  (`ab_threadSet`), any step of RdY's heap-view family `FK` (`ab_of_fk`,
  e.g. `as_user`), any SVK `SVM` step (`ab_of_sv`); one small lemma per callee (no generic unfolding).
  `ab_scAndTimer` (sc_and_timer: commits / unblock checks rewrite refills
  only), `ab_activateThread`.
* `actB_fk` (ActB along `FK`), `cax_se` (at sc_and_timer's start, from RdY's
  `SE`: the new ct is idle, `RdyT` (switch / choose-new targets: R1 / R2), or
  the old ct under resume (then `RCA` at schedule's start)),
  **`cax_schedule`**, **`cax_exit`**.
-/
import Fl4Proofs.P3.SpecInvRd8A1
import Fl4Proofs.P3.SpecInvNtfnQC4
import Fl4Proofs.P3.SpecInvSgI5
open Classical

namespace Fl4Proofs.P3.SInvR.A8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- The mid-entry form of `CAx`. -/
abbrev RCA (s : State Unit) : Prop := s.schedulerAction = .resumeCurThread → CAx s

/-! ## `ActB` of a fixed thread -/

abbrev AB (t : ObjRef) (s : State Unit) : Prop := ActB s t

theorem ab_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefillMax = y.scRefillMax) (t : ObjRef) : IK (AB t) (updateSchedContext (Z := Unit) q f) := by
  intro s hs y hy
  obtain ⟨y0, n0, hk, e⟩ := SVK.updSc_mem hy
  rw [e]
  obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := hs
  have htq : t ≠ q := by rintro rfl; rw [hk] at h1; cases h1
  by_cases ec : c = q
  · subst ec
    have ez : z = y0 ∧ n = n0 := by
      rw [hk] at h3; injection h3 with h; injection h with e1 e2; exact ⟨e1.symm, e2.symm⟩
    obtain ⟨rfl, rfl⟩ := ez
    refine ⟨x, c, f z, n, ?_, h2, ?_, ?_⟩
    · show Function.update s.kheap c _ t = _; rw [Function.update_of_ne htq]; exact h1
    · show Function.update s.kheap c _ c = _; rw [Function.update_self]
    · show activeSc (f z).scRefillMax = true; rw [hf]; exact h4
  · refine ⟨x, c, z, n, ?_, h2, ?_, h4⟩
    · show Function.update s.kheap q _ t = _; rw [Function.update_of_ne htq]; exact h1
    · show Function.update s.kheap q _ c = _; rw [Function.update_of_ne ec]; exact h3

theorem ab_threadSet (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (t' t : ObjRef) :
    IK (AB t) (threadSet (Z := Unit) f t') := by
  intro s hs y hy
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hy
  rw [e]
  obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := hs
  have hct : c ≠ t' := by rintro rfl; rw [hx0] at h3; cases h3
  have h3' : Function.update s.kheap t' (some (.tcb (f x0))) c = some (.schedContext z n) := by
    rw [Function.update_of_ne hct]; exact h3
  by_cases et : t = t'
  · subst et
    have ex : x0 = x := by rw [hx0] at h1; exact KernelObject.tcb.inj (Option.some.inj h1)
    rw [ex] at h3' ⊢
    exact ⟨f x, c, z, n, by simp only [Function.update_self], by rw [hf]; exact h2, h3', h4⟩
  · exact ⟨x, c, z, n, by show Function.update _ _ _ t = _; rw [Function.update_of_ne et]; exact h1, h2, h3', h4⟩

/-- `ActB` along RdY's heap view. -/
theorem actB_fk {σ s : State Unit} {c0 : ObjRef} {u : Ticks} {T : Time} {I S : ObjRef} {t : ObjRef}
    (h : ActB σ t) (hF : FK σ.kheap c0 u T I S s) : ActB s t := by
  obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := h
  obtain ⟨x', hx', ex⟩ := hv_tcb ((hF.1 t).trans (congrArg HV h1))
  exact ⟨x', c, z, n, hx', (hvT_sc ex).trans h2, (hv_sc (hF.1 c)).2 h3, h4⟩

theorem ab_of_fk {α : Type} {m : NonDet (State Unit) α}
    (h : ∀ (K : ObjRef → Option KernelObject) (c0 : ObjRef) (u : Ticks) (T : Time) (I S : ObjRef),
      IK (FK K c0 u T I S) m) (t : ObjRef) : IK (AB t) m := by
  intro s hs y hy
  exact actB_fk hs (h s.kheap s.curSc s.consumedTime s.curTime s.idleThread s.idleSc s (fk_self s) y hy)

/-- `ActB` along SVK's scheduler view. -/
theorem actB_svs {σ σ' : State Unit} {t : ObjRef} (h : ActB σ t) (hS : SVK.SVS σ σ') : ActB σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, h1⟩ := h
  have e1 := hS.1 t; rw [hx] at e1
  obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := σ'.kheap t) e1
  have e2 := hS.1 c; rw [hy] at e2
  obtain ⟨y', hy', -, hm, -⟩ := SVK.sv_sc (o := σ'.kheap c) e2
  refine ⟨x', c, y', n, hx', hxs.trans hc, hy', ?_⟩
  show activeSc y'.scRefillMax = true
  rw [hm]; exact h1

theorem ab_of_sv {α : Type} {m : NonDet (State Unit) α} (h : SVK.SVM m) (t : ObjRef) : IK (AB t) m :=
  fun s hs y hy => actB_svs hs (h s y hy)

syntax "ab_leaf" : tactic
macro_rules | `(tactic| ab_leaf) => `(tactic| fail "no ab_leaf")
macro_rules | `(tactic| ab_leaf) => `(tactic| (refine ab_updateSchedContext _ _ ?_ _; intro _; rfl))
macro_rules | `(tactic| ab_leaf) => `(tactic| (refine ab_threadSet _ ?_ _ _; intro _; rfl))
macro_rules | `(tactic| ab_leaf) => `(tactic| exact ab_of_fk (fun _ _ _ _ _ _ => fk_asUser _ _) _)
macro_rules | `(tactic| ab_leaf) => `(tactic| exact ik_doMachineOp (fun _ _ h => h) _)
macro_rules | `(tactic| ab_leaf) => `(tactic| exact ik_doExtendedOp (fun _ _ h => h) _)
macro_rules | `(tactic| ab_leaf) => `(tactic| (refine ab_of_sv ?_ _; sv_leaf; done))

/-- One walk (no unfolding of callees: each callee has its own lemma). -/
macro "ab_auto" : tactic => `(tactic| repeat' (first | ab_leaf | ik_step0))

theorem ab_getSchedContext (p t : ObjRef) : IK (AB t) (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_getSchedContext _ _)

theorem ab_updateRefillHd (p : ObjRef) (f : Refill → Refill) (t : ObjRef) : IK (AB t) (updateRefillHd (Z := Unit) p f) := by
  unfold updateRefillHd; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_updateRefillHd _ _ _)

theorem ab_updateRefillTl (p : ObjRef) (f : Refill → Refill) (t : ObjRef) : IK (AB t) (updateRefillTl (Z := Unit) p f) := by
  unfold updateRefillTl; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_updateRefillTl _ _ _)

theorem ab_refillAddTail (p : ObjRef) (r : Refill) (t : ObjRef) : IK (AB t) (refillAddTail (Z := Unit) p r) := by
  unfold refillAddTail; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_refillAddTail _ _ _)

theorem ab_refillPopHead (p t : ObjRef) : IK (AB t) (refillPopHead (Z := Unit) p) := by
  unfold refillPopHead getRefillHead; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_refillPopHead _ _)

theorem ab_scheduleUsed (p : ObjRef) (r : Refill) (t : ObjRef) : IK (AB t) (scheduleUsed (Z := Unit) p r) := by
  unfold scheduleUsed getRefills getRefillTail refillFull; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_scheduleUsed _ _ _)

theorem ab_chargeEntireHeadRefill (p : ObjRef) (u : Ticks) (t : ObjRef) :
    IK (AB t) (chargeEntireHeadRefill (Z := Unit) p u) := by
  unfold chargeEntireHeadRefill getRefillHead refillSingle refillSize getRefills; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_chargeEntireHeadRefill _ _ _)

theorem ab_mergeNonoverlappingHeadRefill (p t : ObjRef) : IK (AB t) (mergeNonoverlappingHeadRefill (Z := Unit) p) := by
  unfold mergeNonoverlappingHeadRefill; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_mergeNonoverlappingHeadRefill _ _)

theorem ab_mergeOverlappingRefills (p t : ObjRef) : IK (AB t) (mergeOverlappingRefills (Z := Unit) p) := by
  unfold mergeOverlappingRefills; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_mergeOverlappingRefills _ _)

theorem ab_refillBudgetCheck (u : Ticks) (t : ObjRef) : IK (AB t) (refillBudgetCheck (Z := Unit) u) := by
  unfold refillBudgetCheck handleOverrun headInsufficientLoop isRoundRobin getRefillHead; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_refillBudgetCheck _ _)

theorem ab_refillBudgetCheckRoundRobin (u : Ticks) (t : ObjRef) :
    IK (AB t) (refillBudgetCheckRoundRobin (Z := Unit) u) := by
  unfold refillBudgetCheckRoundRobin; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_refillBudgetCheckRoundRobin _ _)

theorem ab_commitTime (t : ObjRef) : IK (AB t) (commitTime (Z := Unit)) := by
  unfold commitTime getScActive isRoundRobin; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_commitTime _)

theorem ab_refillUnblockCheck (p t : ObjRef) : IK (AB t) (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop isRoundRobin getScRefillReady; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_refillUnblockCheck _ _)

theorem ab_ifCond (o : Option ObjRef) (a b : Option Bool) (t : ObjRef) :
    IK (AB t) (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_ifCond _ _ _ _)

theorem ab_switchSchedContext (t : ObjRef) : IK (AB t) (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ab_auto

theorem ab_setNextInterrupt (t : ObjRef) : IK (AB t) (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt getRefillHead; ab_auto

theorem ab_scAndTimer (t : ObjRef) : IK (AB t) (scAndTimer (Z := Unit)) := by
  unfold scAndTimer
  exact ik_bind (ab_switchSchedContext t) fun _ => ik_bind (ik_gets _) fun _ =>
    ik_when _ (ik_bind (ab_setNextInterrupt t) fun _ => ik_modify fun _ h => h)

theorem ab_setThreadState (t' : ObjRef) (ts : ThreadState) (t : ObjRef) :
    IK (AB t) (setThreadState (Z := Unit) t' ts) := by
  unfold setThreadState setThreadStateAct; ab_auto
macro_rules | `(tactic| ab_leaf) => `(tactic| with_reducible exact ab_setThreadState _ _ _)

theorem ab_completeYieldTo (t' t : ObjRef) : IK (AB t) (completeYieldTo (Z := Unit) t') := by
  unfold completeYieldTo setConsumed schedContextUpdateConsumed schedContextCancelYieldTo replyFromKernel; ab_auto

theorem ab_activateThread (t : ObjRef) : IK (AB t) (activateThread (Z := Unit)) := by
  unfold activateThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (by ab_auto) fun _ =>
    ik_bind (ik_when _ (ab_completeYieldTo _ t)) fun _ => ik_bind (by ab_auto) fun st => ?_
  cases st <;> (try dsimp only) <;> ab_auto

theorem cax_of_ci {m : NonDet (State Unit) Unit} (hc : ∀ c, IK (fun s => s.curThread = c) m)
    (hi : ∀ i, IK (SInvG.IdleIs i) m) (ha : ∀ t, IK (AB t) m) : IK CAx m := by
  intro s hs r hr
  have e1 : r.2.curThread = s.curThread := hc s.curThread s rfl r hr
  have e2 : r.2.idleThread = s.idleThread := hi s.idleThread s rfl r hr
  intro hn
  rw [e1, e2] at hn
  rw [e1]
  exact ha s.curThread s (hs hn) r hr

theorem cax_scAndTimer : IK CAx (scAndTimer (Z := Unit)) :=
  cax_of_ci (fun _ => SInv.ct_scAndTimer) (fun _ => SInvG.idk_scAndTimer) ab_scAndTimer

theorem cax_activateThread : IK CAx (activateThread (Z := Unit)) :=
  cax_of_ci (fun _ => SInv.ct_activateThread) (fun _ => SInvG.idk_activateThread) ab_activateThread

/-! ## The exit -/

/-- `CAx` at `sc_and_timer`'s start (RdY's `SE`). -/
theorem cax_se {σ s : State Unit} (hS : SE σ s) (hRC : RCA σ) : CAx s := by
  obtain ⟨hF, -, -, -, hN⟩ := hS
  intro hn
  rcases hN with e | ⟨hR, -⟩ | ⟨ec, ha⟩
  · exact absurd e hn
  · exact actB_of_rdyT hR
  · have hI : s.idleThread = σ.idleThread := hF.2.2.2.2.1
    have := hRC ha (by rw [← ec, ← hI]; exact hn)
    rw [ec]; exact actB_fk this hF

/-- **`CAx` after `schedule`**, from `RCA` (and rd_scheduleSE's facts) at its start. -/
theorem cax_schedule (σ : State Unit) (hσ : Rdy σ) (hRN : SInvB.RNE σ) (hC : CtR σ) (hAW : AW σ)
    (hRC : RCA σ) : ∀ r ∈ (schedule (Z := Unit) σ).1, CAx r.2 :=
  rd_scheduleSE (Q := CAx) σ (fun s hs r hr => cax_scAndTimer s (cax_se hs hRC) r hr)
    hσ hRN hC hAW

/-- **`CAx` at the kernel exit** (`schedule ; activate_thread`). -/
theorem cax_exit (σ : State Unit) (hσ : Rdy σ) (hRN : SInvB.RNE σ) (hC : CtR σ) (hAW : AW σ)
    (hRC : RCA σ) : ∀ r ∈ ((schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ).1, CAx r.2 := by
  intro r ⟨z, hz, hr⟩
  exact cax_activateThread z.2 (cax_schedule σ hσ hRN hC hAW hRC z hz) r hr

end

end Fl4Proofs.P3.SInvR.A8
