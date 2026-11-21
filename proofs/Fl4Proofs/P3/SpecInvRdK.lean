/-
P3 (DESIGN.md §9), invariant line G1 (rd7): **the syscall front
`update_time_stamp ; check_budget_restart` establishes the mid-entry
disjunct `OS`** (spec side only, outside the JAtZ cone; KENTRY-PLAN rd6
handoff 1).

* **`OS σ := (OffReady σ ∧ Suff σ) ∨ (consumed = 0 ∧ action ≠ resume) ∨ OI σ`**
  (rd14e: `OI`, cur_sc inactive and not idle's, no resume — SpecInvRdY):
  rd4's `hOS0` of `rd_scheduleOff`, stated as a predicate. `OSF σ σ'` is a
  step keeping it (`os_frame`): the consumed time, `cur_sc`, `cur_thread`,
  the idle thread / SC and the time kept (`cfS`, SpecInvRdP), the object at
  `cur_sc` kept when it is an SC afterwards, and `resume_cur_thread` not
  set.
* **`CAx σ := cur_thread ≠ idle_thread → ActB σ cur_thread`** (l4v
  `ct_active ⟶ active_sc_tcb_at cur_thread` at a kernel entry, via l4v's
  `schedule` assert `ct_schedulable ∨ ct = idle` at `resume_cur_thread`):
  the "cur_sc active at check_budget" fact of rd6's observation. It does NOT
  follow from the carried bundle (SInvA', CurScT, SchedQ / RB, Rdy,
  OffReady): no carried fact reads the activity of the current thread's SC,
  and the spec's `schedule` has no assert at `resume_cur_thread` (g1b's
  FINDING). It is a new carried exit fact (lead decision 2026-11-20: carry
  the narrowest fact): `boot_cAx` here; the exit (`schedule` establishes it:
  a switched-to thread is `RdyT`, idle is exempt, the resume branch keeps
  ct) and the mid-entry form `resume → CAx` are handoff items.
* `checkBudget_cases` / `checkBudgetRestart_cases` (the outcome shapes),
  `cbTail_cf` (charge_budget's tail keeps `cfS`, and is the identity when
  ct is not schedulable), `excl_entry` (`Excl cur_sc` at the entry: ct is
  the only thread bound to `cur_sc` by ScBackS, in no ready queue (CtQ), not
  the switch target (Simple), running (not BlkR)), **`rd_cbr`**: from the
  entry facts at `check_budget_restart`'s start, every outcome has `Rdy`
  and `OS`, and a `true` outcome is the start state with `Suff`.
  **`rd_front`**: the same across `update_time_stamp ; check_budget_restart`
  from the entry state.
-/
import Fl4Proofs.P3.SpecInvRdJ
import Fl4Proofs.P3.SpecInvRdY
import Fl4Proofs.P3.SpecInvRdP
import Fl4Proofs.P3.SpecInvCqY
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The mid-entry disjunct and the new exit fact -/

/-- **The mid-entry disjunct at `schedule`'s start** (rd4's `hOS0`). -/
def OS (σ : State Unit) : Prop :=
  (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ σ.schedulerAction ≠ .resumeCurThread) ∨ OI σ

/-- **CAx** (module docstring): the current thread, unless idle, is bound to
an active SC. -/
def CAx (σ : State Unit) : Prop := σ.curThread ≠ σ.idleThread → ActB σ σ.curThread

theorem boot_cAx : CAx (initASt (Z := Unit)) := fun h => absurd rfl h

/-- A step keeping `OS`. -/
def OSF (σ σ' : State Unit) : Prop :=
  cfS σ' = cfS σ ∧
    (∀ y n, σ'.kheap σ'.curSc = some (.schedContext y n) → ∃ y0 n0, σ.kheap σ.curSc = some (.schedContext y0 n0) ∧
      y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax) ∧
    (σ'.schedulerAction = .resumeCurThread → σ.schedulerAction = .resumeCurThread)

theorem os_frame {σ σ' : State Unit} (h : OS σ) (hF : OSF σ σ') : OS σ' := by
  obtain ⟨hc, hk, ha⟩ := hF
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨e1, e2, -, -, e5, e6⟩ := hc
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · left
    refine ⟨fun y n hy => ?_, fun y n hy hA hI => ?_⟩
    · obtain ⟨y0, n0, hy0, er, -⟩ := hk y n hy
      have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
      have := h1 y0 n0 hy0; rw [e1, e6, hh]; exact this
    · obtain ⟨y0, n0, hy0, er, em⟩ := hk y n hy
      have hh : refillHd y = refillHd y0 := by simp only [refillHd, er]
      have hA0 : scActive y0 = true := by simp only [scActive] at hA ⊢; rw [← em]; exact hA
      have := h2 y0 n0 hy0 hA0 (by rw [← e2, ← e5]; exact hI); rw [e1, hh]; exact this
  · right; left; exact ⟨by rw [e1]; exact h1, fun e => h2 (ha e)⟩
  · right; right
    refine ⟨by rw [e2, e5]; exact h1, fun y n hy => ?_, fun e => h3 (ha e)⟩
    obtain ⟨y0, n0, hy0, -, em⟩ := hk y n hy
    have := h2 y0 n0 hy0
    simp only [scActive] at this ⊢; rw [em]; exact this

theorem os_setSchedulerAction_cn : IK OS (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction
  refine ik_modify fun s h => ?_
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h.1, fun e => by cases e⟩)
  · exact Or.inr (Or.inr ⟨h.1, h.2.1, fun e => by cases e⟩)

theorem os_setThreadStateAct (t : ObjRef) : IK OS (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct
  repeat' (first | (with_reducible exact os_setSchedulerAction_cn) | ik_step0 | ik_unfold | (unfold NonDet.when))

theorem os_threadSet (f : Tcb → Tcb) (t : ObjRef) : IK OS (threadSet (Z := Unit) f t) := by
  intro σ h y hy
  obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hy
  rw [e]
  refine os_frame h ⟨rfl, fun z n hz => ?_, id⟩
  dsimp only at hz
  by_cases ec : σ.curSc = t
  · rw [ec, Function.update_self] at hz; cases hz
  · rw [Function.update_of_ne ec] at hz; exact ⟨z, n, hz, rfl, rfl⟩

theorem os_setThreadState (t : ObjRef) (ts : ThreadState) : IK OS (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ik_bind (os_threadSet _ t) fun _ => os_setThreadStateAct t

/-! ## The outcome shapes of the budget checks -/

theorem checkBudget_cases {σ : State Unit} {r : Bool × State Unit} (hr : r ∈ (checkBudget (Z := Unit) σ).1) :
    (r.2 = σ ∧ Suff σ) ∨ (r.1 = false ∧ ((), r.2) ∈ (chargeBudget (Z := Unit) σ.consumedTime true σ).1) := by
  unfold checkBudget at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨z, hz, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨y, n, hk, rfl⟩ := mem_getScRefillSufficient' hz
  dsimp only at hr
  split at hr
  · rename_i hs
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain rfl := Set.mem_singleton_iff.1 hr
    exact Or.inl ⟨rfl, fun y' n' hk' _ _ => by rw [hk] at hk'; cases hk'; exact hs⟩
  · obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨⟨u, s2⟩, hz2, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hr
    cases u
    exact Or.inr ⟨rfl, hz2⟩

theorem checkBudgetRestart_cases {σ : State Unit} {r : Bool × State Unit}
    (hr : r ∈ (checkBudgetRestart (Z := Unit) σ).1) :
    ∃ z, z ∈ (checkBudget (Z := Unit) σ).1 ∧ r.1 = z.1 ∧
      (r.2 = z.2 ∨ (z.1 = false ∧ ((), r.2) ∈ (setThreadState (Z := Unit) z.2.curThread .restart z.2).1)) := by
  unfold checkBudgetRestart at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hr⟩ := hr
  unfold getThreadState at hz2
  obtain ⟨x, -, rfl⟩ := SInvQ.q1_mem_threadGet hz2
  obtain ⟨⟨u, s3⟩, hz3, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hr
  cases u
  refine ⟨z, hz, rfl, ?_⟩
  unfold NonDet.when at hz3
  split_ifs at hz3 with hc
  · right; exact ⟨by simpa using hc.1, hz3⟩
  · left; exact (Prod.mk.inj (Set.mem_singleton_iff.1 hz3)).2

theorem cfk_endTimeslice (c : Bool) : CFK (endTimeslice (Z := Unit) c) := by
  unfold endTimeslice; cfk_auto

/-- `charge_budget`'s tail keeps `cfS`; it is the identity when ct is not schedulable. -/
theorem cbTail_cf {c : Bool} {s : State Unit} {r : Unit × State Unit} (hr : r ∈ (cbTail c s).1) :
    cfS r.2 = cfS s ∧ (schedulable s.curThread s = false → r.2 = s) := by
  unfold cbTail at hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz2
  dsimp only at hr
  by_cases hs : schedulable s.curThread s = true
  · refine ⟨?_, fun e => by rw [hs] at e; cases e⟩
    have hK : CFK (endTimeslice (Z := Unit) c >>= fun _ => rescheduleRequired (Z := Unit) >>= fun _ =>
        NonDet.modify fun s : State Unit => { s with reprogramTimer := true }) :=
      Vs.dk_bind (cfk_endTimeslice c) fun _ => Vs.dk_bind (cfk_rescheduleRequired') fun _ => Vs.dk_modify fun _ => rfl
    unfold NonDet.when at hr
    rw [if_pos hs] at hr
    exact hK s r hr
  · have hf : schedulable s.curThread s = false := by simpa using hs
    unfold NonDet.when at hr
    rw [if_neg hs] at hr
    have e := Set.mem_singleton_iff.1 hr
    rw [e]
    exact ⟨rfl, fun _ => rfl⟩

/-! ## `Excl cur_sc` at the entry -/

theorem not_blkR_run {ts : ThreadState} {f : Option Fault} (h : ts = .running ∨ ts = .idleThreadState) :
    ¬ BlkR ts f := by
  unfold BlkR
  rcases h with h | h <;> rw [h] <;> simp

theorem excl_entry {σ : State Unit} (hB : SInvB.ScBackS σ) (hcs : SInvQ.CurScT σ) {xt : Tcb}
    (hct : σ.kheap σ.curThread = some (.tcb xt)) (hst : xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
    (hQ : SInvQ.CtQ σ) (hSi : SInvQ.Simple σ) : Excl σ σ.curSc := by
  intro t x hx hc
  obtain ⟨y, k, hy, hyt, -⟩ := hB t x σ.curSc hx hc
  obtain ⟨y', k', hy', hyt', -⟩ := hB σ.curThread xt σ.curSc hct (hcs xt hct)
  rw [hy] at hy'; cases hy'
  rw [hyt] at hyt'; cases hyt'
  rw [hct] at hx; cases hx
  exact ⟨fun d q => hQ d q, hSi _, not_blkR_run hst⟩

/-! ## `check_budget_restart` -/

/-- **`check_budget_restart` from the entry facts** (module docstring): every
outcome has `Rdy` and `OS`; a `true` outcome is the start state, with `Suff`. -/
theorem rd_cbr {σ : State Unit} (hR : Rdy σ) (hO : Sched.OffReady σ) (hS : SInvB.ScInv σ)
    (hcs : SInvQ.CurScT σ) {xt : Tcb} (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hst : xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
    (hQ : SInvQ.CtQ σ) (hSi : SInvQ.Simple σ) (hCB : SInvQ.CB σ)
    (hHB : σ.schedulerAction = .resumeCurThread → σ.curThread ∉ σ.releaseQueue)
    (hCA : CAx σ) (hni : σ.curThread ≠ σ.idleThread)
    {r : Bool × State Unit} (hr : r ∈ (checkBudgetRestart (Z := Unit) σ).1) :
    Rdy r.2 ∧ OS r.2 ∧ (r.1 = true → r.2 = σ ∧ Suff σ) := by
  obtain ⟨xa, c, y, n, hxa, hca, hky, hact⟩ := hCA hni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some σ.curSc := hcs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y0, k0, hy0, -, hne⟩ := hS.back σ.curThread xt σ.curSc hct hb
  rw [hky] at hy0; cases hy0
  have hne' : y.scRefills ≠ [] := hne (Or.inr hact)
  obtain ⟨z, hz, e1, hz2⟩ := checkBudgetRestart_cases hr
  -- the state after check_budget
  have key : Rdy z.2 ∧ OS z.2 := by
    rcases checkBudget_cases hz with ⟨e, hsf⟩ | ⟨-, hc⟩
    · rw [e]; exact ⟨hR, Or.inl ⟨hO, hsf⟩⟩
    · obtain ⟨s1, hR1, hO1, hr1⟩ := rd_chargeBudget_head hR hky
        (fun _ => ⟨hact, hne', fun _ => excl_entry hS.back hcs hct hst hQ hSi⟩) _ true hc
      obtain ⟨z0, e, e1, e2, e3, e4, e5, e6⟩ := hO1
      subst e
      have hk1 : ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit).kheap σ.curSc =
          some (.schedContext z0 n) := kh_upd _ _ _ _
      have ha1 : scActive z0 = true := by simp only [scActive, e2]; exact hact
      have hcs' : σ.curThread ≠ σ.curSc := fun e => by rw [e, hky] at hct; cases hct
      have hct1 : ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit).kheap σ.curThread =
          some (.tcb xt) := by simp [Notif.updK, hcs', hct]
      obtain ⟨hRr, hA⟩ := rd_cbTail' true _ hR1 hk1 ha1 hct1 hb (fwd_chargeOut hS.fwd hky e1) hr1
      obtain ⟨hcf, hid⟩ := cbTail_cf hr1
      have hc0 : z.2.consumedTime = 0 := by
        simp only [cfS, Prod.mk.injEq] at hcf; rw [hcf.1]
      refine ⟨hRr, Or.inr (Or.inl ⟨hc0, ?_⟩)⟩
      by_cases hres : σ.schedulerAction = .resumeCurThread
      · have hrun : runnable xt.tcbState = true := by
          rcases hCB hres with ⟨x', hx', hr'⟩ | hi
          · rw [hct] at hx'; cases hx'; exact hr'
          · exact absurd hi hni
        have hsch : schedulable σ.curThread ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit) = true :=
          Sched.schedulable_of hct1 hb hrun hk1 ha1 (hHB hres)
        exact fun e => by have h := hA hsch; dsimp only at h; rw [h] at e; cases e
      · by_cases hsch : schedulable σ.curThread ({ updSc σ σ.curSc z0 n with consumedTime := 0 } : State Unit) = true
        · exact fun e => by have h := hA hsch; dsimp only at h; rw [h] at e; cases e
        · have h := hid (Bool.eq_false_iff.mpr hsch); dsimp only at h; rw [h]; exact hres
  refine ⟨?_, ?_, fun ht => ?_⟩
  · rcases hz2 with e | ⟨-, hs⟩
    · rw [e]; exact key.1
    · exact rd_setThreadState _ .restart trivial z.2 key.1 _ hs
  · rcases hz2 with e | ⟨-, hs⟩
    · rw [e]; exact key.2
    · exact os_setThreadState _ _ z.2 key.2 _ hs
  · have hz1 : z.1 = true := by rw [← e1]; exact ht
    obtain ⟨e, hsf⟩ := suff_checkBudget hz hz1
    rcases hz2 with e' | ⟨hf, -⟩
    · exact ⟨e'.trans e, hsf⟩
    · rw [hz1] at hf; cases hf

/-! ## The front -/

/-- `update_time_stamp` keeps the current and idle thread. -/
theorem ci_updateTimeStamp (c i : ObjRef) :
    IK (fun s : State Unit => s.curThread = c ∧ s.idleThread = i) (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp
  repeat' (first | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

/-- **The syscall front** `update_time_stamp ; check_budget_restart` from the
entry state: every outcome has `Rdy` and `OS`; a `true` outcome is an
outcome of `update_time_stamp` with `Suff`. -/
theorem rd_front {σ : State Unit} (hR : Rdy σ) (hO : Sched.OffReady σ) (hv : SInvV.ValidMachineTime σ)
    (hS : SInvB.ScInv σ) (hcs : SInvQ.CurScT σ) {xt : Tcb} (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hst : xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
    (hQ : SInvQ.CtQ σ) (hSi : SInvQ.Simple σ) (hCB : SInvQ.CB σ)
    (hHB : σ.schedulerAction = .resumeCurThread → σ.curThread ∉ σ.releaseQueue)
    (hCA : CAx σ) (hni : σ.curThread ≠ σ.idleThread) {r : Bool × State Unit}
    (hr : r ∈ (((updateTimeStamp (Z := Unit)) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1) :
    Rdy r.2 ∧ OS r.2 ∧ (r.1 = true → ∃ y ∈ (updateTimeStamp (Z := Unit) σ).1, r.2 = y.2 ∧ Suff y.2) := by
  obtain ⟨y, hy, hr⟩ := hr
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨eq, ea, er, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ y hy
  have hR' := rdy_updateTimeStamp hv hR hy
  have hO' := SInvO.offReady_updateTimeStamp hv hO hy
  have hS' : SInvB.ScInv y.2 := by unfold SInvB.ScInv SInvB.ScSym SInvB.ScBackS SInvB.ScFwd SInvB.RNE; rw [ek]; exact hS
  have hcs' : SInvQ.CurScT y.2 := by intro x hx; rw [ek, et] at hx; rw [ec]; exact hcs x hx
  have hct' : y.2.kheap y.2.curThread = some (.tcb xt) := by rw [ek, et]; exact hct
  have hQ' : SInvQ.CtQ y.2 := by intro d p; rw [eq, et]; exact hQ d p
  have hSi' : SInvQ.Simple y.2 := by intro t; rw [ea]; exact hSi t
  have hCB' : SInvQ.CB y.2 := by
    intro e; rw [ea] at e
    rcases hCB e with h | h
    · left; rw [ek, et]; exact h
    · right; rw [et, eit]; exact h
  have hHB' : y.2.schedulerAction = .resumeCurThread → y.2.curThread ∉ y.2.releaseQueue := by
    intro e; rw [ea] at e; rw [et, er]; exact hHB e
  have hCA' : CAx y.2 := by
    intro h; rw [et, eit] at h
    obtain ⟨x, c, z, n, h1, h2, h3, h4⟩ := hCA h
    exact ⟨x, c, z, n, by rw [ek, et]; exact h1, h2, by rw [ek]; exact h3, h4⟩
  have hni' : y.2.curThread ≠ y.2.idleThread := by rw [et, eit]; exact hni
  obtain ⟨h1, h2, h3⟩ := rd_cbr hR' hO' hS' hcs' hct' hst hQ' hSi' hCB' hHB' hCA' hni' hr
  exact ⟨h1, h2, fun ht => ⟨y, hy, (h3 ht).1, (h3 ht).2⟩⟩

end

end Fl4Proofs.P3.SInvR
