/-
P3 (DESIGN.md §9), invariant line G1 (rd14f, KENTRY-PLAN rd14e-3): **the
preemption path at a preempted state with ct in any state** (spec side only).

rd10's `charge_ss4` reads ct's state only through `excl_entry` (`Excl` of
cur_sc for a Running ct). At a preempted state of a perform ct is Restart (or
Inactive, after its own finalisation), so `Excl` comes from rd8p's
`excl_of_hold` (`CurHold` and ctq's `EB true`) instead.

* **`charge_ss4X`**: rd10's `charge_ss4` with its facts explicit and `Excl`
  given (ct a TCB bound to an active cur_sc, ScInv, `CB`, the release-queue
  half of ctq's `HB`).
* **`ss4_preemptionPath`**: from rd8p's facts at the preempted state (`Rdy`,
  `NQ []`, `ScInv`, `CKN`, `EB true`, `CurHold`), ct ≠ idle, and two facts the
  deletion walk carries — a ct bound to cur_sc finds cur_sc active with
  `OffReady`, an unbound ct finds no resume — every outcome of
  `preemption_path` has `SS4`. Three branches as rd8p's `rd_preemptionPath`
  (check_budget, or charge_budget false, or consumed := 0); each ends in rd9's
  `AW9`, which `maybe_handle_interrupt` keeps (rd10's `aw9_maybeHandleInterrupt`).
-/
import Fl4Proofs.P3.SpecInvRd14fA
import Fl4Proofs.P3.SpecInvRd8wB
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d

noncomputable section

set_option maxHeartbeats 1000000

/-- **rd10's `charge_ss4` with explicit facts and `Excl` given** (ct in any state). -/
theorem charge_ss4X {s : State Unit} (hR : Rdy s) (hSc : SInvB.ScInv s) {xt : Tcb}
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    {y : SchedContext} {n : Nat} (hky : s.kheap s.curSc = some (.schedContext y n)) (hact : scActive y = true)
    (hX : Excl s s.curSc) (hcb : SInvQ.CB s)
    (hhb : s.schedulerAction = .resumeCurThread → s.curThread ∉ s.releaseQueue)
    (hni : s.curThread ≠ s.idleThread) (u : Ticks) (c : Bool) {z : Unit × State Unit}
    (hz : z ∈ (chargeBudget (Z := Unit) u c s).1) : A10.SS4 z.2 := by
  obtain ⟨y0, k0, hy0, hyT, hne⟩ := hSc.back s.curThread xt s.curSc hct hb
  rw [hky] at hy0; cases hy0
  have hne' : y.scRefills ≠ [] := hne (Or.inr hact)
  obtain ⟨s1, hR1, hO1, hr1⟩ := rd_chargeBudget_head hR hky (fun _ => ⟨hact, hne', fun _ => hX⟩) u c hz
  obtain ⟨z0, e, e1, e2, e3, e4, e5, e6⟩ := hO1
  subst e
  have hk1 : ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit).kheap s.curSc =
      some (.schedContext z0 n) := kh_upd _ _ _ _
  have ha1 : scActive z0 = true := by simp only [scActive, e2]; exact hact
  have hcs' : s.curThread ≠ s.curSc := fun e => by rw [e, hky] at hct; cases hct
  have hct1 : ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit).kheap s.curThread =
      some (.tcb xt) := by simp [Notif.updK, hcs', hct]
  obtain ⟨-, hA⟩ := rd_cbTail' c _ hR1 hk1 ha1 hct1 hb (fwd_chargeOut hSc.fwd hky e1) hr1
  obtain ⟨hcf, hid⟩ := cbTail_cf hr1
  have hc0 : z.2.consumedTime = 0 := by
    simp only [cfS, Prod.mk.injEq] at hcf; rw [hcf.1]
  have hnr : z.2.schedulerAction ≠ .resumeCurThread := by
    by_cases hres : s.schedulerAction = .resumeCurThread
    · have hrun : runnable xt.tcbState = true := by
        rcases hcb hres with ⟨x', hx', hr'⟩ | hi
        · rw [hct] at hx'; cases hx'; exact hr'
        · exact absurd hi hni
      have hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true :=
        Sched.schedulable_of hct1 hb hrun hk1 ha1 (hhb hres)
      exact fun e => by have h' := hA hsch; (try dsimp only at h'); rw [h'] at e; cases e
    · by_cases hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true
      · exact fun e => by have h' := hA hsch; (try dsimp only at h'); rw [h'] at e; cases e
      · have h' := hid (Bool.eq_false_iff.mpr hsch); (try dsimp only at h'); rw [h']; exact hres
  have ect : z.2.curThread = s.curThread := congrArg (fun p => p.2.2.1) hcf
  have hC : CtR z.2 := by
    by_cases hsch : schedulable s.curThread ({ updSc s s.curSc z0 n with consumedTime := 0 } : State Unit) = true
    · apply A8.ctR_of_cq
      rw [ect]
      exact A10.cq_cbTail' c _ hR1 hk1 ha1 hct1 hb (e1.trans hyT) hsch hr1
    · have e' := hid (Bool.eq_false_iff.mpr hsch)
      rw [e']
      exact A8.ctR_unsched (Bool.eq_false_iff.mpr hsch)
  exact ⟨Or.inr (Or.inl ⟨hc0, hnr⟩), fun e => absurd e hnr, hC, fun e => absurd e hnr⟩

/-- `maybe_handle_interrupt` from rd9's `AW9` ends in `SS4`. -/
theorem ss4_mhi {w : State Unit} (hw : A9.AW9 w) : ∀ z ∈ (maybeHandleInterrupt (Z := Unit) true w).1, A10.SS4 z.2 :=
  fun z hz => by
    obtain ⟨⟨-, a, -⟩, -, b, c, d⟩ := A10.aw9_maybeHandleInterrupt true w hw z hz
    exact ⟨a, b, c, d⟩

/-- **The preemption path at a preempted state** (module docstring). -/
theorem ss4_preemptionPath {p : State Unit} (hR : Rdy p) (hN : NQ [] p) (hS : SInvB.ScInv p)
    (hK : R14.CKN p) (hEB : SInvQ.EB true p) (hH : B8p.CurHold p) (hni : p.curThread ≠ p.idleThread)
    (hBd : ∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = some p.curSc →
      (∀ y n, p.kheap p.curSc = some (.schedContext y n) → scActive y = true) ∧ Sched.OffReady p)
    (hU : ∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = none → NRes p) :
    ∀ z ∈ (preemptionPath (Z := Unit) p).1, A10.SS4 z.2 := by
  have hX : Excl p p.curSc := B8p.excl_of_hold hH hEB
  have hcb : SInvQ.CB p := hEB.2.2
  have hhb : p.schedulerAction = .resumeCurThread → p.curThread ∉ p.releaseQueue := hEB.2.1.2.2
  have nres_of : (∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = some p.curSc →
      runnable x.tcbState = true → p.curThread ∉ p.releaseQueue → False) → NRes p := by
    intro hF hres
    rcases hcb hres with ⟨x, hx, hr⟩ | hi
    · rcases (hK x hx).1 with h0 | h0
      · exact hU x hx h0 hres
      · exact hF x hx h0 hr (hhb hres)
    · exact hni hi
  intro y hy
  unfold preemptionPath at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  try dsimp only at hy
  split at hy
  · -- (1) ct schedulable: ct bound to cur_sc, which is active
    rename_i hs
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨xt, c, z, m, hct, hc0, hz, ha⟩ := actB_of_schedulable hs
    have hb : xt.tcbSchedContext = some p.curSc := by
      rcases (hK xt hct).1 with h | h
      · rw [h] at hc0; cases hc0
      · exact h
    rw [hb] at hc0; cases hc0
    have hb' : ∀ x, p.kheap p.curThread = some (.tcb x) → x.tcbSchedContext = some p.curSc := by
      intro x hx; rw [hct] at hx; cases hx; exact hb
    rcases checkBudget_cases hw with ⟨e, hSf⟩ | ⟨-, hc⟩
    · rw [e] at hy
      have hO : Sched.OffReady p := (hBd xt hct hb).2
      exact ss4_mhi ⟨⟨hR, Or.inl ⟨hO, hSf⟩, hN⟩, hS, fun _ _ => actB_of_schedulable hs,
        A8.ctR_of_off hb' hO, fun _ x hx => hb' x hx⟩ y hy
    · obtain ⟨y0, k0, hy0, -, hne⟩ := hS.back p.curThread xt p.curSc hct hb
      rw [hz] at hy0; cases hy0
      have hR2 := (rd_chargeBudget hR hz ha (hne (Or.inr ha)) (fun _ _ => hX) hct hb hS.fwd _ true hc).1
      have h4 := charge_ss4X hR hS hct hb hz ha hX hcb hhb hni _ true hc
      exact ss4_mhi ⟨⟨hR2, h4.1, nq_chargeBudget (K := []) _ _ p hN _ hc⟩,
        SInvB.si_chargeBudget _ _ p hS _ hc, h4.2.1, h4.2.2.1, h4.2.2.2⟩ y hy
  · -- ct not schedulable
    rename_i hs
    have hs' : schedulable p.curThread p = false := by
      cases h : schedulable p.curThread p
      · rfl
      · exact absurd h hs
    obtain ⟨w1, hw1, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hw1] at hy
    obtain ⟨w2, hw2, hy⟩ := hy
    obtain ⟨x, n, hk, rfl⟩ := SInvE.mem_getScActive hw2
    try dsimp only at hy
    split at hy
    · -- (2) cur_sc active: the charge, no tail
      rename_i ha
      obtain ⟨w3, hw3, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hw3] at hy
      obtain ⟨z, hz, hy⟩ := hy
      have hnr : NRes p := nres_of fun x' hx' hb hr hq => by
        have := Sched.schedulable_of hx' hb hr hk ha hq
        rw [hs'] at this; cases this
      have hne : x.scRefills ≠ [] := hS.2 p.curSc x n hk (Or.inr ha)
      obtain ⟨s1, hR1, hO, hz1⟩ := rd_chargeBudget_head hR hk (fun _ => ⟨ha, hne, fun _ => hX⟩) _ false hz
      have hs1 : schedulable s1.curThread s1 = false := by
        rw [sched_of_bf (B8p.bf_chargeOut hk hO)]
        exact hs'
      have ez : z.2 = s1 := (cbTail_cf hz1).2 hs1
      obtain ⟨z0, e, -⟩ := hO
      have hN2 := nq_chargeBudget (K := []) _ _ p hN z hz
      have hS2 := SInvB.si_chargeBudget _ _ p hS z hz
      rw [ez] at hy hN2 hS2
      subst e
      have hnr' : NRes ({ updSc p p.curSc z0 n with consumedTime := 0 } : State Unit) := hnr
      exact ss4_mhi ⟨⟨hR1, Or.inr (Or.inl ⟨rfl, hnr'⟩), hN2⟩, hS2, fun e => absurd e hnr',
        A8.ctR_unsched hs1, fun e => absurd e hnr'⟩ y hy
    · -- (3) cur_sc inactive: consumed_time := 0
      rename_i ha
      obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hz] at hy
      try dsimp only at hy
      have hnr : NRes p := nres_of fun x' hx' hb _ _ => ha ((hBd x' hx' hb).1 x n hk)
      have hnr' : NRes ({ p with consumedTime := 0 } : State Unit) := hnr
      have hsz : schedulable ({ p with consumedTime := 0 } : State Unit).curThread
          ({ p with consumedTime := 0 } : State Unit) = false := hs'
      exact ss4_mhi ⟨⟨rdy_consumed0 hR, Or.inr (Or.inl ⟨rfl, hnr'⟩), hN⟩, hS, fun e => absurd e hnr',
        A8.ctR_unsched hsz, fun e => absurd e hnr'⟩ y hy

end

end Fl4Proofs.P3.SInvR.A14f
