/-
P3 (DESIGN.md §9), invariant line G1 (rd8b): **the outcomes of `refill_new`
and `refill_update`** (spec side only, outside the JAtZ cone; KENTRY-PLAN rd7
handoff 2, configure by hand).

Both rewrite only the SC at `p` (a chain of `update_sched_context`s,
`updSc_twice`), keeping its bound TCB, and set refill max and period. `RV`'s
round-robin clause does not hold between their steps (one refill before
`maybe_add_empty_tail`), so `Rdy` is shown on the whole outcome:

* `mae_out`: `maybe_add_empty_tail` appends `(head time, 0)` when the period is 0.
* **`refillNew_out`**: the refills are `[(cur_time, budget)]`, plus `(cur_time, 0)`
  for a round-robin period.
* **`refillUpdate_out`** (refills non-empty): the head keeps its amount cut to the
  budget, its time is the current time when it was ready (else kept), the sum is
  the budget, and a round-robin SC ends with two refills.
-/
import Fl4Proofs.P3.SpecInvRd8bB
import Fl4Proofs.P3.SpecInvEqB
open Classical

namespace Fl4Proofs.P3.SInvR.B8
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

theorem updSc_twice (σ : State Unit) (p : ObjRef) (a b : SchedContext) (n : Nat) :
    Sched.updSc (Sched.updSc σ p a n) p b n = Sched.updSc σ p b n := by
  simp [Sched.updSc, Notif.updK]

theorem updSc_self {σ : State Unit} {p : ObjRef} {z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext z n)) : Sched.updSc σ p z n = σ := by
  have e : Function.update σ.kheap p (some (.schedContext z n)) = σ.kheap := by
    rw [← hk]; exact Function.update_eq_self p σ.kheap
  simp only [Sched.updSc, Notif.updK, e]

/-- `maybe_add_empty_tail`. -/
theorem mae_out {σ : State Unit} {p : ObjRef} {z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext z n)) {r : Unit × State Unit}
    (hr : r ∈ (maybeAddEmptyTail (Z := Unit) p σ).1) :
    r.2 = Sched.updSc σ p (if z.scPeriod = 0 then
      { z with scRefills := z.scRefills ++ [{ rTime := (refillHd z).rTime, rAmount := 0 }] } else z) n := by
  unfold maybeAddEmptyTail at hr
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨x, m, hx, rfl⟩ := SInvE.mem_isRoundRobin hw
  rw [hk] at hx; cases hx
  dsimp only at hr
  unfold NonDet.when at hr
  split_ifs at hr with hp
  · have hp' : z.scPeriod = 0 := of_decide_eq_true hp
    rw [if_pos hp']
    obtain ⟨w1, hw1, hr⟩ := hr
    obtain ⟨-, rfl⟩ := SInvE.mem_getRefillHead hk hw1
    dsimp only at hr
    obtain ⟨w2, hw2, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hw2
    dsimp only at hr
    rw [SInvE.refillAddTail_eq hk] at hr
    obtain rfl := SInvE.mem_one rfl hr
    rfl
  · have hp' : ¬ z.scPeriod = 0 := fun e => hp (decide_eq_true e)
    rw [if_neg hp']
    obtain rfl : r = ((), σ) := hr
    exact (updSc_self hk).symm

/-- **`refill_new p mr b per`**. -/
theorem refillNew_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (mr : Nat) (b per : Ticks) {r : Unit × State Unit}
    (hr : r ∈ (refillNew (Z := Unit) p mr b per σ).1) :
    ∃ z, r.2 = Sched.updSc σ p z n ∧ z.scTcb = y.scTcb ∧ z.scRefillMax = mr ∧ z.scPeriod = per ∧
      z.scRefills = { rTime := σ.curTime, rAmount := b } ::
        (if per = 0 then [{ rTime := σ.curTime, rAmount := 0 }] else []) := by
  unfold refillNew at hr
  rw [Notif.nd_gets_bind] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq hk _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_pure_bind'] at hr
  try dsimp only at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  have e := mae_out (SInvE.updSc_kheap_self _ _ _ _) hr
  simp only [updSc_twice] at e
  refine ⟨_, e, ?_, ?_, ?_, ?_⟩ <;> split
  all_goals first
    | rfl
    | (simp_all [scPeriodUpdate, scBudgetUpdate, scRefillMaxUpdate, scRefillsUpdate] <;> rfl)
    | simp_all [scPeriodUpdate, scBudgetUpdate, scRefillMaxUpdate, scRefillsUpdate]

/-- **`refill_update p per b mr`** of an SC with refills. -/
theorem refillUpdate_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) (per b : Ticks) (mr : Nat)
    {r : Unit × State Unit} (hr : r ∈ (refillUpdate (Z := Unit) p per b mr σ).1) :
    ∃ z, r.2 = Sched.updSc σ p z n ∧ z.scTcb = y.scTcb ∧ z.scRefillMax = mr ∧ z.scPeriod = per ∧
      z.scRefills ≠ [] ∧
      (refillHd z).rAmount = (if b ≤ (refillHd y).rAmount then b else (refillHd y).rAmount) ∧
      ((refillHd z).rTime = (refillHd y).rTime ∨ (refillHd z).rTime = σ.curTime) ∧
      (refillReady σ.curTime (refillHd y) = true → (refillHd z).rTime = σ.curTime) ∧
      rsum z.scRefills = b.toNat ∧ (per = 0 → 2 ≤ z.scRefills.length) := by
  unfold refillUpdate at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq hk _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
  simp only [updSc_twice] at hr
  set y4 : SchedContext := scBudgetUpdate (fun _ => b) (scPeriodUpdate (fun _ => per)
    (scRefillMaxUpdate (fun _ => mr) (scRefillsUpdate (fun rfs => [the rfs.head?]) y))) with hy4
  obtain ⟨z0, hz0, hr⟩ := hr
  obtain rfl := mem_getScRefillReady (SInvE.updSc_kheap_self _ _ _ _) hz0
  dsimp only at hr
  obtain ⟨w5, hw5, hr⟩ := hr
  have hw5' : ∃ h5 : Refill, w5.2 = Sched.updSc σ p { y4 with scRefills := [h5] } n ∧
      h5.rAmount = (refillHd y).rAmount ∧ (h5.rTime = (refillHd y).rTime ∨ h5.rTime = σ.curTime) ∧
      (refillReady σ.curTime (refillHd y) = true → h5.rTime = σ.curTime) := by
    unfold NonDet.when at hw5
    split_ifs at hw5 with hrd
    · obtain ⟨u, hu, hw5⟩ := hw5
      obtain rfl := Set.mem_singleton_iff.1 hu
      dsimp only at hw5
      rw [Sched.updateRefillHd_eq (SInvE.updSc_kheap_self _ _ _ _)] at hw5
      obtain rfl := SInvE.mem_one rfl hw5
      refine ⟨{ refillHd y with rTime := σ.curTime }, ?_, rfl, Or.inr rfl, fun _ => rfl⟩
      simp only [updSc_twice]; rfl
    · obtain rfl := Set.mem_singleton_iff.1 hw5
      exact ⟨refillHd y, rfl, rfl, Or.inl rfl, fun h => absurd h hrd⟩
  obtain ⟨h5, e5, ha5, ht5, hr5⟩ := hw5'
  rw [e5] at hr
  obtain ⟨w6, hw6, hr⟩ := hr
  obtain ⟨-, rfl⟩ := SInvE.mem_getRefillHead (SInvE.updSc_kheap_self _ _ _ _) hw6
  dsimp only at hr
  have hh5 : refillHd { y4 with scRefills := [h5] } = h5 := rfl
  rw [hh5] at hr
  split at hr
  · rename_i hb
    rw [Notif.nd_bind_one (Sched.updateRefillHd_eq (SInvE.updSc_kheap_self _ _ _ _) _)] at hr
    have e := mae_out (SInvE.updSc_kheap_self _ _ _ _) hr
    simp only [updSc_twice] at e
    refine ⟨_, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> split
    all_goals first
      | exact ht5
      | exact hr5
      | rfl
      | (simp_all [scPeriodUpdate, scBudgetUpdate, scRefillMaxUpdate, scRefillsUpdate, rsum] <;> rfl)
      | simp_all [scPeriodUpdate, scBudgetUpdate, scRefillMaxUpdate, scRefillsUpdate, rsum]
  · rename_i hb
    have hlt : h5.rAmount.toNat ≤ b.toNat := by
      rw [BitVec.le_def] at hb; omega
    rw [Notif.nd_pure_bind'] at hr
    try dsimp only at hr
    rw [Notif.nd_pure_bind'] at hr
    try dsimp only at hr
    rw [SInvE.refillAddTail_eq (SInvE.updSc_kheap_self _ _ _ _)] at hr
    obtain rfl := SInvE.mem_one rfl hr
    refine ⟨_, updSc_twice _ _ _ _ _, rfl, rfl, rfl, by simp, ?_, ?_, ?_, ?_, fun _ => by simp⟩
    · show h5.rAmount = _
      rw [ha5, if_neg (by rw [← ha5]; exact hb)]
    · exact ht5
    · exact hr5
    · show rsum ([h5] ++ [_]) = _
      rw [SInvE.rsum_snoc]
      show h5.rAmount.toNat + (rsum []) + (b - h5.rAmount).toNat = b.toNat
      rw [SInvE.sub_toNat hlt]
      simp only [SInvE.rsum_nil]
      omega

/-! ## `Rdy` across the two refill writers -/

theorem active_of_min {z : SchedContext} (h : MIN_REFILLS ≤ z.scRefillMax) : scActive z = true := by
  show decide (0 < z.scRefillMax) = true
  exact decide_eq_true (lt_of_lt_of_le (by decide) h)

theorem updSc_other (σ : State Unit) (p : ObjRef) (z : SchedContext) (n : Nat) :
    ∀ q, q ≠ p → (Sched.updSc σ p z n).kheap q = σ.kheap q := fun q hq => by
  simp [Sched.updSc, Notif.updK, hq]

theorem rsum_lt (l : List Refill) (b : Ticks) (h : rsum l = b.toNat) : rsum l < 2 ^ 64 := by
  rw [h]; exact b.isLt

/-- **`refill_new p mr b per`** keeps `Rdy` (decode: `MIN_REFILLS ≤ mr`, `MIN_BUDGET ≤ b`): the
new head is at the current time, so a released SC stays released (`rdy_frame1`, no exclusivity). -/
theorem rd_refillNew (p : ObjRef) (mr : Nat) (b per : Ticks) (σ : State Unit) (hR : Rdy σ)
    {y : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext y n)) (hm : MIN_REFILLS ≤ mr)
    (hb : MIN_BUDGET ≤ b) {r : Unit × State Unit} (hr : r ∈ (refillNew (Z := Unit) p mr b per σ).1) :
    Rdy r.2 := by
  obtain ⟨z, e, -, hmx, hper, hrf⟩ := refillNew_out hk mr b per hr
  have hza : scActive z = true := active_of_min (hmx ▸ hm)
  have hh : refillHd z = { rTime := σ.curTime, rAmount := b } := by unfold refillHd; rw [hrf]; rfl
  have hrd : refillReady σ.curTime (refillHd z) = true := by rw [hh]; exact ready_of_nat (le_refl _)
  have hs : rsum z.scRefills = b.toNat := by
    rw [hrf]; split <;> simp [rsum]
  have hkp : (Sched.updSc σ p z n).kheap p = some (.schedContext z n) := SInvE.updSc_kheap_self _ _ _ _
  rw [e]
  refine rdy_frame1 hR (updSc_other σ p z n) rfl rfl rfl (fun y' n' hy' _ _ => ?_) (fun x hx => ?_)
    (fun x hx => ?_) (fun z' n' hz' _ => ?_) rfl (fun y' n' hy' _ => ⟨z, n, hkp, hza⟩) rfl (fun _ z' m hz' => ?_)
  · rw [hk] at hy'; cases hy'; exact ⟨z, hkp, hza, hrd⟩
  · rw [hk] at hx; cases hx
  · rw [hkp] at hx; cases hx
  · rw [hkp] at hz'; cases hz'
    refine ⟨hmx ▸ hm, by rw [hh]; exact hb, rsum_lt _ b hs, fun h0 => ?_⟩
    rw [hrf, if_pos (hper ▸ h0)]; simp
  · rw [hkp] at hz'; cases hz'
    refine ⟨by rw [hrf]; simp, by rw [hh]⟩

/-- **`refill_update p per b mr`** of an active SC whose bound threads are `Excl` (configure: the
SC's thread was dequeued and released-removed, is runnable and not the switch target). -/
theorem rd_refillUpdate (p : ObjRef) (per b : Ticks) (mr : Nat) (σ : State Unit) (hR : Rdy σ)
    {y : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (hya : scActive y = true) (hm : MIN_REFILLS ≤ mr) (hb : MIN_BUDGET ≤ b) (hX : Excl σ p)
    {r : Unit × State Unit} (hr : r ∈ (refillUpdate (Z := Unit) p per b mr σ).1) : Rdy r.2 := by
  obtain ⟨z, e, -, hmx, hper, hzn, hza, hzt, hzr, hs, hrr⟩ := refillUpdate_out hk hne per b mr hr
  have hkp : (Sched.updSc σ p z n).kheap p = some (.schedContext z n) := SInvE.updSc_kheap_self _ _ _ _
  have hzA : scActive z = true := active_of_min (hmx ▸ hm)
  rw [e]
  refine rdy_framex hR (updSc_other σ p z n) rfl rfl rfl hX (fun x hx => ?_) (fun x hx => ?_)
    (fun z' n' hz' _ => ?_) rfl (fun y' n' hy' _ => ⟨z, n, hkp, hzA⟩) rfl (fun hpi z' m hz' => ?_)
  · rw [hk] at hx; cases hx
  · rw [hkp] at hx; cases hx
  · rw [hkp] at hz'; cases hz'
    refine ⟨hmx ▸ hm, ?_, rsum_lt _ b hs, fun h0 => hrr (hper ▸ h0)⟩
    rw [hza]
    split
    · exact hb
    · exact (hR.2.2.2.1 p y n hk hya).2.1
  · rw [hkp] at hz'; cases hz'
    refine ⟨hzn, ?_⟩
    have hI := hR.2.2.2.2.2 y n (by rw [← hpi]; exact hk)
    rcases hzt with h1 | h1
    · rw [h1]; exact hI.2
    · rw [h1]

end

end Fl4Proofs.P3.SInvR.B8
