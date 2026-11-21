/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq1): **`EpQAll` as a
corollary of carried invariants** (spec side only, outside the `JAtZ` cone).

`EpQAll σ := ∀ e, EpQPre σ e` (SpecFinOutEp, the CNode decode's `hQ`): every
endpoint-queued thread is `MemOKE` (a TCB whose SC, when it has no fault, is
`ScOK`: refills, a ready and sufficient head when active, `RefOK` when active
and sporadic), plus `ScBack` and `ActReady`.

* `RPosS y` / **`RPos σ` [J]** (l4v `valid_refills` of a sporadic SC, the part
  `RefOK` needs beyond rd's `RV`): an active SC with a non-zero period (not
  round-robin: `isRoundRobin` is `scPeriod = 0`) has only positive refill
  amounts, summing below `2 ^ 64` and to at least `MIN_BUDGET` (the budget;
  the lower bound keeps `head_insufficient_loop` from merging a single
  refill). Round-robin SCs are exempt: their empty
  tail (`maybe_add_empty_tail`, `refill_reset_rr`) has amount 0.
* **`epQAll_of`**: `Rdy ∧ ScInv ∧ EpQB ∧ RPos ⇒ EpQAll`. A queued thread is
  blocked on the endpoint (EpQB); without a fault it is `BlkR`, so bound to an
  active SC with a ready head (rd's R3); `RV` gives the head's `MIN_BUDGET`
  (sufficiency) and the sum; `RPos` the positive amounts; sb2's `RNE` the
  non-empty refills; `ScBackS` is `ScBack`; R2 + RV + RNE give `ActReady`.
* `boot_rpos` (non-vacuity only, per the 2026-11-20 decision).
-/
import Fl4Proofs.P3.SpecInvRdA
import Fl4Proofs.P3.SpecInvSbK
import Fl4Proofs.P3.SpecInvNtfnQ
import Fl4Proofs.P3.SpecFinOutEp
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvB

noncomputable section

/-- The refill facts of one active sporadic SC. -/
def RPosS (y : SchedContext) : Prop :=
  scActive y = true → y.scPeriod ≠ 0 → (∀ r ∈ y.scRefills, 0 < r.rAmount.toNat) ∧ rsum y.scRefills < 2 ^ 64 ∧
    MIN_BUDGET.toNat ≤ rsum y.scRefills

/-- **RPos [J]** (l4v `valid_refills`, sporadic part): every active sporadic
SC has positive refill amounts summing below `2 ^ 64` and to at least
`MIN_BUDGET` (the sum is the configured budget: charges and merges conserve
it, `refill_new` / `refill_update` set it to a decoded budget). -/
def RPos (σ : State Unit) : Prop := ∀ p y n, σ.kheap p = some (.schedContext y n) → RPosS y

/-- **EpQAll** (INV-PLAN E7, the CNode decode's `hQ`). -/
def EpQAll (σ : State Unit) : Prop := ∀ e, Sched.EpQPre σ e

theorem boot_rpos : RPos (initASt (Z := Unit)) := by
  intro p y n hy ha hp
  have hy' : initKheap p = some (.schedContext y n) := hy
  by_cases e : p = idleScPtr
  · subst e
    rw [SInvV.initKheap_idleSc] at hy'
    cases hy'
    exact absurd rfl hp
  · exfalso
    unfold initKheap at hy'
    simp only [Function.update_apply, e, if_false] at hy'
    split_ifs at hy' <;> cases hy'

/-- An active SC's `ScOK` clauses from `RV`, `RNE`, `RPos` and a ready head. -/
theorem scOK_clauses {σ : State Unit} {c : ObjRef} {y : SchedContext} {k : Nat}
    (hk : σ.kheap c = some (.schedContext y k)) (hV : RV σ) (hN : RNE σ) (hP : RPos σ)
    (hrd : scActive y = true → refillReady σ.curTime (refillHd y) = true) :
    ((y.scSporadic = true ∨ scActive y = true) → y.scRefills ≠ []) ∧
    (scActive y = true → refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true) ∧
    (scActive y = true → y.scPeriod ≠ 0 → Sched.RefOK y) := by
  have hne := hN c y k hk
  refine ⟨hne, fun ha => ⟨hrd ha, suff0_of (hV c y k hk ha).2.1⟩, fun ha hp => ?_⟩
  obtain ⟨hpos, hsum, -⟩ := hP c y k hk ha hp
  exact ⟨hne (Or.inr ha), hpos, hsum, (hV c y k hk ha).2.1⟩

/-- **The corollary.** -/
theorem epQAll_of {σ : State Unit} (hR : Rdy σ) (hS : ScInv σ) (hE : EpQB σ) (hP : RPos σ) : EpQAll σ := by
  obtain ⟨-, hR2, hR3, hV, -⟩ := hR
  have hN : RNE σ := hS.2
  have hB : Sched.ScBack σ := fun u xu c h1 h2 => hS.back u xu c h1 h2
  refine fun e y hy => ⟨fun u hu => ?_, hB, ?_⟩
  · obtain ⟨xu, hku, hbl⟩ := hE e y u hy hu
    refine ⟨xu, hku, fun hf c hc => ?_⟩
    obtain ⟨ys, k, hky, -, -⟩ := hS.back u xu c hku hc
    have hblk : BlkR xu.tcbState xu.tcbFault := by
      cases hst : xu.tcbState <;> simp only [hst, epBlocked, reduceCtorEq] at hbl
      all_goals first
        | exact Or.inr (Or.inl ⟨_, _, rfl, fun b h => by rw [hf] at h; cases h⟩)
        | exact Or.inr (Or.inr ⟨_, _, _, rfl⟩)
    obtain ⟨x', c', y', n', hx', hc', hy', ha', hr'⟩ := hR3 u xu c hku hblk hc
    rw [hku] at hx'; cases hx'
    rw [hc] at hc'; cases hc'
    rw [hky] at hy'; cases hy'
    exact ⟨ys, k, hky, scOK_clauses hky hV hN hP fun _ => hr'⟩
  · refine Sched.actReady_iff.2 fun t ht _ => ?_
    obtain ⟨x, c, ys, n, hx, hc, hy', ha, hr⟩ := hR2 t ht
    obtain ⟨h1, h2, -⟩ := scOK_clauses hy' hV hN hP fun _ => hr
    exact ⟨x, c, ys, n, hx, hc, hy', h1 (Or.inr ha), (h2 ha).1, (h2 ha).2⟩

end

end Fl4Proofs.P3.SInvE
