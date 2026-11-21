/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd6): **`charge_budget`'s
charge** (spec side only, outside the `JAtZ` cone; KENTRY-PLAN rd5 handoff 1).

* `RV`'s round-robin clause (rd6, lead decision; SpecInvRdA): an active SC with
  `scPeriod = 0` has at least two refills.
* `rrr_list`: `refill_reset_rr`'s list step on `a :: b :: t` (head := head +
  tail, tail := 0): non-empty, the head's time kept, its amount `a + last`
  (no wrap: both are summands of a sum below `2 ^ 64`), sum and length kept.
* **`rd_refillResetRr`**: `Rdy` across `refill_reset_rr p` of an active
  round-robin SC (two refills by `RV`); only that SC's refills change, the
  head's release time is kept (so no `Excl` is needed: `rdy_frame1`).
* `cbTail c`: what `charge_budget` runs after `consumed_time := 0`.
* **`rd_chargeBudget_head`**: every outcome of `charge_budget u c` is an outcome
  of `cbTail c` from a state `s1` with `Rdy s1`, consumed time 0, and only the
  current SC rewritten (binding, refill max, period, sporadic flag, badge kept,
  refills non-empty when they were) — `ChargeOut`. Hypotheses at the charge
  (state facts, l4v `charge_budget`'s preconditions): the current SC is an SC;
  if it is not the idle SC it is active with non-empty refills (sb2's `RNE`),
  and when it is sporadic it is `Excl` (only the current thread is bound to it,
  and that thread is not queued, not the switch target, running).
-/
import Fl4Proofs.P3.SpecInvRdG
import Fl4Proofs.P3.SpecInvRdY
open Classical
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

section
open Fl4Spec

/-! ## `refill_reset_rr` -/

/-- `refill_reset_rr`'s list step (module docstring). -/
theorem rrr_list (a b : Refill) (t : List Refill) (hs : rsum (a :: b :: t) < 2 ^ 64) :
    let a' : Refill := { a with rAmount := a.rAmount + (the (b :: t).getLast?).rAmount }
    let L : List Refill := (a' :: b :: t).dropLast ++ [{ (the (a' :: b :: t).getLast?) with rAmount := 0 }]
    L ≠ [] ∧ the L.head? = a' ∧ (a'.rAmount.toNat = a.rAmount.toNat + (the (b :: t).getLast?).rAmount.toNat) ∧
      rsum L = rsum (a :: b :: t) ∧ L.length = (a :: b :: t).length := by
  intro a' L
  have hsp := rsum_split (b :: t) (List.cons_ne_nil _ _)
  have hsa : (a'.rAmount).toNat = a.rAmount.toNat + (the (b :: t).getLast?).rAmount.toNat := by
    show (a.rAmount + (the (b :: t).getLast?).rAmount).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]
    rw [rsum_cons] at hs; omega
  have hgl : (a' :: b :: t).getLast? = (b :: t).getLast? := List.getLast?_cons_cons
  have hdl : (a' :: b :: t).dropLast = a' :: (b :: t).dropLast := List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)
  have hL : L = a' :: ((b :: t).dropLast ++ [{ (the (b :: t).getLast?) with rAmount := 0 }]) := by
    show (a' :: b :: t).dropLast ++ _ = _
    rw [hdl, hgl]; rfl
  refine ⟨by rw [hL]; exact List.cons_ne_nil _ _, by rw [hL]; rfl, hsa, ?_, ?_⟩
  · rw [hL, rsum_cons, rsum_append, rsum_cons, hsa, rsum_cons]
    have e0 : rsum ([] : List Refill) = 0 := rfl
    have e1 : ({ (the (b :: t).getLast?) with rAmount := 0 } : Refill).rAmount.toNat = 0 := rfl
    rw [e0, e1]; omega
  · rw [hL]; simp

/-- **`Rdy` across `refill_reset_rr`** of an active round-robin SC (module
docstring). -/
theorem rd_refillResetRr {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap p = some (.schedContext x n)) (ha : scActive x = true) (hrr : x.scPeriod = 0)
    {r : Unit × State Unit} (hr : r ∈ (refillResetRr (Z := Unit) p σ).1) :
    Rdy r.2 ∧ ∃ zs, r.2 = updSc σ p { x with scRefills := zs } n ∧ zs ≠ [] ∧
      (refillHd { x with scRefills := zs }).rTime = (refillHd x).rTime := by
  obtain ⟨v1, v2, v3, v4⟩ := h.2.2.2.1 p x n hk ha
  have hlen := v4 hrr
  obtain ⟨a, b, t, e⟩ : ∃ a b t, x.scRefills = a :: b :: t := by
    rcases hx : x.scRefills with _ | ⟨a, _ | ⟨b, t⟩⟩
    · rw [hx] at hlen; simp at hlen
    · rw [hx] at hlen; simp at hlen
    · exact ⟨a, b, t, rfl⟩
  have hne : x.scRefills ≠ [] := by rw [e]; exact List.cons_ne_nil _ _
  unfold refillResetRr at hr
  rw [nd_bind_one (getRefillHead_eq hk hne), nd_bind_one (getRefillTail_eq hk hne),
    nd_bind_one (updateRefillHd_eq hk _), updateRefillTl_eq (kh_upd _ _ _ _), updSc_updSc] at hr
  obtain rfl : r = ((), _) := hr
  rw [e] at v3
  obtain ⟨l1, l2, l3, l4, l5⟩ := rrr_list a b t v3
  have eH : refillHd x = a := by unfold refillHd; rw [e]; rfl
  have eT : refillTl x = the (b :: t).getLast? := by unfold refillTl; rw [e]; rfl
  set zs := ((({ (the x.scRefills.head?) with rAmount := (refillHd x).rAmount + (refillTl x).rAmount } : Refill) ::
      x.scRefills.tail).dropLast ++ [{ (the (({ (the x.scRefills.head?) with
        rAmount := (refillHd x).rAmount + (refillTl x).rAmount } : Refill) :: x.scRefills.tail).getLast?) with
        rAmount := 0 }]) with hzs
  have hz : zs = ({ a with rAmount := a.rAmount + (the (b :: t).getLast?).rAmount } :: b :: t).dropLast ++
      [{ (the ({ a with rAmount := a.rAmount + (the (b :: t).getLast?).rAmount } :: b :: t).getLast?) with
        rAmount := 0 }] := by
    rw [hzs, ← eT]
    have e2 : the x.scRefills.head? = a := by rw [e]; rfl
    have e3 : x.scRefills.tail = b :: t := by rw [e]; rfl
    rw [e2, e3, eH]
  have hzs' : ({ { x with scRefills := (({ (the x.scRefills.head?) with
      rAmount := (refillHd x).rAmount + (refillTl x).rAmount } : Refill) :: x.scRefills.tail) } with
      scRefills := zs } : SchedContext) = { x with scRefills := zs } := rfl
  have hkp := kh_upd σ p { x with scRefills := zs } n
  have hkq : ∀ q, q ≠ p → (updSc σ p { x with scRefills := zs } n).kheap q = σ.kheap q :=
    fun q hq => by simp [Notif.updK, hq]
  have hHd : refillHd { x with scRefills := zs } = { a with rAmount := a.rAmount + (the (b :: t).getLast?).rAmount } := by
    show the zs.head? = _; rw [hz]; exact l2
  have hzne : zs ≠ [] := by rw [hz]; exact l1
  have hRT : (refillHd { x with scRefills := zs }).rTime = (refillHd x).rTime := by rw [hHd, eH]
  refine ⟨?_, zs, rfl, hzne, hRT⟩
  have hay : scActive { x with scRefills := zs } = scActive x := rfl
  refine rdy_frame1 h hkq rfl rfl rfl (fun y0 n0 hy0 ha0 hr0 => ?_) (fun x0 hx0 => by rw [hk] at hx0; cases hx0)
    (fun x0 hx0 => by rw [hkp] at hx0; cases hx0) (fun z m hz' _ => ?_) rfl
    (fun y0 n0 hy0 ha0 => ⟨_, n, hkp, by rw [hk] at hy0; cases hy0; exact ha0⟩) rfl
    (fun eI z m hz' => ?_)
  · rw [hk] at hy0; cases hy0
    refine ⟨_, hkp, ha0, ?_⟩
    exact ready_of_nat (by rw [hRT]; exact nat_of_ready hr0)
  · rw [hkp] at hz'; cases hz'
    refine ⟨v1, ?_, ?_, fun _ => ?_⟩
    · rw [hHd, BitVec.le_def, l3]; rw [eH, BitVec.le_def] at v2; omega
    · rw [hz, l4]; exact v3
    · rw [hz, l5]; rw [e] at hlen; exact hlen
  · rw [hkp] at hz'; cases hz'
    have := h.2.2.2.2.2 x n (by rw [← eI]; exact hk)
    exact ⟨hzne, by rw [hRT]; exact this.2⟩

/-! ## The charge of `charge_budget` -/

/-- What `charge_budget` runs after `consumed_time := 0`. -/
def cbTail (canTimeout : Bool) : NonDet (State Unit) Unit := do
  let ct ← NonDet.gets fun s : State Unit => s.curThread
  let sched ← NonDet.gets (schedulable ct)
  NonDet.when sched <| do
    endTimeslice canTimeout
    rescheduleRequired
    NonDet.modify fun s : State Unit => { s with reprogramTimer := true }

/-- The state after `charge_budget`'s charge (module docstring). -/
def ChargeOut (σ : State Unit) (x : SchedContext) (n : Nat) (s1 : State Unit) : Prop :=
  ∃ z, s1 = { updSc σ σ.curSc z n with consumedTime := 0 } ∧ z.scTcb = x.scTcb ∧ z.scRefillMax = x.scRefillMax ∧
    z.scPeriod = x.scPeriod ∧ z.scSporadic = x.scSporadic ∧ z.scBadge = x.scBadge ∧
    (x.scRefills ≠ [] → z.scRefills ≠ [])

theorem rdy_consumed0 {σ : State Unit} (h : Rdy σ) : Rdy ({ σ with consumedTime := 0 } : State Unit) :=
  rdy_congr h rfl rfl rfl rfl rfl fun _ h => h

/-- **`charge_budget`'s charge** (module docstring). -/
theorem rd_chargeBudget_head {σ : State Unit} {x : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n))
    (hC : σ.curSc ≠ σ.idleSc → scActive x = true ∧ x.scRefills ≠ [] ∧ (x.scPeriod ≠ 0 → Excl σ σ.curSc))
    (u : Ticks) (c : Bool) {r : Unit × State Unit} (hr : r ∈ (chargeBudget (Z := Unit) u c σ).1) :
    ∃ s1, Rdy s1 ∧ ChargeOut σ x n s1 ∧ r ∈ (cbTail c s1).1 := by
  unfold chargeBudget at hr
  rw [nd_gets_bind, nd_gets_bind] at hr
  obtain ⟨y1, hy1, hr⟩ := hr
  beta_reduce at hr
  rw [SInvV.sv_bind_modify] at hr
  have key : Rdy y1.2 ∧ ∃ z, y1.2 = updSc σ σ.curSc z n ∧ z.scTcb = x.scTcb ∧ z.scRefillMax = x.scRefillMax ∧
      z.scPeriod = x.scPeriod ∧ z.scSporadic = x.scSporadic ∧ z.scBadge = x.scBadge ∧
      (x.scRefills ≠ [] → z.scRefills ≠ []) := by
    by_cases hci : σ.curSc ≠ σ.idleSc
    · obtain ⟨ha, hne, hX⟩ := hC hci
      rw [NonDet.when, if_pos hci, nd_bind_one (isRoundRobin_eq hk)] at hy1
      dsimp only at hy1
      have hcont : ∀ y2 : Unit × State Unit,
          (Rdy y2.2 ∧ ∃ zs, y2.2 = updSc σ σ.curSc { x with scRefills := zs } n ∧ zs ≠ []) →
          y1 ∈ (updateSchedContext (Z := Unit) σ.curSc (fun sc => { sc with scConsumed := sc.scConsumed + u })
            y2.2).1 →
          Rdy y1.2 ∧ ∃ z, y1.2 = updSc σ σ.curSc z n ∧ z.scTcb = x.scTcb ∧ z.scRefillMax = x.scRefillMax ∧
            z.scPeriod = x.scPeriod ∧ z.scSporadic = x.scSporadic ∧ z.scBadge = x.scBadge ∧
            (x.scRefills ≠ [] → z.scRefills ≠ []) := by
        rintro y2 ⟨hR, zs, e2, hz2⟩ hy1
        have hR1 : Rdy y1.2 := rd_updateSchedContext σ.curSc
          (fun sc => { sc with scConsumed := sc.scConsumed + u }) (fun _ => ⟨rfl, rfl, rfl⟩) y2.2 hR y1 hy1
        rw [e2, updateSchedContext_eq (kh_upd _ _ _ _), updSc_updSc] at hy1
        obtain rfl := Set.mem_singleton_iff.1 hy1
        exact ⟨hR1, _, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => hz2⟩
      by_cases hrr : x.scPeriod = 0
      · rw [if_pos (by simpa using hrr)] at hy1
        obtain ⟨y2, hy2, hy1⟩ := hy1
        obtain ⟨hR, zs, e2, hz2, -⟩ := rd_refillResetRr h hk ha hrr hy2
        exact hcont y2 ⟨hR, zs, e2, hz2⟩ hy1
      · rw [if_neg (by simpa using hrr)] at hy1
        obtain ⟨y2, hy2, hy1⟩ := hy1
        exact hcont y2 (rd_refillBudgetCheck h hk hci (hX hrr) hrr hne ha u hy2) hy1
    · rw [NonDet.when, if_neg hci] at hy1
      obtain rfl : y1 = ((), σ) := hy1
      exact ⟨h, x, (updSc_self hk).symm, rfl, rfl, rfl, rfl, rfl, id⟩
  obtain ⟨hR1, z, e, e1, e2, e3, e4, e5, e6⟩ := key
  exact ⟨_, rdy_consumed0 hR1, ⟨z, by rw [e], e1, e2, e3, e4, e5, e6⟩, hr⟩

end

end

end Fl4Proofs.P3.SInvR
