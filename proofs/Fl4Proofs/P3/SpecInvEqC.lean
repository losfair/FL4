/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq1): **configure's
decode fact and `refill_new`** (spec side only, outside the `JAtZ` cone).

* `minBudget_le_usToTicks`: `MIN_BUDGET_US ≤ b ≤ MAX_PERIOD_US` gives
  `MIN_BUDGET ≤ us_to_ticks b` (platform constants only, as rd's
  `minBudget_le_maxPeriod`).
* `CfgDec inv`: a decoded SchedControl configure carries a budget of at least
  `MIN_BUDGET`; **`okv_fl4DecodeCfg`**: every `fl4DecodeInvocation` result
  satisfies it (`decode_sched_control_invocation_flags` range-checks the
  budget; every other branch returns another constructor).
* **`rpos_refillNew`**: `refill_new p mr b per` from `RPos` with
  `MIN_BUDGET ≤ b` keeps `RPos` (the new refill list is `[b]`, or a
  round-robin one when `per = 0`).
-/
import Fl4Proofs.P3.SpecInvEqB
import Fl4Proofs.P3.SpecInvUtD
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The budget bound -/

theorem minBudget_le_usToTicks {b : Ticks} (hlo : MIN_BUDGET_US ≤ b) (hhi : b ≤ MAX_PERIOD_US) :
    MIN_BUDGET ≤ usToTicks b := by
  have h2 := MIN_BUDGET_bound
  have h3 := getCurrentTime_buffer_bound
  have h4 := ticks_per_timer_unit_non_zero
  simp only [unat, maxTime, BitVec.toNat_allOnes] at h2 h3
  have ht : 0 < ticksPerTimerUnit.toNat :=
    Nat.pos_of_ne_zero fun h => h4 (BitVec.eq_of_toNat_eq (by simpa using h))
  unfold MIN_BUDGET_US at hlo
  rw [BitVec.le_def] at hlo hhi ⊢
  unfold MIN_BUDGET kernelWCETTicks usToTicks
  generalize ha : kernelWCETUs = a at hlo h2
  generalize hm : MAX_PERIOD_US = M at hhi h3
  generalize hT : ticksPerTimerUnit = T at h2 h3 ht
  generalize hU : timerUnit = U
  have h2t : 2 * a.toNat ≤ 2 * a.toNat * T.toNat := Nat.le_mul_of_pos_right _ ht
  have h2a : (2 * a).toNat = 2 * a.toNat := by rw [BitVec.toNat_mul]; simp; omega
  rw [h2a] at hlo
  have hat : a.toNat * T.toNat ≤ b.toNat * T.toNat := Nat.mul_le_mul_right _ (by omega)
  have hbt : b.toNat * T.toNat ≤ M.toNat * T.toNat := Nat.mul_le_mul_right _ hhi
  have hmt : M.toNat * T.toNat < 2 ^ 64 := by
    have : M.toNat * T.toNat ≤ 5 * M.toNat * T.toNat := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by decide)
    omega
  have e1 : (a * T).toNat = a.toNat * T.toNat := by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have e2 : (b * T).toNat = b.toNat * T.toNat := by rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have hdiv : 2 * (a.toNat * T.toNat / U.toNat) ≤ b.toNat * T.toNat / U.toNat := by
    refine Nat.le_trans (Nat.mul_div_le_mul_div_assoc _ _ _) (Nat.div_le_div_right ?_)
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  rw [BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_udiv, e1, e2]
  have h22 : (2 : BitVec 64).toNat = 2 := rfl
  rw [h22, Nat.mod_eq_of_lt (by have := Nat.le_trans hdiv (Nat.div_le_self _ _); omega)]
  exact hdiv

/-! ## The decode fact -/

/-- A configure invocation's budget is at least `MIN_BUDGET`. -/
def CfgDec : Fl4Invocation → Prop
  | .invokeSchedControl (.invokeSchedControlConfigureFlags _ b _ _ _ _) => MIN_BUDGET ≤ b
  | _ => True

theorem okv_decodeSchedControlFlags {w : UView} (label : Data) (args : List Data) (excaps : List Cap) :
    OkV w (fun i => CfgDec (.invokeSchedControl i))
      (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags
  refine okv_unlessE_bind fun _ => okv_whenE_bind fun _ => okv_whenE_bind fun _ => okv_returnOk_bind ?_
  refine okv_whenE_bind fun hb1 => okv_returnOk_bind ?_
  refine okv_whenE_bind fun _ => okv_whenE_bind fun hb2 => okv_whenE_bind fun _ => okv_whenE_bind fun _ => ?_
  refine okv_returnOk_bind (okv_whenE_bind fun _ => okv_returnOk_bind ?_)
  refine okv_bind (fun _ => ike_assertE _) (okv_triv fun _ => trivial) fun _ _ => okv_returnOk_bind ?_
  refine okv_whenE_bind fun _ => okv_returnOk_bind (okv_returnOk_bind (okv_returnOk ?_))
  exact minBudget_le_usToTicks (BitVec.not_lt.1 hb2) (BitVec.not_lt.1 hb1)

set_option maxHeartbeats 4000000 in
theorem okv_fl4DecodeCfg {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w CfgDec (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | schedControlCap =>
    unfold fl4DecodeInvocation
    exact okv_ite (okv_throw _) (okv_liftME (okv_decodeSchedControlFlags _ _ _))
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-! ## `refill_new` -/

theorem oth_of_mem_upd {p : ObjRef} {f : SchedContext → SchedContext} {s : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (updateSchedContext (Z := Unit) p f s).1) (h : Oth p s) :
    Oth p x.2 ∧ ∃ y n, x.2.kheap p = some (.schedContext (f y) n) := by
  obtain ⟨y, n, -, e⟩ := SInvB.mem_updateSchedContext hx
  rw [e]
  exact ⟨oth_updSc h (f y) n, y, n, by simp⟩

theorem rpos_of_oth {σ : State Unit} {p : ObjRef} (h : Oth p σ) {y : SchedContext} {n : Nat}
    (hy : σ.kheap p = some (.schedContext y n)) (hs : RPosS y) : RPos σ := by
  intro q z m hq
  by_cases e : q = p
  · subst e; rw [hy] at hq; cases hq; exact hs
  · exact h q z m e hq

theorem rposS_single {y : SchedContext} {r : Refill} (hr : y.scRefills = [r]) (hb : MIN_BUDGET ≤ r.rAmount) :
    RPosS y := by
  intro _ _
  have hm : (0 : Ticks) < MIN_BUDGET := MIN_BUDGET_pos'
  rw [BitVec.lt_def] at hm; rw [BitVec.le_def] at hb
  have hl := r.rAmount.isLt
  rw [hr]
  refine ⟨fun r' h => ?_, ?_, ?_⟩
  · simp only [List.mem_singleton] at h; subst h; omega
  · simp [SInvR.rsum]; omega
  · simp [SInvR.rsum]; omega

theorem rpos_refillNew (p : ObjRef) (mr : Nat) (b per : Ticks) (hb : MIN_BUDGET ≤ b) (σ : State Unit)
    (hσ : RPos σ) : ∀ r ∈ (refillNew (Z := Unit) p mr b per σ).1, RPos r.2 := by
  intro r hr
  unfold refillNew at hr
  rw [Notif.nd_gets_bind] at hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain ⟨o1, -⟩ := oth_of_mem_upd hz1 (oth_of_rpos hσ p)
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain ⟨o2, -⟩ := oth_of_mem_upd hz2 o1
  obtain ⟨z3, hz3, hr⟩ := hr
  obtain ⟨o3, -⟩ := oth_of_mem_upd hz3 o2
  dsimp only at hr
  rw [Notif.nd_pure_bind'] at hr
  obtain ⟨z4, hz4, hr⟩ := hr
  obtain ⟨o4, y4, n4, hy4⟩ := oth_of_mem_upd hz4 o3
  exact pz_maybeAddEmptyTail p z4.2 (rpos_of_oth o4 hy4 (rposS_single rfl hb)) r hr

end

end Fl4Proofs.P3.SInvE
