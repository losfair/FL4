/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd5): **`refill_budget_check`
for any charge, on the spec alone** (spec side only, outside the `JAtZ` cone;
KENTRY-PLAN rd2 handoff 2, rd4 handoff 2: `charge_budget`'s charge is the
insufficient one, so ScHead's `refillBudgetCheck_head` — a sufficient charge —
does not apply, and ScBudgetTop's `BudgetPost` is proved only through the FL4
relation).

The spec's refill steps are already computed on FL4 lists (`toRefill` images,
ScBudgetSpec / ScBudget: `chargeEntire_eq`, `postBody_eq`, `mergeNH_eq`); any
spec refill list is such an image (`ofR`). Only the amounts matter: their sum
`lsum` is fixed below `2 ^ 64`, so no merge wraps.

* `wl_inv2`: a `whileLoop` invariant on the loop value and state, with the
  exit condition.
* `LI σ p x n S s`: `s` is `σ` with the SC at `p` replaced by `x` with a
  non-empty refill list summing to `S`.
* `lsum_chargeL`, `lsum_mergeL`: the list steps keep the sum.
* `ho_out` (`handle_overrun`: `LI` kept, and at the exit the head is not
  overrun), `body_out` (the partial charge of the head after the loop),
  `hil_out` (`head_insufficient_loop`: `LI` kept, at the exit the head holds
  at least `MIN_BUDGET`, since the sum does and a single refill is the sum).
* **`rbc_out`**: every outcome of `refill_budget_check u` on the current SC
  (period ≠ 0, refills non-empty, summing below `2 ^ 64` and to at least
  `MIN_BUDGET`) is `σ` with only that SC's refill list replaced, non-empty,
  with the same sum and a head of at least `MIN_BUDGET` (l4v
  `refill_budget_check_valid_refills` / `refills_sum` preservation).
-/
import Fl4Proofs.P3.SpecInvRdB
open Classical
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

section
open Fl4Spec

/-- **A `whileLoop` invariant on the value and the state, with the exit condition.** -/
theorem wl_inv2 {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (P : α → State Unit → Prop)
    (hB : ∀ a s, P a s → C a s → ∀ y ∈ (B a s).1, P y.1 y.2) {a : α} {s : State Unit} (hs : P a s)
    {r : α × State Unit} (hr : r ∈ (NonDet.whileLoop C B a s).1) : P r.1 r.2 ∧ ¬ C r.1 r.2 := by
  have hw : NonDet.WhileResults C B a s r := hr
  clear hr
  revert hs
  induction hw with
  | done hc => exact fun hs => ⟨hs, hc⟩
  | step hc hm _ ih => exact fun hs => ih (hB _ _ hs hc _ hm)

/-- The SC at `p` is `x` with a non-empty refill list summing to `S`. -/
def LI (σ : State Unit) (p : ObjRef) (x : SchedContext) (n : Nat) (S : Nat) (s : State Unit) : Prop :=
  ∃ rs : List sporadic.Refill, s = updSc σ p { x with scRefills := rs.map toRefill } n ∧ rs ≠ [] ∧ lsum rs = S

theorem lsum_chargeL (m : Nat) (per : U64) {rs : List sporadic.Refill} (hne : rs ≠ []) (hs : lsum rs < 2 ^ 64) :
    lsum (chargeL m per rs) = lsum rs ∧ chargeL m per rs ≠ [] := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold chargeL
  by_cases h1 : (a :: l).length = 1
  · have hl : l = [] := by simpa using h1
    subst hl
    rw [if_pos h1]
    exact ⟨by simp [lsum], by simp⟩
  · rw [if_neg h1]
    have hl : l ≠ [] := by rintro rfl; exact h1 rfl
    have h2 := le_lsum (getLastD_mem hl)
    rw [lsum_cons] at hs
    have hno : (l.getLastD zR).amount.val + a.amount.val < 2 ^ 64 := by omega
    refine ⟨?_, schedUsedL_ne⟩
    have e := lsum_schedUsedL (m := m) (nw := ⟨core.num.U64.wrapping_add a.time per, a.amount⟩) hl hno
    rw [lsum_cons]
    exact e.trans (by show lsum l + a.amount.val = a.amount.val + lsum l; omega)

theorem lsum_mergeL {rs : List sporadic.Refill} (h2 : 2 ≤ rs.length) (hs : lsum rs < 2 ^ 64) :
    lsum (mergeL rs) = lsum rs := by
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, rs = a :: b :: l := by
    match rs, h2 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have e1 : lsum (a :: b :: l) = a.amount.val + (b.amount.val + lsum l) := by rw [lsum_cons, lsum_cons]
  rw [e1] at hs ⊢
  unfold mergeL
  rw [lsum_cons]
  show (core.num.U64.wrapping_add b.amount a.amount).val + lsum l = _
  rw [wadd_val' (by omega)]
  omega

/-! ## The overrun loop -/

theorem ho_step {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} {S : Nat} (hS : S < 2 ^ 64)
    {per : U64} (hper : x.scPeriod = per.bv) (a : Ticks) (s : State Unit) (hs : LI σ p x n S s) :
    ∀ y ∈ (chargeEntireHeadRefill (Z := Unit) p a s).1, LI σ p x n S y.2 := by
  obtain ⟨rs, rfl, hne, hsum⟩ := hs
  intro y hy
  rw [chargeEntire_eq (kh_upd σ p { x with scRefills := rs.map toRefill } n) (rs := rs) rfl hne hper,
    updSc_updSc] at hy
  obtain rfl := Set.mem_singleton_iff.1 hy
  obtain ⟨e1, e2⟩ := lsum_chargeL x.scRefillMax per hne (hsum ▸ hS)
  exact ⟨_, rfl, e2, e1.trans hsum⟩

/-- **`handle_overrun`**: the list invariant, and at the exit the head is not overrun. -/
theorem ho_out {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} {S : Nat} (hS : S < 2 ^ 64)
    {per : U64} (hper : x.scPeriod = per.bv) {u : Ticks} {s : State Unit} (hs : LI σ p x n S s)
    {r : Ticks × State Unit} (hr : r ∈ (handleOverrun (Z := Unit) p u s).1) :
    ∃ rs, r.2 = updSc σ p { x with scRefills := rs.map toRefill } n ∧ rs ≠ [] ∧ lsum rs = S ∧
      ¬ ((toRefill (rs.headD zR)).rAmount ≤ r.1 ∧ (toRefill (rs.headD zR)).rTime < MAX_RELEASE_TIME) := by
  unfold handleOverrun at hr
  obtain ⟨⟨rs, e, hne, hsum⟩, hC⟩ := wl_inv2 (fun _ s => LI σ p x n S s)
    (fun a s0 hs0 _ y hy => ho_step hS hper a s0 hs0 y hy) hs hr
  refine ⟨rs, e, hne, hsum, fun h => hC ?_⟩
  show Fl4Spec.the (headRefillOverrun (Z := Unit) p r.1 r.2) = true
  rw [e, headRefillOverrun_eq (kh_upd _ _ _ _) (by simpa using hne),
    refillHd_map (x := { x with scRefills := rs.map toRefill }) rfl hne, Sched.the_some]
  exact decide_eq_true h

/-! ## The partial charge after the loop -/

theorem body_out {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} {S : Nat} (hS : S < 2 ^ 64)
    {rs : List sporadic.Refill} (hne : rs ≠ []) (hsum : lsum rs = S) {u : U64}
    (hx : ¬ ((toRefill (rs.headD zR)).rAmount ≤ u.bv ∧ (toRefill (rs.headD zR)).rTime < MAX_RELEASE_TIME))
    {y : Unit × State Unit}
    (hy : y ∈ (NonDet.when (u.bv > 0 ∧ (toRefill (rs.headD zR)).rTime < MAX_RELEASE_TIME) (do
      let sc ← getSchedContext p
      let used ← pure { rTime := (toRefill (rs.headD zR)).rTime + sc.scPeriod, rAmount := u.bv : Refill }
      updateRefillHd p fun r => { r with rAmount := (toRefill (rs.headD zR)).rAmount - u.bv }
      updateRefillHd p fun r => { r with rTime := (toRefill (rs.headD zR)).rTime + u.bv }
      scheduleUsed (Z := Unit) p used) (updSc σ p { x with scRefills := rs.map toRefill } n)).1) :
    LI σ p x n S y.2 := by
  by_cases hc : u.bv > 0 ∧ (toRefill (rs.headD zR)).rTime < MAX_RELEASE_TIME
  · rw [NonDet.when, if_pos hc] at hy
    obtain ⟨q, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hk1 := kh_upd σ p { x with scRefills := (q :: l).map toRefill } n
    rw [postBody_eq hk1 (hd := q) (tl := l) rfl (per := ⟨x.scPeriod⟩) rfl (toRefill ((q :: l).headD zR)) rfl u,
      updSc_updSc] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    have hlt : u.bv.toNat < q.amount.val := by
      have h1 : ¬ (toRefill q).rAmount ≤ u.bv := fun h => hx ⟨h, hc.2⟩
      have h2 := BitVec.not_le.mp h1
      exact BitVec.lt_def.mp h2
    have hS' : lsum (q :: l) < 2 ^ 64 := hsum ▸ hS
    rw [lsum_cons] at hS' hsum
    have hi4 : (core.num.U64.wrapping_sub q.amount u).val = q.amount.val - u.bv.toNat :=
      wsub_val (show u.val ≤ q.amount.val from by show u.bv.toNat ≤ _; omega)
    have hno : ((⟨core.num.U64.wrapping_add q.time u, core.num.U64.wrapping_sub q.amount u⟩ :: l :
        List sporadic.Refill).getLastD zR).amount.val + u.val < 2 ^ 64 := by
      show _ + u.bv.toNat < _
      by_cases hl : l = []
      · subst hl; simp only [List.getLastD_cons, List.getLastD_nil]; rw [hi4]; omega
      · rw [getLastD_eq (by simp), List.getLast_cons hl]
        have := le_lsum (rs := l) (List.getLast_mem hl)
        omega
    refine ⟨_, rfl, schedUsedL_ne, ?_⟩
    rw [lsum_schedUsedL (by simp) hno, lsum_cons, ← hsum]
    show (core.num.U64.wrapping_sub q.amount u).val + lsum l + u.bv.toNat = _
    rw [hi4]; omega
  · rw [NonDet.when, if_neg hc] at hy
    obtain rfl : y = ((), _) := hy
    exact ⟨rs, rfl, hne, hsum⟩

/-! ## The insufficient-head loop -/

/-- **`head_insufficient_loop`**: the list invariant, and at the exit the head
holds at least `MIN_BUDGET`. -/
theorem hil_out {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} {S : Nat} (hS : S < 2 ^ 64)
    (hmin : MIN_BUDGET.toNat ≤ S) {s : State Unit} (hs : LI σ p x n S s) {r : Unit × State Unit}
    (hr : r ∈ (headInsufficientLoop (Z := Unit) p s).1) :
    ∃ rs, r.2 = updSc σ p { x with scRefills := rs.map toRefill } n ∧ rs ≠ [] ∧ lsum rs = S ∧
      MIN_BUDGET ≤ (toRefill (rs.headD zR)).rAmount := by
  unfold headInsufficientLoop at hr
  have hB : ∀ (a : Unit) s0, LI σ p x n S s0 →
      Fl4Spec.the (refillHeadInsufficient (Z := Unit) p s0) = true →
      ∀ y ∈ (mergeNonoverlappingHeadRefill (Z := Unit) p s0).1, LI σ p x n S y.2 := by
    intro a s0 hs0 hc y hy
    obtain ⟨rs, rfl, hne, hsum⟩ := hs0
    rw [refillHeadInsufficient_eq (kh_upd _ _ _ _) (by simpa using hne),
      refillHd_map (x := { x with scRefills := rs.map toRefill }) rfl hne, Sched.the_some] at hc
    have hlt := of_decide_eq_true hc
    have h2 : 2 ≤ rs.length := by
      obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      rcases l with _ | ⟨b, l⟩
      · exfalso
        have e1 : a.amount.val = S := by rw [← hsum, lsum_single]
        have e2 : (toRefill a).rAmount.toNat < MIN_BUDGET.toNat := BitVec.lt_def.mp hlt
        have e3 : (toRefill a).rAmount.toNat = a.amount.val := rfl
        omega
      · simp
    rw [mergeNH_eq (kh_upd σ p { x with scRefills := rs.map toRefill } n) (rs := rs) rfl h2, updSc_updSc] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨mergeL rs, rfl, by simp [mergeL], (lsum_mergeL h2 (hsum ▸ hS)).trans hsum⟩
  obtain ⟨⟨rs, e, hne, hsum⟩, hC⟩ :=
    wl_inv2 (C := fun _ s => Fl4Spec.the (refillHeadInsufficient (Z := Unit) p s) = true)
      (fun _ s => LI σ p x n S s) hB hs hr
  refine ⟨rs, e, hne, hsum, ?_⟩
  have hC' : ¬ Fl4Spec.the (refillHeadInsufficient (Z := Unit) p r.2) = true := hC
  rw [e, refillHeadInsufficient_eq (kh_upd _ _ _ _) (by simpa using hne),
    refillHd_map (x := { x with scRefills := rs.map toRefill }) rfl hne, Sched.the_some] at hC'
  exact BitVec.not_lt.mp fun h => hC' (decide_eq_true h)

/-! ## `refill_budget_check` -/

/-- **`refill_budget_check` for any charge** (module docstring). -/
theorem rbc_out {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat} (hcur : σ.curSc = p)
    (hk : σ.kheap p = some (.schedContext x n)) (hp0 : x.scPeriod ≠ 0) (hne : x.scRefills ≠ [])
    (hsum : rsum x.scRefills < 2 ^ 64) (hmin : MIN_BUDGET.toNat ≤ rsum x.scRefills) (u : Ticks)
    {r : Unit × State Unit} (hr : r ∈ (refillBudgetCheck (Z := Unit) u σ).1) :
    ∃ zs, r.2 = updSc σ p { x with scRefills := zs } n ∧ zs ≠ [] ∧ rsum zs = rsum x.scRefills ∧
      MIN_BUDGET ≤ (refillHd { x with scRefills := zs }).rAmount := by
  obtain ⟨rs0, hx0⟩ : ∃ rs0 : List sporadic.Refill, x.scRefills = rs0.map toRefill := ⟨_, (map_ofR _).symm⟩
  have hS : lsum rs0 = rsum x.scRefills := by rw [hx0, rsum_map]
  have hne0 : rs0 ≠ [] := by rintro rfl; exact hne (by rw [hx0]; rfl)
  have hs0 : LI σ p x n (rsum x.scRefills) σ := ⟨rs0, by rw [← hx0]; exact (updSc_self hk).symm, hne0, hS⟩
  rw [refillBudgetCheck_eq hcur hk hp0 u] at hr
  obtain ⟨y1, h1, hr⟩ := hr
  dsimp only at hr
  obtain ⟨rs1, e1, hne1, hs1, hx1⟩ := ho_out hsum (per := ⟨x.scPeriod⟩) rfl hs0 h1
  rw [e1] at hr
  unfold Sched.specTail at hr
  rw [nd_bind_one (getRefillHead_eq (kh_upd σ p { x with scRefills := rs1.map toRefill } n) (by simpa using hne1)),
    refillHd_map (x := { x with scRefills := rs1.map toRefill }) rfl hne1] at hr
  obtain ⟨y2, h2, hr⟩ := hr
  have hL2 := body_out hsum hne1 hs1 (u := ⟨y1.1⟩) hx1 h2
  obtain ⟨rs, e, hne', hs', hm⟩ := hil_out hsum hmin hL2 hr
  refine ⟨rs.map toRefill, e, by simpa using hne', by rw [rsum_map, hs'], ?_⟩
  rw [refillHd_map (x := { x with scRefills := rs.map toRefill }) rfl hne']
  exact hm

/-! ## `Rdy` across the sporadic charge -/

/-- **`Rdy` across the sporadic charge of the current SC** (any usage): the
current SC active, not the idle SC, `Excl` (no thread bound to it is queued,
the switch target or `BlkR`: at the entry only the current thread is bound to
it, l4v `ct_not_in_q` / `simple_sched_action`), its refills non-empty (sb2's
`RNE`), period ≠ 0 (not round robin, which `refill_budget_check` asserts). -/
theorem rd_refillBudgetCheck {σ : State Unit} {x : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (hI : σ.curSc ≠ σ.idleSc) (hX : Excl σ σ.curSc)
    (hp0 : x.scPeriod ≠ 0) (hne : x.scRefills ≠ []) (ha : scActive x = true) (u : Ticks)
    {r : Unit × State Unit} (hr : r ∈ (refillBudgetCheck (Z := Unit) u σ).1) :
    Rdy r.2 ∧ ∃ zs, r.2 = updSc σ σ.curSc { x with scRefills := zs } n ∧ zs ≠ [] := by
  obtain ⟨v1, v2, v3, -⟩ := h.2.2.2.1 _ x n hk ha
  have hmin : MIN_BUDGET.toNat ≤ rsum x.scRefills := by
    obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne
    have e2 : (refillHd x).rAmount = a.rAmount := by unfold refillHd; rw [e]; rfl
    rw [e2, BitVec.le_def] at v2
    rw [e, rsum_cons]; omega
  obtain ⟨zs, e, hz, hs, hm⟩ := rbc_out rfl hk hp0 hne v3 hmin u hr
  refine ⟨?_, zs, e, hz⟩
  rw [e]
  have hkq : ∀ q, q ≠ σ.curSc → (updSc σ σ.curSc { x with scRefills := zs } n).kheap q = σ.kheap q :=
    fun q hq => by simp [Notif.updK, hq]
  have hkp := kh_upd σ σ.curSc { x with scRefills := zs } n
  refine rdy_framex h hkq rfl rfl rfl hX (fun x0 hx0 => by rw [hk] at hx0; cases hx0)
    (fun x0 hx0 => by rw [hkp] at hx0; cases hx0) (fun z m hz _ => ?_) rfl
    (fun y0 n0 hy0 ha0 => ⟨_, n, hkp, by rw [hk] at hy0; cases hy0; exact ha0⟩) rfl (fun e => absurd e hI)
  rw [hkp] at hz; cases hz
  exact ⟨v1, hm, by rw [hs]; exact v3, fun h0 => absurd h0 hp0⟩

end

end

end Fl4Proofs.P3.SInvR
