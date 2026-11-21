/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq1): **the refill
writers keep `RPos`** (spec side only, outside the `JAtZ` cone).

Each refill writer rewrites the refill list of one SC `p` and keeps its size,
period and refill max. `AtK p n per mx k σ`: `RPos` holds for every other SC,
and the SC at `p` (size `n`, period `per`, refill max `mx`) has, when active
and sporadic, refills `LK l k`: positive amounts with `rsum l + k` in
`[MIN_BUDGET, 2 ^ 64)`. `k` is the amount in transit (popped and not yet
re-added). Each primitive (`update_refill_hd` / `_tl`, `refill_add_tail`,
`refill_pop_head`) is one `updSc` step; the loops keep `AtK … 0`.

* `ak_scheduleUsed`: from `AtK … k` with `k` the new refill's (positive) amount
  to `AtK … 0` (merge into the tail, append, or the full case).
-/
import Fl4Proofs.P3.SpecInvEqK
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR

noncomputable section

set_option maxHeartbeats 1000000

/-! ## List arithmetic -/

/-- Positive amounts. -/
def AP (l : List Refill) : Prop := ∀ r ∈ l, 0 < r.rAmount.toNat

/-- The refill facts with `k` in transit. -/
def LK (l : List Refill) (k : Nat) : Prop :=
  AP l ∧ rsum l + k < 2 ^ 64 ∧ MIN_BUDGET.toNat ≤ rsum l + k

theorem rsum_cons (h : Refill) (t : List Refill) : rsum (h :: t) = h.rAmount.toNat + rsum t := by
  simp [rsum]

theorem rsum_snoc (l : List Refill) (r : Refill) : rsum (l ++ [r]) = rsum l + r.rAmount.toNat := by
  simp [rsum]

theorem rsum_nil : rsum [] = 0 := rfl

theorem le_rsum {l : List Refill} {r : Refill} (h : r ∈ l) : r.rAmount.toNat ≤ rsum l := by
  unfold rsum
  exact List.le_sum_of_mem (List.mem_map.2 ⟨r, h, rfl⟩)

theorem ap_cons {h : Refill} {t : List Refill} : AP (h :: t) ↔ 0 < h.rAmount.toNat ∧ AP t := by
  simp [AP]

theorem ap_snoc {l : List Refill} {r : Refill} : AP (l ++ [r]) ↔ AP l ∧ 0 < r.rAmount.toNat := by
  simp [AP, or_imp, forall_and]

theorem ap_dropLast {l : List Refill} (h : AP l) : AP l.dropLast :=
  fun r hr => h r (List.dropLast_subset _ hr)

theorem split_last {l : List Refill} (hne : l ≠ []) :
    l = l.dropLast ++ [l.getLast hne] ∧ l.getLast? = some (l.getLast hne) :=
  ⟨(List.dropLast_append_getLast hne).symm, List.getLast?_eq_getLast hne⟩

theorem add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have := a.isLt
  have := b.isLt
  rw [show 2 ^ 64 - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-! ## The state predicate -/

/-- `RPos` at every SC but `p`. -/
def Oth (p : ObjRef) (σ : State Unit) : Prop :=
  ∀ q y n, q ≠ p → σ.kheap q = some (.schedContext y n) → RPosS y

/-- The guard: active (`MIN_REFILLS`-style refill max `mx > 0`) and sporadic. -/
def G (per : Time) (mx : Nat) : Prop := activeSc mx = true ∧ per ≠ 0

/-- The SC at `p` keeps size, period and refill max; when active and sporadic
its refills hold `LK … k`; `RPos` elsewhere. -/
def AtK (p : ObjRef) (n : Nat) (per : Time) (mx : Nat) (k : Nat) (σ : State Unit) : Prop :=
  Oth p σ ∧ ∃ y, σ.kheap p = some (.schedContext y n) ∧ y.scPeriod = per ∧ y.scRefillMax = mx ∧
    (G per mx → LK y.scRefills k)

theorem oth_of_rpos {σ : State Unit} (h : RPos σ) (p : ObjRef) : Oth p σ :=
  fun q y n _ hq => h q y n hq

theorem atK_of_rpos {σ : State Unit} (h : RPos σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hy : σ.kheap p = some (.schedContext y n)) : AtK p n y.scPeriod y.scRefillMax 0 σ := by
  refine ⟨oth_of_rpos h p, y, hy, rfl, rfl, fun hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h p y n hy hg.1 hg.2
  exact ⟨h1, by simpa using h2, by simpa using h3⟩

theorem rpos_of_atK {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat} (h : AtK p n per mx 0 σ) :
    RPos σ := by
  obtain ⟨ho, y, hy, hp, hm, hL⟩ := h
  intro q z m hq
  by_cases e : q = p
  · subst e
    rw [hy] at hq; cases hq
    intro ha hpe
    obtain ⟨h1, h2, h3⟩ := hL ⟨by rw [← hm]; exact ha, by rw [← hp]; exact hpe⟩
    exact ⟨h1, by simpa using h2, by simpa using h3⟩
  · exact ho q z m e hq

theorem oth_updSc {σ : State Unit} {p : ObjRef} (h : Oth p σ) (x : SchedContext) (n : Nat) :
    Oth p (Sched.updSc σ p x n) := by
  intro q y m hq hk
  simp only [Sched.updSc, Notif.updK_kheap, Function.update_of_ne hq] at hk
  exact h q y m hq hk

theorem oth_kheap {σ σ' : State Unit} {p : ObjRef} (h : Oth p σ) (hk : σ'.kheap = σ.kheap) : Oth p σ' := by
  intro q y m hq hy; rw [hk] at hy; exact h q y m hq hy

theorem atK_kheap {σ σ' : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx k : Nat} (h : AtK p n per mx k σ)
    (hk : σ'.kheap = σ.kheap) : AtK p n per mx k σ' := by
  obtain ⟨ho, y, hy, e⟩ := h
  exact ⟨oth_kheap ho hk, y, by rw [hk]; exact hy, e⟩

theorem updSc_kheap_self (σ : State Unit) (p : ObjRef) (x : SchedContext) (n : Nat) :
    (Sched.updSc σ p x n).kheap p = some (.schedContext x n) := by
  simp [Sched.updSc]

/-- **The step**: a new refill list at `p`. -/
theorem atK_upd {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx k : Nat} (h : AtK p n per mx k σ)
    {y : SchedContext} (hy : σ.kheap p = some (.schedContext y n)) (l : List Refill) (k' : Nat)
    (hL : G per mx → LK y.scRefills k → LK l k') :
    AtK p n per mx k' (Sched.updSc σ p { y with scRefills := l } n) := by
  obtain ⟨ho, y0, hy0, hp, hm, hL0⟩ := h
  rw [hy] at hy0; cases hy0
  exact ⟨oth_updSc ho _ _, { y with scRefills := l }, updSc_kheap_self _ _ _ _, hp, hm, fun hg => hL hg (hL0 hg)⟩

theorem atK_sc {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx k : Nat} (h : AtK p n per mx k σ) :
    ∃ y, σ.kheap p = some (.schedContext y n) ∧ y.scPeriod = per ∧ y.scRefillMax = mx ∧
      (G per mx → LK y.scRefills k) := h.2

/-! ## Reads -/

theorem getRefills_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    getRefills (Z := Unit) p σ = ({(x.scRefills, σ)}, False) := by
  unfold getRefills
  rw [Notif.nd_bind_one (Sched.getSchedContext_eq hk)]; rfl

theorem readRefillTail_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    readRefillTail (Z := Unit) p σ = some (refillTl x) := by
  show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
    (fun _ => Lookup.oreturn (refillTl sc) σ)) = _
  rw [Sched.readSchedContext_eq hk]
  simp [Lookup.oassert, hne, Lookup.oreturn]

theorem getRefillTail_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    getRefillTail (Z := Unit) p σ = ({(refillTl x, σ)}, False) := by
  simp [getRefillTail, NonDet.getsThe, readRefillTail_eq hk hne, NonDet.assertOpt]; rfl

theorem refillFull_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    refillFull (Z := Unit) p σ = ({(decide (x.scRefills.length = x.scRefillMax), σ)}, False) := by
  unfold refillFull
  rw [Notif.nd_bind_one (Sched.getSchedContext_eq hk)]; rfl

theorem updateRefillTl_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (f : Refill → Refill) :
    updateRefillTl (Z := Unit) p f σ =
      ({((), Sched.updSc σ p { x with scRefills := x.scRefills.dropLast ++ [f (the x.scRefills.getLast?)] } n)},
        False) :=
  Sched.updateSchedContext_eq hk _

theorem refillAddTail_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (r : Refill) :
    refillAddTail (Z := Unit) p r σ =
      ({((), Sched.updSc σ p { x with scRefills := x.scRefills ++ [r] } n)}, False) :=
  Sched.updateSchedContext_eq hk _

theorem mem_one {α : Type} {S : Set (α × State Unit) × Prop} {a : α} {s : State Unit} {y : α × State Unit}
    (e : S = ({(a, s)}, False)) (h : y ∈ S.1) : y = (a, s) := by
  rw [e] at h; exact h

/-! ## `schedule_used` -/

theorem lk_tl {l : List Refill} (hne : l ≠ []) {k k' : Nat} (hL : LK l k) (x : Refill)
    (hx : x.rAmount.toNat + k' = (l.getLast hne).rAmount.toNat + k) (hp : 0 < x.rAmount.toNat) :
    LK (l.dropLast ++ [x]) k' := by
  obtain ⟨e, -⟩ := split_last hne
  obtain ⟨h1, h2, h3⟩ := hL
  have hs : rsum l = rsum l.dropLast + (l.getLast hne).rAmount.toNat := by
    conv_lhs => rw [e]
    exact rsum_snoc _ _
  refine ⟨ap_snoc.2 ⟨ap_dropLast h1, hp⟩, ?_, ?_⟩ <;> rw [rsum_snoc] <;> omega

theorem getLast_snoc' (l : List Refill) (x : Refill) (h : l ++ [x] ≠ []) : (l ++ [x]).getLast h = x := by
  simp

theorem ak_scheduleUsed {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx k : Nat}
    (h : AtK p n per mx k σ) (new : Refill) (hk : k = new.rAmount.toNat) (hpos : G per mx → 0 < new.rAmount.toNat) :
    ∀ r ∈ (scheduleUsed (Z := Unit) p new σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  obtain ⟨y, hy, -, -, -⟩ := atK_sc h
  unfold scheduleUsed at hr
  rw [Notif.nd_bind_one (getRefills_eq hy)] at hr
  obtain ⟨z, ⟨hne, rfl⟩, hr⟩ := hr
  dsimp only at hr
  rw [Notif.nd_bind_one (getRefillTail_eq hy hne)] at hr
  obtain ⟨-, hlast⟩ := split_last hne
  have hth : the y.scRefills.getLast? = y.scRefills.getLast hne := by rw [hlast]; rfl
  have htl : refillTl y = y.scRefills.getLast hne := hth
  have hlm := List.getLast_mem hne
  split at hr
  · rw [updateRefillTl_eq hy] at hr
    obtain rfl := mem_one rfl hr
    refine atK_upd h hy _ 0 fun _ hL => ?_
    have hle := le_rsum hlm
    have hp0 := hL.1 _ hlm
    have hadd : ((refillTl y).rAmount + new.rAmount).toNat =
        (y.scRefills.getLast hne).rAmount.toNat + new.rAmount.toNat := by
      rw [htl]; exact add_toNat (by have := hL.2.1; omega)
    refine lk_tl hne hL _ ?_ ?_ <;> dsimp only <;> rw [hadd] <;> omega
  · rw [Notif.nd_bind_one (refillFull_eq hy)] at hr
    split at hr
    · rw [refillAddTail_eq hy] at hr
      obtain rfl := mem_one rfl hr
      refine atK_upd h hy _ 0 fun hg hL => ?_
      obtain ⟨h1, h2, h3⟩ := hL
      refine ⟨ap_snoc.2 ⟨h1, hpos hg⟩, ?_, ?_⟩ <;> rw [rsum_snoc] <;> omega
    · rw [Notif.nd_bind_one (updateRefillTl_eq hy _)] at hr
      rw [updateRefillTl_eq (updSc_kheap_self _ _ _ _)] at hr
      obtain rfl := mem_one rfl hr
      have h1 := atK_upd h hy (y.scRefills.dropLast ++
        [{ the y.scRefills.getLast? with rTime := new.rTime - (refillTl y).rAmount }]) k fun _ hL =>
          lk_tl hne hL _ (by dsimp only; rw [hth]) (by dsimp only; rw [hth]; exact hL.1 _ hlm)
      refine atK_upd h1 (updSc_kheap_self _ _ _ _) _ 0 fun _ hL => ?_
      have hne1 : y.scRefills.dropLast ++
          [{ the y.scRefills.getLast? with rTime := new.rTime - (refillTl y).rAmount }] ≠ [] := by simp
      have hle := le_rsum hlm
      have hadd : ((refillTl y).rAmount + new.rAmount).toNat =
          (y.scRefills.getLast hne).rAmount.toNat + new.rAmount.toNat := by
        rw [htl]
        refine add_toNat ?_
        obtain ⟨-, a2, -⟩ := hL
        rw [rsum_snoc] at a2
        have : (({ the y.scRefills.getLast? with rTime := new.rTime - (refillTl y).rAmount } : Refill)).rAmount =
          (y.scRefills.getLast hne).rAmount := by dsimp only; rw [hth]
        rw [this] at a2
        omega
      refine lk_tl hne1 hL _ ?_ ?_
      · dsimp only; rw [hadd, getLast_snoc']; dsimp only; rw [hth]; omega
      · dsimp only; rw [hadd]
        have := hL.1 _ (List.mem_append_right _ (List.mem_singleton_self _))
        dsimp only at this; rw [hth] at this; omega

/-! ## More reads -/

theorem eq_readRefillHead_nil {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (he : x.scRefills = []) :
    readRefillHead (Z := Unit) p σ = none := by
  show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
    (fun _ => Lookup.oreturn (refillHd sc) σ)) = _
  rw [Sched.readSchedContext_eq hk]
  simp [Lookup.oassert, he, Lookup.ofail]

theorem mem_getRefillHead {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {z : Refill × State Unit}
    (h : z ∈ (getRefillHead (Z := Unit) p σ).1) : x.scRefills ≠ [] ∧ z = (refillHd x, σ) := by
  by_cases he : x.scRefills = []
  · exfalso
    simp only [getRefillHead, NonDet.getsThe, eq_readRefillHead_nil hk he, NonDet.assertOpt, NonDet.fail] at h
    exact h
  · exact ⟨he, mem_one (Sched.getRefillHead_eq hk he) h⟩

theorem eq_readRefillTail_nil {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (he : x.scRefills = []) :
    readRefillTail (Z := Unit) p σ = none := by
  show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
    (fun _ => Lookup.oreturn (refillTl sc) σ)) = _
  rw [Sched.readSchedContext_eq hk]
  simp [Lookup.oassert, he, Lookup.ofail]

theorem mem_getRefillTail {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {z : Refill × State Unit}
    (h : z ∈ (getRefillTail (Z := Unit) p σ).1) : x.scRefills ≠ [] ∧ z = (refillTl x, σ) := by
  by_cases he : x.scRefills = []
  · exfalso
    simp only [getRefillTail, NonDet.getsThe, eq_readRefillTail_nil hk he, NonDet.assertOpt, NonDet.fail] at h
    exact h
  · exact ⟨he, mem_one (getRefillTail_eq hk he) h⟩

theorem mem_getSchedContext {σ : State Unit} {p : ObjRef} {z : SchedContext × State Unit}
    (h : z ∈ (getSchedContext (Z := Unit) p σ).1) : ∃ n, σ.kheap p = some (.schedContext z.1 n) ∧ z.2 = σ := by
  unfold getSchedContext at h
  obtain ⟨y, hy, h⟩ := h
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨o, y2⟩ := y
  simp only at hk hs; subst hs
  cases o with
  | schedContext sc m =>
    have e : z = (sc, y2) := Set.mem_singleton_iff.1 h
    subst e; exact ⟨m, hk, rfl⟩
  | _ => exact h.elim

theorem mem_isRoundRobin {σ : State Unit} {p : ObjRef} {z : Bool × State Unit}
    (h : z ∈ (isRoundRobin (Z := Unit) p σ).1) :
    ∃ x n, σ.kheap p = some (.schedContext x n) ∧ z = (decide (x.scPeriod = 0), σ) := by
  unfold isRoundRobin at h
  obtain ⟨y, hy, h⟩ := h
  obtain ⟨n, hk, hs⟩ := mem_getSchedContext hy
  have e : z = (decide (y.1.scPeriod = 0), y.2) := Set.mem_singleton_iff.1 h
  rw [hs] at e
  exact ⟨y.1, n, hk, e⟩

theorem refillSingle_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    refillSingle (Z := Unit) p σ = ({(decide (x.scRefills.length = 1), σ)}, False) := by
  unfold refillSingle refillSize
  have e : (getRefills (Z := Unit) p >>= fun refills => (pure refills.length : NonDet (State Unit) Nat)) σ =
      ({(x.scRefills.length, σ)}, False) := by
    rw [Notif.nd_bind_one (getRefills_eq hk)]; rfl
  rw [Notif.nd_bind_one e]; rfl

/-! ## List steps at the head -/

theorem lk_hd {hd : Refill} {tl : List Refill} {k k' : Nat} (hL : LK (hd :: tl) k) (x : Refill)
    (hx : x.rAmount.toNat + k' = hd.rAmount.toNat + k) (hp : 0 < x.rAmount.toNat) : LK (x :: tl) k' := by
  obtain ⟨h1, h2, h3⟩ := hL
  rw [ap_cons] at h1
  refine ⟨ap_cons.2 ⟨hp, h1.2⟩, ?_, ?_⟩ <;> rw [rsum_cons] at h2 h3 ⊢ <;> omega

theorem the_cons (a : Refill) (l : List Refill) : the (a :: l).head? = a := rfl

/-- An update of the head keeping its amount. -/
theorem lk_hd_keep {l : List Refill} (hne : l ≠ []) {k : Nat} (hL : LK l k) (f : Refill → Refill)
    (hf : ∀ r, (f r).rAmount = r.rAmount) : LK (f (the l.head?) :: l.tail) k := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine lk_hd hL _ (by rw [hf]; rfl) ?_
  rw [hf]; exact (ap_cons.1 hL.1).1

/-! ## `refill_pop_head`, `charge_entire_head_refill`, `handle_overrun` -/

theorem ak_pop {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat} (h : AtK p n per mx 0 σ)
    {y : SchedContext} (hy : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    AtK p n per mx (refillHd y).rAmount.toNat (Sched.updSc σ p { y with scRefills := y.scRefills.tail } n) := by
  refine atK_upd h hy _ _ fun _ hL => ?_
  obtain ⟨hd, tl, e⟩ := List.exists_cons_of_ne_nil hne
  have eh : refillHd y = hd := by show the y.scRefills.head? = hd; rw [e]; rfl
  rw [e] at hL ⊢; rw [eh]
  simp only [List.tail_cons]
  obtain ⟨h1, h2, h3⟩ := hL
  rw [ap_cons] at h1; rw [rsum_cons] at h2 h3
  exact ⟨h1.2, by omega, by omega⟩

theorem ak_chargeEntireHeadRefill {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) (u : Ticks) :
    ∀ r ∈ (chargeEntireHeadRefill (Z := Unit) p u σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  obtain ⟨y, hy, -, -, -⟩ := atK_sc h
  unfold chargeEntireHeadRefill at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨hne, rfl⟩ := mem_getRefillHead hy hz
  dsimp only at hr
  rw [Notif.nd_bind_one (Sched.getSchedContext_eq hy), Notif.nd_bind_one (refillSingle_eq hy)] at hr
  split at hr
  · rw [Notif.nd_bind_one (Sched.updateRefillHd_eq hy _)] at hr
    obtain rfl := Set.mem_singleton_iff.1 hr
    exact atK_upd h hy _ 0 fun _ hL =>
      lk_hd_keep hne hL (fun r => { r with rTime := (refillHd y).rTime + y.scPeriod }) fun _ => rfl
  · rw [Notif.nd_bind_one (Sched.refillPopHead_eq hy hne)] at hr
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hr
    have hpos : G per mx → 0 < (refillHd y).rAmount.toNat := fun hg => by
      obtain ⟨y', hy', -, -, hL'⟩ := atK_sc h
      rw [hy] at hy'; cases hy'
      obtain ⟨hd0, tl, e⟩ := List.exists_cons_of_ne_nil hne
      have hd := (hL' hg).1
      have eh : refillHd y = hd0 := by show the y.scRefills.head? = hd0; rw [e]; rfl
      rw [e] at hd; rw [eh]; exact (ap_cons.1 hd).1
    exact ak_scheduleUsed (ak_pop h hy hne)
      { rTime := (refillHd y).rTime + y.scPeriod, rAmount := (refillHd y).rAmount } rfl hpos z hz

/-- A `whileLoop` outcome satisfies the invariant and fails the guard. -/
theorem wl_exit {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α} (P : State Unit → Prop)
    (hB : ∀ a s, P s → C a s → ∀ y ∈ (B a s).1, P y.2) {a : α} {s : State Unit} (hs : P s)
    {r : α × State Unit} (hr : r ∈ (NonDet.whileLoop C B a s).1) : P r.2 ∧ ¬ C r.1 r.2 := by
  have hw : NonDet.WhileResults C B a s r := hr
  clear hr
  revert hs
  induction hw with
  | done hc => exact fun hs => ⟨hs, hc⟩
  | step hc hm _ ih => exact fun hs => ih (hB _ _ hs hc _ hm)

theorem ak_handleOverrun {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) (u : Ticks) : ∀ r ∈ (handleOverrun (Z := Unit) p u σ).1,
      AtK p n per mx 0 r.2 ∧ ¬ (the (headRefillOverrun (Z := Unit) p r.1 r.2) = true) := by
  intro r hr
  unfold handleOverrun at hr
  exact wl_exit (AtK p n per mx 0) (fun a s hs _ y hy => ak_chargeEntireHeadRefill hs a y hy) h hr

/-! ## `head_insufficient_loop` -/

theorem ak_mergeNonoverlapping {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) (hc : the (refillHeadInsufficient (Z := Unit) p σ) = true) :
    ∀ r ∈ (mergeNonoverlappingHeadRefill (Z := Unit) p σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  obtain ⟨y, hy, -, -, -⟩ := atK_sc h
  unfold mergeNonoverlappingHeadRefill at hr
  obtain ⟨z, hz, hr⟩ := hr
  have hne : y.scRefills ≠ [] := by
    intro he
    unfold refillPopHead at hz
    obtain ⟨w, hw, -⟩ := hz
    exact (mem_getRefillHead hy hw).1 he
  rw [Sched.refillPopHead_eq hy hne] at hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  dsimp only at hr
  have h1 := ak_pop h hy hne
  obtain ⟨hd, tl, e⟩ := List.exists_cons_of_ne_nil hne
  have eh : refillHd y = hd := by show the y.scRefills.head? = hd; rw [e]; rfl
  have et : y.scRefills.tail = tl := by rw [e]; rfl
  rw [Notif.nd_bind_one (Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _) _)] at hr
  rw [Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _)] at hr
  obtain rfl := mem_one rfl hr
  have h2 := atK_upd h1 (updSc_kheap_self _ _ _ _)
    ((fun head => { head with rAmount := head.rAmount + (refillHd y).rAmount })
      (the y.scRefills.tail.head?) :: y.scRefills.tail.tail) 0 fun hg hL => by
    obtain ⟨y0, hy0, -, -, hL0⟩ := atK_sc h
    rw [hy] at hy0; cases hy0
    have hL0 := hL0 hg
    rw [et] at hL ⊢; rw [eh] at hL ⊢
    cases tl with
    | nil =>
      exfalso
      rw [Sched.refillHeadInsufficient_eq hy hne] at hc
      simp only [the, decide_eq_true_eq, eh] at hc
      rw [e] at hL0
      have h3 := hL0.2.2
      rw [rsum_cons, rsum_nil] at h3
      rw [BitVec.lt_def] at hc
      omega
    | cons h2 t2 =>
      have hs := hL0.2.1
      rw [e, rsum_cons, rsum_cons] at hs
      have hp2 := (ap_cons.1 hL.1).1
      refine lk_hd (tl := t2) (hd := h2) (k := hd.rAmount.toNat) hL _ ?_ ?_ <;> dsimp only <;>
        rw [the_cons, add_toNat (by omega)] <;> omega
  exact atK_upd h2 (updSc_kheap_self _ _ _ _) _ 0 fun _ hL =>
    lk_hd_keep (List.cons_ne_nil _ _) hL (fun head => { head with rTime := head.rTime - (refillHd y).rAmount })
      fun _ => rfl

theorem ak_headInsufficientLoop {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) : ∀ r ∈ (headInsufficientLoop (Z := Unit) p σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  unfold headInsufficientLoop at hr
  exact (wl_exit (AtK p n per mx 0) (fun a s hs hc y hy => ak_mergeNonoverlapping hs hc y hy) h hr).1

/-! ## `refill_budget_check` -/

/-- `refill_budget_check` on the current SC: its size, period (non-zero) and
refill max kept, its refills `LK … 0`. -/
theorem ak_refillBudgetCheck (u : Ticks) (σ : State Unit) (hσ : RPos σ) :
    ∀ r ∈ (refillBudgetCheck (Z := Unit) u σ).1, ∃ y n, σ.kheap σ.curSc = some (.schedContext y n) ∧
      y.scPeriod ≠ 0 ∧ AtK σ.curSc n y.scPeriod y.scRefillMax 0 r.2 := by
  intro r hr
  unfold refillBudgetCheck at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz
  dsimp only at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨y, n, hy, rfl⟩ := mem_isRoundRobin hz
  dsimp only at hr
  obtain ⟨z, ⟨hrob, rfl⟩, hr⟩ := hr
  dsimp only at hr
  have h0 := atK_of_rpos hσ hy
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨h1, hx⟩ := ak_handleOverrun h0 u z hz
  obtain ⟨y1, hy1, -, -, -⟩ := atK_sc h1
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨hne1, rfl⟩ := mem_getRefillHead hy1 hw
  dsimp only at hr
  obtain ⟨w, hw, hr⟩ := hr
  refine ⟨y, n, hy, by simpa using hrob, ak_headInsufficientLoop ?_ r hr⟩
  unfold NonDet.when at hw
  split at hw
  · rename_i hc
    obtain ⟨hu0, hmax⟩ := hc
    have hlt : z.1 < (refillHd y1).rAmount := by
      rw [Sched.headRefillOverrun_eq hy1 hne1] at hx
      simp only [the, decide_eq_true_eq, not_and] at hx
      exact BitVec.not_le.1 fun hle => hx hle hmax
    rw [BitVec.lt_def] at hlt
    rw [Notif.nd_bind_one (Sched.getSchedContext_eq hy1)] at hw
    rw [Notif.nd_pure_bind'] at hw
    rw [Notif.nd_bind_one (Sched.updateRefillHd_eq hy1 _)] at hw
    rw [Notif.nd_bind_one (Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _) _)] at hw
    obtain ⟨hd, tl, e⟩ := List.exists_cons_of_ne_nil hne1
    have eh : refillHd y1 = hd := by show the y1.scRefills.head? = hd; rw [e]; rfl
    have h2 := atK_upd h1 hy1
      ((fun r => { r with rAmount := (refillHd y1).rAmount - z.1 }) (the y1.scRefills.head?) :: y1.scRefills.tail)
      z.1.toNat fun _ hL => by
        rw [e] at hL ⊢
        refine lk_hd hL _ ?_ ?_ <;> dsimp only <;> rw [eh] at hlt ⊢ <;> rw [sub_toNat (by omega)] <;> omega
    refine ak_scheduleUsed (atK_upd h2 (updSc_kheap_self _ _ _ _) _ z.1.toNat fun _ hL =>
      lk_hd_keep (List.cons_ne_nil _ _) hL (fun r => { r with rTime := (refillHd y1).rTime + z.1 }) fun _ => rfl)
      _ rfl (fun _ => ?_) w hw
    exact BitVec.lt_def.1 hu0
  · obtain rfl := Set.mem_singleton_iff.1 hw
    exact h1

theorem pz_refillBudgetCheck (u : Ticks) : PZK (refillBudgetCheck (Z := Unit) u) := by
  intro σ hσ r hr
  obtain ⟨y, n, -, -, h⟩ := ak_refillBudgetCheck u σ hσ r hr
  exact rpos_of_atK h

/-! ## `refill_unblock_check` -/

theorem mem_getScRefillReady {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {z : Bool × State Unit}
    (h : z ∈ (getScRefillReady (Z := Unit) p σ).1) : x.scRefills ≠ [] ∧ z.2 = σ := by
  by_cases he : x.scRefills = []
  · exfalso
    have hn : readScRefillReady (Z := Unit) p σ = none := by
      show Option.bind (readRefillHead p σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
        (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
      rw [eq_readRefillHead_nil hk he]; rfl
    simp only [getScRefillReady, NonDet.getsThe, hn, NonDet.assertOpt, NonDet.fail] at h
    exact h
  · rw [Sched.getScRefillReady_eq hk he] at h
    exact ⟨he, by rw [Set.mem_singleton_iff.1 h]⟩

theorem ak_mergeOverlapping {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) (hc : the (refillHeadOverlapping (Z := Unit) p σ) = true) :
    ∀ r ∈ (mergeOverlappingRefills (Z := Unit) p σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  obtain ⟨y, hy, -, -, -⟩ := atK_sc h
  rw [Sched.refillHeadOverlapping_eq hy] at hc
  obtain ⟨hlen, -⟩ := of_decide_eq_true hc
  obtain ⟨hd, tl, e⟩ := List.exists_cons_of_ne_nil (by intro he; rw [he] at hlen; simp at hlen : y.scRefills ≠ [])
  have hne : y.scRefills ≠ [] := by rw [e]; simp
  obtain ⟨h2, t2, e2⟩ := List.exists_cons_of_ne_nil (by intro he; rw [e, he] at hlen; simp at hlen : tl ≠ [])
  have eh : refillHd y = hd := by show the y.scRefills.head? = hd; rw [e]; rfl
  unfold mergeOverlappingRefills at hr
  rw [Notif.nd_bind_one (Sched.refillPopHead_eq hy hne)] at hr
  rw [Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _)] at hr
  obtain rfl := mem_one rfl hr
  refine atK_upd (ak_pop h hy hne) (updSc_kheap_self _ _ _ _) _ 0 fun hg hL => ?_
  obtain ⟨y0, hy0, -, -, hL0⟩ := atK_sc h
  rw [hy] at hy0; cases hy0
  have hs := (hL0 hg).2.1
  have hp := (hL0 hg).1
  rw [e, e2] at hs hp
  rw [rsum_cons, rsum_cons] at hs
  have et : y.scRefills.tail = h2 :: t2 := by rw [e, e2]; rfl
  dsimp only
  rw [et] at hL ⊢
  rw [eh] at hL ⊢
  have hp2 := (ap_cons.1 hL.1).1
  refine lk_hd hL _ ?_ ?_ <;> dsimp only [mergeRefill] <;> rw [the_cons, add_toNat (by omega)] <;> omega

theorem ak_overlapLoop {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat}
    (h : AtK p n per mx 0 σ) : ∀ r ∈ (refillHeadOverlappingLoop (Z := Unit) p σ).1, AtK p n per mx 0 r.2 := by
  intro r hr
  unfold refillHeadOverlappingLoop at hr
  exact (wl_exit (AtK p n per mx 0) (fun a s hs hc y hy => ak_mergeOverlapping hs hc y hy) h hr).1

theorem pz_refillUnblockCheck (p : ObjRef) : PZK (refillUnblockCheck (Z := Unit) p) := by
  intro σ hσ r hr
  unfold refillUnblockCheck at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨y, n, hy, rfl⟩ := mem_isRoundRobin hz
  dsimp only at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨hne, hz2⟩ := mem_getScRefillReady hy hz
  obtain ⟨b, s⟩ := z
  simp only at hz2; subst hz2
  dsimp only at hr
  have h0 := atK_of_rpos hσ hy
  unfold NonDet.when at hr
  split at hr
  · rw [Notif.nd_gets_bind] at hr
    rw [Notif.nd_bind_one (Sched.updateRefillHd_eq hy _)] at hr
    have h1 := atK_upd h0 hy _ 0 fun _ hL => lk_hd_keep hne hL (fun r => { r with rTime := s.curTime }) fun _ => rfl
    obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hz
    dsimp only at hr
    refine rpos_of_atK (n := n) (per := y.scPeriod) (mx := y.scRefillMax) (ak_overlapLoop ?_ r hr)
    exact atK_kheap h1 rfl
  · obtain rfl := Set.mem_singleton_iff.1 hr
    exact hσ

/-! ## Round-robin writers: the SC's period is 0, so `RPos` says nothing of it -/

theorem nG_of {per : Time} {mx : Nat} (h : per = 0) : ¬ G per mx := fun hg => hg.2 h

theorem pz_maybeAddEmptyTail (p : ObjRef) : PZK (maybeAddEmptyTail (Z := Unit) p) := by
  intro σ hσ r hr
  unfold maybeAddEmptyTail at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨y, n, hy, rfl⟩ := mem_isRoundRobin hz
  dsimp only at hr
  unfold NonDet.when at hr
  split at hr
  · rename_i hp
    have hp' : y.scPeriod = 0 := of_decide_eq_true hp
    obtain ⟨z, hz, hr⟩ := hr
    obtain ⟨-, rfl⟩ := mem_getRefillHead hy hz
    dsimp only at hr
    rw [Notif.nd_pure_bind', refillAddTail_eq hy] at hr
    obtain rfl := mem_one rfl hr
    exact rpos_of_atK (atK_upd (atK_of_rpos hσ hy) hy _ 0 fun hg => absurd hg (nG_of hp'))
  · obtain rfl := Set.mem_singleton_iff.1 hr
    exact hσ

/-- `refill_reset_rr` of a round-robin SC. -/
theorem pz_refillResetRr_p (p : ObjRef) (σ : State Unit) {y : SchedContext} {n : Nat}
    (hy : σ.kheap p = some (.schedContext y n)) (hp : y.scPeriod = 0) : IKp RPos σ (refillResetRr (Z := Unit) p) := by
  intro hσ r hr
  unfold refillResetRr at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨-, rfl⟩ := mem_getRefillHead hy hz
  dsimp only at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨-, rfl⟩ := mem_getRefillTail hy hz
  dsimp only at hr
  rw [Notif.nd_bind_one (Sched.updateRefillHd_eq hy _), updateRefillTl_eq (updSc_kheap_self _ _ _ _)] at hr
  obtain rfl := mem_one rfl hr
  exact rpos_of_atK (atK_upd (atK_upd (atK_of_rpos hσ hy) hy _ 0 fun hg => absurd hg (nG_of hp))
    (updSc_kheap_self _ _ _ _) _ 0 fun hg => absurd hg (nG_of hp))

/-- `refill_budget_check_round_robin` with a round-robin current SC. -/
theorem pz_rbcRR_p (u : Ticks) (σ : State Unit) {y : SchedContext} {n : Nat}
    (hy : σ.kheap σ.curSc = some (.schedContext y n)) (hp : y.scPeriod = 0) :
    IKp RPos σ (refillBudgetCheckRoundRobin (Z := Unit) u) := by
  intro hσ r hr
  unfold refillBudgetCheckRoundRobin at hr
  rw [Notif.nd_gets_bind, Notif.nd_bind_one (Sched.updateRefillHd_eq hy _),
    updateRefillTl_eq (updSc_kheap_self _ _ _ _)] at hr
  obtain rfl := mem_one rfl hr
  exact rpos_of_atK (atK_upd (atK_upd (atK_of_rpos hσ hy) hy _ 0 fun hg => absurd hg (nG_of hp))
    (updSc_kheap_self _ _ _ _) _ 0 fun hg => absurd hg (nG_of hp))

/-- `is_round_robin` read with its value. -/
theorem ikp_isRoundRobin {β : Type} {p : ObjRef} {σ : State Unit} {g : Bool → NonDet (State Unit) β}
    (h : ∀ y n, σ.kheap p = some (.schedContext y n) → IKp RPos σ (g (decide (y.scPeriod = 0)))) :
    IKp RPos σ (isRoundRobin (Z := Unit) p >>= g) := by
  intro hσ r ⟨z, hz, hr⟩
  obtain ⟨y, n, hy, rfl⟩ := mem_isRoundRobin hz
  exact h y n hy hσ r hr

/-! ## `sched_context_set_inactive` -/

theorem pz_schedContextSetInactive (p : ObjRef) : PZK (schedContextSetInactive (Z := Unit) p) := by
  intro σ hσ r hr
  unfold schedContextSetInactive at hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain ⟨y, n, hy, e1⟩ := SInvB.mem_updateSchedContext hz1
  obtain ⟨z2, hz2, hr⟩ := hr
  obtain ⟨y2, n2, hy2, e2⟩ := SInvB.mem_updateSchedContext hz2
  have hR2 : RPos z2.2 := by
    intro q w m hq
    rw [e2] at hq
    dsimp only at hq
    rw [Function.update_apply] at hq
    split_ifs at hq with eq
    · cases hq
      intro ha; simp [scRefillMaxUpdate, scActive, activeSc] at ha
    · rw [e1] at hq
      dsimp only at hq
      rw [Function.update_of_ne eq] at hq
      exact hσ q w m hq
  dsimp only at hr
  exact ik_bind (pz_updateSchedContext p (scBudgetUpdate fun _ => 0) fun _ => ⟨rfl, rfl, rfl⟩)
    (fun _ => pz_updateSchedContext p (scSporadicUpdate fun _ => false) fun _ => ⟨rfl, rfl, rfl⟩) z2.2 hR2 r hr

/-! ## `commit_time` -/

theorem pz_commitTime : PZK (commitTime (Z := Unit)) := by
  unfold commitTime
  refine ik_gets_bind fun σ => ?_
  refine ikp_keep (fun y hy => ?_) fun active => ?_
  · unfold getScActive NonDet.getsThe at hy
    cases e : readScActive (Z := Unit) σ.curSc σ with
    | none => rw [e] at hy; exact hy.elim
    | some a => rw [e] at hy; rw [Set.mem_singleton_iff.1 hy]
  refine ikp_gets_bind (ikp_bind ?_ fun _ => ik_modify fun s h => rpos_kheap h rfl)
  unfold NonDet.when
  split
  · refine ikp_gets_bind (ikp_bind ?_ fun _ => pz_updateSchedContext _ _ fun _ => ⟨rfl, rfl, rfl⟩)
    split
    · refine ikp_isRoundRobin fun y n hy => ?_
      by_cases hp : y.scPeriod = 0
      · rw [if_pos (decide_eq_true hp)]
        exact pz_rbcRR_p _ σ hy hp
      · rw [if_neg (by simpa using hp)]
        exact ikp_of_ik (pz_refillBudgetCheck _) σ
    · exact ikp_of_ik (ik_pure' _) σ
  · exact ikp_of_ik (ik_pure' _) σ

/-! ## Leaves for the generated family -/

macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_refillBudgetCheck _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_refillUnblockCheck _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_commitTime)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextSetInactive _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_maybeAddEmptyTail _)

end

end Fl4Proofs.P3.SInvE
