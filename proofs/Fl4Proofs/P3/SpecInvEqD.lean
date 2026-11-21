/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, epq2): **the configure
perform keeps `RPos`** (spec side only, outside the `JAtZ` cone).

`refill_update` keeps the old head and appends `budget - head` (or cuts the
head to `budget`), so it needs a non-empty refill list with a positive head
at the SC it rewrites (`HP p`). For a sporadic SC `RPos` itself gives that
(`MIN_BUDGET ≤ rsum`); for a round-robin one it is the entry fact `CfgOK`
carried to the perform (and across the perform's own `commit_time`):

* **`CfgOK σ p`**: the SC at `p`, when active, has refills, a head of at least
  `MIN_BUDGET`, and when `p` is the current (non-idle) SC a head sufficient for
  the consumed time. A function of SpecInvEqV's view `VZv` (`cfg_vz`); it holds
  after the front's `check_budget_restart` returned true (rd's `RV`, sb2's `RNE`,
  rd's `Suff`: `cfgOK_of`).
* `HP p σ`: the SC at `p`, when active, has refills and a positive head.
  `hp_of_cfg`, `hp_of_atK` (a sporadic SC after `refill_budget_check`),
  `hp_rbcRR` (round-robin `commit`: by `Suff` the head stays `≥ MIN_BUDGET`, or a
  single refill keeps its amount), **`hp_commitTime`**.
* **`rpos_refillUpdate`** (`RPos ∧ HP` at the SC, `MIN_BUDGET ≤ budget`).
* **`pz_configure (hD : CfgDec (.invokeSchedControl iv)) (hC : ∀ p, CfgOK σ p)`**.
-/
import Fl4Proofs.P3.SpecInvEqC
import Fl4Proofs.P3.SpecInvEqV
import Fl4Proofs.P3.SpecInvEqG6
import Fl4Proofs.P3.SpecInvRdD
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The entry fact and the head fact -/

/-- **The configure perform's entry fact** at the SC `p` (module docstring). -/
def CfgOK (σ : State Unit) (p : ObjRef) : Prop :=
  ∀ y n, σ.kheap p = some (.schedContext y n) → scActive y = true →
    y.scRefills ≠ [] ∧ MIN_BUDGET ≤ (refillHd y).rAmount ∧
    (p = σ.curSc → p ≠ σ.idleSc → refillSufficient σ.consumedTime (refillHd y) = true)

/-- The SC at `p`, when active, has refills and a positive head. -/
def HP (p : ObjRef) (σ : State Unit) : Prop :=
  ∀ y n, σ.kheap p = some (.schedContext y n) → scActive y = true →
    y.scRefills ≠ [] ∧ 0 < (refillHd y).rAmount.toNat

theorem minBudget_toNat_pos : 0 < MIN_BUDGET.toNat := by
  have h : (0 : Ticks) < MIN_BUDGET := MIN_BUDGET_pos'
  rw [BitVec.lt_def] at h
  simpa using h

theorem pos_of_minBudget {a : Ticks} (h : MIN_BUDGET ≤ a) : 0 < a.toNat := by
  have := minBudget_toNat_pos
  rw [BitVec.le_def] at h
  omega

theorem kheap_of_vz {σ σ' : State Unit} (e : VZv σ' = VZv σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (h : σ'.kheap p = some (.schedContext y n)) : σ.kheap p = some (.schedContext y n) := by
  have e1 : scAt σ' p = scAt σ p := congrFun (congrArg Prod.fst e) p
  have h1 : scAt σ' p = some (y, n) := by unfold scAt; rw [h]
  rw [e1] at h1
  unfold scAt at h1
  cases hk : σ.kheap p with
  | none => rw [hk] at h1; cases h1
  | some o =>
    rw [hk] at h1
    cases o with
    | schedContext y' n' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rfl
    | _ => cases h1

theorem cfg_vz {σ σ' : State Unit} (e : VZv σ' = VZv σ) {p : ObjRef} (h : CfgOK σ p) : CfgOK σ' p := by
  intro y n hk ha
  have e2 : σ'.curSc = σ.curSc := congrArg (fun v : VZw => v.2.1) e
  have e3 : σ'.idleSc = σ.idleSc := congrArg (fun v : VZw => v.2.2.1) e
  have e4 : σ'.consumedTime = σ.consumedTime := congrArg (fun v : VZw => v.2.2.2) e
  rw [e2, e3, e4]
  exact h y n (kheap_of_vz e hk) ha

theorem hp_of_cfg {σ : State Unit} {p : ObjRef} (h : CfgOK σ p) : HP p σ := fun y n hk ha =>
  let ⟨h1, h2, _⟩ := h y n hk ha
  ⟨h1, pos_of_minBudget h2⟩

theorem hp_vz {σ σ' : State Unit} (e : VZv σ' = VZv σ) {p : ObjRef} (h : HP p σ) : HP p σ' :=
  fun y n hk ha => h y n (kheap_of_vz e hk) ha

theorem hp_kheap {σ σ' : State Unit} {p : ObjRef} (h : HP p σ) (e : σ'.kheap = σ.kheap) : HP p σ' :=
  fun y n hk ha => h y n (by rw [← e]; exact hk) ha

/-- An SC update keeping the refills and the refill max keeps `HP`. -/
theorem hp_updSc_keep {p : ObjRef} {f : SchedContext → SchedContext} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (updateSchedContext (Z := Unit) p f σ).1)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax) (h : HP p σ) : HP p x.2 := by
  obtain ⟨y, n, hy, e⟩ := SInvB.mem_updateSchedContext hx
  intro z m hz ha
  rw [e] at hz
  simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  have ha' : scActive y = true := by
    have := (hf y).2
    simp only [scActive] at ha ⊢
    rw [← this]; exact ha
  have := h y n hy ha'
  show (f y).scRefills ≠ [] ∧ 0 < (the (f y).scRefills.head?).rAmount.toNat
  rw [(hf y).1]; exact this

theorem lk_hp {l : List Refill} (h : LK l 0) : l ≠ [] ∧ 0 < (the l.head?).rAmount.toNat := by
  obtain ⟨hA, -, hm⟩ := h
  cases l with
  | nil =>
    exfalso
    have := minBudget_toNat_pos
    simp only [rsum_nil] at hm
    omega
  | cons a t => exact ⟨List.cons_ne_nil _ _, hA a (by simp)⟩

/-- A sporadic SC tracked by `AtK` has a positive head. -/
theorem hp_of_atK {σ : State Unit} {p : ObjRef} {n : Nat} {per : Time} {mx : Nat} (h : AtK p n per mx 0 σ)
    (hp : per ≠ 0) : HP p σ := by
  obtain ⟨-, y, hy, hper, hmx, hL⟩ := h
  intro z m hz ha
  rw [hy] at hz; cases hz
  exact lk_hp (hL ⟨by rw [← hmx]; exact ha, hp⟩)

/-- `get_sc_active` reads the SC (it fails on a non-SC). -/
theorem mem_getScActive {σ : State Unit} {p : ObjRef} {z : Bool × State Unit}
    (h : z ∈ (getScActive (Z := Unit) p σ).1) :
    ∃ x n, σ.kheap p = some (.schedContext x n) ∧ z = (scActive x, σ) := by
  by_cases hs : ∃ x n, σ.kheap p = some (.schedContext x n)
  · obtain ⟨x, n, hk⟩ := hs
    exact ⟨x, n, hk, mem_one (Sched.getScActive_eq hk) h⟩
  · exfalso
    have e0 : readSchedContext (Z := Unit) p σ = none := by
      show Option.bind (σ.kheap p) (fun k => (match k with
        | .schedContext sc _ => Lookup.oreturn sc
        | _ => Lookup.ofail) σ) = none
      cases e : σ.kheap p with
      | none => rfl
      | some o =>
        cases o <;> first | rfl | exact absurd ⟨_, _, e⟩ hs
    have e1 : readScActive (Z := Unit) p σ = none := by
      show Option.bind (readSchedContext p σ) (fun sc => Lookup.oreturn (scActive sc) σ) = none
      rw [e0]; rfl
    simp only [getScActive, NonDet.getsThe, e1, NonDet.assertOpt, NonDet.fail] at h
    exact h

/-! ## `commit_time` -/

/-- The round-robin charge leaves a positive head (list arithmetic). -/
theorem rr_head (hd : Refill) (tl : List Refill) (c : Ticks) (hmin : MIN_BUDGET ≤ hd.rAmount)
    (hs : refillSufficient c hd = true) :
    ({ hd with rAmount := hd.rAmount - c } :: tl).dropLast ++
        [{ the ({ hd with rAmount := hd.rAmount - c } :: tl).getLast? with
            rAmount := (the ({ hd with rAmount := hd.rAmount - c } :: tl).getLast?).rAmount + c }] ≠ [] ∧
      0 < (the (({ hd with rAmount := hd.rAmount - c } :: tl).dropLast ++
        [{ the ({ hd with rAmount := hd.rAmount - c } :: tl).getLast? with
            rAmount := (the ({ hd with rAmount := hd.rAmount - c } :: tl).getLast?).rAmount + c }]).head?).rAmount.toNat := by
  have h0 := minBudget_toNat_pos
  unfold refillSufficient refillCapacity at hs
  simp only [decide_eq_true_eq] at hs
  split_ifs at hs with hlt
  · exact absurd (pos_of_minBudget hs) (by simp)
  · refine ⟨by simp, ?_⟩
    cases tl with
    | nil =>
      show 0 < (hd.rAmount - c + c).toNat
      rw [BitVec.sub_add_cancel]
      exact pos_of_minBudget hmin
    | cons t ts =>
      show 0 < (hd.rAmount - c).toNat
      exact pos_of_minBudget hs

theorem hp_rbcRR {σ : State Unit} {x : SchedContext} {n : Nat} (hy : σ.kheap σ.curSc = some (.schedContext x n))
    (hC : CfgOK σ σ.curSc) (hi : σ.curSc ≠ σ.idleSc) {r : Unit × State Unit}
    (hr : r ∈ (refillBudgetCheckRoundRobin (Z := Unit) σ.consumedTime σ).1) : HP σ.curSc r.2 := by
  unfold refillBudgetCheckRoundRobin at hr
  rw [Notif.nd_gets_bind, Notif.nd_bind_one (Sched.updateRefillHd_eq hy _),
    updateRefillTl_eq (updSc_kheap_self _ _ _ _)] at hr
  obtain rfl := mem_one rfl hr
  intro z m hz ha
  rw [updSc_kheap_self] at hz
  cases hz
  have hax : scActive x = true := ha
  obtain ⟨hne, hmin, hsuf⟩ := hC x n hy hax
  have hs := hsuf rfl hi
  obtain ⟨hd, tl, e⟩ := List.exists_cons_of_ne_nil hne
  have eh : refillHd x = hd := by show the x.scRefills.head? = hd; rw [e]; rfl
  rw [eh] at hmin hs
  have := rr_head hd tl σ.consumedTime hmin hs
  show (_ : List Refill) ≠ [] ∧ _
  simp only [e]
  exact this

/-- **`commit_time` from `CfgOK` at the current SC**: `RPos`, and a positive head. -/
theorem hp_commitTime (σ : State Unit) (hσ : RPos σ) (hC : CfgOK σ σ.curSc) :
    ∀ r ∈ (commitTime (Z := Unit) σ).1, RPos r.2 ∧ HP σ.curSc r.2 := by
  intro r hr
  refine ⟨pz_commitTime σ hσ r hr, ?_⟩
  unfold commitTime at hr
  rw [Notif.nd_gets_bind] at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨x0, n0, hk0, rfl⟩ := mem_getScActive hz
  try dsimp only at hr
  rw [Notif.nd_gets_bind] at hr
  obtain ⟨w, hw, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hr]
  refine hp_kheap (σ := w.2) ?_ rfl
  unfold NonDet.when at hw
  split at hw
  · rename_i hc
    rw [Notif.nd_gets_bind] at hw
    obtain ⟨v, hv, hw⟩ := hw
    refine hp_updSc_keep hw (fun _ => ⟨rfl, rfl⟩) ?_
    split at hv
    · obtain ⟨u, hu, hv⟩ := hv
      obtain ⟨x, n, hx, rfl⟩ := mem_isRoundRobin hu
      try dsimp only at hv
      split at hv
      · exact hp_rbcRR hx hC hc.2 hv
      · obtain ⟨y, m, -, hp, h⟩ := ak_refillBudgetCheck _ σ hσ v hv
        exact hp_of_atK h hp
    · rw [Set.mem_singleton_iff.1 hv]; exact hp_of_cfg hC
  · rw [Set.mem_singleton_iff.1 hw]; exact hp_of_cfg hC

/-! ## `refill_update` -/

theorem rposS_two {b : Ticks} (hb : MIN_BUDGET ≤ b) {y : SchedContext} {h r : Refill} (hr : y.scRefills = [h] ++ [r])
    (hpos : 0 < h.rAmount.toNat) (hlt : ¬ b ≤ h.rAmount) (ha : r.rAmount = b - h.rAmount) : RPosS y := by
  intro _ _
  rw [BitVec.not_le, BitVec.lt_def] at hlt
  have hs : r.rAmount.toNat = b.toNat - h.rAmount.toNat := by rw [ha, sub_toNat (by omega)]
  have hbl := b.isLt
  have hm := pos_of_minBudget hb
  rw [BitVec.le_def] at hb
  rw [hr]
  refine ⟨fun r' h' => ?_, ?_, ?_⟩
  · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl
    · exact hpos
    · omega
  · simp [SInvR.rsum]; omega
  · simp [SInvR.rsum]; omega

/-- **`refill_update` keeps `RPos`** from a non-empty refill list with a positive head. -/
theorem rpos_refillUpdate (p : ObjRef) (per b : Ticks) (mr : Nat) (hb : MIN_BUDGET ≤ b) (σ : State Unit)
    (hσ : RPos σ) {x : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext x n))
    (hne : x.scRefills ≠ []) (hpos : 0 < (refillHd x).rAmount.toNat) :
    ∀ r ∈ (refillUpdate (Z := Unit) p per b mr σ).1, RPos r.2 := by
  intro r hr
  unfold refillUpdate at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq hk _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (updSc_kheap_self _ _ _ _) _)] at hr
  rw [Notif.nd_bind_one (Sched.updateSchedContext_eq (updSc_kheap_self _ _ _ _) _)] at hr
  obtain ⟨z0, hz0, hr⟩ := hr
  obtain ⟨-, hz0s⟩ := mem_getScRefillReady (updSc_kheap_self _ _ _ _) hz0
  obtain ⟨rd, s0⟩ := z0
  simp only at hz0s
  subst hz0s
  try dsimp only at hr
  have ho : Oth p σ := oth_of_rpos hσ p
  unfold NonDet.when at hr
  split at hr
  · obtain ⟨z, hz, hr⟩ := hr
    rw [Notif.nd_gets_bind, Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _) _] at hz
    obtain rfl := mem_one rfl hz
    try dsimp only at hr
    obtain ⟨z1, hz1, hr⟩ := hr
    obtain ⟨-, rfl⟩ := mem_getRefillHead (updSc_kheap_self _ _ _ _) hz1
    try dsimp only at hr
    split at hr
    · rw [Notif.nd_bind_one (Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _) _)] at hr
      refine pz_maybeAddEmptyTail p _ ?_ r hr
      exact rpos_of_oth (by repeat (first | exact ho | refine oth_updSc ?_ _ _))
        (updSc_kheap_self _ _ _ _) (rposS_single rfl hb)
    · rename_i hlt
      rw [Notif.nd_pure_bind'] at hr
      try dsimp only at hr
      rw [Notif.nd_pure_bind'] at hr
      try dsimp only at hr
      rw [refillAddTail_eq (updSc_kheap_self _ _ _ _)] at hr
      obtain rfl := mem_one rfl hr
      exact rpos_of_oth (by repeat (first | exact ho | refine oth_updSc ?_ _ _)) (updSc_kheap_self _ _ _ _)
        (rposS_two hb rfl hpos hlt rfl)
  · obtain ⟨z, hz, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hz
    try dsimp only at hr
    obtain ⟨z1, hz1, hr⟩ := hr
    obtain ⟨-, rfl⟩ := mem_getRefillHead (updSc_kheap_self _ _ _ _) hz1
    try dsimp only at hr
    split at hr
    · rw [Notif.nd_bind_one (Sched.updateRefillHd_eq (updSc_kheap_self _ _ _ _) _)] at hr
      refine pz_maybeAddEmptyTail p _ ?_ r hr
      exact rpos_of_oth (by repeat (first | exact ho | refine oth_updSc ?_ _ _))
        (updSc_kheap_self _ _ _ _) (rposS_single rfl hb)
    · rename_i hlt
      rw [Notif.nd_pure_bind'] at hr
      try dsimp only at hr
      rw [Notif.nd_pure_bind'] at hr
      try dsimp only at hr
      rw [refillAddTail_eq (updSc_kheap_self _ _ _ _)] at hr
      obtain rfl := mem_one rfl hr
      exact rpos_of_oth (by repeat (first | exact ho | refine oth_updSc ?_ _ _)) (updSc_kheap_self _ _ _ _)
        (rposS_two hb rfl hpos hlt rfl)

/-! ## The configure perform -/

/-- The front of configure: the SC's TCB leaves the queues and, when the SC is
the current one, the consumed time is committed. -/
theorem cfg_front (scPtr : ObjRef) (sc : SchedContext) (σ : State Unit) (hσ : RPos σ) (hC : ∀ p, CfgOK σ p)
    {z : Unit × State Unit}
    (hz : z ∈ (NonDet.when (sc.scTcb ≠ none) (do
      let tcbPtr ← NonDet.assertOpt sc.scTcb
      tcbReleaseRemove (Z := Unit) tcbPtr
      tcbSchedAction tcbSchedDequeue tcbPtr
      let curSc ← NonDet.gets fun s : State Unit => s.curSc
      NonDet.when (curSc = scPtr) commitTime) σ).1) :
    RPos z.2 ∧ (sc.scTcb ≠ none → HP scPtr z.2) := by
  unfold NonDet.when at hz
  split at hz
  · rename_i hne
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨w0, hw0, hz⟩ := hz
    rw [ht] at hw0
    obtain rfl := Set.mem_singleton_iff.1 hw0
    try dsimp only at hz
    obtain ⟨w1, hw1, hz⟩ := hz
    have p1 := pz_tcbReleaseRemove t σ hσ w1 hw1
    have v1 : VZ (VZv σ) w1.2 := vz_tcbReleaseRemove t σ rfl w1 hw1
    obtain ⟨w2, hw2, hz⟩ := hz
    have p2 := pz_tcbSchedAction tcbSchedDequeue t w1.2 p1 w2 hw2
    have v2 : VZ (VZv σ) w2.2 := vz_tcbSchedAction tcbSchedDequeue t w1.2 v1 w2 hw2
    have hC2 : ∀ p, CfgOK w2.2 p := fun p => cfg_vz v2 (hC p)
    obtain ⟨w3, hw3, hz⟩ := hz
    obtain rfl := Set.mem_singleton_iff.1 hw3
    try dsimp only at hz
    split at hz
    · rename_i heq
      have h := hp_commitTime w2.2 p2 (hC2 _) z hz
      rw [heq] at h
      exact ⟨h.1, fun _ => h.2⟩
    · rw [Set.mem_singleton_iff.1 hz]
      exact ⟨p2, fun _ => hp_of_cfg (hC2 scPtr)⟩
  · rename_i hne
    rw [Set.mem_singleton_iff.1 hz]
    exact ⟨hσ, fun h => absurd h hne⟩

/-- **The configure perform keeps `RPos`**, from its decode fact (a budget of at
least `MIN_BUDGET`) and the entry fact `CfgOK` at every SC. -/
theorem pz_configure (iv : SchedControlInvocation) (hD : CfgDec (.invokeSchedControl iv)) (σ : State Unit)
    (hσ : RPos σ) (hC : ∀ p, CfgOK σ p) :
    ∀ r ∈ (invokeSchedControlConfigureFlags (Z := Unit) iv σ).1, RPos r.2 := by
  obtain ⟨scPtr, budget, period, mr, badge, flag⟩ := iv
  have hb : MIN_BUDGET ≤ budget := hD
  intro r hr
  simp only [invokeSchedControlConfigureFlags] at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨n0, -, hz2⟩ := mem_getSchedContext hz
  rw [hz2] at hr
  try dsimp only at hr
  obtain ⟨z1, hz1, hr⟩ := hr
  have h1 := cfg_front scPtr z.1 σ hσ hC hz1
  try dsimp only at hr
  split at hr
  · obtain ⟨z2, hz2, hr⟩ := hr
    have h2 := rpos_refillNew _ _ _ _ hb _ h1.1 z2 hz2
    try dsimp only at hr
    refine (?_ : PZK _) z2.2 h2 r hr
    pz_auto
  · obtain ⟨w, hw, hr⟩ := hr
    obtain ⟨x, n, hx, rfl⟩ := mem_getScActive hw
    try dsimp only at hr
    split at hr
    · rename_i hcond
      obtain ⟨hact, hne⟩ := hcond
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hne
      obtain ⟨w1, hw1, hr⟩ := hr
      rw [ht] at hw1
      obtain rfl := Set.mem_singleton_iff.1 hw1
      try dsimp only at hr
      obtain ⟨w2, hw2, hr⟩ := hr
      have p2 := pz_getThreadState t _ h1.1 w2 hw2
      have v2 : VZ (VZv z1.2) w2.2 := vz_getThreadState t _ rfl w2 hw2
      try dsimp only at hr
      split at hr
      · obtain ⟨z2, hz2, hr⟩ := hr
        have hk2 : w2.2.kheap scPtr = some (.schedContext x n) :=
          kheap_of_vz (show VZv w2.2 = VZv z1.2 from v2).symm hx
        obtain ⟨hne', hpos⟩ := h1.2 hne x n hx hact
        have h2 := rpos_refillUpdate scPtr period budget mr hb _ p2 hk2 hne' hpos z2 hz2
        try dsimp only at hr
        refine (?_ : PZK _) z2.2 h2 r hr
        pz_auto
      · obtain ⟨z2, hz2, hr⟩ := hr
        have h2 := rpos_refillNew _ _ _ _ hb _ p2 z2 hz2
        try dsimp only at hr
        refine (?_ : PZK _) z2.2 h2 r hr
        pz_auto
    · obtain ⟨z2, hz2, hr⟩ := hr
      have h2 := rpos_refillNew _ _ _ _ hb _ h1.1 z2 hz2
      try dsimp only at hr
      refine (?_ : PZK _) z2.2 h2 r hr
      pz_auto

end

end Fl4Proofs.P3.SInvE
