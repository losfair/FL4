/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd1): **the SC switch at the
kernel exit: `refill_unblock_check` and `switch_sched_context` give `OffReady`
and keep `Rdy`** (spec side only, outside the `JAtZ` cone).

* `wl_inv`: an invariant of `whileLoop`'s outcomes.
* `ruc_out`: `refill_unblock_check p` either changes nothing, or rewrites only
  the SC at `p` (and sets the reprogram flag), the new head at the current
  time, binding / refill max / period / sporadic flag kept, refills non-empty
  (`refill_head_overlapping_loop`'s merges keep the head's time).
* `icb_out`: the same for `if_constant_bandwidth_refill_unblock_check`.
* `Excl σ p`: no thread bound to `p` is ready-queued, the switch target, or in
  a `BlkR` state (at the SC switch, the only thread bound to the new SC is
  the new current thread, which is dequeued, not the switch target (the action
  is `resume_cur_thread`) and runnable). `rdy_framex`: `Rdy` across any
  rewrite of such an SC keeping its refill-max clause.
* **`sw_out`**: `switch_sched_context` from a state with `Rdy`, `OffReady`,
  `Suff` (the intra-entry sufficiency), the current SC an SC with refills when
  active, the current thread bound to an SC `p` with refills whose head is ready
  when `p` is not the current SC (the off1 item 6 obligation: from R1 / R2 /
  the idle SC), and `Excl σ p` when `p` is not the current SC: afterwards
  `Rdy`, **`OffReady`** and the current SC is `p`.
  rd4: the precondition `OffReady ∧ Suff` is generalised to the overrun
  disjunct `(OffReady ∧ Suff) ∨ (consumed = 0 ∧ (p = cur_sc → OffReady))`
  (after `charge_budget`'s overrun the head is in the future but the consumed
  time is 0, so `commit_time` changes no refill: `commit_zero`,
  `rdy_commitZero`), and `p`'s refills are needed only when `p ≠ cur_sc`.
-/
import Fl4Proofs.P3.SpecInvRdA
open Classical
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

section
open Fl4Spec

/-- **An invariant of `whileLoop`'s outcomes.** -/
theorem wl_inv {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α} (P : State Unit → Prop)
    (hB : ∀ a s, P s → C a s → ∀ y ∈ (B a s).1, P y.2) {a : α} {s : State Unit} (hs : P s)
    {r : α × State Unit} (hr : r ∈ (NonDet.whileLoop C B a s).1) : P r.2 := by
  have hw : NonDet.WhileResults C B a s r := hr
  clear hr
  revert hs
  induction hw with
  | done _ => exact id
  | step hc hm _ ih => exact fun hs => ih (hB _ _ hs hc _ hm)

/-- The merge invariant of `refill_unblock_check` from `σ2`, SC `p`, head time `T`. -/
def UI (σ2 : State Unit) (p : ObjRef) (n : Nat) (T : Time) (y0 : SchedContext) (s : State Unit) : Prop :=
  ∃ z, s = updSc σ2 p z n ∧ z.scRefills ≠ [] ∧ (refillHd z).rTime = T ∧ z.scTcb = y0.scTcb ∧
    z.scRefillMax = y0.scRefillMax ∧ z.scSporadic = y0.scSporadic ∧ z.scPeriod = y0.scPeriod ∧
    (rsum y0.scRefills < 2 ^ 64 → rsum z.scRefills = rsum y0.scRefills ∧
      (refillHd y0).rAmount.toNat ≤ (refillHd z).rAmount.toNat)

theorem ui_merge {σ2 : State Unit} {p : ObjRef} {n : Nat} {T : Time} {y0 : SchedContext} (a : Unit)
    (s : State Unit) (hs : UI σ2 p n T y0 s) (hc : the (refillHeadOverlapping (Z := Unit) p s) = true) :
    ∀ y ∈ (mergeOverlappingRefills (Z := Unit) p s).1, UI σ2 p n T y0 y.2 := by
  obtain ⟨z, rfl, hz1, hz2, hz3, hz4, hz5, hz6, hz9⟩ := hs
  rw [refillHeadOverlapping_eq (kh_upd _ _ _ _)] at hc
  have hlen : z.scRefills.length > 1 := by
    simp only [Sched.the_some, decide_eq_true_eq] at hc; exact hc.1
  obtain ⟨a, b, rest, hab⟩ : ∃ a b rest, z.scRefills = a :: b :: rest := by
    rcases hz : z.scRefills with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rw [hz] at hlen; simp at hlen
    · rw [hz] at hlen; simp at hlen
    · exact ⟨a, b, rest, rfl⟩
  intro y hy
  unfold mergeOverlappingRefills at hy
  rw [nd_bind_one (refillPopHead_eq (kh_upd _ _ _ _) hz1), updateRefillHd_eq (kh_upd _ _ _ _), updSc_updSc,
    updSc_updSc] at hy
  obtain rfl : y = ((), _) := hy
  refine ⟨_, rfl, by simp, ?_, hz3, hz4, hz5, hz6, fun hs0 => ?_⟩
  · show (refillHd { z with scRefills := mergeRefill (refillHd z) (the z.scRefills.tail.head?) ::
      z.scRefills.tail.tail }).rTime = T
    simp only [refillHd, List.head?_cons, Sched.the_some, mergeRefill]
    exact hz2
  · obtain ⟨hz7, hz8⟩ := hz9 hs0
    show rsum (mergeRefill (refillHd z) (the z.scRefills.tail.head?) :: z.scRefills.tail.tail) = _ ∧
      _ ≤ (refillHd { z with scRefills := mergeRefill (refillHd z) (the z.scRefills.tail.head?) ::
        z.scRefills.tail.tail }).rAmount.toNat
    simp only [refillHd, hab, List.head?_cons, Sched.the_some, List.tail_cons, mergeRefill, rsum_cons] at hz7 hz8 ⊢
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **`refill_unblock_check`** (module docstring). -/
theorem ruc_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p σ).1) :
    r.2 = σ ∨ (y.scPeriod ≠ 0 ∧ UI { σ with reprogramTimer := true } p n σ.curTime y r.2) := by
  unfold refillUnblockCheck at hr
  rw [nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getScRefillReady_eq hk hne)] at hr
  simp only [NonDet.when] at hr
  split_ifs at hr with hc
  · rw [nd_gets_bind, nd_bind_one (updateRefillHd_eq hk _), SInvV.sv_bind_modify] at hr
    right
    refine ⟨fun h0 => by simp [h0] at hc, ?_⟩
    unfold refillHeadOverlappingLoop at hr
    refine wl_inv (UI { σ with reprogramTimer := true } p n σ.curTime y) (fun a s hs hc' => ui_merge a s hs hc')
      ?_ hr
    refine ⟨{ y with scRefills := { (the y.scRefills.head?) with rTime := σ.curTime } :: y.scRefills.tail }, rfl,
      by simp, ?_, rfl, rfl, rfl, rfl, fun _ => ⟨?_, ?_⟩⟩
    · simp only [refillHd, List.head?_cons, Sched.the_some]
    · obtain ⟨h0, t0, e⟩ := List.exists_cons_of_ne_nil hne
      show rsum (({ (the y.scRefills.head?) with rTime := σ.curTime } : Refill) :: y.scRefills.tail) = _
      rw [e]; simp only [List.head?_cons, Sched.the_some, List.tail_cons, rsum_cons]
    · show _ ≤ (refillHd { y with scRefills := { (the y.scRefills.head?) with rTime := σ.curTime } ::
        y.scRefills.tail }).rAmount.toNat
      simp only [refillHd, List.head?_cons, Sched.the_some]; exact le_refl _
  · left
    obtain rfl : r = ((), σ) := hr
    rfl

/-- **`if_constant_bandwidth_refill_unblock_check (some p)`**. -/
theorem icb_out {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {r : Unit × State Unit}
    (hr : r ∈ (ifConstantBandwidthRefillUnblockCheck (Z := Unit) (some p) σ).1) :
    r.2 = σ ∨ (y.scPeriod ≠ 0 ∧ UI { σ with reprogramTimer := true } p n σ.curTime y r.2) := by
  change r ∈ (ifCondRefillUnblockCheck (Z := Unit) (some p) none none σ).1 at hr
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hr
  dsimp only at hr
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind'] at hr
  simp only [NonDet.when] at hr
  split_ifs at hr
  all_goals first
    | exact ruc_out hk hne hr
    | (left; obtain rfl : r = ((), σ) := hr; rfl)

/-! ## The SC switch -/

/-- No thread bound to `p` is queued, the switch target, or `BlkR`. -/
def Excl (σ : State Unit) (p : ObjRef) : Prop :=
  ∀ t x, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some p →
    (∀ d q, t ∉ σ.readyQueues d q) ∧ σ.schedulerAction ≠ .switchThread t ∧ ¬ BlkR x.tcbState x.tcbFault

theorem rdyT_keep {σ σ' : State Unit} {p : ObjRef} (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime) (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) {t : ObjRef} (h : RdyT σ t)
    (hn : ∀ x, σ.kheap t = some (.tcb x) → x.tcbSchedContext ≠ some p) : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, ha, hr⟩ := h
  have htp : t ≠ p := by rintro rfl; exact hpt x hx
  have hcp : c ≠ p := by rintro rfl; exact hn x hx hc
  exact ⟨x, c, y, n, by rw [hk t htp]; exact hx, hc, by rw [hk c hcp]; exact hy, ha, by rw [ht]; exact hr⟩

/-- **`Rdy` across a rewrite of an `Excl` SC.** -/
theorem rdy_framex {σ σ' : State Unit} {p : ObjRef} (h : Rdy σ) (hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q)
    (ht : σ'.curTime = σ.curTime) (hq : σ'.readyQueues = σ.readyQueues)
    (ha : σ'.schedulerAction = σ.schedulerAction) (hX : Excl σ p)
    (hpt : ∀ x, σ.kheap p ≠ some (.tcb x)) (hpt' : ∀ x, σ'.kheap p ≠ some (.tcb x))
    (hpv : ∀ z n, σ'.kheap p = some (.schedContext z n) → scActive z = true → RVs z)
    (hrq : σ'.releaseQueue = σ.releaseQueue)
    (hpa : ∀ y n, σ.kheap p = some (.schedContext y n) → scActive y = true →
      ∃ z m, σ'.kheap p = some (.schedContext z m) ∧ scActive z = true)
    (hid : σ'.idleSc = σ.idleSc)
    (hpI : p = σ.idleSc → ∀ z m, σ'.kheap p = some (.schedContext z m) →
      z.scRefills ≠ [] ∧ (refillHd z).rTime.toNat ≤ σ.curTime.toNat) :
    Rdy σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d q t hm => ?_, fun t e => ?_, fun t x c hx hb hc => ?_, fun q z n hz hz' => ?_,
    fun t hm => actB_frame1 hk hpt hpa (h5 t (hrq ▸ hm)), fun z m hz => ?_⟩
  rotate_right
  · rw [hid] at hz; rw [ht]
    by_cases e : σ.idleSc = p
    · exact hpI e.symm z m (e ▸ hz)
    · rw [hk _ e] at hz; exact h6 z m hz
  · rw [hq] at hm
    exact rdyT_keep hk ht hpt (h1 d q t hm) fun x hx e => (hX t x hx e).1 d q hm
  · rw [ha] at e
    exact rdyT_keep hk ht hpt (h2 t e) fun x hx e' => (hX t x hx e').2.1 e
  · have htp : t ≠ p := by rintro rfl; exact hpt' x hx
    rw [hk t htp] at hx
    exact rdyT_keep hk ht hpt (h3 t x c hx hb hc) fun x' hx' e' => by
      rw [hx] at hx'; cases hx'; exact (hX t x hx e').2.2 hb
  · by_cases e : q = p
    · subst e; exact hpv z n hz hz'
    · rw [hk q e] at hz; exact h4 q z n hz hz'

/-- `Rdy` reads only the heap, the queues, the action and the time. -/
theorem rdy_congr {σ σ' : State Unit} (h : Rdy σ) (hk : σ'.kheap = σ.kheap) (ht : σ'.curTime = σ.curTime)
    (hid : σ'.idleSc = σ.idleSc) (hq : σ'.readyQueues = σ.readyQueues) (ha : σ'.schedulerAction = σ.schedulerAction)
    (hrq : ∀ t, t ∈ σ'.releaseQueue → t ∈ σ.releaseQueue) : Rdy σ' := by
  have F : ∀ {t}, RdyT σ t → RdyT σ' t := fun {t} ⟨x, c, y, n, hx, hc, hy, h1, h2⟩ =>
    ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1, by rw [ht]; exact h2⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨fun d q t hm => F (h1 d q t (hq ▸ hm)), fun t e => F (h2 t (ha ▸ e)),
    fun t x c hx hb hc => F (h3 t x c (hk ▸ hx) hb hc), fun q z n hz hz' => h4 q z n (hk ▸ hz) hz',
    fun t hm => by
      obtain ⟨x, c, y, n, hx, hc, hy, h1⟩ := h5 t (hrq t hm)
      exact ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1⟩,
    fun z m hz => by rw [hid, hk] at hz; rw [ht]; exact h6 z m hz⟩

theorem rvs_congr' {y z : SchedContext} (e1 : z.scRefills = y.scRefills) (e2 : z.scRefillMax = y.scRefillMax)
    (e3 : z.scPeriod = y.scPeriod) (h : RVs y) : RVs z := by
  unfold RVs refillHd at *; rw [e1, e2, e3]; exact h

/-- **`commit_time` at zero consumed time** (rd4): only the current SC's
`scConsumed` changes (refills, refill max, binding kept), consumed time 0. -/
theorem commit_zero {σ : State Unit} {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (h0 : σ.consumedTime = 0) {r : Unit × State Unit}
    (hr : r ∈ (commitTime (Z := Unit) σ).1) :
    ∃ y, r.2 = { Sched.updSc σ σ.curSc y n with consumedTime := 0 } ∧ y.scRefills = x.scRefills ∧
      y.scRefillMax = x.scRefillMax ∧ y.scPeriod = x.scPeriod := by
  unfold commitTime at hr
  rw [nd_gets_bind, nd_bind_one (getScActive_eq hk), nd_gets_bind] at hr
  by_cases hc : scActive x = true ∧ σ.curSc ≠ σ.idleSc
  · rw [NonDet.when, if_pos hc, nd_bind_assoc', nd_gets_bind, nd_bind_assoc'] at hr
    have h0' : ¬ (0 < σ.consumedTime) := by rw [h0]; simp
    rw [NonDet.when, if_neg h0', nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl),
      nd_bind_one (updateSchedContext_eq hk _)] at hr
    obtain rfl : r = ((), _) := hr
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [NonDet.when, if_neg hc, nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
      at hr
    obtain rfl : r = ((), _) := hr
    refine ⟨x, ?_, rfl, rfl, rfl⟩
    show _ = { Sched.updSc σ σ.curSc x n with consumedTime := 0 }
    rw [updSc_self hk]

/-- **`commit_time` with the current SC inactive** (rd14e's FINDING, lead
option (a)): nothing is committed, only the consumed time is reset. -/
theorem commit_inactive {σ : State Unit} {x : SchedContext} {n : Nat}
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (ha : scActive x = false) {r : Unit × State Unit}
    (hr : r ∈ (commitTime (Z := Unit) σ).1) : r.2 = { σ with consumedTime := 0 } := by
  unfold commitTime at hr
  rw [nd_gets_bind, nd_bind_one (getScActive_eq hk), nd_gets_bind] at hr
  have hc : ¬ (scActive x = true ∧ σ.curSc ≠ σ.idleSc) := fun h => by rw [ha] at h; exact Bool.false_ne_true h.1
  rw [NonDet.when, if_neg hc, nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
    at hr
  obtain rfl : r = ((), _) := hr
  rfl

/-- `Rdy` across `commit_time` at zero consumed time. -/
theorem rdy_commitZero {σ : State Unit} {x : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) {y : SchedContext} (e1 : y.scRefills = x.scRefills)
    (e2 : y.scRefillMax = x.scRefillMax) (e3 : y.scPeriod = x.scPeriod) :
    Rdy ({ Sched.updSc σ σ.curSc y n with consumedTime := 0 } : State Unit) := by
  have hkc : ∀ q, q ≠ σ.curSc → ({ Sched.updSc σ σ.curSc y n with consumedTime := 0 } : State Unit).kheap q =
      σ.kheap q := fun q hq => by simp [Notif.updK, hq]
  have hkp : ({ Sched.updSc σ σ.curSc y n with consumedTime := 0 } : State Unit).kheap σ.curSc =
      some (.schedContext y n) := kh_upd _ _ _ _
  have hay : scActive y = scActive x := by simp only [scActive, e2]
  have ehd : refillHd y = refillHd x := by unfold refillHd; rw [e1]
  refine rdy_frame1 h hkc rfl rfl rfl (fun y0 n0 hy0 ha0 hr0 => ?_) (fun x0 hx0 => by rw [hk] at hx0; cases hx0)
    (fun x0 hx0 => by rw [hkp] at hx0; cases hx0) (fun z n0 hz hz' => ?_) rfl
    (fun y0 n0 hy0 ha0 => ⟨y, n, hkp, by rw [hk] at hy0; cases hy0; rw [hay]; exact ha0⟩) rfl
    (fun eI z0 m0 hz0 => by
      rw [hkp] at hz0; cases hz0
      have := h.2.2.2.2.2 x n (by rw [← eI]; exact hk)
      exact ⟨by rw [e1]; exact this.1, by rw [ehd]; exact this.2⟩)
  · rw [hk] at hy0; cases hy0
    exact ⟨y, hkp, by rw [hay]; exact ha0, by rw [ehd]; exact hr0⟩
  · rw [hkp] at hz; cases hz
    rw [hay] at hz'
    exact rvs_congr' e1 e2 e3 (h.2.2.2.1 _ x n hk hz')

/-- **`switch_sched_context`** (module docstring; rd4: the overrun case
`consumed = 0` is allowed, `hOS`, and the new SC's refills are needed only
when it is not the current SC). -/
theorem sw_out {σ : State Unit} {x : SchedContext} {n : Nat} {xt : Tcb} {p : ObjRef} {y : SchedContext} {m : Nat}
    (h : Rdy σ) (hk : σ.kheap σ.curSc = some (.schedContext x n))
    (hOS : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ (p = σ.curSc → Sched.OffReady σ)) ∨
      (scActive x = false ∧ p ≠ σ.curSc))
    (hne : scActive x = true → x.scRefills ≠ []) (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hsc : xt.tcbSchedContext = some p) (hp : σ.kheap p = some (.schedContext y m))
    (hnp : p ≠ σ.curSc → y.scRefills ≠ [])
    (hHR : p ≠ σ.curSc → (refillHd y).rTime.toNat ≤ σ.curTime.toNat) (hX : p ≠ σ.curSc → Excl σ p)
    {r : Unit × State Unit} (hr : r ∈ (switchSchedContext (Z := Unit) σ).1) :
    Rdy r.2 ∧ Sched.OffReady r.2 ∧ r.2.curSc = p := by
  unfold switchSchedContext at hr
  rw [nd_gets_bind, nd_gets_bind, nd_bind_one (Endp.getTcbObjRef_eq _ hct), hsc,
    nd_bind_one (show NonDet.assertOpt (some p) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (getSchedContext_eq hk)] at hr
  -- the tail: reprogram test, commit, the new current SC
  have tail : ∀ s : State Unit, Rdy s →
      ((Sched.OffReady s ∧ Suff s) ∨ (s.consumedTime = 0 ∧ (p = σ.curSc → Sched.OffReady s)) ∨
        (scActive x = false ∧ p ≠ σ.curSc)) →
      s.curSc = σ.curSc →
      s.kheap σ.curSc = some (.schedContext x n) → (s.reprogramTimer = false → s.curSc = p) →
      (∀ z k, s.kheap p = some (.schedContext z k) → p ≠ σ.curSc → (refillHd z).rTime.toNat ≤ s.curTime.toNat) →
      ∀ r ∈ ((do
        let reprogram ← NonDet.gets fun s : State Unit => s.reprogramTimer
        NonDet.when reprogram commitTime
        NonDet.modify fun s : State Unit => { s with curSc := p }) s).1,
      Rdy r.2 ∧ Sched.OffReady r.2 ∧ r.2.curSc = p := by
    intro s hR hOS' hcs hks hrp hpz r hr
    rw [nd_gets_bind] at hr
    simp only [NonDet.when] at hr
    have hks' : s.kheap s.curSc = some (.schedContext x n) := by rw [hcs]; exact hks
    split_ifs at hr with hrt
    · obtain ⟨c, hc, hr⟩ := hr
      rcases hOS' with ⟨hO', hS'⟩ | ⟨h0, hOp⟩ | ⟨hxa, hpne⟩
      · obtain ⟨hR2, hO2, y2, e, -, -, -, -, -, -, -, -, -⟩ := rdy_commitTime hR hks' hO' hS' hne hc
        obtain rfl : r = ((), _) := hr
        refine ⟨rdy_congr hR2 rfl rfl rfl rfl rfl fun _ h => h, fun z k hz => ?_, rfl⟩
        have hz0 : c.2.kheap p = some (.schedContext z k) := hz
        show (refillHd z).rTime.toNat + c.2.consumedTime.toNat ≤ c.2.curTime.toNat
        by_cases epc : p = s.curSc
        · have ec : c.2.curSc = p := by rw [e]; exact epc.symm
          exact hO2 z k (ec ▸ hz0)
        · rw [e] at hz0 ⊢
          have hz' : s.kheap p = some (.schedContext z k) := by simpa [Notif.updK, epc] using hz0
          show (refillHd z).rTime.toNat + (0 : Ticks).toNat ≤ s.curTime.toNat
          simpa using hpz z k hz' (by rw [← hcs]; exact epc)
      · obtain ⟨y2, e, ey1, ey2, ey3⟩ := commit_zero hks' h0 hc
        obtain rfl : r = ((), _) := hr
        have hR2 : Rdy c.2 := by rw [e]; exact rdy_commitZero hR hks' ey1 ey2 ey3
        refine ⟨rdy_congr hR2 rfl rfl rfl rfl rfl fun _ h => h, fun z k hz => ?_, rfl⟩
        have hz0 : c.2.kheap p = some (.schedContext z k) := hz
        show (refillHd z).rTime.toNat + c.2.consumedTime.toNat ≤ c.2.curTime.toNat
        rw [e] at hz0 ⊢
        show (refillHd z).rTime.toNat + (0 : Ticks).toNat ≤ s.curTime.toNat
        by_cases epc : p = s.curSc
        · rw [epc, kh_upd] at hz0
          have ehd : refillHd z = refillHd x := by
            have e3 : y2 = z := by injection hz0 with e; injection e
            rw [← e3]; unfold refillHd; rw [ey1]
          have := hOp (epc.trans hcs) x n hks'
          rw [h0] at this
          rw [ehd]; simpa using this
        · have hz' : s.kheap p = some (.schedContext z k) := by simpa [Notif.updK, epc] using hz0
          simpa using hpz z k hz' (by rw [← hcs]; exact epc)
      · have e := commit_inactive hks' hxa hc
        obtain ⟨_, c2⟩ := c
        dsimp only at e hr
        subst e
        obtain rfl : r = ((), _) := hr
        refine ⟨rdy_congr hR rfl rfl rfl rfl rfl fun _ h => h, fun z k hz => ?_, rfl⟩
        have hz' : s.kheap p = some (.schedContext z k) := hz
        show (refillHd z).rTime.toNat + (0 : Ticks).toNat ≤ s.curTime.toNat
        simpa using hpz z k hz' hpne
    · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () s = ({((), s)}, False) from rfl)] at hr
      obtain rfl : r = ((), _) := hr
      have e := hrp (by simpa using hrt)
      have hO' : Sched.OffReady s := by
        rcases hOS' with ⟨hO', -⟩ | ⟨-, hOp⟩ | ⟨-, hpne⟩
        · exact hO'
        · exact hOp (by rw [← hcs, e])
        · exact absurd (e.symm.trans hcs) hpne
      refine ⟨rdy_congr hR rfl rfl rfl rfl rfl fun _ h => h, fun z k hz => ?_, rfl⟩
      exact hO' z k (by rw [e]; exact hz)
  by_cases hpc : p = σ.curSc
  · rw [NonDet.when, if_neg (not_not.2 hpc),
      nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)] at hr
    exact tail σ h hOS rfl hk (fun _ => hpc.symm) (fun _ _ _ e => absurd hpc e) r hr
  · rw [NonDet.when, if_pos hpc, nd_bind_assoc', SInvV.sv_bind_modify] at hr
    obtain ⟨c, hc, hr⟩ := hr
    have hpk : ({ σ with reprogramTimer := true } : State Unit).kheap p = some (.schedContext y m) := hp
    have hcne : σ.curSc ≠ p := fun e => hpc e.symm
    have hOSr : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ (p = σ.curSc → Sched.OffReady σ)) ∨
        (scActive x = false ∧ p ≠ σ.curSc) := hOS
    rcases icb_out hpk (hnp hpc) hc with e | ⟨hpp, z, e, hz1, hz2, hz3, hz4, hz5, hz6, hz9⟩
    · rw [e] at hr
      refine tail { σ with reprogramTimer := true } (rdy_congr h rfl rfl rfl rfl rfl fun _ h => h) hOSr rfl hk
        (fun e => by cases e) (fun z k hz _ => ?_) r hr
      have hz' : σ.kheap p = some (.schedContext z k) := hz
      rw [hp] at hz'; cases hz'; exact hHR hpc
    · rw [e] at hr
      have hkq : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z m).kheap q = σ.kheap q :=
        fun q hq => by simp [Notif.updK, hq]
      refine tail (updSc { σ with reprogramTimer := true } p z m) ?_ ?_ rfl ((hkq _ hcne).trans hk)
        (fun e => by cases e) (fun z' k hz _ => ?_) r hr
      · refine rdy_framex h hkq rfl rfl rfl (hX hpc) (fun x0 hx0 => by rw [hp] at hx0; cases hx0)
          (fun x0 hx0 => by
            have hx1 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.tcb x0) := hx0
            rw [kh_upd] at hx1; cases hx1) (fun z' k hz hz' => ?_) rfl
          (fun y0 n0 hy0 ha0 => ⟨z, m, kh_upd _ _ _ _, by
            rw [hp] at hy0; cases hy0; simpa only [scActive, hz4] using ha0⟩) rfl
          (fun _ z' k hz => by
            have hz0 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.schedContext z' k) := hz
            rw [kh_upd] at hz0; cases hz0
            exact ⟨hz1, by rw [hz2]⟩)
        have hz0 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.schedContext z' k) := hz
        rw [kh_upd] at hz0; cases hz0
        have ha : scActive y = true := by simpa only [scActive, hz4] using hz'
        obtain ⟨v1, v2, v3, -⟩ := h.2.2.2.1 p y m hp ha
        obtain ⟨w1, w2⟩ := hz9 v3
        refine ⟨by rw [hz4]; exact v1, ?_, by rw [w1]; exact v3, fun h0 => absurd (by rw [← hz6]; exact h0) hpp⟩
        rw [BitVec.le_def] at v2 ⊢; omega
      · rcases hOS with ⟨hO, hS⟩ | ⟨h0, -⟩ | hI3
        · refine Or.inl ⟨fun z' k hz => ?_, fun z' k hz hz' hz'' => ?_⟩
          · exact hO z' k ((hkq _ hcne).symm.trans hz)
          · exact hS z' k ((hkq _ hcne).symm.trans hz) hz' hz''
        · exact Or.inr (Or.inl ⟨h0, fun e => absurd e hpc⟩)
        · exact Or.inr (Or.inr hI3)
      · have hz0 : (updSc { σ with reprogramTimer := true } p z m).kheap p = some (.schedContext z' k) := hz
        rw [kh_upd] at hz0; cases hz0
        show (refillHd z).rTime.toNat ≤ σ.curTime.toNat
        rw [hz2]

end

end

end Fl4Proofs.P3.SInvR
