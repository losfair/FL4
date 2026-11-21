/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd2): **`Suff` is
intra-entry, established locally** (lead decision 2: never carried; KENTRY-PLAN
rd1 handoff 4).

* `mem_getScRefillSufficient'`: an outcome of `get_sc_refill_sufficient p u`
  reads an SC at `p` and returns `refill_sufficient u (refill_hd sc)`, the state
  unchanged (no outcome when `p` is not an SC with refills).
* **`suff_checkBudget`**: an outcome of `check_budget` returning `true` leaves
  the state unchanged and the consumed time sufficient for the current SC's
  head (`Suff`, unconditionally: no activity / idle test needed).
* **`suff_checkBudgetRestart`**: the same for `check_budget_restart`.
-/
import Fl4Proofs.P3.SpecInvRdC
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

theorem readSchedContext_none {σ : State Unit} {p : ObjRef} (hk : ∀ y n, σ.kheap p ≠ some (.schedContext y n)) :
    readSchedContext (Z := Unit) p σ = none := by
  show Option.bind (readObject p σ) (fun k => (match k with
    | .schedContext sc _ => Lookup.oreturn sc
    | _ => Lookup.ofail) σ) = _
  cases e : σ.kheap p with
  | none => simp [readObject, e]
  | some o =>
    cases o with
    | schedContext y n => exact absurd e (hk y n)
    | _ => simp [readObject, e, Lookup.ofail]

theorem mem_getScRefillSufficient' {σ : State Unit} {p : ObjRef} {u : Ticks} {w : Bool × State Unit}
    (h : w ∈ (getScRefillSufficient (Z := Unit) p u σ).1) :
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ w = (refillSufficient u (refillHd y), σ) := by
  by_cases hk : ∃ y n, σ.kheap p = some (.schedContext y n)
  · obtain ⟨y, n, hk⟩ := hk
    exact ⟨y, n, hk, mem_getScRefillSufficient hk u h⟩
  · exfalso
    have hk' : ∀ y n, σ.kheap p ≠ some (.schedContext y n) := fun y n e => hk ⟨y, n, e⟩
    have e : readScRefillSufficient (Z := Unit) p u σ = none := by
      show Option.bind (readRefillHead p σ) (fun h => Lookup.oreturn (refillSufficient u h) σ) = _
      have e2 : readRefillHead (Z := Unit) p σ = none := by
        show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
          (fun _ => Lookup.oreturn (refillHd sc) σ)) = _
        rw [readSchedContext_none hk']; rfl
      rw [e2]; rfl
    change w ∈ (NonDet.assertOpt (readScRefillSufficient (Z := Unit) p u σ) σ).1 at h
    rw [e] at h; exact h

/-- **`check_budget` returning `true`**: state unchanged, `Suff`. -/
theorem suff_checkBudget {σ : State Unit} {r : Bool × State Unit} (hr : r ∈ (checkBudget (Z := Unit) σ).1)
    (ht : r.1 = true) : r.2 = σ ∧ Suff σ := by
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
    refine ⟨rfl, fun y' n' hk' _ _ => ?_⟩
    rw [hk] at hk'; cases hk'; exact hs
  · obtain ⟨z, -, hr⟩ := hr
    obtain ⟨z, -, hr⟩ := hr
    obtain rfl := Set.mem_singleton_iff.1 hr
    cases ht

/-- **`check_budget_restart` returning `true`**: state unchanged, `Suff`. -/
theorem suff_checkBudgetRestart {σ : State Unit} {r : Bool × State Unit}
    (hr : r ∈ (checkBudgetRestart (Z := Unit) σ).1) (ht : r.1 = true) : r.2 = σ ∧ Suff σ := by
  unfold checkBudgetRestart at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨z1, hz1, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz1
  obtain ⟨z2, hz2, hr⟩ := hr
  unfold getThreadState at hz2
  obtain ⟨x, -, rfl⟩ := q1_mem_threadGet hz2
  obtain ⟨z3, hz3, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hr
  have hb : z.1 = true := ht
  have hw : z3.2 = z.2 := by
    unfold NonDet.when at hz3
    rw [if_neg (by rw [hb]; simp)] at hz3
    rw [Set.mem_singleton_iff.1 hz3]
  obtain ⟨e, hS⟩ := suff_checkBudget hz hb
  exact ⟨hw.trans e, hS⟩

/-! ## The time stamp -/

/-- `Rdy` across a later time (same heap, queues, action). -/
theorem rdy_later {σ σ' : State Unit} (h : Rdy σ) (hk : σ'.kheap = σ.kheap)
    (hq : σ'.readyQueues = σ.readyQueues) (ha : σ'.schedulerAction = σ.schedulerAction)
    (ht : σ.curTime.toNat ≤ σ'.curTime.toNat) (hrq : σ'.releaseQueue = σ.releaseQueue)
    (hid : σ'.idleSc = σ.idleSc) : Rdy σ' := by
  have F : ∀ {t}, RdyT σ t → RdyT σ' t := fun {t} ⟨x, c, y, n, hx, hc, hy, h1, h2⟩ =>
    ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1,
      ready_of_nat (Nat.le_trans (nat_of_ready h2) ht)⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨fun d q t hm => F (h1 d q t (hq ▸ hm)), fun t e => F (h2 t (ha ▸ e)),
    fun t x c hx hb hc => F (h3 t x c (hk ▸ hx) hb hc), fun q z n hz hz' => h4 q z n (hk ▸ hz) hz',
    fun t hm => by
      obtain ⟨x, c, y, n, hx, hc, hy, h1⟩ := h5 t (hrq ▸ hm)
      exact ⟨x, c, y, n, by rw [hk]; exact hx, hc, by rw [hk]; exact hy, h1⟩,
    fun z m hz => by
      rw [hid, hk] at hz
      obtain ⟨a1, a2⟩ := h6 z m hz
      exact ⟨a1, Nat.le_trans a2 ht⟩⟩

/-- The queues and the action, fixed. -/
abbrev QA (Q : Domain → Priority → List ObjRef) (A : SchedulerAction) (R : List ObjRef) (I : ObjRef)
    (σ : State Unit) : Prop :=
  σ.readyQueues = Q ∧ σ.schedulerAction = A ∧ σ.releaseQueue = R ∧ σ.idleSc = I

theorem qa_updateTimeStamp (Q : Domain → Priority → List ObjRef) (A : SchedulerAction) (R : List ObjRef)
    (I : ObjRef) : IK (QA Q A R I) (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp
  repeat' (first | (with_reducible exact ik_doMachineOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

/-- **`update_time_stamp` keeps `Rdy`** (the clock is monotone by
`ValidMachineTime`, the new time below `2 ^ 64`). -/
theorem rdy_updateTimeStamp {σ : State Unit} (hv : SInvV.ValidMachineTime σ) (h : Rdy σ)
    {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) : Rdy x.2 := by
  obtain ⟨ek, -, et, -⟩ := SInvO.uts_off hx
  obtain ⟨eq, ea, er, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ x hx
  refine rdy_later h ek eq ea ?_ er ei
  have a1 : σ.curTime.toNat ≤ σ.machineState.lastMachineTime.toNat := BitVec.le_def.mp hv.1
  have a2 : σ.machineState.lastMachineTime.toNat ≤ SInvV.gctN σ.machineState := by
    unfold SInvV.gctN; exact le_min hv.2 (Nat.le_add_right _ _)
  rw [et, SInvV.gctN_toNat]
  omega

/-! ## Writers pinned to an `RdyT` thread -/

/-- **`tcb_sched_enqueue` / `tcb_sched_append`** of a thread `RdyT` at this state. -/
theorem rd_enqueue_p (t : ObjRef) (σ : State Unit) (hR : RdyT σ t) :
    IKp Rdy σ (tcbSchedAction (Z := Unit) tcbSchedEnqueue t) :=
  rd_tsa_p _ t σ fun q u hu => (q1_enq t q u hu).imp id fun e => ⟨e, hR⟩

theorem rd_append_p (t : ObjRef) (σ : State Unit) (hR : RdyT σ t) :
    IKp Rdy σ (tcbSchedAction (Z := Unit) tcbSchedAppend t) :=
  rd_tsa_p _ t σ fun q u hu => (q1_app t q u hu).imp id fun e => ⟨e, hR⟩

/-- A TCB write at an `RdyT` thread keeping its binding (any state / fault). -/
theorem rdy_upd_r {σ : State Unit} (h : Rdy σ) (p : ObjRef) (x y : Tcb) (hx : σ.kheap p = some (.tcb x))
    (hy : y.tcbSchedContext = x.tcbSchedContext) (hR : RdyT σ p) :
    Rdy { σ with kheap := Function.update σ.kheap p (some (.tcb y)) } := by
  set σ' : State Unit := { σ with kheap := Function.update σ.kheap p (some (.tcb y)) }
  have hk : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q := fun q hq => by simp [σ', hq]
  have hp : σ'.kheap p = some (.tcb y) := by simp [σ']
  have F : ∀ {t}, RdyT σ t → RdyT σ' t := by
    intro t ⟨x0, c, y0, n, hx0, hc, hy0, h1, h2⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    by_cases e : t = p
    · subst e
      rw [hx] at hx0; cases hx0
      exact ⟨y, c, y0, n, hp, by rw [hy]; exact hc, by rw [hk c hcp]; exact hy0, h1, h2⟩
    · exact ⟨x0, c, y0, n, by rw [hk t e]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1, h2⟩
  have G : ∀ {t}, ActB σ t → ActB σ' t := by
    intro t ⟨x0, c, y0, n, hx0, hc, hy0, h1⟩
    have hcp : c ≠ p := by rintro rfl; rw [hx] at hy0; cases hy0
    by_cases e : t = p
    · subst e
      rw [hx] at hx0; cases hx0
      exact ⟨y, c, y0, n, hp, by rw [hy]; exact hc, by rw [hk c hcp]; exact hy0, h1⟩
    · exact ⟨x0, c, y0, n, by rw [hk t e]; exact hx0, hc, by rw [hk c hcp]; exact hy0, h1⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun d q t hm => F (h1 d q t hm), fun t e => F (h2 t e), fun t x' c hx' hb hc => ?_,
    fun q z n hz hz' => ?_, fun t hm => G (h5 t hm), fun z m hz => ?_⟩
  rotate_right
  · have e : σ.idleSc ≠ p := by rintro e; rw [← e] at hp; change σ'.kheap σ.idleSc = _ at hz; rw [hp] at hz; cases hz
    change σ'.kheap σ.idleSc = _ at hz; rw [hk _ e] at hz; exact h6 z m hz
  · by_cases e : t = p
    · subst e; exact F hR
    · rw [hk t e] at hx'; exact F (h3 t x' c hx' hb hc)
  · by_cases e : q = p
    · subst e; rw [hp] at hz; cases hz
    · rw [hk q e] at hz; exact h4 q z n hz hz'

theorem rd_threadSet_r (f : Tcb → Tcb) (t : ObjRef) (σ : State Unit)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (hR : RdyT σ t) :
    IKp Rdy σ (threadSet (Z := Unit) f t) := by
  unfold threadSet
  intro hσ r ⟨z, hz, hr⟩
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some x =>
    rw [e] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    unfold setObject at hr
    obtain ⟨y, hy, hr⟩ := hr
    obtain ⟨hk, hs⟩ := mem_getObject hy
    obtain ⟨y1, y2⟩ := y
    simp only at hk hs; subst hs
    obtain ⟨z, ⟨-, rfl⟩, hr⟩ := hr
    obtain ⟨w, hw, hr⟩ := hr
    rw [Set.mem_singleton_iff.1 hw] at hr
    rw [Set.mem_singleton_iff.1 hr]
    exact rdy_upd_r hσ t x (f x) (getTcb_kheap e) (hf x) hR

/-- **`set_thread_state`** of a thread `RdyT` at this state (a blocked state
included: l4v `released_ipc_queues` for a thread blocking with a released SC). -/
theorem rd_setThreadState_r (t : ObjRef) (ts : ThreadState) (σ : State Unit) (hR : RdyT σ t) :
    IKp Rdy σ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  exact ikp_bind (rd_threadSet_r _ t σ (fun _ => rfl) hR) fun _ => rd_setThreadStateAct t

end

end Fl4Proofs.P3.SInvR
