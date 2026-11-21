/-
P3 (DESIGN.md §9), invariant line G1 (ctq8): **the budget path carries the
event bundle** (KENTRY-PLAN ctq7 handoff 1; spec side only, outside the JAtZ
cone).

* `BC s`: the current SC is bound to the current thread only (what
  `end_timeslice`'s `postpone cur_sc` needs; ctq7's `hB`).
* `BF H C S R`: the refill part of `charge_budget` (`refill_reset_rr` /
  `refill_budget_check` / the consumed-time update) keeps the current thread,
  the current SC, the release queue and every object except SCs, whose
  `sc_tcb` and activeness (`sc_refill_max`) are kept (`bf_auto`, one leaf:
  `updateSchedContext` with such an update). Hence `BC` and `schedulable ct`
  survive the refill ops (`bc_of_bf`, `sched_of_bf`).
* **`eb_chargeBudget_p (hB : schedulable ct σ → BC σ) (hN : NQ [] σ) : HKp
  (EB true) (EB false) σ (charge_budget c cto)`**: the refill part keeps `EB
  true`; the tail (`eb_chargeTail_p`) runs only when ct is schedulable, then
  ct is runnable (nq3's `NQ [ct]` by `nq_consR`) and `BC` holds.
* **`eb_checkBudget_p`**: every outcome `(r, s)` of `check_budget` has `EB r
  s` (the budget is sufficient: state kept; else charged, `false`);
  **`eb_checkBudgetRestart_p`** (the `Restart` write is runnable);
  **`eb_handleYield_p`**.
* Interrupts: `eb_handleInterrupt_p` (the IRQ signal: ctq7's
  `eb_sendSignal_p` with nq1's NtfnQB and the idle thread's state at the
  start), `eb_maybeHandleInterrupt_p`, `ebx_maybeHandleInterrupt : IK (EBX N
  S b)` with `EBX := EB false ∧ NQ [] ∧ VI N S b` (nq3 / vi2 lemmas).
* **`ebx_preemptionPath_p : HKp (EB true) (EBX N S b) σ preemption_path`**
  given `hB`, `NQ []` and `VI N S b` at σ: the schedulable arm is
  `check_budget`; the other arm charges only a non-schedulable ct, so `hB` is
  vacuous there.
-/
import Fl4Proofs.P3.SpecInvCqE4
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The binding of the current SC -/

/-- The current SC is bound to the current thread only. -/
abbrev BC (s : State Unit) : Prop :=
  ∀ y n t, s.kheap s.curSc = some (.schedContext y n) → y.scTcb = some t → t = s.curThread

/-- An SC update keeping the binding and the activeness. -/
abbrev SCo (y y' : SchedContext) : Prop := y'.scTcb = y.scTcb ∧ scActive y' = scActive y

/-- An object kept, or an SC changed as `SCo`. -/
def KOb (o o' : Option KernelObject) : Prop :=
  o' = o ∨ ∃ y y' n, o = some (.schedContext y n) ∧ o' = some (.schedContext y' n) ∧ SCo y y'

/-- **The budget-path frame.** -/
def BF (H : ObjRef → Option KernelObject) (C S : ObjRef) (R : List ObjRef) (s : State Unit) : Prop :=
  s.curThread = C ∧ s.curSc = S ∧ s.releaseQueue = R ∧ ∀ p, KOb (H p) (s.kheap p)

theorem bf_refl (σ : State Unit) : BF σ.kheap σ.curThread σ.curSc σ.releaseQueue σ :=
  ⟨rfl, rfl, rfl, fun _ => Or.inl rfl⟩

variable {H : ObjRef → Option KernelObject} {C S : ObjRef} {R : List ObjRef}

theorem bf_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, SCo y (f y)) :
    IK (BF H C S R) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ y hy
  unfold updateSchedContext at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := mem_getObject hz
  obtain ⟨o, z2⟩ := z
  simp only at hk hs; subst hs
  dsimp only at hy
  split at hy
  · rename_i sc n
    rw [cq6_setObject hy]
    obtain ⟨e1, e2, e3, e4⟩ := hσ
    refine ⟨e1, e2, e3, fun q => ?_⟩
    dsimp only
    rw [Function.update_apply]
    split
    · rename_i hq
      rw [hq]
      have h0 := e4 p
      rw [hk] at h0
      right
      rcases h0 with e | ⟨y0, y1, n0, e0, e1', h1⟩
      · exact ⟨sc, f sc, n, e.symm, rfl, hf sc⟩
      · cases e1'
        exact ⟨_, _, _, e0, rfl, (hf _).1.trans h1.1, (hf _).2.trans h1.2⟩
    · exact e4 q
  · exact hy.elim

macro "bf_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine bf_updateSchedContext _ _ ?_); exact fun _ => ⟨rfl, rfl⟩)
  | ik_step0 | ik_unfold | (unfold NonDet.when)))

theorem bc_of_bf {σ s : State Unit} (hB : BC σ) (hF : BF σ.kheap σ.curThread σ.curSc σ.releaseQueue s) : BC s := by
  obtain ⟨e1, e2, -, e4⟩ := hF
  intro y n t hk ht
  rw [e2] at hk
  rw [e1]
  rcases e4 σ.curSc with e | ⟨y0, y1, n0, e0, e1', h1⟩
  · rw [hk] at e
    exact hB y n t e.symm ht
  · rw [hk] at e1'
    cases e1'
    exact hB _ _ t e0 (by rw [← h1.1]; exact ht)

theorem sched_of_bf {σ s : State Unit} (hF : BF σ.kheap σ.curThread σ.curSc σ.releaseQueue s) :
    schedulable s.curThread s = schedulable σ.curThread σ := by
  obtain ⟨e1, -, e3, e4⟩ := hF
  rw [e1]
  refine Sched.schedulable_congr ?_ (fun p => ?_) e3
  · rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq]
    rcases e4 σ.curThread with e | ⟨y0, y1, n0, e0, e1', -⟩
    · rw [e]
    · rw [e0, e1']
  · rw [Sched.scsOf_eq, Sched.scsOf_eq]
    rcases e4 p with e | ⟨y0, y1, n0, e0, e1', h1⟩
    · rw [e]
    · rw [e0, e1']
      exact congrArg some h1.2

/-! ## `charge_budget` -/

theorem eb_any {s : State Unit} (b : Bool) (h : EB true s) : EB b s := by
  cases b
  · exact eb_weak h
  · exact h

theorem rn_nq {ts : ThreadState} (h : runnable ts = true) : ¬ isBoN ts ∧ epBlocked ts = none := by
  revert h; cases ts <;> simp [runnable, isBoN, epBlocked]

/-- **`charge_budget`** (module docstring). -/
theorem eb_chargeBudget_p (consumed : Ticks) (cto : Bool) (σ : State Unit)
    (hB : schedulable σ.curThread σ = true → BC σ) (hN : NQ [] σ) :
    HKp (EB true) (EB false) σ (chargeBudget (Z := Unit) consumed cto) := by
  intro hσ y hy
  unfold chargeBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨z, hz, hy⟩ := hy
  have hE3 : EB true z.2 := by
    refine (?_ : EBK true _) σ hσ z hz
    eb_auto
  have hN3 : NQ [] z.2 := by
    refine (?_ : NQK [] _) σ hN z hz
    nq_auto
  have hF3 : BF σ.kheap σ.curThread σ.curSc σ.releaseQueue z.2 := by
    refine (?_ : IK (BF σ.kheap σ.curThread σ.curSc σ.releaseQueue) _) σ (bf_refl σ) z hz
    bf_auto
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨w5, h5, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h5] at hy
  obtain ⟨w6, h6, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h6] at hy
  try dsimp only at hy
  by_cases hs : schedulable (Z := Unit) z.2.curThread { z.2 with consumedTime := 0 } = true
  · have hs' : schedulable z.2.curThread z.2 = true := hs
    have hBs : BC z.2 := bc_of_bf (hB (by rw [← sched_of_bf hF3]; exact hs')) hF3
    obtain ⟨x, hx, hr⟩ := schedulable_rn hs'
    have hN4 : NQ [z.2.curThread] z.2 := nq_consR hN3 hx (rn_nq hr).1 (rn_nq hr).2
    exact eb_chargeTail_p (K := [z.2.curThread]) cto { z.2 with consumedTime := 0 } hBs hN4
      (List.mem_singleton_self _) hE3 y hy
  · unfold NonDet.when at hy
    rw [if_neg hs] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact eb_weak hE3

/-! ## `check_budget`, `check_budget_restart`, `handle_yield` -/

/-- **`check_budget`**: `EB r` after an outcome `r`. -/
theorem eb_checkBudget_p (σ : State Unit) (hB : schedulable σ.curThread σ = true → BC σ) (hN : NQ [] σ) :
    EB true σ → ∀ y, y ∈ (checkBudget (Z := Unit) σ).1 → EB y.1 y.2 := by
  intro hσ y hy
  unfold checkBudget at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  obtain ⟨y3, h3, hy⟩ := hy
  have e3 : y3.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
  obtain ⟨r, s3⟩ := y3
  simp only at e3; subst s3
  try dsimp only at hy
  split at hy
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 h4] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact eb_any _ hσ
  · obtain ⟨y4, h4, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 h4] at hy
    obtain ⟨y5, h5, hy⟩ := hy
    have := eb_chargeBudget_p _ true σ hB hN hσ y5 h5
    rw [Set.mem_singleton_iff.1 hy]
    exact this

/-- **`check_budget_restart`**: `EB r` after an outcome `r`. -/
theorem eb_checkBudgetRestart_p (σ : State Unit) (hB : schedulable σ.curThread σ = true → BC σ)
    (hN : NQ [] σ) : EB true σ → ∀ y, y ∈ (checkBudgetRestart (Z := Unit) σ).1 → EB y.1 y.2 := by
  intro hσ y hy
  unfold checkBudgetRestart at hy
  obtain ⟨z, hz, hy⟩ := hy
  have h1 := eb_checkBudget_p σ hB hN hσ z hz
  obtain ⟨w, hw, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hw] at hy
  obtain ⟨v, hv, hy⟩ := hy
  have ev : v.2 = z.2 := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hv
  obtain ⟨u, hu, hy⟩ := hy
  have h2 : EB z.1 u.2 :=
    (ik_when _ (eb_setThreadState_r (k := z.1) _ _ rfl)) v.2 (by rw [ev]; exact h1) u hu
  rw [Set.mem_singleton_iff.1 hy]
  exact h2

/-- **`handle_yield`**. -/
theorem eb_handleYield_p (σ : State Unit) (hB : schedulable σ.curThread σ = true → BC σ) (hN : NQ [] σ) :
    HKp (EB true) (EB false) σ (handleYield (Z := Unit)) := by
  intro hσ y hy
  unfold handleYield at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have e2 : y2.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h2
  obtain ⟨sc, s2⟩ := y2
  simp only at e2; subst s2
  obtain ⟨y3, h3, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h3] at hy
  obtain ⟨y4, h4, hy⟩ := hy
  have e4 : y4.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h4
  obtain ⟨hd, s4⟩ := y4
  simp only at e4; subst s4
  obtain ⟨y5, h5, hy⟩ := hy
  have h5' := eb_chargeBudget_p _ false σ hB hN hσ y5 h5
  refine (?_ : EBK false _) y5.2 h5' y hy
  eb_auto

/-! ## Interrupts -/

/-- The idle thread is in its idle state. -/
abbrev IdS (s : State Unit) : Prop := ∀ x, s.kheap s.idleThread = some (.tcb x) → x.tcbState = .idleThreadState

theorem eb_handleInterrupt_p (irq : Irq) (σ : State Unit) (hN : NtfnQB σ) (hI : IdS σ) :
    IKp (EB false) σ (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt
  split
  · exact ikp_of_ik (by eb_auto) σ
  · refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun st => ?_
    try dsimp only
    split
    · refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun slot => ?_
      refine ikp_keep (fun y hy => cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun cap => ?_
      refine ikp_bind (ikp_when _ fun _ => eb_sendSignal_p _ _ σ hN hI (fun e => by cases e)) fun _ => ?_
      eb_auto
    · exact ikp_of_ik (by eb_auto) σ
    · exact ikp_of_ik (by eb_auto) σ
    · exact ikp_of_ik (by eb_auto) σ

theorem eb_maybeHandleInterrupt_p (k : Bool) (σ : State Unit) (hN : NtfnQB σ) (hI : IdS σ) :
    IKp (EB false) σ (maybeHandleInterrupt (Z := Unit) k) := by
  unfold maybeHandleInterrupt
  intro hE y ⟨z, hz, hy⟩
  have hz1 := (ik_doMachineOp (P := fun s => EB false s ∧ NtfnQB s ∧ IdS s) (fun _ _ h => h) _) σ ⟨hE, hN, hI⟩ z hz
  cases hz2 : z.1 with
  | none =>
    rw [hz2] at hy
    exact (show EBK false (handleSpuriousIrq (Z := Unit)) by eb_auto) z.2 hz1.1 y hy
  | some irq =>
    rw [hz2] at hy
    exact eb_handleInterrupt_p _ z.2 hz1.2.1 hz1.2.2 hz1.1 y hy

/-- The event bundle after a charge, with nq3's and vi2's carried facts. -/
abbrev EBX (N S : ObjRef) (b : Bool) (s : State Unit) : Prop := EB false s ∧ NQ [] s ∧ SInvI.VI N S b s

theorem ids_of_vi {N S : ObjRef} {b : Bool} {s : State Unit} (h : SInvI.VI N S b s) : IdS s := fun x hx => by
  obtain ⟨y0, hy0, hs, -⟩ := SInvI.vi_idle h
  rw [hy0] at hx; cases hx; exact hs

theorem ntfnQB_of_nq {K : List ObjRef} {s : State Unit} (h : NQ K s) : NtfnQB s := by
  unfold NQ at h; exact h.1.1

theorem ebx_maybeHandleInterrupt (N S : ObjRef) (b k : Bool) : IK (EBX N S b) (maybeHandleInterrupt (Z := Unit) k) :=
  fun σ h y hy => ⟨eb_maybeHandleInterrupt_p k σ (ntfnQB_of_nq h.2.1) (ids_of_vi h.2.2) h.1 y hy,
    nq_maybeHandleInterrupt (Kq := []) k σ h.2.1 y hy, SInvI.vi_maybeHandleInterrupt k σ h.2.2 y hy⟩

/-! ## `preemption_path` -/

/-- **`preemption_path`** (module docstring). -/
theorem ebx_preemptionPath_p (N S : ObjRef) (b : Bool) (σ : State Unit)
    (hB : schedulable σ.curThread σ = true → BC σ) (hN : NQ [] σ) (hV : SInvI.VI N S b σ) :
    HKp (EB true) (EBX N S b) σ (preemptionPath (Z := Unit)) := by
  intro hE y hy
  unfold preemptionPath at hy
  obtain ⟨y1, h1, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h1] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 h2] at hy
  try dsimp only at hy
  split at hy
  · obtain ⟨w, hw, hy⟩ := hy
    exact ebx_maybeHandleInterrupt N S b true w.2 ⟨eb_weak (eb_checkBudget_p σ hB hN hE w hw),
      nq_checkBudget (K := []) σ hN w hw, SInvI.vi_checkBudget σ hV w hw⟩ y hy
  · rename_i hs
    obtain ⟨w1, hw1, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hw1] at hy
    obtain ⟨w2, hw2, hy⟩ := hy
    have e2 : w2.2 = σ := cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hw2
    obtain ⟨act, s2⟩ := w2
    simp only at e2; subst s2
    try dsimp only at hy
    split at hy
    · obtain ⟨w3, hw3, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hw3] at hy
      obtain ⟨z, hz, hy⟩ := hy
      exact ebx_maybeHandleInterrupt N S b true z.2 ⟨eb_chargeBudget_p _ _ σ (fun h => absurd h hs) hN hE z hz,
        nq_chargeBudget (K := []) _ _ σ hN z hz, SInvI.vi_chargeBudget _ _ σ hV z hz⟩ y hy
    · obtain ⟨z, hz, hy⟩ := hy
      rw [Set.mem_singleton_iff.1 hz] at hy
      try dsimp only at hy
      exact ebx_maybeHandleInterrupt N S b true { σ with consumedTime := 0 } ⟨eb_weak hE, hN, hV⟩ y hy

end

end Fl4Proofs.P3.SInvQ
