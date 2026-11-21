/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd3): **`sc_and_timer`:
`Rdy ∧ OffReady` after the exit's SC switch** (spec side only, outside the
`JAtZ` cone; KENTRY-PLAN rd2 handoff 5, the `kentry_offReady` step).

* `KO`: heap, current SC, consumed time and time fixed (`set_next_interrupt`
  writes only the machine state); `offReady_ko`.
* **`rd_scAndTimer`**: from rd1's `sw_out` preconditions at the start of
  `sc_and_timer`, every outcome has `Rdy`, `OffReady` and `cur_sc = p` (the
  current thread's SC).
-/
import Fl4Proofs.P3.SpecInvRdU
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000

/-- Heap, current SC, consumed time and time, fixed. -/
abbrev KO (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) (σ : State Unit) : Prop :=
  σ.kheap = K ∧ σ.curSc = c ∧ σ.consumedTime = u ∧ σ.curTime = T

theorem ko_setNextInterrupt (K : ObjRef → Option KernelObject) (c : ObjRef) (u : Ticks) (T : Time) :
    IK (KO K c u T) (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt
  repeat' (first | ((with_reducible refine ik_doMachineOp ?_ _); intro _ _ h; exact h) | ik_step0 | ik_unfold)

theorem offReady_ko {σ σ' : State Unit} (h : Sched.OffReady σ) (hk : σ'.kheap = σ.kheap)
    (hc : σ'.curSc = σ.curSc) (hu : σ'.consumedTime = σ.consumedTime) (ht : σ'.curTime = σ.curTime) :
    Sched.OffReady σ' := by
  intro y n hy
  rw [hk, hc] at hy
  rw [hu, ht]
  exact h y n hy

/-- **`sc_and_timer`** (module docstring). -/
theorem rd_scAndTimer {σ : State Unit} {x : SchedContext} {n : Nat} {xt : Tcb} {p : ObjRef} {y : SchedContext}
    {m : Nat} (h : Rdy σ) (hk : σ.kheap σ.curSc = some (.schedContext x n))
    (hOS : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ (p = σ.curSc → Sched.OffReady σ)) ∨
      (scActive x = false ∧ p ≠ σ.curSc))
    (hne : scActive x = true → x.scRefills ≠ []) (hct : σ.kheap σ.curThread = some (.tcb xt))
    (hsc : xt.tcbSchedContext = some p) (hp : σ.kheap p = some (.schedContext y m))
    (hnp : p ≠ σ.curSc → y.scRefills ≠ [])
    (hHR : p ≠ σ.curSc → (refillHd y).rTime.toNat ≤ σ.curTime.toNat) (hX : p ≠ σ.curSc → Excl σ p)
    {r : Unit × State Unit} (hr : r ∈ (scAndTimer (Z := Unit) σ).1) :
    Rdy r.2 ∧ Sched.OffReady r.2 ∧ r.2.curSc = p := by
  unfold scAndTimer at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨z1, z2, z3⟩ := sw_out h hk hOS hne hct hsc hp hnp hHR hX hz
  obtain ⟨w, hw, hr⟩ := hr
  rw [Set.mem_singleton_iff.1 hw] at hr
  dsimp only at hr
  by_cases hrt : z.2.reprogramTimer = true
  · rw [NonDet.when, if_pos hrt] at hr
    obtain ⟨v, hv, hr⟩ := hr
    have v1 := rd_setNextInterrupt z.2 z1 v hv
    obtain ⟨e1, e2, e3, e4⟩ := ko_setNextInterrupt _ _ _ _ z.2 ⟨rfl, rfl, rfl, rfl⟩ v hv
    rw [Set.mem_singleton_iff.1 hr]
    exact ⟨rdy_rpt v1 false, offReady_ko z2 e1 e2 e3 e4, e2.trans z3⟩
  · rw [NonDet.when, if_neg hrt] at hr
    rw [Set.mem_singleton_iff.1 hr]
    exact ⟨z1, z2, z3⟩

end

end Fl4Proofs.P3.SInvR
