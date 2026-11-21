/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd6): **`end_timeslice` and
`charge_budget`'s tail** (spec side only, outside the `JAtZ` cone; KENTRY-PLAN
rd5 handoff 2; ctq7's `et_endTimeslice_p` is the template).

* **`rd_endTimeslice_p`**: `Rdy` across `end_timeslice c` from a state where
  the current SC is an active SC, the current thread a TCB bound to it
  (ctq5's `kentry_curScT`), sb2's `ScFwd` holds, and the timeout arm keeps
  `Rdy` (`hTO`, discharged by `rd_handleTimeout_p` for the timeout fault the
  arm raises). Non-timeout arms: the append of the current thread, `RdyT`
  from the head `end_timeslice` itself read ready (`rd_append_p`), or
  `postpone cur_sc` (its bound thread `ActB` by `ScFwd` and the active SC:
  `rd_postpone_fwd`).
* **`rd_cbTail`**: `charge_budget`'s `when (schedulable ct)` tail keeps `Rdy`,
  and when it runs (`schedulable ct`) it ends at `choose_new_thread` (the
  reschedule): the overrun case of rd4's `hOS0`, `action ≠ resume`.
-/
import Fl4Proofs.P3.SpecInvRdH
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.Notif

noncomputable section

set_option maxHeartbeats 1000000

/-- **`end_timeslice`** (module docstring). -/
theorem rd_endTimeslice_p (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb}
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hF : SInvB.ScFwd s)
    (hTO : ∀ b, IKp Rdy s (handleTimeout (Z := Unit) s.curThread (.timeout b))) :
    IKp Rdy s (endTimeslice (Z := Unit) c) := by
  unfold endTimeslice
  refine ikp_gets_bind ?_
  refine ikp_keep (fun y hy => SInvQ.cq5_ro (fun _ => by unfold isRoundRobin; repeat' (first | ik_step0 | ik_unfold))
    hy) fun rr => ?_
  refine ikp_gets_bind ?_
  refine ikp_keep (fun y hy => by obtain ⟨_, -, rfl⟩ := SInvQ.q1_mem_threadGet hy; rfl) fun ts => ?_
  dsimp only
  split
  all_goals refine ikp_keep (fun y hy => ?_) fun valid => ?_
  all_goals first
    | (rw [Set.mem_singleton_iff.1 hy]; done)
    | (exact SInvQ.cq5_ro (fun _ => by unfold isValidTimeoutHandler; repeat' (first | ik_step0 | ik_unfold)) hy)
    | skip
  all_goals
    split
    · refine ikp_keep (fun y hy => SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun sc => ?_
      exact hTO _
    · intro hσ r ⟨w, hw, hr⟩
      obtain rfl := mem_getScRefillReady hk hw
      obtain ⟨w2, hw2, hr⟩ := hr
      obtain rfl := mem_getScRefillSufficient hk 0 hw2
      dsimp only at hr
      split at hr
      · rename_i hc
        exact rd_append_p _ s ⟨xt, _, z, n, hct, hb, hk, ha, hc.1⟩ hσ r hr
      · exact rd_postpone_fwd _ s hF (fun y m hy => by rw [hk] at hy; cases hy; exact ha) hσ r hr

/-- **`charge_budget`'s tail** (module docstring). -/
theorem rd_cbTail (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb} (hR : Rdy s)
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hF : SInvB.ScFwd s)
    (hTO : ∀ b, IKp Rdy s (handleTimeout (Z := Unit) s.curThread (.timeout b)))
    {r : Unit × State Unit} (hr : r ∈ (cbTail c s).1) :
    Rdy r.2 ∧ (schedulable s.curThread s = true → r.2.schedulerAction = .chooseNewThread) := by
  unfold cbTail at hr
  rw [nd_gets_bind, nd_gets_bind] at hr
  by_cases hs : schedulable s.curThread s = true
  · rw [NonDet.when, if_pos hs] at hr
    obtain ⟨y1, hy1, hr⟩ := hr
    obtain ⟨y2, hy2, hr⟩ := hr
    have h1 := rd_endTimeslice_p c s hk ha hct hb hF hTO hR y1 hy1
    have h2 := rd_rescheduleRequired y1.2 h1 y2 hy2
    have h3 := SInvQ.rescheduleRequired_cn y1.2 y2 hy2
    obtain rfl := Set.mem_singleton_iff.1 hr
    exact ⟨rdy_congr h2 rfl rfl rfl rfl rfl (fun _ h => h), fun _ => h3⟩
  · rw [NonDet.when, if_neg hs] at hr
    obtain rfl : r = ((), s) := hr
    exact ⟨hR, fun h => absurd h hs⟩

end

end Fl4Proofs.P3.SInvR
