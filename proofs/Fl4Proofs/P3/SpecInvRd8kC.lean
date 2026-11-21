/-
P3 (DESIGN.md §9), invariant line G1 (rd8k): **the SC bind's decode fact
for `BlockedScActive`** (spec side only, outside the JAtZ cone; KENTRY-PLAN
rd8i handoff 3).

rd8c's `BindRel` speaks of `BlkR` (send / receive / notification blocked); the
decode's check `¬ (ipc_queued_thread_state ∧ ¬ sc_released)` covers every
ipc-queued state, BlockedOnReply included, which is what rd8i's
`ba_schedContextBindTcb_p` (`NotQ t ∨ PA p`) needs.

* **`BQ σ p t`**: `t`, if an ipc-queued TCB, has `p` released (`sc_released`
  = active ∧ head ready); `nqpa_of_bq`.
* `RqS` / `RqD`, `okp_decodeSchedContextBindQ`,
  `okp_decodeSchedContextInvocationQ`, **`okp_fl4DecodeRqD`** (rd8c's
  `okp_fl4DecodeRdD` pattern; sb2's `RNE` for the released read).
* `bq_bk` (along rd8c's `BK` view), `bq_setThreadState` (a write to a
  non-ipc-queued state), **`bq_perform`**: a decoded SC-to-TCB bind satisfies
  `BQ` at the perform (after `set_thread_state ct Restart`).
-/
import Fl4Proofs.P3.SpecInvRd8kB
import Fl4Proofs.P3.SpecInvRd8cD
open Classical

namespace Fl4Proofs.P3.SInvR.B8k
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvB Fl4Proofs.P3.SInvE
  Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i

noncomputable section

set_option maxHeartbeats 1000000

/-- `t`, if an ipc-queued TCB, has `p` released. -/
def BQ (σ : State Unit) (p t : ObjRef) : Prop :=
  ∀ x, σ.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = true →
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ scReleased σ.curTime y = true

theorem nqpa_of_bq {σ : State Unit} {p t : ObjRef} (h : BQ σ p t) : NotQ t σ ∨ PA p σ := by
  by_cases hq : ∃ x, σ.kheap t = some (.tcb x) ∧ ipcQueuedThreadState x.tcbState = true
  · obtain ⟨x, hx, hq⟩ := hq
    obtain ⟨y, n, hy, hr⟩ := h x hx hq
    refine Or.inr ⟨y, n, hy, ?_⟩
    simp only [scReleased, Bool.and_eq_true] at hr
    exact hr.1
  · refine Or.inl fun x hx => ?_
    cases e : ipcQueuedThreadState x.tcbState
    · rfl
    · exact absurd ⟨x, hx, e⟩ hq

def RqS (σ : State Unit) : SchedContextInvocation → Prop
  | .invokeSchedContextBind p (.threadCap t) => BQ σ p t
  | _ => True

def RqD (σ : State Unit) : Fl4Invocation → Prop
  | .invokeSchedContext iv => RqS σ iv
  | _ => True

theorem okp_decodeSchedContextBindQ (σ : State Unit) (hN : SInvB.RNE σ) (scPtr : ObjRef) (excaps : List Cap) :
    OkP σ (RqS σ) (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind
  refine okp_whenE_bind fun _ => okp_returnOk_bind ?_
  refine okp_liftE_bind (Q := fun sc => ∃ n, σ.kheap scPtr = some (.schedContext sc n))
    (fun y hy => SInvQ.cq5_mem_getSc hy) fun sc ⟨n, hsc⟩ => ?_
  (try dsimp only)
  split
  · rename_i tcbPtr heq
    refine okp_whenE_bind fun h1 => ?_
    refine okp_liftE_bind (Q := fun o => ∃ x, σ.kheap tcbPtr = some (.tcb x) ∧ o = x.tcbSchedContext)
      (fun y hy => ?_) fun o ⟨x, hx, ho⟩ => ?_
    · obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet hy; exact ⟨rfl, x, hx, rfl⟩
    refine okp_whenE_bind fun h2 => ?_
    refine okp_liftE_bind (Q := fun st => st = x.tcbState) (fun y hy => ?_) fun st hst => ?_
    · obtain ⟨x', hx', rfl⟩ := SInvQ.q1_mem_threadGet hy; rw [hx] at hx'; cases hx'; exact ⟨rfl, rfl⟩
    refine okp_liftE_bind (Q := fun r => r = scReleased σ.curTime sc) (fun y hy => ?_) fun r hr => ?_
    · rw [Sched.getScReleased_eq hsc (fun ha => hN scPtr sc n hsc (Or.inr ha))] at hy
      obtain rfl := Set.mem_singleton_iff.1 hy; exact ⟨rfl, rfl⟩
    refine okp_whenE_bind fun h3 => okp_returnOk ?_
    rw [heq]
    show BQ σ scPtr tcbPtr
    intro x' hx' hq
    rw [hx] at hx'; cases hx'
    refine ⟨sc, n, hsc, ?_⟩
    subst hst; subst hr
    by_contra hn
    exact h3 ⟨hq, hn⟩
  · rename_i ntfnPtr bd rs heq
    rw [heq]
    refine okp_of_okA ?_
    okA_auto
  · exact okp_throw_bind _

theorem okp_decodeSchedContextInvocationQ (σ : State Unit) (hN : SInvB.RNE σ) (label : Data) (scPtr : ObjRef)
    (excaps : List Cap) : OkP σ (RqS σ) (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation
  split
  · exact okp_returnOk trivial
  · exact okp_decodeSchedContextBindQ σ hN scPtr excaps
  all_goals refine okp_of_okA ?_
  all_goals first
    | exact okA_throw _
    | (unfold decodeSchedContextUnbindObject; okA_auto)
    | (unfold decodeSchedContextYieldTo; okA_auto)
    | okA_auto

set_option maxHeartbeats 4000000 in
/-- **Every decoded invocation satisfies `RqD` of the decode's state.** -/
theorem okp_fl4DecodeRqD (σ : State Unit) (hN : SInvB.RNE σ) (fp : Bool) (label : Data) (args : List Data)
    (ci : CapRef) (sl : CslotPtr) (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkP σ (RqD σ) (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | schedContextCap sc sz =>
    unfold fl4DecodeInvocation
    exact okp_ite (okp_throw _) (okp_liftME (okp_decodeSchedContextInvocationQ σ hN label sc _))
  | _ =>
    unfold fl4DecodeInvocation
    refine okp_of_okA ?_
    repeat' (first
      | exact okA_throw _ | exact okA_returnOk trivial
      | (exact okA_liftME (okA_triv fun _ => trivial))
      | (refine okA_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

theorem bq_bk {σ σ' : State Unit} {p t : ObjRef} (h : BKv σ' = BKv σ) (hB : BQ σ p t) : BQ σ' p t := by
  have h' := h
  unfold BKv at h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hT, hS, hC⟩ := h'
  intro x' hx' hq
  have e := congrFun hT t
  try simp only at e
  rw [hx'] at e
  obtain ⟨x, hx, e1, -, -⟩ := tcbV_some e.symm
  obtain ⟨y, n, hy, hr⟩ := hB x hx (by rw [e1]; exact hq)
  exact ⟨y, n, scAt_iff.1 (by rw [hS]; exact scAt_iff.2 hy), by rw [hC]; exact hr⟩

theorem bq_setThreadState {σ : State Unit} {p t : ObjRef} (hB : BQ σ p t) (c : ObjRef) (ts : ThreadState)
    (hts : ipcQueuedThreadState ts = false) {y : Unit × State Unit}
    (hy : y ∈ (setThreadState (Z := Unit) c ts σ).1) : BQ y.2 p t := by
  unfold setThreadState at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨x0, hx0, e⟩ := SInv.mem_threadSet hz
  have k : y.2.kheap = z.2.kheap ∧ y.2.curTime = z.2.curTime :=
    (show IK (fun s => s.kheap = z.2.kheap ∧ s.curTime = z.2.curTime) (setThreadStateAct (Z := Unit) c) from by
      unfold setThreadStateAct setSchedulerAction; repeat' (first | ik_step0 | ik_unfold)) z.2 ⟨rfl, rfl⟩ y hy
  intro x' hx' hq
  rw [k.1, e] at hx'
  change Function.update σ.kheap c _ t = _ at hx'
  by_cases et : t = c
  · subst et; rw [Function.update_self] at hx'; cases hx'
    rw [hts] at hq; cases hq
  · rw [Function.update_of_ne et] at hx'
    obtain ⟨y0, n, hy0, hr⟩ := hB x' hx' hq
    have hpc : p ≠ c := fun h => by rw [h, hx0] at hy0; cases hy0
    refine ⟨y0, n, ?_, ?_⟩
    · rw [k.1, e]; change Function.update σ.kheap c _ p = _; rw [Function.update_of_ne hpc]; exact hy0
    · rw [k.2, e]; exact hr

/-- **A decoded SC-to-TCB bind satisfies `BQ` at the perform** (after the shell's
`set_thread_state ct Restart`); `RNE` (sb2's `ScInv`) at the decode's state. -/
theorem bq_perform {σ : State Unit} (hN : SInvB.RNE σ) {fp : Bool} {label : Data} {args : List Data}
    {ci : CapRef} {sl : CslotPtr} {cap : Cap} {ex : List (Cap × CslotPtr)} {buf : Option ObjRef}
    {p t : ObjRef} {s : State Unit}
    (h : ((.ok (.invokeSchedContext (.invokeSchedContextBind p (.threadCap t))), s) :
        Except SyscallError Fl4Invocation × State Unit) ∈
      ((fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf).run σ).1)
    (c : ObjRef) {y : Unit × State Unit} (hy : y ∈ (setThreadState (Z := Unit) c .restart s).1) :
    BQ y.2 p t := by
  have hD : BQ σ p t := okp_fl4DecodeRqD σ hN fp label args ci sl cap ex buf _ s h
  have hV : BKv s = BKv σ := bk_fl4DecodeInvocation (V := BKv σ) fp label args ci sl cap ex buf σ rfl _ h
  exact bq_setThreadState (bq_bk hV hD) c .restart rfl hy

end

end Fl4Proofs.P3.SInvR.B8k
