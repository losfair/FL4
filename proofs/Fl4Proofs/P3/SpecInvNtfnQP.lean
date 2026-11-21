/-
P3 (DESIGN.md §9), invariant line G1 (nq3): **the threads of `L` stay out of
the IPC-blocked and BlockedOnReply states** across the TCB-cap installs of
`invoke_tcb` (spec side only).

* `pjQ L p x := p ∈ L → epBlocked x.tcbState = none ∧ ¬ isBoR x.tcbState`,
  `PJ L := TP (pjQ L)` (SpecInvFaultTcbsT's pointwise TCB predicates).
* Why: ThreadControlSched's `set_priority` re-inserts a BlockedOnSend /
  BlockedOnReceive target into its endpoint queue; for ReplyRecv /
  NBSendRecv / NBSendWait the current thread (Restart during
  `perform_invocation`) must stay in no queue for the following receive. Its
  `install_tcb_cap` / `set_mcpriority` prefix writes thread states only to
  Inactive / Restart / Running (deletion, cancellation, restart), so `PJ L`
  holds at `set_priority`.
* Leaves: the `tp_*` writers, `pj_setThreadState` (an allowed state); the rest
  generated for the cone of `install_tcb_cap` and `set_mcpriority`
  (SpecInvNtfnQP1, P2: proofs/scratch/nq3/mkpj.sh).
-/
import Fl4Proofs.P3.SpecInvNtfnQ
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- Not IPC-blocked on an endpoint, not BlockedOnReply. -/
abbrev okSt (s : ThreadState) : Prop := epBlocked s = none ∧ ¬ isBoR s

/-- The threads of `L` are in an `okSt` state. -/
abbrev pjQ (L : List ObjRef) (p : ObjRef) (x : Tcb) : Prop := p ∈ L → okSt x.tcbState

abbrev PJ (L : List ObjRef) (σ : State Unit) : Prop := TP (pjQ L) σ

variable {Lp : List ObjRef}

abbrev PJK {α : Type} (L : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (PJ L) m
abbrev PJKE {ε α : Type} (L : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (PJ L) m

theorem pj_noRpl {L : List ObjRef} {σ : State Unit} (h : PJ L σ) : NoRpl L σ :=
  fun u hu x hx => (h u x hx hu).2

theorem pj_epB {L : List ObjRef} {σ : State Unit} (h : PJ L σ) {t : ObjRef} (ht : t ∈ L) {x : Tcb}
    (hx : σ.kheap t = some (.tcb x)) : epBlocked x.tcbState = none :=
  (h t x hx ht).1

/-- The side conditions of the TCB-writer leaves. -/
macro "pj_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (exact ⟨rfl, fun h => h⟩))

syntax "pj_leaf" : tactic
macro_rules | `(tactic| pj_leaf) => `(tactic| fail "no pj_leaf")

macro "pj_auto" : tactic => `(tactic| repeat' (first | pj_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); pj_side))
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- `set_thread_state` to a state outside the IPC-blocked / BlockedOnReply ones. -/
theorem pj_setThreadState (t : ObjRef) (ts : ThreadState) (h : okSt ts) :
    PJK Lp (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun x _ _ => h) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine pj_setThreadState _ _ ?_); pj_side))

theorem pj_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, pjQ Lp t x → pjQ Lp t (fn v x)) : PJK Lp (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| pj_leaf) => `(tactic| ((with_reducible refine pj_optionUpdateThread _ _ _ ?_); pj_side))


end

end Fl4Proofs.P3.SInv
