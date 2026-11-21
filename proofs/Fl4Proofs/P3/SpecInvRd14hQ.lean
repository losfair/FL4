/-
P3 (DESIGN.md §9), invariant line G1 (rd14h, rd14g handoff (1)): **rd14c's
`QT t` (t a TCB in a Restart / Running / Inactive state) as a generated frame
family** over the cone of `cap_delete` / `cap_revoke` / `install_tcb_cap` /
`install_tcb_frame_cap` / `set_mcpriority` / `set_priority` /
`sched_context_bind_tcb` / `sched_context_unbind_tcb` /
`invoke_sched_control_configure_flags` (spec side only).

* `QTK t m := IK (QT t) m`, `QTKE` (the exception monad).
* Why it holds: the cone writes thread states only to Inactive / Restart /
  Running (suspension, cancellation, restart), no TCB is detyped (no
  `delete_objects` / retype in the cone: finalisation only, memory is freed
  only by Untyped), and `set_object` asserts the object type, so a TCB stays a
  TCB.
* Leaves: rd14c's `qt_setThreadState` (a good state) / `qt_threadSet` (a
  state-keeping update) / `qt_setObject` (no TCB written) / `qt_setSimpleKo`,
  rd8d's `TV` writers by `qt_of_tv` (arch / user context, message registers,
  cap slots), rd14g C's `qt_dmo` / `qt_preemptionPoint`, and the existing
  hand lemmas (`qt_cancelIpc`, `qt_suspend`, `qt_restart`,
  `qt_cancelYieldTo`, rd14e's `qt_replyRemove` / `qt_cancelAll*` /
  `qt_fastFinalise` / `qt_capDeleteOne`, rd14g F's `qt_schedContextDonate`);
  the rest generated (SpecInvRd14hQ1, Q2: proofs/scratch/rd14h/mkqt.sh), the
  two least fixed points (`rec_del`, `cap_revoke`) by `ik_lfp`.
-/
import Fl4Proofs.P3.SpecInvRd14gF
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

abbrev QTK {α : Type} (t : ObjRef) (m : NonDet (State Unit) α) : Prop := IK (QT t) m
abbrev QTKE {ε α : Type} (t : ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (QT t) m

variable {Tq : ObjRef}

theorem qth_doExtendedOp (eop : DetExtMonad Unit) : QTK Tq (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) eop

theorem qth_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, (fn v x).tcbState = x.tcbState) : QTK Tq (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact qt_threadSet _ _ _ fun x g => by rw [h]; exact g

syntax "qth_leaf" : tactic
macro_rules | `(tactic| qth_leaf) => `(tactic| fail "no qth_leaf")

/-- The state-keeping `thread_set` leaf, tried before the generated leaves (some of those time out
when tried against a `thread_set` goal). -/
macro "qth_pre" : tactic => `(tactic| ((with_reducible refine qt_threadSet _ _ _ ?_); intro _ h; exact h))

macro "qth_auto" : tactic => `(tactic| repeat' (first | qth_pre | qth_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_dmo _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_doExtendedOp _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| qth_leaf) => `(tactic| ((with_reducible refine qt_setObject _ _ _ ?_); intro _ h; cases h; done))
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_setSimpleKo _ _ _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| ((with_reducible refine qt_threadSet _ _ _ ?_); intro _ h; exact h))
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_of_tv _ fun _ => B8d.tv_archThreadSet _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_of_tv _ fun _ => B8d.tv_asUser _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_of_tv _ fun _ => B8d.tv_setMrs _ _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_of_tv _ fun _ => B8d.tv_setCap _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| ((with_reducible refine qt_setThreadState _ _ _ ?_); first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)))
macro_rules | `(tactic| qth_leaf) => `(tactic| ((with_reducible refine qth_optionUpdateThread _ _ _ ?_); intro _ _; rfl))
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_preemptionPoint _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_cancelIpc _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_cancelYieldTo _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_suspend _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_restart _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_replyRemove _ _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_cancelAllIpc _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_cancelAllSignals _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_fastFinalise _ _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_capDeleteOne _ _)
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qt_schedContextDonate _ _ _)

end

end Fl4Proofs.P3.SInvR.A14h
