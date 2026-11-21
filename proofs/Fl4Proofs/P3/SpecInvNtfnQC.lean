/-
P3 (DESIGN.md §9), invariant line G1 (nq1): **the current-thread frame**
`CTK c m`: every run of `m` from a state whose current thread is `c` ends in
one whose current thread is `c` (spec side only). Only the scheduler writes
`cur_thread`, so every other spec function of the syscall entry is a frame
(SpecInvNtfnQC1..C4, generated). The NtfnQB shell uses it where the spec
re-reads the current thread (`perform_invocation`'s sender, `handle_recv`
after the ReplyRecv send phase, the events' fault handlers).
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

/-- The current thread stays `c`. -/
abbrev CTK {α : Type} (c : ObjRef) (m : NonDet (State Unit) α) : Prop := IK (fun s => s.curThread = c) m
abbrev CTKE {ε α : Type} (c : ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (fun s => s.curThread = c) m

syntax "ct_leaf" : tactic
macro_rules | `(tactic| ct_leaf) => `(tactic| fail "no ct_leaf")

macro "ct_auto" : tactic => `(tactic| repeat' (first | ct_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem ct_doMachineOp {c : ObjRef} {α : Type} (mop : NonDet MachineState α) : CTK c (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

theorem ct_doExtendedOp {c : ObjRef} (eop : DetExtMonad Unit) : CTK c (doExtendedOp (Z := Unit) eop) :=
  ik_doExtendedOp (fun _ _ h => h) _

macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doMachineOp _)
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doExtendedOp _)
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ik_getObject _)

end

end Fl4Proofs.P3.SInv
