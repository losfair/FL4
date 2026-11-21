/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the FL4 arch state
through the preemption path keeps `MR`** (`MRKeep`, `MK.*`). ArchKeep's `ARKeep`
/ `AK.*` walk, cloned for an arch predicate that the clock read does NOT keep
(`MR a ms`: XTopJointMachRel's platform relation at a fixed spec machine
state): `MRKeep` is `ARKeep` without its `now` field, and every `MK.*` walk
below goes through no `now` call (the walk fails on one: `mk_call` has no
field for it).

* `MRKeep arI AR` [P]: the state-returning arch operations of the IPC and
  scheduling paths other than the clock (`set_deadline`, `send_reschedule`,
  `remote_stall`, the four lazy-FPU operations, `vcpu_barrier`) keep `AR` at
  every second argument. With `AR := MR`: they change none of the IRQ masks,
  pending lines or clock (l4v: those machine operations are
  `machine_op_lift`s of the underlying machine, outside `irq_masks`,
  `irq_state`, `time_state`, `last_machine_time`). Arch-only (∀ a, no spec
  state). (The model platform satisfies it:
  XTopJointMRPath's `modelArch_mrKeep`.)
* `MK.*`: ArchKeep's `AK.*` walks with `MRKeep`, plus
  `MK.sched_end_timeslice`, `MK.sched_charge_budget`, `MK.sched_check_budget`,
  `MK.syscall_mcs_preemption_point`: the MCS preemption point keeps `AR`.
-/
import Fl4Proofs.P3.ArchKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {A C : Type} (arI : machine.Arch A)

/-- **[P] The state-returning arch operations other than the clock keep `AR`**
(module docstring). -/
structure MRKeep (AR : A → C → Prop) : Prop where
  set_deadline : ∀ a d c, AR a c → arI.set_deadline a d ⦃ a' => AR a' c ⦄
  send_reschedule : ∀ a m c, AR a c → arI.send_reschedule a m ⦃ a' => AR a' c ⦄
  remote_stall : ∀ a cpu c, AR a c → arI.remote_stall a cpu ⦃ a' => AR a' c ⦄
  fpu_flush : ∀ a t c, AR a c → arI.fpu_flush a t ⦃ a' => AR a' c ⦄
  fpu_release : ∀ a t c, AR a c → arI.fpu_release a t ⦃ a' => AR a' c ⦄
  fpu_sanitise : ∀ a t c, AR a c → arI.fpu_sanitise a t ⦃ a' => AR a' c ⦄
  fpu_reload : ∀ a t c, AR a c → arI.fpu_reload a t ⦃ a' => AR a' c ⦄
  vcpu_barrier : ∀ a c, AR a c → arI.vcpu_barrier a ⦃ a' => AR a' c ⦄

end

open Lean Elab Tactic Meta in
/-- ArchKeep's `ak_call` with `MRKeep`'s fields and the `MK.*` lemmas. -/
elab "mk_call" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Aeneas.Std.WP.spec do throwError "mk_call: not a spec"
  let args := target.getAppArgs
  let program := args[args.size - 2]!
  let program ← match ← Lean.Meta.reduceMatcher? program with
    | Lean.Meta.ReduceMatcherResult.reduced e => pure e.headBeta
    | _ => pure program
  let (m, bound) := match Aeneas.Step.getBindArgs? program with
    | some (m, _) => (m, true)
    | none => (program, false)
  let some n := m.getAppFn.constName? | throwError "mk_call: no constant head"
  let hS := mkIdent `hS
  let hA := mkIdent `hA
  let hK := mkIdent `hK
  if n.getPrefix == ``fl4_core.machine.Arch then
    let f := mkIdent (`MRKeep ++ Name.mkSimple n.getString!)
    let k := (m.getAppNumArgs) - 3
    let us : Array (TSyntax `term) := Array.replicate (k + 2) (← `(_))
    unless bound do throwError "mk_call: arch operation in tail position"
    evalTactic (← `(tactic| refine WP.spec_bind ($f $hK $us* (by assumption)) (fun _ _ => ?_)))
  else
    let ak := `Fl4Proofs.P3.MK ++ Name.mkSimple (((n.replacePrefix `fl4_core .anonymous).toString).replace "." "_")
    unless (← getEnv).contains ak do throwError "mk_call: not an arch-threading function"
    let f := mkIdent ak
    if bound then
      evalTactic (← `(tactic| refine WP.spec_bind ($f $hS $hA $hK (by assumption)) (fun _ _ => ?_)))
    else
      evalTactic (← `(tactic| exact $f $hS $hA $hK (by assumption)))

macro "mk_walk" : tactic => `(tactic|
  ((repeat' (first | mk_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> ak_close))

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeep arI AR) {c : C}
include hS hA hK
set_option linter.unusedSectionVars false

theorem MK.debug_configure_single_stepping {s : S} {a : A} {t : obj.Tcb} {bp : Std.U64} {n_instr : Std.U64} {is_reply : Bool} (h : AR a c) :
    debug.configure_single_stepping st arI s a t bp n_instr is_reply ⦃ r => AR r.2.2 c ⦄ := by
  unfold debug.configure_single_stepping; mk_walk

theorem MK.smp_migrate_tcb {s : S} {a : A} {t : obj.Tcb} {cpu : Std.U64} (h : AR a c) :
    smp.migrate_tcb st arI s a t cpu ⦃ r => AR r.2 c ⦄ := by
  unfold smp.migrate_tcb; mk_walk

theorem MK.smp_remote_reschedule {s : S} {a : A} {cpu : Std.U64} (h : AR a c) :
    smp.remote_reschedule st arI s a cpu ⦃ r => AR r.2 c ⦄ := by
  unfold smp.remote_reschedule; mk_walk

theorem MK.smp_remote_tcb_stall {s : S} {a : A} {t : obj.Tcb} (h : AR a c) :
    smp.remote_tcb_stall st arI s a t ⦃ r => AR r.2 c ⦄ := by
  unfold smp.remote_tcb_stall; mk_walk

theorem MK.schedcontext_donate {s : S} {a : A} {sc : obj.Sc} {«to» : obj.Tcb} (h : AR a c) :
    schedcontext.donate st arI s a sc «to» ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.donate; mk_walk

theorem MK.ipc_reply_push {s : S} {a : A} {caller : obj.Tcb} {callee : obj.Tcb} {r : obj.Reply} {can_donate : Bool} (h : AR a c) :
    ipc.reply_push st arI s a caller callee r can_donate ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_push; mk_walk

theorem MK.endpoint_send_ipc {s : S} {a : A} {blocking : Bool} {do_call : Bool} {badge : Std.U64} {can_grant : Bool} {can_grant_reply : Bool} {can_donate : Bool} {thread : obj.Tcb} {ep_ptr : Std.U64} (h : AR a c) :
    endpoint.send_ipc st arI s a blocking do_call badge can_grant can_grant_reply can_donate thread ep_ptr ⦃ r => AR r.2 c ⦄ := by
  unfold endpoint.send_ipc; mk_walk

theorem MK.faults_handle_fault_reply {s : S} {a : A} {receiver : obj.Tcb} {sender : obj.Tcb} (h : AR a c) :
    faults.handle_fault_reply st arI s a receiver sender ⦃ r => AR r.2.2 c ⦄ := by
  unfold faults.handle_fault_reply; mk_walk

theorem MK.faults_send_fault_ipc {s : S} {a : A} {t : obj.Tcb} {handler : capability.Cap} {can_donate : Bool} {f : error.Fault} (h : AR a c) :
    faults.send_fault_ipc st arI s a t handler can_donate f ⦃ r => AR r.2.2 c ⦄ := by
  unfold faults.send_fault_ipc; mk_walk

theorem MK.faults_handle_timeout {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} (h : AR a c) :
    faults.handle_timeout st arI s a t f ⦃ r => AR r.2 c ⦄ := by
  unfold faults.handle_timeout; mk_walk

theorem MK.ipc_cancel_ipc {s : S} {a : A} {t : obj.Tcb} (h : AR a c) :
    ipc.cancel_ipc st arI s a t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.cancel_ipc; mk_walk

theorem MK.ipc_reply_pop {s : S} {a : A} {r : obj.Reply} {t : obj.Tcb} (h : AR a c) :
    ipc.reply_pop st arI s a r t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_pop; mk_walk

theorem MK.ipc_reply_remove {s : S} {a : A} {r : obj.Reply} {t : obj.Tcb} (h : AR a c) :
    ipc.reply_remove st arI s a r t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_remove; mk_walk

theorem MK.ipc_do_reply_transfer {s : S} {a : A} {sender : obj.Tcb} {r : obj.Reply} {grant : Bool} (h : AR a c) :
    ipc.do_reply_transfer st arI s a sender r grant ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.do_reply_transfer; mk_walk

theorem MK.schedcontext_resume {s : S} {a : A} {sc : obj.Sc} (h : AR a c) :
    schedcontext.resume st arI s a sc ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.resume; mk_walk

theorem MK.notification_maybe_donate_sched_context {s : S} {a : A} {t : obj.Tcb} {n : obj.Ntfn} (h : AR a c) :
    notification.maybe_donate_sched_context st arI s a t n ⦃ r => AR r.2 c ⦄ := by
  unfold notification.maybe_donate_sched_context; mk_walk

theorem MK.notification_send_signal {s : S} {a : A} {n_ptr : Std.U64} {badge : Std.U64} (h : AR a c) :
    notification.send_signal st arI s a n_ptr badge ⦃ r => AR r.2 c ⦄ := by
  unfold notification.send_signal; mk_walk


theorem MK.schedcontext_bind_tcb {s : S} {a : A} {sc : obj.Sc} {t : obj.Tcb} (h : AR a c) :
    schedcontext.bind_tcb st arI s a sc t ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.bind_tcb; mk_walk

theorem MK.sched_end_timeslice {s : S} {a : A} {b : Bool} (h : AR a c) :
    sched.end_timeslice st arI s a b ⦃ r => AR r.2 c ⦄ := by
  unfold sched.end_timeslice; mk_walk

theorem MK.sched_charge_budget {s : S} {a : A} {u : Std.U64} {b : Bool} (h : AR a c) :
    sched.charge_budget st arI s a u b ⦃ r => AR r.2 c ⦄ := by
  unfold sched.charge_budget; mk_walk

theorem MK.sched_check_budget {s : S} {a : A} (h : AR a c) :
    sched.check_budget st arI s a ⦃ r => AR r.2.2 c ⦄ := by
  unfold sched.check_budget; mk_walk

theorem MK.syscall_mcs_preemption_point {s : S} {a : A} (h : AR a c) :
    syscall.mcs_preemption_point st arI s a ⦃ r => AR r.2 c ⦄ := by
  unfold syscall.mcs_preemption_point; mk_walk

end

end Fl4Proofs.P3
