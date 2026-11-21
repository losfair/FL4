/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN g4b): **FL4's `finish` keeps
`MR`** (`MKD.syscall_finish`): MachKeepD's `MKD.*` walk extended to the
arch-threading call graph of `syscall.finish` (`schedule`, `activate_thread`,
the timer firing loop, the scheduler's switch and next-interrupt steps;
scripted: scratch/mr6/topo.py + mkdgen.py on scratch/g4b/fin_gen.txt). Every
arch operation reached is a field of `MRKeepD` (`fpu_flush`, `fpu_release`,
`remote_stall`, `send_reschedule`, `set_deadline`, `set_vspace`) or a query
returning no arch state (`kernel_wcet_ticks`, `max_us`, `ticks_to_us`,
`us_to_ticks`). The same for `handle_recv` and `handle_yield`
(`MKD.syscall_handle_recv`, `MKD.syscall_handle_yield`). Arch-only (no spec state, no P1 import).
-/
import Fl4Proofs.P3.MachKeepD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : MRKeepD arI AR) {c₀ : C}
include hS hA hK
set_option linter.unusedSectionVars false

theorem MKD.schedcontext_resume {s : S} {a : A} {sc : obj.Sc} (h : AR a c₀) :
    schedcontext.resume st arI s a sc ⦃ r => AR r.2 c₀ ⦄ := by
  unfold schedcontext.resume; mkd_walk

theorem MKD.notification_maybe_donate_sched_context {s : S} {a : A} {t : obj.Tcb} {n : obj.Ntfn} (h : AR a c₀) :
    notification.maybe_donate_sched_context st arI s a t n ⦃ r => AR r.2 c₀ ⦄ := by
  unfold notification.maybe_donate_sched_context; mkd_walk

theorem MKD.notification_send_signal {s : S} {a : A} {n_ptr : Std.U64} {badge : Std.U64} (h : AR a c₀) :
    notification.send_signal st arI s a n_ptr badge ⦃ r => AR r.2 c₀ ⦄ := by
  unfold notification.send_signal; mkd_walk

theorem MKD.sched_activate_thread {s : S} {a : A}  (h : AR a c₀) :
    sched.activate_thread st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.activate_thread; mkd_walk

theorem MKD.timer_fire_loop {s : S} {a : A} {now i : Std.U64} (h : AR a c₀) :
    timer.fire_loop st arI s a now i ⦃ r => AR r.2 c₀ ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, x2) => timer.FIRE_BATCH.val - x2.val)
    (inv := fun x => AR x.2.1 c₀)
  · rintro ⟨x0, x1, x2⟩ h1
    dsimp only at h1
    unfold timer.fire_loop.body
    mkd_walk
  · exact h

theorem MKD.timer_fire {s : S} {a : A}  (h : AR a c₀) :
    timer.fire st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold timer.fire; mkd_walk

theorem MKD.sched_awaken {s : S} {a : A}  (h : AR a c₀) :
    sched.awaken st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.awaken; mkd_walk

theorem MKD.sched_switch_to_idle_thread {s : S} {a : A}  (h : AR a c₀) :
    sched.switch_to_idle_thread st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.switch_to_idle_thread; mkd_walk

theorem MKD.sched_switch_to_thread {s : S} {a : A} {t : obj.Tcb} (h : AR a c₀) :
    sched.switch_to_thread st arI s a t ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.switch_to_thread; mkd_walk

theorem MKD.sched_choose_thread {s : S} {a : A}  (h : AR a c₀) :
    sched.choose_thread st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.choose_thread; mkd_walk

theorem MKD.sched_schedule_choose_new_thread {s : S} {a : A}  (h : AR a c₀) :
    sched.schedule_choose_new_thread st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.schedule_choose_new_thread; mkd_walk

theorem MKD.sched_set_next_interrupt {s : S} {a : A}  (h : AR a c₀) :
    sched.set_next_interrupt st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.set_next_interrupt; mkd_walk

theorem MKD.sched_switch_sched_context {s : S} {a : A}  (h : AR a c₀) :
    sched.switch_sched_context st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.switch_sched_context; mkd_walk

theorem MKD.smp_send_pending {s : S} {a : A}  (h : AR a c₀) :
    smp.send_pending st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold smp.send_pending; mkd_walk

theorem MKD.sched_schedule {s : S} {a : A}  (h : AR a c₀) :
    sched.schedule st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.schedule; mkd_walk

theorem MKD.syscall_finish {s : S} {a : A}  (h : AR a c₀) :
    syscall.finish st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold syscall.finish; mkd_walk

/-! The receive and yield handlers (scratch/g4b/rv_gen.txt). -/

theorem MKD.ipc_reply_push {s : S} {a : A} {caller : obj.Tcb} {callee : obj.Tcb} {r : obj.Reply} {can_donate : Bool} (h : AR a c₀) :
    ipc.reply_push st arI s a caller callee r can_donate ⦃ r => AR r.2 c₀ ⦄ := by
  unfold ipc.reply_push; mkd_walk

theorem MKD.endpoint_receive_from_sender {s : S} {a : A} {thread : obj.Tcb} {ep_ptr : Std.U64} {reply : obj.Reply} (h : AR a c₀) :
    endpoint.receive_from_sender st arI s a thread ep_ptr reply ⦃ r => AR r.2 c₀ ⦄ := by
  unfold endpoint.receive_from_sender; mkd_walk

theorem MKD.endpoint_take_reply {s : S} {a : A} {thread : obj.Tcb} {reply_cap : capability.Cap} (h : AR a c₀) :
    endpoint.take_reply st arI s a thread reply_cap ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold endpoint.take_reply; mkd_walk

theorem MKD.notification_complete_signal {s : S} {a : A} {n : obj.Ntfn} {t : obj.Tcb} (h : AR a c₀) :
    notification.complete_signal st arI s a n t ⦃ r => AR r.2 c₀ ⦄ := by
  unfold notification.complete_signal; mkd_walk

theorem MKD.endpoint_receive_ipc {s : S} {a : A} {thread : obj.Tcb} {cap : capability.Cap} {blocking : Bool} {reply_cap : capability.Cap} (h : AR a c₀) :
    endpoint.receive_ipc st arI s a thread cap blocking reply_cap ⦃ r => AR r.2 c₀ ⦄ := by
  unfold endpoint.receive_ipc; mkd_walk

theorem MKD.endpoint_send_ipc {s : S} {a : A} {blocking : Bool} {do_call : Bool} {badge : Std.U64} {can_grant : Bool} {can_grant_reply : Bool} {can_donate : Bool} {thread : obj.Tcb} {ep_ptr : Std.U64} (h : AR a c₀) :
    endpoint.send_ipc st arI s a blocking do_call badge can_grant can_grant_reply can_donate thread ep_ptr ⦃ r => AR r.2 c₀ ⦄ := by
  unfold endpoint.send_ipc; mkd_walk

theorem MKD.faults_send_fault_ipc {s : S} {a : A} {t : obj.Tcb} {handler : capability.Cap} {can_donate : Bool} {f : error.Fault} (h : AR a c₀) :
    faults.send_fault_ipc st arI s a t handler can_donate f ⦃ r => AR r.2.2 c₀ ⦄ := by
  unfold faults.send_fault_ipc; mkd_walk

theorem MKD.faults_handle_fault {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} (h : AR a c₀) :
    faults.handle_fault st arI s a t f ⦃ r => AR r.2 c₀ ⦄ := by
  unfold faults.handle_fault; mkd_walk

theorem MKD.faults_handle_timeout {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} (h : AR a c₀) :
    faults.handle_timeout st arI s a t f ⦃ r => AR r.2 c₀ ⦄ := by
  unfold faults.handle_timeout; mkd_walk

theorem MKD.notification_receive_signal {s : S} {a : A} {t : obj.Tcb} {n_ptr : Std.U64} {blocking : Bool} (h : AR a c₀) :
    notification.receive_signal st arI s a t n_ptr blocking ⦃ r => AR r.2 c₀ ⦄ := by
  unfold notification.receive_signal; mkd_walk

theorem MKD.sched_end_timeslice {s : S} {a : A} {can_timeout_fault : Bool} (h : AR a c₀) :
    sched.end_timeslice st arI s a can_timeout_fault ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.end_timeslice; mkd_walk

theorem MKD.sched_charge_budget {s : S} {a : A} {used : Std.U64} {can_timeout_fault : Bool} (h : AR a c₀) :
    sched.charge_budget st arI s a used can_timeout_fault ⦃ r => AR r.2 c₀ ⦄ := by
  unfold sched.charge_budget; mkd_walk

theorem MKD.syscall_cap_fault_recv {s : S} {a : A} {cptr : Std.U64} {lf : error.LookupFault} (h : AR a c₀) :
    syscall.cap_fault_recv st arI s a cptr lf ⦃ r => AR r.2 c₀ ⦄ := by
  unfold syscall.cap_fault_recv; mkd_walk

theorem MKD.syscall_handle_recv {s : S} {a : A} {blocking : Bool} {can_reply : Bool} (h : AR a c₀) :
    syscall.handle_recv st arI s a blocking can_reply ⦃ r => AR r.2 c₀ ⦄ := by
  unfold syscall.handle_recv; mkd_walk

theorem MKD.syscall_handle_yield {s : S} {a : A}  (h : AR a c₀) :
    syscall.handle_yield st arI s a ⦃ r => AR r.2 c₀ ⦄ := by
  unfold syscall.handle_yield; mkd_walk

end

end Fl4Proofs.P3
