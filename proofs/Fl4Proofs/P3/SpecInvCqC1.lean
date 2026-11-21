/-
P3 (DESIGN.md §9), invariant line G1 (ctq12): **EB across the performs**,
part 1: the invocation arms whose callees all have generated tq / sa / q4 /
rb leaves (spec side only, outside the JAtZ cone). Each keeps `EB k` for
every `k`.
-/
import Fl4Proofs.P3.SpecInvCqB4
import Fl4Proofs.P3.SpecInvCqB5
import Fl4Proofs.P3.SpecInvCqP
open Classical

namespace Fl4Proofs.P3.SInvQ.P12
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ

noncomputable section

set_option maxHeartbeats 1000000
variable {k : Bool}

theorem eb_perfFl4Tcb (bl call don : Bool) (i : Fl4TcbInvocation) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeFl4TCB i)) := by
  simp only [fl4PerformInvocation]; eb_auto

theorem eb_perfIrqControl (bl call don : Bool) (i : Fl4IrqControlInvocation) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeIRQControl i)) := by
  simp only [fl4PerformInvocation]; eb_auto

theorem eb_perfIrqAck (bl call don : Bool) (irq : Irq) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeIRQHandler (.aCKIrq irq))) := by
  simp only [fl4PerformInvocation, invokeIrqHandler]; eb_auto

theorem eb_perfTls (bl call don : Bool) (t : ObjRef) (b : Data) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.setTLSBase t b))) := by
  simp only [fl4PerformInvocation, invokeTcb]; eb_auto

theorem eb_perfSetFlags (bl call don : Bool) (t : ObjRef) (c s : TcbFlags) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.setFlags t c s))) := by
  simp only [fl4PerformInvocation, invokeTcb]; eb_auto

theorem eb_perfNtfnControl (bl call don : Bool) (t : ObjRef) (n : Option ObjRef) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeTCB (.notificationControl t n))) := by
  cases n <;> (simp only [fl4PerformInvocation, invokeTcb]; eb_auto)

theorem eb_perfScConsumed (bl call don : Bool) (p : ObjRef) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedContext (.invokeSchedContextConsumed p))) := by
  simp only [fl4PerformInvocation, withoutPreemption, invokeSchedContext]; eb_auto

theorem eb_perfScUnbindObject (bl call don : Bool) (p : ObjRef) (c : Cap) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedContext (.invokeSchedContextUnbindObject p c))) := by
  simp only [fl4PerformInvocation, withoutPreemption, invokeSchedContext]
  cases c <;> (try simp only) <;> eb_auto

theorem eb_perfScUnbind (bl call don : Bool) (p : ObjRef) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeSchedContext (.invokeSchedContextUnbind p))) := by
  simp only [fl4PerformInvocation, withoutPreemption, invokeSchedContext]; eb_auto

theorem eb_perfArchNoPool (bl call don : Bool) (i : Fl4ArchInvocation)
    (hi : ∀ o, i ≠ .spec (.invokeASIDControl o)) :
    EBKE k (fl4PerformInvocation (Z := Unit) bl call don (.invokeArchObject i)) := by
  cases i
  case spec a =>
    cases a
    case invokeASIDControl o => exact absurd rfl (hi o)
    all_goals (simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]; eb_auto)
  all_goals (simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; eb_auto)

end

end Fl4Proofs.P3.SInvQ.P12
