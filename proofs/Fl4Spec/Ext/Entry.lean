/-
FL4 differences (PORTING.md, "FL4 differences"): **the kernel entry with
FL4's dispatcher**.

* `fl4HandleEvent rep` is l4v's `handle_event` (Syscall_A, `handleEvent`)
  with `handle_invocation` replaced by FL4's `fl4HandleInvocationR rep`
  (Ext/ReplyError over Ext/Invocation): the same substitution one level up.
  The other events do not invoke (`fl4HandleEvent_other`, by `rfl`).
* `fl4CallKernel rep` is l4v's `call_kernel` (`callKernel`) with
  `fl4HandleEvent rep` for `handleEvent` and FL4's TCB timer step
  `fl4Awaken` (Ext/Timer, l4h 0003) before `schedule`: FL4's
  `sched::schedule` first runs `sched::awaken`, which fires the expired TCB
  timers (`timer::fire`) before l4v's release-queue `awaken`.
* `fl4KernelEntrySyscall rep c`: the syscall entry. FL4's `handle_syscall`
  first writes the current thread's `FaultIP` register := `NextIP - 2` (the
  `syscall` instruction is two bytes long), so that a restarted thread
  re-executes the syscall. l4v has no such write in `call_kernel`: ADT_A's
  `kernel_entry` installs the user context in which this is already done
  (`thread_set (tcb_arch := arch_tcb_context_set tc)` before `call_kernel`,
  the C kernel's `c_handle_syscall` / `setRegister(FaultIP, NextIP - 2)` in
  seL4's x86 `traps.S`/`c_traps.c`). The definition is that register write on
  the current thread followed by `fl4CallKernel rep (.syscallEvent c)`.

The ported modules are not changed.
-/
import Fl4Spec.Ext.ReplyError
import Fl4Spec.Ext.Timer

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-- The `match call` of l4v's `handle_event` with FL4's dispatcher
`fl4HandleInvocationR rep` for `handleInvocation`. -/
def fl4HandleSyscall (rep : Bool) : Syscall → PMonad Z Unit
  | .sysSend => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationR rep false true false false cptr
  | .sysNBSend => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationR rep false false false false cptr
  | .sysCall => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationR rep true true true false cptr
  | .sysRecv => withoutPreemption <| handleRecv true true
  | .sysYield => withoutPreemption handleYield
  | .sysReplyRecv => do
    let replyCptr ← withoutPreemption <| getCapReg replyRegister
    fl4HandleInvocationR rep false false true true replyCptr
    withoutPreemption <| handleRecv true true
  | .sysNBSendRecv => do
    let dest ← withoutPreemption <| getCapReg nbsendRecvDest
    fl4HandleInvocationR rep false false true true dest
    withoutPreemption <| handleRecv true true
  | .sysNBSendWait => do
    let replyCptr ← withoutPreemption <| getCapReg replyRegister
    fl4HandleInvocationR rep false false true true replyCptr
    withoutPreemption <| handleRecv true false
  | .sysWait => withoutPreemption <| handleRecv true false
  | .sysNBWait => withoutPreemption <| handleRecv false false
  | .sysNBRecv => withoutPreemption <| handleRecv false true

/-- l4v's `handle_event` with FL4's dispatcher `fl4HandleInvocationR rep`
for `handleInvocation` (the module docstring). -/
def fl4HandleEvent (rep : Bool) : Event → PMonad Z Unit
  | .syscallEvent call => do
    NonDetE.liftE updateTimeStamp
    let restart ← NonDetE.liftE checkBudgetRestart
    NonDetE.whenE restart (fl4HandleSyscall rep call)
  | ev => handleEvent ev

/-- The non-syscall events are l4v's. -/
theorem fl4HandleEvent_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    fl4HandleEvent (Z := Z) rep ev = handleEvent ev := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => rfl

/-- l4v's `call_kernel` with `fl4HandleEvent rep`, and FL4's TCB timers
(`fl4Awaken`, Ext/Timer) before `schedule`. -/
def fl4CallKernel (rep : Bool) (ev : Event) : SMonad Z Unit := do
  let _ ← ExceptT.run <| NonDetE.handleE (fl4HandleEvent rep ev) (fun _ => withoutPreemption preemptionPath)
  fl4Awaken
  schedule
  activateThread

/-- The `FaultIP := NextIP - 2` write of FL4's `handle_syscall` on a thread
(the context that l4v's `kernel_entry` installs). -/
def fl4SyscallFaultIP (thread : ObjRef) : SMonad Z Unit :=
  asUser thread (NonDet.bind (getRegister nextInstructionRegister)
    (fun n => setRegister faultRegister (n - 2)))

/-- **The syscall entry** (the module docstring): the `FaultIP` write on the
current thread, then `fl4CallKernel rep (.syscallEvent c)`. -/
def fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : SMonad Z Unit := do
  let ct ← NonDet.gets fun s : State Z => s.curThread
  fl4SyscallFaultIP ct
  fl4CallKernel rep (.syscallEvent c)

end

end

end Fl4Spec
