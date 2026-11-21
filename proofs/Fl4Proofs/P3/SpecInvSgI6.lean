/- sg1: idle-thread frame lemmas `IdK t` (ut7's SpecInvUtNK6 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvSgI5
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem idk_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : IdK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateWaitingNtfn _ _ _)

theorem idk_sendSignal (ntfnptr : ObjRef) (badge : Badge) : IdK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_sendSignal _ _)

theorem idk_fl4Awaken : IdK N (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact idk_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem idk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    IdKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem idk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : IdKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem idk_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : IdK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_initArchObjects _ _ _ _ _ _)

theorem idk_resetUntypedCap (srcSlot : CslotPtr) : IdKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_resetUntypedCap _)

theorem idk_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : IdKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeUntypedWith _ _)

theorem idk_invokeCnode (i : CnodeInvocation) : IdKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeCnode _)

theorem idk_threadSetDomain (tptr : ObjRef) (domain : Domain) : IdK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_threadSetDomain _ _)

theorem idk_setDomain (tptr : ObjRef) (newDom : Domain) : IdK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setDomain _ _)

theorem idk_invokeSetDomain (thread : ObjRef) (domain : Domain) : IdK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeSetDomain _ _)

theorem idk_invokeDomain (domInv : DomainInvocation) : IdK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeDomain _)

theorem idk_invokeIrqControl (a0 : IrqControlInvocation) : IdKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeIrqControl _)

theorem idk_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IdKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeFl4IrqControl _)

theorem idk_invokeFl4Tcb (a0 : Fl4TcbInvocation) : IdKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeFl4Tcb _)

theorem idk_invokeIrqHandler (a0 : IrqHandlerInvocation) : IdK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeIrqHandler _)

theorem idk_returnConsumed (scPtr : ObjRef) : IdK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_returnConsumed _)

theorem idk_schedContextBindNtfn (sc ntfn : ObjRef) : IdK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextBindNtfn _ _)

theorem idk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : IdK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextBindTcb _ _)

theorem idk_schedContextYieldTo (scPtr : ObjRef) : IdK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedContextYieldTo _)

theorem idk_invokeSchedContext (iv : SchedContextInvocation) : IdK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeSchedContext _)

theorem idk_maybeAddEmptyTail (scPtr : ObjRef) : IdK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_maybeAddEmptyTail _)

theorem idk_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : IdK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillNew _ _ _ _)

theorem idk_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : IdK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_refillUpdate _ _ _ _)

theorem idk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : IdK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeSchedControlConfigureFlags _)

theorem idk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : IdKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_installTcbCap _ _ _ _)

theorem idk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : IdKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_installTcbFrameCap _ _ _)

theorem idk_setFlags (ref : ObjRef) (flags : TcbFlags) : IdK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setFlags _ _)

theorem idk_setMcpriority (ref : ObjRef) (mcp : Priority) : IdK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setMcpriority _ _)

theorem idk_reorderEp (epPtr tptr : ObjRef) : IdK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_reorderEp _ _)

theorem idk_reorderNtfn (ntfnPtr tptr : ObjRef) : IdK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_reorderNtfn _ _)

theorem idk_threadSetPriority (tptr : ObjRef) (prio : Priority) : IdK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_threadSetPriority _ _)

theorem idk_setPriority (tptr : ObjRef) (prio : Priority) : IdK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setPriority _ _)

theorem idk_invokeTcb (a0 : TcbInvocation) : IdKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeTcb _)

theorem idk_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : IdKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4PerformInvocation _ _ _ _)

theorem idk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : IdK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4ReplyFromKernelError _ _ _)

theorem idk_handleNoFault (tptr : ObjRef) : IdK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleNoFault _)

theorem idk_handleFault (thread : ObjRef) (ex : Fault) : IdK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleFault _ _)

theorem idk_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : IdKE N mFault) (h_hFault : ∀ x0, IdK N (hFault x0)) (h_mError : ∀ x0, IdKE N (mError x0)) (h_hError : ∀ x0, IdK N (hError x0)) (h_mFinalise : ∀ x0, IdKE N (mFinalise x0)) : IdKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; idk_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem idk_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : IdKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4HandleInvocationR _ _ _ _ _ _)

theorem idk_getCapReg (reg : Register) : IdK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getCapReg _)

theorem idk_lookupReply  : IdKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lookupReply)

theorem idk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : IdK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_maybeReturnSc _ _)

theorem idk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : IdK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem idk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IdK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_receiveIpc _ _ _ _)

theorem idk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : IdK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbNtfnAppend _ _)

theorem idk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : IdK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_receiveSignalBlocked _ _ _)

theorem idk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : IdK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_receiveSignal _ _ _)

theorem idk_handleRecv (isBlocking canReply : Bool) : IdK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleRecv _ _)

theorem idk_handleYield  : IdK N (handleYield (Z := Unit)) := by
  unfold handleYield; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleYield)

theorem idk_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : IdKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4HandleSyscall _ _)

theorem idk_invokeUntyped (ui : UntypedInvocation) : IdKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invokeUntyped _)

theorem idk_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : IdKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performInvocation _ _ _ _)

theorem idk_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : IdKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleInvocation _ _ _ _ _)

theorem idk_handleCall  : IdKE N (handleCall (Z := Unit)) := by
  unfold handleCall; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleCall)

theorem idk_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : IdK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleHypervisorFault _ _)

theorem idk_handleSend (bl : Bool) : IdKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleSend _)

theorem idk_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : IdKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleVmFault _ _)

theorem idk_handleReservedIrq (_irq : Irq) : IdK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleReservedIrq _)

theorem idk_handleInterrupt (irq : Irq) : IdK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleInterrupt _)

theorem idk_handleSpuriousIrq  : IdK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleSpuriousIrq)

theorem idk_maybeHandleInterrupt (inKernel : Bool) : IdK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_maybeHandleInterrupt _)

theorem idk_handleEvent (a0 : Event) : IdKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleEvent _)

theorem idk_fl4HandleEvent (rep : Bool) (a0 : Event) : IdKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4HandleEvent _ _)

theorem idk_preemptionPath  : IdK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_preemptionPath)

theorem idk_fl4CallKernel (rep : Bool) (ev : Event) : IdK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4CallKernel _ _)

theorem idk_fl4SyscallFaultIP (thread : ObjRef) : IdK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4SyscallFaultIP _)

theorem idk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : IdK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInvG
