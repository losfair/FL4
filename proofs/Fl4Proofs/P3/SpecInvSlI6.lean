/- sl1: idle-SC frame lemmas `IsK t` (sg1 SpecInvSgI6 renamed; see SpecInvSlI1). -/
import Fl4Proofs.P3.SpecInvSlI5
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem isk_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : IsK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateWaitingNtfn _ _ _)

theorem isk_sendSignal (ntfnptr : ObjRef) (badge : Badge) : IsK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_sendSignal _ _)

theorem isk_fl4Awaken : IsK N (fl4Awaken (Z := Unit)) := by
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
    · exact isk_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem isk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    IsKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem isk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : IsKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem isk_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : IsK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_initArchObjects _ _ _ _ _ _)

theorem isk_resetUntypedCap (srcSlot : CslotPtr) : IsKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_resetUntypedCap _)

theorem isk_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : IsKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeUntypedWith _ _)

theorem isk_invokeCnode (i : CnodeInvocation) : IsKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeCnode _)

theorem isk_threadSetDomain (tptr : ObjRef) (domain : Domain) : IsK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_threadSetDomain _ _)

theorem isk_setDomain (tptr : ObjRef) (newDom : Domain) : IsK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setDomain _ _)

theorem isk_invokeSetDomain (thread : ObjRef) (domain : Domain) : IsK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeSetDomain _ _)

theorem isk_invokeDomain (domInv : DomainInvocation) : IsK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeDomain _)

theorem isk_invokeIrqControl (a0 : IrqControlInvocation) : IsKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeIrqControl _)

theorem isk_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IsKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeFl4IrqControl _)

theorem isk_invokeFl4Tcb (a0 : Fl4TcbInvocation) : IsKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeFl4Tcb _)

theorem isk_invokeIrqHandler (a0 : IrqHandlerInvocation) : IsK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeIrqHandler _)

theorem isk_returnConsumed (scPtr : ObjRef) : IsK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_returnConsumed _)

theorem isk_schedContextBindNtfn (sc ntfn : ObjRef) : IsK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextBindNtfn _ _)

theorem isk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : IsK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextBindTcb _ _)

theorem isk_schedContextYieldTo (scPtr : ObjRef) : IsK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedContextYieldTo _)

theorem isk_invokeSchedContext (iv : SchedContextInvocation) : IsK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeSchedContext _)

theorem isk_maybeAddEmptyTail (scPtr : ObjRef) : IsK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_maybeAddEmptyTail _)

theorem isk_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : IsK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillNew _ _ _ _)

theorem isk_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : IsK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_refillUpdate _ _ _ _)

theorem isk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : IsK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeSchedControlConfigureFlags _)

theorem isk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : IsKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_installTcbCap _ _ _ _)

theorem isk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : IsKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_installTcbFrameCap _ _ _)

theorem isk_setFlags (ref : ObjRef) (flags : TcbFlags) : IsK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setFlags _ _)

theorem isk_setMcpriority (ref : ObjRef) (mcp : Priority) : IsK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setMcpriority _ _)

theorem isk_reorderEp (epPtr tptr : ObjRef) : IsK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_reorderEp _ _)

theorem isk_reorderNtfn (ntfnPtr tptr : ObjRef) : IsK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_reorderNtfn _ _)

theorem isk_threadSetPriority (tptr : ObjRef) (prio : Priority) : IsK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_threadSetPriority _ _)

theorem isk_setPriority (tptr : ObjRef) (prio : Priority) : IsK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setPriority _ _)

theorem isk_invokeTcb (a0 : TcbInvocation) : IsKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeTcb _)

theorem isk_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : IsKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4PerformInvocation _ _ _ _)

theorem isk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : IsK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4ReplyFromKernelError _ _ _)

theorem isk_handleNoFault (tptr : ObjRef) : IsK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleNoFault _)

theorem isk_handleFault (thread : ObjRef) (ex : Fault) : IsK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleFault _ _)

theorem isk_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : IsKE N mFault) (h_hFault : ∀ x0, IsK N (hFault x0)) (h_mError : ∀ x0, IsKE N (mError x0)) (h_hError : ∀ x0, IsK N (hError x0)) (h_mFinalise : ∀ x0, IsKE N (mFinalise x0)) : IsKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; isk_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem isk_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : IsKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4HandleInvocationR _ _ _ _ _ _)

theorem isk_getCapReg (reg : Register) : IsK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getCapReg _)

theorem isk_lookupReply  : IsKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lookupReply)

theorem isk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : IsK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_maybeReturnSc _ _)

theorem isk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : IsK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem isk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IsK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_receiveIpc _ _ _ _)

theorem isk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : IsK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbNtfnAppend _ _)

theorem isk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : IsK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_receiveSignalBlocked _ _ _)

theorem isk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : IsK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_receiveSignal _ _ _)

theorem isk_handleRecv (isBlocking canReply : Bool) : IsK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleRecv _ _)

theorem isk_handleYield  : IsK N (handleYield (Z := Unit)) := by
  unfold handleYield; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleYield)

theorem isk_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : IsKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4HandleSyscall _ _)

theorem isk_invokeUntyped (ui : UntypedInvocation) : IsKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invokeUntyped _)

theorem isk_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : IsKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performInvocation _ _ _ _)

theorem isk_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : IsKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleInvocation _ _ _ _ _)

theorem isk_handleCall  : IsKE N (handleCall (Z := Unit)) := by
  unfold handleCall; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleCall)

theorem isk_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : IsK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleHypervisorFault _ _)

theorem isk_handleSend (bl : Bool) : IsKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleSend _)

theorem isk_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : IsKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleVmFault _ _)

theorem isk_handleReservedIrq (_irq : Irq) : IsK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleReservedIrq _)

theorem isk_handleInterrupt (irq : Irq) : IsK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleInterrupt _)

theorem isk_handleSpuriousIrq  : IsK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleSpuriousIrq)

theorem isk_maybeHandleInterrupt (inKernel : Bool) : IsK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_maybeHandleInterrupt _)

theorem isk_handleEvent (a0 : Event) : IsKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleEvent _)

theorem isk_fl4HandleEvent (rep : Bool) (a0 : Event) : IsKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4HandleEvent _ _)

theorem isk_preemptionPath  : IsK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_preemptionPath)

theorem isk_fl4CallKernel (rep : Bool) (ev : Event) : IsK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4CallKernel _ _)

theorem isk_fl4SyscallFaultIP (thread : ObjRef) : IsK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4SyscallFaultIP _)

theorem isk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : IsK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInvL
