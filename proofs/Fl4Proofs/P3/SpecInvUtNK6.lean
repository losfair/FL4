/- ut7: IRQ-node frame lemmas `NK N`, part 6 (invA's NativeScope scripts renamed; see SpecInvUtNK1). -/
import Fl4Proofs.P3.SpecInvUtNK5
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef}

theorem nk_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateWaitingNtfn _ _ _)

theorem nk_sendSignal (ntfnptr : ObjRef) (badge : Badge) : NK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_sendSignal _ _)

theorem nk_fl4Awaken : NK N (fl4Awaken (Z := Unit)) := by
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
    · exact nk_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem nk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem nk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem nk_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_initArchObjects _ _ _ _ _ _)

theorem nk_resetUntypedCap (srcSlot : CslotPtr) : NKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_resetUntypedCap _)

theorem nk_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : NKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeUntypedWith _ _)

theorem nk_invokeCnode (i : CnodeInvocation) : NKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeCnode _)

theorem nk_threadSetDomain (tptr : ObjRef) (domain : Domain) : NK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_threadSetDomain _ _)

theorem nk_setDomain (tptr : ObjRef) (newDom : Domain) : NK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setDomain _ _)

theorem nk_invokeSetDomain (thread : ObjRef) (domain : Domain) : NK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeSetDomain _ _)

theorem nk_invokeDomain (domInv : DomainInvocation) : NK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeDomain _)

theorem nk_invokeIrqControl (a0 : IrqControlInvocation) : NKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeIrqControl _)

theorem nk_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeFl4IrqControl _)

theorem nk_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeFl4Tcb _)

theorem nk_invokeIrqHandler (a0 : IrqHandlerInvocation) : NK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeIrqHandler _)

theorem nk_returnConsumed (scPtr : ObjRef) : NK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_returnConsumed _)

theorem nk_schedContextBindNtfn (sc ntfn : ObjRef) : NK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextBindNtfn _ _)

theorem nk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextBindTcb _ _)

theorem nk_schedContextYieldTo (scPtr : ObjRef) : NK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedContextYieldTo _)

theorem nk_invokeSchedContext (iv : SchedContextInvocation) : NK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeSchedContext _)

theorem nk_maybeAddEmptyTail (scPtr : ObjRef) : NK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_maybeAddEmptyTail _)

theorem nk_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillNew _ _ _ _)

theorem nk_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_refillUpdate _ _ _ _)

theorem nk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeSchedControlConfigureFlags _)

theorem nk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_installTcbCap _ _ _ _)

theorem nk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_installTcbFrameCap _ _ _)

theorem nk_setFlags (ref : ObjRef) (flags : TcbFlags) : NK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setFlags _ _)

theorem nk_setMcpriority (ref : ObjRef) (mcp : Priority) : NK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setMcpriority _ _)

theorem nk_reorderEp (epPtr tptr : ObjRef) : NK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_reorderEp _ _)

theorem nk_reorderNtfn (ntfnPtr tptr : ObjRef) : NK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_reorderNtfn _ _)

theorem nk_threadSetPriority (tptr : ObjRef) (prio : Priority) : NK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_threadSetPriority _ _)

theorem nk_setPriority (tptr : ObjRef) (prio : Priority) : NK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setPriority _ _)

theorem nk_invokeTcb (a0 : TcbInvocation) : NKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeTcb _)

theorem nk_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : NKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4PerformInvocation _ _ _ _)

theorem nk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4ReplyFromKernelError _ _ _)

theorem nk_handleNoFault (tptr : ObjRef) : NK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleNoFault _)

theorem nk_handleFault (thread : ObjRef) (ex : Fault) : NK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleFault _ _)

theorem nk_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NKE N mFault) (h_hFault : ∀ x0, NK N (hFault x0)) (h_mError : ∀ x0, NKE N (mError x0)) (h_hError : ∀ x0, NK N (hError x0)) (h_mFinalise : ∀ x0, NKE N (mFinalise x0)) : NKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; nk_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem nk_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4HandleInvocationR _ _ _ _ _ _)

theorem nk_getCapReg (reg : Register) : NK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getCapReg _)

theorem nk_lookupReply  : NKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lookupReply)

theorem nk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_maybeReturnSc _ _)

theorem nk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : NK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem nk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    NK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_receiveIpc _ _ _ _)

theorem nk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : NK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbNtfnAppend _ _)

theorem nk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : NK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_receiveSignalBlocked _ _ _)

theorem nk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : NK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_receiveSignal _ _ _)

theorem nk_handleRecv (isBlocking canReply : Bool) : NK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleRecv _ _)

theorem nk_handleYield  : NK N (handleYield (Z := Unit)) := by
  unfold handleYield; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleYield)

theorem nk_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : NKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4HandleSyscall _ _)

theorem nk_invokeUntyped (ui : UntypedInvocation) : NKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invokeUntyped _)

theorem nk_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : NKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performInvocation _ _ _ _)

theorem nk_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleInvocation _ _ _ _ _)

theorem nk_handleCall  : NKE N (handleCall (Z := Unit)) := by
  unfold handleCall; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleCall)

theorem nk_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleHypervisorFault _ _)

theorem nk_handleSend (bl : Bool) : NKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleSend _)

theorem nk_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleVmFault _ _)

theorem nk_handleReservedIrq (_irq : Irq) : NK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleReservedIrq _)

theorem nk_handleInterrupt (irq : Irq) : NK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleInterrupt _)

theorem nk_handleSpuriousIrq  : NK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleSpuriousIrq)

theorem nk_maybeHandleInterrupt (inKernel : Bool) : NK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_maybeHandleInterrupt _)

theorem nk_handleEvent (a0 : Event) : NKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleEvent _)

theorem nk_fl4HandleEvent (rep : Bool) (a0 : Event) : NKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4HandleEvent _ _)

theorem nk_preemptionPath  : NK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_preemptionPath)

theorem nk_fl4CallKernel (rep : Bool) (ev : Event) : NK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4CallKernel _ _)

theorem nk_fl4SyscallFaultIP (thread : ObjRef) : NK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4SyscallFaultIP _)

theorem nk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : NK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInvU
