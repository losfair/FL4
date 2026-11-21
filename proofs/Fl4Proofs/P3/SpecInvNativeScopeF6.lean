/- invA: NativeScope frame lemmas, part 6 (generated; see SpecInvNativeScopeF1). -/
import Fl4Proofs.P3.SpecInvNativeScopeF5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem ns_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NSK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateWaitingNtfn _ _ _)

theorem ns_sendSignal (ntfnptr : ObjRef) (badge : Badge) : NSK (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_sendSignal _ _)

theorem ns_fl4Awaken : NSK (fl4Awaken (Z := Unit)) := by
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
    · exact ns_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ns_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NSKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ns_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NSKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ns_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NSK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_initArchObjects _ _ _ _ _ _)

theorem ns_resetUntypedCap (srcSlot : CslotPtr) : NSKE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_resetUntypedCap _)

theorem ns_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : NSKE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeUntypedWith _ _)

theorem ns_invokeCnode (i : CnodeInvocation) : NSKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeCnode _)

theorem ns_threadSetDomain (tptr : ObjRef) (domain : Domain) : NSK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_threadSetDomain _ _)

theorem ns_setDomain (tptr : ObjRef) (newDom : Domain) : NSK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setDomain _ _)

theorem ns_invokeSetDomain (thread : ObjRef) (domain : Domain) : NSK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSetDomain _ _)

theorem ns_invokeDomain (domInv : DomainInvocation) : NSK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeDomain _)

theorem ns_invokeIrqControl (a0 : IrqControlInvocation) : NSKE (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeIrqControl _)

theorem ns_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NSKE (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeFl4IrqControl _)

theorem ns_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NSKE (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeFl4Tcb _)

theorem ns_invokeIrqHandler (a0 : IrqHandlerInvocation) : NSK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeIrqHandler _)

theorem ns_returnConsumed (scPtr : ObjRef) : NSK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_returnConsumed _)

theorem ns_schedContextBindNtfn (sc ntfn : ObjRef) : NSK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextBindNtfn _ _)

theorem ns_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NSK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextBindTcb _ _)

theorem ns_schedContextYieldTo (scPtr : ObjRef) : NSK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedContextYieldTo _)

theorem ns_invokeSchedContext (iv : SchedContextInvocation) : NSK (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSchedContext _)

theorem ns_maybeAddEmptyTail (scPtr : ObjRef) : NSK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeAddEmptyTail _)

theorem ns_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NSK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillNew _ _ _ _)

theorem ns_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NSK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_refillUpdate _ _ _ _)

theorem ns_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NSK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeSchedControlConfigureFlags _)

theorem ns_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NSKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbCap _ _ _ _)

theorem ns_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NSKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_installTcbFrameCap _ _ _)

theorem ns_setFlags (ref : ObjRef) (flags : TcbFlags) : NSK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setFlags _ _)

theorem ns_setMcpriority (ref : ObjRef) (mcp : Priority) : NSK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setMcpriority _ _)

theorem ns_reorderEp (epPtr tptr : ObjRef) : NSK (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_reorderEp _ _)

theorem ns_reorderNtfn (ntfnPtr tptr : ObjRef) : NSK (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_reorderNtfn _ _)

theorem ns_threadSetPriority (tptr : ObjRef) (prio : Priority) : NSK (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_threadSetPriority _ _)

theorem ns_setPriority (tptr : ObjRef) (prio : Priority) : NSK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPriority _ _)

theorem ns_invokeTcb (a0 : TcbInvocation) : NSKE (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeTcb _)

theorem ns_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : NSKE (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4PerformInvocation _ _ _ _)

theorem ns_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NSK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ReplyFromKernelError _ _ _)

theorem ns_handleNoFault (tptr : ObjRef) : NSK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleNoFault _)

theorem ns_handleFault (thread : ObjRef) (ex : Fault) : NSK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleFault _ _)

theorem ns_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NSKE mFault) (h_hFault : ∀ x0, NSK (hFault x0)) (h_mError : ∀ x0, NSKE (mError x0)) (h_hError : ∀ x0, NSK (hError x0)) (h_mFinalise : ∀ x0, NSKE (mFinalise x0)) : NSKE (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ns_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ns_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NSKE (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleInvocationR _ _ _ _ _ _)

theorem ns_getCapReg (reg : Register) : NSK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getCapReg _)

theorem ns_lookupReply  : NSKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lookupReply)

theorem ns_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NSK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeReturnSc _ _)

theorem ns_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : NSK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem ns_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    NSK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveIpc _ _ _ _)

theorem ns_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : NSK (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbNtfnAppend _ _)

theorem ns_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : NSK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveSignalBlocked _ _ _)

theorem ns_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : NSK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_receiveSignal _ _ _)

theorem ns_handleRecv (isBlocking canReply : Bool) : NSK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleRecv _ _)

theorem ns_handleYield  : NSK (handleYield (Z := Unit)) := by
  unfold handleYield; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleYield)

theorem ns_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : NSKE (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleSyscall _ _)

theorem ns_invokeUntyped (ui : UntypedInvocation) : NSKE (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invokeUntyped _)

theorem ns_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : NSKE (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performInvocation _ _ _ _)

theorem ns_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : NSKE (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleInvocation _ _ _ _ _)

theorem ns_handleCall  : NSKE (handleCall (Z := Unit)) := by
  unfold handleCall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleCall)

theorem ns_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NSK (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleHypervisorFault _ _)

theorem ns_handleSend (bl : Bool) : NSKE (handleSend (Z := Unit) bl) := by
  unfold handleSend; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleSend _)

theorem ns_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NSKE (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleVmFault _ _)

theorem ns_handleReservedIrq (_irq : Irq) : NSK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleReservedIrq _)

theorem ns_handleInterrupt (irq : Irq) : NSK (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleInterrupt _)

theorem ns_handleSpuriousIrq  : NSK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleSpuriousIrq)

theorem ns_maybeHandleInterrupt (inKernel : Bool) : NSK (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_maybeHandleInterrupt _)

theorem ns_handleEvent (a0 : Event) : NSKE (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleEvent _)

theorem ns_fl4HandleEvent (rep : Bool) (a0 : Event) : NSKE (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4HandleEvent _ _)

theorem ns_preemptionPath  : NSK (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_preemptionPath)

theorem ns_fl4CallKernel (rep : Bool) (ev : Event) : NSK (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4CallKernel _ _)

theorem ns_fl4SyscallFaultIP (thread : ObjRef) : NSK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4SyscallFaultIP _)

theorem ns_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : NSK (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInv
