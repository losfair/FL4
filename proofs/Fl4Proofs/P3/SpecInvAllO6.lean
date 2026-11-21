/- g1c: OnlyIdle frame lemmas, part 6 (generated; see SpecInvAllO1). -/
import Fl4Proofs.P3.SpecInvAllO5
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem oi_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : OIK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateWaitingNtfn _ _ _)

theorem oi_sendSignal (ntfnptr : ObjRef) (badge : Badge) : OIK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendSignal _ _)

theorem oi_fl4Awaken : OIK N (fl4Awaken (Z := Unit)) := by
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
    · exact oi_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem oi_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OIKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem oi_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : OIKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem oi_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : OIK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_initArchObjects _ _ _ _ _ _)

theorem oi_resetUntypedCap (srcSlot : CslotPtr) : OIKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_resetUntypedCap _)

theorem oi_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : OIKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeUntypedWith _ _)

theorem oi_invokeCnode (i : CnodeInvocation) : OIKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeCnode _)

theorem oi_threadSetDomain (tptr : ObjRef) (domain : Domain) : OIK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetDomain _ _)

theorem oi_setDomain (tptr : ObjRef) (newDom : Domain) : OIK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setDomain _ _)

theorem oi_invokeSetDomain (thread : ObjRef) (domain : Domain) : OIK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSetDomain _ _)

theorem oi_invokeDomain (domInv : DomainInvocation) : OIK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeDomain _)

theorem oi_invokeIrqControl (a0 : IrqControlInvocation) : OIKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqControl _)

theorem oi_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : OIKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeFl4IrqControl _)

theorem oi_invokeFl4Tcb (a0 : Fl4TcbInvocation) : OIKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeFl4Tcb _)

theorem oi_invokeIrqHandler (a0 : IrqHandlerInvocation) : OIK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqHandler _)

theorem oi_returnConsumed (scPtr : ObjRef) : OIK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_returnConsumed _)

theorem oi_schedContextBindNtfn (sc ntfn : ObjRef) : OIK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindNtfn _ _)

theorem oi_schedContextBindTcb (scPtr tcbPtr : ObjRef) : OIK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindTcb _ _)

theorem oi_schedContextYieldTo (scPtr : ObjRef) : OIK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextYieldTo _)

theorem oi_invokeSchedContext (iv : SchedContextInvocation) : OIK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedContext _)

theorem oi_maybeAddEmptyTail (scPtr : ObjRef) : OIK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeAddEmptyTail _)

theorem oi_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : OIK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillNew _ _ _ _)

theorem oi_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : OIK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUpdate _ _ _ _)

theorem oi_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : OIK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedControlConfigureFlags _)

theorem oi_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : OIKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_installTcbCap _ _ _ _)

theorem oi_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : OIKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_installTcbFrameCap _ _ _)

theorem oi_setFlags (ref : ObjRef) (flags : TcbFlags) : OIK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setFlags _ _)

theorem oi_setMcpriority (ref : ObjRef) (mcp : Priority) : OIK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setMcpriority _ _)

theorem oi_reorderEp (epPtr tptr : ObjRef) : OIK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderEp _ _)

theorem oi_reorderNtfn (ntfnPtr tptr : ObjRef) : OIK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderNtfn _ _)

theorem oi_threadSetPriority (tptr : ObjRef) (prio : Priority) : OIK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetPriority _ _)

theorem oi_setPriority (tptr : ObjRef) (prio : Priority) : OIK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPriority _ _)

theorem oi_invokeTcb (a0 : TcbInvocation) : OIKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeTcb _)

theorem oi_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : OIKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4PerformInvocation _ _ _ _)

theorem oi_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : OIK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ReplyFromKernelError _ _ _)

theorem oi_handleNoFault (tptr : ObjRef) : OIK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleNoFault _)

theorem oi_handleFault (thread : ObjRef) (ex : Fault) : OIK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleFault _ _)

theorem oi_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : OIKE N mFault) (h_hFault : ∀ x0, OIK N (hFault x0)) (h_mError : ∀ x0, OIKE N (mError x0)) (h_hError : ∀ x0, OIK N (hError x0)) (h_mFinalise : ∀ x0, OIKE N (mFinalise x0)) : OIKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; oi_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem oi_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : OIKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleInvocationR _ _ _ _ _ _)

theorem oi_getCapReg (reg : Register) : OIK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getCapReg _)

theorem oi_lookupReply  : OIKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupReply)

theorem oi_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : OIK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeReturnSc _ _)

theorem oi_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : OIK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem oi_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    OIK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpc _ _ _ _)

theorem oi_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : OIK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnAppend _ _)

theorem oi_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : OIK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignalBlocked _ _ _)

theorem oi_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : OIK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignal _ _ _)

theorem oi_handleRecv (isBlocking canReply : Bool) : OIK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleRecv _ _)

theorem oi_handleYield  : OIK N (handleYield (Z := Unit)) := by
  unfold handleYield; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleYield)

theorem oi_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : OIKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleSyscall _ _)

theorem oi_invokeUntyped (ui : UntypedInvocation) : OIKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeUntyped _)

theorem oi_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : OIKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performInvocation _ _ _ _)

theorem oi_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : OIKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleInvocation _ _ _ _ _)

theorem oi_handleCall  : OIKE N (handleCall (Z := Unit)) := by
  unfold handleCall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleCall)

theorem oi_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : OIK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleHypervisorFault _ _)

theorem oi_handleSend (bl : Bool) : OIKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleSend _)

theorem oi_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : OIKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleVmFault _ _)

theorem oi_handleReservedIrq (_irq : Irq) : OIK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleReservedIrq _)

theorem oi_handleInterrupt (irq : Irq) : OIK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleInterrupt _)

theorem oi_handleSpuriousIrq  : OIK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleSpuriousIrq)

theorem oi_maybeHandleInterrupt (inKernel : Bool) : OIK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeHandleInterrupt _)

theorem oi_handleEvent (a0 : Event) : OIKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleEvent _)

theorem oi_fl4HandleEvent (rep : Bool) (a0 : Event) : OIKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4HandleEvent _ _)

theorem oi_preemptionPath  : OIK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPath)

theorem oi_fl4CallKernel (rep : Bool) (ev : Event) : OIK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4CallKernel _ _)

theorem oi_fl4SyscallFaultIP (thread : ObjRef) : OIK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4SyscallFaultIP _)

theorem oi_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : OIK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInvAll
