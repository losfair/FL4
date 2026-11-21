
/- fo1: generated frames `OIK Qo` (sg1's SpecInvSgI6 renamed, the owner / retype / detype writers removed; see SpecInvFoG1). -/
import Fl4Proofs.P3.SpecInvFoG5
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Qo : Option ObjRef}

theorem oi_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : OIK Qo (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateWaitingNtfn _ _ _)

theorem oi_sendSignal (ntfnptr : ObjRef) (badge : Badge) : OIK Qo (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_sendSignal _ _)

theorem oi_fl4Awaken : OIK Qo (fl4Awaken (Z := Unit)) := by
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
    OIKE Qo (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem oi_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : OIKE Qo (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem oi_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : OIK Qo (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_initArchObjects _ _ _ _ _ _)

theorem oi_threadSetDomain (tptr : ObjRef) (domain : Domain) : OIK Qo (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetDomain _ _)

theorem oi_setDomain (tptr : ObjRef) (newDom : Domain) : OIK Qo (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setDomain _ _)

theorem oi_invokeIrqControl (a0 : IrqControlInvocation) : OIKE Qo (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqControl _)

theorem oi_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : OIKE Qo (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeFl4IrqControl _)

theorem oi_invokeIrqHandler (a0 : IrqHandlerInvocation) : OIK Qo (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeIrqHandler _)

theorem oi_returnConsumed (scPtr : ObjRef) : OIK Qo (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_returnConsumed _)

theorem oi_schedContextBindNtfn (sc ntfn : ObjRef) : OIK Qo (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindNtfn _ _)

theorem oi_schedContextBindTcb (scPtr tcbPtr : ObjRef) : OIK Qo (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextBindTcb _ _)

theorem oi_schedContextYieldTo (scPtr : ObjRef) : OIK Qo (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedContextYieldTo _)

theorem oi_invokeSchedContext (iv : SchedContextInvocation) : OIK Qo (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedContext _)

theorem oi_maybeAddEmptyTail (scPtr : ObjRef) : OIK Qo (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeAddEmptyTail _)

theorem oi_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : OIK Qo (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillNew _ _ _ _)

theorem oi_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : OIK Qo (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_refillUpdate _ _ _ _)

theorem oi_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : OIK Qo (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invokeSchedControlConfigureFlags _)

theorem oi_setFlags (ref : ObjRef) (flags : TcbFlags) : OIK Qo (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setFlags _ _)

theorem oi_setMcpriority (ref : ObjRef) (mcp : Priority) : OIK Qo (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setMcpriority _ _)

theorem oi_reorderEp (epPtr tptr : ObjRef) : OIK Qo (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderEp _ _)

theorem oi_reorderNtfn (ntfnPtr tptr : ObjRef) : OIK Qo (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_reorderNtfn _ _)

theorem oi_threadSetPriority (tptr : ObjRef) (prio : Priority) : OIK Qo (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_threadSetPriority _ _)

theorem oi_setPriority (tptr : ObjRef) (prio : Priority) : OIK Qo (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPriority _ _)

theorem oi_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : OIK Qo (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ReplyFromKernelError _ _ _)

theorem oi_handleNoFault (tptr : ObjRef) : OIK Qo (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleNoFault _)

theorem oi_handleFault (thread : ObjRef) (ex : Fault) : OIK Qo (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleFault _ _)

theorem oi_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : OIKE Qo mFault) (h_hFault : ∀ x0, OIK Qo (hFault x0)) (h_mError : ∀ x0, OIKE Qo (mError x0)) (h_hError : ∀ x0, OIK Qo (hError x0)) (h_mFinalise : ∀ x0, OIKE Qo (mFinalise x0)) : OIKE Qo (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; oi_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem oi_getCapReg (reg : Register) : OIK Qo (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getCapReg _)

theorem oi_lookupReply  : OIKE Qo (lookupReply (Z := Unit)) := by
  unfold lookupReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lookupReply)

theorem oi_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : OIK Qo (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeReturnSc _ _)

theorem oi_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : OIK Qo (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem oi_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    OIK Qo (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveIpc _ _ _ _)

theorem oi_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : OIK Qo (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbNtfnAppend _ _)

theorem oi_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : OIK Qo (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignalBlocked _ _ _)

theorem oi_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : OIK Qo (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_receiveSignal _ _ _)

theorem oi_handleRecv (isBlocking canReply : Bool) : OIK Qo (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleRecv _ _)

theorem oi_handleYield  : OIK Qo (handleYield (Z := Unit)) := by
  unfold handleYield; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleYield)

theorem oi_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : OIK Qo (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleHypervisorFault _ _)

theorem oi_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : OIKE Qo (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleVmFault _ _)

theorem oi_handleReservedIrq (_irq : Irq) : OIK Qo (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleReservedIrq _)

theorem oi_handleInterrupt (irq : Irq) : OIK Qo (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleInterrupt _)

theorem oi_handleSpuriousIrq  : OIK Qo (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleSpuriousIrq)

theorem oi_maybeHandleInterrupt (inKernel : Bool) : OIK Qo (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_maybeHandleInterrupt _)

theorem oi_preemptionPath  : OIK Qo (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_preemptionPath)

theorem oi_fl4SyscallFaultIP (thread : ObjRef) : OIK Qo (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvF
