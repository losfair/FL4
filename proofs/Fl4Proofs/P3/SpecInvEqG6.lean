
/- epq1: generated frames `PZK` (sg1's SpecInvSgI6 renamed, the refill writers and the configure path removed; see SpecInvEqG1). -/
import Fl4Proofs.P3.SpecInvEqG5
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000


theorem pz_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : PZK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateWaitingNtfn _ _ _)

theorem pz_sendSignal (ntfnptr : ObjRef) (badge : Badge) : PZK (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_sendSignal _ _)

theorem pz_fl4Awaken : PZK (fl4Awaken (Z := Unit)) := by
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
    · exact pz_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem pz_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    PZKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem pz_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : PZKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem pz_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : PZK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_initArchObjects _ _ _ _ _ _)

theorem pz_resetUntypedCap (srcSlot : CslotPtr) : PZKE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_resetUntypedCap _)

theorem pz_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : PZKE (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeUntypedWith _ _)

theorem pz_invokeCnode (i : CnodeInvocation) : PZKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeCnode _)

theorem pz_threadSetDomain (tptr : ObjRef) (domain : Domain) : PZK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_threadSetDomain _ _)

theorem pz_setDomain (tptr : ObjRef) (newDom : Domain) : PZK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setDomain _ _)

theorem pz_invokeSetDomain (thread : ObjRef) (domain : Domain) : PZK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeSetDomain _ _)

theorem pz_invokeDomain (domInv : DomainInvocation) : PZK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeDomain _)

theorem pz_invokeIrqControl (a0 : IrqControlInvocation) : PZKE (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeIrqControl _)

theorem pz_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : PZKE (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeFl4IrqControl _)

theorem pz_invokeFl4Tcb (a0 : Fl4TcbInvocation) : PZKE (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeFl4Tcb _)

theorem pz_invokeIrqHandler (a0 : IrqHandlerInvocation) : PZK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeIrqHandler _)

theorem pz_returnConsumed (scPtr : ObjRef) : PZK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_returnConsumed _)

theorem pz_schedContextBindNtfn (sc ntfn : ObjRef) : PZK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextBindNtfn _ _)

theorem pz_schedContextBindTcb (scPtr tcbPtr : ObjRef) : PZK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextBindTcb _ _)

theorem pz_schedContextYieldTo (scPtr : ObjRef) : PZK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedContextYieldTo _)

theorem pz_invokeSchedContext (iv : SchedContextInvocation) : PZK (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeSchedContext _)

theorem pz_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : PZKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_installTcbCap _ _ _ _)

theorem pz_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : PZKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_installTcbFrameCap _ _ _)

theorem pz_setFlags (ref : ObjRef) (flags : TcbFlags) : PZK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setFlags _ _)

theorem pz_setMcpriority (ref : ObjRef) (mcp : Priority) : PZK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setMcpriority _ _)

theorem pz_reorderEp (epPtr tptr : ObjRef) : PZK (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_reorderEp _ _)

theorem pz_reorderNtfn (ntfnPtr tptr : ObjRef) : PZK (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_reorderNtfn _ _)

theorem pz_threadSetPriority (tptr : ObjRef) (prio : Priority) : PZK (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_threadSetPriority _ _)

theorem pz_setPriority (tptr : ObjRef) (prio : Priority) : PZK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setPriority _ _)

theorem pz_invokeTcb (a0 : TcbInvocation) : PZKE (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeTcb _)

theorem pz_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : PZK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4ReplyFromKernelError _ _ _)

theorem pz_handleNoFault (tptr : ObjRef) : PZK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleNoFault _)

theorem pz_handleFault (thread : ObjRef) (ex : Fault) : PZK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleFault _ _)

theorem pz_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : PZKE mFault) (h_hFault : ∀ x0, PZK (hFault x0)) (h_mError : ∀ x0, PZKE (mError x0)) (h_hError : ∀ x0, PZK (hError x0)) (h_mFinalise : ∀ x0, PZKE (mFinalise x0)) : PZKE (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; pz_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem pz_getCapReg (reg : Register) : PZK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getCapReg _)

theorem pz_lookupReply  : PZKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lookupReply)

theorem pz_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : PZK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_maybeReturnSc _ _)

theorem pz_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : PZK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem pz_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    PZK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_receiveIpc _ _ _ _)

theorem pz_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : PZK (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbNtfnAppend _ _)

theorem pz_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : PZK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_receiveSignalBlocked _ _ _)

theorem pz_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : PZK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_receiveSignal _ _ _)

theorem pz_handleRecv (isBlocking canReply : Bool) : PZK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleRecv _ _)

theorem pz_handleYield  : PZK (handleYield (Z := Unit)) := by
  unfold handleYield; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleYield)

theorem pz_invokeUntyped (ui : UntypedInvocation) : PZKE (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invokeUntyped _)

theorem pz_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : PZK (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleHypervisorFault _ _)

theorem pz_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : PZKE (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleVmFault _ _)

theorem pz_handleReservedIrq (_irq : Irq) : PZK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleReservedIrq _)

theorem pz_handleInterrupt (irq : Irq) : PZK (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleInterrupt _)

theorem pz_handleSpuriousIrq  : PZK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleSpuriousIrq)

theorem pz_maybeHandleInterrupt (inKernel : Bool) : PZK (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_maybeHandleInterrupt _)

theorem pz_preemptionPath  : PZK (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_preemptionPath)

theorem pz_fl4SyscallFaultIP (thread : ObjRef) : PZK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvE
