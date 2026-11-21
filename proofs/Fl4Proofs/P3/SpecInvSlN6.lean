/- sl2: NtfnScB family lemmas, part 6 (generated; see SpecInvSlN1). -/
import Fl4Proofs.P3.SpecInvSlN5
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem nb_schedule  : NBK (schedule (Z := Unit)) := by
  unfold schedule; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedule)

theorem nb_domainSetStart (index : Nat) : NBK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_domainSetStart _)

theorem nb_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NBKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem nb_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NBKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem nb_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NBKE (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem nb_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NBK (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ReplyFromKernelError _ _ _)

theorem nb_fl4SyscallFaultIP (thread : ObjRef) : NBK (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4SyscallFaultIP _)

theorem nb_getCapReg (reg : Register) : NBK (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getCapReg _)

theorem nb_handleNoFault (tptr : ObjRef) : NBK (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleNoFault _)

theorem nb_handleFault (thread : ObjRef) (ex : Fault) : NBK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleFault _ _)

theorem nb_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NBK (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleHypervisorFault _ _)

theorem nb_handleReservedIrq (_irq : Irq) : NBK (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleReservedIrq _)

theorem nb_handleSpuriousIrq  : NBK (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleSpuriousIrq)

theorem nb_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NBKE (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleVmFault _ _)

theorem nb_handleYield  : NBK (handleYield (Z := Unit)) := by
  unfold handleYield; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleYield)

theorem nb_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NBK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_initArchObjects _ _ _ _ _ _)

theorem nb_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : NBKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_installTcbCap _ _ _ _)

theorem nb_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : NBKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_installTcbFrameCap _ _ _)

theorem nb_invokeCnode (i : CnodeInvocation) : NBKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeCnode _)

theorem nb_threadSetDomain (tptr : ObjRef) (domain : Domain) : NBK (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadSetDomain _ _)

theorem nb_setDomain (tptr : ObjRef) (newDom : Domain) : NBK (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setDomain _ _)

theorem nb_invokeSetDomain (thread : ObjRef) (domain : Domain) : NBK (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeSetDomain _ _)

theorem nb_invokeDomain (domInv : DomainInvocation) : NBK (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeDomain _)

theorem nb_invokeIrqControl (a0 : IrqControlInvocation) : NBKE (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeIrqControl _)

theorem nb_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NBKE (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeFl4IrqControl _)

theorem nb_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NBKE (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeFl4Tcb _)

theorem nb_invokeIrqHandler (a0 : IrqHandlerInvocation) : NBK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeIrqHandler _)

theorem nb_maybeAddEmptyTail (scPtr : ObjRef) : NBK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeAddEmptyTail _)

theorem nb_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NBK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillNew _ _ _ _)

theorem nb_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NBK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillUpdate _ _ _ _)

theorem nb_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NBK (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeSchedControlConfigureFlags _)

theorem nb_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NBK (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextBindTcb _ _)

theorem nb_setFlags (ref : ObjRef) (flags : TcbFlags) : NBK (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setFlags _ _)

theorem nb_setMcpriority (ref : ObjRef) (mcp : Priority) : NBK (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setMcpriority _ _)

theorem nb_reorderEp (epPtr tptr : ObjRef) : NBK (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_reorderEp _ _)

theorem nb_threadSetPriority (tptr : ObjRef) (prio : Priority) : NBK (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_threadSetPriority _ _)

theorem nb_setPriority (tptr : ObjRef) (prio : Priority) : NBK (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPriority _ _)

theorem nb_invokeTcb (a0 : TcbInvocation) : NBKE (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invokeTcb _)

theorem nb_lookupReply  : NBKE (lookupReply (Z := Unit)) := by
  unfold lookupReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lookupReply)

theorem nb_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : NBK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeDonateSc _ _)

theorem nb_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NBK (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_maybeReturnSc _ _)

theorem nb_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NBK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storeAsidPoolEntry _ _ _)

theorem nb_performAsidPoolInvocation (iv : AsidPoolInvocation) : NBK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performAsidPoolInvocation _)

theorem nb_performDeriveSubframe (iv : Fl4SubframeInvocation) : NBK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performDeriveSubframe _)

theorem nb_portIn (f : MachineMonad Data) : NBK (portIn (Z := Unit) f) := by
  unfold portIn; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_portIn _)

theorem nb_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NBK (portOut (Z := Unit) f w) := by
  unfold portOut; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_portOut _ _)

theorem nb_performIoPortInvocation (i : IoPortInvocation) : NBK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performIoPortInvocation _)

theorem nb_performIoportControlInvocation (i : IoPortControlInvocation) : NBK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performIoportControlInvocation _)

theorem nb_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NBK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageDirectoryInvocation _)

theorem nb_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NBK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageInvocationUnmap _ _)

theorem nb_performPageInvocation (iv : PageInvocation) : NBK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageInvocation _)

theorem nb_performPageTableInvocation (iv : PageTableInvocation) : NBK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPageTableInvocation _)

theorem nb_performPdptInvocation (iv : PdptInvocation) : NBK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPdptInvocation _)

theorem nb_performPml4Flush (a0 : Fl4Pml4Invocation) : NBK (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performPml4Flush _)

theorem nb_performTestAndClearAccessed (_slot : ObjRef) : NBK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_performTestAndClearAccessed _)

theorem nb_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : NBK (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_receiveIpcBlocked _ _ _ _)

theorem nb_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : NBK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_receiveSignalBlocked _ _ _)

theorem nb_returnConsumed (scPtr : ObjRef) : NBK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_returnConsumed _)

theorem nb_schedContextYieldTo (scPtr : ObjRef) : NBK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextYieldTo _)

theorem nb_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NBKE mFault) (h_hFault : ∀ x0, NBK (hFault x0)) (h_mError : ∀ x0, NBKE (mError x0)) (h_hError : ∀ x0, NBK (hError x0)) (h_mFinalise : ∀ x0, NBKE (mFinalise x0)) : NBKE (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; nb_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem nb_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : NBK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateWaitingNtfn _ _ _)

end

end Fl4Proofs.P3.SInvL
