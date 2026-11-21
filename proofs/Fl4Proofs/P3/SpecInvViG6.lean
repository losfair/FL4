
/- vi1: generated frames `IK (VIT N S T b)` (sg1's SpecInvSgI6 renamed, the idle-relevant writers removed; see SpecInvViG1). -/
import Fl4Proofs.P3.SpecInvViG5
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem vi_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    IKE (VIT N S T b) (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem vi_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : IKE (VIT N S T b) (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem vi_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : IK (VIT N S T b) (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_initArchObjects _ _ _ _ _ _)

theorem vi_threadSetDomain (tptr : ObjRef) (domain : Domain) : IK (VIT N S T b) (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_threadSetDomain _ _)

theorem vi_setDomain (tptr : ObjRef) (newDom : Domain) : IK (VIT N S T b) (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setDomain _ _)

theorem vi_invokeSetDomain (thread : ObjRef) (domain : Domain) : IK (VIT N S T b) (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeSetDomain _ _)

theorem vi_invokeDomain (domInv : DomainInvocation) : IK (VIT N S T b) (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeDomain _)

theorem vi_invokeIrqControl (a0 : IrqControlInvocation) : IKE (VIT N S T b) (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeIrqControl _)

theorem vi_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IKE (VIT N S T b) (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeFl4IrqControl _)

theorem vi_invokeFl4Tcb (a0 : Fl4TcbInvocation) : IKE (VIT N S T b) (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeFl4Tcb _)

theorem vi_returnConsumed (scPtr : ObjRef) : IK (VIT N S T b) (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_returnConsumed _)

theorem vi_schedContextBindNtfn (sc ntfn : ObjRef) : IK (VIT N S T b) (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextBindNtfn _ _)

theorem vi_maybeAddEmptyTail (scPtr : ObjRef) : IK (VIT N S T b) (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_maybeAddEmptyTail _)

theorem vi_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : IK (VIT N S T b) (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillNew _ _ _ _)

theorem vi_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : IK (VIT N S T b) (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillUpdate _ _ _ _)

theorem vi_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : IK (VIT N S T b) (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invokeSchedControlConfigureFlags _)

theorem vi_setFlags (ref : ObjRef) (flags : TcbFlags) : IK (VIT N S T b) (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setFlags _ _)

theorem vi_setMcpriority (ref : ObjRef) (mcp : Priority) : IK (VIT N S T b) (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setMcpriority _ _)

theorem vi_threadSetPriority (tptr : ObjRef) (prio : Priority) : IK (VIT N S T b) (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_threadSetPriority _ _)

theorem vi_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : IK (VIT N S T b) (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4ReplyFromKernelError _ _ _)

theorem vi_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : IKE (VIT N S T b) mFault) (h_hFault : ∀ x0, IK (VIT N S T b) (hFault x0)) (h_mError : ∀ x0, IKE (VIT N S T b) (mError x0)) (h_hError : ∀ x0, IK (VIT N S T b) (hError x0)) (h_mFinalise : ∀ x0, IKE (VIT N S T b) (mFinalise x0)) : IKE (VIT N S T b) (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; vi_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem vi_getCapReg (reg : Register) : IK (VIT N S T b) (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getCapReg _)

theorem vi_lookupReply  : IKE (VIT N S T b) (lookupReply (Z := Unit)) := by
  unfold lookupReply; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lookupReply)

theorem vi_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : IK (VIT N S T b) (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleHypervisorFault _ _)

theorem vi_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : IKE (VIT N S T b) (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleVmFault _ _)

theorem vi_handleReservedIrq (_irq : Irq) : IK (VIT N S T b) (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleReservedIrq _)

theorem vi_handleSpuriousIrq  : IK (VIT N S T b) (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleSpuriousIrq)

theorem vi_fl4SyscallFaultIP (thread : ObjRef) : IK (VIT N S T b) (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvI
