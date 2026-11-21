/- ft2: generic frame lemmas, part 6 (generated; see SpecInvFaultTcbsG1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsG5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Fq : FQ} {Sq : Set ObjRef} {Cq : ObjRef → Prop}

theorem fg_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : FGK Fq Sq Cq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleFaultReply _ _ _ _)

theorem fg_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : FGK Fq Sq Cq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleHypervisorFault _ _)

theorem fg_handleNoFault (tptr : ObjRef) : FGK Fq Sq Cq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleNoFault _)

theorem fg_handleReservedIrq (_irq : Irq) : FGK Fq Sq Cq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleReservedIrq _)

theorem fg_handleSpuriousIrq  : FGK Fq Sq Cq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleSpuriousIrq)

theorem fg_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : FGKE Fq Sq Cq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleVmFault _ _)

theorem fg_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : FGK Fq Sq Cq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_initArchObjects _ _ _ _ _ _)

theorem fg_threadSetDomain (tptr : ObjRef) (domain : Domain) : FGK Fq Sq Cq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadSetDomain _ _)

theorem fg_setDomain (tptr : ObjRef) (newDom : Domain) : FGK Fq Sq Cq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setDomain _ _)

theorem fg_invokeSetDomain (thread : ObjRef) (domain : Domain) : FGK Fq Sq Cq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSetDomain _ _)

theorem fg_invokeDomain (domInv : DomainInvocation) : FGK Fq Sq Cq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeDomain _)

theorem fg_invokeIrqControl (a0 : IrqControlInvocation) : FGKE Fq Sq Cq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeIrqControl _)

theorem fg_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : FGKE Fq Sq Cq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeFl4IrqControl _)

theorem fg_invokeFl4Tcb (a0 : Fl4TcbInvocation) : FGKE Fq Sq Cq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeFl4Tcb _)

theorem fg_returnConsumed (scPtr : ObjRef) : FGK Fq Sq Cq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_returnConsumed _)

theorem fg_schedContextBindNtfn (sc ntfn : ObjRef) : FGK Fq Sq Cq (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextBindNtfn _ _)

theorem fg_schedContextBindTcb (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextBindTcb _ _)

theorem fg_schedContextUnbindTcb (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindTcb _)

theorem fg_schedContextUnbindAllTcbs (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindAllTcbs _)

theorem fg_schedContextUnbindNtfn (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindNtfn _)

theorem fg_schedContextUnbindReply (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindReply _)

theorem fg_schedContextYieldTo (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextYieldTo _)

theorem fg_invokeSchedContext (iv : SchedContextInvocation) : FGK Fq Sq Cq (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSchedContext _)

theorem fg_maybeAddEmptyTail (scPtr : ObjRef) : FGK Fq Sq Cq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeAddEmptyTail _)

theorem fg_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : FGK Fq Sq Cq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillNew _ _ _ _)

theorem fg_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : FGK Fq Sq Cq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillUpdate _ _ _ _)

theorem fg_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : FGK Fq Sq Cq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeSchedControlConfigureFlags _)

theorem fg_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : FGKE Fq Sq Cq f) (h_g : FGKE Fq Sq Cq g) : FGKE Fq Sq Cq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; fg_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_orChoiceE _ _ _ ?_ ?_)

theorem fg_updateTimeStamp  : FGK Fq Sq Cq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateTimeStamp)

theorem fg_preemptionPoint  : FGKE Fq Sq Cq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_preemptionPoint)

theorem fg_resetUntypedCap (srcSlot : CslotPtr) : FGKE Fq Sq Cq (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_resetUntypedCap _)

theorem fg_invokeUntyped (ui : UntypedInvocation) : FGKE Fq Sq Cq (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeUntyped _)

theorem fg_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : FGKE Fq Sq Cq (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_invokeUntypedWith _ _)

theorem fg_isValidTimeoutHandler (tptr : ObjRef) : FGK Fq Sq Cq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isValidTimeoutHandler _)

theorem fg_lookupReply  : FGKE Fq Sq Cq (lookupReply (Z := Unit)) := by
  unfold lookupReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupReply)

theorem fg_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_maybeReturnSc _ _)

theorem fg_prepareThreadDelete (threadPtr : ObjRef) : FGK Fq Sq Cq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_prepareThreadDelete _)

theorem fg_refillResetRr (cscPtr : ObjRef) : FGK Fq Sq Cq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillResetRr _)

theorem fg_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : FGK Fq Sq Cq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbAppend _ _)

theorem fg_reorderEp (epPtr tptr : ObjRef) : FGK Fq Sq Cq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_reorderEp _ _)

theorem fg_replyUnlinkSc (scPtr replyPtr : ObjRef) : FGK Fq Sq Cq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyUnlinkSc _ _)

theorem fg_replyRemove (caller r : ObjRef) : FGK Fq Sq Cq (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyRemove _ _)

theorem fg_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : FGK Fq Sq Cq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextMaybeUnbindNtfn _)

theorem fg_schedContextSetInactive (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextSetInactive _)

theorem fg_schedContextUnbindYieldFrom (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUnbindYieldFrom _)

theorem fg_setFlags (ref : ObjRef) (flags : TcbFlags) : FGK Fq Sq Cq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setFlags _ _)

theorem fg_setMcpriority (ref : ObjRef) (mcp : Priority) : FGK Fq Sq Cq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setMcpriority _ _)

theorem fg_updateRestartPc (threadPtr : ObjRef) : FGK Fq Sq Cq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateRestartPc _)

theorem fg_suspend (thread : ObjRef) : FGK Fq Sq Cq (suspend (Z := Unit) thread) := by
  unfold suspend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_suspend _)

theorem fg_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : FGKE Fq Sq Cq mFault) (h_hFault : ∀ x0, FGK Fq Sq Cq (hFault x0)) (h_mError : ∀ x0, FGKE Fq Sq Cq (mError x0)) (h_hError : ∀ x0, FGK Fq Sq Cq (hError x0)) (h_mFinalise : ∀ x0, FGKE Fq Sq Cq (mFinalise x0)) : FGKE Fq Sq Cq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; fg_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem fg_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : FGK Fq Sq Cq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbEpAppend _ _ _)

theorem fg_testPossibleSwitchTo (tcbPtr : ObjRef) : FGK Fq Sq Cq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_testPossibleSwitchTo _)

theorem fg_threadSetPriority (tptr : ObjRef) (prio : Priority) : FGK Fq Sq Cq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadSetPriority _ _)

theorem fg_unbindFromSc (tcbPtr : ObjRef) : FGK Fq Sq Cq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindFromSc _)

theorem fg_unbindMaybeNotification (ntfnptr : ObjRef) : FGK Fq Sq Cq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindMaybeNotification _)

theorem fg_unbindNotification (tcb : ObjRef) : FGK Fq Sq Cq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unbindNotification _)

end

end Fl4Proofs.P3.SInv
