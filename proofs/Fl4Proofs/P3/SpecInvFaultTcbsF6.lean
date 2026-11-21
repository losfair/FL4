/- invA2: FaultTcbsS frame lemmas, part 6 (generated; see SpecInvFaultTcbsF1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsF5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem ft_handleNoFault (tptr : ObjRef) : FTK L (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleNoFault _)

theorem ft_handleReservedIrq (_irq : Irq) : FTK L (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleReservedIrq _)

theorem ft_handleSpuriousIrq  : FTK L (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleSpuriousIrq)

theorem ft_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : FTKE L (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleVmFault _ _)

theorem ft_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : FTK L (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_initArchObjects _ _ _ _ _ _)

theorem ft_threadSetDomain (tptr : ObjRef) (domain : Domain) : FTK L (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadSetDomain _ _)

theorem ft_setDomain (tptr : ObjRef) (newDom : Domain) : FTK L (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setDomain _ _)

theorem ft_invokeSetDomain (thread : ObjRef) (domain : Domain) : FTK L (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSetDomain _ _)

theorem ft_invokeDomain (domInv : DomainInvocation) : FTK L (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeDomain _)

theorem ft_invokeIrqControl (a0 : IrqControlInvocation) : FTKE L (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeIrqControl _)

theorem ft_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : FTKE L (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeFl4IrqControl _)

theorem ft_invokeFl4Tcb (a0 : Fl4TcbInvocation) : FTKE L (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeFl4Tcb _)

theorem ft_returnConsumed (scPtr : ObjRef) : FTK L (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_returnConsumed _)

theorem ft_schedContextBindNtfn (sc ntfn : ObjRef) : FTK L (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextBindNtfn _ _)

theorem ft_schedContextBindTcb (scPtr tcbPtr : ObjRef) : FTK L (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextBindTcb _ _)

theorem ft_schedContextUnbindTcb (scPtr : ObjRef) : FTK L (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindTcb _)

theorem ft_schedContextUnbindAllTcbs (scPtr : ObjRef) : FTK L (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindAllTcbs _)

theorem ft_schedContextUnbindNtfn (scPtr : ObjRef) : FTK L (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindNtfn _)

theorem ft_schedContextUnbindReply (scPtr : ObjRef) : FTK L (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindReply _)

theorem ft_schedContextYieldTo (scPtr : ObjRef) : FTK L (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextYieldTo _)

theorem ft_invokeSchedContext (iv : SchedContextInvocation) : FTK L (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSchedContext _)

theorem ft_maybeAddEmptyTail (scPtr : ObjRef) : FTK L (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeAddEmptyTail _)

theorem ft_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : FTK L (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillNew _ _ _ _)

theorem ft_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : FTK L (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillUpdate _ _ _ _)

theorem ft_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : FTK L (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeSchedControlConfigureFlags _)

theorem ft_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : FTKE L f) (h_g : FTKE L g) : FTKE L (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ft_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_orChoiceE _ _ _ ?_ ?_)

theorem ft_updateTimeStamp  : FTK L (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateTimeStamp)

theorem ft_preemptionPoint  : FTKE L (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_preemptionPoint)

theorem ft_resetUntypedCap (srcSlot : CslotPtr) : FTKE L (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resetUntypedCap _)

theorem ft_invokeUntyped (ui : UntypedInvocation) : FTKE L (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeUntyped _)

theorem ft_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : FTKE L (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invokeUntypedWith _ _)

theorem ft_isValidTimeoutHandler (tptr : ObjRef) : FTK L (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isValidTimeoutHandler _)

theorem ft_lookupReply  : FTKE L (lookupReply (Z := Unit)) := by
  unfold lookupReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupReply)

theorem ft_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : FTK L (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_maybeReturnSc _ _)

theorem ft_prepareThreadDelete (threadPtr : ObjRef) : FTK L (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_prepareThreadDelete _)

theorem ft_refillResetRr (cscPtr : ObjRef) : FTK L (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillResetRr _)

theorem ft_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : FTK L (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbAppend _ _)

theorem ft_reorderEp (epPtr tptr : ObjRef) : FTK L (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_reorderEp _ _)

theorem ft_reorderNtfn (ntfnPtr tptr : ObjRef) : FTK L (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_reorderNtfn _ _)

theorem ft_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : FTK L (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyPush _ _ _ _)

theorem ft_replyUnlinkSc (scPtr replyPtr : ObjRef) : FTK L (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyUnlinkSc _ _)

theorem ft_replyRemove (caller r : ObjRef) : FTK L (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyRemove _ _)

theorem ft_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : FTK L (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextMaybeUnbindNtfn _)

theorem ft_schedContextSetInactive (scPtr : ObjRef) : FTK L (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextSetInactive _)

theorem ft_schedContextUnbindYieldFrom (scPtr : ObjRef) : FTK L (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUnbindYieldFrom _)

theorem ft_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : FTK L (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbEpAppend _ _ _)

theorem ft_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : FTK L (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_sendIpcBlocked _ _ _ _ _ _)

theorem ft_setFlags (ref : ObjRef) (flags : TcbFlags) : FTK L (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setFlags _ _)

theorem ft_setMcpriority (ref : ObjRef) (mcp : Priority) : FTK L (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setMcpriority _ _)

theorem ft_threadSetPriority (tptr : ObjRef) (prio : Priority) : FTK L (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadSetPriority _ _)

theorem ft_setPriority (tptr : ObjRef) (prio : Priority) : FTK L (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPriority _ _)

theorem ft_updateRestartPc (threadPtr : ObjRef) : FTK L (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateRestartPc _)

theorem ft_suspend (thread : ObjRef) : FTK L (suspend (Z := Unit) thread) := by
  unfold suspend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_suspend _)

theorem ft_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : FTKE L mFault) (h_hFault : ∀ x0, FTK L (hFault x0)) (h_mError : ∀ x0, FTKE L (mError x0)) (h_hError : ∀ x0, FTK L (hError x0)) (h_mFinalise : ∀ x0, FTKE L (mFinalise x0)) : FTKE L (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ft_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ft_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : FTK L (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbNtfnAppend _ _)

theorem ft_testPossibleSwitchTo (tcbPtr : ObjRef) : FTK L (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_testPossibleSwitchTo _)

theorem ft_unbindFromSc (tcbPtr : ObjRef) : FTK L (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindFromSc _)

theorem ft_unbindMaybeNotification (ntfnptr : ObjRef) : FTK L (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindMaybeNotification _)

theorem ft_unbindNotification (tcb : ObjRef) : FTK L (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unbindNotification _)

end

end Fl4Proofs.P3.SInv
