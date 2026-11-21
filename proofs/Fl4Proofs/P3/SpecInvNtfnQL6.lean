/- il1: IfLiveT family lemmas, part 6 (generated; see SpecInvNtfnQL1). -/
import Fl4Proofs.P3.SpecInvNtfnQL5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem il_schedContextUnbindTcb (scPtr : ObjRef) : ILK Kq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextUnbindTcb _)

theorem il_schedContextUnbindAllTcbs (scPtr : ObjRef) : ILK Kq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextUnbindAllTcbs _)

theorem il_schedContextUnbindNtfn (scPtr : ObjRef) : ILK Kq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextUnbindNtfn _)

theorem il_schedContextUnbindReply (scPtr : ObjRef) : ILK Kq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextUnbindReply _)

theorem il_schedContextYieldTo (scPtr : ObjRef) : ILK Kq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextYieldTo _)

theorem il_invokeSchedContext (iv : SchedContextInvocation) : ILK Kq (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeSchedContext _)

theorem il_maybeAddEmptyTail (scPtr : ObjRef) : ILK Kq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_maybeAddEmptyTail _)

theorem il_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : ILK Kq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillNew _ _ _ _)

theorem il_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : ILK Kq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillUpdate _ _ _ _)

theorem il_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : ILK Kq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeSchedControlConfigureFlags _)

theorem il_isValidTimeoutHandler (tptr : ObjRef) : ILK Kq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_isValidTimeoutHandler _)

theorem il_lookupReply  : ILKE Kq (lookupReply (Z := Unit)) := by
  unfold lookupReply; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupReply)

theorem il_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : ILK Kq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_maybeReturnSc _ _)

theorem il_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : ILKE Kq f) (h_g : ILKE Kq g) : ILKE Kq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; il_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_orChoiceE _ _ _ ?_ ?_)

theorem il_portIn (f : MachineMonad Data) : ILK Kq (portIn (Z := Unit) f) := by
  unfold portIn; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_portIn _)

theorem il_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : ILK Kq (portOut (Z := Unit) f w) := by
  unfold portOut; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_portOut _ _)

theorem il_performIoPortInvocation (i : IoPortInvocation) : ILK Kq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_performIoPortInvocation _)

theorem il_performIoportControlInvocation (i : IoPortControlInvocation) : ILK Kq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_performIoportControlInvocation _)

theorem il_performPml4Flush (a0 : Fl4Pml4Invocation) : ILK Kq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_performPml4Flush _)

theorem il_performTestAndClearAccessed (_slot : ObjRef) : ILK Kq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_performTestAndClearAccessed _)

theorem il_postCapDeletion (cap : Cap) : ILK Kq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_postCapDeletion _)

theorem il_updateTimeStamp  : ILK Kq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateTimeStamp)

theorem il_preemptionPoint  : ILKE Kq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_preemptionPoint)

theorem il_prepareThreadDelete (threadPtr : ObjRef) : ILK Kq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_prepareThreadDelete _)

theorem il_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : ILK Kq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbAppend _ _)

theorem il_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : ILK Kq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbEpAppend _ _ _)

theorem il_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) (hk_thread : thread ∈ Kq) : ILK Kq (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_receiveIpcBlocked _ _ _ _ ?_) <;> nq_mem))

theorem il_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : ILK Kq (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbNtfnAppend _ _)

theorem il_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) (hk_thread : thread ∈ Kq) : ILK Kq (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_receiveSignalBlocked _ _ _ ?_) <;> nq_mem))

theorem il_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (hk_thread : thread ∈ Kq) : ILK Kq (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_receiveSignal _ _ _ ?_) <;> nq_mem))

theorem il_refillResetRr (cscPtr : ObjRef) : ILK Kq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_refillResetRr _)

theorem il_restartThreadIfNoFault (t : ObjRef) (hk_t : t ∈ Kq) : ILK Kq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_restartThreadIfNoFault _ ?_) <;> nq_mem))

theorem il_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) (hk_t : t ∈ Kq) : ILK Kq (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_removeAndRestartBadgedThread _ _ _ ?_) <;> nq_mem))

theorem il_removeAndRestartEpQueuedThread (t epptr : ObjRef) (hk_t : t ∈ Kq) : ILK Kq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_removeAndRestartEpQueuedThread _ _ ?_) <;> nq_mem))

theorem il_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) (hk_t : t ∈ Kq) : ILK Kq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_removeAndRestartNtfnQueuedThread _ _ ?_) <;> nq_mem))

theorem il_reorderEp (epPtr tptr : ObjRef) : ILK Kq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_reorderEp _ _)

theorem il_reorderNtfn (ntfnPtr tptr : ObjRef) : ILK Kq (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_reorderNtfn _ _)

theorem il_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) (hk_caller : caller ∈ Kq) : ILK Kq (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_replyPush _ _ _ _ ?_) <;> nq_mem))

theorem il_replyUnlinkSc (scPtr replyPtr : ObjRef) : ILK Kq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_replyUnlinkSc _ _)

theorem il_replyRemove (caller r : ObjRef) : ILK Kq (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_replyRemove _ _)

theorem il_testPossibleSwitchTo (tcbPtr : ObjRef) : ILK Kq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_testPossibleSwitchTo _)

theorem il_restart (thread : ObjRef) (hk_thread : thread ∈ Kq) : ILK Kq (restart (Z := Unit) thread) := by
  unfold restart; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_restart _ ?_) <;> nq_mem))

theorem il_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : ILK Kq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextMaybeUnbindNtfn _)

theorem il_schedContextSetInactive (scPtr : ObjRef) : ILK Kq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextSetInactive _)

theorem il_schedContextUnbindYieldFrom (scPtr : ObjRef) : ILK Kq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextUnbindYieldFrom _)

theorem il_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) (hk_thread : thread ∈ Kq) : ILK Kq (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| ((with_reducible refine il_sendIpcBlocked _ _ _ _ _ _ ?_) <;> nq_mem))

theorem il_setFlags (ref : ObjRef) (flags : TcbFlags) : ILK Kq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setFlags _ _)

theorem il_setMcpriority (ref : ObjRef) (mcp : Priority) : ILK Kq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setMcpriority _ _)

theorem il_threadSetPriority (tptr : ObjRef) (prio : Priority) : ILK Kq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_threadSetPriority _ _)

theorem il_setPriority (tptr : ObjRef) (prio : Priority) : ILK Kq (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setPriority _ _)

theorem il_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : ILK Kq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_storeAsidPoolEntry _ _ _)

theorem il_updateRestartPc (threadPtr : ObjRef) : ILK Kq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateRestartPc _)

theorem il_suspend (thread : ObjRef) : ILK Kq (suspend (Z := Unit) thread) := by
  unfold suspend; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_suspend _)

theorem il_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : ILKE Kq mFault) (h_hFault : ∀ x0, ILK Kq (hFault x0)) (h_mError : ∀ x0, ILKE Kq (mError x0)) (h_hError : ∀ x0, ILK Kq (hError x0)) (h_mFinalise : ∀ x0, ILKE Kq (mFinalise x0)) : ILKE Kq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; il_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem il_unbindFromSc (tcbPtr : ObjRef) : ILK Kq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unbindFromSc _)

theorem il_unbindMaybeNotification (ntfnptr : ObjRef) : ILK Kq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unbindMaybeNotification _)

theorem il_unbindNotification (tcb : ObjRef) : ILK Kq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unbindNotification _)

end

end Fl4Proofs.P3.SInv
