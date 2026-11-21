/- sl1: ScLive family lemmas, part 6 (generated; see SpecInvSlF1). -/
import Fl4Proofs.P3.SpecInvSlF5
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Iq : ObjRef × ObjRef} {Kq : List ObjRef}

theorem sl_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : SLK Iq Kq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillUpdate _ _ _ _)

theorem sl_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : SLK Iq Kq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_orderedInsert _ _ _ _)

theorem sl_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : SLK Iq Kq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_readyTimesAppend _ _)

theorem sl_tcbReleaseEnqueue (tcbPtr : ObjRef) : SLK Iq Kq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseEnqueue _)

theorem sl_postpone (scPtr : ObjRef) : SLK Iq Kq (postpone (Z := Unit) scPtr) := by
  unfold postpone; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_postpone _)

theorem sl_schedContextResume (scPtr : ObjRef) : SLK Iq Kq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextResume _)

theorem sl_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : SLK Iq Kq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeSchedControlConfigureFlags _)

theorem sl_isValidTimeoutHandler (tptr : ObjRef) : SLK Iq Kq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isValidTimeoutHandler _)

theorem sl_lookupReply  : SLKE Iq Kq (lookupReply (Z := Unit)) := by
  unfold lookupReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupReply)

theorem sl_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : SLK Iq Kq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_maybeReturnSc _ _)

theorem sl_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : SLKE Iq Kq f) (h_g : SLKE Iq Kq g) : SLKE Iq Kq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; sl_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_orChoiceE _ _ _ ?_ ?_)

theorem sl_portIn (f : MachineMonad Data) : SLK Iq Kq (portIn (Z := Unit) f) := by
  unfold portIn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_portIn _)

theorem sl_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : SLK Iq Kq (portOut (Z := Unit) f w) := by
  unfold portOut; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_portOut _ _)

theorem sl_performIoPortInvocation (i : IoPortInvocation) : SLK Iq Kq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performIoPortInvocation _)

theorem sl_performIoportControlInvocation (i : IoPortControlInvocation) : SLK Iq Kq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performIoportControlInvocation _)

theorem sl_performPml4Flush (a0 : Fl4Pml4Invocation) : SLK Iq Kq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performPml4Flush _)

theorem sl_performTestAndClearAccessed (_slot : ObjRef) : SLK Iq Kq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_performTestAndClearAccessed _)

theorem sl_postCapDeletion (cap : Cap) : SLK Iq Kq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_postCapDeletion _)

theorem sl_updateTimeStamp  : SLK Iq Kq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateTimeStamp)

theorem sl_preemptionPoint  : SLKE Iq Kq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_preemptionPoint)

theorem sl_prepareThreadDelete (threadPtr : ObjRef) : SLK Iq Kq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_prepareThreadDelete _)

theorem sl_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : SLK Iq Kq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbAppend _ _)

theorem sl_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : SLK Iq Kq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbEpAppend _ _ _)

theorem sl_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : SLK Iq Kq (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_receiveIpcBlocked _ _ _ _)

theorem sl_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : SLK Iq Kq (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbNtfnAppend _ _)

theorem sl_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : SLK Iq Kq (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_receiveSignalBlocked _ _ _)

theorem sl_refillResetRr (cscPtr : ObjRef) : SLK Iq Kq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillResetRr _)

theorem sl_reorderEp (epPtr tptr : ObjRef) : SLK Iq Kq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_reorderEp _ _)

theorem sl_reorderNtfn (ntfnPtr tptr : ObjRef) : SLK Iq Kq (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_reorderNtfn _ _)

theorem sl_replyUnlinkSc (scPtr replyPtr : ObjRef) : SLK Iq Kq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_replyUnlinkSc _ _)

theorem sl_testPossibleSwitchTo (tcbPtr : ObjRef) : SLK Iq Kq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_testPossibleSwitchTo _)

theorem sl_restart (thread : ObjRef) : SLK Iq Kq (restart (Z := Unit) thread) := by
  unfold restart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_restart _)

theorem sl_returnConsumed (scPtr : ObjRef) : SLK Iq Kq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_returnConsumed _)

theorem sl_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : SLK Iq Kq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextMaybeUnbindNtfn _)

theorem sl_schedContextSetInactive (scPtr : ObjRef) : SLK Iq Kq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextSetInactive _)

theorem sl_schedContextUnbindTcb (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindTcb _)

theorem sl_schedContextUnbindAllTcbs (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindAllTcbs _)

theorem sl_schedContextUnbindNtfn (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindNtfn _)

theorem sl_schedContextUnbindReply (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindReply _)

theorem sl_schedContextUnbindYieldFrom (scPtr : ObjRef) : SLK Iq Kq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextUnbindYieldFrom _)

theorem sl_schedContextYieldTo (scPtr : ObjRef) : SLK Iq Kq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedContextYieldTo _)

theorem sl_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : SLK Iq Kq (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_sendIpcBlocked _ _ _ _ _ _)

theorem sl_setFlags (ref : ObjRef) (flags : TcbFlags) : SLK Iq Kq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setFlags _ _)

theorem sl_setMcpriority (ref : ObjRef) (mcp : Priority) : SLK Iq Kq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setMcpriority _ _)

theorem sl_threadSetPriority (tptr : ObjRef) (prio : Priority) : SLK Iq Kq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_threadSetPriority _ _)

theorem sl_setPriority (tptr : ObjRef) (prio : Priority) : SLK Iq Kq (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPriority _ _)

theorem sl_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : SLK Iq Kq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storeAsidPoolEntry _ _ _)

theorem sl_updateRestartPc (threadPtr : ObjRef) : SLK Iq Kq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateRestartPc _)

theorem sl_suspend (thread : ObjRef) : SLK Iq Kq (suspend (Z := Unit) thread) := by
  unfold suspend; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_suspend _)

theorem sl_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : SLKE Iq Kq mFault) (h_hFault : ∀ x0, SLK Iq Kq (hFault x0)) (h_mError : ∀ x0, SLKE Iq Kq (mError x0)) (h_hError : ∀ x0, SLK Iq Kq (hError x0)) (h_mFinalise : ∀ x0, SLKE Iq Kq (mFinalise x0)) : SLKE Iq Kq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; sl_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem sl_testReschedule (fromTptr : ObjRef) : SLK Iq Kq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_testReschedule _)

theorem sl_unbindFromSc (tcbPtr : ObjRef) : SLK Iq Kq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindFromSc _)

theorem sl_unbindMaybeNotification (ntfnptr : ObjRef) : SLK Iq Kq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindMaybeNotification _)

theorem sl_unbindNotification (tcb : ObjRef) : SLK Iq Kq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unbindNotification _)

end

end Fl4Proofs.P3.SInvL
