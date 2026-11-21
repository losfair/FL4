/- nq1: NtfnQB family lemmas, part 6 (generated; see SpecInvNtfnQF1). -/
import Fl4Proofs.P3.SpecInvNtfnQF5
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_invokeSetDomain (thread : ObjRef) (domain : Domain) : NQK Kq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeSetDomain _ _)

theorem nq_invokeDomain (domInv : DomainInvocation) : NQK Kq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeDomain _)

theorem nq_invokeIrqControl (a0 : IrqControlInvocation) : NQKE Kq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeIrqControl _)

theorem nq_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : NQKE Kq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeFl4IrqControl _)

theorem nq_invokeFl4Tcb (a0 : Fl4TcbInvocation) : NQKE Kq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeFl4Tcb _)

theorem nq_returnConsumed (scPtr : ObjRef) : NQK Kq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_returnConsumed _)

theorem nq_schedContextBindNtfn (sc ntfn : ObjRef) : NQK Kq (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextBindNtfn _ _)

theorem nq_schedContextBindTcb (scPtr tcbPtr : ObjRef) : NQK Kq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextBindTcb _ _)

theorem nq_schedContextUnbindTcb (scPtr : ObjRef) : NQK Kq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUnbindTcb _)

theorem nq_schedContextUnbindAllTcbs (scPtr : ObjRef) : NQK Kq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUnbindAllTcbs _)

theorem nq_schedContextUnbindNtfn (scPtr : ObjRef) : NQK Kq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUnbindNtfn _)

theorem nq_schedContextUnbindReply (scPtr : ObjRef) : NQK Kq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUnbindReply _)

theorem nq_schedContextYieldTo (scPtr : ObjRef) : NQK Kq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextYieldTo _)

theorem nq_invokeSchedContext (iv : SchedContextInvocation) : NQK Kq (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeSchedContext _)

theorem nq_maybeAddEmptyTail (scPtr : ObjRef) : NQK Kq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_maybeAddEmptyTail _)

theorem nq_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : NQK Kq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillNew _ _ _ _)

theorem nq_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : NQK Kq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillUpdate _ _ _ _)

theorem nq_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : NQK Kq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_invokeSchedControlConfigureFlags _)

theorem nq_isValidTimeoutHandler (tptr : ObjRef) : NQK Kq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_isValidTimeoutHandler _)

theorem nq_lookupReply  : NQKE Kq (lookupReply (Z := Unit)) := by
  unfold lookupReply; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupReply)

theorem nq_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : NQK Kq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_maybeReturnSc _ _)

theorem nq_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : NQKE Kq f) (h_g : NQKE Kq g) : NQKE Kq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; nq_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_orChoiceE _ _ _ ?_ ?_)

theorem nq_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NQK Kq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_storeAsidPoolEntry _ _ _)

theorem nq_performAsidPoolInvocation (iv : AsidPoolInvocation) : NQK Kq (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performAsidPoolInvocation _)

theorem nq_performDeriveSubframe (iv : Fl4SubframeInvocation) : NQK Kq (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performDeriveSubframe _)

theorem nq_portIn (f : MachineMonad Data) : NQK Kq (portIn (Z := Unit) f) := by
  unfold portIn; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_portIn _)

theorem nq_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NQK Kq (portOut (Z := Unit) f w) := by
  unfold portOut; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_portOut _ _)

theorem nq_performIoPortInvocation (i : IoPortInvocation) : NQK Kq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performIoPortInvocation _)

theorem nq_performIoportControlInvocation (i : IoPortControlInvocation) : NQK Kq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performIoportControlInvocation _)

theorem nq_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NQK Kq (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPageDirectoryInvocation _)

theorem nq_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NQK Kq (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPageInvocationUnmap _ _)

theorem nq_performPageInvocation (iv : PageInvocation) : NQK Kq (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPageInvocation _)

theorem nq_performPageTableInvocation (iv : PageTableInvocation) : NQK Kq (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPageTableInvocation _)

theorem nq_performPdptInvocation (iv : PdptInvocation) : NQK Kq (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPdptInvocation _)

theorem nq_performPml4Flush (a0 : Fl4Pml4Invocation) : NQK Kq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performPml4Flush _)

theorem nq_performTestAndClearAccessed (_slot : ObjRef) : NQK Kq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_performTestAndClearAccessed _)

theorem nq_updateTimeStamp  : NQK Kq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateTimeStamp)

theorem nq_preemptionPoint  : NQKE Kq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_preemptionPoint)

theorem nq_prepareThreadDelete (threadPtr : ObjRef) : NQK Kq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_prepareThreadDelete _)

theorem nq_refillResetRr (cscPtr : ObjRef) : NQK Kq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_refillResetRr _)

theorem nq_replyUnlinkSc (scPtr replyPtr : ObjRef) : NQK Kq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_replyUnlinkSc _ _)

theorem nq_replyRemove (caller r : ObjRef) (hk_caller : caller ∈ Kq) : NQK Kq (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_replyRemove _ _ ?_) <;> nq_mem))

theorem nq_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : NQK Kq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextMaybeUnbindNtfn _)

theorem nq_schedContextSetInactive (scPtr : ObjRef) : NQK Kq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextSetInactive _)

theorem nq_schedContextUnbindYieldFrom (scPtr : ObjRef) : NQK Kq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUnbindYieldFrom _)

theorem nq_setFlags (ref : ObjRef) (flags : TcbFlags) : NQK Kq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setFlags _ _)

theorem nq_setMcpriority (ref : ObjRef) (mcp : Priority) : NQK Kq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setMcpriority _ _)

theorem nq_updateRestartPc (threadPtr : ObjRef) : NQK Kq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateRestartPc _)

theorem nq_suspend (t : ObjRef) : NQK Kq (suspend (Z := Unit) t) := by
  unfold suspend
  refine ik_nqhk_bind (nq_cancelIpc_post _) fun _ => ?_
  nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_suspend _)

theorem nq_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : NQKE Kq mFault) (h_hFault : ∀ x0, NQK Kq (hFault x0)) (h_mError : ∀ x0, NQKE Kq (mError x0)) (h_hError : ∀ x0, NQK Kq (hError x0)) (h_mFinalise : ∀ x0, NQKE Kq (mFinalise x0)) : NQKE Kq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; nq_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem nq_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : NQK Kq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbAppend _ _)

theorem nq_testPossibleSwitchTo (tcbPtr : ObjRef) : NQK Kq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_testPossibleSwitchTo _)

theorem nq_threadSetPriority (tptr : ObjRef) (prio : Priority) : NQK Kq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_threadSetPriority _ _)

theorem nq_unbindFromSc (tcbPtr : ObjRef) : NQK Kq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unbindFromSc _)

theorem nq_unbindMaybeNotification (ntfnptr : ObjRef) : NQK Kq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unbindMaybeNotification _)

theorem nq_unbindNotification (tcb : ObjRef) : NQK Kq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unbindNotification _)

end

end Fl4Proofs.P3.SInv
