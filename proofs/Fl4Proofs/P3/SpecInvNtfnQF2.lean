/- nq1: NtfnQB family lemmas, part 2 (generated; see SpecInvNtfnQF1). -/
import Fl4Proofs.P3.SpecInvNtfnQF1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NQK Kq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unmapPageTable _ _ _)

theorem nq_flushAll (vspace : ObjRef) (asid : Asid) : NQK Kq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_flushAll _ _)

theorem nq_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NQK Kq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unmapPd _ _ _)

theorem nq_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NQK Kq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setPml4 _ _)

theorem nq_storePml4e (p : ObjRef) (pte : PML4E) : NQK Kq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_storePml4e _ _)

theorem nq_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NQK Kq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_unmapPdpt _ _ _)

theorem nq_archFinaliseCap (c : ArchCap) (x : Bool) : NQK Kq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archFinaliseCap _ _)

theorem nq_archGetSanitiseRegisterInfo (_t : ObjRef) : NQK Kq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archGetSanitiseRegisterInfo _)

theorem nq_setOriginal (slot : CslotPtr) (v : Bool) : NQK Kq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setOriginal _ _)

theorem nq_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : NQK Kq (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setUntypedCapAsFull _ _ _)

theorem nq_setCdt (t : Cdt) : NQK Kq (setCdt (Z := Unit) t) := by
  unfold setCdt; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setCdt _)

theorem nq_updateCdt (f : Cdt → Cdt) : NQK Kq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateCdt _)

theorem nq_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : NQK Kq (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_capInsert _ _ _)

theorem nq_setIrqState (state : IrqState) (irq : Irq) : NQK Kq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setIrqState _ _)

theorem nq_updateIrqState (irq : Irq) (irqState : X64IRQState) : NQK Kq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateIrqState _ _)

theorem nq_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NQK Kq m) : NQKE Kq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_withoutPreemption _ ?_)

theorem nq_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NQKE Kq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archInvokeIrqControl _)

theorem nq_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NQK Kq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archInvokeIrqHandler _)

theorem nq_archMaskIrqSignal (irq : Irq) : NQK Kq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archMaskIrqSignal _)

theorem nq_setIoportMask (f l : IoPort) (val : Bool) : NQK Kq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setIoportMask _ _ _)

theorem nq_freeIoportRange (f l : IoPort) : NQK Kq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_freeIoportRange _ _)

theorem nq_archPostCapDeletion (ac : ArchCap) : NQK Kq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPostCapDeletion _)

theorem nq_archPostModifyRegisters (cur t : ObjRef) : NQK Kq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPostModifyRegisters _ _)

theorem nq_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NQK Kq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPostResetUntyped _ _)

theorem nq_loadFpuState (t : ObjRef) : NQK Kq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_loadFpuState _)

theorem nq_saveFpuState (t : ObjRef) : NQK Kq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_saveFpuState _)

theorem nq_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NQK Kq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setX64CurrentFpuOwner _)

theorem nq_switchLocalFpuOwner (newOwner : Option ObjRef) : NQK Kq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_switchLocalFpuOwner _)

theorem nq_fpuRelease (threadPtr : ObjRef) : NQK Kq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fpuRelease _)

theorem nq_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : NQK Kq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_threadGet _ _)

theorem nq_lazyFpuRestore (threadPtr : ObjRef) : NQK Kq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lazyFpuRestore _)

theorem nq_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NQK Kq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPostSetFlags _ _)

theorem nq_archPrepareNextDomain  : NQK Kq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPrepareNextDomain)

theorem nq_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NQK Kq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archPrepareSetDomain _ _)

theorem nq_archSwitchToIdleThread  : NQK Kq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archSwitchToIdleThread)

theorem nq_archSwitchToThread (t : ObjRef) : NQK Kq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_archSwitchToThread _)

theorem nq_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : NQK Kq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getTcbObjRef _ _)

theorem nq_getScRefillReady (scPtr : ObjRef) : NQK Kq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getScRefillReady _)

theorem nq_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NQK Kq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getScRefillSufficient _ _)

theorem nq_setSchedulerAction (action : SchedulerAction) : NQK Kq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setSchedulerAction _)

theorem nq_getTcbQueue (d : Domain) (prio : Priority) : NQK Kq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getTcbQueue _ _)

theorem nq_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NQK Kq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setTcbQueue _ _ _)

theorem nq_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NQK Kq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbSchedAction _ _)

theorem nq_rescheduleRequired  : NQK Kq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_rescheduleRequired)

theorem nq_possibleSwitchTo (target : ObjRef) : NQK Kq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_possibleSwitchTo _)

theorem nq_tcbReleaseRemove (tcbPtr : ObjRef) : NQK Kq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbReleaseRemove _)

theorem nq_tcbReleaseDequeue  : NQK Kq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_tcbReleaseDequeue)

theorem nq_awaken  : NQK Kq (awaken (Z := Unit)) := by
  unfold awaken; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_awaken)

theorem nq_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NQK Kq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getSimpleKo _ _)

theorem nq_bindNotification (tcbptr ntfnptr : ObjRef) : NQK Kq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_bindNotification _ _)

theorem nq_getSchedContext (ptr : ObjRef) : NQK Kq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getSchedContext _)

theorem nq_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : NQK Kq (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_updateSchedContext _ _)

theorem nq_bindScReply (scPtr replyPtr : ObjRef) : NQK Kq (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_bindScReply _ _)

theorem nq_getBlockingObject (state : ThreadState) : NQK Kq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getBlockingObject _)

theorem nq_getThreadState (ref : ObjRef) : NQK Kq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getThreadState _)

theorem nq_setThreadStateAct (tcbPtr : ObjRef) : NQK Kq (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setThreadStateAct _)

/-- `reply_unlink_tcb` of a thread of `K` (read BlockedOnReply, or dequeued from its endpoint). -/
theorem nq_replyUnlinkTcb (t r : ObjRef) (ht : t ∈ Kq) : NQK Kq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_replyUnlinkTcb _ _ ?_); nq_mem))

/-- `blocked_cancel_ipc`: the thread is dequeued from its endpoint (so joins `K`, by EpQB) before its state is written. -/
theorem nq_blockedCancelIpc_post (st : ThreadState) (t : ObjRef) (r : Option ObjRef) :
    HK (NQ Kq) (NQ (t :: Kq)) (blockedCancelIpc (Z := Unit) st t r) := by
  unfold blockedCancelIpc getBlockingObject
  refine hk_bind (hk_of_ik (by nq_auto)) fun ep => ?_
  refine hk_bind (nq_tcbEpDequeue_post t ep) fun _ => hk_of_ik ?_
  nq_auto
end

end Fl4Proofs.P3.SInv
