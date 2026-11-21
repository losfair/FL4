/- nq1: the current-thread frame `CTK c` (the current thread stays `c`) for every spec function reachable from the syscall entry except the scheduler, part 2 (generated: proofs/scratch/nq1/mkck.sh). -/
import Fl4Proofs.P3.SpecInvNtfnQC1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {cq : ObjRef}

theorem ct_portIn (f : MachineMonad Data) : CTK cq (portIn (Z := Unit) f) := by
  unfold portIn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_portIn _)

theorem ct_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : CTK cq (portOut (Z := Unit) f w) := by
  unfold portOut; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_portOut _ _)

theorem ct_performIoPortInvocation (i : IoPortInvocation) : CTK cq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performIoPortInvocation _)

theorem ct_setIoportMask (f l : IoPort) (val : Bool) : CTK cq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setIoportMask _ _ _)

theorem ct_performIoportControlInvocation (i : IoPortControlInvocation) : CTK cq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performIoportControlInvocation _)

theorem ct_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : CTK cq (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPageDirectoryInvocation _)

theorem ct_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : CTK cq (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPageInvocationUnmap _ _)

theorem ct_performPageInvocation (iv : PageInvocation) : CTK cq (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPageInvocation _)

theorem ct_performPageTableInvocation (iv : PageTableInvocation) : CTK cq (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPageTableInvocation _)

theorem ct_performPdptInvocation (iv : PdptInvocation) : CTK cq (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPdptInvocation _)

theorem ct_archPerformInvocation (i : ArchInvocation) : CTKE cq (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPerformInvocation _)

theorem ct_freeIoportRange (f l : IoPort) : CTK cq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_freeIoportRange _ _)

theorem ct_archPostCapDeletion (ac : ArchCap) : CTK cq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPostCapDeletion _)

theorem ct_archPostModifyRegisters (cur t : ObjRef) : CTK cq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPostModifyRegisters _ _)

theorem ct_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : CTK cq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPostResetUntyped _ _)

theorem ct_loadFpuState (t : ObjRef) : CTK cq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_loadFpuState _)

theorem ct_saveFpuState (t : ObjRef) : CTK cq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_saveFpuState _)

theorem ct_archThreadSet (f : ArchTcb → ArchTcb) (tptr : ObjRef) : CTK cq (archThreadSet (Z := Unit) f tptr) := by
  unfold archThreadSet; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archThreadSet _ _)

theorem ct_setX64CurrentFpuOwner (newOwner : Option ObjRef) : CTK cq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setX64CurrentFpuOwner _)

theorem ct_switchLocalFpuOwner (newOwner : Option ObjRef) : CTK cq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_switchLocalFpuOwner _)

theorem ct_fpuRelease (threadPtr : ObjRef) : CTK cq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fpuRelease _)

theorem ct_lazyFpuRestore (threadPtr : ObjRef) : CTK cq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lazyFpuRestore _)

theorem ct_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : CTK cq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPostSetFlags _ _)

theorem ct_archPrepareNextDomain  : CTK cq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPrepareNextDomain)

theorem ct_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : CTK cq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archPrepareSetDomain _ _)

theorem ct_archSwitchToIdleThread  : CTK cq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archSwitchToIdleThread)

theorem ct_archSwitchToThread (t : ObjRef) : CTK cq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_archSwitchToThread _)

theorem ct_getScRefillReady (scPtr : ObjRef) : CTK cq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getScRefillReady _)

theorem ct_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : CTK cq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getScRefillSufficient _ _)

theorem ct_getTcbQueue (d : Domain) (prio : Priority) : CTK cq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getTcbQueue _ _)

theorem ct_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : CTK cq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setTcbQueue _ _ _)

theorem ct_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : CTK cq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbSchedAction _ _)

theorem ct_rescheduleRequired  : CTK cq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_rescheduleRequired)

theorem ct_possibleSwitchTo (target : ObjRef) : CTK cq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_possibleSwitchTo _)

theorem ct_tcbReleaseRemove (tcbPtr : ObjRef) : CTK cq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbReleaseRemove _)

theorem ct_tcbReleaseDequeue  : CTK cq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbReleaseDequeue)

theorem ct_awaken  : CTK cq (awaken (Z := Unit)) := by
  unfold awaken; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_awaken)

theorem ct_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : CTK cq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getSimpleKo _ _)

theorem ct_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) (ep : α) : CTK cq (setSimpleKo (Z := Unit) f ptr ep) := by
  unfold setSimpleKo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setSimpleKo _ _ _)

theorem ct_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : CTK cq (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateSkObjRef _ _ _ _)

theorem ct_bindNotification (tcbptr ntfnptr : ObjRef) : CTK cq (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_bindNotification _ _)

theorem ct_bindScReply (scPtr replyPtr : ObjRef) : CTK cq (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_bindScReply _ _)

theorem ct_getBlockingObject (state : ThreadState) : CTK cq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getBlockingObject _)

theorem ct_replyUnlinkTcb (t r : ObjRef) : CTK cq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyUnlinkTcb _ _)

theorem ct_tcbEpDequeue (tptr epPtr : ObjRef) : CTK cq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbEpDequeue _ _)

theorem ct_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : CTK cq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_blockedCancelIpc _ _ _)

theorem ct_isRoundRobin (scPtr : ObjRef) : CTK cq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isRoundRobin _)

theorem ct_getRefillHead (scPtr : ObjRef) : CTK cq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getRefillHead _)

theorem ct_refillPopHead (scPtr : ObjRef) : CTK cq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillPopHead _)

theorem ct_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : CTK cq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateRefillHd _ _)

theorem ct_mergeOverlappingRefills (scPtr : ObjRef) : CTK cq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_mergeOverlappingRefills _)

theorem ct_refillHeadOverlappingLoop (scPtr : ObjRef) : CTK cq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillHeadOverlappingLoop _)

theorem ct_refillUnblockCheck (scPtr : ObjRef) : CTK cq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillUnblockCheck _)

theorem ct_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : CTK cq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_ifCondRefillUnblockCheck _ _ _)

theorem ct_restartThreadIfNoFault (t : ObjRef) : CTK cq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_restartThreadIfNoFault _)

theorem ct_removeAndRestartEpQueuedThread (t epptr : ObjRef) : CTK cq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_removeAndRestartEpQueuedThread _ _)

theorem ct_cancelAllIpc (epptr : ObjRef) : CTK cq (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_cancelAllIpc _)

theorem ct_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : CTK cq (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbNtfnDequeue _ _)

theorem ct_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : CTK cq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_removeAndRestartNtfnQueuedThread _ _)

theorem ct_cancelAllSignals (ntfnptr : ObjRef) : CTK cq (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_cancelAllSignals _)

theorem ct_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : CTK cq (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_removeAndRestartBadgedThread _ _ _)

theorem ct_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : CTK cq (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_cancelBadgedSends _ _)

theorem ct_cancelSignal (threadptr ntfnptr : ObjRef) : CTK cq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_cancelSignal _ _)

theorem ct_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : CTK cq (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getSkObjRef _ _ _)

theorem ct_replyRemoveTcb (tptr rptr : ObjRef) : CTK cq (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyRemoveTcb _ _)

theorem ct_cancelIpc (tptr : ObjRef) : CTK cq (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_cancelIpc _)

theorem ct_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : CTK cq (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capSwap _ _ _ _)

theorem ct_capSwapForDelete (slot1 slot2 : CslotPtr) : CTK cq (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capSwapForDelete _ _)

theorem ct_deletedIrqHandler (irq : Irq) : CTK cq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deletedIrqHandler _)

theorem ct_postCapDeletion (cap : Cap) : CTK cq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_postCapDeletion _)

theorem ct_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : CTK cq (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_emptySlot _ _)

theorem ct_replyUnlinkSc (scPtr replyPtr : ObjRef) : CTK cq (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyUnlinkSc _ _)

theorem ct_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : CTK cq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getScObjRef _ _)

theorem ct_testReschedule (fromTptr : ObjRef) : CTK cq (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_testReschedule _)

theorem ct_schedContextDonate (scPtr tcbPtr : ObjRef) : CTK cq (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextDonate _ _)

theorem ct_replyRemove (caller r : ObjRef) : CTK cq (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyRemove _ _)

theorem ct_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : CTK cq (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextMaybeUnbindNtfn _)

theorem ct_unbindMaybeNotification (ntfnptr : ObjRef) : CTK cq (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unbindMaybeNotification _)

theorem ct_fastFinalise (a0 : Cap) (a1 : Bool) : CTK cq (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fastFinalise _ _)

theorem ct_capDeleteOne (slot : CslotPtr) : CTK cq (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capDeleteOne _)

theorem ct_getIrqSlot (irq : Irq) : CTK cq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getIrqSlot _)

theorem ct_deletingIrqHandler (irq : Irq) : CTK cq (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deletingIrqHandler _)

theorem ct_prepareThreadDelete (threadPtr : ObjRef) : CTK cq (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_prepareThreadDelete _)

theorem ct_schedContextSetInactive (scPtr : ObjRef) : CTK cq (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextSetInactive _)

theorem ct_schedContextUnbindTcb (scPtr : ObjRef) : CTK cq (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUnbindTcb _)

theorem ct_schedContextUnbindAllTcbs (scPtr : ObjRef) : CTK cq (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUnbindAllTcbs _)

theorem ct_schedContextUnbindNtfn (scPtr : ObjRef) : CTK cq (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUnbindNtfn _)

theorem ct_schedContextUnbindReply (scPtr : ObjRef) : CTK cq (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUnbindReply _)

theorem ct_schedContextUnbindYieldFrom (scPtr : ObjRef) : CTK cq (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextUnbindYieldFrom _)

theorem ct_updateRestartPc (threadPtr : ObjRef) : CTK cq (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateRestartPc _)

theorem ct_suspend (thread : ObjRef) : CTK cq (suspend (Z := Unit) thread) := by
  unfold suspend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_suspend _)

theorem ct_unbindFromSc (tcbPtr : ObjRef) : CTK cq (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unbindFromSc _)

theorem ct_unbindNotification (tcb : ObjRef) : CTK cq (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_unbindNotification _)

theorem ct_finaliseCap (a0 : Cap) (a1 : Bool) : CTK cq (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_finaliseCap _ _)

theorem ct_getScActive (scPtr : ObjRef) : CTK cq (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getScActive _)

theorem ct_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : CTKE cq f) (h_g : CTKE cq g) : CTKE cq (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ct_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_orChoiceE _ _ _ ?_ ?_)

theorem ct_updateTimeStamp  : CTK cq (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateTimeStamp)

theorem ct_preemptionPoint  : CTKE cq (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem ct_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, CTK cq (f k)) (k : RecDelCall) : CTKE cq (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, CTKE cq (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ct_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ct_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ct_auto
    all_goals exact hrec' _

theorem ct_recDel (c : RecDelCall) : CTKE cq (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ct_recDelF hf k) c
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_recDel _)

theorem ct_capDelete (slot : CslotPtr) : CTKE cq (capDelete (Z := Unit) slot) := by
  unfold capDelete; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capDelete _)

theorem ct_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : CTKE cq m) : CTKE cq (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_capFaultOnFailure _ _ _ ?_)

theorem ct_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : CTK cq (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem ct_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, CTK cq (f k)) (sl : CslotPtr) : CTKE cq (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, CTKE cq (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ct_auto
  all_goals exact hrec' _

theorem ct_capRevoke (sl : CslotPtr) : CTKE cq (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ct_capRevokeF hf k) sl
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_capRevoke _)
end

end Fl4Proofs.P3.SInv
