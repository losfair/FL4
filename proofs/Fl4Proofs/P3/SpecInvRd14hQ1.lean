/- rd14h: the QT frame family, part 1 (generated: proofs/scratch/rd14h/mkqt.sh; see SpecInvRd14hQ). -/
import Fl4Proofs.P3.SpecInvRd14hQ
open Classical

namespace Fl4Proofs.P3.SInvR.A14h
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f Fl4Proofs.P3.SInvR.A14g

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Tq : ObjRef}

theorem qth_getAsidPool (ptr : ObjRef) : QTK Tq (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getAsidPool _)

theorem qth_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : QTK Tq (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_hwAsidInvalidate _ _)

theorem qth_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : QTK Tq (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setAsidPool _ _)

theorem qth_findVspaceForAsid (asid : Asid) : QTKE Tq (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_findVspaceForAsid _)

theorem qth_getCap (a0 : CslotPtr) : QTK Tq (getCap (Z := Unit) a0) := by
  unfold getCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getCap _)

theorem qth_getCurrentCr3  : QTK Tq (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getCurrentCr3)

theorem qth_setCurrentCr3 (c : Cr3) : QTK Tq (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setCurrentCr3 _)

theorem qth_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : QTK Tq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setCurrentVspaceRoot _ _)

theorem qth_setVmRoot (tcb : ObjRef) : QTK Tq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setVmRoot _)

theorem qth_deleteAsid (asid : Asid) (pml4 : ObjRef) : QTK Tq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_deleteAsid _ _)

theorem qth_deleteAsidPool (base : Asid) (ptr : ObjRef) : QTK Tq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_deleteAsidPool _ _)

theorem qth_getPd (ptr : ObjRef) : QTK Tq (getPd (Z := Unit) ptr) := by
  unfold getPd; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPd _)

theorem qth_getPde (ptr : ObjRef) : QTK Tq (getPde (Z := Unit) ptr) := by
  unfold getPde; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPde _)

theorem qth_getPdpt (ptr : ObjRef) : QTK Tq (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPdpt _)

theorem qth_getPdpte (ptr : ObjRef) : QTK Tq (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPdpte _)

theorem qth_getPt (ptr : ObjRef) : QTK Tq (getPt (Z := Unit) ptr) := by
  unfold getPt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPt _)

theorem qth_getPte (ptr : ObjRef) : QTK Tq (getPte (Z := Unit) ptr) := by
  unfold getPte; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPte _)

theorem qth_getPml4 (ptr : ObjRef) : QTK Tq (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPml4 _)

theorem qth_getPml4e (ptr : ObjRef) : QTK Tq (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getPml4e _)

theorem qth_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : QTKE Tq (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_lookupPdptSlot _ _)

theorem qth_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : QTKE Tq (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_lookupPdSlot _ _)

theorem qth_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : QTKE Tq (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_lookupPtSlot _ _)

theorem qth_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : QTK Tq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setPd _ _)

theorem qth_storePde (p : ObjRef) (pde : PDE) : QTK Tq (storePde (Z := Unit) p pde) := by
  unfold storePde; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_storePde _ _)

theorem qth_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : QTK Tq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setPdpt _ _)

theorem qth_storePdpte (p : ObjRef) (pte : PDPTE) : QTK Tq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_storePdpte _ _)

theorem qth_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : QTK Tq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setPt _ _)

theorem qth_storePte (p : ObjRef) (pte : PTE) : QTK Tq (storePte (Z := Unit) p pte) := by
  unfold storePte; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_storePte _ _)

theorem qth_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : QTK Tq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unmapPage _ _ _ _)

theorem qth_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : QTK Tq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_flushTable _ _ _ _)

theorem qth_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : QTK Tq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_invalidatePageStructureCacheAsid _ _)

theorem qth_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : QTK Tq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unmapPageTable _ _ _)

theorem qth_flushAll (vspace : ObjRef) (asid : Asid) : QTK Tq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_flushAll _ _)

theorem qth_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : QTK Tq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unmapPd _ _ _)

theorem qth_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : QTK Tq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setPml4 _ _)

theorem qth_storePml4e (p : ObjRef) (pte : PML4E) : QTK Tq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_storePml4e _ _)

theorem qth_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : QTK Tq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_unmapPdpt _ _ _)

theorem qth_archFinaliseCap (c : ArchCap) (x : Bool) : QTK Tq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_archFinaliseCap _ _)

theorem qth_setIoportMask (f l : IoPort) (val : Bool) : QTK Tq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setIoportMask _ _ _)

theorem qth_freeIoportRange (f l : IoPort) : QTK Tq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_freeIoportRange _ _)

theorem qth_archPostCapDeletion (ac : ArchCap) : QTK Tq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_archPostCapDeletion _)

theorem qth_getBlockingObject (state : ThreadState) : QTK Tq (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getBlockingObject _)

theorem qth_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : QTK Tq (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getSimpleKo _ _)

theorem qth_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : QTK Tq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_threadGet _ _)

theorem qth_getThreadState (ref : ObjRef) : QTK Tq (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getThreadState _)

theorem qth_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : QTK Tq (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateSkObjRef _ _ _ _)

theorem qth_setSchedulerAction (action : SchedulerAction) : QTK Tq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setSchedulerAction _)

theorem qth_setThreadStateAct (tcbPtr : ObjRef) : QTK Tq (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setThreadStateAct _)

theorem qth_replyUnlinkTcb (t r : ObjRef) : QTK Tq (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_replyUnlinkTcb _ _)

theorem qth_tcbEpDequeue (tptr epPtr : ObjRef) : QTK Tq (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbEpDequeue _ _)

theorem qth_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : QTK Tq (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_blockedCancelIpc _ _ _)

theorem qth_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : QTK Tq (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbNtfnDequeue _ _)

theorem qth_cancelSignal (threadptr ntfnptr : ObjRef) : QTK Tq (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_cancelSignal _ _)

theorem qth_setCdt (t : Cdt) : QTK Tq (setCdt (Z := Unit) t) := by
  unfold setCdt; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setCdt _)

theorem qth_setOriginal (slot : CslotPtr) (v : Bool) : QTK Tq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setOriginal _ _)

theorem qth_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : QTK Tq (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_capSwap _ _ _ _)

theorem qth_capSwapForDelete (slot1 slot2 : CslotPtr) : QTK Tq (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_capSwapForDelete _ _)

theorem qth_setIrqState (state : IrqState) (irq : Irq) : QTK Tq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setIrqState _ _)

theorem qth_deletedIrqHandler (irq : Irq) : QTK Tq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_deletedIrqHandler _)

theorem qth_postCapDeletion (cap : Cap) : QTK Tq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_postCapDeletion _)

theorem qth_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : QTK Tq (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_emptySlot _ _)

theorem qth_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : QTK Tq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getTcbObjRef _ _)

theorem qth_getSchedContext (ptr : ObjRef) : QTK Tq (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getSchedContext _)

theorem qth_getScRefillReady (scPtr : ObjRef) : QTK Tq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getScRefillReady _)

theorem qth_isRoundRobin (scPtr : ObjRef) : QTK Tq (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_isRoundRobin _)

theorem qth_getRefillHead (scPtr : ObjRef) : QTK Tq (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getRefillHead _)

theorem qth_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : QTK Tq (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateSchedContext _ _)

theorem qth_refillPopHead (scPtr : ObjRef) : QTK Tq (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillPopHead _)

theorem qth_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : QTK Tq (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_updateRefillHd _ _)

theorem qth_mergeOverlappingRefills (scPtr : ObjRef) : QTK Tq (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_mergeOverlappingRefills _)

theorem qth_refillHeadOverlappingLoop (scPtr : ObjRef) : QTK Tq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillHeadOverlappingLoop _)

theorem qth_refillUnblockCheck (scPtr : ObjRef) : QTK Tq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_refillUnblockCheck _)

theorem qth_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : QTK Tq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_ifCondRefillUnblockCheck _ _ _)

theorem qth_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : QTK Tq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getScRefillSufficient _ _)

theorem qth_getTcbQueue (d : Domain) (prio : Priority) : QTK Tq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_getTcbQueue _ _)

theorem qth_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : QTK Tq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_setTcbQueue _ _ _)

theorem qth_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : QTK Tq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_tcbSchedAction _ _)

theorem qth_rescheduleRequired  : QTK Tq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_rescheduleRequired)

theorem qth_possibleSwitchTo (target : ObjRef) : QTK Tq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_possibleSwitchTo _)

theorem qth_restartThreadIfNoFault (t : ObjRef) : QTK Tq (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_restartThreadIfNoFault _)

theorem qth_removeAndRestartEpQueuedThread (t epptr : ObjRef) : QTK Tq (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_removeAndRestartEpQueuedThread _ _)

theorem qth_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : QTK Tq (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; qth_auto
macro_rules | `(tactic| qth_leaf) => `(tactic| with_reducible exact qth_removeAndRestartNtfnQueuedThread _ _)
end

end Fl4Proofs.P3.SInvR.A14h
