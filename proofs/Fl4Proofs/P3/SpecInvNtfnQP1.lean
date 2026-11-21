/- nq3: the PJ frame family, part 1 (generated: proofs/scratch/nq3/mkpj.sh; see SpecInvNtfnQP). -/
import Fl4Proofs.P3.SpecInvNtfnQP
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Lp : List ObjRef}

theorem pj_getAsidPool (ptr : ObjRef) : PJK Lp (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getAsidPool _)

theorem pj_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : PJK Lp (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_hwAsidInvalidate _ _)

theorem pj_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : PJK Lp (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setAsidPool _ _)

theorem pj_findVspaceForAsid (asid : Asid) : PJKE Lp (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_findVspaceForAsid _)

theorem pj_getCap (a0 : CslotPtr) : PJK Lp (getCap (Z := Unit) a0) := by
  unfold getCap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getCap _)

theorem pj_getCurrentCr3  : PJK Lp (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getCurrentCr3)

theorem pj_setCurrentCr3 (c : Cr3) : PJK Lp (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setCurrentCr3 _)

theorem pj_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : PJK Lp (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setCurrentVspaceRoot _ _)

theorem pj_setVmRoot (tcb : ObjRef) : PJK Lp (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setVmRoot _)

theorem pj_deleteAsid (asid : Asid) (pml4 : ObjRef) : PJK Lp (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_deleteAsid _ _)

theorem pj_deleteAsidPool (base : Asid) (ptr : ObjRef) : PJK Lp (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_deleteAsidPool _ _)

theorem pj_getPd (ptr : ObjRef) : PJK Lp (getPd (Z := Unit) ptr) := by
  unfold getPd; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPd _)

theorem pj_getPde (ptr : ObjRef) : PJK Lp (getPde (Z := Unit) ptr) := by
  unfold getPde; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPde _)

theorem pj_getPdpt (ptr : ObjRef) : PJK Lp (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPdpt _)

theorem pj_getPdpte (ptr : ObjRef) : PJK Lp (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPdpte _)

theorem pj_getPt (ptr : ObjRef) : PJK Lp (getPt (Z := Unit) ptr) := by
  unfold getPt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPt _)

theorem pj_getPte (ptr : ObjRef) : PJK Lp (getPte (Z := Unit) ptr) := by
  unfold getPte; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPte _)

theorem pj_getPml4 (ptr : ObjRef) : PJK Lp (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPml4 _)

theorem pj_getPml4e (ptr : ObjRef) : PJK Lp (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getPml4e _)

theorem pj_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : PJKE Lp (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_lookupPdptSlot _ _)

theorem pj_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : PJKE Lp (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_lookupPdSlot _ _)

theorem pj_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : PJKE Lp (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_lookupPtSlot _ _)

theorem pj_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : PJK Lp (setPd (Z := Unit) ptr pd) := by
  unfold setPd; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setPd _ _)

theorem pj_storePde (p : ObjRef) (pde : PDE) : PJK Lp (storePde (Z := Unit) p pde) := by
  unfold storePde; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_storePde _ _)

theorem pj_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : PJK Lp (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setPdpt _ _)

theorem pj_storePdpte (p : ObjRef) (pte : PDPTE) : PJK Lp (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_storePdpte _ _)

theorem pj_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : PJK Lp (setPt (Z := Unit) ptr pt) := by
  unfold setPt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setPt _ _)

theorem pj_storePte (p : ObjRef) (pte : PTE) : PJK Lp (storePte (Z := Unit) p pte) := by
  unfold storePte; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_storePte _ _)

theorem pj_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : PJK Lp (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unmapPage _ _ _ _)

theorem pj_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : PJK Lp (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_flushTable _ _ _ _)

theorem pj_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : PJK Lp (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_invalidatePageStructureCacheAsid _ _)

theorem pj_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : PJK Lp (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unmapPageTable _ _ _)

theorem pj_flushAll (vspace : ObjRef) (asid : Asid) : PJK Lp (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_flushAll _ _)

theorem pj_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : PJK Lp (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unmapPd _ _ _)

theorem pj_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : PJK Lp (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setPml4 _ _)

theorem pj_storePml4e (p : ObjRef) (pte : PML4E) : PJK Lp (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_storePml4e _ _)

theorem pj_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : PJK Lp (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_unmapPdpt _ _ _)

theorem pj_archFinaliseCap (c : ArchCap) (x : Bool) : PJK Lp (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_archFinaliseCap _ _)

theorem pj_setIoportMask (f l : IoPort) (val : Bool) : PJK Lp (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setIoportMask _ _ _)

theorem pj_freeIoportRange (f l : IoPort) : PJK Lp (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_freeIoportRange _ _)

theorem pj_archPostCapDeletion (ac : ArchCap) : PJK Lp (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_archPostCapDeletion _)

theorem pj_getBlockingObject (state : ThreadState) : PJK Lp (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getBlockingObject _)

theorem pj_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : PJK Lp (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getSimpleKo _ _)

theorem pj_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : PJK Lp (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_threadGet _ _)

theorem pj_getThreadState (ref : ObjRef) : PJK Lp (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getThreadState _)

theorem pj_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : PJK Lp (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateSkObjRef _ _ _ _)

theorem pj_setSchedulerAction (action : SchedulerAction) : PJK Lp (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setSchedulerAction _)

theorem pj_setThreadStateAct (tcbPtr : ObjRef) : PJK Lp (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setThreadStateAct _)

theorem pj_replyUnlinkTcb (t r : ObjRef) : PJK Lp (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_replyUnlinkTcb _ _)

theorem pj_tcbEpDequeue (tptr epPtr : ObjRef) : PJK Lp (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_tcbEpDequeue _ _)

theorem pj_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : PJK Lp (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_blockedCancelIpc _ _ _)

theorem pj_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : PJK Lp (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getTcbObjRef _ _)

theorem pj_getSchedContext (ptr : ObjRef) : PJK Lp (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getSchedContext _)

theorem pj_getScRefillReady (scPtr : ObjRef) : PJK Lp (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getScRefillReady _)

theorem pj_isRoundRobin (scPtr : ObjRef) : PJK Lp (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_isRoundRobin _)

theorem pj_getRefillHead (scPtr : ObjRef) : PJK Lp (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getRefillHead _)

theorem pj_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : PJK Lp (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateSchedContext _ _)

theorem pj_refillPopHead (scPtr : ObjRef) : PJK Lp (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_refillPopHead _)

theorem pj_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : PJK Lp (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_updateRefillHd _ _)

theorem pj_mergeOverlappingRefills (scPtr : ObjRef) : PJK Lp (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_mergeOverlappingRefills _)

theorem pj_refillHeadOverlappingLoop (scPtr : ObjRef) : PJK Lp (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_refillHeadOverlappingLoop _)

theorem pj_refillUnblockCheck (scPtr : ObjRef) : PJK Lp (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_refillUnblockCheck _)

theorem pj_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : PJK Lp (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_ifCondRefillUnblockCheck _ _ _)

theorem pj_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : PJK Lp (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getScRefillSufficient _ _)

theorem pj_getTcbQueue (d : Domain) (prio : Priority) : PJK Lp (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_getTcbQueue _ _)

theorem pj_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : PJK Lp (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_setTcbQueue _ _ _)

theorem pj_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : PJK Lp (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_tcbSchedAction _ _)

theorem pj_rescheduleRequired  : PJK Lp (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_rescheduleRequired)

theorem pj_possibleSwitchTo (target : ObjRef) : PJK Lp (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_possibleSwitchTo _)

theorem pj_restartThreadIfNoFault (t : ObjRef) : PJK Lp (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; pj_auto
macro_rules | `(tactic| pj_leaf) => `(tactic| with_reducible exact pj_restartThreadIfNoFault _)
end

end Fl4Proofs.P3.SInv
