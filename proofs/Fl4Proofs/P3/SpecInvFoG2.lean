
/- fo1: generated frames `OIK Qo` (sg1's SpecInvSgI2 renamed, the owner / retype / detype writers removed; see SpecInvFoG1). -/
import Fl4Proofs.P3.SpecInvFoG1
open Classical

namespace Fl4Proofs.P3.SInvF
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Qo : Option ObjRef}

theorem oi_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : OIK Qo (setPt (Z := Unit) ptr pt) := by
  unfold setPt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPt _ _)

theorem oi_storePte (p : ObjRef) (pte : PTE) : OIK Qo (storePte (Z := Unit) p pte) := by
  unfold storePte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePte _ _)

theorem oi_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : OIK Qo (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPage _ _ _ _)

theorem oi_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : OIK Qo (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushTable _ _ _ _)

theorem oi_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : OIK Qo (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invalidatePageStructureCacheAsid _ _)

theorem oi_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : OIK Qo (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPageTable _ _ _)

theorem oi_flushAll (vspace : ObjRef) (asid : Asid) : OIK Qo (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushAll _ _)

theorem oi_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : OIK Qo (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPd _ _ _)

theorem oi_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : OIK Qo (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPml4 _ _)

theorem oi_storePml4e (p : ObjRef) (pte : PML4E) : OIK Qo (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePml4e _ _)

theorem oi_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : OIK Qo (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPdpt _ _ _)

theorem oi_archFinaliseCap (c : ArchCap) (x : Bool) : OIK Qo (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archFinaliseCap _ _)

theorem oi_archGetSanitiseRegisterInfo (_t : ObjRef) : OIK Qo (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archGetSanitiseRegisterInfo _)

theorem oi_setOriginal (slot : CslotPtr) (v : Bool) : OIK Qo (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setOriginal _ _)

theorem oi_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : OIK Qo (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setUntypedCapAsFull _ _ _)

theorem oi_setCdt (t : Cdt) : OIK Qo (setCdt (Z := Unit) t) := by
  unfold setCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setCdt _)

theorem oi_updateCdt (f : Cdt → Cdt) : OIK Qo (updateCdt (Z := Unit) f) := by
  unfold updateCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateCdt _)

theorem oi_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK Qo (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capInsert _ _ _)

theorem oi_setIrqState (state : IrqState) (irq : Irq) : OIK Qo (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIrqState _ _)

theorem oi_updateIrqState (irq : Irq) (irqState : X64IRQState) : OIK Qo (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateIrqState _ _)

theorem oi_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : OIK Qo m) : OIKE Qo (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_withoutPreemption _ ?_)

theorem oi_archInvokeIrqControl (aic : ArchIrqControlInvocation) : OIKE Qo (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqControl _)

theorem oi_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : OIK Qo (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqHandler _)

theorem oi_archMaskIrqSignal (irq : Irq) : OIK Qo (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archMaskIrqSignal _)

theorem oi_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : OIK Qo (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storeAsidPoolEntry _ _ _)

theorem oi_performAsidPoolInvocation (iv : AsidPoolInvocation) : OIK Qo (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performAsidPoolInvocation _)

theorem oi_portIn (f : MachineMonad Data) : OIK Qo (portIn (Z := Unit) f) := by
  unfold portIn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portIn _)

theorem oi_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : OIK Qo (portOut (Z := Unit) f w) := by
  unfold portOut; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portOut _ _)

theorem oi_performIoPortInvocation (i : IoPortInvocation) : OIK Qo (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoPortInvocation _)

theorem oi_setIoportMask (f l : IoPort) (val : Bool) : OIK Qo (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIoportMask _ _ _)

theorem oi_performIoportControlInvocation (i : IoPortControlInvocation) : OIK Qo (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoportControlInvocation _)

theorem oi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : OIK Qo (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageDirectoryInvocation _)

theorem oi_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : OIK Qo (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocationUnmap _ _)

theorem oi_performPageInvocation (iv : PageInvocation) : OIK Qo (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocation _)

theorem oi_performPageTableInvocation (iv : PageTableInvocation) : OIK Qo (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageTableInvocation _)

theorem oi_performPdptInvocation (iv : PdptInvocation) : OIK Qo (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPdptInvocation _)

theorem oi_freeIoportRange (f l : IoPort) : OIK Qo (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_freeIoportRange _ _)

theorem oi_archPostCapDeletion (ac : ArchCap) : OIK Qo (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostCapDeletion _)

theorem oi_archPostModifyRegisters (cur t : ObjRef) : OIK Qo (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostModifyRegisters _ _)

theorem oi_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : OIK Qo (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostResetUntyped _ _)

theorem oi_loadFpuState (t : ObjRef) : OIK Qo (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadFpuState _)

theorem oi_saveFpuState (t : ObjRef) : OIK Qo (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_saveFpuState _)

theorem oi_archSwitchToIdleThread  : OIK Qo (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archSwitchToIdleThread)

theorem oi_getScRefillReady (scPtr : ObjRef) : OIK Qo (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillReady _)

theorem oi_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : OIK Qo (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillSufficient _ _)

theorem oi_getTcbQueue (d : Domain) (prio : Priority) : OIK Qo (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getTcbQueue _ _)

theorem oi_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : OIK Qo (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setTcbQueue _ _ _)

theorem oi_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : OIK Qo (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbSchedAction _ _)

theorem oi_rescheduleRequired  : OIK Qo (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_rescheduleRequired)

theorem oi_possibleSwitchTo (target : ObjRef) : OIK Qo (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_possibleSwitchTo _)

theorem oi_tcbReleaseRemove (tcbPtr : ObjRef) : OIK Qo (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseRemove _)

theorem oi_tcbReleaseDequeue  : OIK Qo (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseDequeue)

theorem oi_awaken  : OIK Qo (awaken (Z := Unit)) := by
  unfold awaken; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_awaken)

theorem oi_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : OIK Qo (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSimpleKo _ _)

theorem oi_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : OIK Qo (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateSkObjRef _ _ _ _)

theorem oi_bindNotification (tcbptr ntfnptr : ObjRef) : OIK Qo (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindNotification _ _)

theorem oi_bindScReply (scPtr replyPtr : ObjRef) : OIK Qo (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindScReply _ _)

theorem oi_getBlockingObject (state : ThreadState) : OIK Qo (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getBlockingObject _)

theorem oi_replyUnlinkTcb (t r : ObjRef) : OIK Qo (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvF
