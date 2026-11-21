/- sl1: idle-SC frame lemmas `IsK t` (sg1 SpecInvSgI2 renamed; see SpecInvSlI1). -/
import Fl4Proofs.P3.SpecInvSlI1
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem isk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : IsK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setPt _ _)

theorem isk_storePte (p : ObjRef) (pte : PTE) : IsK N (storePte (Z := Unit) p pte) := by
  unfold storePte; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storePte _ _)

theorem isk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : IsK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unmapPage _ _ _ _)

theorem isk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : IsK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_flushTable _ _ _ _)

theorem isk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : IsK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_invalidatePageStructureCacheAsid _ _)

theorem isk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : IsK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unmapPageTable _ _ _)

theorem isk_flushAll (vspace : ObjRef) (asid : Asid) : IsK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_flushAll _ _)

theorem isk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : IsK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unmapPd _ _ _)

theorem isk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : IsK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setPml4 _ _)

theorem isk_storePml4e (p : ObjRef) (pte : PML4E) : IsK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storePml4e _ _)

theorem isk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : IsK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_unmapPdpt _ _ _)

theorem isk_archFinaliseCap (c : ArchCap) (x : Bool) : IsK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archFinaliseCap _ _)

theorem isk_archGetSanitiseRegisterInfo (_t : ObjRef) : IsK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archGetSanitiseRegisterInfo _)

theorem isk_setOriginal (slot : CslotPtr) (v : Bool) : IsK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setOriginal _ _)

theorem isk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : IsK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setUntypedCapAsFull _ _ _)

theorem isk_setCdt (t : Cdt) : IsK N (setCdt (Z := Unit) t) := by
  unfold setCdt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setCdt _)

theorem isk_updateCdt (f : Cdt → Cdt) : IsK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateCdt _)

theorem isk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : IsK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_capInsert _ _ _)

theorem isk_setIrqState (state : IrqState) (irq : Irq) : IsK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setIrqState _ _)

theorem isk_updateIrqState (irq : Irq) (irqState : X64IRQState) : IsK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateIrqState _ _)

theorem isk_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IsK N m) : IsKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; isk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_withoutPreemption _ ?_)

theorem isk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IsKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archInvokeIrqControl _)

theorem isk_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : IsK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archInvokeIrqHandler _)

theorem isk_archMaskIrqSignal (irq : Irq) : IsK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archMaskIrqSignal _)

theorem isk_performAsidControlInvocation (iv : AsidControlInvocation) : IsK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performAsidControlInvocation _)

theorem isk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : IsK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_storeAsidPoolEntry _ _ _)

theorem isk_performAsidPoolInvocation (iv : AsidPoolInvocation) : IsK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performAsidPoolInvocation _)

theorem isk_portIn (f : MachineMonad Data) : IsK N (portIn (Z := Unit) f) := by
  unfold portIn; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_portIn _)

theorem isk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : IsK N (portOut (Z := Unit) f w) := by
  unfold portOut; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_portOut _ _)

theorem isk_performIoPortInvocation (i : IoPortInvocation) : IsK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performIoPortInvocation _)

theorem isk_setIoportMask (f l : IoPort) (val : Bool) : IsK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setIoportMask _ _ _)

theorem isk_performIoportControlInvocation (i : IoPortControlInvocation) : IsK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performIoportControlInvocation _)

theorem isk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : IsK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPageDirectoryInvocation _)

theorem isk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : IsK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPageInvocationUnmap _ _)

theorem isk_performPageInvocation (iv : PageInvocation) : IsK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPageInvocation _)

theorem isk_performPageTableInvocation (iv : PageTableInvocation) : IsK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPageTableInvocation _)

theorem isk_performPdptInvocation (iv : PdptInvocation) : IsK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPdptInvocation _)

theorem isk_archPerformInvocation (i : ArchInvocation) : IsKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPerformInvocation _)

theorem isk_freeIoportRange (f l : IoPort) : IsK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_freeIoportRange _ _)

theorem isk_archPostCapDeletion (ac : ArchCap) : IsK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPostCapDeletion _)

theorem isk_archPostModifyRegisters (cur t : ObjRef) : IsK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPostModifyRegisters _ _)

theorem isk_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : IsK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPostResetUntyped _ _)

theorem isk_loadFpuState (t : ObjRef) : IsK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_loadFpuState _)

theorem isk_saveFpuState (t : ObjRef) : IsK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_saveFpuState _)

theorem isk_setX64CurrentFpuOwner (newOwner : Option ObjRef) : IsK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setX64CurrentFpuOwner _)

theorem isk_switchLocalFpuOwner (newOwner : Option ObjRef) : IsK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_switchLocalFpuOwner _)

theorem isk_fpuRelease (threadPtr : ObjRef) : IsK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fpuRelease _)

theorem isk_lazyFpuRestore (threadPtr : ObjRef) : IsK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_lazyFpuRestore _)

theorem isk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : IsK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPostSetFlags _ _)

theorem isk_archPrepareNextDomain  : IsK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPrepareNextDomain)

theorem isk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : IsK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archPrepareSetDomain _ _)

theorem isk_archSwitchToIdleThread  : IsK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archSwitchToIdleThread)

theorem isk_archSwitchToThread (t : ObjRef) : IsK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_archSwitchToThread _)

theorem isk_getScRefillReady (scPtr : ObjRef) : IsK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getScRefillReady _)

theorem isk_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : IsK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getScRefillSufficient _ _)

theorem isk_getTcbQueue (d : Domain) (prio : Priority) : IsK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getTcbQueue _ _)

theorem isk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : IsK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setTcbQueue _ _ _)

theorem isk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : IsK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbSchedAction _ _)

theorem isk_rescheduleRequired  : IsK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_rescheduleRequired)

theorem isk_possibleSwitchTo (target : ObjRef) : IsK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_possibleSwitchTo _)

theorem isk_tcbReleaseRemove (tcbPtr : ObjRef) : IsK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbReleaseRemove _)

theorem isk_tcbReleaseDequeue  : IsK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_tcbReleaseDequeue)

theorem isk_awaken  : IsK N (awaken (Z := Unit)) := by
  unfold awaken; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_awaken)

theorem isk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : IsK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getSimpleKo _ _)

theorem isk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : IsK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_updateSkObjRef _ _ _ _)

theorem isk_bindNotification (tcbptr ntfnptr : ObjRef) : IsK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_bindNotification _ _)

theorem isk_bindScReply (scPtr replyPtr : ObjRef) : IsK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_bindScReply _ _)

theorem isk_getBlockingObject (state : ThreadState) : IsK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getBlockingObject _)

theorem isk_replyUnlinkTcb (t r : ObjRef) : IsK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvL
