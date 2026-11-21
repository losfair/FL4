
/- epq1: generated frames `PZK` (sg1's SpecInvSgI2 renamed, the refill writers and the configure path removed; see SpecInvEqG1). -/
import Fl4Proofs.P3.SpecInvEqG1
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000


theorem pz_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : PZK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setPt _ _)

theorem pz_storePte (p : ObjRef) (pte : PTE) : PZK (storePte (Z := Unit) p pte) := by
  unfold storePte; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_storePte _ _)

theorem pz_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : PZK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unmapPage _ _ _ _)

theorem pz_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : PZK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_flushTable _ _ _ _)

theorem pz_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : PZK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_invalidatePageStructureCacheAsid _ _)

theorem pz_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : PZK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unmapPageTable _ _ _)

theorem pz_flushAll (vspace : ObjRef) (asid : Asid) : PZK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_flushAll _ _)

theorem pz_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : PZK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unmapPd _ _ _)

theorem pz_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : PZK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setPml4 _ _)

theorem pz_storePml4e (p : ObjRef) (pte : PML4E) : PZK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_storePml4e _ _)

theorem pz_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : PZK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_unmapPdpt _ _ _)

theorem pz_archFinaliseCap (c : ArchCap) (x : Bool) : PZK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archFinaliseCap _ _)

theorem pz_archGetSanitiseRegisterInfo (_t : ObjRef) : PZK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archGetSanitiseRegisterInfo _)

theorem pz_setOriginal (slot : CslotPtr) (v : Bool) : PZK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setOriginal _ _)

theorem pz_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : PZK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setUntypedCapAsFull _ _ _)

theorem pz_setCdt (t : Cdt) : PZK (setCdt (Z := Unit) t) := by
  unfold setCdt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setCdt _)

theorem pz_updateCdt (f : Cdt → Cdt) : PZK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateCdt _)

theorem pz_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : PZK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_capInsert _ _ _)

theorem pz_setIrqState (state : IrqState) (irq : Irq) : PZK (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setIrqState _ _)

theorem pz_updateIrqState (irq : Irq) (irqState : X64IRQState) : PZK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateIrqState _ _)

theorem pz_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : PZK m) : PZKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; pz_auto
  all_goals first | exact h_m
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_withoutPreemption _ ?_)

theorem pz_archInvokeIrqControl (aic : ArchIrqControlInvocation) : PZKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archInvokeIrqControl _)

theorem pz_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : PZK (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archInvokeIrqHandler _)

theorem pz_archMaskIrqSignal (irq : Irq) : PZK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archMaskIrqSignal _)

theorem pz_performAsidControlInvocation (iv : AsidControlInvocation) : PZK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performAsidControlInvocation _)

theorem pz_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : PZK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_storeAsidPoolEntry _ _ _)

theorem pz_performAsidPoolInvocation (iv : AsidPoolInvocation) : PZK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performAsidPoolInvocation _)

theorem pz_portIn (f : MachineMonad Data) : PZK (portIn (Z := Unit) f) := by
  unfold portIn; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_portIn _)

theorem pz_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : PZK (portOut (Z := Unit) f w) := by
  unfold portOut; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_portOut _ _)

theorem pz_performIoPortInvocation (i : IoPortInvocation) : PZK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performIoPortInvocation _)

theorem pz_setIoportMask (f l : IoPort) (val : Bool) : PZK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setIoportMask _ _ _)

theorem pz_performIoportControlInvocation (i : IoPortControlInvocation) : PZK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performIoportControlInvocation _)

theorem pz_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : PZK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPageDirectoryInvocation _)

theorem pz_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : PZK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPageInvocationUnmap _ _)

theorem pz_performPageInvocation (iv : PageInvocation) : PZK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPageInvocation _)

theorem pz_performPageTableInvocation (iv : PageTableInvocation) : PZK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPageTableInvocation _)

theorem pz_performPdptInvocation (iv : PdptInvocation) : PZK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPdptInvocation _)

theorem pz_archPerformInvocation (i : ArchInvocation) : PZKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPerformInvocation _)

theorem pz_freeIoportRange (f l : IoPort) : PZK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_freeIoportRange _ _)

theorem pz_archPostCapDeletion (ac : ArchCap) : PZK (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPostCapDeletion _)

theorem pz_archPostModifyRegisters (cur t : ObjRef) : PZK (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPostModifyRegisters _ _)

theorem pz_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : PZK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPostResetUntyped _ _)

theorem pz_loadFpuState (t : ObjRef) : PZK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_loadFpuState _)

theorem pz_saveFpuState (t : ObjRef) : PZK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_saveFpuState _)

theorem pz_setX64CurrentFpuOwner (newOwner : Option ObjRef) : PZK (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setX64CurrentFpuOwner _)

theorem pz_switchLocalFpuOwner (newOwner : Option ObjRef) : PZK (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_switchLocalFpuOwner _)

theorem pz_fpuRelease (threadPtr : ObjRef) : PZK (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fpuRelease _)

theorem pz_lazyFpuRestore (threadPtr : ObjRef) : PZK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_lazyFpuRestore _)

theorem pz_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : PZK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPostSetFlags _ _)

theorem pz_archPrepareNextDomain  : PZK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPrepareNextDomain)

theorem pz_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : PZK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archPrepareSetDomain _ _)

theorem pz_archSwitchToIdleThread  : PZK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archSwitchToIdleThread)

theorem pz_archSwitchToThread (t : ObjRef) : PZK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_archSwitchToThread _)

theorem pz_getScRefillReady (scPtr : ObjRef) : PZK (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getScRefillReady _)

theorem pz_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : PZK (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getScRefillSufficient _ _)

theorem pz_getTcbQueue (d : Domain) (prio : Priority) : PZK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getTcbQueue _ _)

theorem pz_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : PZK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setTcbQueue _ _ _)

theorem pz_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : PZK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbSchedAction _ _)

theorem pz_rescheduleRequired  : PZK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_rescheduleRequired)

theorem pz_possibleSwitchTo (target : ObjRef) : PZK (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_possibleSwitchTo _)

theorem pz_tcbReleaseRemove (tcbPtr : ObjRef) : PZK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbReleaseRemove _)

theorem pz_tcbReleaseDequeue  : PZK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_tcbReleaseDequeue)

theorem pz_awaken  : PZK (awaken (Z := Unit)) := by
  unfold awaken; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_awaken)

theorem pz_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : PZK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getSimpleKo _ _)

theorem pz_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : PZK (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_updateSkObjRef _ _ _ _)

theorem pz_bindNotification (tcbptr ntfnptr : ObjRef) : PZK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_bindNotification _ _)

theorem pz_bindScReply (scPtr replyPtr : ObjRef) : PZK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_bindScReply _ _)

theorem pz_getBlockingObject (state : ThreadState) : PZK (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getBlockingObject _)

theorem pz_replyUnlinkTcb (t r : ObjRef) : PZK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvE
