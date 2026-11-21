/- sg1: idle-thread frame lemmas `IdK t` (ut7's SpecInvUtNK2 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvSgI1
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem idk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : IdK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setPt _ _)

theorem idk_storePte (p : ObjRef) (pte : PTE) : IdK N (storePte (Z := Unit) p pte) := by
  unfold storePte; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storePte _ _)

theorem idk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : IdK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unmapPage _ _ _ _)

theorem idk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : IdK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_flushTable _ _ _ _)

theorem idk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : IdK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_invalidatePageStructureCacheAsid _ _)

theorem idk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : IdK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unmapPageTable _ _ _)

theorem idk_flushAll (vspace : ObjRef) (asid : Asid) : IdK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_flushAll _ _)

theorem idk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : IdK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unmapPd _ _ _)

theorem idk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : IdK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setPml4 _ _)

theorem idk_storePml4e (p : ObjRef) (pte : PML4E) : IdK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storePml4e _ _)

theorem idk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : IdK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_unmapPdpt _ _ _)

theorem idk_archFinaliseCap (c : ArchCap) (x : Bool) : IdK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archFinaliseCap _ _)

theorem idk_archGetSanitiseRegisterInfo (_t : ObjRef) : IdK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archGetSanitiseRegisterInfo _)

theorem idk_setOriginal (slot : CslotPtr) (v : Bool) : IdK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setOriginal _ _)

theorem idk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : IdK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setUntypedCapAsFull _ _ _)

theorem idk_setCdt (t : Cdt) : IdK N (setCdt (Z := Unit) t) := by
  unfold setCdt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setCdt _)

theorem idk_updateCdt (f : Cdt → Cdt) : IdK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateCdt _)

theorem idk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : IdK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_capInsert _ _ _)

theorem idk_setIrqState (state : IrqState) (irq : Irq) : IdK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setIrqState _ _)

theorem idk_updateIrqState (irq : Irq) (irqState : X64IRQState) : IdK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateIrqState _ _)

theorem idk_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IdK N m) : IdKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; idk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_withoutPreemption _ ?_)

theorem idk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IdKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archInvokeIrqControl _)

theorem idk_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : IdK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archInvokeIrqHandler _)

theorem idk_archMaskIrqSignal (irq : Irq) : IdK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archMaskIrqSignal _)

theorem idk_performAsidControlInvocation (iv : AsidControlInvocation) : IdK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performAsidControlInvocation _)

theorem idk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : IdK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_storeAsidPoolEntry _ _ _)

theorem idk_performAsidPoolInvocation (iv : AsidPoolInvocation) : IdK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performAsidPoolInvocation _)

theorem idk_portIn (f : MachineMonad Data) : IdK N (portIn (Z := Unit) f) := by
  unfold portIn; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_portIn _)

theorem idk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : IdK N (portOut (Z := Unit) f w) := by
  unfold portOut; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_portOut _ _)

theorem idk_performIoPortInvocation (i : IoPortInvocation) : IdK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performIoPortInvocation _)

theorem idk_setIoportMask (f l : IoPort) (val : Bool) : IdK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setIoportMask _ _ _)

theorem idk_performIoportControlInvocation (i : IoPortControlInvocation) : IdK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performIoportControlInvocation _)

theorem idk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : IdK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPageDirectoryInvocation _)

theorem idk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : IdK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPageInvocationUnmap _ _)

theorem idk_performPageInvocation (iv : PageInvocation) : IdK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPageInvocation _)

theorem idk_performPageTableInvocation (iv : PageTableInvocation) : IdK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPageTableInvocation _)

theorem idk_performPdptInvocation (iv : PdptInvocation) : IdK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPdptInvocation _)

theorem idk_archPerformInvocation (i : ArchInvocation) : IdKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPerformInvocation _)

theorem idk_freeIoportRange (f l : IoPort) : IdK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_freeIoportRange _ _)

theorem idk_archPostCapDeletion (ac : ArchCap) : IdK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPostCapDeletion _)

theorem idk_archPostModifyRegisters (cur t : ObjRef) : IdK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPostModifyRegisters _ _)

theorem idk_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : IdK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPostResetUntyped _ _)

theorem idk_loadFpuState (t : ObjRef) : IdK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_loadFpuState _)

theorem idk_saveFpuState (t : ObjRef) : IdK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_saveFpuState _)

theorem idk_setX64CurrentFpuOwner (newOwner : Option ObjRef) : IdK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setX64CurrentFpuOwner _)

theorem idk_switchLocalFpuOwner (newOwner : Option ObjRef) : IdK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_switchLocalFpuOwner _)

theorem idk_fpuRelease (threadPtr : ObjRef) : IdK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fpuRelease _)

theorem idk_lazyFpuRestore (threadPtr : ObjRef) : IdK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_lazyFpuRestore _)

theorem idk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : IdK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPostSetFlags _ _)

theorem idk_archPrepareNextDomain  : IdK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPrepareNextDomain)

theorem idk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : IdK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archPrepareSetDomain _ _)

theorem idk_archSwitchToIdleThread  : IdK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archSwitchToIdleThread)

theorem idk_archSwitchToThread (t : ObjRef) : IdK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_archSwitchToThread _)

theorem idk_getScRefillReady (scPtr : ObjRef) : IdK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getScRefillReady _)

theorem idk_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : IdK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getScRefillSufficient _ _)

theorem idk_getTcbQueue (d : Domain) (prio : Priority) : IdK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getTcbQueue _ _)

theorem idk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : IdK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setTcbQueue _ _ _)

theorem idk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : IdK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbSchedAction _ _)

theorem idk_rescheduleRequired  : IdK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_rescheduleRequired)

theorem idk_possibleSwitchTo (target : ObjRef) : IdK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_possibleSwitchTo _)

theorem idk_tcbReleaseRemove (tcbPtr : ObjRef) : IdK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbReleaseRemove _)

theorem idk_tcbReleaseDequeue  : IdK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_tcbReleaseDequeue)

theorem idk_awaken  : IdK N (awaken (Z := Unit)) := by
  unfold awaken; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_awaken)

theorem idk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : IdK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getSimpleKo _ _)

theorem idk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : IdK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_updateSkObjRef _ _ _ _)

theorem idk_bindNotification (tcbptr ntfnptr : ObjRef) : IdK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_bindNotification _ _)

theorem idk_bindScReply (scPtr replyPtr : ObjRef) : IdK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_bindScReply _ _)

theorem idk_getBlockingObject (state : ThreadState) : IdK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getBlockingObject _)

theorem idk_replyUnlinkTcb (t r : ObjRef) : IdK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvG
