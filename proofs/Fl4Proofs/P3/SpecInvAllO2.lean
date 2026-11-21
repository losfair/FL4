/- g1c: OnlyIdle frame lemmas, part 2 (generated; see SpecInvAllO1). -/
import Fl4Proofs.P3.SpecInvAllO1
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem oi_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : OIK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPt _ _)

theorem oi_storePte (p : ObjRef) (pte : PTE) : OIK N (storePte (Z := Unit) p pte) := by
  unfold storePte; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePte _ _)

theorem oi_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : OIK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPage _ _ _ _)

theorem oi_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : OIK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushTable _ _ _ _)

theorem oi_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : OIK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_invalidatePageStructureCacheAsid _ _)

theorem oi_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : OIK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPageTable _ _ _)

theorem oi_flushAll (vspace : ObjRef) (asid : Asid) : OIK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_flushAll _ _)

theorem oi_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : OIK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPd _ _ _)

theorem oi_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : OIK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setPml4 _ _)

theorem oi_storePml4e (p : ObjRef) (pte : PML4E) : OIK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storePml4e _ _)

theorem oi_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : OIK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_unmapPdpt _ _ _)

theorem oi_archFinaliseCap (c : ArchCap) (x : Bool) : OIK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archFinaliseCap _ _)

theorem oi_archGetSanitiseRegisterInfo (_t : ObjRef) : OIK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archGetSanitiseRegisterInfo _)

theorem oi_setOriginal (slot : CslotPtr) (v : Bool) : OIK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setOriginal _ _)

theorem oi_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : OIK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setUntypedCapAsFull _ _ _)

theorem oi_setCdt (t : Cdt) : OIK N (setCdt (Z := Unit) t) := by
  unfold setCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setCdt _)

theorem oi_updateCdt (f : Cdt → Cdt) : OIK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateCdt _)

theorem oi_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : OIK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_capInsert _ _ _)

theorem oi_setIrqState (state : IrqState) (irq : Irq) : OIK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIrqState _ _)

theorem oi_updateIrqState (irq : Irq) (irqState : X64IRQState) : OIK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateIrqState _ _)

theorem oi_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : OIK N m) : OIKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; oi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_withoutPreemption _ ?_)

theorem oi_archInvokeIrqControl (aic : ArchIrqControlInvocation) : OIKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqControl _)

theorem oi_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : OIK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archInvokeIrqHandler _)

theorem oi_archMaskIrqSignal (irq : Irq) : OIK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archMaskIrqSignal _)

theorem oi_performAsidControlInvocation (iv : AsidControlInvocation) : OIK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performAsidControlInvocation _)

theorem oi_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : OIK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_storeAsidPoolEntry _ _ _)

theorem oi_performAsidPoolInvocation (iv : AsidPoolInvocation) : OIK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performAsidPoolInvocation _)

theorem oi_portIn (f : MachineMonad Data) : OIK N (portIn (Z := Unit) f) := by
  unfold portIn; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portIn _)

theorem oi_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : OIK N (portOut (Z := Unit) f w) := by
  unfold portOut; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_portOut _ _)

theorem oi_performIoPortInvocation (i : IoPortInvocation) : OIK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoPortInvocation _)

theorem oi_setIoportMask (f l : IoPort) (val : Bool) : OIK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setIoportMask _ _ _)

theorem oi_performIoportControlInvocation (i : IoPortControlInvocation) : OIK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performIoportControlInvocation _)

theorem oi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : OIK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageDirectoryInvocation _)

theorem oi_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : OIK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocationUnmap _ _)

theorem oi_performPageInvocation (iv : PageInvocation) : OIK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageInvocation _)

theorem oi_performPageTableInvocation (iv : PageTableInvocation) : OIK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPageTableInvocation _)

theorem oi_performPdptInvocation (iv : PdptInvocation) : OIK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPdptInvocation _)

theorem oi_archPerformInvocation (i : ArchInvocation) : OIKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPerformInvocation _)

theorem oi_freeIoportRange (f l : IoPort) : OIK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_freeIoportRange _ _)

theorem oi_archPostCapDeletion (ac : ArchCap) : OIK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostCapDeletion _)

theorem oi_archPostModifyRegisters (cur t : ObjRef) : OIK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostModifyRegisters _ _)

theorem oi_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : OIK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostResetUntyped _ _)

theorem oi_loadFpuState (t : ObjRef) : OIK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_loadFpuState _)

theorem oi_saveFpuState (t : ObjRef) : OIK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_saveFpuState _)

theorem oi_setX64CurrentFpuOwner (newOwner : Option ObjRef) : OIK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setX64CurrentFpuOwner _)

theorem oi_switchLocalFpuOwner (newOwner : Option ObjRef) : OIK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchLocalFpuOwner _)

theorem oi_fpuRelease (threadPtr : ObjRef) : OIK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fpuRelease _)

theorem oi_lazyFpuRestore (threadPtr : ObjRef) : OIK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_lazyFpuRestore _)

theorem oi_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : OIK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPostSetFlags _ _)

theorem oi_archPrepareNextDomain  : OIK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPrepareNextDomain)

theorem oi_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : OIK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archPrepareSetDomain _ _)

theorem oi_archSwitchToIdleThread  : OIK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archSwitchToIdleThread)

theorem oi_archSwitchToThread (t : ObjRef) : OIK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_archSwitchToThread _)

theorem oi_getScRefillReady (scPtr : ObjRef) : OIK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillReady _)

theorem oi_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : OIK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScRefillSufficient _ _)

theorem oi_getTcbQueue (d : Domain) (prio : Priority) : OIK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getTcbQueue _ _)

theorem oi_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : OIK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setTcbQueue _ _ _)

theorem oi_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : OIK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbSchedAction _ _)

theorem oi_rescheduleRequired  : OIK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_rescheduleRequired)

theorem oi_possibleSwitchTo (target : ObjRef) : OIK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_possibleSwitchTo _)

theorem oi_tcbReleaseRemove (tcbPtr : ObjRef) : OIK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseRemove _)

theorem oi_tcbReleaseDequeue  : OIK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_tcbReleaseDequeue)

theorem oi_awaken  : OIK N (awaken (Z := Unit)) := by
  unfold awaken; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_awaken)

theorem oi_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : OIK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getSimpleKo _ _)

theorem oi_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : OIK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_updateSkObjRef _ _ _ _)

theorem oi_bindNotification (tcbptr ntfnptr : ObjRef) : OIK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindNotification _ _)

theorem oi_bindScReply (scPtr replyPtr : ObjRef) : OIK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_bindScReply _ _)

theorem oi_getBlockingObject (state : ThreadState) : OIK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getBlockingObject _)

theorem oi_replyUnlinkTcb (t r : ObjRef) : OIK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvAll
