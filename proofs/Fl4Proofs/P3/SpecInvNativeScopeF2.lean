/- invA: NativeScope frame lemmas, part 2 (generated; see SpecInvNativeScopeF1). -/
import Fl4Proofs.P3.SpecInvNativeScopeF1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem ns_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : NSK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPt _ _)

theorem ns_storePte (p : ObjRef) (pte : PTE) : NSK (storePte (Z := Unit) p pte) := by
  unfold storePte; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePte _ _)

theorem ns_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : NSK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPage _ _ _ _)

theorem ns_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : NSK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_flushTable _ _ _ _)

theorem ns_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : NSK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_invalidatePageStructureCacheAsid _ _)

theorem ns_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NSK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPageTable _ _ _)

theorem ns_flushAll (vspace : ObjRef) (asid : Asid) : NSK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_flushAll _ _)

theorem ns_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NSK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPd _ _ _)

theorem ns_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NSK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setPml4 _ _)

theorem ns_storePml4e (p : ObjRef) (pte : PML4E) : NSK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storePml4e _ _)

theorem ns_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NSK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_unmapPdpt _ _ _)

theorem ns_archFinaliseCap (c : ArchCap) (x : Bool) : NSK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archFinaliseCap _ _)

theorem ns_archGetSanitiseRegisterInfo (_t : ObjRef) : NSK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archGetSanitiseRegisterInfo _)

theorem ns_setOriginal (slot : CslotPtr) (v : Bool) : NSK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setOriginal _ _)

theorem ns_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : NSK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setUntypedCapAsFull _ _ _)

theorem ns_setCdt (t : Cdt) : NSK (setCdt (Z := Unit) t) := by
  unfold setCdt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setCdt _)

theorem ns_updateCdt (f : Cdt → Cdt) : NSK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateCdt _)

theorem ns_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : NSK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_capInsert _ _ _)

theorem ns_setIrqState (state : IrqState) (irq : Irq) : NSK (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setIrqState _ _)

theorem ns_updateIrqState (irq : Irq) (irqState : X64IRQState) : NSK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateIrqState _ _)

theorem ns_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NSK m) : NSKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ns_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_withoutPreemption _ ?_)

theorem ns_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NSKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archInvokeIrqControl _)

theorem ns_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NSK (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archInvokeIrqHandler _)

theorem ns_archMaskIrqSignal (irq : Irq) : NSK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archMaskIrqSignal _)

theorem ns_performAsidControlInvocation (iv : AsidControlInvocation) : NSK (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performAsidControlInvocation _)

theorem ns_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NSK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_storeAsidPoolEntry _ _ _)

theorem ns_performAsidPoolInvocation (iv : AsidPoolInvocation) : NSK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performAsidPoolInvocation _)

theorem ns_portIn (f : MachineMonad Data) : NSK (portIn (Z := Unit) f) := by
  unfold portIn; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_portIn _)

theorem ns_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NSK (portOut (Z := Unit) f w) := by
  unfold portOut; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_portOut _ _)

theorem ns_performIoPortInvocation (i : IoPortInvocation) : NSK (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performIoPortInvocation _)

theorem ns_setIoportMask (f l : IoPort) (val : Bool) : NSK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setIoportMask _ _ _)

theorem ns_performIoportControlInvocation (i : IoPortControlInvocation) : NSK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performIoportControlInvocation _)

theorem ns_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NSK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageDirectoryInvocation _)

theorem ns_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NSK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageInvocationUnmap _ _)

theorem ns_performPageInvocation (iv : PageInvocation) : NSK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageInvocation _)

theorem ns_performPageTableInvocation (iv : PageTableInvocation) : NSK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPageTableInvocation _)

theorem ns_performPdptInvocation (iv : PdptInvocation) : NSK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPdptInvocation _)

theorem ns_archPerformInvocation (i : ArchInvocation) : NSKE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPerformInvocation _)

theorem ns_freeIoportRange (f l : IoPort) : NSK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_freeIoportRange _ _)

theorem ns_archPostCapDeletion (ac : ArchCap) : NSK (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostCapDeletion _)

theorem ns_archPostModifyRegisters (cur t : ObjRef) : NSK (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostModifyRegisters _ _)

theorem ns_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NSK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostResetUntyped _ _)

theorem ns_loadFpuState (t : ObjRef) : NSK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_loadFpuState _)

theorem ns_saveFpuState (t : ObjRef) : NSK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_saveFpuState _)

theorem ns_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NSK (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setX64CurrentFpuOwner _)

theorem ns_switchLocalFpuOwner (newOwner : Option ObjRef) : NSK (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchLocalFpuOwner _)

theorem ns_fpuRelease (threadPtr : ObjRef) : NSK (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fpuRelease _)

theorem ns_lazyFpuRestore (threadPtr : ObjRef) : NSK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_lazyFpuRestore _)

theorem ns_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NSK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPostSetFlags _ _)

theorem ns_archPrepareNextDomain  : NSK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPrepareNextDomain)

theorem ns_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NSK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archPrepareSetDomain _ _)

theorem ns_archSwitchToIdleThread  : NSK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archSwitchToIdleThread)

theorem ns_archSwitchToThread (t : ObjRef) : NSK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_archSwitchToThread _)

theorem ns_getScRefillReady (scPtr : ObjRef) : NSK (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScRefillReady _)

theorem ns_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NSK (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScRefillSufficient _ _)

theorem ns_getTcbQueue (d : Domain) (prio : Priority) : NSK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getTcbQueue _ _)

theorem ns_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NSK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setTcbQueue _ _ _)

theorem ns_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NSK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbSchedAction _ _)

theorem ns_rescheduleRequired  : NSK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_rescheduleRequired)

theorem ns_possibleSwitchTo (target : ObjRef) : NSK (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_possibleSwitchTo _)

theorem ns_tcbReleaseRemove (tcbPtr : ObjRef) : NSK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseRemove _)

theorem ns_tcbReleaseDequeue  : NSK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_tcbReleaseDequeue)

theorem ns_awaken  : NSK (awaken (Z := Unit)) := by
  unfold awaken; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_awaken)

theorem ns_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NSK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getSimpleKo _ _)

theorem ns_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : NSK (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_updateSkObjRef _ _ _ _)

theorem ns_bindNotification (tcbptr ntfnptr : ObjRef) : NSK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_bindNotification _ _)

theorem ns_bindScReply (scPtr replyPtr : ObjRef) : NSK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_bindScReply _ _)

theorem ns_getBlockingObject (state : ThreadState) : NSK (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getBlockingObject _)

theorem ns_replyUnlinkTcb (t r : ObjRef) : NSK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInv
