/- ut7: IRQ-node frame lemmas `NK N`, part 2 (invA's NativeScope scripts renamed; see SpecInvUtNK1). -/
import Fl4Proofs.P3.SpecInvUtNK1
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef}

theorem nk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : NK N (setPt (Z := Unit) ptr pt) := by
  unfold setPt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setPt _ _)

theorem nk_storePte (p : ObjRef) (pte : PTE) : NK N (storePte (Z := Unit) p pte) := by
  unfold storePte; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storePte _ _)

theorem nk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : NK N (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unmapPage _ _ _ _)

theorem nk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : NK N (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_flushTable _ _ _ _)

theorem nk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : NK N (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_invalidatePageStructureCacheAsid _ _)

theorem nk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NK N (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unmapPageTable _ _ _)

theorem nk_flushAll (vspace : ObjRef) (asid : Asid) : NK N (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_flushAll _ _)

theorem nk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NK N (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unmapPd _ _ _)

theorem nk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NK N (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setPml4 _ _)

theorem nk_storePml4e (p : ObjRef) (pte : PML4E) : NK N (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storePml4e _ _)

theorem nk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NK N (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_unmapPdpt _ _ _)

theorem nk_archFinaliseCap (c : ArchCap) (x : Bool) : NK N (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archFinaliseCap _ _)

theorem nk_archGetSanitiseRegisterInfo (_t : ObjRef) : NK N (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archGetSanitiseRegisterInfo _)

theorem nk_setOriginal (slot : CslotPtr) (v : Bool) : NK N (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setOriginal _ _)

theorem nk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : NK N (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setUntypedCapAsFull _ _ _)

theorem nk_setCdt (t : Cdt) : NK N (setCdt (Z := Unit) t) := by
  unfold setCdt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setCdt _)

theorem nk_updateCdt (f : Cdt → Cdt) : NK N (updateCdt (Z := Unit) f) := by
  unfold updateCdt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateCdt _)

theorem nk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : NK N (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_capInsert _ _ _)

theorem nk_setIrqState (state : IrqState) (irq : Irq) : NK N (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setIrqState _ _)

theorem nk_updateIrqState (irq : Irq) (irqState : X64IRQState) : NK N (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateIrqState _ _)

theorem nk_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NK N m) : NKE N (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; nk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_withoutPreemption _ ?_)

theorem nk_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NKE N (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archInvokeIrqControl _)

theorem nk_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NK N (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archInvokeIrqHandler _)

theorem nk_archMaskIrqSignal (irq : Irq) : NK N (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archMaskIrqSignal _)

theorem nk_performAsidControlInvocation (iv : AsidControlInvocation) : NK N (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performAsidControlInvocation _)

theorem nk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : NK N (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_storeAsidPoolEntry _ _ _)

theorem nk_performAsidPoolInvocation (iv : AsidPoolInvocation) : NK N (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performAsidPoolInvocation _)

theorem nk_portIn (f : MachineMonad Data) : NK N (portIn (Z := Unit) f) := by
  unfold portIn; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_portIn _)

theorem nk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : NK N (portOut (Z := Unit) f w) := by
  unfold portOut; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_portOut _ _)

theorem nk_performIoPortInvocation (i : IoPortInvocation) : NK N (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performIoPortInvocation _)

theorem nk_setIoportMask (f l : IoPort) (val : Bool) : NK N (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setIoportMask _ _ _)

theorem nk_performIoportControlInvocation (i : IoPortControlInvocation) : NK N (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performIoportControlInvocation _)

theorem nk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : NK N (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPageDirectoryInvocation _)

theorem nk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : NK N (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPageInvocationUnmap _ _)

theorem nk_performPageInvocation (iv : PageInvocation) : NK N (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPageInvocation _)

theorem nk_performPageTableInvocation (iv : PageTableInvocation) : NK N (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPageTableInvocation _)

theorem nk_performPdptInvocation (iv : PdptInvocation) : NK N (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPdptInvocation _)

theorem nk_archPerformInvocation (i : ArchInvocation) : NKE N (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPerformInvocation _)

theorem nk_freeIoportRange (f l : IoPort) : NK N (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_freeIoportRange _ _)

theorem nk_archPostCapDeletion (ac : ArchCap) : NK N (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPostCapDeletion _)

theorem nk_archPostModifyRegisters (cur t : ObjRef) : NK N (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPostModifyRegisters _ _)

theorem nk_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NK N (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPostResetUntyped _ _)

theorem nk_loadFpuState (t : ObjRef) : NK N (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_loadFpuState _)

theorem nk_saveFpuState (t : ObjRef) : NK N (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_saveFpuState _)

theorem nk_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NK N (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setX64CurrentFpuOwner _)

theorem nk_switchLocalFpuOwner (newOwner : Option ObjRef) : NK N (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_switchLocalFpuOwner _)

theorem nk_fpuRelease (threadPtr : ObjRef) : NK N (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fpuRelease _)

theorem nk_lazyFpuRestore (threadPtr : ObjRef) : NK N (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_lazyFpuRestore _)

theorem nk_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NK N (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPostSetFlags _ _)

theorem nk_archPrepareNextDomain  : NK N (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPrepareNextDomain)

theorem nk_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NK N (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archPrepareSetDomain _ _)

theorem nk_archSwitchToIdleThread  : NK N (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archSwitchToIdleThread)

theorem nk_archSwitchToThread (t : ObjRef) : NK N (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_archSwitchToThread _)

theorem nk_getScRefillReady (scPtr : ObjRef) : NK N (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getScRefillReady _)

theorem nk_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NK N (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getScRefillSufficient _ _)

theorem nk_getTcbQueue (d : Domain) (prio : Priority) : NK N (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getTcbQueue _ _)

theorem nk_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NK N (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setTcbQueue _ _ _)

theorem nk_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NK N (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbSchedAction _ _)

theorem nk_rescheduleRequired  : NK N (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_rescheduleRequired)

theorem nk_possibleSwitchTo (target : ObjRef) : NK N (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_possibleSwitchTo _)

theorem nk_tcbReleaseRemove (tcbPtr : ObjRef) : NK N (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbReleaseRemove _)

theorem nk_tcbReleaseDequeue  : NK N (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_tcbReleaseDequeue)

theorem nk_awaken  : NK N (awaken (Z := Unit)) := by
  unfold awaken; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_awaken)

theorem nk_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NK N (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getSimpleKo _ _)

theorem nk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : NK N (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_updateSkObjRef _ _ _ _)

theorem nk_bindNotification (tcbptr ntfnptr : ObjRef) : NK N (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_bindNotification _ _)

theorem nk_bindScReply (scPtr replyPtr : ObjRef) : NK N (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_bindScReply _ _)

theorem nk_getBlockingObject (state : ThreadState) : NK N (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getBlockingObject _)

theorem nk_replyUnlinkTcb (t r : ObjRef) : NK N (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_replyUnlinkTcb _ _)
end

end Fl4Proofs.P3.SInvU
