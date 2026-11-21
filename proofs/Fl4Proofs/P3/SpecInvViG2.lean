
/- vi1: generated frames `IK (VIT N S T b)` (sg1's SpecInvSgI2 renamed, the idle-relevant writers removed; see SpecInvViG1). -/
import Fl4Proofs.P3.SpecInvViG1
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}

theorem vi_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : IK (VIT N S T b) (setPt (Z := Unit) ptr pt) := by
  unfold setPt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setPt _ _)

theorem vi_storePte (p : ObjRef) (pte : PTE) : IK (VIT N S T b) (storePte (Z := Unit) p pte) := by
  unfold storePte; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storePte _ _)

theorem vi_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : IK (VIT N S T b) (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unmapPage _ _ _ _)

theorem vi_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : IK (VIT N S T b) (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_flushTable _ _ _ _)

theorem vi_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : IK (VIT N S T b) (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_invalidatePageStructureCacheAsid _ _)

theorem vi_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : IK (VIT N S T b) (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unmapPageTable _ _ _)

theorem vi_flushAll (vspace : ObjRef) (asid : Asid) : IK (VIT N S T b) (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_flushAll _ _)

theorem vi_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : IK (VIT N S T b) (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unmapPd _ _ _)

theorem vi_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : IK (VIT N S T b) (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setPml4 _ _)

theorem vi_storePml4e (p : ObjRef) (pte : PML4E) : IK (VIT N S T b) (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storePml4e _ _)

theorem vi_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : IK (VIT N S T b) (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_unmapPdpt _ _ _)

theorem vi_archFinaliseCap (c : ArchCap) (x : Bool) : IK (VIT N S T b) (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archFinaliseCap _ _)

theorem vi_archGetSanitiseRegisterInfo (_t : ObjRef) : IK (VIT N S T b) (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archGetSanitiseRegisterInfo _)

theorem vi_setOriginal (slot : CslotPtr) (v : Bool) : IK (VIT N S T b) (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setOriginal _ _)

theorem vi_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : IK (VIT N S T b) (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setUntypedCapAsFull _ _ _)

theorem vi_setCdt (t : Cdt) : IK (VIT N S T b) (setCdt (Z := Unit) t) := by
  unfold setCdt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setCdt _)

theorem vi_updateCdt (f : Cdt → Cdt) : IK (VIT N S T b) (updateCdt (Z := Unit) f) := by
  unfold updateCdt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateCdt _)

theorem vi_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : IK (VIT N S T b) (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_capInsert _ _ _)

theorem vi_setIrqState (state : IrqState) (irq : Irq) : IK (VIT N S T b) (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setIrqState _ _)

theorem vi_updateIrqState (irq : Irq) (irqState : X64IRQState) : IK (VIT N S T b) (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateIrqState _ _)

theorem vi_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IK (VIT N S T b) m) : IKE (VIT N S T b) (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_withoutPreemption _ ?_)

theorem vi_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IKE (VIT N S T b) (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archInvokeIrqControl _)

theorem vi_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : IK (VIT N S T b) (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archInvokeIrqHandler _)

theorem vi_archMaskIrqSignal (irq : Irq) : IK (VIT N S T b) (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archMaskIrqSignal _)

theorem vi_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : IK (VIT N S T b) (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_storeAsidPoolEntry _ _ _)

theorem vi_performAsidPoolInvocation (iv : AsidPoolInvocation) : IK (VIT N S T b) (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performAsidPoolInvocation _)

theorem vi_portIn (f : MachineMonad Data) : IK (VIT N S T b) (portIn (Z := Unit) f) := by
  unfold portIn; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_portIn _)

theorem vi_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : IK (VIT N S T b) (portOut (Z := Unit) f w) := by
  unfold portOut; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_portOut _ _)

theorem vi_performIoPortInvocation (i : IoPortInvocation) : IK (VIT N S T b) (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performIoPortInvocation _)

theorem vi_setIoportMask (f l : IoPort) (val : Bool) : IK (VIT N S T b) (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setIoportMask _ _ _)

theorem vi_performIoportControlInvocation (i : IoPortControlInvocation) : IK (VIT N S T b) (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performIoportControlInvocation _)

theorem vi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : IK (VIT N S T b) (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPageDirectoryInvocation _)

theorem vi_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : IK (VIT N S T b) (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPageInvocationUnmap _ _)

theorem vi_performPageInvocation (iv : PageInvocation) : IK (VIT N S T b) (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPageInvocation _)

theorem vi_performPageTableInvocation (iv : PageTableInvocation) : IK (VIT N S T b) (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPageTableInvocation _)

theorem vi_performPdptInvocation (iv : PdptInvocation) : IK (VIT N S T b) (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPdptInvocation _)

theorem vi_freeIoportRange (f l : IoPort) : IK (VIT N S T b) (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_freeIoportRange _ _)

theorem vi_archPostCapDeletion (ac : ArchCap) : IK (VIT N S T b) (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPostCapDeletion _)

theorem vi_archPostModifyRegisters (cur t : ObjRef) : IK (VIT N S T b) (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPostModifyRegisters _ _)

theorem vi_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : IK (VIT N S T b) (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPostResetUntyped _ _)

theorem vi_loadFpuState (t : ObjRef) : IK (VIT N S T b) (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_loadFpuState _)

theorem vi_saveFpuState (t : ObjRef) : IK (VIT N S T b) (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_saveFpuState _)

theorem vi_setX64CurrentFpuOwner (newOwner : Option ObjRef) : IK (VIT N S T b) (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setX64CurrentFpuOwner _)

theorem vi_switchLocalFpuOwner (newOwner : Option ObjRef) : IK (VIT N S T b) (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_switchLocalFpuOwner _)

theorem vi_fpuRelease (threadPtr : ObjRef) : IK (VIT N S T b) (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fpuRelease _)

theorem vi_lazyFpuRestore (threadPtr : ObjRef) : IK (VIT N S T b) (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_lazyFpuRestore _)

theorem vi_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : IK (VIT N S T b) (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPostSetFlags _ _)

theorem vi_archPrepareNextDomain  : IK (VIT N S T b) (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPrepareNextDomain)

theorem vi_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : IK (VIT N S T b) (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archPrepareSetDomain _ _)

theorem vi_archSwitchToIdleThread  : IK (VIT N S T b) (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archSwitchToIdleThread)

theorem vi_archSwitchToThread (t : ObjRef) : IK (VIT N S T b) (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_archSwitchToThread _)

theorem vi_getScRefillReady (scPtr : ObjRef) : IK (VIT N S T b) (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getScRefillReady _)

theorem vi_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : IK (VIT N S T b) (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getScRefillSufficient _ _)

theorem vi_getTcbQueue (d : Domain) (prio : Priority) : IK (VIT N S T b) (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getTcbQueue _ _)

theorem vi_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : IK (VIT N S T b) (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setTcbQueue _ _ _)

theorem vi_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : IK (VIT N S T b) (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbSchedAction _ _)

theorem vi_rescheduleRequired  : IK (VIT N S T b) (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_rescheduleRequired)

theorem vi_possibleSwitchTo (target : ObjRef) : IK (VIT N S T b) (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_possibleSwitchTo _)

theorem vi_tcbReleaseRemove (tcbPtr : ObjRef) : IK (VIT N S T b) (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbReleaseRemove _)

theorem vi_tcbReleaseDequeue  : IK (VIT N S T b) (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_tcbReleaseDequeue)

theorem vi_awaken  : IK (VIT N S T b) (awaken (Z := Unit)) := by
  unfold awaken; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_awaken)

theorem vi_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : IK (VIT N S T b) (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getSimpleKo _ _)

theorem vi_getBlockingObject (state : ThreadState) : IK (VIT N S T b) (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getBlockingObject _)

end

end Fl4Proofs.P3.SInvI
