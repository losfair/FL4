/- il1: IfLiveT family lemmas, part 2 (generated; see SpecInvNtfnQL1). -/
import Fl4Proofs.P3.SpecInvNtfnQL1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem il_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : ILK Kq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setCurrentVspaceRoot _ _)

theorem il_setVmRoot (tcb : ObjRef) : ILK Kq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setVmRoot _)

theorem il_deleteAsid (asid : Asid) (pml4 : ObjRef) : ILK Kq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_deleteAsid _ _)

theorem il_deleteAsidPool (base : Asid) (ptr : ObjRef) : ILK Kq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_deleteAsidPool _ _)

theorem il_getPt (ptr : ObjRef) : ILK Kq (getPt (Z := Unit) ptr) := by
  unfold getPt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getPt _)

theorem il_getPte (ptr : ObjRef) : ILK Kq (getPte (Z := Unit) ptr) := by
  unfold getPte; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getPte _)

theorem il_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : ILK Kq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setPd _ _)

theorem il_storePde (p : ObjRef) (pde : PDE) : ILK Kq (storePde (Z := Unit) p pde) := by
  unfold storePde; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_storePde _ _)

theorem il_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : ILK Kq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setPdpt _ _)

theorem il_storePdpte (p : ObjRef) (pte : PDPTE) : ILK Kq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_storePdpte _ _)

theorem il_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : ILK Kq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setPt _ _)

theorem il_storePte (p : ObjRef) (pte : PTE) : ILK Kq (storePte (Z := Unit) p pte) := by
  unfold storePte; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_storePte _ _)

theorem il_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : ILK Kq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unmapPage _ _ _ _)

theorem il_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : ILK Kq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_flushTable _ _ _ _)

theorem il_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : ILK Kq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invalidatePageStructureCacheAsid _ _)

theorem il_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : ILK Kq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unmapPageTable _ _ _)

theorem il_flushAll (vspace : ObjRef) (asid : Asid) : ILK Kq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_flushAll _ _)

theorem il_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : ILK Kq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unmapPd _ _ _)

theorem il_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : ILK Kq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setPml4 _ _)

theorem il_storePml4e (p : ObjRef) (pte : PML4E) : ILK Kq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_storePml4e _ _)

theorem il_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : ILK Kq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_unmapPdpt _ _ _)

theorem il_archFinaliseCap (c : ArchCap) (x : Bool) : ILK Kq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archFinaliseCap _ _)

theorem il_archGetSanitiseRegisterInfo (_t : ObjRef) : ILK Kq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archGetSanitiseRegisterInfo _)

theorem il_setOriginal (slot : CslotPtr) (v : Bool) : ILK Kq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setOriginal _ _)

theorem il_setCdt (t : Cdt) : ILK Kq (setCdt (Z := Unit) t) := by
  unfold setCdt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setCdt _)

theorem il_updateCdt (f : Cdt → Cdt) : ILK Kq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateCdt _)

theorem il_setIrqState (state : IrqState) (irq : Irq) : ILK Kq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setIrqState _ _)

theorem il_updateIrqState (irq : Irq) (irqState : X64IRQState) : ILK Kq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_updateIrqState _ _)

theorem il_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : ILK Kq m) : ILKE Kq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_withoutPreemption _ ?_)

theorem il_archInvokeIrqControl (aic : ArchIrqControlInvocation) : ILKE Kq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archInvokeIrqControl _)

theorem il_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : ILK Kq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archInvokeIrqHandler _)

theorem il_archMaskIrqSignal (irq : Irq) : ILK Kq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archMaskIrqSignal _)

theorem il_setIoportMask (f l : IoPort) (val : Bool) : ILK Kq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setIoportMask _ _ _)

theorem il_freeIoportRange (f l : IoPort) : ILK Kq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_freeIoportRange _ _)

theorem il_archPostCapDeletion (ac : ArchCap) : ILK Kq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPostCapDeletion _)

theorem il_archPostModifyRegisters (cur t : ObjRef) : ILK Kq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPostModifyRegisters _ _)

theorem il_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : ILK Kq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPostResetUntyped _ _)

theorem il_loadFpuState (t : ObjRef) : ILK Kq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_loadFpuState _)

theorem il_saveFpuState (t : ObjRef) : ILK Kq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_saveFpuState _)

theorem il_setX64CurrentFpuOwner (newOwner : Option ObjRef) : ILK Kq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setX64CurrentFpuOwner _)

theorem il_switchLocalFpuOwner (newOwner : Option ObjRef) : ILK Kq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_switchLocalFpuOwner _)

theorem il_fpuRelease (threadPtr : ObjRef) : ILK Kq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fpuRelease _)

theorem il_lazyFpuRestore (threadPtr : ObjRef) : ILK Kq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lazyFpuRestore _)

theorem il_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : ILK Kq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPostSetFlags _ _)

theorem il_archPrepareNextDomain  : ILK Kq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPrepareNextDomain)

theorem il_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : ILK Kq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archPrepareSetDomain _ _)

theorem il_archSwitchToIdleThread  : ILK Kq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archSwitchToIdleThread)

theorem il_archSwitchToThread (t : ObjRef) : ILK Kq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_archSwitchToThread _)

theorem il_getScRefillReady (scPtr : ObjRef) : ILK Kq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getScRefillReady _)

theorem il_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : ILK Kq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getScRefillSufficient _ _)

theorem il_getTcbQueue (d : Domain) (prio : Priority) : ILK Kq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getTcbQueue _ _)

theorem il_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : ILK Kq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setTcbQueue _ _ _)

theorem il_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : ILK Kq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbSchedAction _ _)

theorem il_rescheduleRequired  : ILK Kq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_rescheduleRequired)

theorem il_possibleSwitchTo (target : ObjRef) : ILK Kq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_possibleSwitchTo _)

theorem il_tcbReleaseRemove (tcbPtr : ObjRef) : ILK Kq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbReleaseRemove _)

theorem il_tcbReleaseDequeue  : ILK Kq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_tcbReleaseDequeue)

theorem il_awaken  : ILK Kq (awaken (Z := Unit)) := by
  unfold awaken; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_awaken)
end

end Fl4Proofs.P3.SInv
