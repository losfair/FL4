/- sl1: ScLive family lemmas, part 2 (generated; see SpecInvSlF1). -/
import Fl4Proofs.P3.SpecInvSlF1
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Iq : ObjRef × ObjRef} {Kq : List ObjRef}

theorem sl_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setCurrentVspaceRoot _ _)

theorem sl_setVmRoot (tcb : ObjRef) : SLK Iq Kq (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setVmRoot _)

theorem sl_deleteAsid (asid : Asid) (pml4 : ObjRef) : SLK Iq Kq (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deleteAsid _ _)

theorem sl_deleteAsidPool (base : Asid) (ptr : ObjRef) : SLK Iq Kq (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deleteAsidPool _ _)

theorem sl_getPt (ptr : ObjRef) : SLK Iq Kq (getPt (Z := Unit) ptr) := by
  unfold getPt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPt _)

theorem sl_getPte (ptr : ObjRef) : SLK Iq Kq (getPte (Z := Unit) ptr) := by
  unfold getPte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getPte _)

theorem sl_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SLK Iq Kq (setPd (Z := Unit) ptr pd) := by
  unfold setPd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPd _ _)

theorem sl_storePde (p : ObjRef) (pde : PDE) : SLK Iq Kq (storePde (Z := Unit) p pde) := by
  unfold storePde; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePde _ _)

theorem sl_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SLK Iq Kq (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPdpt _ _)

theorem sl_storePdpte (p : ObjRef) (pte : PDPTE) : SLK Iq Kq (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePdpte _ _)

theorem sl_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SLK Iq Kq (setPt (Z := Unit) ptr pt) := by
  unfold setPt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPt _ _)

theorem sl_storePte (p : ObjRef) (pte : PTE) : SLK Iq Kq (storePte (Z := Unit) p pte) := by
  unfold storePte; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePte _ _)

theorem sl_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SLK Iq Kq (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPage _ _ _ _)

theorem sl_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : SLK Iq Kq (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_flushTable _ _ _ _)

theorem sl_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invalidatePageStructureCacheAsid _ _)

theorem sl_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SLK Iq Kq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPageTable _ _ _)

theorem sl_flushAll (vspace : ObjRef) (asid : Asid) : SLK Iq Kq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_flushAll _ _)

theorem sl_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SLK Iq Kq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPd _ _ _)

theorem sl_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SLK Iq Kq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setPml4 _ _)

theorem sl_storePml4e (p : ObjRef) (pte : PML4E) : SLK Iq Kq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_storePml4e _ _)

theorem sl_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SLK Iq Kq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_unmapPdpt _ _ _)

theorem sl_archFinaliseCap (c : ArchCap) (x : Bool) : SLK Iq Kq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archFinaliseCap _ _)

theorem sl_archGetSanitiseRegisterInfo (_t : ObjRef) : SLK Iq Kq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archGetSanitiseRegisterInfo _)

theorem sl_setOriginal (slot : CslotPtr) (v : Bool) : SLK Iq Kq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setOriginal _ _)

theorem sl_setCdt (t : Cdt) : SLK Iq Kq (setCdt (Z := Unit) t) := by
  unfold setCdt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setCdt _)

theorem sl_updateCdt (f : Cdt → Cdt) : SLK Iq Kq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateCdt _)

theorem sl_setIrqState (state : IrqState) (irq : Irq) : SLK Iq Kq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setIrqState _ _)

theorem sl_updateIrqState (irq : Irq) (irqState : X64IRQState) : SLK Iq Kq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_updateIrqState _ _)

theorem sl_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : SLK Iq Kq m) : SLKE Iq Kq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_withoutPreemption _ ?_)

theorem sl_archInvokeIrqControl (aic : ArchIrqControlInvocation) : SLKE Iq Kq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archInvokeIrqControl _)

theorem sl_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : SLK Iq Kq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archInvokeIrqHandler _)

theorem sl_archMaskIrqSignal (irq : Irq) : SLK Iq Kq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archMaskIrqSignal _)

theorem sl_setIoportMask (f l : IoPort) (val : Bool) : SLK Iq Kq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setIoportMask _ _ _)

theorem sl_freeIoportRange (f l : IoPort) : SLK Iq Kq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_freeIoportRange _ _)

theorem sl_archPostCapDeletion (ac : ArchCap) : SLK Iq Kq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostCapDeletion _)

theorem sl_archPostModifyRegisters (cur t : ObjRef) : SLK Iq Kq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostModifyRegisters _ _)

theorem sl_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : SLK Iq Kq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostResetUntyped _ _)

theorem sl_loadFpuState (t : ObjRef) : SLK Iq Kq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadFpuState _)

theorem sl_saveFpuState (t : ObjRef) : SLK Iq Kq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_saveFpuState _)

theorem sl_setX64CurrentFpuOwner (newOwner : Option ObjRef) : SLK Iq Kq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setX64CurrentFpuOwner _)

theorem sl_switchLocalFpuOwner (newOwner : Option ObjRef) : SLK Iq Kq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchLocalFpuOwner _)

theorem sl_fpuRelease (threadPtr : ObjRef) : SLK Iq Kq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fpuRelease _)

theorem sl_lazyFpuRestore (threadPtr : ObjRef) : SLK Iq Kq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lazyFpuRestore _)

theorem sl_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : SLK Iq Kq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPostSetFlags _ _)

theorem sl_archPrepareNextDomain  : SLK Iq Kq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPrepareNextDomain)

theorem sl_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : SLK Iq Kq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archPrepareSetDomain _ _)

theorem sl_archSwitchToIdleThread  : SLK Iq Kq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archSwitchToIdleThread)

theorem sl_archSwitchToThread (t : ObjRef) : SLK Iq Kq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_archSwitchToThread _)

theorem sl_getScRefillReady (scPtr : ObjRef) : SLK Iq Kq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScRefillReady _)

theorem sl_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : SLK Iq Kq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScRefillSufficient _ _)

theorem sl_getTcbQueue (d : Domain) (prio : Priority) : SLK Iq Kq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getTcbQueue _ _)

theorem sl_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : SLK Iq Kq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setTcbQueue _ _ _)

theorem sl_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : SLK Iq Kq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbSchedAction _ _)

theorem sl_rescheduleRequired  : SLK Iq Kq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_rescheduleRequired)

theorem sl_possibleSwitchTo (target : ObjRef) : SLK Iq Kq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_possibleSwitchTo _)

theorem sl_tcbReleaseRemove (tcbPtr : ObjRef) : SLK Iq Kq (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseRemove _)

theorem sl_tcbReleaseDequeue  : SLK Iq Kq (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_tcbReleaseDequeue)
end

end Fl4Proofs.P3.SInvL
