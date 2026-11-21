/- sl2: NtfnScB family lemmas, part 2 (generated; see SpecInvSlN1). -/
import Fl4Proofs.P3.SpecInvSlN1
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem nb_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : NBK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPd _ _)

theorem nb_storePde (p : ObjRef) (pde : PDE) : NBK (storePde (Z := Unit) p pde) := by
  unfold storePde; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePde _ _)

theorem nb_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : NBK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPdpt _ _)

theorem nb_storePdpte (p : ObjRef) (pte : PDPTE) : NBK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePdpte _ _)

theorem nb_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : NBK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPt _ _)

theorem nb_storePte (p : ObjRef) (pte : PTE) : NBK (storePte (Z := Unit) p pte) := by
  unfold storePte; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePte _ _)

theorem nb_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : NBK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPage _ _ _ _)

theorem nb_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : NBK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_flushTable _ _ _ _)

theorem nb_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : NBK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_invalidatePageStructureCacheAsid _ _)

theorem nb_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : NBK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPageTable _ _ _)

theorem nb_flushAll (vspace : ObjRef) (asid : Asid) : NBK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_flushAll _ _)

theorem nb_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : NBK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPd _ _ _)

theorem nb_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : NBK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setPml4 _ _)

theorem nb_storePml4e (p : ObjRef) (pte : PML4E) : NBK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_storePml4e _ _)

theorem nb_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : NBK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_unmapPdpt _ _ _)

theorem nb_archFinaliseCap (c : ArchCap) (x : Bool) : NBK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archFinaliseCap _ _)

theorem nb_archGetSanitiseRegisterInfo (_t : ObjRef) : NBK (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archGetSanitiseRegisterInfo _)

theorem nb_setOriginal (slot : CslotPtr) (v : Bool) : NBK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setOriginal _ _)

theorem nb_setCdt (t : Cdt) : NBK (setCdt (Z := Unit) t) := by
  unfold setCdt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setCdt _)

theorem nb_updateCdt (f : Cdt → Cdt) : NBK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateCdt _)

theorem nb_setIrqState (state : IrqState) (irq : Irq) : NBK (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setIrqState _ _)

theorem nb_updateIrqState (irq : Irq) (irqState : X64IRQState) : NBK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateIrqState _ _)

theorem nb_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : NBK m) : NBKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; nb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_withoutPreemption _ ?_)

theorem nb_archInvokeIrqControl (aic : ArchIrqControlInvocation) : NBKE (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archInvokeIrqControl _)

theorem nb_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : NBK (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archInvokeIrqHandler _)

theorem nb_archMaskIrqSignal (irq : Irq) : NBK (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archMaskIrqSignal _)

theorem nb_setIoportMask (f l : IoPort) (val : Bool) : NBK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setIoportMask _ _ _)

theorem nb_freeIoportRange (f l : IoPort) : NBK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_freeIoportRange _ _)

theorem nb_archPostCapDeletion (ac : ArchCap) : NBK (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostCapDeletion _)

theorem nb_archPostModifyRegisters (cur t : ObjRef) : NBK (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostModifyRegisters _ _)

theorem nb_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : NBK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostResetUntyped _ _)

theorem nb_loadFpuState (t : ObjRef) : NBK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_loadFpuState _)

theorem nb_saveFpuState (t : ObjRef) : NBK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_saveFpuState _)

theorem nb_setX64CurrentFpuOwner (newOwner : Option ObjRef) : NBK (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setX64CurrentFpuOwner _)

theorem nb_switchLocalFpuOwner (newOwner : Option ObjRef) : NBK (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchLocalFpuOwner _)

theorem nb_fpuRelease (threadPtr : ObjRef) : NBK (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fpuRelease _)

theorem nb_lazyFpuRestore (threadPtr : ObjRef) : NBK (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_lazyFpuRestore _)

theorem nb_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : NBK (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPostSetFlags _ _)

theorem nb_archPrepareNextDomain  : NBK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPrepareNextDomain)

theorem nb_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : NBK (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archPrepareSetDomain _ _)

theorem nb_archSwitchToIdleThread  : NBK (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archSwitchToIdleThread)

theorem nb_archSwitchToThread (t : ObjRef) : NBK (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_archSwitchToThread _)

theorem nb_getScRefillReady (scPtr : ObjRef) : NBK (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScRefillReady _)

theorem nb_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : NBK (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScRefillSufficient _ _)

theorem nb_getTcbQueue (d : Domain) (prio : Priority) : NBK (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getTcbQueue _ _)

theorem nb_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : NBK (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setTcbQueue _ _ _)

theorem nb_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : NBK (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbSchedAction _ _)

theorem nb_rescheduleRequired  : NBK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_rescheduleRequired)

theorem nb_possibleSwitchTo (target : ObjRef) : NBK (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_possibleSwitchTo _)

theorem nb_tcbReleaseRemove (tcbPtr : ObjRef) : NBK (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseRemove _)

theorem nb_tcbReleaseDequeue  : NBK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbReleaseDequeue)

theorem nb_awaken  : NBK (awaken (Z := Unit)) := by
  unfold awaken; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_awaken)

theorem nb_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : NBK (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getSimpleKo _ _)

theorem nb_bindNotification (tcbptr ntfnptr : ObjRef) : NBK (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_bindNotification _ _)

theorem nb_bindScReply (scPtr replyPtr : ObjRef) : NBK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_bindScReply _ _)

theorem nb_getBlockingObject (state : ThreadState) : NBK (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getBlockingObject _)

theorem nb_replyUnlinkTcb (t r : ObjRef) : NBK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_replyUnlinkTcb _ _)

theorem nb_tcbEpDequeue (tptr epPtr : ObjRef) : NBK (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_tcbEpDequeue _ _)

theorem nb_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : NBK (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_blockedCancelIpc _ _ _)

theorem nb_isRoundRobin (scPtr : ObjRef) : NBK (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isRoundRobin _)

theorem nb_getRefillHead (scPtr : ObjRef) : NBK (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getRefillHead _)

theorem nb_refillPopHead (scPtr : ObjRef) : NBK (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_refillPopHead _)

theorem nb_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : NBK (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_updateRefillHd _ _)
end

end Fl4Proofs.P3.SInvL
