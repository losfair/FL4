/- invA2: FaultTcbsS frame lemmas, part 2 (generated; see SpecInvFaultTcbsF1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsF1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem ft_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : FTK L (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPd _ _ _)

theorem ft_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : FTK L (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPml4 _ _)

theorem ft_storePml4e (p : ObjRef) (pte : PML4E) : FTK L (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePml4e _ _)

theorem ft_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : FTK L (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPdpt _ _ _)

theorem ft_archFinaliseCap (c : ArchCap) (x : Bool) : FTK L (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archFinaliseCap _ _)

theorem ft_archGetSanitiseRegisterInfo (_t : ObjRef) : FTK L (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archGetSanitiseRegisterInfo _)

theorem ft_setOriginal (slot : CslotPtr) (v : Bool) : FTK L (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setOriginal _ _)

theorem ft_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : FTK L (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setUntypedCapAsFull _ _ _)

theorem ft_setCdt (t : Cdt) : FTK L (setCdt (Z := Unit) t) := by
  unfold setCdt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCdt _)

theorem ft_updateCdt (f : Cdt → Cdt) : FTK L (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateCdt _)

theorem ft_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : FTK L (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_capInsert _ _ _)

theorem ft_setIrqState (state : IrqState) (irq : Irq) : FTK L (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setIrqState _ _)

theorem ft_updateIrqState (irq : Irq) (irqState : X64IRQState) : FTK L (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_updateIrqState _ _)

theorem ft_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : FTK L m) : FTKE L (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_withoutPreemption _ ?_)

theorem ft_archInvokeIrqControl (aic : ArchIrqControlInvocation) : FTKE L (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archInvokeIrqControl _)

theorem ft_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : FTK L (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archInvokeIrqHandler _)

theorem ft_archMaskIrqSignal (irq : Irq) : FTK L (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archMaskIrqSignal _)

theorem ft_performAsidControlInvocation (iv : AsidControlInvocation) : FTK L (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performAsidControlInvocation _)

theorem ft_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : FTK L (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storeAsidPoolEntry _ _ _)

theorem ft_performAsidPoolInvocation (iv : AsidPoolInvocation) : FTK L (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performAsidPoolInvocation _)

theorem ft_portIn (f : MachineMonad Data) : FTK L (portIn (Z := Unit) f) := by
  unfold portIn; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_portIn _)

theorem ft_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : FTK L (portOut (Z := Unit) f w) := by
  unfold portOut; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_portOut _ _)

theorem ft_performIoPortInvocation (i : IoPortInvocation) : FTK L (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performIoPortInvocation _)

theorem ft_setIoportMask (f l : IoPort) (val : Bool) : FTK L (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setIoportMask _ _ _)

theorem ft_performIoportControlInvocation (i : IoPortControlInvocation) : FTK L (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performIoportControlInvocation _)

theorem ft_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : FTK L (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageDirectoryInvocation _)

theorem ft_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : FTK L (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageInvocationUnmap _ _)

theorem ft_performPageInvocation (iv : PageInvocation) : FTK L (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageInvocation _)

theorem ft_performPageTableInvocation (iv : PageTableInvocation) : FTK L (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPageTableInvocation _)

theorem ft_performPdptInvocation (iv : PdptInvocation) : FTK L (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPdptInvocation _)

theorem ft_archPerformInvocation (i : ArchInvocation) : FTKE L (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPerformInvocation _)

theorem ft_freeIoportRange (f l : IoPort) : FTK L (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_freeIoportRange _ _)

theorem ft_archPostCapDeletion (ac : ArchCap) : FTK L (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostCapDeletion _)

theorem ft_archPostModifyRegisters (cur t : ObjRef) : FTK L (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostModifyRegisters _ _)

theorem ft_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : FTK L (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostResetUntyped _ _)

theorem ft_loadFpuState (t : ObjRef) : FTK L (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadFpuState _)

theorem ft_saveFpuState (t : ObjRef) : FTK L (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_saveFpuState _)

theorem ft_setX64CurrentFpuOwner (newOwner : Option ObjRef) : FTK L (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setX64CurrentFpuOwner _)

theorem ft_switchLocalFpuOwner (newOwner : Option ObjRef) : FTK L (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchLocalFpuOwner _)

theorem ft_fpuRelease (threadPtr : ObjRef) : FTK L (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fpuRelease _)

theorem ft_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : FTK L (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_threadGet _ _)

theorem ft_lazyFpuRestore (threadPtr : ObjRef) : FTK L (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lazyFpuRestore _)

theorem ft_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : FTK L (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPostSetFlags _ _)

theorem ft_archPrepareNextDomain  : FTK L (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPrepareNextDomain)

theorem ft_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : FTK L (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archPrepareSetDomain _ _)

theorem ft_archSwitchToIdleThread  : FTK L (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archSwitchToIdleThread)

theorem ft_archSwitchToThread (t : ObjRef) : FTK L (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archSwitchToThread _)

theorem ft_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : FTK L (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getTcbObjRef _ _)

theorem ft_getScRefillReady (scPtr : ObjRef) : FTK L (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScRefillReady _)

theorem ft_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : FTK L (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScRefillSufficient _ _)

theorem ft_setSchedulerAction (action : SchedulerAction) : FTK L (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setSchedulerAction _)

theorem ft_getTcbQueue (d : Domain) (prio : Priority) : FTK L (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getTcbQueue _ _)

theorem ft_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : FTK L (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setTcbQueue _ _ _)

theorem ft_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : FTK L (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbSchedAction _ _)

theorem ft_rescheduleRequired  : FTK L (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_rescheduleRequired)

theorem ft_possibleSwitchTo (target : ObjRef) : FTK L (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_possibleSwitchTo _)

theorem ft_tcbReleaseRemove (tcbPtr : ObjRef) : FTK L (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseRemove _)

theorem ft_tcbReleaseDequeue  : FTK L (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_tcbReleaseDequeue)

theorem ft_awaken  : FTK L (awaken (Z := Unit)) := by
  unfold awaken; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_awaken)

theorem ft_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : FTK L (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getSimpleKo _ _)
end

end Fl4Proofs.P3.SInv
