/- ft2: generic frame lemmas, part 2 (generated; see SpecInvFaultTcbsG1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsG1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Fq : FQ} {Sq : Set ObjRef} {Cq : ObjRef → Prop}

theorem fg_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : FGK Fq Sq Cq (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPageTable _ _ _)

theorem fg_flushAll (vspace : ObjRef) (asid : Asid) : FGK Fq Sq Cq (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_flushAll _ _)

theorem fg_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : FGK Fq Sq Cq (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPd _ _ _)

theorem fg_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : FGK Fq Sq Cq (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setPml4 _ _)

theorem fg_storePml4e (p : ObjRef) (pte : PML4E) : FGK Fq Sq Cq (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storePml4e _ _)

theorem fg_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : FGK Fq Sq Cq (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_unmapPdpt _ _ _)

theorem fg_archFinaliseCap (c : ArchCap) (x : Bool) : FGK Fq Sq Cq (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archFinaliseCap _ _)

theorem fg_archGetSanitiseRegisterInfo (_t : ObjRef) : FGK Fq Sq Cq (archGetSanitiseRegisterInfo (Z := Unit) _t) := by
  unfold archGetSanitiseRegisterInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archGetSanitiseRegisterInfo _)

theorem fg_setOriginal (slot : CslotPtr) (v : Bool) : FGK Fq Sq Cq (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setOriginal _ _)

theorem fg_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : FGK Fq Sq Cq (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setUntypedCapAsFull _ _ _)

theorem fg_setCdt (t : Cdt) : FGK Fq Sq Cq (setCdt (Z := Unit) t) := by
  unfold setCdt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setCdt _)

theorem fg_updateCdt (f : Cdt → Cdt) : FGK Fq Sq Cq (updateCdt (Z := Unit) f) := by
  unfold updateCdt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateCdt _)

theorem fg_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : FGK Fq Sq Cq (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_capInsert _ _ _)

theorem fg_setIrqState (state : IrqState) (irq : Irq) : FGK Fq Sq Cq (setIrqState (Z := Unit) state irq) := by
  unfold setIrqState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setIrqState _ _)

theorem fg_updateIrqState (irq : Irq) (irqState : X64IRQState) : FGK Fq Sq Cq (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_updateIrqState _ _)

theorem fg_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : FGK Fq Sq Cq m) : FGKE Fq Sq Cq (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_withoutPreemption _ ?_)

theorem fg_archInvokeIrqControl (aic : ArchIrqControlInvocation) : FGKE Fq Sq Cq (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archInvokeIrqControl _)

theorem fg_archInvokeIrqHandler (a0 : IrqHandlerInvocation) : FGK Fq Sq Cq (archInvokeIrqHandler (Z := Unit) a0) := by
  unfold archInvokeIrqHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archInvokeIrqHandler _)

theorem fg_archMaskIrqSignal (irq : Irq) : FGK Fq Sq Cq (archMaskIrqSignal (Z := Unit) irq) := by
  unfold archMaskIrqSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archMaskIrqSignal _)

theorem fg_performAsidControlInvocation (iv : AsidControlInvocation) : FGK Fq Sq Cq (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performAsidControlInvocation _)

theorem fg_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : FGK Fq Sq Cq (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storeAsidPoolEntry _ _ _)

theorem fg_performAsidPoolInvocation (iv : AsidPoolInvocation) : FGK Fq Sq Cq (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performAsidPoolInvocation _)

theorem fg_portIn (f : MachineMonad Data) : FGK Fq Sq Cq (portIn (Z := Unit) f) := by
  unfold portIn; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_portIn _)

theorem fg_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : FGK Fq Sq Cq (portOut (Z := Unit) f w) := by
  unfold portOut; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_portOut _ _)

theorem fg_performIoPortInvocation (i : IoPortInvocation) : FGK Fq Sq Cq (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performIoPortInvocation _)

theorem fg_setIoportMask (f l : IoPort) (val : Bool) : FGK Fq Sq Cq (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setIoportMask _ _ _)

theorem fg_performIoportControlInvocation (i : IoPortControlInvocation) : FGK Fq Sq Cq (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performIoportControlInvocation _)

theorem fg_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : FGK Fq Sq Cq (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageDirectoryInvocation _)

theorem fg_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : FGK Fq Sq Cq (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageInvocationUnmap _ _)

theorem fg_performPageInvocation (iv : PageInvocation) : FGK Fq Sq Cq (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageInvocation _)

theorem fg_performPageTableInvocation (iv : PageTableInvocation) : FGK Fq Sq Cq (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPageTableInvocation _)

theorem fg_performPdptInvocation (iv : PdptInvocation) : FGK Fq Sq Cq (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPdptInvocation _)

theorem fg_archPerformInvocation (i : ArchInvocation) : FGKE Fq Sq Cq (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPerformInvocation _)

theorem fg_freeIoportRange (f l : IoPort) : FGK Fq Sq Cq (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_freeIoportRange _ _)

theorem fg_archPostCapDeletion (ac : ArchCap) : FGK Fq Sq Cq (archPostCapDeletion (Z := Unit) ac) := by
  unfold archPostCapDeletion; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostCapDeletion _)

theorem fg_archPostModifyRegisters (cur t : ObjRef) : FGK Fq Sq Cq (archPostModifyRegisters (Z := Unit) cur t) := by
  unfold archPostModifyRegisters; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostModifyRegisters _ _)

theorem fg_archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : FGK Fq Sq Cq (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostResetUntyped _ _)

theorem fg_loadFpuState (t : ObjRef) : FGK Fq Sq Cq (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadFpuState _)

theorem fg_saveFpuState (t : ObjRef) : FGK Fq Sq Cq (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_saveFpuState _)

theorem fg_setX64CurrentFpuOwner (newOwner : Option ObjRef) : FGK Fq Sq Cq (setX64CurrentFpuOwner (Z := Unit) newOwner) := by
  unfold setX64CurrentFpuOwner; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setX64CurrentFpuOwner _)

theorem fg_switchLocalFpuOwner (newOwner : Option ObjRef) : FGK Fq Sq Cq (switchLocalFpuOwner (Z := Unit) newOwner) := by
  unfold switchLocalFpuOwner; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchLocalFpuOwner _)

theorem fg_fpuRelease (threadPtr : ObjRef) : FGK Fq Sq Cq (fpuRelease (Z := Unit) threadPtr) := by
  unfold fpuRelease; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fpuRelease _)

theorem fg_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : FGK Fq Sq Cq (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_threadGet _ _)

theorem fg_lazyFpuRestore (threadPtr : ObjRef) : FGK Fq Sq Cq (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lazyFpuRestore _)

theorem fg_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : FGK Fq Sq Cq (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPostSetFlags _ _)

theorem fg_archPrepareNextDomain  : FGK Fq Sq Cq (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPrepareNextDomain)

theorem fg_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : FGK Fq Sq Cq (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archPrepareSetDomain _ _)

theorem fg_archSwitchToIdleThread  : FGK Fq Sq Cq (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archSwitchToIdleThread)

theorem fg_archSwitchToThread (t : ObjRef) : FGK Fq Sq Cq (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_archSwitchToThread _)

theorem fg_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : FGK Fq Sq Cq (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getTcbObjRef _ _)

theorem fg_getScRefillReady (scPtr : ObjRef) : FGK Fq Sq Cq (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScRefillReady _)

theorem fg_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : FGK Fq Sq Cq (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScRefillSufficient _ _)

theorem fg_setSchedulerAction (action : SchedulerAction) : FGK Fq Sq Cq (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setSchedulerAction _)

theorem fg_getTcbQueue (d : Domain) (prio : Priority) : FGK Fq Sq Cq (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getTcbQueue _ _)

theorem fg_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : FGK Fq Sq Cq (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setTcbQueue _ _ _)

theorem fg_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : FGK Fq Sq Cq (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_tcbSchedAction _ _)

theorem fg_rescheduleRequired  : FGK Fq Sq Cq (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_rescheduleRequired)

theorem fg_possibleSwitchTo (target : ObjRef) : FGK Fq Sq Cq (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_possibleSwitchTo _)
end

end Fl4Proofs.P3.SInv
