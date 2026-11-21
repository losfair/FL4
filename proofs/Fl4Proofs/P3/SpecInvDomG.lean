/-
P3 (DESIGN.md §9), invariant line G1 (invC): **`DL` leaves of the spec
functions** (SpecInvDomF's domain-list frame), bottom-up: a scripted copy of
the `DK` lemmas of VsDom, VsDomOps, DomRecDel, TcbDom, CnodeDom and AllDom
(`DK` -> `DL`; scratch-invC/genDL.py, untracked), whose cones reach FL4's
side. The recursive functions as in SpecInvDomF.
-/
import Fl4Proofs.P3.SpecInvDomF
import Fl4Proofs.P3.SpecInvDomL
open Classical

namespace Fl4Proofs.P3.SInvDom
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

theorem dl_setCap (c : Cap) (sl : CslotPtr) : DL (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setCap _ _)

theorem dl_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    DL (portOut (Z := Unit) f w) := by
  unfold portOut; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_portOut _ _)

theorem dl_getPt (ptr : ObjRef) : DL (getPt (Z := Unit) ptr) := by
  unfold getPt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPt _)

theorem dl_getPte (ptr : ObjRef) : DL (getPte (Z := Unit) ptr) := by
  unfold getPte; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPte _)

theorem dl_getPd (ptr : ObjRef) : DL (getPd (Z := Unit) ptr) := by
  unfold getPd; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPd _)

theorem dl_getPde (ptr : ObjRef) : DL (getPde (Z := Unit) ptr) := by
  unfold getPde; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPde _)

theorem dl_getPml4 (ptr : ObjRef) : DL (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPml4 _)

theorem dl_getPml4e (ptr : ObjRef) : DL (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPml4e _)

theorem dl_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : DLE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupPdptSlot _ _)

theorem dl_getPdpt (ptr : ObjRef) : DL (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPdpt _)

theorem dl_getPdpte (ptr : ObjRef) : DL (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getPdpte _)

theorem dl_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : DLE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupPdSlot _ _)

theorem dl_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : DLE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupPtSlot _ _)

theorem dl_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : DL (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setPdpt _ _)

theorem dl_storePdpte (p : ObjRef) (pte : PDPTE) : DL (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storePdpte _ _)

theorem dl_getAsidPool (ptr : ObjRef) : DL (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getAsidPool _)

theorem dl_findVspaceForAsid (asid : Asid) : DLE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_findVspaceForAsid _)

theorem dl_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : DL (setPt (Z := Unit) ptr pt) := by
  unfold setPt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setPt _ _)

theorem dl_storePte (p : ObjRef) (pte : PTE) : DL (storePte (Z := Unit) p pte) := by
  unfold storePte; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storePte _ _)

theorem dl_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : DL (setPd (Z := Unit) ptr pd) := by
  unfold setPd; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setPd _ _)

theorem dl_storePde (p : ObjRef) (pde : PDE) : DL (storePde (Z := Unit) p pde) := by
  unfold storePde; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storePde _ _)

theorem dl_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : DL (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unmapPage _ _ _ _)

theorem dl_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : DL (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performPageInvocationUnmap _ _)

theorem dl_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : DL (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setAsidPool _ _)

theorem dl_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : DL (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_flushTable _ _ _ _)

theorem dl_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : DL (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setPml4 _ _)

theorem dl_setOriginal (slot : CslotPtr) (v : Bool) : DL (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setOriginal _ _)

theorem dl_updateCdt (f : Cdt → Cdt) : DL (updateCdt (Z := Unit) f) := by
  unfold updateCdt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateCdt _)

theorem dl_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : DL (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setUntypedCapAsFull _ _ _)

theorem dl_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : DL (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_retypeRegion _ _ _ _ _)

theorem dl_storePml4e (p : ObjRef) (pte : PML4E) : DL (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storePml4e _ _)

theorem dl_flushAll (vspace : ObjRef) (asid : Asid) : DL (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_flushAll _ _)

theorem dl_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : DL (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unmapPdpt _ _ _)

theorem dl_setIoportMask (f l : IoPort) (val : Bool) : DL (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setIoportMask _ _ _)

theorem dl_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : DL (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_invalidatePageStructureCacheAsid _ _)

theorem dl_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : DL (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unmapPd _ _ _)

theorem dl_deleteObjects (ptr : Word) (bits : Nat) : DL (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_deleteObjects _ _)

theorem dl_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : DL (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capInsert _ _ _)

theorem dl_portIn (f : MachineMonad Data) : DL (portIn (Z := Unit) f) := by
  unfold portIn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_portIn _)

theorem dl_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : DL (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unmapPageTable _ _ _)

theorem dl_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : DL (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storeAsidPoolEntry _ _ _)

theorem dl_performPageInvocation (iv : PageInvocation) : DL (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performPageInvocation _)

theorem dl_performPageTableInvocation (iv : PageTableInvocation) : DL (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performPageTableInvocation _)

theorem dl_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : DL (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performPageDirectoryInvocation _)

theorem dl_performPdptInvocation (iv : PdptInvocation) : DL (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performPdptInvocation _)

theorem dl_performAsidPoolInvocation (iv : AsidPoolInvocation) : DL (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performAsidPoolInvocation _)

theorem dl_performAsidControlInvocation (iv : AsidControlInvocation) : DL (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performAsidControlInvocation _)

theorem dl_performIoPortInvocation (i : IoPortInvocation) : DL (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performIoPortInvocation _)

theorem dl_performIoportControlInvocation (i : IoPortControlInvocation) : DL (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performIoportControlInvocation _)

theorem dl_performDeriveSubframe (iv : Fl4SubframeInvocation) : DL (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performDeriveSubframe _)

theorem dl_performTestAndClearAccessed (_slot : ObjRef) : DL (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_performTestAndClearAccessed _)

theorem dl_performPml4Flush (i : Fl4Pml4Invocation) : DL (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact dl_flushAll _ _

theorem dle_archPerformInvocation (i : ArchInvocation) : DLE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE; cases i <;> dl_auto0

theorem dle_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : DLE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact dle_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; dl_auto0; exact dl_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; dl_auto0
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; dl_auto0

theorem dl_threadSet' (f : Tcb → Tcb) (t : ObjRef) : DL (threadSet (Z := Unit) f t) := by
  unfold threadSet; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_threadSet' _ _)

theorem dl_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : DL (threadGet (Z := Unit) f t) := by
  unfold threadGet; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_threadGet' _ _)

theorem dl_setThreadState' (t : ObjRef) (ts : ThreadState) : DL (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setThreadState' _ _)

theorem dl_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    DL (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getSimpleKo' _ _)

theorem dl_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    DL (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setSimpleKo' _ _ _)

theorem dl_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    DL (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateSkObjRef' _ _ _ _)

theorem dl_getSchedContext' (q : ObjRef) : DL (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getSchedContext' _)

theorem dl_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    DL (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateSchedContext' _ _)

theorem dl_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : DL (asUser (Z := Unit) t u) := by
  unfold asUser; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_asUser' _ _)

theorem dl_replyUnlinkTcb' (t r : ObjRef) : DL (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyUnlinkTcb' _ _)

theorem dl_getThreadState' (t : ObjRef) : DL (getThreadState (Z := Unit) t) := by
  unfold getThreadState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getThreadState' _)

theorem dl_cancelIpc' (t : ObjRef) : DL (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_cancelIpc' _)

theorem dl_suspend' (t : ObjRef) : DL (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_suspend' _)

theorem dl_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : DL (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getSkObjRef' _ _ _)

theorem dl_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : DL (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getScObjRef' _ _)

theorem dl_getIrqSlot' (irq : Irq) : DL (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getIrqSlot' _)

theorem dl_isFinalCap' (c : Cap) : DL (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_isFinalCap' _)

theorem dl_hwAsidInvalidate' (a : Asid) (v : ObjRef) : DL (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_hwAsidInvalidate' _ _)

theorem dl_getCurrentCr3' : DL (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getCurrentCr3' )

theorem dl_setCurrentCr3' (c : Cr3) : DL (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setCurrentCr3' _)

theorem dl_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : DL (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setCurrentVspaceRoot' _ _)

theorem dl_setVmRoot' (t : ObjRef) : DL (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setVmRoot' _)

theorem dl_freeIoportRange' (f l : IoPort) : DL (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_freeIoportRange' _ _)

theorem dl_setIrqState' (i : IrqState) (irq : Irq) : DL (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setIrqState' _ _)

theorem dl_deletedIrqHandler' (irq : Irq) : DL (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_deletedIrqHandler' _)

theorem dl_lookupIpcBuffer' (b : Bool) (t : ObjRef) : DL (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupIpcBuffer' _ _)

theorem dl_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : DL (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_storeWordOffs' _ _ _)

theorem dl_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : DL (setMrs (Z := Unit) t b m) := by
  unfold setMrs; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setMrs' _ _ _)

theorem dl_setMessageInfo' (t : ObjRef) (i : MessageInfo) : DL (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setMessageInfo' _ _)

theorem dl_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : DL (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archThreadSet' _ _)

theorem dl_saveFpuState' (t : ObjRef) : DL (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_saveFpuState' _)

theorem dl_loadFpuState' (t : ObjRef) : DL (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_loadFpuState' _)

theorem dl_setX64CurrentFpuOwner' (o : Option ObjRef) : DL (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setX64CurrentFpuOwner' _)

theorem dl_switchLocalFpuOwner' (o : Option ObjRef) : DL (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_switchLocalFpuOwner' _)

theorem dl_getTcbQueue' (d : Domain) (p : Priority) : DL (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getTcbQueue' _ _)

theorem dl_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : DL (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setTcbQueue' _ _ _)

theorem dl_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : DL (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbSchedAction' _ _)

theorem dl_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : DL (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getTcbObjRef' _ _)

theorem dl_setSchedulerAction' (a : SchedulerAction) : DL (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setSchedulerAction' _)

theorem dl_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : DL (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getScRefillSufficient' _ _)

theorem dl_getScRefillReady' (sc : ObjRef) : DL (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getScRefillReady' _)

theorem dl_tcbReleaseRemove' (t : ObjRef) : DL (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbReleaseRemove' _)

theorem dl_rescheduleRequired' : DL (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_rescheduleRequired' )

theorem dl_testReschedule' (t : ObjRef) : DL (testReschedule (Z := Unit) t) := by
  unfold testReschedule; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_testReschedule' _)

theorem dl_possibleSwitchTo' (t : ObjRef) : DL (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_possibleSwitchTo' _)

theorem dl_tcbEpDequeue' (t e : ObjRef) : DL (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbEpDequeue' _ _)

theorem dl_tcbNtfnDequeue' (t n : ObjRef) : DL (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbNtfnDequeue' _ _)

theorem dl_isRoundRobin' (sc : ObjRef) : DL (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_isRoundRobin' _)

theorem dl_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : DL (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateRefillHd' _ _)

theorem dl_getRefillHead' (sc : ObjRef) : DL (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getRefillHead' _)

theorem dl_refillPopHead' (sc : ObjRef) : DL (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillPopHead' _)

theorem dl_mergeOverlappingRefills' (sc : ObjRef) : DL (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_mergeOverlappingRefills' _)

theorem dl_refillHeadOverlappingLoop' (sc : ObjRef) : DL (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillHeadOverlappingLoop' _)

theorem dl_refillUnblockCheck' (sc : ObjRef) : DL (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillUnblockCheck' _)

theorem dl_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : DL (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_ifCondRefillUnblockCheck' _ _ _)

theorem dl_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : DL (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem dl_restartThreadIfNoFault' (t : ObjRef) : DL (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_restartThreadIfNoFault' _)

theorem dl_removeAndRestartEpQueuedThread' (t e : ObjRef) : DL (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_removeAndRestartEpQueuedThread' _ _)

theorem dl_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : DL (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_removeAndRestartNtfnQueuedThread' _ _)

theorem dl_replyUnlinkSc' (sc r : ObjRef) : DL (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyUnlinkSc' _ _)

theorem dl_schedContextDonate' (sc t : ObjRef) : DL (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextDonate' _ _)

theorem dl_schedContextUpdateConsumed' (sc : ObjRef) : DL (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUpdateConsumed' _)

theorem dl_replyFromKernel' (t : ObjRef) (x : Data × List Data) : DL (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyFromKernel' _ _)

theorem dl_setConsumed' (sc t : ObjRef) : DL (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setConsumed' _ _)

theorem dl_schedContextCancelYieldTo' (t : ObjRef) : DL (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextCancelYieldTo' _)

theorem dl_fpuRelease' (t : ObjRef) : DL (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_fpuRelease' _)

theorem dl_deleteAsidPool' (b : Asid) (p : ObjRef) : DL (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_deleteAsidPool' _ _)

theorem dl_deleteAsid' (a : Asid) (p : ObjRef) : DL (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_deleteAsid' _ _)

theorem dl_archPostCapDeletion' (c : ArchCap) : DL (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archPostCapDeletion' _)

theorem dl_postCapDeletion' (c : Cap) : DL (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_postCapDeletion' _)

theorem dl_emptySlot' (sl : CslotPtr) (c : Cap) : DL (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_emptySlot' _ _)

theorem dl_cancelAllIpc' (e : ObjRef) : DL (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_cancelAllIpc' _)

theorem dl_schedContextMaybeUnbindNtfn' (n : ObjRef) : DL (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextMaybeUnbindNtfn' _)

theorem dl_unbindMaybeNotification' (n : ObjRef) : DL (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unbindMaybeNotification' _)

theorem dl_cancelAllSignals' (n : ObjRef) : DL (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_cancelAllSignals' _)

theorem dl_replyRemove' (t r : ObjRef) : DL (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyRemove' _ _)

theorem dl_unbindNotification' (t : ObjRef) : DL (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unbindNotification' _)

theorem dl_schedContextUnbindTcb' (sc : ObjRef) : DL (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUnbindTcb' _)

theorem dl_completeYieldTo' (t : ObjRef) : DL (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_completeYieldTo' _)

theorem dl_unbindFromSc' (t : ObjRef) : DL (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_unbindFromSc' _)

theorem dl_schedContextUnbindAllTcbs' (sc : ObjRef) : DL (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUnbindAllTcbs' _)

theorem dl_schedContextUnbindNtfn' (sc : ObjRef) : DL (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUnbindNtfn' _)

theorem dl_schedContextUnbindReply' (sc : ObjRef) : DL (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUnbindReply' _)

theorem dl_schedContextUnbindYieldFrom' (sc : ObjRef) : DL (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextUnbindYieldFrom' _)

theorem dl_schedContextSetInactive' (sc : ObjRef) : DL (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextSetInactive' _)

theorem dl_prepareThreadDelete' (t : ObjRef) : DL (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_prepareThreadDelete' _)

theorem dl_archFinaliseCap' (c : ArchCap) (x : Bool) : DL (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archFinaliseCap' _ _)

theorem dl_fastFinalise' (c : Cap) (b : Bool) : DL (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_fastFinalise' _ _)

theorem dl_capDeleteOne' (sl : CslotPtr) : DL (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capDeleteOne' _)

theorem dl_deletingIrqHandler' (irq : Irq) : DL (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_deletingIrqHandler' _)

theorem dl_finaliseCap (c : Cap) (b : Bool) : DL (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_finaliseCap _ _)

theorem dl_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : DL (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capSwap' _ _ _ _)

theorem dl_capSwapForDelete' (s1 s2 : CslotPtr) : DL (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capSwapForDelete' _ _)

theorem dle_preemptionPoint' : DLE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_preemptionPoint')

set_option maxHeartbeats 4000000 in
theorem dl_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, DL (f k)) (k : RecDelCall) : DLE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, DLE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF; dl_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF; dl_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF
    split <;> dl_auto
    all_goals exact hrec' _

/-- `rec_del` keeps the domain list. -/
theorem dle_recDel (c : RecDelCall) : DLE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | dlV y.2 = dlV t}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => dl_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf c σ).1 hx
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_recDel _)

set_option maxHeartbeats 4000000 in
theorem dl_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, DL (f k)) (sl : CslotPtr) : DLE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, DLE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF
  dl_auto
  all_goals exact hrec' _

/-- `cap_revoke` keeps the domain list. -/
theorem dle_capRevoke (sl : CslotPtr) : DLE (capRevoke (Z := Unit) sl) := by
  intro σ x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | dlV y.2 = dlV t}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => dl_capRevokeF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (Fl4Proofs.P3.SInvDomL.lfp_le_prefixed' _ f hf sl σ).1 hx
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_capRevoke _)

theorem dl_capDelete (sl : CslotPtr) : DLE (capDelete (Z := Unit) sl) := by
  unfold capDelete; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capDelete _)

theorem dl_capMove' (c : Cap) (s1 s2 : CslotPtr) : DL (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_capMove' _ _ _)

theorem dl_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    DL (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_removeAndRestartBadgedThread' _ _ _)

theorem dl_cancelBadgedSends' (e : ObjRef) (b : Badge) : DL (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_cancelBadgedSends' _ _)

theorem dle_invokeCnode (i : CnodeInvocation) : DLE (invokeCnode (Z := Unit) i) := by
  cases i <;> unfold invokeCnode withoutPreemption <;> dl_auto0

theorem dl_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : DL (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_orderedInsert' _ _ _ _)

theorem dl_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : DL (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_readyTimesAppend' _ _)

theorem dl_tcbReleaseEnqueue' (t : ObjRef) : DL (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbReleaseEnqueue' _)

theorem dl_tcbAppend' (t : ObjRef) (q : List ObjRef) : DL (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbAppend' _ _)

theorem dl_postpone' (sc : ObjRef) : DL (postpone (Z := Unit) sc) := by
  unfold postpone; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_postpone' _)

theorem dl_threadSetPriority' (t : ObjRef) (p : Priority) : DL (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_threadSetPriority' _ _)

theorem dl_reorderEp' (e t : ObjRef) : DL (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_reorderEp' _ _)

theorem dl_reorderNtfn' (n t : ObjRef) : DL (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_reorderNtfn' _ _)

theorem dl_archPostModifyRegisters' (c t : ObjRef) : DL (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archPostModifyRegisters' _ _)

theorem dl_schedContextResume' (sc : ObjRef) : DL (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextResume' _)

theorem dl_testPossibleSwitchTo' (t : ObjRef) : DL (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_testPossibleSwitchTo' _)

theorem dl_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : DL (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_ifSporadicCurScTestRefillUnblockCheck' _)

theorem dl_restart' (t : ObjRef) : DL (restart (Z := Unit) t) := by
  unfold restart; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_restart' _)

theorem dl_setMcpriority' (t : ObjRef) (m : Priority) : DL (setMcpriority (Z := Unit) t m) := by
  unfold setMcpriority; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setMcpriority' _ _)

theorem dl_setPriority' (t : ObjRef) (p : Priority) : DL (setPriority (Z := Unit) t p) := by
  unfold setPriority; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setPriority' _ _)

theorem dl_schedContextBindTcb' (sc t : ObjRef) : DL (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextBindTcb' _ _)

theorem dl_bindNotification' (t n : ObjRef) : DL (bindNotification (Z := Unit) t n) := by
  unfold bindNotification; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_bindNotification' _ _)

theorem dl_setFlags' (t : ObjRef) (f : TcbFlags) : DL (setFlags (Z := Unit) t f) := by
  unfold setFlags; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setFlags' _ _)

theorem dl_lazyFpuRestore' (t : ObjRef) : DL (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lazyFpuRestore' _)

theorem dl_archPostSetFlags' (t : ObjRef) (f : TcbFlags) : DL (archPostSetFlags (Z := Unit) t f) := by
  unfold archPostSetFlags; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archPostSetFlags' _ _)

theorem dl_checkCapAt' (c : Cap) (sl : CslotPtr) {m : SMonad Unit Unit} (h : DL m) :
    DL (checkCapAt (Z := Unit) c sl m) := by
  unfold checkCapAt; dl_auto0; exact h
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dl_checkCapAt' _ _ ?_)

theorem dle_installTcbCap' (t : ObjRef) (sl : CslotPtr) (n : Nat) (o : Option (Cap × CslotPtr)) :
    DLE (installTcbCap (Z := Unit) t sl n o) := by
  unfold installTcbCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_installTcbCap' _ _ _ _)

theorem dle_installTcbFrameCap' (t : ObjRef) (sl : CslotPtr) (b : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    DLE (installTcbFrameCap (Z := Unit) t sl b) := by
  unfold installTcbFrameCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_installTcbFrameCap' _ _ _)

theorem dle_invokeTcb (i : TcbInvocation) : DLE (invokeTcb (Z := Unit) i) := by
  cases i <;> unfold invokeTcb <;> dl_auto0

theorem dle_invokeFl4Tcb (i : Fl4TcbInvocation) : DLE (invokeFl4Tcb (Z := Unit) i) := by
  cases i <;> unfold invokeFl4Tcb <;> dl_auto0

theorem dle_fl4PerformTcb (blk call don : Bool) (i : TcbInvocation) :
    DLE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := dle_invokeTcb i

theorem dle_fl4PerformFl4Tcb (blk call don : Bool) (i : Fl4TcbInvocation) :
    DLE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := dle_invokeFl4Tcb i

theorem dle_fl4PerformCnode (blk call don : Bool) (i : CnodeInvocation) :
    DLE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  show DLE (do invokeCnode (Z := Unit) i; NonDetE.returnOk [])
  exact Vs.dke_bind (dle_invokeCnode i) fun _ => Vs.dke_returnOk _

theorem dle_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : DL m) :
    DLE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dle_withoutPreemption' ?_)

theorem dle_resolveAddressBits (p : Cap × CapRef) : DLE (resolveAddressBits (Z := Unit) p) := dle_rab p
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_resolveAddressBits _)

theorem dl_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : DLE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupSlotForThread' _ _)

theorem dl_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : DLE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupCapAndSlot' _ _)

theorem dl_lookupCap' (thread : ObjRef) (ref : CapRef) : DLE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupCap' _ _)

theorem dl_captransferFromWords' (ptr : Word) : DL (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_captransferFromWords' _)

theorem dl_loadCapTransfer' (buffer : ObjRef) : DL (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_loadCapTransfer' _)

theorem dl_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : DL (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_setExtraBadge' _ _ _)

theorem dle_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : DLE m) :
    DLE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dle_lookupErrorOnFailure' _ ?_)

theorem dl_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : DLE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupSlotForCnodeOp' _ _ _ _)

theorem dl_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : DLE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact dl_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupTargetSlot' _ _ _)

theorem dl_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : DL (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archPostResetUntyped' _ _)

theorem dl_resetUntypedCap' (srcSlot : CslotPtr) : DLE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_resetUntypedCap' _)

theorem dl_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : DL (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_retypeRegionWith' _ _ _ _ _ _)

theorem dl_copyGlobalMappings' (newPm : ObjRef) : DL (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_copyGlobalMappings' _)

theorem dl_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : DL (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_initArchObjects' _ _ _ _ _ _)

theorem dl_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : DL (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_createCap' _ _ _ _ _)

theorem dl_ensureNoChildren' (cslotPtr : CslotPtr) : DLE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_ensureNoChildren' _)

theorem dl_getRefillTail' (scPtr : ObjRef) : DL (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getRefillTail' _)

theorem dl_getRefills' (scPtr : ObjRef) : DL (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getRefills' _)

theorem dl_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : DL (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillAddTail' _ _)

theorem dl_refillFull' (scPtr : ObjRef) : DL (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillFull' _)

theorem dl_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : DL (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateRefillTl' _ _)

theorem dl_scheduleUsed' (scPtr : ObjRef) (new : Refill) : DL (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_scheduleUsed' _ _)

theorem dl_refillSize' (scPtr : ObjRef) : DL (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillSize' _)

theorem dl_refillSingle' (scPtr : ObjRef) : DL (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillSingle' _)

theorem dl_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : DL (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_chargeEntireHeadRefill' _ _)

theorem dl_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : DL (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_mergeNonoverlappingHeadRefill' _)

theorem dl_updateIrqState' (irq : Irq) (irqState : X64IRQState) : DL (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateIrqState' _ _)

theorem dle_archInvokeIrqControl' (i : ArchIrqControlInvocation) : DLE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_archInvokeIrqControl' _)

theorem dl_invokeIrqControl' (i : IrqControlInvocation) : DLE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_invokeIrqControl' _)

theorem dle_invokeUntypedWith' (b : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) :
    DLE (invokeUntypedWith (Z := Unit) b ui) := by
  cases ui; unfold invokeUntypedWith; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_invokeUntypedWith' _ _)

theorem dle_fl4InvokeUntyped' (ui : UntypedInvocation) : DLE (fl4InvokeUntyped (Z := Unit) ui) :=
  dle_invokeUntypedWith' _ ui
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_fl4InvokeUntyped' _)

theorem dle_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : DLE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_invokeFl4IrqControl' _)

theorem dle_archDeriveCap' (c : ArchCap) : DLE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_archDeriveCap' _)

theorem dle_deriveCap' (sl : CslotPtr) (c : Cap) : DLE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dle_deriveCap' _ _)

theorem dl_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : DL (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_makeArchFaultMsg' _ _)

theorem dle_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : DLE m) :
    DLE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dle_unifyFailure' ?_)

theorem dl_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : DLE m) :
    DL (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dl_emptyOnFailure' ?_)

theorem dl_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : DLE m) :
    DL (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dl_constOnFailure' _ ?_)

theorem dle_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : DLE m) :
    DLE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible refine dle_capFaultOnFailure' _ _ ?_)

theorem dl_loadWordOffs' (ptr : ObjRef) (offs : Nat) : DL (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact dl_doMachineOp _
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_loadWordOffs' _ _)

theorem dl_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : DL (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => dl_loadWordOffs' _ _) _)
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getExtraCptrs' _ _)

theorem dl_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : DL (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getReceiveSlots' _ _)

theorem dl_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      DL (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; dl_auto0
  | n, (c, sl) :: rest, slots, mi => by
    have ih := dl_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    dl_auto0
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_transferCapsLoop' _ _ _ _ _ _)

theorem dl_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : DLE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_lookupExtraCaps' _ _ _)

theorem dl_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : DL (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_copyMrs' _ _ _ _ _)

theorem dl_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : DL (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_transferCaps' _ _ _ _ _)

theorem dl_makeFaultMsg' (f : Fault) (t : ObjRef) : DL (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_makeFaultMsg' _ _)

theorem dl_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : DL (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleOverrun' _ _)

theorem dl_headInsufficientLoop' (scPtr : ObjRef) : DL (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_headInsufficientLoop' _)

theorem dl_getMessageInfo' (thread : ObjRef) : DL (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getMessageInfo' _)

theorem dl_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : DL (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_tcbEpAppend' _ _ _)

theorem dl_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : DL (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doNormalTransfer' _ _ _ _ _ _ _)

theorem dl_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : DL (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doFaultTransfer' _ _ _ _)

theorem dl_bindScReply' (scPtr replyPtr : ObjRef) : DL (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_bindScReply' _ _)

theorem dl_isValidTimeoutHandler' (tptr : ObjRef) : DL (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_isValidTimeoutHandler' _)

theorem dl_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : DL (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doIpcTransfer' _ _ _ _ _)

theorem dl_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : DL (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_replyPush' _ _ _ _)

theorem dl_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : DL (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_sendIpcBlocked' _ _ _ _ _ _)

theorem dl_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : DL (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_sendIpc' _ _ _ _ _ _ _ _)

theorem dl_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : DL (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_sendFaultIpc' _ _ _ _)

theorem dl_refillBudgetCheckRoundRobin' (usage : Ticks) : DL (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillBudgetCheckRoundRobin' _)

theorem dl_refillBudgetCheck' (usage : Ticks) : DL (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillBudgetCheck' _)

theorem dl_maybeAddEmptyTail' (scPtr : ObjRef) : DL (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_maybeAddEmptyTail' _)

theorem dl_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : DL (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_maybeDonateSc' _ _)

theorem dl_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : DL (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_updateWaitingNtfn' _ _ _)

theorem dl_handleTimeout' (tptr : ObjRef) (ex : Fault) : DL (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleTimeout' _ _)

theorem dl_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : DL (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getMrs' _ _ _)

theorem dl_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    DL (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_handleFaultReply' _ _ _ _)

theorem dl_returnConsumed' (scPtr : ObjRef) : DL (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_returnConsumed' _)

theorem dl_schedContextBindNtfn' (sc ntfn : ObjRef) : DL (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextBindNtfn' _ _)

theorem dl_schedContextYieldTo' (scPtr : ObjRef) : DL (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_schedContextYieldTo' _)

theorem dl_getScActive' (scPtr : ObjRef) : DL (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_getScActive' _)

theorem dl_commitTime' : DL (commitTime (Z := Unit) ) := by
  unfold commitTime; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_commitTime' )

theorem dl_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : DL (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillNew' _ _ _ _)

theorem dl_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : DL (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_refillUpdate' _ _ _ _)

theorem dl_archInvokeIrqHandler' (i : IrqHandlerInvocation) : DL (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_archInvokeIrqHandler' _)

theorem dl_sendSignal' (n : ObjRef) (b : Badge) : DL (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_sendSignal' _ _)

theorem dl_doReplyTransfer' (s r : ObjRef) (g : Bool) : DL (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_doReplyTransfer' _ _ _)

theorem dl_invokeSchedContext' (i : SchedContextInvocation) : DL (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_invokeSchedContext' _)

theorem dl_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : DL (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_invokeSchedControlConfigureFlags' _)

theorem dl_invokeIrqHandler' (i : IrqHandlerInvocation) : DL (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold invokeIrqHandler <;> dl_auto0
macro_rules | `(tactic| dl_leaf) => `(tactic| with_reducible exact dl_invokeIrqHandler' _)

end

end Fl4Proofs.P3.SInvDom
