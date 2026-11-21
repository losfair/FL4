/-
P3 (DESIGN.md §9), invariant line G1 (rd7): **the spec steps keep the consumed
time, the current SC, the current thread, the idle thread / SC and the current
time** (spec side only, outside the JAtZ cone; `CFK`). MachFieldFamT's `MTK`
family (scratch/mr6) with the projection `cfS` instead of `msFT`
(scratch/rd7/mkp.py, untracked): every machine operation keeps `cfS`
(`cfk_doMachineOp`, any `mop`), and the only writers of these fields in the
MTK set, `commit_time` (`consumed_time := 0`) and its caller
`invoke_sched_control_configure_flags` (commit when the configured SC is
`cur_sc`), are left out. Used to carry `consumed_time = 0` (charge_budget's
overrun) and the scalar parts of `OffReady` from the charge to `schedule`.
-/
import Fl4Proofs.P3.MachFieldFamT

open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT

noncomputable section

/-- The consumed time, the current SC and thread, the idle thread and SC, the time. -/
def cfS (σ : State Unit) := (σ.consumedTime, σ.curSc, σ.curThread, σ.idleThread, σ.idleSc, σ.curTime)

/-- Every outcome of `m` keeps `cfS`. -/
abbrev CFK {α : Type} (m : NonDet (State Unit) α) : Prop := FK cfS m

/-- `CFK` for the exception monad. -/
abbrev CFKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE cfS m

theorem cfk_doMachineOp {α : Type} {mop : NonDet MachineState α} (_hm : MKF mop) :
    CFK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨-, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  rfl

/-- A `CFK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "cfk_leaf" : tactic
macro_rules | `(tactic| cfk_leaf) => `(tactic| fail "no cfk_leaf")
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_loadWord _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_storeWord _ _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_machineOpLift _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_invalidateASID _ _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_invalidateTranslationSingleASID _ _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_invalidateLocalPageStructureCacheASID _ _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp mkf_readFpuState)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_writeFpuState _))
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp mkf_enableFpu)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp mkf_disableFpu)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp mkf_isFpuEnable)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp mkf_getFaultAddress)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doMachineOp (mkf_ackInterrupt _))

macro "cfk_auto" : tactic => `(tactic| repeat' (first | cfk_leaf | dk_step0))

theorem cfk_doExtendedOp (eop : DetExtMonad Unit) : CFK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doExtendedOp _)

theorem cfk_setObject (p : ObjRef) (o : KernelObject) : CFK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setObject _ _)

theorem cfk_setCap (c : Cap) (sl : CslotPtr) : CFK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setCap _ _)

theorem cfk_getCap (sl : CslotPtr) : CFK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getCap _)

theorem cfk_getPt (ptr : ObjRef) : CFK (getPt (Z := Unit) ptr) := by
  unfold getPt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPt _)

theorem cfk_getPte (ptr : ObjRef) : CFK (getPte (Z := Unit) ptr) := by
  unfold getPte; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPte _)

theorem cfk_getPd (ptr : ObjRef) : CFK (getPd (Z := Unit) ptr) := by
  unfold getPd; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPd _)

theorem cfk_getPde (ptr : ObjRef) : CFK (getPde (Z := Unit) ptr) := by
  unfold getPde; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPde _)

theorem cfk_getPml4 (ptr : ObjRef) : CFK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPml4 _)

theorem cfk_getPml4e (ptr : ObjRef) : CFK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPml4e _)

theorem cfk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : CFKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupPdptSlot _ _)

theorem cfk_getPdpt (ptr : ObjRef) : CFK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPdpt _)

theorem cfk_getPdpte (ptr : ObjRef) : CFK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getPdpte _)

theorem cfk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : CFKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupPdSlot _ _)

theorem cfk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : CFKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupPtSlot _ _)

theorem cfk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : CFK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setPdpt _ _)

theorem cfk_storePdpte (p : ObjRef) (pte : PDPTE) : CFK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storePdpte _ _)

theorem cfk_getAsidPool (ptr : ObjRef) : CFK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getAsidPool _)

theorem cfk_findVspaceForAsid (asid : Asid) : CFKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_findVspaceForAsid _)

theorem cfk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : CFK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setPt _ _)

theorem cfk_storePte (p : ObjRef) (pte : PTE) : CFK (storePte (Z := Unit) p pte) := by
  unfold storePte; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storePte _ _)

theorem cfk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : CFK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setPd _ _)

theorem cfk_storePde (p : ObjRef) (pde : PDE) : CFK (storePde (Z := Unit) p pde) := by
  unfold storePde; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storePde _ _)

theorem cfk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : CFK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unmapPage _ _ _ _)

theorem cfk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : CFK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performPageInvocationUnmap _ _)

theorem cfk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : CFK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setAsidPool _ _)

theorem cfk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : CFK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_flushTable _ _ _ _)

theorem cfk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : CFK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setPml4 _ _)

theorem cfk_setOriginal (slot : CslotPtr) (v : Bool) : CFK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setOriginal _ _)

theorem cfk_updateCdt (f : Cdt → Cdt) : CFK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateCdt _)

theorem cfk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : CFK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setUntypedCapAsFull _ _ _)

theorem cfk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : CFK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_retypeRegion _ _ _ _ _)

theorem cfk_storePml4e (p : ObjRef) (pte : PML4E) : CFK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storePml4e _ _)

theorem cfk_flushAll (vspace : ObjRef) (asid : Asid) : CFK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_flushAll _ _)

theorem cfk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : CFK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unmapPdpt _ _ _)

theorem cfk_setIoportMask (f l : IoPort) (val : Bool) : CFK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setIoportMask _ _ _)

theorem cfk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : CFK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_invalidatePageStructureCacheAsid _ _)

theorem cfk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : CFK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unmapPd _ _ _)

theorem cfk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : CFK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_capInsert _ _ _)

theorem cfk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : CFK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unmapPageTable _ _ _)

theorem cfk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : CFK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storeAsidPoolEntry _ _ _)

theorem cfk_performPageInvocation (iv : PageInvocation) : CFK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performPageInvocation _)

theorem cfk_performPageTableInvocation (iv : PageTableInvocation) : CFK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performPageTableInvocation _)

theorem cfk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : CFK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performPageDirectoryInvocation _)

theorem cfk_performPdptInvocation (iv : PdptInvocation) : CFK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performPdptInvocation _)

theorem cfk_performAsidPoolInvocation (iv : AsidPoolInvocation) : CFK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performAsidPoolInvocation _)

theorem cfk_performIoportControlInvocation (i : IoPortControlInvocation) : CFK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performIoportControlInvocation _)

theorem cfk_performDeriveSubframe (iv : Fl4SubframeInvocation) : CFK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performDeriveSubframe _)

theorem cfk_performTestAndClearAccessed (_slot : ObjRef) : CFK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_performTestAndClearAccessed _)

theorem cfk_performPml4Flush (i : Fl4Pml4Invocation) : CFK (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact cfk_flushAll _ _

theorem cfk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : CFK (threadSet (Z := Unit) f t) := by
  unfold threadSet; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_threadSet' _ _)

theorem cfk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : CFK (threadGet (Z := Unit) f t) := by
  unfold threadGet; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_threadGet' _ _)

theorem cfk_setThreadState' (t : ObjRef) (ts : ThreadState) : CFK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setThreadState' _ _)

theorem cfk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    CFK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getSimpleKo' _ _)

theorem cfk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    CFK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setSimpleKo' _ _ _)

theorem cfk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    CFK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateSkObjRef' _ _ _ _)

theorem cfk_getSchedContext' (q : ObjRef) : CFK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getSchedContext' _)

theorem cfk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    CFK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateSchedContext' _ _)

theorem cfk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : CFK (asUser (Z := Unit) t u) := by
  unfold asUser; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_asUser' _ _)

theorem cfk_replyUnlinkTcb' (t r : ObjRef) : CFK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_replyUnlinkTcb' _ _)

theorem cfk_getThreadState' (t : ObjRef) : CFK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getThreadState' _)

theorem cfk_cancelIpc' (t : ObjRef) : CFK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_cancelIpc' _)

theorem cfk_suspend' (t : ObjRef) : CFK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_suspend' _)

theorem cfk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : CFK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getSkObjRef' _ _ _)

theorem cfk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : CFK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getScObjRef' _ _)

theorem cfk_getIrqSlot' (irq : Irq) : CFK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getIrqSlot' _)

theorem cfk_isFinalCap' (c : Cap) : CFK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_isFinalCap' _)

theorem cfk_hwAsidInvalidate' (a : Asid) (v : ObjRef) : CFK (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_hwAsidInvalidate' _ _)

theorem cfk_getCurrentCr3' : CFK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getCurrentCr3' )

theorem cfk_setCurrentCr3' (c : Cr3) : CFK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setCurrentCr3' _)

theorem cfk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : CFK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setCurrentVspaceRoot' _ _)

theorem cfk_setVmRoot' (t : ObjRef) : CFK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setVmRoot' _)

theorem cfk_freeIoportRange' (f l : IoPort) : CFK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_freeIoportRange' _ _)

theorem cfk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : CFK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupIpcBuffer' _ _)

theorem cfk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, CFK (g a b)) :
    ∀ l1 l2, CFK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => cfk_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine cfk_zipWithMx' (fun _ _ => ?_) _ _)

theorem cfk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : CFK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_storeWordOffs' _ _ _)

theorem cfk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : CFK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setMrs' _ _ _)

theorem cfk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : CFK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setMessageInfo' _ _)

theorem cfk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : CFK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_archThreadSet' _ _)

theorem cfk_saveFpuState' (t : ObjRef) : CFK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_saveFpuState' _)

theorem cfk_loadFpuState' (t : ObjRef) : CFK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_loadFpuState' _)

theorem cfk_setX64CurrentFpuOwner' (o : Option ObjRef) : CFK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setX64CurrentFpuOwner' _)

theorem cfk_switchLocalFpuOwner' (o : Option ObjRef) : CFK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_switchLocalFpuOwner' _)

theorem cfk_getTcbQueue' (d : Domain) (p : Priority) : CFK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getTcbQueue' _ _)

theorem cfk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : CFK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setTcbQueue' _ _ _)

theorem cfk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : CFK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbSchedAction' _ _)

theorem cfk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : CFK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getTcbObjRef' _ _)

theorem cfk_setSchedulerAction' (a : SchedulerAction) : CFK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setSchedulerAction' _)

theorem cfk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : CFK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getScRefillSufficient' _ _)

theorem cfk_getScRefillReady' (sc : ObjRef) : CFK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getScRefillReady' _)

theorem cfk_tcbReleaseRemove' (t : ObjRef) : CFK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbReleaseRemove' _)

theorem cfk_rescheduleRequired' : CFK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_rescheduleRequired' )

theorem cfk_testReschedule' (t : ObjRef) : CFK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_testReschedule' _)

theorem cfk_possibleSwitchTo' (t : ObjRef) : CFK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_possibleSwitchTo' _)

theorem cfk_tcbEpDequeue' (t e : ObjRef) : CFK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbEpDequeue' _ _)

theorem cfk_tcbNtfnDequeue' (t n : ObjRef) : CFK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbNtfnDequeue' _ _)

theorem cfk_isRoundRobin' (sc : ObjRef) : CFK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_isRoundRobin' _)

theorem cfk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : CFK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateRefillHd' _ _)

theorem cfk_getRefillHead' (sc : ObjRef) : CFK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getRefillHead' _)

theorem cfk_refillPopHead' (sc : ObjRef) : CFK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillPopHead' _)

theorem cfk_mergeOverlappingRefills' (sc : ObjRef) : CFK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_mergeOverlappingRefills' _)

theorem cfk_refillHeadOverlappingLoop' (sc : ObjRef) : CFK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillHeadOverlappingLoop' _)

theorem cfk_refillUnblockCheck' (sc : ObjRef) : CFK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillUnblockCheck' _)

theorem cfk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : CFK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_ifCondRefillUnblockCheck' _ _ _)

theorem cfk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : CFK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem cfk_restartThreadIfNoFault' (t : ObjRef) : CFK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_restartThreadIfNoFault' _)

theorem cfk_removeAndRestartEpQueuedThread' (t e : ObjRef) : CFK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_removeAndRestartEpQueuedThread' _ _)

theorem cfk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : CFK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_removeAndRestartNtfnQueuedThread' _ _)

theorem cfk_replyUnlinkSc' (sc r : ObjRef) : CFK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_replyUnlinkSc' _ _)

theorem cfk_schedContextDonate' (sc t : ObjRef) : CFK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextDonate' _ _)

theorem cfk_schedContextUpdateConsumed' (sc : ObjRef) : CFK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUpdateConsumed' _)

theorem cfk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : CFK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_replyFromKernel' _ _)

theorem cfk_setConsumed' (sc t : ObjRef) : CFK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setConsumed' _ _)

theorem cfk_schedContextCancelYieldTo' (t : ObjRef) : CFK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextCancelYieldTo' _)

theorem cfk_fpuRelease' (t : ObjRef) : CFK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_fpuRelease' _)

theorem cfk_deleteAsidPool' (b : Asid) (p : ObjRef) : CFK (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_deleteAsidPool' _ _)

theorem cfk_deleteAsid' (a : Asid) (p : ObjRef) : CFK (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_deleteAsid' _ _)

theorem cfk_archPostCapDeletion' (c : ArchCap) : CFK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_archPostCapDeletion' _)

theorem cfk_cancelAllIpc' (e : ObjRef) : CFK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_cancelAllIpc' _)

theorem cfk_schedContextMaybeUnbindNtfn' (n : ObjRef) : CFK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextMaybeUnbindNtfn' _)

theorem cfk_unbindMaybeNotification' (n : ObjRef) : CFK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unbindMaybeNotification' _)

theorem cfk_cancelAllSignals' (n : ObjRef) : CFK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_cancelAllSignals' _)

theorem cfk_replyRemove' (t r : ObjRef) : CFK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_replyRemove' _ _)

theorem cfk_unbindNotification' (t : ObjRef) : CFK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unbindNotification' _)

theorem cfk_schedContextUnbindTcb' (sc : ObjRef) : CFK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUnbindTcb' _)

theorem cfk_completeYieldTo' (t : ObjRef) : CFK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_completeYieldTo' _)

theorem cfk_unbindFromSc' (t : ObjRef) : CFK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_unbindFromSc' _)

theorem cfk_schedContextUnbindAllTcbs' (sc : ObjRef) : CFK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUnbindAllTcbs' _)

theorem cfk_schedContextUnbindNtfn' (sc : ObjRef) : CFK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUnbindNtfn' _)

theorem cfk_schedContextUnbindReply' (sc : ObjRef) : CFK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUnbindReply' _)

theorem cfk_schedContextUnbindYieldFrom' (sc : ObjRef) : CFK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextUnbindYieldFrom' _)

theorem cfk_schedContextSetInactive' (sc : ObjRef) : CFK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextSetInactive' _)

theorem cfk_prepareThreadDelete' (t : ObjRef) : CFK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_prepareThreadDelete' _)

theorem cfk_archFinaliseCap' (c : ArchCap) (x : Bool) : CFK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_archFinaliseCap' _ _)

theorem cfk_fastFinalise' (c : Cap) (b : Bool) : CFK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_fastFinalise' _ _)

/-- `empty_slot` with a null cleanup: `postCapDeletion nullCap` does nothing. -/
theorem cfk_emptySlotNull (sl : CslotPtr) : CFK (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot postCapDeletion; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_emptySlotNull _)

theorem cfk_capDeleteOne' (sl : CslotPtr) : CFK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_capDeleteOne' _)

theorem cfk_deletingIrqHandler' (irq : Irq) : CFK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_deletingIrqHandler' _)

theorem cfk_finaliseCap (c : Cap) (b : Bool) : CFK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_finaliseCap _ _)

theorem cfk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : CFK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_capSwap' _ _ _ _)

theorem cfk_capSwapForDelete' (s1 s2 : CslotPtr) : CFK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_capSwapForDelete' _ _)

theorem cfk_capMove' (c : Cap) (s1 s2 : CslotPtr) : CFK (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_capMove' _ _ _)

theorem cfk_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    CFK (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_removeAndRestartBadgedThread' _ _ _)

theorem cfk_cancelBadgedSends' (e : ObjRef) (b : Badge) : CFK (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_cancelBadgedSends' _ _)

theorem cfk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : CFK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_orderedInsert' _ _ _ _)

theorem cfk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : CFK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_readyTimesAppend' _ _)

theorem cfk_tcbReleaseEnqueue' (t : ObjRef) : CFK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbReleaseEnqueue' _)

theorem cfk_tcbAppend' (t : ObjRef) (q : List ObjRef) : CFK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbAppend' _ _)

theorem cfk_postpone' (sc : ObjRef) : CFK (postpone (Z := Unit) sc) := by
  unfold postpone; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_postpone' _)

theorem cfk_threadSetPriority' (t : ObjRef) (p : Priority) : CFK (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_threadSetPriority' _ _)

theorem cfk_reorderEp' (e t : ObjRef) : CFK (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_reorderEp' _ _)

theorem cfk_reorderNtfn' (n t : ObjRef) : CFK (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_reorderNtfn' _ _)

theorem cfk_archPostModifyRegisters' (c t : ObjRef) : CFK (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_archPostModifyRegisters' _ _)

theorem cfk_schedContextResume' (sc : ObjRef) : CFK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextResume' _)

theorem cfk_testPossibleSwitchTo' (t : ObjRef) : CFK (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_testPossibleSwitchTo' _)

theorem cfk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : CFK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem mtke_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : CFK m) :
    CFKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine mtke_withoutPreemption' ?_)

theorem mtke_rab (p : Cap × CapRef) : CFKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (cfk_getCap _)) fun nc => ?_
        split
        · exact mtke_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact mtke_rab _)

theorem mtke_resolveAddressBits (p : Cap × CapRef) : CFKE (resolveAddressBits (Z := Unit) p) := mtke_rab p
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact mtke_resolveAddressBits _)

theorem cfk_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : CFKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupSlotForThread' _ _)

theorem cfk_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : CFKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupCapAndSlot' _ _)

theorem cfk_lookupCap' (thread : ObjRef) (ref : CapRef) : CFKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupCap' _ _)

theorem cfk_captransferFromWords' (ptr : Word) : CFK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_captransferFromWords' _)

theorem cfk_loadCapTransfer' (buffer : ObjRef) : CFK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_loadCapTransfer' _)

theorem cfk_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : CFK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_setExtraBadge' _ _ _)

theorem mtke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : CFKE m) :
    CFKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine mtke_lookupErrorOnFailure' _ ?_)

theorem cfk_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : CFKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupSlotForCnodeOp' _ _ _ _)

theorem cfk_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : CFKE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact cfk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupTargetSlot' _ _ _)

theorem mtke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : CFKE (f a)) :
    CFKE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine mtke_bind_returnOk' ?_)

theorem cfk_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : CFK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_archPostResetUntyped' _ _)

theorem cfk_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : CFK (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_retypeRegionWith' _ _ _ _ _ _)

theorem cfk_copyGlobalMappings' (newPm : ObjRef) : CFK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_copyGlobalMappings' _)

theorem cfk_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : CFK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_initArchObjects' _ _ _ _ _ _)

theorem cfk_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : CFK (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_createCap' _ _ _ _ _)

theorem cfk_ensureNoChildren' (cslotPtr : CslotPtr) : CFKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_ensureNoChildren' _)

theorem cfk_getRefillTail' (scPtr : ObjRef) : CFK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getRefillTail' _)

theorem cfk_getRefills' (scPtr : ObjRef) : CFK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getRefills' _)

theorem cfk_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : CFK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillAddTail' _ _)

theorem cfk_refillFull' (scPtr : ObjRef) : CFK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillFull' _)

theorem cfk_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : CFK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateRefillTl' _ _)

theorem cfk_scheduleUsed' (scPtr : ObjRef) (new : Refill) : CFK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_scheduleUsed' _ _)

theorem cfk_refillSize' (scPtr : ObjRef) : CFK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillSize' _)

theorem cfk_refillSingle' (scPtr : ObjRef) : CFK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillSingle' _)

theorem cfk_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : CFK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_chargeEntireHeadRefill' _ _)

theorem cfk_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : CFK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_mergeNonoverlappingHeadRefill' _)

theorem cfk_updateIrqState' (irq : Irq) (irqState : X64IRQState) : CFK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateIrqState' _ _)

theorem mtke_archDeriveCap' (c : ArchCap) : CFKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact mtke_archDeriveCap' _)

theorem mtke_deriveCap' (sl : CslotPtr) (c : Cap) : CFKE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact mtke_deriveCap' _ _)

theorem cfk_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : CFK (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_makeArchFaultMsg' _ _)

theorem mtke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : CFKE m) :
    CFKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine mtke_unifyFailure' ?_)

theorem cfk_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : CFKE m) :
    CFK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine cfk_emptyOnFailure' ?_)

theorem cfk_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : CFKE m) :
    CFK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine cfk_constOnFailure' _ ?_)

theorem mtke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : CFKE m) :
    CFKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible refine mtke_capFaultOnFailure' _ _ ?_)

theorem cfk_loadWordOffs' (ptr : ObjRef) (offs : Nat) : CFK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_loadWordOffs' _ _)

theorem cfk_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : CFK (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => cfk_loadWordOffs' _ _) _)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getExtraCptrs' _ _)

theorem cfk_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : CFK (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getReceiveSlots' _ _)

theorem cfk_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      CFK (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; cfk_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := cfk_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    cfk_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_transferCapsLoop' _ _ _ _ _ _)

theorem cfk_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : CFKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lookupExtraCaps' _ _ _)

theorem cfk_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : CFK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_copyMrs' _ _ _ _ _)

theorem cfk_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : CFK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_transferCaps' _ _ _ _ _)

theorem cfk_makeFaultMsg' (f : Fault) (t : ObjRef) : CFK (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_makeFaultMsg' _ _)

theorem cfk_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : CFK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_handleOverrun' _ _)

theorem cfk_headInsufficientLoop' (scPtr : ObjRef) : CFK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_headInsufficientLoop' _)

theorem cfk_getMessageInfo' (thread : ObjRef) : CFK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getMessageInfo' _)

theorem cfk_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : CFK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_tcbEpAppend' _ _ _)

theorem cfk_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : CFK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doNormalTransfer' _ _ _ _ _ _ _)

theorem cfk_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : CFK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doFaultTransfer' _ _ _ _)

theorem cfk_bindScReply' (scPtr replyPtr : ObjRef) : CFK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_bindScReply' _ _)

theorem cfk_isValidTimeoutHandler' (tptr : ObjRef) : CFK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_isValidTimeoutHandler' _)

theorem cfk_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : CFK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doIpcTransfer' _ _ _ _ _)

theorem cfk_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : CFK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_replyPush' _ _ _ _)

theorem cfk_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : CFK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_sendIpcBlocked' _ _ _ _ _ _)

theorem cfk_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : CFK (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_sendIpc' _ _ _ _ _ _ _ _)

theorem cfk_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : CFK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_sendFaultIpc' _ _ _ _)

theorem cfk_refillBudgetCheckRoundRobin' (usage : Ticks) : CFK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillBudgetCheckRoundRobin' _)

theorem cfk_refillBudgetCheck' (usage : Ticks) : CFK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillBudgetCheck' _)

theorem cfk_maybeAddEmptyTail' (scPtr : ObjRef) : CFK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_maybeAddEmptyTail' _)

theorem cfk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : CFK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_maybeDonateSc' _ _)

theorem cfk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : CFK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_updateWaitingNtfn' _ _ _)

theorem cfk_handleTimeout' (tptr : ObjRef) (ex : Fault) : CFK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_handleTimeout' _ _)

theorem cfk_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : CFK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getMrs' _ _ _)

theorem cfk_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    CFK (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_handleFaultReply' _ _ _ _)

theorem cfk_returnConsumed' (scPtr : ObjRef) : CFK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_returnConsumed' _)

theorem cfk_schedContextBindNtfn' (sc ntfn : ObjRef) : CFK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextBindNtfn' _ _)

theorem cfk_schedContextYieldTo' (scPtr : ObjRef) : CFK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_schedContextYieldTo' _)

theorem cfk_getScActive' (scPtr : ObjRef) : CFK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_getScActive' _)

theorem cfk_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : CFK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillNew' _ _ _ _)

theorem cfk_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : CFK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_refillUpdate' _ _ _ _)

theorem cfk_sendSignal' (n : ObjRef) (b : Badge) : CFK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_sendSignal' _ _)

theorem cfk_doReplyTransfer' (s r : ObjRef) (g : Bool) : CFK (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_doReplyTransfer' _ _ _)

end

end Fl4Proofs.P3.SInvR
