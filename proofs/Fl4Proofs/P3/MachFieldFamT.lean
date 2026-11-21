/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **the spec steps keep the
machine fields `MR` reads, the interrupt table and the current time**
(spec side only; `MTK`). MachFieldFam's `MFK` family with `curTime` added to
the projection (`ValidMachineTime` reads it), and with the machine-operation
leaves MachFieldFam lacked: the TLB flushes (`invalidateASID`,
`invalidateTranslationSingleASID`, `invalidateLocalPageStructureCacheASID`)
and the lazy-FPU operations (`readFpuState`, `writeFpuState`, `enableFpu`,
`disableFpu`): `machine_op_lift`s of the machine's opaque rest plus the FPU
enable bit, none of the four machine fields `MR` reads. So the deletion's
finalisation (`finaliseCap`: FPU release, TLB flushes of the VSpace
unmaps) is in the family (`mtk_finaliseCap`).

* `msFT σ`: MachFieldFam's `msF σ` and `σ.curTime`; `MTK m := FK msFT m`.
* Leaves: MachFieldFam's `MKF` (`mtk_doMachineOp`), the new `mkf_*` above.
* The rest: one lemma per spec function by `mtk_auto`, VsDomOps / DomRecDel /
  TcbDom / AllDom's `DK` lemmas renamed (generated: scratch/mr6/mtgen.py +
  head/tail.lean + skip.txt, `sh scratch/mr6/mk.sh`); left out are the
  functions reaching `getActiveIRQ`, `getCurrentTime`, `maskInterrupt` (and
  `setIrqState`), `portOut`, `portIn`, `setDeadline`, `ackDeadlineIRQ`,
  `clearMemory`, `freeMemory`, and their dependents.
-/
import Fl4Proofs.P3.MachFieldFam

open Classical

namespace Fl4Proofs.P3.MachT
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF

noncomputable section

/-- `msF` and the current time. -/
def msFT (σ : State Unit) := (msF σ, σ.curTime)

/-- Every outcome of `m` keeps `msFT`. -/
abbrev MTK {α : Type} (m : NonDet (State Unit) α) : Prop := FK msFT m

/-- `MTK` for the exception monad. -/
abbrev MTKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE msFT m

section MKF

theorem mkf_stateAssert (P : MachineState → Prop) : MKF (NonDet.stateAssert P) := by
  intro ms x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem mkf_machineRestLift {α : Type} (f : MachineRestMonad α) : MKF (machineRestLift f) := by
  unfold machineRestLift
  exact mkf_bind (mkf_gets _) fun _ => mkf_bind (mkf_selectF _) fun _ => mkf_bind (mkf_modify fun _ => rfl)
    fun _ => mkf_pure _

theorem mkf_invalidateASID (v a : Word) : MKF (invalidateASID v a) := mkf_machineOpLift _

theorem mkf_invalidateTranslationSingleASID (v a : Word) : MKF (invalidateTranslationSingleASID v a) :=
  mkf_machineOpLift _

theorem mkf_invalidateLocalPageStructureCacheASID (v a : Word) :
    MKF (invalidateLocalPageStructureCacheASID v a) := mkf_machineOpLift _

theorem mkf_readFpuState : MKF readFpuState := by
  unfold readFpuState
  exact mkf_bind (mkf_stateAssert _) fun _ => mkf_machineRestLift _

theorem mkf_writeFpuState (v : FpuState) : MKF (writeFpuState v) := by
  unfold writeFpuState
  exact mkf_bind (mkf_stateAssert _) fun _ => mkf_machineOpLift _

theorem mkf_enableFpu : MKF enableFpu := by
  unfold enableFpu
  exact mkf_bind (mkf_machineOpLift _) fun _ => mkf_modify fun _ => rfl

theorem mkf_disableFpu : MKF disableFpu := by
  unfold disableFpu
  exact mkf_bind (mkf_machineOpLift _) fun _ => mkf_modify fun _ => rfl

theorem mkf_isFpuEnable : MKF isFpuEnable := mkf_gets _

theorem mkf_getFaultAddress : MKF getFaultAddress := mkf_gets _

theorem mkf_ackInterrupt (i : Irq) : MKF (ackInterrupt i) := mkf_pure _

end MKF

theorem mtk_doMachineOp {α : Type} {mop : NonDet MachineState α} (hm : MKF mop) :
    MTK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  have h := mfk_doMachineOp hm σ x hx
  have ht : x.2.curTime = σ.curTime := by
    unfold doMachineOp at hx
    obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 h1] at h2
    obtain ⟨-, e2⟩ := h2
    simp only [Prod.mk.injEq] at e2 h3
    obtain ⟨-, rfl⟩ := e2
    rw [Set.mem_singleton_iff.1 h3] at hx
    rw [Set.mem_singleton_iff.1 hx]
  show (msF x.2, x.2.curTime) = (msF σ, σ.curTime)
  rw [h, ht]

/-- A `MTK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "mtk_leaf" : tactic
macro_rules | `(tactic| mtk_leaf) => `(tactic| fail "no mtk_leaf")
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_loadWord _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_storeWord _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_machineOpLift _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateTranslationSingleASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateLocalPageStructureCacheASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_readFpuState)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_writeFpuState _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_enableFpu)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_disableFpu)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_isFpuEnable)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_getFaultAddress)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_ackInterrupt _))

macro "mtk_auto" : tactic => `(tactic| repeat' (first | mtk_leaf | dk_step0))

theorem mtk_doExtendedOp (eop : DetExtMonad Unit) : MTK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doExtendedOp _)

theorem mtk_setObject (p : ObjRef) (o : KernelObject) : MTK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setObject _ _)

theorem mtk_setCap (c : Cap) (sl : CslotPtr) : MTK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setCap _ _)

theorem mtk_getCap (sl : CslotPtr) : MTK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getCap _)

theorem mtk_getPt (ptr : ObjRef) : MTK (getPt (Z := Unit) ptr) := by
  unfold getPt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPt _)

theorem mtk_getPte (ptr : ObjRef) : MTK (getPte (Z := Unit) ptr) := by
  unfold getPte; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPte _)

theorem mtk_getPd (ptr : ObjRef) : MTK (getPd (Z := Unit) ptr) := by
  unfold getPd; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPd _)

theorem mtk_getPde (ptr : ObjRef) : MTK (getPde (Z := Unit) ptr) := by
  unfold getPde; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPde _)

theorem mtk_getPml4 (ptr : ObjRef) : MTK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPml4 _)

theorem mtk_getPml4e (ptr : ObjRef) : MTK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPml4e _)

theorem mtk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : MTKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupPdptSlot _ _)

theorem mtk_getPdpt (ptr : ObjRef) : MTK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPdpt _)

theorem mtk_getPdpte (ptr : ObjRef) : MTK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getPdpte _)

theorem mtk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : MTKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupPdSlot _ _)

theorem mtk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : MTKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupPtSlot _ _)

theorem mtk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : MTK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setPdpt _ _)

theorem mtk_storePdpte (p : ObjRef) (pte : PDPTE) : MTK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storePdpte _ _)

theorem mtk_getAsidPool (ptr : ObjRef) : MTK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getAsidPool _)

theorem mtk_findVspaceForAsid (asid : Asid) : MTKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_findVspaceForAsid _)

theorem mtk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : MTK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setPt _ _)

theorem mtk_storePte (p : ObjRef) (pte : PTE) : MTK (storePte (Z := Unit) p pte) := by
  unfold storePte; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storePte _ _)

theorem mtk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : MTK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setPd _ _)

theorem mtk_storePde (p : ObjRef) (pde : PDE) : MTK (storePde (Z := Unit) p pde) := by
  unfold storePde; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storePde _ _)

theorem mtk_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : MTK (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unmapPage _ _ _ _)

theorem mtk_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : MTK (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performPageInvocationUnmap _ _)

theorem mtk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : MTK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setAsidPool _ _)

theorem mtk_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : MTK (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_flushTable _ _ _ _)

theorem mtk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : MTK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setPml4 _ _)

theorem mtk_setOriginal (slot : CslotPtr) (v : Bool) : MTK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setOriginal _ _)

theorem mtk_updateCdt (f : Cdt → Cdt) : MTK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateCdt _)

theorem mtk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : MTK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setUntypedCapAsFull _ _ _)

theorem mtk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : MTK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_retypeRegion _ _ _ _ _)

theorem mtk_storePml4e (p : ObjRef) (pte : PML4E) : MTK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storePml4e _ _)

theorem mtk_flushAll (vspace : ObjRef) (asid : Asid) : MTK (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_flushAll _ _)

theorem mtk_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : MTK (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unmapPdpt _ _ _)

theorem mtk_setIoportMask (f l : IoPort) (val : Bool) : MTK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setIoportMask _ _ _)

theorem mtk_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : MTK (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invalidatePageStructureCacheAsid _ _)

theorem mtk_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : MTK (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unmapPd _ _ _)

theorem mtk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : MTK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_capInsert _ _ _)

theorem mtk_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : MTK (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unmapPageTable _ _ _)

theorem mtk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : MTK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storeAsidPoolEntry _ _ _)

theorem mtk_performPageInvocation (iv : PageInvocation) : MTK (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performPageInvocation _)

theorem mtk_performPageTableInvocation (iv : PageTableInvocation) : MTK (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performPageTableInvocation _)

theorem mtk_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : MTK (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performPageDirectoryInvocation _)

theorem mtk_performPdptInvocation (iv : PdptInvocation) : MTK (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performPdptInvocation _)

theorem mtk_performAsidPoolInvocation (iv : AsidPoolInvocation) : MTK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performAsidPoolInvocation _)

theorem mtk_performIoportControlInvocation (i : IoPortControlInvocation) : MTK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performIoportControlInvocation _)

theorem mtk_performDeriveSubframe (iv : Fl4SubframeInvocation) : MTK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performDeriveSubframe _)

theorem mtk_performTestAndClearAccessed (_slot : ObjRef) : MTK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_performTestAndClearAccessed _)

theorem mtk_performPml4Flush (i : Fl4Pml4Invocation) : MTK (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact mtk_flushAll _ _

theorem mtk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : MTK (threadSet (Z := Unit) f t) := by
  unfold threadSet; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_threadSet' _ _)

theorem mtk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : MTK (threadGet (Z := Unit) f t) := by
  unfold threadGet; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_threadGet' _ _)

theorem mtk_setThreadState' (t : ObjRef) (ts : ThreadState) : MTK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setThreadState' _ _)

theorem mtk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    MTK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getSimpleKo' _ _)

theorem mtk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    MTK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setSimpleKo' _ _ _)

theorem mtk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    MTK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateSkObjRef' _ _ _ _)

theorem mtk_getSchedContext' (q : ObjRef) : MTK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getSchedContext' _)

theorem mtk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    MTK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateSchedContext' _ _)

theorem mtk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : MTK (asUser (Z := Unit) t u) := by
  unfold asUser; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_asUser' _ _)

theorem mtk_replyUnlinkTcb' (t r : ObjRef) : MTK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_replyUnlinkTcb' _ _)

theorem mtk_getThreadState' (t : ObjRef) : MTK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getThreadState' _)

theorem mtk_cancelIpc' (t : ObjRef) : MTK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_cancelIpc' _)

theorem mtk_suspend' (t : ObjRef) : MTK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_suspend' _)

theorem mtk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : MTK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getSkObjRef' _ _ _)

theorem mtk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : MTK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getScObjRef' _ _)

theorem mtk_getIrqSlot' (irq : Irq) : MTK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getIrqSlot' _)

theorem mtk_isFinalCap' (c : Cap) : MTK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_isFinalCap' _)

theorem mtk_hwAsidInvalidate' (a : Asid) (v : ObjRef) : MTK (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_hwAsidInvalidate' _ _)

theorem mtk_getCurrentCr3' : MTK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getCurrentCr3' )

theorem mtk_setCurrentCr3' (c : Cr3) : MTK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setCurrentCr3' _)

theorem mtk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : MTK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setCurrentVspaceRoot' _ _)

theorem mtk_setVmRoot' (t : ObjRef) : MTK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setVmRoot' _)

theorem mtk_freeIoportRange' (f l : IoPort) : MTK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_freeIoportRange' _ _)

theorem mtk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : MTK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupIpcBuffer' _ _)

theorem mtk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, MTK (g a b)) :
    ∀ l1 l2, MTK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => mtk_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtk_zipWithMx' (fun _ _ => ?_) _ _)

theorem mtk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : MTK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_storeWordOffs' _ _ _)

theorem mtk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : MTK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setMrs' _ _ _)

theorem mtk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : MTK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setMessageInfo' _ _)

theorem mtk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : MTK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archThreadSet' _ _)

theorem mtk_saveFpuState' (t : ObjRef) : MTK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_saveFpuState' _)

theorem mtk_loadFpuState' (t : ObjRef) : MTK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_loadFpuState' _)

theorem mtk_setX64CurrentFpuOwner' (o : Option ObjRef) : MTK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setX64CurrentFpuOwner' _)

theorem mtk_switchLocalFpuOwner' (o : Option ObjRef) : MTK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_switchLocalFpuOwner' _)

theorem mtk_getTcbQueue' (d : Domain) (p : Priority) : MTK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getTcbQueue' _ _)

theorem mtk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : MTK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setTcbQueue' _ _ _)

theorem mtk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : MTK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbSchedAction' _ _)

theorem mtk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : MTK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getTcbObjRef' _ _)

theorem mtk_setSchedulerAction' (a : SchedulerAction) : MTK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setSchedulerAction' _)

theorem mtk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : MTK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getScRefillSufficient' _ _)

theorem mtk_getScRefillReady' (sc : ObjRef) : MTK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getScRefillReady' _)

theorem mtk_tcbReleaseRemove' (t : ObjRef) : MTK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbReleaseRemove' _)

theorem mtk_rescheduleRequired' : MTK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_rescheduleRequired' )

theorem mtk_testReschedule' (t : ObjRef) : MTK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_testReschedule' _)

theorem mtk_possibleSwitchTo' (t : ObjRef) : MTK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_possibleSwitchTo' _)

theorem mtk_tcbEpDequeue' (t e : ObjRef) : MTK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbEpDequeue' _ _)

theorem mtk_tcbNtfnDequeue' (t n : ObjRef) : MTK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbNtfnDequeue' _ _)

theorem mtk_isRoundRobin' (sc : ObjRef) : MTK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_isRoundRobin' _)

theorem mtk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : MTK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateRefillHd' _ _)

theorem mtk_getRefillHead' (sc : ObjRef) : MTK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getRefillHead' _)

theorem mtk_refillPopHead' (sc : ObjRef) : MTK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillPopHead' _)

theorem mtk_mergeOverlappingRefills' (sc : ObjRef) : MTK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_mergeOverlappingRefills' _)

theorem mtk_refillHeadOverlappingLoop' (sc : ObjRef) : MTK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillHeadOverlappingLoop' _)

theorem mtk_refillUnblockCheck' (sc : ObjRef) : MTK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillUnblockCheck' _)

theorem mtk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : MTK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_ifCondRefillUnblockCheck' _ _ _)

theorem mtk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : MTK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem mtk_restartThreadIfNoFault' (t : ObjRef) : MTK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_restartThreadIfNoFault' _)

theorem mtk_removeAndRestartEpQueuedThread' (t e : ObjRef) : MTK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_removeAndRestartEpQueuedThread' _ _)

theorem mtk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : MTK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_removeAndRestartNtfnQueuedThread' _ _)

theorem mtk_replyUnlinkSc' (sc r : ObjRef) : MTK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_replyUnlinkSc' _ _)

theorem mtk_schedContextDonate' (sc t : ObjRef) : MTK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextDonate' _ _)

theorem mtk_schedContextUpdateConsumed' (sc : ObjRef) : MTK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUpdateConsumed' _)

theorem mtk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : MTK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_replyFromKernel' _ _)

theorem mtk_setConsumed' (sc t : ObjRef) : MTK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setConsumed' _ _)

theorem mtk_schedContextCancelYieldTo' (t : ObjRef) : MTK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextCancelYieldTo' _)

theorem mtk_fpuRelease' (t : ObjRef) : MTK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_fpuRelease' _)

theorem mtk_deleteAsidPool' (b : Asid) (p : ObjRef) : MTK (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_deleteAsidPool' _ _)

theorem mtk_deleteAsid' (a : Asid) (p : ObjRef) : MTK (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_deleteAsid' _ _)

theorem mtk_archPostCapDeletion' (c : ArchCap) : MTK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPostCapDeletion' _)

theorem mtk_cancelAllIpc' (e : ObjRef) : MTK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_cancelAllIpc' _)

theorem mtk_schedContextMaybeUnbindNtfn' (n : ObjRef) : MTK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextMaybeUnbindNtfn' _)

theorem mtk_unbindMaybeNotification' (n : ObjRef) : MTK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unbindMaybeNotification' _)

theorem mtk_cancelAllSignals' (n : ObjRef) : MTK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_cancelAllSignals' _)

theorem mtk_replyRemove' (t r : ObjRef) : MTK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_replyRemove' _ _)

theorem mtk_unbindNotification' (t : ObjRef) : MTK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unbindNotification' _)

theorem mtk_schedContextUnbindTcb' (sc : ObjRef) : MTK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUnbindTcb' _)

theorem mtk_completeYieldTo' (t : ObjRef) : MTK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_completeYieldTo' _)

theorem mtk_unbindFromSc' (t : ObjRef) : MTK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_unbindFromSc' _)

theorem mtk_schedContextUnbindAllTcbs' (sc : ObjRef) : MTK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUnbindAllTcbs' _)

theorem mtk_schedContextUnbindNtfn' (sc : ObjRef) : MTK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUnbindNtfn' _)

theorem mtk_schedContextUnbindReply' (sc : ObjRef) : MTK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUnbindReply' _)

theorem mtk_schedContextUnbindYieldFrom' (sc : ObjRef) : MTK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextUnbindYieldFrom' _)

theorem mtk_schedContextSetInactive' (sc : ObjRef) : MTK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextSetInactive' _)

theorem mtk_prepareThreadDelete' (t : ObjRef) : MTK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_prepareThreadDelete' _)

theorem mtk_archFinaliseCap' (c : ArchCap) (x : Bool) : MTK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archFinaliseCap' _ _)

theorem mtk_fastFinalise' (c : Cap) (b : Bool) : MTK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_fastFinalise' _ _)

/-- `empty_slot` with a null cleanup: `postCapDeletion nullCap` does nothing. -/
theorem mtk_emptySlotNull (sl : CslotPtr) : MTK (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot postCapDeletion; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_emptySlotNull _)

theorem mtk_capDeleteOne' (sl : CslotPtr) : MTK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_capDeleteOne' _)

theorem mtk_deletingIrqHandler' (irq : Irq) : MTK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_deletingIrqHandler' _)

theorem mtk_finaliseCap (c : Cap) (b : Bool) : MTK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_finaliseCap _ _)

theorem mtk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : MTK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_capSwap' _ _ _ _)

theorem mtk_capSwapForDelete' (s1 s2 : CslotPtr) : MTK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_capSwapForDelete' _ _)

theorem mtk_capMove' (c : Cap) (s1 s2 : CslotPtr) : MTK (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_capMove' _ _ _)

theorem mtk_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    MTK (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_removeAndRestartBadgedThread' _ _ _)

theorem mtk_cancelBadgedSends' (e : ObjRef) (b : Badge) : MTK (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_cancelBadgedSends' _ _)

theorem mtk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : MTK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_orderedInsert' _ _ _ _)

theorem mtk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : MTK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_readyTimesAppend' _ _)

theorem mtk_tcbReleaseEnqueue' (t : ObjRef) : MTK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbReleaseEnqueue' _)

theorem mtk_tcbAppend' (t : ObjRef) (q : List ObjRef) : MTK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbAppend' _ _)

theorem mtk_postpone' (sc : ObjRef) : MTK (postpone (Z := Unit) sc) := by
  unfold postpone; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_postpone' _)

theorem mtk_threadSetPriority' (t : ObjRef) (p : Priority) : MTK (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_threadSetPriority' _ _)

theorem mtk_reorderEp' (e t : ObjRef) : MTK (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_reorderEp' _ _)

theorem mtk_reorderNtfn' (n t : ObjRef) : MTK (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_reorderNtfn' _ _)

theorem mtk_archPostModifyRegisters' (c t : ObjRef) : MTK (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPostModifyRegisters' _ _)

theorem mtk_schedContextResume' (sc : ObjRef) : MTK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextResume' _)

theorem mtk_testPossibleSwitchTo' (t : ObjRef) : MTK (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_testPossibleSwitchTo' _)

theorem mtk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : MTK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem mtke_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : MTK m) :
    MTKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtke_withoutPreemption' ?_)

theorem mtke_rab (p : Cap × CapRef) : MTKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (mtk_getCap _)) fun nc => ?_
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
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtke_rab _)

theorem mtke_resolveAddressBits (p : Cap × CapRef) : MTKE (resolveAddressBits (Z := Unit) p) := mtke_rab p
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtke_resolveAddressBits _)

theorem mtk_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : MTKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupSlotForThread' _ _)

theorem mtk_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : MTKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupCapAndSlot' _ _)

theorem mtk_lookupCap' (thread : ObjRef) (ref : CapRef) : MTKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupCap' _ _)

theorem mtk_captransferFromWords' (ptr : Word) : MTK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_captransferFromWords' _)

theorem mtk_loadCapTransfer' (buffer : ObjRef) : MTK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_loadCapTransfer' _)

theorem mtk_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : MTK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setExtraBadge' _ _ _)

theorem mtke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : MTKE m) :
    MTKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtke_lookupErrorOnFailure' _ ?_)

theorem mtk_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : MTKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupSlotForCnodeOp' _ _ _ _)

theorem mtk_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : MTKE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact mtk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupTargetSlot' _ _ _)

theorem mtke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : MTKE (f a)) :
    MTKE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtke_bind_returnOk' ?_)

theorem mtk_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : MTK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_archPostResetUntyped' _ _)

theorem mtk_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : MTK (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_retypeRegionWith' _ _ _ _ _ _)

theorem mtk_copyGlobalMappings' (newPm : ObjRef) : MTK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_copyGlobalMappings' _)

theorem mtk_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : MTK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_initArchObjects' _ _ _ _ _ _)

theorem mtk_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : MTK (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_createCap' _ _ _ _ _)

theorem mtk_ensureNoChildren' (cslotPtr : CslotPtr) : MTKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_ensureNoChildren' _)

theorem mtk_getRefillTail' (scPtr : ObjRef) : MTK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getRefillTail' _)

theorem mtk_getRefills' (scPtr : ObjRef) : MTK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getRefills' _)

theorem mtk_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : MTK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillAddTail' _ _)

theorem mtk_refillFull' (scPtr : ObjRef) : MTK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillFull' _)

theorem mtk_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : MTK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateRefillTl' _ _)

theorem mtk_scheduleUsed' (scPtr : ObjRef) (new : Refill) : MTK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_scheduleUsed' _ _)

theorem mtk_refillSize' (scPtr : ObjRef) : MTK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillSize' _)

theorem mtk_refillSingle' (scPtr : ObjRef) : MTK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillSingle' _)

theorem mtk_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : MTK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_chargeEntireHeadRefill' _ _)

theorem mtk_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : MTK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_mergeNonoverlappingHeadRefill' _)

theorem mtk_updateIrqState' (irq : Irq) (irqState : X64IRQState) : MTK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateIrqState' _ _)

theorem mtke_archDeriveCap' (c : ArchCap) : MTKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtke_archDeriveCap' _)

theorem mtke_deriveCap' (sl : CslotPtr) (c : Cap) : MTKE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtke_deriveCap' _ _)

theorem mtk_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : MTK (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_makeArchFaultMsg' _ _)

theorem mtke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : MTKE m) :
    MTKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtke_unifyFailure' ?_)

theorem mtk_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : MTKE m) :
    MTK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtk_emptyOnFailure' ?_)

theorem mtk_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : MTKE m) :
    MTK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtk_constOnFailure' _ ?_)

theorem mtke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : MTKE m) :
    MTKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible refine mtke_capFaultOnFailure' _ _ ?_)

theorem mtk_loadWordOffs' (ptr : ObjRef) (offs : Nat) : MTK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_loadWordOffs' _ _)

theorem mtk_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : MTK (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => mtk_loadWordOffs' _ _) _)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getExtraCptrs' _ _)

theorem mtk_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : MTK (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getReceiveSlots' _ _)

theorem mtk_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      MTK (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; mtk_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := mtk_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    mtk_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_transferCapsLoop' _ _ _ _ _ _)

theorem mtk_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : MTKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_lookupExtraCaps' _ _ _)

theorem mtk_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : MTK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_copyMrs' _ _ _ _ _)

theorem mtk_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : MTK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_transferCaps' _ _ _ _ _)

theorem mtk_makeFaultMsg' (f : Fault) (t : ObjRef) : MTK (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_makeFaultMsg' _ _)

theorem mtk_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : MTK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleOverrun' _ _)

theorem mtk_headInsufficientLoop' (scPtr : ObjRef) : MTK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_headInsufficientLoop' _)

theorem mtk_getMessageInfo' (thread : ObjRef) : MTK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getMessageInfo' _)

theorem mtk_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : MTK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_tcbEpAppend' _ _ _)

theorem mtk_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : MTK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doNormalTransfer' _ _ _ _ _ _ _)

theorem mtk_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : MTK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doFaultTransfer' _ _ _ _)

theorem mtk_bindScReply' (scPtr replyPtr : ObjRef) : MTK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_bindScReply' _ _)

theorem mtk_isValidTimeoutHandler' (tptr : ObjRef) : MTK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_isValidTimeoutHandler' _)

theorem mtk_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : MTK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doIpcTransfer' _ _ _ _ _)

theorem mtk_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : MTK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_replyPush' _ _ _ _)

theorem mtk_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : MTK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_sendIpcBlocked' _ _ _ _ _ _)

theorem mtk_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : MTK (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_sendIpc' _ _ _ _ _ _ _ _)

theorem mtk_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : MTK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_sendFaultIpc' _ _ _ _)

theorem mtk_refillBudgetCheckRoundRobin' (usage : Ticks) : MTK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillBudgetCheckRoundRobin' _)

theorem mtk_refillBudgetCheck' (usage : Ticks) : MTK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillBudgetCheck' _)

theorem mtk_maybeAddEmptyTail' (scPtr : ObjRef) : MTK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_maybeAddEmptyTail' _)

theorem mtk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : MTK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_maybeDonateSc' _ _)

theorem mtk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : MTK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_updateWaitingNtfn' _ _ _)

theorem mtk_handleTimeout' (tptr : ObjRef) (ex : Fault) : MTK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleTimeout' _ _)

theorem mtk_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : MTK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getMrs' _ _ _)

theorem mtk_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    MTK (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_handleFaultReply' _ _ _ _)

theorem mtk_returnConsumed' (scPtr : ObjRef) : MTK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_returnConsumed' _)

theorem mtk_schedContextBindNtfn' (sc ntfn : ObjRef) : MTK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextBindNtfn' _ _)

theorem mtk_schedContextYieldTo' (scPtr : ObjRef) : MTK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_schedContextYieldTo' _)

theorem mtk_getScActive' (scPtr : ObjRef) : MTK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getScActive' _)

theorem mtk_commitTime' : MTK (commitTime (Z := Unit) ) := by
  unfold commitTime; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_commitTime' )

theorem mtk_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : MTK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillNew' _ _ _ _)

theorem mtk_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : MTK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_refillUpdate' _ _ _ _)

theorem mtk_sendSignal' (n : ObjRef) (b : Badge) : MTK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_sendSignal' _ _)

theorem mtk_doReplyTransfer' (s r : ObjRef) (g : Bool) : MTK (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doReplyTransfer' _ _ _)

theorem mtk_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : MTK (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_invokeSchedControlConfigureFlags' _)

end

end Fl4Proofs.P3.MachT
