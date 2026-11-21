/-
P3 (DESIGN.md §9), invariant line G1 (rd13b, KENTRY-PLAN rd12b handoff 1):
**the VSpace / IO port arms keep every scheduler view** (spec side only).

* SVK's `SVM` family over the VSpace cone, generated from SpecInvRdP's `CFK`
  family (same functions, same order; `sv13_*`, untracked generator
  proofs/scratch/rd13b/mksv.py): every page-table / ASID-pool / IO-port writer
  rewrites an object of the same arch type, so no TCB or SC view changes.
* **`perfA_archSpec`**: every l4v arch invocation but ASID control (MakePool:
  a retype) has `PerfA` from `KP σ0 ∧ CB0`; **`perfA_pml4Flush`**.
-/
import Fl4Proofs.P3.SpecInvRd13bB
open Classical

namespace Fl4Proofs.P3.SInvR.A13b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 1000000

theorem sv13_getPt (ptr : ObjRef) : SVK.SVM (getPt (Z := Unit) ptr) := by
  unfold getPt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPt _)

theorem sv13_getPte (ptr : ObjRef) : SVK.SVM (getPte (Z := Unit) ptr) := by
  unfold getPte; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPte _)

theorem sv13_getPd (ptr : ObjRef) : SVK.SVM (getPd (Z := Unit) ptr) := by
  unfold getPd; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPd _)

theorem sv13_getPde (ptr : ObjRef) : SVK.SVM (getPde (Z := Unit) ptr) := by
  unfold getPde; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPde _)

theorem sv13_getPml4 (ptr : ObjRef) : SVK.SVM (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPml4 _)

theorem sv13_getPml4e (ptr : ObjRef) : SVK.SVM (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPml4e _)

theorem sv13_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : SVK.SVE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_lookupPdptSlot _ _)

theorem sv13_getPdpt (ptr : ObjRef) : SVK.SVM (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPdpt _)

theorem sv13_getPdpte (ptr : ObjRef) : SVK.SVM (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getPdpte _)

theorem sv13_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : SVK.SVE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_lookupPdSlot _ _)

theorem sv13_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : SVK.SVE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_lookupPtSlot _ _)

theorem sv13_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SVK.SVM (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setPdpt _ _)

theorem sv13_storePdpte (p : ObjRef) (pte : PDPTE) : SVK.SVM (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_storePdpte _ _)

theorem sv13_getAsidPool (ptr : ObjRef) : SVK.SVM (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_getAsidPool _)

theorem sv13_findVspaceForAsid (asid : Asid) : SVK.SVE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_findVspaceForAsid _)

theorem sv13_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SVK.SVM (setPt (Z := Unit) ptr pt) := by
  unfold setPt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setPt _ _)

theorem sv13_storePte (p : ObjRef) (pte : PTE) : SVK.SVM (storePte (Z := Unit) p pte) := by
  unfold storePte; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_storePte _ _)

theorem sv13_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SVK.SVM (setPd (Z := Unit) ptr pd) := by
  unfold setPd; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setPd _ _)

theorem sv13_storePde (p : ObjRef) (pde : PDE) : SVK.SVM (storePde (Z := Unit) p pde) := by
  unfold storePde; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_storePde _ _)

theorem sv13_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SVK.SVM (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_unmapPage _ _ _ _)

theorem sv13_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : SVK.SVM (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPageInvocationUnmap _ _)

theorem sv13_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SVK.SVM (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setAsidPool _ _)

theorem sv13_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : SVK.SVM (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_flushTable _ _ _ _)

theorem sv13_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SVK.SVM (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setPml4 _ _)

theorem sv13_storePml4e (p : ObjRef) (pte : PML4E) : SVK.SVM (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_storePml4e _ _)

theorem sv13_flushAll (vspace : ObjRef) (asid : Asid) : SVK.SVM (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_flushAll _ _)

theorem sv13_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SVK.SVM (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_unmapPdpt _ _ _)

theorem sv13_setIoportMask (f l : IoPort) (val : Bool) : SVK.SVM (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_setIoportMask _ _ _)

theorem sv13_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SVK.SVM (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_invalidatePageStructureCacheAsid _ _)

theorem sv13_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SVK.SVM (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_unmapPd _ _ _)

theorem sv13_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SVK.SVM (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_unmapPageTable _ _ _)

theorem sv13_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : SVK.SVM (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_storeAsidPoolEntry _ _ _)

theorem sv13_performPageInvocation (iv : PageInvocation) : SVK.SVM (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPageInvocation _)

theorem sv13_performPageTableInvocation (iv : PageTableInvocation) : SVK.SVM (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPageTableInvocation _)

theorem sv13_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : SVK.SVM (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPageDirectoryInvocation _)

theorem sv13_performPdptInvocation (iv : PdptInvocation) : SVK.SVM (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPdptInvocation _)

theorem sv13_performAsidPoolInvocation (iv : AsidPoolInvocation) : SVK.SVM (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performAsidPoolInvocation _)

theorem sv13_performIoportControlInvocation (i : IoPortControlInvocation) : SVK.SVM (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performIoportControlInvocation _)

theorem sv13_performDeriveSubframe (iv : Fl4SubframeInvocation) : SVK.SVM (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performDeriveSubframe _)

theorem sv13_performTestAndClearAccessed (_slot : ObjRef) : SVK.SVM (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performTestAndClearAccessed _)

theorem sv13_performPml4Flush (i : Fl4Pml4Invocation) : SVK.SVM (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact sv13_flushAll _ _

theorem sv13_performIoPortInvocation (i : IoPortInvocation) : SVK.SVM (performIoPortInvocation (Z := Unit) i) := by
  rcases i with ⟨port, d⟩
  cases d <;> simp only [performIoPortInvocation, portIn, portOut] <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performIoPortInvocation _)

theorem cfk13_performIoPortInvocation (i : IoPortInvocation) : CFK (performIoPortInvocation (Z := Unit) i) := by
  rcases i with ⟨port, d⟩
  cases d <;> simp only [performIoPortInvocation, portIn, portOut] <;> cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk13_performIoPortInvocation _)

macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv13_performPml4Flush _)

theorem cfk13_performPml4Flush (i : Fl4Pml4Invocation) : CFK (performPml4Flush (Z := Unit) i) := by
  cases i; simp only [performPml4Flush, flushAll]; cfk_auto
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk13_performPml4Flush _)

/-- **Every l4v arch invocation but ASID control.** -/
theorem perfA_archSpec {σ0 s : State Unit} (bl call don : Bool) (i : ArchInvocation)
    (hi : ∀ o, i ≠ .invokeASIDControl o) (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeArchObject (.spec i)) s := by
  cases i
  case invokeASIDControl o => exact absurd rfl (hi o)
  all_goals refine perfA_sve ?_ ?_ ?_ hK hb <;>
    simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation, archNoReturn]
  all_goals first
    | (ne_auto; done)
    | (cfk_auto; done)
    | (refine SVK.sve_liftE ?_; sv_auto; done)
    | skip

theorem perfA_pml4Flush {σ0 s : State Unit} (bl call don : Bool) (i : Fl4Pml4Invocation)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeArchObject (.pml4Flush i)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archNoReturn]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; ne_auto) hK hb

/-! ## TCB register arms without suspend / resume -/

theorem perfA_readRegisters {σ0 s : State Unit} (bl call don : Bool) (src : ObjRef) (n a : _)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeTCB (.readRegisters src false n a)) s := by
  refine perfA_sve ?_ ?_ ?_ hK hb <;>
    simp only [fl4PerformInvocation, invokeTcb, NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · ne_auto

theorem perfA_writeRegisters {σ0 s : State Unit} (bl call don : Bool) (dest : ObjRef) (v a : _)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeTCB (.writeRegisters dest false v a)) s := by
  refine perfA_sve ?_ ?_ ?_ hK hb <;>
    simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo, archPostModifyRegisters,
      NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · ne_auto

theorem perfA_copyRegisters {σ0 s : State Unit} (bl call don : Bool) (dest src : ObjRef) (f i : Bool) (a : _)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeTCB (.copyRegisters dest src false false f i a)) s := by
  refine perfA_sve ?_ ?_ ?_ hK hb <;>
    simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo, archPostModifyRegisters,
      NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · ne_auto

end

end Fl4Proofs.P3.SInvR.A13b
