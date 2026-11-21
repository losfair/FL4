/-
P3 (DESIGN.md §9), invariant line G1 (invA2): **FaultTcbsS (l4v
`fault_tcbs_valid_states`) kept by the spec functions** (spec side only,
outside the JAtZ cone), with a list `L` of threads known to have no fault.

* `ftlQ L p x := ftsQ x ∧ (p ∈ L → x.tcbFault = none)`, `FTL L := TP (ftlQ L)`;
  `FTL [] σ ↔ FaultTcbsS σ`. Carrying `L` lets a wake-up to Running /
  Restart / a receive state of a thread `t ∈ L` keep the invariant
  (`ft_setThreadState`'s side condition: the new state is Inactive /
  BlockedOnSend / BlockedOnReply, or `t ∈ L`).
* Leaves: SpecInvFaultTcbsT's `tp_*` writers; every TCB write of the spec but
  the fault write of `sendFaultIpc` and the wake-ups keeps `ftlQ L`
  pointwise (fault cleared, or state and fault unchanged).
* The rest: one lemma per spec function by `ft_auto` (generated, as
  SpecInvNativeScopeF*; invA scratch gen.py), for every `L`; the functions
  with a wake-up or the fault write are proved by hand (SpecInvFaultTcbsW).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsT
import Fl4Proofs.P3.SpecInvFaultTcbs
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- `ftsQ`, and no fault for the threads of `L`. -/
def ftlQ (L : List ObjRef) (p : ObjRef) (x : Tcb) : Prop := ftsQ x ∧ (p ∈ L → x.tcbFault = none)

/-- FaultTcbsS, and no fault at the threads of `L`. -/
abbrev FTL (L : List ObjRef) (σ : State Unit) : Prop := TP (ftlQ L) σ

theorem FTL.nil_iff (σ : State Unit) : FTL [] σ ↔ FaultTcbsS σ :=
  ⟨fun h p x hp => (h p x hp).1, fun h p x hp => ⟨h p x hp, fun h => nomatch h⟩⟩

variable {L : List ObjRef}

abbrev FTK {α : Type} (L : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (FTL L) m
abbrev FTKE {ε α : Type} (L : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (FTL L) m

/-- The side conditions of the TCB-writer leaves. -/
macro "ft_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (intro _ _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (exact Or.inl trivial)
  | (exact Or.inr (by simp; done))
  | (simp [ftlQ, ftsQ, faultTcbSt]; done)
  | (intro _ hx; simpa [ftlQ, ftsQ, faultTcbSt] using hx)
  | (intro _ _ hx; simpa [ftlQ, ftsQ, faultTcbSt] using hx))

syntax "ft_leaf" : tactic
macro_rules | `(tactic| ft_leaf) => `(tactic| fail "no ft_leaf")

macro "ft_auto" : tactic => `(tactic| repeat' (first | ft_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); ft_side))
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- `set_thread_state`: a fault-holding state, or a thread known to have no fault. -/
theorem ft_setThreadState (t : ObjRef) (ts : ThreadState) (h : faultTcbSt ts ∨ t ∈ L) :
    FTK L (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun x hx => ⟨fun hf => ?_, hx.2⟩) fun _ => ?_
  · rcases h with h | h
    · exact h
    · exact absurd (hx.2 h) hf
  · unfold setThreadStateAct setSchedulerAction; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ft_setThreadState _ _ ?_); ft_side))

theorem ft_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, ftlQ L t x → ftlQ L t (fn v x)) : FTK L (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| ft_leaf) => `(tactic| ((with_reducible refine ft_optionUpdateThread _ _ _ ?_); ft_side))

theorem ft_archActivateIdleThread (_t : ObjRef) : FTK L (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archActivateIdleThread _)

theorem ft_archCheckIrq (_irq : Data) : FTKE L (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archCheckIrq _)

theorem ft_getCap (a0 : CslotPtr) : FTK L (getCap (Z := Unit) a0) := by
  unfold getCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCap _)

theorem ft_ensureEmpty (slot : CslotPtr) : FTKE L (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureEmpty _)

theorem ft_isIoportRangeFree (f l : IoPort) : FTK L (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isIoportRangeFree _ _)

theorem ft_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : FTKE L m) : FTKE L (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_lookupErrorOnFailure _ _ ?_)

theorem ft_resolveAddressBits' (p : Cap × CapRef) : FTKE L (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ft_auto)) fun nc => ?_
        split
        · exact ft_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resolveAddressBits' _)

theorem ft_resolveAddressBits (a0 : Cap × CapRef) : FTKE L (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_resolveAddressBits _)

theorem ft_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : FTKE L (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSlotForCnodeOp _ _ _ _)

theorem ft_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupTargetSlot _ _ _)

theorem ft_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : FTKE L (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIoportControlInvocation _ _ _ _ _)

theorem ft_getAsidPool (ptr : ObjRef) : FTK L (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getAsidPool _)

theorem ft_findVspaceForAsid (asid : Asid) : FTKE L (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_findVspaceForAsid _)

theorem ft_getPdpt (ptr : ObjRef) : FTK L (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPdpt _)

theorem ft_getPdpte (ptr : ObjRef) : FTK L (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPdpte _)

theorem ft_isFinalCap (cap : Cap) : FTK L (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isFinalCap _)

theorem ft_getPml4 (ptr : ObjRef) : FTK L (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPml4 _)

theorem ft_getPml4e (ptr : ObjRef) : FTK L (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPml4e _)

theorem ft_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPdptSlot _ _)

theorem ft_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageDirectoryInvocation _ _ _ _ _)

theorem ft_checkVpAlignment (sz : VMPageSize) (vptr : Word) : FTKE L (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_checkVpAlignment _ _)

theorem ft_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPdSlot _ _)

theorem ft_getPd (ptr : ObjRef) : FTK L (getPd (Z := Unit) ptr) := by
  unfold getPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPd _)

theorem ft_getPde (ptr : ObjRef) : FTK L (getPde (Z := Unit) ptr) := by
  unfold getPde; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPde _)

theorem ft_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : FTKE L (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPtSlot _ _)

theorem ft_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : FTKE L (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_createMappingEntries _ _ _ _ _ _)

theorem ft_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : FTKE L (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureSafeMapping _)

theorem ft_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageInvocation _ _ _ _ _)

theorem ft_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePageTableInvocation _ _ _ _ _)

theorem ft_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePdptInvocation _ _ _ _ _)

theorem ft_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : FTKE L (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensurePortOperationAllowed _ _ _)

theorem ft_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : FTKE L (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePortInvocation _ _ _)

theorem ft_ensureNoChildren (cslotPtr : CslotPtr) : FTKE L (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ensureNoChildren _)

theorem ft_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : FTK L (selectExt (Z := Unit) a S) := by
  unfold selectExt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_selectExt _ _)

theorem ft_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDecodeInvocation _ _ _ _ _ _)

theorem ft_getIrqState (irq : Irq) : FTK L (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getIrqState _)

theorem ft_isIrqActive (irq : Irq) : FTK L (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isIrqActive _)

theorem ft_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDecodeIrqControlInvocation _ _ _ _)

theorem ft_archDeriveCap (c : ArchCap) : FTKE L (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_archDeriveCap _)

theorem ft_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : FTK L (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_hwAsidInvalidate _ _)

theorem ft_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : FTK L (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setAsidPool _ _)

theorem ft_getCurrentCr3  : FTK L (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCurrentCr3)

theorem ft_setCurrentCr3 (c : Cr3) : FTK L (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCurrentCr3 _)

theorem ft_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : FTK L (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setCurrentVspaceRoot _ _)

theorem ft_setVmRoot (tcb : ObjRef) : FTK L (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setVmRoot _)

theorem ft_deleteAsid (asid : Asid) (pml4 : ObjRef) : FTK L (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deleteAsid _ _)

theorem ft_deleteAsidPool (base : Asid) (ptr : ObjRef) : FTK L (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deleteAsidPool _ _)

theorem ft_getPt (ptr : ObjRef) : FTK L (getPt (Z := Unit) ptr) := by
  unfold getPt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPt _)

theorem ft_getPte (ptr : ObjRef) : FTK L (getPte (Z := Unit) ptr) := by
  unfold getPte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getPte _)

theorem ft_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : FTK L (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPd _ _)

theorem ft_storePde (p : ObjRef) (pde : PDE) : FTK L (storePde (Z := Unit) p pde) := by
  unfold storePde; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePde _ _)

theorem ft_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : FTK L (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPdpt _ _)

theorem ft_storePdpte (p : ObjRef) (pte : PDPTE) : FTK L (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePdpte _ _)

theorem ft_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : FTK L (setPt (Z := Unit) ptr pt) := by
  unfold setPt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setPt _ _)

theorem ft_storePte (p : ObjRef) (pte : PTE) : FTK L (storePte (Z := Unit) p pte) := by
  unfold storePte; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storePte _ _)

theorem ft_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : FTK L (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPage _ _ _ _)

theorem ft_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : FTK L (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_flushTable _ _ _ _)

theorem ft_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : FTK L (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_invalidatePageStructureCacheAsid _ _)

theorem ft_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : FTK L (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_unmapPageTable _ _ _)

theorem ft_flushAll (vspace : ObjRef) (asid : Asid) : FTK L (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_flushAll _ _)
end

end Fl4Proofs.P3.SInv
