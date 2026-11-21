/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch14 (i)): **the first-phase
invocation keeps the current thread out of the ready queues and no switch to
it pending** (spec side only), for the receive of ReplyRecv / NBSendRecv /
NBSendWait at the mid state (`JMidRecvHyp`, XTopJointKEntry8).

* `qV σ := (readyQueues, schedulerAction)`, `QV m := FK qV m` (VsDom's
  projection frame; the leaves as SpecGlobFK's `GK` lemmas, scripted copy):
  the front of the invocation (`getMessageInfo`, `midF`, `midE`: the lookups
  and the first-phase decode), every arch invocation, IRQ control and the IRQ
  acknowledge write neither field.
* `CQ ct σ := CtRs ct σ ∧ PPNQ.NQ ct σ` (SpecPPRQ: `ct` in no ready queue, no
  switch to `ct` pending); `PQ ct m`: every outcome of `m` from a `CQ` state is
  `CQ`. `pq_of`: `KF` (XTopJointMidRunK) and `QK` (SpecPPRQ) together.
  `pq_sendIpc` (non-blocking non-calling), `pq_sendSignal` (from `NQ`: ct in
  no notification queue), `pq_doReplyTransfer`: the woken thread is `≠ ct`
  by the same state reads as XTopJointMidRunP's `pr_` lemmas (receiver
  `BlockedOnReceive` / `BlockedOnReply`, bound TCB `receive_blocked`, queue
  head not ct), so `possible_switch_to` keeps `PPNQ.NQ ct` (`qk_possibleSwitchTo`).
* `perf_firstQ`: every `FirstInv` perform but `PerfW` keeps `CQ`;
  `JMidPerfHypQ` [W]: sch12's `JMidPerfHyp` with `CQ` for `CtRs` (same
  `MidPerfAt` path restriction, same l4v lemma family:
  `perform_invocation_not_blocking_not_calling_ct_active` and
  `ct_not_in_q`/`scheduler_act_sane` kept by invoke_untyped, invoke_irq_handler,
  perform_asid_control_invocation: none of them enqueues or switches to the
  current thread); `JMidPerfHypQ.toP`.
* `midRunQ_shell`: from `CQ ∧ NQ` at the entry, every outcome of the
  first-phase non-blocking non-calling invocation is `CQ`.
-/
import Fl4Proofs.P3.XTopJointMidRunS
import Fl4Proofs.P3.SpecPPRQ
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The ready queues and the scheduler action. -/
def qV (σ : State Unit) : (Domain → Priority → List ObjRef) × SchedulerAction :=
  (σ.readyQueues, σ.schedulerAction)

/-- Every outcome of `m` keeps the ready queues and the action. -/
abbrev QV {α : Type} (m : NonDet (State Unit) α) : Prop := FK qV m

/-- `QV` for the exception monad. -/
abbrev QVE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE qV m


/-- A `QV` lemma of a spec function (extended below, one rule per lemma). -/
syntax "qv_leaf" : tactic
macro_rules | `(tactic| qv_leaf) => `(tactic| fail "no qv_leaf")

macro "qv_auto" : tactic => `(tactic| repeat' (first | qv_leaf | dk_step0))

theorem qv_doMachineOp {α : Type} (mop : NonDet MachineState α) : QV (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_doMachineOp _)

theorem qv_doExtendedOp (eop : DetExtMonad Unit) : QV (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_doExtendedOp _)
theorem qve_pure_run {ε α : Type} (a : α) : QV (ExceptT.run (pure a : NonDetE (State Unit) ε α)) := dk_pure _

theorem qv_setObject (p : ObjRef) (o : KernelObject) : QV (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setObject _ _)

theorem qv_setCap (c : Cap) (sl : CslotPtr) : QV (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setCap _ _)

theorem qv_getCap (sl : CslotPtr) : QV (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getCap _)

theorem qv_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    QV (portOut (Z := Unit) f w) := by
  unfold portOut; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_portOut _ _)

theorem qv_getPt (ptr : ObjRef) : QV (getPt (Z := Unit) ptr) := by
  unfold getPt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPt _)

theorem qv_getPte (ptr : ObjRef) : QV (getPte (Z := Unit) ptr) := by
  unfold getPte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPte _)

theorem qv_getPd (ptr : ObjRef) : QV (getPd (Z := Unit) ptr) := by
  unfold getPd; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPd _)

theorem qv_getPde (ptr : ObjRef) : QV (getPde (Z := Unit) ptr) := by
  unfold getPde; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPde _)

theorem qv_getPml4 (ptr : ObjRef) : QV (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPml4 _)

theorem qv_getPml4e (ptr : ObjRef) : QV (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPml4e _)

theorem qv_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : QVE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPdptSlot _ _)

theorem qv_getPdpt (ptr : ObjRef) : QV (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPdpt _)

theorem qv_getPdpte (ptr : ObjRef) : QV (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getPdpte _)

theorem qv_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : QVE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPdSlot _ _)

theorem qv_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : QVE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupPtSlot _ _)

theorem qv_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : QV (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setPdpt _ _)

theorem qv_storePdpte (p : ObjRef) (pte : PDPTE) : QV (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storePdpte _ _)

theorem qv_getAsidPool (ptr : ObjRef) : QV (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getAsidPool _)

theorem qv_findVspaceForAsid (asid : Asid) : QVE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_findVspaceForAsid _)

theorem qv_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : QV (setPt (Z := Unit) ptr pt) := by
  unfold setPt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setPt _ _)

theorem qv_storePte (p : ObjRef) (pte : PTE) : QV (storePte (Z := Unit) p pte) := by
  unfold storePte; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storePte _ _)

theorem qv_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : QV (setPd (Z := Unit) ptr pd) := by
  unfold setPd; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setPd _ _)

theorem qv_storePde (p : ObjRef) (pde : PDE) : QV (storePde (Z := Unit) p pde) := by
  unfold storePde; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storePde _ _)

theorem qv_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : QV (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_unmapPage _ _ _ _)

theorem qv_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : QV (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performPageInvocationUnmap _ _)

theorem qv_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : QV (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setAsidPool _ _)

theorem qv_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : QV (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_flushTable _ _ _ _)

theorem qv_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : QV (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setPml4 _ _)

theorem qv_setOriginal (slot : CslotPtr) (v : Bool) : QV (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setOriginal _ _)

theorem qv_updateCdt (f : Cdt → Cdt) : QV (updateCdt (Z := Unit) f) := by
  unfold updateCdt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_updateCdt _)

theorem qv_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : QV (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setUntypedCapAsFull _ _ _)

theorem qv_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : QV (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_retypeRegion _ _ _ _ _)

theorem qv_storePml4e (p : ObjRef) (pte : PML4E) : QV (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storePml4e _ _)

theorem qv_flushAll (vspace : ObjRef) (asid : Asid) : QV (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_flushAll _ _)

theorem qv_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : QV (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_unmapPdpt _ _ _)

theorem qv_setIoportMask (f l : IoPort) (val : Bool) : QV (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setIoportMask _ _ _)

theorem qv_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : QV (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_invalidatePageStructureCacheAsid _ _)

theorem qv_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : QV (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_unmapPd _ _ _)

theorem qv_deleteObjects (ptr : Word) (bits : Nat) : QV (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_deleteObjects _ _)

theorem qv_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : QV (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_capInsert _ _ _)

theorem qv_portIn (f : MachineMonad Data) : QV (portIn (Z := Unit) f) := by
  unfold portIn; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_portIn _)

theorem qv_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : QV (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_unmapPageTable _ _ _)

theorem qv_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : QV (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_storeAsidPoolEntry _ _ _)

theorem qv_performPageInvocation (iv : PageInvocation) : QV (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performPageInvocation _)

theorem qv_performPageTableInvocation (iv : PageTableInvocation) : QV (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performPageTableInvocation _)

theorem qv_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : QV (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performPageDirectoryInvocation _)

theorem qv_performPdptInvocation (iv : PdptInvocation) : QV (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performPdptInvocation _)

theorem qv_performAsidPoolInvocation (iv : AsidPoolInvocation) : QV (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performAsidPoolInvocation _)

theorem qv_performAsidControlInvocation (iv : AsidControlInvocation) : QV (performAsidControlInvocation (Z := Unit) iv) := by
  unfold performAsidControlInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performAsidControlInvocation _)

theorem qv_performIoPortInvocation (i : IoPortInvocation) : QV (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performIoPortInvocation _)

theorem qv_performIoportControlInvocation (i : IoPortControlInvocation) : QV (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performIoportControlInvocation _)

theorem qv_performDeriveSubframe (iv : Fl4SubframeInvocation) : QV (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performDeriveSubframe _)

theorem qv_performTestAndClearAccessed (_slot : ObjRef) : QV (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_performTestAndClearAccessed _)


theorem qv_performPml4Flush (i : Fl4Pml4Invocation) : QV (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact qv_flushAll _ _

theorem qve_archPerformInvocation (i : ArchInvocation) : QVE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE; cases i <;> qv_auto

/-- **The arch invocations keep the domain schedule.** -/
theorem qve_fl4ArchPerformInvocation (i : Fl4ArchInvocation) : QVE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact qve_archPerformInvocation i
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; qv_auto; exact qv_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; qv_auto
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; qv_auto


theorem qv_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : QV (asUser (Z := Unit) t u) := by
  unfold asUser; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_asUser _ _)

theorem qve_rab (p : Cap × CapRef) : QVE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (qv_getCap _)) fun nc => ?_
        split
        · exact qve_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_rab _)

theorem qv_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, QV (g a b)) :
    ∀ l1 l2, QV (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => qv_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_zipWithMx' (fun _ _ => ?_) _ _)

macro "qv_auto2" : tactic => `(tactic| repeat' (first | qv_leaf | dk_step0 | fv_unfold))

section
set_option maxRecDepth 20000

theorem qve_lookupCapAndSlot (t : ObjRef) (c : CapRef) : QVE (lookupCapAndSlot (Z := Unit) t c) := by
  qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_lookupCapAndSlot _ _)

theorem qv_lookupIpcBuffer (b : Bool) (t : ObjRef) : QV (lookupIpcBuffer (Z := Unit) b t) := by
  qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupIpcBuffer _ _)

theorem qve_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    QVE (lookupExtraCaps (Z := Unit) t b mi) := by
  qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_lookupExtraCaps _ _ _)

theorem qv_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : QV (getMrs (Z := Unit) t b mi) := by
  qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getMrs _ _ _)

theorem qv_getMessageInfo (t : ObjRef) : QV (getMessageInfo (Z := Unit) t) := by
  qv_auto2

theorem qve_decodeIrqControl (r : Bool) (label : Data) (args : List Data) (sl : CslotPtr) (ex : List Cap) :
    QVE (decodeFl4IrqControl (Z := Unit) r label args sl ex) := by
  qv_auto2

theorem qve_decodeIrqHandler (label : Data) (irq : Irq) (ex : List (Cap × CslotPtr)) :
    QVE (decodeIrqHandlerInvocation (Z := Unit) label irq ex) := by
  qv_auto2

theorem qve_decodeUntyped (label : Data) (args : List Data) (sl : CslotPtr) (cap : Cap) (ex : List Cap) :
    QVE (fl4DecodeUntypedInvocation (Z := Unit) label args sl cap ex) := by
  qv_auto2

set_option maxHeartbeats 2000000 in
theorem qve_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    QVE (decodePdptInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePdptInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePdptInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    QVE (decodePageDirectoryInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageDirectoryInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePageDirectoryInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    QVE (decodePageTableInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageTableInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePageTableInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    QVE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePageInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) :
    QVE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePortInvocation _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : ArchCap) (ex : List Cap) :
    QVE (decodeIoportControlInvocation (Z := Unit) label args slot cap ex) := by
  unfold decodeIoportControlInvocation; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeIoportControlInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_decodePml4Flush (cap : ArchCap) :
    QVE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodePml4Flush _)

set_option maxHeartbeats 2000000 in
theorem qve_decodeTestAndClearAccessed (cap : ArchCap) :
    QVE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeTestAndClearAccessed _)

set_option maxHeartbeats 2000000 in
theorem qve_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    QVE (decodeDeriveSubframe (Z := Unit) args cte cap ex) := by
  unfold decodeDeriveSubframe; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeDeriveSubframe _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem qve_archDecodeInvocation (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : QVE (archDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold archDecodeInvocation
  split
  all_goals qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_archDecodeInvocation _ _ _ _ _ _)

theorem qve_archDecode (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : QVE (fl4ArchDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals qv_auto2

macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeIrqControl _ _ _ _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeIrqHandler _ _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_decodeUntyped _ _ _ _ _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_archDecode _ _ _ _ _ _)

set_option maxHeartbeats 2000000 in
/-- **The first-phase decode keeps `fV`.** -/
theorem qve_decodeFirst (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    QVE (fl4DecodeInvocation (Z := Unit) true label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try rw [if_pos rfl]
  all_goals qv_auto2

theorem qve_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : QV m) :
    QVE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qve_withoutPreemption' ?_)
theorem qve_resolveAddressBits (p : Cap × CapRef) : QVE (resolveAddressBits (Z := Unit) p) := qve_rab p
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_resolveAddressBits _)

theorem qv_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : QVE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupSlotForThread' _ _)

theorem qv_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : QVE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupCapAndSlot' _ _)

theorem qv_lookupCap' (thread : ObjRef) (ref : CapRef) : QVE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupCap' _ _)

theorem qv_captransferFromWords' (ptr : Word) : QV (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_captransferFromWords' _)

theorem qv_loadCapTransfer' (buffer : ObjRef) : QV (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_loadCapTransfer' _)

theorem qv_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : QV (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setExtraBadge' _ _ _)

theorem qve_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : QVE m) :
    QVE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qve_lookupErrorOnFailure' _ ?_)

theorem qv_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : QVE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupSlotForCnodeOp' _ _ _ _)

theorem qv_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : QVE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact qv_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupTargetSlot' _ _ _)

theorem qve_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : QVE (f a)) :
    QVE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qve_bind_returnOk' ?_)

theorem qv_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : QV (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_archPostResetUntyped' _ _)

theorem qv_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : QV (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_retypeRegionWith' _ _ _ _ _ _)

theorem qv_copyGlobalMappings' (newPm : ObjRef) : QV (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_copyGlobalMappings' _)

theorem qv_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : QV (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_initArchObjects' _ _ _ _ _ _)

theorem qv_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : QV (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_createCap' _ _ _ _ _)

theorem qv_ensureNoChildren' (cslotPtr : CslotPtr) : QVE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_ensureNoChildren' _)

theorem qv_getRefillTail' (scPtr : ObjRef) : QV (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getRefillTail' _)

theorem qv_getRefills' (scPtr : ObjRef) : QV (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getRefills' _)

theorem qv_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : QV (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_refillAddTail' _ _)

theorem qv_refillFull' (scPtr : ObjRef) : QV (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_refillFull' _)

theorem qv_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : QV (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_updateRefillTl' _ _)

theorem qv_scheduleUsed' (scPtr : ObjRef) (new : Refill) : QV (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_scheduleUsed' _ _)

theorem qv_refillSize' (scPtr : ObjRef) : QV (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_refillSize' _)

theorem qv_refillSingle' (scPtr : ObjRef) : QV (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_refillSingle' _)

theorem qv_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : QV (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_chargeEntireHeadRefill' _ _)

theorem qv_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : QV (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_mergeNonoverlappingHeadRefill' _)

theorem qv_updateIrqState' (irq : Irq) (irqState : X64IRQState) : QV (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_updateIrqState' _ _)

theorem qve_archInvokeIrqControl' (i : ArchIrqControlInvocation) : QVE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_archInvokeIrqControl' _)

theorem qv_invokeIrqControl' (i : IrqControlInvocation) : QVE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_invokeIrqControl' _)

theorem qve_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : QVE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_invokeFl4IrqControl' _)

theorem qve_archDeriveCap' (c : ArchCap) : QVE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_archDeriveCap' _)

theorem qve_deriveCap' (sl : CslotPtr) (c : Cap) : QVE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qve_deriveCap' _ _)

theorem qv_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : QV (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_makeArchFaultMsg' _ _)

theorem qve_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : QVE m) :
    QVE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qve_unifyFailure' ?_)

theorem qv_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : QVE m) :
    QV (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_emptyOnFailure' ?_)

theorem qv_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : QVE m) :
    QV (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qv_constOnFailure' _ ?_)

theorem qve_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : QVE m) :
    QVE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible refine qve_capFaultOnFailure' _ _ ?_)

theorem qv_loadWordOffs' (ptr : ObjRef) (offs : Nat) : QV (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact qv_doMachineOp _
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_loadWordOffs' _ _)

theorem qv_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : QV (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => qv_loadWordOffs' _ _) _)
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getExtraCptrs' _ _)

theorem qv_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : QV (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getReceiveSlots' _ _)

theorem qv_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      QV (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; qv_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := qv_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    qv_auto
    all_goals first | exact ih _ _ | qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_transferCapsLoop' _ _ _ _ _ _)

theorem qv_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : QVE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_lookupExtraCaps' _ _ _)

theorem qv_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : QV (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_copyMrs' _ _ _ _ _)

theorem qv_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : QV (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_transferCaps' _ _ _ _ _)

theorem qv_makeFaultMsg' (f : Fault) (t : ObjRef) : QV (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_makeFaultMsg' _ _)

theorem qv_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : QV (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_handleOverrun' _ _)

theorem qv_headInsufficientLoop' (scPtr : ObjRef) : QV (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_headInsufficientLoop' _)

theorem qv_getMessageInfo' (thread : ObjRef) : QV (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getMessageInfo' _)

theorem qv_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : QV (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_tcbEpAppend' _ _ _)

theorem qv_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : QV (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_doNormalTransfer' _ _ _ _ _ _ _)

theorem qv_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : QV (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_doFaultTransfer' _ _ _ _)

theorem qv_bindScReply' (scPtr replyPtr : ObjRef) : QV (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_bindScReply' _ _)

theorem qv_isValidTimeoutHandler' (tptr : ObjRef) : QV (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_isValidTimeoutHandler' _)

theorem qv_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : QV (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_doIpcTransfer' _ _ _ _ _)


theorem qv_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : QV (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_orderedInsert' _ _ _ _)

theorem qv_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : QV (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; qv_auto
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_readyTimesAppend' _ _)

theorem qv_tcbReleaseEnqueue' (t : ObjRef) : QV (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_tcbReleaseEnqueue' _)

theorem qv_getNtfnObjRef' (f : Notification → Option ObjRef) (n : ObjRef) :
    QV (getNtfnObjRef (Z := Unit) f n) := by
  unfold getNtfnObjRef; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_getNtfnObjRef' _ _)

theorem qv_setReplyObjRef' (f : (Option ObjRef → Option ObjRef) → Reply → Reply) (r : ObjRef) (v : Option ObjRef) :
    QV (setReplyObjRef (Z := Unit) f r v) := by
  unfold setReplyObjRef; qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_setReplyObjRef' _ _ _)

theorem qv_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    QV (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> qv_auto2
macro_rules | `(tactic| qv_leaf) => `(tactic| with_reducible exact qv_handleFaultReply' _ _ _ _)


theorem qve_midF (t : ObjRef) (info : MessageInfo) (cptr : CapRef) : QVE (midF t info cptr) := by
  unfold midF; qv_auto2

theorem qve_midE (t : ObjRef) (info : MessageInfo) (cptr : CapRef) (a) : QVE (midE t info cptr a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold midE
  refine dke_bind (dke_liftE (qv_getMrs _ _ _)) fun _ => qve_decodeFirst _ _ _ _ _ _ _

end

/-! ## `CQ`: `CtRs` and the ready-queue / action fact together -/

/-- `ct` current, runnable without a fault, in no ready queue, no switch to it pending. -/
def CQ (ct : ObjRef) (σ : State Unit) : Prop := CtRs ct σ ∧ PPNQ.NQ ct σ

/-- Every outcome of `m` from a `CQ` state is `CQ`. -/
def PQ (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, CQ ct σ → x ∈ (m σ).1 → CQ ct x.2

section
variable {ct : ObjRef}

theorem qk_of_qv {α : Type} {m : NonDet (State Unit) α} (h : QV m) : PPNQ.QK ct m := by
  intro σ x hx hN
  have e := h σ x hx
  simp only [qV, Prod.mk.injEq] at e
  exact ⟨by rw [e.1]; exact hN.1, by rw [e.2]; exact hN.2⟩

theorem qke_of_qve {ε α : Type} {m : NonDetE (State Unit) ε α} (h : QVE m) : PPNQ.QKE ct m :=
  qk_of_qv h

theorem pq_of {α : Type} {m : NonDet (State Unit) α} (h1 : KF ct m) (h2 : PPNQ.QK ct m) : PQ ct m :=
  fun σ x hs hx => ⟨CtRs.of_ctV (h1 σ x hx) hs.1, h2 σ x hx hs.2⟩

theorem pq_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β}
    (hm : PQ ct m) (hf : ∀ a, PQ ct (f a)) : PQ ct (m >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => hf y.1 y.2 x (hm σ y hs hy) hx

theorem pq_fail_bind {α β : Type} {f : α → NonDet (State Unit) β} : PQ ct (NonDet.fail >>= f) :=
  fun _ _ _ ⟨_, hy, _⟩ => hy.elim

theorem pq_threadGet_bind {α β : Type} (f : Tcb → α) (t : ObjRef) {k : α → NonDet (State Unit) β}
    (hk : ∀ tcb, (t = ct → runnable tcb.tcbState = true ∧ tcb.tcbFault = none) → PQ ct (k (f tcb))) :
    PQ ct (threadGet (Z := Unit) f t >>= k) := by
  intro σ x hs ⟨⟨a, s1⟩, ⟨⟨tcb, s0⟩, h0, h1⟩, hx⟩
  obtain ⟨e0, e0'⟩ := mem_getsThe' h0
  simp only at e0 e0'
  subst e0'
  have h1 := mem_pure' h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hk tcb (fun e => by subst e; exact hs.1.2 tcb (getTcb_some e0)) _ x hs hx

theorem pq_gts_bind {β : Type} (t : ObjRef) {k : ThreadState → NonDet (State Unit) β}
    (hk : ∀ ts, (t = ct → runnable ts = true) → PQ ct (k ts)) :
    PQ ct (getThreadState (Z := Unit) t >>= k) := by
  unfold getThreadState
  exact pq_threadGet_bind _ t fun tcb h => hk _ fun e => (h e).1

theorem pq_pure_bind {α β : Type} {a : α} {f : α → NonDet (State Unit) β} (h : PQ ct (f a)) :
    PQ ct (pure a >>= f) :=
  fun σ x hs ⟨y, hy, hx⟩ => by
    have hy := mem_pure' hy; subst hy; exact h σ x hs hx

end

macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qke_of_qve (qve_rab _))
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact PPNQ.qk_possibleSwitchTo (by assumption))

macro "qk_auto2" : tactic => `(tactic| repeat' (first | qk_leaf | qk_step0 | fv_unfold))

macro_rules | `(tactic| qk_leaf) => `(tactic| exact qk_of_qv (by qv_leaf))
macro_rules | `(tactic| qk_leaf) => `(tactic| exact qke_of_qve (by qv_leaf))

macro "pq_step" : tactic => `(tactic| first
  | exact pq_of (by kf_auto) (by qk_auto)
  | exact pq_of (by kf_auto) (by qk_auto2))


section
variable {c : ObjRef}

theorem qk_postponeQ (sc : ObjRef) : PPNQ.QK c (postpone (Z := Unit) sc) := by
  unfold postpone
  exact PPNQ.qk_bind (PPNQ.qk_getScObjRef' _ _) fun _ => PPNQ.qk_bind (PPNQ.qk_assertOpt _) fun _ =>
    PPNQ.qk_bind (PPNQ.qk_tcbSchedDequeue _) fun _ => PPNQ.qk_bind (qk_of_qv (qv_tcbReleaseEnqueue' _)) fun _ =>
      PPNQ.qk_modify fun _ h => h
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_postponeQ _)

theorem qk_schedContextResumeQ (sc : ObjRef) : PPNQ.QK c (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_schedContextResumeQ _)

theorem qk_maybeDonateScQ (t n : ObjRef) : PPNQ.QK c (maybeDonateSc (Z := Unit) t n) := by
  unfold maybeDonateSc; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_maybeDonateScQ _ _)

theorem qk_replyPushQ (caller callee r : ObjRef) (d : Bool) : PPNQ.QK c (replyPush (Z := Unit) caller callee r d) := by
  unfold replyPush; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_replyPushQ _ _ _ _)

theorem qk_sendIpcBlockedQ (t e : ObjRef) (b : Badge) (g gr call : Bool) :
    PPNQ.QK c (sendIpcBlocked (Z := Unit) t e b g gr call) := by
  unfold sendIpcBlocked; qk_auto
macro_rules | `(tactic| qk_leaf) => `(tactic| with_reducible exact qk_sendIpcBlockedQ _ _ _ _ _ _)

end

section
variable {ct : ObjRef}
set_option maxRecDepth 20000

/-- The receive branch of `send_ipc` (pr_sendIpc_recv with `CQ`). -/
theorem pq_sendIpc_recv (call : Bool) (badge : Badge) (g gr d : Bool) (thread ep dest : ObjRef)
    (hth : thread ≠ ct ∨ call = false) :
    PQ ct (do
      tcbEpDequeue (Z := Unit) dest ep
      let recvState ← getThreadState dest
      let reply ← match recvState with
        | .blockedOnReceive _ reply _data => pure reply
        | _ => NonDet.fail
      doIpcTransfer thread (some ep) badge g dest
      NonDet.maybeM (replyUnlinkTcb dest) reply
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext dest
      let fault ← threadGet Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (g ∨ gr) ∧ reply ≠ none then
          replyPush thread dest (the reply) d
        else
          setThreadState thread .inactive
      else NonDet.when (d ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef Tcb.tcbSchedContext thread
        schedContextDonate (the threadSc) dest
      setThreadState dest .running
      let destSc ← getTcbObjRef Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck destSc
      possibleSwitchTo dest) := by
  refine pq_bind (by pq_step) fun _ => ?_
  refine pq_gts_bind dest fun ts hts => ?_
  cases ts
  case blockedOnReceive e r dt =>
    have hd : dest ≠ ct := fun e => by have := hts e; simp [runnable] at this
    refine pq_bind (pq_of (dk_pure _) (PPNQ.qk_pure _)) fun reply => ?_
    refine pq_bind (by pq_step) fun _ => ?_
    refine pq_bind (by pq_step) fun _ => ?_
    refine pq_bind (by pq_step) fun scOpt => ?_
    refine pq_threadGet_bind _ thread fun tf htf => ?_
    simp only [letFun]
    split
    · next hc =>
      have ht : thread ≠ ct := by
        rcases hth with h | hcall
        · exact h
        · intro e
          have h2 := (htf e).2
          subst hcall
          simp only [h2] at hc
          simp at hc
      pq_step
    · pq_step
  all_goals exact pq_fail_bind

/-- **`send_ipc` keeps `CQ`** from a sender `≠ ct`, or non-blocking and
non-calling from any sender. -/
theorem pq_sendIpc (block call : Bool) (badge : Badge) (g gr d : Bool) (thread ep : ObjRef)
    (hth : thread ≠ ct ∨ (block = false ∧ call = false)) :
    PQ ct (sendIpc (Z := Unit) block call badge g gr d thread ep) := by
  unfold sendIpc
  refine pq_bind (by pq_step) fun e => ?_
  have hr : thread ≠ ct ∨ call = false := hth.imp_right (·.2)
  cases e with
  | idleEP =>
    cases block
    · exact pq_of (dk_pure _) (PPNQ.qk_pure _)
    · exact pq_of (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp))) (qk_sendIpcBlockedQ _ _ _ _ _ _)
  | sendEP q =>
    cases block
    · exact pq_of (dk_pure _) (PPNQ.qk_pure _)
    · exact pq_of (kf_sendIpcBlocked' _ _ _ _ _ _ (hth.resolve_right (by simp))) (qk_sendIpcBlockedQ _ _ _ _ _ _)
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact fun _ _ _ hx => hx.elim
    | cons dest q => cases block <;> exact pq_sendIpc_recv call badge g gr d thread ep dest hr

theorem pq_sendFaultIpc (tptr : ObjRef) (hc : Cap) (f : Fault) (d : Bool) (ht : tptr ≠ ct) :
    PQ ct (sendFaultIpc (Z := Unit) tptr hc f d) := by
  unfold sendFaultIpc
  split
  · refine pq_bind (pq_of (kf_threadSet_ne _ _ ht) (PPNQ.qk_threadSet' _ _)) fun _ => ?_
    exact pq_bind (pq_sendIpc _ _ _ _ _ _ _ _ (Or.inl ht)) fun _ => pq_of (dk_pure _) (PPNQ.qk_pure _)
  · exact pq_of (dk_pure _) (PPNQ.qk_pure _)
  · exact fun _ _ _ hx => hx.elim

theorem pq_handleTimeout (tptr : ObjRef) (ex : Fault) (ht : tptr ≠ ct) :
    PQ ct (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout
  refine pq_bind (by pq_step) fun _ => ?_
  refine pq_bind (by pq_step) fun _ => ?_
  refine pq_bind (pq_of (dk_pure _) (PPNQ.qk_pure _)) fun _ => ?_
  refine pq_bind (by pq_step) fun _ => ?_
  exact pq_bind (pq_sendFaultIpc _ _ _ _ ht) fun _ => pq_of (dk_pure _) (PPNQ.qk_pure _)

/-- The tail of `do_reply_transfer` (the receiver `≠ ct` woken or charged). -/
theorem pq_drt_tail (receiver : ObjRef) (hd : receiver ≠ ct) (fault : Option Fault) :
    PQ ct (do
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
      let state ← getThreadState receiver
      NonDet.when (scOpt ≠ none ∧ runnable state) <| do
        let scPtr ← NonDet.assertOpt scOpt
        let sc ← getSchedContext scPtr
        let curtime ← NonDet.gets fun s : State Unit => s.curTime
        if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
        then possibleSwitchTo receiver
        else do
          let tcb ← NonDet.getsThe (getTcb receiver)
          if isEpCap tcb.tcbTimeoutHandler ∧
             ¬(fault.elim false isTimeoutFault = true)
          then handleTimeout receiver (.timeout sc.scBadge)
          else postpone scPtr) := by
  refine pq_bind (by pq_step) fun _ => ?_
  refine pq_bind (by pq_step) fun _ => ?_
  unfold NonDet.when
  split
  · refine pq_bind (by pq_step) fun _ => ?_
    refine pq_bind (by pq_step) fun _ => ?_
    refine pq_bind (by pq_step) fun _ => ?_
    split
    · pq_step
    · refine pq_bind (by pq_step) fun _ => ?_
      split
      · exact pq_handleTimeout _ _ hd
      · pq_step
  · exact pq_of (dk_pure' _) (PPNQ.qk_pure' _)

/-- **`do_reply_transfer` keeps `CQ`**: the receiver is `BlockedOnReply`. -/
theorem pq_doReplyTransfer (sender reply : ObjRef) (grant : Bool) :
    PQ ct (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine pq_bind (by pq_step) fun recvOpt => ?_
  cases recvOpt with
  | none => exact pq_of (dk_pure' _) (PPNQ.qk_pure' _)
  | some receiver =>
    refine pq_gts_bind receiver fun ts hts => ?_
    cases ts
    case blockedOnReply r =>
      have hd : receiver ≠ ct := fun e => by have := hts e; simp [runnable] at this
      refine pq_bind (by pq_step) fun _ => ?_
      refine pq_bind (by pq_step) fun _ => ?_
      refine pq_bind (by pq_step) fun _ => ?_
      refine pq_bind (by pq_step) fun _ => ?_
      refine pq_bind (by pq_step) fun fault => ?_
      simp only [letFun]
      split
      all_goals repeat (first
        | exact pq_drt_tail receiver hd _
        | refine pq_bind (by pq_step) fun _ => ?_)
    all_goals exact pq_of (dk_pure _) (PPNQ.qk_pure _)

set_option maxHeartbeats 2000000 in
/-- **`send_signal` keeps `CQ`**, from a state where `ct` waits on no
notification (`NQ`). -/
theorem pq_sendSignal (n : ObjRef) (b : Badge) :
    ∀ σ x, CQ ct σ → NQ ct σ → x ∈ (sendSignal (Z := Unit) n b σ).1 → CQ ct x.2 := by
  intro σ x hs hq hx
  unfold sendSignal at hx
  obtain ⟨⟨nt, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := getSimpleKo_mem h1
  simp only at e1 hk
  subst e1
  rcases hno : nt.ntfnObj with _ | q | b' <;> rcases hbt : nt.ntfnBoundTcb with _ | tcb <;>
    simp only [hno, hbt] at hx
  · exact (pq_of (kf_setSimpleKo _ _ _) (PPNQ.qk_setSimpleKo' _ _ _)) _ x hs hx
  · refine (pq_gts_bind tcb fun ts hts => ?_) _ x hs hx
    split
    · next hrb =>
      have hd : tcb ≠ ct := fun e => by
        have := hts e; cases ts <;> simp_all [runnable, receiveBlocked]
      pq_step
    · pq_step
  all_goals try exact (pq_of (kf_setSimpleKo _ _ _) (PPNQ.qk_setSimpleKo' _ _ _)) _ x hs hx
  all_goals
    have hq' : ct ∉ q := hq n nt q hk hno
    unfold updateWaitingNtfn at hx
    refine (?_ : PQ ct _) _ x hs hx
    by_cases hqe : q = []
    · subst hqe; exact fun _ _ _ ⟨y, hy, _⟩ => absurd rfl hy.1
    · have hd : the q.head? ≠ ct := fun e => hq' (e ▸ the_head_mem hqe)
      refine pq_bind (by pq_step) fun _ => ?_
      refine pq_pure_bind ?_
      pq_step

end

section
variable {ct : ObjRef}

theorem pq_setThreadState_run (t : ObjRef) (ts : ThreadState) (hr : runnable ts = true) :
    PQ ct (setThreadState (Z := Unit) t ts) :=
  fun σ x hs hx => ⟨pr_setThreadState_run t ts hr σ x hs.1 hx, PPNQ.qk_setThreadState' t ts σ x hx hs.2⟩

theorem pq_post {α : Type} {m : NonDet (State Unit) α} (h : PQ ct m) {σ : State Unit} (hs : CQ ct σ) :
    ∀ y ∈ (m σ).1, CQ ct y.2 :=
  fun y hy => h σ y hs hy

theorem pqe_post {ε α : Type} {m : NonDetE (State Unit) ε α} (h1 : KFE ct m) (h2 : QVE m) {σ : State Unit}
    (hs : CQ ct σ) : ∀ y ∈ (m.run σ).1, CQ ct y.2 :=
  fun y hy => ⟨CtRs.of_ctV (h1 σ y hy) hs.1, qk_of_qv h2 σ y hy hs.2⟩

/-- `CQ ∧ NQ` across an `fV`- and `qV`-frame. -/
theorem fq_I {α : Type} {m : NonDet (State Unit) α} (h1 : FV ct m) (h2 : QV m) {σ : State Unit}
    (hI : CQ ct σ ∧ NQ ct σ) : ∀ x ∈ (m σ).1, CQ ct x.2 ∧ NQ ct x.2 := by
  intro x hx
  obtain ⟨a, b⟩ := fv_I h1 ⟨hI.1.1, hI.2⟩ x hx
  exact ⟨⟨a, qk_of_qv h2 σ x hx hI.1.2⟩, b⟩

set_option maxRecDepth 20000 in
/-- **The perform of a first-phase invocation but `PerfW` keeps `CQ`** from
`CQ ∧ NQ` (module docstring). -/
theorem perf_firstQ (don : Bool) (inv : Fl4Invocation) (hf : FirstInv inv) (hw : ¬ PerfW inv) {σ : State Unit}
    (hs : CQ ct σ) (hq : NQ ct σ) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ).1, CQ ct y.2 := by
  cases inv with
  | invokeUntyped i => exact absurd trivial hw
  | invokeEndpoint ep badge g gr =>
    simp only [fl4PerformInvocation, withoutPreemption]
    exact post_liftE (pq_post (pq_bind (pq_of (dk_gets _) (PPNQ.qk_gets _)) fun thread =>
      pq_bind (pq_sendIpc false false badge g gr don thread ep (Or.inr ⟨rfl, rfl⟩)) fun _ =>
        pq_of (dk_pure _) (PPNQ.qk_pure _)) hs)
  | invokeNotification ep badge =>
    simp only [fl4PerformInvocation, withoutPreemption]
    have h1 := post_liftE (ε := Unit) (fun x hx => pq_sendSignal ep badge σ x hs hq hx)
    refine post_bindE (R := CQ ct) h1 (fun _ h => h) fun _ s' hm y hy => ?_
    rw [NonDetE.returnOk, ExceptT.run_pure] at hy
    rw [Set.mem_singleton_iff.1 hy]
    exact h1 _ hm
  | invokeReply reply grant =>
    simp only [fl4PerformInvocation]
    exact post_liftE (pq_post (pq_bind (pq_of (dk_gets _) (PPNQ.qk_gets _)) fun sender =>
      pq_bind (pq_doReplyTransfer sender reply grant) fun _ => pq_of (dk_pure _) (PPNQ.qk_pure _)) hs)
  | invokeIRQControl i =>
    simp only [fl4PerformInvocation]
    exact pqe_post (by kf_auto) (by qv_auto2) hs
  | invokeIRQHandler i =>
    cases i with
    | aCKIrq irq =>
      simp only [fl4PerformInvocation, invokeIrqHandler]
      exact pqe_post (by kf_auto) (by qv_auto2) hs
    | _ => exact absurd trivial hw
  | invokeArchObject i =>
    cases i with
    | spec i =>
      cases i with
      | invokeASIDControl _ => exact absurd trivial hw
      | _ =>
        simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation]
        exact pqe_post (by kf_auto) (by qv_auto2) hs
    | _ =>
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation]
      exact pqe_post (by kf_auto) (by qv_auto2) hs
  | _ => exact absurd hf id

end

/-- **[W] `JMidPerfHyp` with `CQ`** (module docstring): the Untyped, IRQ
handler set / clear and ASID control performs keep the current thread
runnable without a fault, out of the ready queues and not the target of a
pending switch, at the states where they start on a run of ReplyRecv /
NBSendRecv / NBSendWait's invocation from the entry state `σ` (`MidPerfAt`).
l4v `perform_invocation_not_blocking_not_calling_ct_active` with
`ct_not_in_q` / `scheduler_act_sane` (valid_sched) for these cases:
invoke_untyped and perform_asid_control_invocation write no queue and no
action (retype of a free region); invoke_irq_handler's `cap_delete_one`
restarts (enqueues, switches to) only `BlockedOnNotification` threads, not
`ct`, which is `Restart`. -/
def JMidPerfHypQ (don : Bool) (cptr : CapRef) (σ : State Unit) : Prop :=
  ∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv →
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) false false don inv).run σ1).1, CQ σ.curThread y.2

theorem JMidPerfHypQ.toP {don : Bool} {cptr : CapRef} {σ : State Unit} (h : JMidPerfHypQ don cptr σ) :
    JMidPerfHyp don cptr σ :=
  fun inv σ1 hA hW y hy => (h inv σ1 hA hW y hy).1

set_option maxHeartbeats 1000000 in
/-- **The shell with `CQ`**: from `CQ ∧ NQ` at the entry, every outcome of
the first-phase non-blocking non-calling invocation is `CQ`. -/
theorem midRunQ_shell (rep don : Bool) (cptr : CapRef) (σ : State Unit) (hs : CQ σ.curThread σ)
    (hq : NQ σ.curThread σ) (hW : JMidPerfHypQ don cptr σ) :
    ∀ y ∈ ((fl4HandleInvocationR (Z := Unit) rep false false don true cptr).run σ).1, CQ σ.curThread y.2 := by
  intro y hy
  unfold fl4HandleInvocationR at hy
  obtain ⟨z, hz, ⟨t, ht, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
  obtain rfl : w = (σ.curThread, σ) := hw
  simp only [Except.ok.injEq] at ht
  subst ht
  obtain ⟨z, hz, ⟨info, hi, hy⟩ | ⟨e, he, -⟩⟩ := mem_bindE_inv' hy
  swap
  · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  obtain ⟨⟨info', σa⟩, hia, rfl⟩ := mem_liftE_inv' hz
  simp only [Except.ok.injEq] at hi
  subst hi
  have hIa := fq_I (fv_getMessageInfo (ct := σ.curThread) _) (qv_getMessageInfo' _) ⟨hs, hq⟩ _ hia
  refine syscall_post (mF := midF σ.curThread info' cptr) (mE := midE σ.curThread info' cptr)
    (I := fun s => CQ σ.curThread s ∧ NQ σ.curThread s) (Q := CQ σ.curThread)
    (fun w hw => fq_I (fve_midF _ _ _) (qve_midF _ _ _) hIa w hw) ?_
    (fun a s has w hw => fq_I (fve_midE _ _ _ a) (qve_midE _ _ _ a)
      (fq_I (fve_midF _ _ _) (qve_midF _ _ _) hIa _ has) w hw) ?_ ?_ y hy
  · intro f s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact hI.1
  · intro e s hI v hv
    simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte] at hv
    obtain rfl : v = ((), s) := hv
    exact hI.1
  · intro a s b s' has hbs hI y hy
    have hFI : FirstInv b := okAll_midE _ _ _ a s _ hbs b rfl
    refine post_bindE (R := fun s => CQ σ.curThread s ∧ NQ σ.curThread s) ?_ (fun _ h => h.1) ?_ y hy
    · unfold withoutPreemption
      exact post_liftE (Q := fun s => CQ σ.curThread s ∧ NQ σ.curThread s) fun x hx =>
        ⟨pq_setThreadState_run _ _ rfl s' x hI.1 hx, NQ.of_nV (nv_setThreadState _ _ s' x hx) hI.2⟩
    intro u s1 h1 y hy
    obtain ⟨⟨u', s1'⟩, h1', e1⟩ := mem_liftE_inv' h1
    simp only [Prod.mk.injEq] at e1
    obtain ⟨-, rfl⟩ := e1
    have hI1 : CQ σ.curThread s1 ∧ NQ σ.curThread s1 :=
      ⟨pq_setThreadState_run _ _ rfl s' _ hI.1 h1', NQ.of_nV (nv_setThreadState _ _ s' _ h1') hI.2⟩
    refine post_bindE (R := CQ σ.curThread) ?_ (fun _ h => h) ?_ y hy
    · by_cases hw : PerfW b
      · exact hW b s1 ⟨info', σa, a, s, s', hia, has, hbs, h1'⟩ hw
      · exact perf_firstQ don b hFI hw hI1.1 hI1.2
    intro r s2 h2 y hy
    have hs2 : CQ σ.curThread s2 := by
      by_cases hw : PerfW b
      · exact hW b s1 ⟨info', σa, a, s, s', hia, has, hbs, h1'⟩ hw (.ok r, s2) h2
      · exact perf_firstQ don b hFI hw hI1.1 hI1.2 (.ok r, s2) h2
    unfold withoutPreemption at hy
    refine post_liftE (pq_post ?_ hs2) y hy
    refine pq_gts_bind _ fun ts _ => ?_
    split
    · refine pq_bind (pq_of (dk_pure _) (PPNQ.qk_pure _)) fun _ => ?_
      exact pq_setThreadState_run _ _ rfl
    · exact pq_of (dk_pure _) (PPNQ.qk_pure _)

end

end Fl4Proofs.P3.MidRun
