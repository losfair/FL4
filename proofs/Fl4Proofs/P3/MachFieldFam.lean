/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr2): **the spec steps keep the
machine fields `MR` reads and the interrupt table** (spec side only; `MFK`).

* `msF σ`: the IRQ masks, the IRQ and clock oracle positions, the last machine
  time (the four fields XTopJointMachRel's `MachPlat.frame` says `MR` reads)
  and the interrupt table (for `ValidIrqMasks`). `MFK m := FK msF m`
  (VsDom's generic projection frame: VsDom's combinators and `dk_step0`
  apply).
* Machine-operation leaves: `MKF mop` (the four machine fields kept);
  `loadWord`, `storeWord`, `machineOpLift` (the machine's opaque rest), so
  `doMachineOp` of each keeps `msF` (`mfk_doMachineOp`). `getCurrentTime`,
  `getActiveIRQ` and `maskInterrupt` do not (the preemption point, the IRQ
  take, IRQ control and IRQ handler deletion move `MR` by `MachPlat`), nor
  does setting an IRQ's state.
* The rest: one lemma per spec function, bottom-up by `mfk_auto`, mirroring
  VsDomOps / DomRecDel / TcbDom / AllDom's `DK` lemmas (generated:
  scratch/mr2/mfgen.py; the DK lemmas whose function reaches one of the
  operations above are left out, as are their dependents).
-/
import Fl4Proofs.P3.AllDom

open Classical

namespace Fl4Proofs.P3.MachF
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The machine fields `MR` reads and the interrupt table. -/
def msF (σ : State Unit) :=
  (σ.machineState.irqMasks, σ.machineState.irqState, σ.machineState.timeState,
    σ.machineState.lastMachineTime, σ.interruptStates)

/-- Every outcome of `m` keeps `msF`. -/
abbrev MFK {α : Type} (m : NonDet (State Unit) α) : Prop := FK msF m

/-- `MFK` for the exception monad. -/
abbrev MFKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE msF m

/-- The four machine fields. -/
def mF (ms : MachineState) := (ms.irqMasks, ms.irqState, ms.timeState, ms.lastMachineTime)

/-- A machine operation keeping the four machine fields. -/
def MKF {α : Type} (m : NonDet MachineState α) : Prop := ∀ ms x, x ∈ (m ms).1 → mF x.2 = mF ms

section MKF

theorem mkf_bind {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MKF m)
    (hg : ∀ a, MKF (g a)) : MKF (m >>= g) := by
  intro ms x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm ms y hy)

theorem mkf_pure {α : Type} (a : α) : MKF (pure a : NonDet MachineState α) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mkf_gets {α : Type} (g : MachineState → α) : MKF (NonDet.gets g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mkf_assert (P : Prop) : MKF (NonDet.assert P : NonDet MachineState Unit) := by
  intro ms x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem mkf_selectF {α : Type} (S : Set α × Prop) : MKF (NonDet.selectF S : NonDet MachineState α) := by
  intro ms x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem mkf_modify {g : MachineState → MachineState} (hg : ∀ ms, mF (g ms) = mF ms) :
    MKF (NonDet.modify g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg ms

theorem mkf_loadWord (p : Word) : MKF (loadWord p) := by
  unfold loadWord
  exact mkf_bind (mkf_gets _) fun _ => mkf_bind (mkf_assert _) fun _ => mkf_pure _

theorem mkf_storeWord (p w : Word) : MKF (storeWord p w) := by
  unfold storeWord
  exact mkf_bind (mkf_assert _) fun _ => mkf_modify fun _ => rfl

theorem mkf_machineOpLift (f : MachineRestMonad Unit) : MKF (machineOpLift f) := by
  unfold machineOpLift machineRestLift
  exact mkf_bind (mkf_gets _) fun _ => mkf_bind (mkf_selectF _) fun _ => mkf_bind (mkf_modify fun _ => rfl)
    fun _ => mkf_pure _

end MKF

theorem mfk_doMachineOp {α : Type} {mop : NonDet MachineState α} (hm : MKF mop) :
    MFK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨hm2, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  have e := hm _ _ hm2
  simp only [mF, Prod.mk.injEq] at e
  simp only [msF, e]

/-- A `MFK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "mfk_leaf" : tactic
macro_rules | `(tactic| mfk_leaf) => `(tactic| fail "no mfk_leaf")
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doMachineOp (mkf_loadWord _))
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doMachineOp (mkf_storeWord _ _))
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doMachineOp (mkf_machineOpLift _))

macro "mfk_auto" : tactic => `(tactic| repeat' (first | mfk_leaf | dk_step0))

theorem mfk_doExtendedOp (eop : DetExtMonad Unit) : MFK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doExtendedOp _)

theorem mfk_setObject (p : ObjRef) (o : KernelObject) : MFK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setObject _ _)

theorem mfk_setCap (c : Cap) (sl : CslotPtr) : MFK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setCap _ _)

theorem mfk_getCap (sl : CslotPtr) : MFK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getCap _)

theorem mfk_getPt (ptr : ObjRef) : MFK (getPt (Z := Unit) ptr) := by
  unfold getPt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPt _)

theorem mfk_getPte (ptr : ObjRef) : MFK (getPte (Z := Unit) ptr) := by
  unfold getPte; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPte _)

theorem mfk_getPd (ptr : ObjRef) : MFK (getPd (Z := Unit) ptr) := by
  unfold getPd; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPd _)

theorem mfk_getPde (ptr : ObjRef) : MFK (getPde (Z := Unit) ptr) := by
  unfold getPde; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPde _)

theorem mfk_getPml4 (ptr : ObjRef) : MFK (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPml4 _)

theorem mfk_getPml4e (ptr : ObjRef) : MFK (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPml4e _)

theorem mfk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : MFKE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupPdptSlot _ _)

theorem mfk_getPdpt (ptr : ObjRef) : MFK (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPdpt _)

theorem mfk_getPdpte (ptr : ObjRef) : MFK (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getPdpte _)

theorem mfk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : MFKE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupPdSlot _ _)

theorem mfk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : MFKE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupPtSlot _ _)

theorem mfk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : MFK (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setPdpt _ _)

theorem mfk_storePdpte (p : ObjRef) (pte : PDPTE) : MFK (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storePdpte _ _)

theorem mfk_getAsidPool (ptr : ObjRef) : MFK (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getAsidPool _)

theorem mfk_findVspaceForAsid (asid : Asid) : MFKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_findVspaceForAsid _)

theorem mfk_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : MFK (setPt (Z := Unit) ptr pt) := by
  unfold setPt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setPt _ _)

theorem mfk_storePte (p : ObjRef) (pte : PTE) : MFK (storePte (Z := Unit) p pte) := by
  unfold storePte; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storePte _ _)

theorem mfk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : MFK (setPd (Z := Unit) ptr pd) := by
  unfold setPd; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setPd _ _)

theorem mfk_storePde (p : ObjRef) (pde : PDE) : MFK (storePde (Z := Unit) p pde) := by
  unfold storePde; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storePde _ _)

theorem mfk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : MFK (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setAsidPool _ _)

theorem mfk_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : MFK (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setPml4 _ _)

theorem mfk_setOriginal (slot : CslotPtr) (v : Bool) : MFK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setOriginal _ _)

theorem mfk_updateCdt (f : Cdt → Cdt) : MFK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateCdt _)

theorem mfk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : MFK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setUntypedCapAsFull _ _ _)

theorem mfk_retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : MFK (retypeRegion (Z := Unit) ptr numObjects oBits type dev) := by
  unfold retypeRegion; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_retypeRegion _ _ _ _ _)

theorem mfk_storePml4e (p : ObjRef) (pte : PML4E) : MFK (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storePml4e _ _)

theorem mfk_setIoportMask (f l : IoPort) (val : Bool) : MFK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setIoportMask _ _ _)

theorem mfk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : MFK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_capInsert _ _ _)

theorem mfk_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : MFK (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storeAsidPoolEntry _ _ _)

theorem mfk_performAsidPoolInvocation (iv : AsidPoolInvocation) : MFK (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_performAsidPoolInvocation _)

theorem mfk_performIoportControlInvocation (i : IoPortControlInvocation) : MFK (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_performIoportControlInvocation _)

theorem mfk_performDeriveSubframe (iv : Fl4SubframeInvocation) : MFK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_performDeriveSubframe _)

theorem mfk_performTestAndClearAccessed (_slot : ObjRef) : MFK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_performTestAndClearAccessed _)

theorem mfk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : MFK (threadSet (Z := Unit) f t) := by
  unfold threadSet; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_threadSet' _ _)

theorem mfk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : MFK (threadGet (Z := Unit) f t) := by
  unfold threadGet; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_threadGet' _ _)

theorem mfk_setThreadState' (t : ObjRef) (ts : ThreadState) : MFK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setThreadState' _ _)

theorem mfk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    MFK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getSimpleKo' _ _)

theorem mfk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    MFK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setSimpleKo' _ _ _)

theorem mfk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    MFK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateSkObjRef' _ _ _ _)

theorem mfk_getSchedContext' (q : ObjRef) : MFK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getSchedContext' _)

theorem mfk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    MFK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateSchedContext' _ _)

theorem mfk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : MFK (asUser (Z := Unit) t u) := by
  unfold asUser; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_asUser' _ _)

theorem mfk_replyUnlinkTcb' (t r : ObjRef) : MFK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_replyUnlinkTcb' _ _)

theorem mfk_getThreadState' (t : ObjRef) : MFK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getThreadState' _)

theorem mfk_cancelIpc' (t : ObjRef) : MFK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_cancelIpc' _)

theorem mfk_suspend' (t : ObjRef) : MFK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_suspend' _)

theorem mfk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : MFK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getSkObjRef' _ _ _)

theorem mfk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : MFK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getScObjRef' _ _)

theorem mfk_getIrqSlot' (irq : Irq) : MFK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getIrqSlot' _)

theorem mfk_isFinalCap' (c : Cap) : MFK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_isFinalCap' _)

theorem mfk_getCurrentCr3' : MFK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getCurrentCr3' )

theorem mfk_setCurrentCr3' (c : Cr3) : MFK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setCurrentCr3' _)

theorem mfk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : MFK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setCurrentVspaceRoot' _ _)

theorem mfk_setVmRoot' (t : ObjRef) : MFK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setVmRoot' _)

theorem mfk_freeIoportRange' (f l : IoPort) : MFK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_freeIoportRange' _ _)

theorem mfk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : MFK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupIpcBuffer' _ _)

theorem mfk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, MFK (g a b)) :
    ∀ l1 l2, MFK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => mfk_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfk_zipWithMx' (fun _ _ => ?_) _ _)

theorem mfk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : MFK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_storeWordOffs' _ _ _)

theorem mfk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : MFK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setMrs' _ _ _)

theorem mfk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : MFK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setMessageInfo' _ _)

theorem mfk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : MFK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_archThreadSet' _ _)

theorem mfk_setX64CurrentFpuOwner' (o : Option ObjRef) : MFK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setX64CurrentFpuOwner' _)

theorem mfk_getTcbQueue' (d : Domain) (p : Priority) : MFK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getTcbQueue' _ _)

theorem mfk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : MFK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setTcbQueue' _ _ _)

theorem mfk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : MFK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbSchedAction' _ _)

theorem mfk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : MFK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getTcbObjRef' _ _)

theorem mfk_setSchedulerAction' (a : SchedulerAction) : MFK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setSchedulerAction' _)

theorem mfk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : MFK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getScRefillSufficient' _ _)

theorem mfk_getScRefillReady' (sc : ObjRef) : MFK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getScRefillReady' _)

theorem mfk_tcbReleaseRemove' (t : ObjRef) : MFK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbReleaseRemove' _)

theorem mfk_rescheduleRequired' : MFK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_rescheduleRequired' )

theorem mfk_testReschedule' (t : ObjRef) : MFK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_testReschedule' _)

theorem mfk_possibleSwitchTo' (t : ObjRef) : MFK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_possibleSwitchTo' _)

theorem mfk_tcbEpDequeue' (t e : ObjRef) : MFK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbEpDequeue' _ _)

theorem mfk_tcbNtfnDequeue' (t n : ObjRef) : MFK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbNtfnDequeue' _ _)

theorem mfk_isRoundRobin' (sc : ObjRef) : MFK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_isRoundRobin' _)

theorem mfk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : MFK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateRefillHd' _ _)

theorem mfk_getRefillHead' (sc : ObjRef) : MFK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getRefillHead' _)

theorem mfk_refillPopHead' (sc : ObjRef) : MFK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillPopHead' _)

theorem mfk_mergeOverlappingRefills' (sc : ObjRef) : MFK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_mergeOverlappingRefills' _)

theorem mfk_refillHeadOverlappingLoop' (sc : ObjRef) : MFK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillHeadOverlappingLoop' _)

theorem mfk_refillUnblockCheck' (sc : ObjRef) : MFK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillUnblockCheck' _)

theorem mfk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : MFK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_ifCondRefillUnblockCheck' _ _ _)

theorem mfk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : MFK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem mfk_restartThreadIfNoFault' (t : ObjRef) : MFK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_restartThreadIfNoFault' _)

theorem mfk_removeAndRestartEpQueuedThread' (t e : ObjRef) : MFK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_removeAndRestartEpQueuedThread' _ _)

theorem mfk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : MFK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_removeAndRestartNtfnQueuedThread' _ _)

theorem mfk_replyUnlinkSc' (sc r : ObjRef) : MFK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_replyUnlinkSc' _ _)

theorem mfk_schedContextDonate' (sc t : ObjRef) : MFK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextDonate' _ _)

theorem mfk_schedContextUpdateConsumed' (sc : ObjRef) : MFK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUpdateConsumed' _)

theorem mfk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : MFK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_replyFromKernel' _ _)

theorem mfk_setConsumed' (sc t : ObjRef) : MFK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setConsumed' _ _)

theorem mfk_schedContextCancelYieldTo' (t : ObjRef) : MFK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextCancelYieldTo' _)

theorem mfk_archPostCapDeletion' (c : ArchCap) : MFK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_archPostCapDeletion' _)

theorem mfk_cancelAllIpc' (e : ObjRef) : MFK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_cancelAllIpc' _)

theorem mfk_schedContextMaybeUnbindNtfn' (n : ObjRef) : MFK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextMaybeUnbindNtfn' _)

theorem mfk_unbindMaybeNotification' (n : ObjRef) : MFK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_unbindMaybeNotification' _)

theorem mfk_cancelAllSignals' (n : ObjRef) : MFK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_cancelAllSignals' _)

theorem mfk_replyRemove' (t r : ObjRef) : MFK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_replyRemove' _ _)

theorem mfk_unbindNotification' (t : ObjRef) : MFK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_unbindNotification' _)

theorem mfk_schedContextUnbindTcb' (sc : ObjRef) : MFK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUnbindTcb' _)

theorem mfk_completeYieldTo' (t : ObjRef) : MFK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_completeYieldTo' _)

theorem mfk_unbindFromSc' (t : ObjRef) : MFK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_unbindFromSc' _)

theorem mfk_schedContextUnbindAllTcbs' (sc : ObjRef) : MFK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUnbindAllTcbs' _)

theorem mfk_schedContextUnbindNtfn' (sc : ObjRef) : MFK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUnbindNtfn' _)

theorem mfk_schedContextUnbindReply' (sc : ObjRef) : MFK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUnbindReply' _)

theorem mfk_schedContextUnbindYieldFrom' (sc : ObjRef) : MFK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextUnbindYieldFrom' _)

theorem mfk_schedContextSetInactive' (sc : ObjRef) : MFK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextSetInactive' _)

theorem mfk_fastFinalise' (c : Cap) (b : Bool) : MFK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_fastFinalise' _ _)

theorem mfk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : MFK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_capSwap' _ _ _ _)

theorem mfk_capSwapForDelete' (s1 s2 : CslotPtr) : MFK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_capSwapForDelete' _ _)

theorem mfk_capMove' (c : Cap) (s1 s2 : CslotPtr) : MFK (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_capMove' _ _ _)

theorem mfk_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    MFK (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_removeAndRestartBadgedThread' _ _ _)

theorem mfk_cancelBadgedSends' (e : ObjRef) (b : Badge) : MFK (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_cancelBadgedSends' _ _)

theorem mfk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : MFK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_orderedInsert' _ _ _ _)

theorem mfk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : MFK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_readyTimesAppend' _ _)

theorem mfk_tcbReleaseEnqueue' (t : ObjRef) : MFK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbReleaseEnqueue' _)

theorem mfk_tcbAppend' (t : ObjRef) (q : List ObjRef) : MFK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbAppend' _ _)

theorem mfk_postpone' (sc : ObjRef) : MFK (postpone (Z := Unit) sc) := by
  unfold postpone; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_postpone' _)

theorem mfk_threadSetPriority' (t : ObjRef) (p : Priority) : MFK (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_threadSetPriority' _ _)

theorem mfk_reorderEp' (e t : ObjRef) : MFK (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_reorderEp' _ _)

theorem mfk_reorderNtfn' (n t : ObjRef) : MFK (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_reorderNtfn' _ _)

theorem mfk_archPostModifyRegisters' (c t : ObjRef) : MFK (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_archPostModifyRegisters' _ _)

theorem mfk_schedContextResume' (sc : ObjRef) : MFK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextResume' _)

theorem mfk_testPossibleSwitchTo' (t : ObjRef) : MFK (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_testPossibleSwitchTo' _)

theorem mfk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : MFK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem mfke_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : MFK m) :
    MFKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfke_withoutPreemption' ?_)

theorem mfke_rab (p : Cap × CapRef) : MFKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (mfk_getCap _)) fun nc => ?_
        split
        · exact mfke_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfke_rab _)

theorem mfke_resolveAddressBits (p : Cap × CapRef) : MFKE (resolveAddressBits (Z := Unit) p) := mfke_rab p
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfke_resolveAddressBits _)

theorem mfk_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : MFKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupSlotForThread' _ _)

theorem mfk_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : MFKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupCapAndSlot' _ _)

theorem mfk_lookupCap' (thread : ObjRef) (ref : CapRef) : MFKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupCap' _ _)

theorem mfk_captransferFromWords' (ptr : Word) : MFK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_captransferFromWords' _)

theorem mfk_loadCapTransfer' (buffer : ObjRef) : MFK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_loadCapTransfer' _)

theorem mfk_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : MFK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_setExtraBadge' _ _ _)

theorem mfke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : MFKE m) :
    MFKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfke_lookupErrorOnFailure' _ ?_)

theorem mfk_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : MFKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupSlotForCnodeOp' _ _ _ _)

theorem mfk_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : MFKE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact mfk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupTargetSlot' _ _ _)

theorem mfke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : MFKE (f a)) :
    MFKE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfke_bind_returnOk' ?_)

theorem mfk_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : MFK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_archPostResetUntyped' _ _)

theorem mfk_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : MFK (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_retypeRegionWith' _ _ _ _ _ _)

theorem mfk_copyGlobalMappings' (newPm : ObjRef) : MFK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_copyGlobalMappings' _)

theorem mfk_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : MFK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_initArchObjects' _ _ _ _ _ _)

theorem mfk_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : MFK (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_createCap' _ _ _ _ _)

theorem mfk_ensureNoChildren' (cslotPtr : CslotPtr) : MFKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_ensureNoChildren' _)

theorem mfk_getRefillTail' (scPtr : ObjRef) : MFK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getRefillTail' _)

theorem mfk_getRefills' (scPtr : ObjRef) : MFK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getRefills' _)

theorem mfk_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : MFK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillAddTail' _ _)

theorem mfk_refillFull' (scPtr : ObjRef) : MFK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillFull' _)

theorem mfk_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : MFK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateRefillTl' _ _)

theorem mfk_scheduleUsed' (scPtr : ObjRef) (new : Refill) : MFK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_scheduleUsed' _ _)

theorem mfk_refillSize' (scPtr : ObjRef) : MFK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillSize' _)

theorem mfk_refillSingle' (scPtr : ObjRef) : MFK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillSingle' _)

theorem mfk_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : MFK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_chargeEntireHeadRefill' _ _)

theorem mfk_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : MFK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_mergeNonoverlappingHeadRefill' _)

theorem mfk_updateIrqState' (irq : Irq) (irqState : X64IRQState) : MFK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateIrqState' _ _)

theorem mfke_archDeriveCap' (c : ArchCap) : MFKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfke_archDeriveCap' _)

theorem mfke_deriveCap' (sl : CslotPtr) (c : Cap) : MFKE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfke_deriveCap' _ _)

theorem mfk_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : MFK (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_makeArchFaultMsg' _ _)

theorem mfke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : MFKE m) :
    MFKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfke_unifyFailure' ?_)

theorem mfk_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : MFKE m) :
    MFK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfk_emptyOnFailure' ?_)

theorem mfk_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : MFKE m) :
    MFK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfk_constOnFailure' _ ?_)

theorem mfke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : MFKE m) :
    MFKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible refine mfke_capFaultOnFailure' _ _ ?_)

theorem mfk_loadWordOffs' (ptr : ObjRef) (offs : Nat) : MFK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_loadWordOffs' _ _)

theorem mfk_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : MFK (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => mfk_loadWordOffs' _ _) _)
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getExtraCptrs' _ _)

theorem mfk_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : MFK (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getReceiveSlots' _ _)

theorem mfk_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      MFK (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; mfk_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := mfk_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    mfk_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_transferCapsLoop' _ _ _ _ _ _)

theorem mfk_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : MFKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_lookupExtraCaps' _ _ _)

theorem mfk_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : MFK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_copyMrs' _ _ _ _ _)

theorem mfk_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : MFK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_transferCaps' _ _ _ _ _)

theorem mfk_makeFaultMsg' (f : Fault) (t : ObjRef) : MFK (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_makeFaultMsg' _ _)

theorem mfk_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : MFK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_handleOverrun' _ _)

theorem mfk_headInsufficientLoop' (scPtr : ObjRef) : MFK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_headInsufficientLoop' _)

theorem mfk_getMessageInfo' (thread : ObjRef) : MFK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getMessageInfo' _)

theorem mfk_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : MFK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_tcbEpAppend' _ _ _)

theorem mfk_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : MFK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doNormalTransfer' _ _ _ _ _ _ _)

theorem mfk_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : MFK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doFaultTransfer' _ _ _ _)

theorem mfk_bindScReply' (scPtr replyPtr : ObjRef) : MFK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_bindScReply' _ _)

theorem mfk_isValidTimeoutHandler' (tptr : ObjRef) : MFK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_isValidTimeoutHandler' _)

theorem mfk_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : MFK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doIpcTransfer' _ _ _ _ _)

theorem mfk_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : MFK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_replyPush' _ _ _ _)

theorem mfk_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : MFK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_sendIpcBlocked' _ _ _ _ _ _)

theorem mfk_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : MFK (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_sendIpc' _ _ _ _ _ _ _ _)

theorem mfk_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : MFK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_sendFaultIpc' _ _ _ _)

theorem mfk_refillBudgetCheckRoundRobin' (usage : Ticks) : MFK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillBudgetCheckRoundRobin' _)

theorem mfk_refillBudgetCheck' (usage : Ticks) : MFK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillBudgetCheck' _)

theorem mfk_maybeAddEmptyTail' (scPtr : ObjRef) : MFK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_maybeAddEmptyTail' _)

theorem mfk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : MFK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_maybeDonateSc' _ _)

theorem mfk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : MFK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_updateWaitingNtfn' _ _ _)

theorem mfk_handleTimeout' (tptr : ObjRef) (ex : Fault) : MFK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_handleTimeout' _ _)

theorem mfk_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : MFK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getMrs' _ _ _)

theorem mfk_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    MFK (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_handleFaultReply' _ _ _ _)

theorem mfk_returnConsumed' (scPtr : ObjRef) : MFK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_returnConsumed' _)

theorem mfk_schedContextBindNtfn' (sc ntfn : ObjRef) : MFK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextBindNtfn' _ _)

theorem mfk_schedContextYieldTo' (scPtr : ObjRef) : MFK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_schedContextYieldTo' _)

theorem mfk_getScActive' (scPtr : ObjRef) : MFK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_getScActive' _)

theorem mfk_commitTime' : MFK (commitTime (Z := Unit) ) := by
  unfold commitTime; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_commitTime' )

theorem mfk_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : MFK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillNew' _ _ _ _)

theorem mfk_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : MFK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_refillUpdate' _ _ _ _)

theorem mfk_sendSignal' (n : ObjRef) (b : Badge) : MFK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_sendSignal' _ _)

theorem mfk_doReplyTransfer' (s r : ObjRef) (g : Bool) : MFK (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_doReplyTransfer' _ _ _)

theorem mfk_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : MFK (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_invokeSchedControlConfigureFlags' _)

/-! ### The MCS budget check (not in the `DK` list) -/

theorem mfk_chargeBudget (u : Ticks) (b : Bool) : MFK (chargeBudget (Z := Unit) u b) := by
  unfold chargeBudget endTimeslice refillResetRr tcbSchedAppend
  mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_chargeBudget _ _)

theorem mfk_checkBudget : MFK (checkBudget (Z := Unit)) := by
  unfold checkBudget
  mfk_auto

end

end Fl4Proofs.P3.MachF
