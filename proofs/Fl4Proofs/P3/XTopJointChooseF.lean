/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch23 (c1)): **the SC frame of
the first-phase invocation** (spec side only), for `jMidChooseFact`
(XTopJointChooseB).

* `sV σ`: the current SC, the idle SC, the release queue, and for every
  reference the SC field of the TCB there and the bound TCB and refill max
  of the SC there (`tP`, `cP`). `SV m := FK sV m` (VsDom's projection frame).
* Leaves: `setObject` of an object that is no TCB, SC or CNode (by
  `set_object`'s type assertion the old object is no TCB or SC either),
  `setCap` (the old object is the CNode or TCB read), `threadSet` /
  `archThreadSet` / `asUser` keeping the SC field, `updateSchedContext`
  keeping the bound TCB and the refill max (refill, reply-stack and
  consumed-time updates). The rest as XTopJointMidRunQ's `QV` lemmas
  (scripted copy: sch23gen/genA.py, untracked); `sck_auto2` unfolds spec
  functions down to the leaves.
* The writes of SC bindings (`schedContextDonate`, `maybeReturnSc`) and of
  the release queue (`tcbReleaseEnqueue`, `tcbReleaseRemove`, `postpone`)
  are no `SV` frames; XTopJointChooseB proves them by hand.
-/
import Fl4Proofs.P3.XTopJointMidRunQ
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The SC field of a TCB. -/
def tP : Option KernelObject → Option (Option ObjRef)
  | some (.tcb x) => some x.tcbSchedContext
  | _ => none

/-- The bound TCB and the refill max of an SC. -/
def cP : Option KernelObject → Option (Option ObjRef × Nat)
  | some (.schedContext y _) => some (y.scTcb, y.scRefillMax)
  | _ => none

/-- The SC fields of the heap. -/
def mV (σ : State Unit) : ObjRef → Option (Option ObjRef) × Option (Option ObjRef × Nat) :=
  fun p => (tP (σ.kheap p), cP (σ.kheap p))

/-- The view type. -/
abbrev VT := ObjRef × ObjRef × List ObjRef × (ObjRef → Option (Option ObjRef) × Option (Option ObjRef × Nat))

/-- The SC view (module docstring). -/
def sV (σ : State Unit) : VT := (σ.curSc, σ.idleSc, σ.releaseQueue, mV σ)

abbrev SV {α : Type} (m : NonDet (State Unit) α) : Prop := FK sV m

abbrev SVE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE sV m

theorem sV_upd {σ : State Unit} {p : ObjRef} {o : KernelObject}
    (h : tP (σ.kheap p) = tP (some o) ∧ cP (σ.kheap p) = cP (some o)) :
    sV { σ with kheap := Function.update σ.kheap p (some o) } = sV σ := by
  unfold sV
  simp only [Prod.mk.injEq, true_and]
  funext q
  unfold mV
  dsimp only
  by_cases hq : q = p
  · subst hq; rw [Function.update_self]; exact Prod.ext h.1.symm h.2.symm
  · rw [Function.update_of_ne hq]

/-- A syntax for `SV` leaves (extended below, one rule per lemma). -/
syntax "sck_leaf" : tactic
macro_rules | `(tactic| sck_leaf) => `(tactic| fail "no sck_leaf")

macro "sck_auto" : tactic => `(tactic| repeat' (first | sck_leaf | dk_step0))
macro "sck_auto2" : tactic => `(tactic| repeat' (first | sck_leaf | dk_step0 | fv_unfold))

theorem sck_setObject_ns (p : ObjRef) (o : KernelObject) (ht : ∀ y, o ≠ .tcb y)
    (hs : ∀ y n, o ≠ .schedContext y n) (hc : ∀ sz cs, o ≠ .cnode sz cs) : SV (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨⟨k, hk, hA⟩, e⟩ := setObject_out hx
  rw [e]
  apply sV_upd
  rw [hk]
  have hk1 : ∀ y, k ≠ .tcb y := by
    rintro y rfl
    cases o <;> simp_all [aType]
  have hk2 : ∀ y n, k ≠ .schedContext y n := by
    rintro y n rfl
    by_cases hv : validSchedContextSize n <;> cases o <;> simp_all [aType]
  have e1 : tP (some k) = none := by cases k <;> first | rfl | exact absurd rfl (hk1 _)
  have e2 : cP (some k) = none := by cases k <;> first | rfl | exact absurd rfl (hk2 _ _)
  have e3 : tP (some o) = none := by cases o <;> first | rfl | exact absurd rfl (ht _)
  have e4 : cP (some o) = none := by cases o <;> first | rfl | exact absurd rfl (hs _ _)
  exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩
macro_rules | `(tactic| sck_leaf) => `(tactic| ((with_reducible refine sck_setObject_ns _ _ ?_ ?_ ?_) <;> simp))

theorem sck_threadSet (f : Tcb → Tcb) (t : ObjRef) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) :
    SV (threadSet (Z := Unit) f t) := by
  intro σ x ⟨⟨tcb, s1⟩, h1, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨-, e⟩ := setObject_out hx
  rw [e]
  apply sV_upd
  rw [getTcb_some e1]
  exact ⟨by simp only [tP, hf], rfl⟩
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_threadSet _ _ (fun _ => rfl))

theorem sck_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : SV (archThreadSet (Z := Unit) f t) :=
  sck_threadSet (fun tcb => { tcb with tcbArch := f tcb.tcbArch }) t (fun _ => rfl)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_archThreadSet _ _)

theorem sck_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : SV (asUser (Z := Unit) t u) := by
  intro σ x ⟨⟨tcb, s1⟩, h1, y2, h2, ⟨⟨a, uc'⟩, s3⟩, h3, y4, h4, y5, h5, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  have h2 := mem_pure' h2; subst h2
  obtain ⟨-, e3⟩ := h3
  simp only at e3; subst e3
  have h4 := mem_pure' h4; subst h4
  obtain ⟨-, e⟩ := setObject_out h5
  have hx := mem_pure' hx; subst hx
  simp only
  rw [e]
  apply sV_upd
  rw [getTcb_some e1]
  exact ⟨rfl, rfl⟩
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_asUser _ _)

theorem sck_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scTcb = y.scTcb ∧ (f y).scRefillMax = y.scRefillMax) :
    SV (updateSchedContext (Z := Unit) p f) := by
  intro σ x ⟨⟨k, s1⟩, h1, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  simp only [readObject] at e1
  cases k with
  | schedContext y n =>
    obtain ⟨-, e⟩ := setObject_out hx
    rw [e]
    apply sV_upd
    rw [e1]
    exact ⟨rfl, by simp only [cP, (hf y).1, (hf y).2]⟩
  | _ => exact hx.elim
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_updateSchedContext _ _ (fun _ => ⟨rfl, rfl⟩))

set_option maxHeartbeats 1000000 in
theorem sck_setCap (c : Cap) (sl : CslotPtr) : SV (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x hx
  unfold setCap at hx
  obtain ⟨⟨k, s1⟩, h1, hx⟩ := hx
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  simp only [readObject] at e1
  cases k
  all_goals dsimp only at hx
  all_goals (repeat' split at hx)
  all_goals first
    | exact hx.elim
    | (obtain ⟨y, hy, -⟩ := hx; exact hy.elim)
    | (obtain ⟨y, hy, hx'⟩ := hx
       have hy := mem_pure' hy
       subst hy
       dsimp only at hx'
       obtain ⟨-, e⟩ := setObject_out hx'
       rw [e]; apply sV_upd; rw [e1]; exact ⟨rfl, rfl⟩)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setCap _ _)

theorem sck_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ a, (∀ y, C a ≠ .tcb y) ∧ (∀ y n, C a ≠ .schedContext y n) ∧ ∀ sz cs, C a ≠ .cnode sz cs) :
    SV (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  repeat' (first | exact sck_setObject_ns _ _ (hC _).1 (hC _).2.1 (hC _).2.2 | dk_step0)

theorem sck_setSimpleKo_ep (q : ObjRef) (e : Endpoint) : SV (setSimpleKo (Z := Unit) KernelObject.endpoint q e) :=
  sck_setSimpleKo _ q e (fun _ => ⟨by simp, by simp, by simp⟩)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setSimpleKo_ep _ _)

theorem sck_setSimpleKo_ntfn (q : ObjRef) (e : Notification) :
    SV (setSimpleKo (Z := Unit) KernelObject.notification q e) :=
  sck_setSimpleKo _ q e (fun _ => ⟨by simp, by simp, by simp⟩)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setSimpleKo_ntfn _ _)

theorem sck_setSimpleKo_reply (q : ObjRef) (e : Reply) : SV (setSimpleKo (Z := Unit) KernelObject.reply q e) :=
  sck_setSimpleKo _ q e (fun _ => ⟨by simp, by simp, by simp⟩)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setSimpleKo_reply _ _)

theorem sck_doMachineOp {α : Type} (mop : NonDet MachineState α) : SV (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_doMachineOp _)

theorem sck_doExtendedOp (eop : DetExtMonad Unit) : SV (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_doExtendedOp _)
theorem scke_pure_run {ε α : Type} (a : α) : SV (ExceptT.run (pure a : NonDetE (State Unit) ε α)) := dk_pure _

theorem sck_getCap (sl : CslotPtr) : SV (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getCap _)

theorem sck_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    SV (portOut (Z := Unit) f w) := by
  unfold portOut; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_portOut _ _)

theorem sck_getPt (ptr : ObjRef) : SV (getPt (Z := Unit) ptr) := by
  unfold getPt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPt _)

theorem sck_getPte (ptr : ObjRef) : SV (getPte (Z := Unit) ptr) := by
  unfold getPte; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPte _)

theorem sck_getPd (ptr : ObjRef) : SV (getPd (Z := Unit) ptr) := by
  unfold getPd; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPd _)

theorem sck_getPde (ptr : ObjRef) : SV (getPde (Z := Unit) ptr) := by
  unfold getPde; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPde _)

theorem sck_getPml4 (ptr : ObjRef) : SV (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPml4 _)

theorem sck_getPml4e (ptr : ObjRef) : SV (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPml4e _)

theorem sck_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : SVE (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupPdptSlot _ _)

theorem sck_getPdpt (ptr : ObjRef) : SV (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPdpt _)

theorem sck_getPdpte (ptr : ObjRef) : SV (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getPdpte _)

theorem sck_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : SVE (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupPdSlot _ _)

theorem sck_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : SVE (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupPtSlot _ _)

theorem sck_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SV (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setPdpt _ _)

theorem sck_storePdpte (p : ObjRef) (pte : PDPTE) : SV (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_storePdpte _ _)

theorem sck_getAsidPool (ptr : ObjRef) : SV (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getAsidPool _)

theorem sck_findVspaceForAsid (asid : Asid) : SVE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_findVspaceForAsid _)

theorem sck_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SV (setPt (Z := Unit) ptr pt) := by
  unfold setPt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setPt _ _)

theorem sck_storePte (p : ObjRef) (pte : PTE) : SV (storePte (Z := Unit) p pte) := by
  unfold storePte; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_storePte _ _)

theorem sck_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SV (setPd (Z := Unit) ptr pd) := by
  unfold setPd; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setPd _ _)

theorem sck_storePde (p : ObjRef) (pde : PDE) : SV (storePde (Z := Unit) p pde) := by
  unfold storePde; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_storePde _ _)

theorem sck_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : SV (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_unmapPage _ _ _ _)

theorem sck_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : SV (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performPageInvocationUnmap _ _)

theorem sck_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SV (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setAsidPool _ _)

theorem sck_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : SV (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_flushTable _ _ _ _)

theorem sck_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SV (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setPml4 _ _)

theorem sck_setOriginal (slot : CslotPtr) (v : Bool) : SV (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setOriginal _ _)

theorem sck_updateCdt (f : Cdt → Cdt) : SV (updateCdt (Z := Unit) f) := by
  unfold updateCdt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_updateCdt _)

theorem sck_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : SV (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setUntypedCapAsFull _ _ _)

theorem sck_storePml4e (p : ObjRef) (pte : PML4E) : SV (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_storePml4e _ _)

theorem sck_flushAll (vspace : ObjRef) (asid : Asid) : SV (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_flushAll _ _)

theorem sck_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : SV (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_unmapPdpt _ _ _)

theorem sck_setIoportMask (f l : IoPort) (val : Bool) : SV (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setIoportMask _ _ _)

theorem sck_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : SV (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_invalidatePageStructureCacheAsid _ _)

theorem sck_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : SV (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_unmapPd _ _ _)

theorem sck_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : SV (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_capInsert _ _ _)

theorem sck_portIn (f : MachineMonad Data) : SV (portIn (Z := Unit) f) := by
  unfold portIn; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_portIn _)

theorem sck_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : SV (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_unmapPageTable _ _ _)

theorem sck_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : SV (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_storeAsidPoolEntry _ _ _)

theorem sck_performPageInvocation (iv : PageInvocation) : SV (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performPageInvocation _)

theorem sck_performPageTableInvocation (iv : PageTableInvocation) : SV (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performPageTableInvocation _)

theorem sck_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : SV (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performPageDirectoryInvocation _)

theorem sck_performPdptInvocation (iv : PdptInvocation) : SV (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performPdptInvocation _)

theorem sck_performAsidPoolInvocation (iv : AsidPoolInvocation) : SV (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performAsidPoolInvocation _)

theorem sck_performIoPortInvocation (i : IoPortInvocation) : SV (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performIoPortInvocation _)

theorem sck_performIoportControlInvocation (i : IoPortControlInvocation) : SV (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performIoportControlInvocation _)

theorem sck_performDeriveSubframe (iv : Fl4SubframeInvocation) : SV (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performDeriveSubframe _)

theorem sck_performTestAndClearAccessed (_slot : ObjRef) : SV (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_performTestAndClearAccessed _)


theorem sck_performPml4Flush (i : Fl4Pml4Invocation) : SV (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact sck_flushAll _ _

theorem scke_rab (p : Cap × CapRef) : SVE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (sck_getCap _)) fun nc => ?_
        split
        · exact scke_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_rab _)

theorem sck_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, SV (g a b)) :
    ∀ l1 l2, SV (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => sck_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine sck_zipWithMx' (fun _ _ => ?_) _ _)

theorem sck_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : SV (setMrs (Z := Unit) t b m) := by
  unfold setMrs
  intro σ x ⟨⟨tcb, s1⟩, h1, y2, h2, y3, h3, y4, h4, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  have h2 := mem_pure' h2; subst h2
  have h3 := mem_pure' h3; subst h3
  obtain ⟨-, e⟩ := setObject_out h4
  refine Eq.trans ((?_ : FK sV _) _ _ hx) ?_
  · sck_auto2
  rw [e]
  apply sV_upd
  rw [getTcb_some e1]
  exact ⟨rfl, rfl⟩
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setMrs' _ _ _)



section
set_option maxRecDepth 20000

theorem scke_lookupCapAndSlot (t : ObjRef) (c : CapRef) : SVE (lookupCapAndSlot (Z := Unit) t c) := by
  sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_lookupCapAndSlot _ _)

theorem sck_lookupIpcBuffer (b : Bool) (t : ObjRef) : SV (lookupIpcBuffer (Z := Unit) b t) := by
  sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupIpcBuffer _ _)

theorem scke_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    SVE (lookupExtraCaps (Z := Unit) t b mi) := by
  sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_lookupExtraCaps _ _ _)

theorem sck_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : SV (getMrs (Z := Unit) t b mi) := by
  sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getMrs _ _ _)

theorem sck_getMessageInfo (t : ObjRef) : SV (getMessageInfo (Z := Unit) t) := by
  sck_auto2

theorem scke_decodeIrqControl (r : Bool) (label : Data) (args : List Data) (sl : CslotPtr) (ex : List Cap) :
    SVE (decodeFl4IrqControl (Z := Unit) r label args sl ex) := by
  sck_auto2

theorem scke_decodeIrqHandler (label : Data) (irq : Irq) (ex : List (Cap × CslotPtr)) :
    SVE (decodeIrqHandlerInvocation (Z := Unit) label irq ex) := by
  sck_auto2

theorem scke_decodeUntyped (label : Data) (args : List Data) (sl : CslotPtr) (cap : Cap) (ex : List Cap) :
    SVE (fl4DecodeUntypedInvocation (Z := Unit) label args sl cap ex) := by
  sck_auto2

set_option maxHeartbeats 2000000 in
theorem scke_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    SVE (decodePdptInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePdptInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePdptInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    SVE (decodePageDirectoryInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageDirectoryInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePageDirectoryInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    SVE (decodePageTableInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageTableInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePageTableInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    SVE (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePageInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) :
    SVE (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePortInvocation _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : ArchCap) (ex : List Cap) :
    SVE (decodeIoportControlInvocation (Z := Unit) label args slot cap ex) := by
  unfold decodeIoportControlInvocation; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeIoportControlInvocation _ _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_decodePml4Flush (cap : ArchCap) :
    SVE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodePml4Flush _)

set_option maxHeartbeats 2000000 in
theorem scke_decodeTestAndClearAccessed (cap : ArchCap) :
    SVE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeTestAndClearAccessed _)

set_option maxHeartbeats 2000000 in
theorem scke_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (ex : List (Cap × CslotPtr)) :
    SVE (decodeDeriveSubframe (Z := Unit) args cte cap ex) := by
  unfold decodeDeriveSubframe; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeDeriveSubframe _ _ _ _)

set_option maxHeartbeats 2000000 in
theorem scke_archDecodeInvocation (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : SVE (archDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold archDecodeInvocation
  split
  all_goals sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_archDecodeInvocation _ _ _ _ _ _)

theorem scke_archDecode (label : Data) (args : List Data) (x : CapRef) (sl : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : SVE (fl4ArchDecodeInvocation (Z := Unit) label args x sl cap ex) := by
  unfold fl4ArchDecodeInvocation
  split
  all_goals sck_auto2

macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeIrqControl _ _ _ _ _)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeIrqHandler _ _ _)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_decodeUntyped _ _ _ _ _)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_archDecode _ _ _ _ _ _)

set_option maxHeartbeats 2000000 in
/-- **The first-phase decode keeps `fV`.** -/
theorem scke_decodeFirst (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    SVE (fl4DecodeInvocation (Z := Unit) true label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try rw [if_pos rfl]
  all_goals sck_auto2

theorem scke_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : SV m) :
    SVE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine scke_withoutPreemption' ?_)
theorem scke_resolveAddressBits (p : Cap × CapRef) : SVE (resolveAddressBits (Z := Unit) p) := scke_rab p
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_resolveAddressBits _)

theorem sck_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : SVE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupSlotForThread' _ _)

theorem sck_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : SVE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupCapAndSlot' _ _)

theorem sck_lookupCap' (thread : ObjRef) (ref : CapRef) : SVE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupCap' _ _)

theorem sck_captransferFromWords' (ptr : Word) : SV (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_captransferFromWords' _)

theorem sck_loadCapTransfer' (buffer : ObjRef) : SV (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_loadCapTransfer' _)

theorem sck_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : SV (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setExtraBadge' _ _ _)

theorem scke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : SVE m) :
    SVE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine scke_lookupErrorOnFailure' _ ?_)

theorem sck_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : SVE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupSlotForCnodeOp' _ _ _ _)

theorem sck_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : SVE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact sck_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupTargetSlot' _ _ _)

theorem scke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : SVE (f a)) :
    SVE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [run_bind_ok (run_returnOk a σ)] at hx
  exact h σ x hx
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine scke_bind_returnOk' ?_)

theorem sck_ensureNoChildren' (cslotPtr : CslotPtr) : SVE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_ensureNoChildren' _)

theorem sck_getRefillTail' (scPtr : ObjRef) : SV (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getRefillTail' _)

theorem sck_getRefills' (scPtr : ObjRef) : SV (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getRefills' _)

theorem sck_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : SV (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_refillAddTail' _ _)

theorem sck_refillFull' (scPtr : ObjRef) : SV (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_refillFull' _)

theorem sck_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : SV (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_updateRefillTl' _ _)

theorem sck_scheduleUsed' (scPtr : ObjRef) (new : Refill) : SV (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_scheduleUsed' _ _)

theorem sck_refillSize' (scPtr : ObjRef) : SV (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_refillSize' _)

theorem sck_refillSingle' (scPtr : ObjRef) : SV (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_refillSingle' _)

theorem sck_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : SV (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_chargeEntireHeadRefill' _ _)

theorem sck_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : SV (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_mergeNonoverlappingHeadRefill' _)

theorem sck_updateIrqState' (irq : Irq) (irqState : X64IRQState) : SV (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_updateIrqState' _ _)

theorem scke_archInvokeIrqControl' (i : ArchIrqControlInvocation) : SVE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_archInvokeIrqControl' _)

theorem sck_invokeIrqControl' (i : IrqControlInvocation) : SVE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_invokeIrqControl' _)

theorem scke_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : SVE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_invokeFl4IrqControl' _)

theorem scke_archDeriveCap' (c : ArchCap) : SVE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_archDeriveCap' _)

theorem scke_deriveCap' (sl : CslotPtr) (c : Cap) : SVE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact scke_deriveCap' _ _)

theorem sck_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : SV (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_makeArchFaultMsg' _ _)

theorem scke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : SVE m) :
    SVE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine scke_unifyFailure' ?_)

theorem sck_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : SVE m) :
    SV (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine sck_emptyOnFailure' ?_)

theorem sck_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : SVE m) :
    SV (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine sck_constOnFailure' _ ?_)

theorem scke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : SVE m) :
    SVE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible refine scke_capFaultOnFailure' _ _ ?_)

theorem sck_loadWordOffs' (ptr : ObjRef) (offs : Nat) : SV (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact sck_doMachineOp _
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_loadWordOffs' _ _)

theorem sck_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : SV (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => sck_loadWordOffs' _ _) _)
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getExtraCptrs' _ _)

theorem sck_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : SV (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getReceiveSlots' _ _)

theorem sck_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      SV (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; sck_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := sck_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    sck_auto
    all_goals first | exact ih _ _ | sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_transferCapsLoop' _ _ _ _ _ _)

theorem sck_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SVE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_lookupExtraCaps' _ _ _)

theorem sck_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : SV (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_copyMrs' _ _ _ _ _)

theorem sck_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : SV (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_transferCaps' _ _ _ _ _)

theorem sck_makeFaultMsg' (f : Fault) (t : ObjRef) : SV (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_makeFaultMsg' _ _)

theorem sck_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : SV (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_handleOverrun' _ _)

theorem sck_headInsufficientLoop' (scPtr : ObjRef) : SV (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_headInsufficientLoop' _)

theorem sck_getMessageInfo' (thread : ObjRef) : SV (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getMessageInfo' _)

theorem sck_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : SV (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_tcbEpAppend' _ _ _)

theorem sck_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SV (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_doNormalTransfer' _ _ _ _ _ _ _)

theorem sck_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : SV (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_doFaultTransfer' _ _ _ _)

theorem sck_bindScReply' (scPtr replyPtr : ObjRef) : SV (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_bindScReply' _ _)

theorem sck_isValidTimeoutHandler' (tptr : ObjRef) : SV (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_isValidTimeoutHandler' _)

theorem sck_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : SV (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_doIpcTransfer' _ _ _ _ _)


theorem sck_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : SV (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_orderedInsert' _ _ _ _)

theorem sck_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : SV (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; sck_auto
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_readyTimesAppend' _ _)

theorem sck_getNtfnObjRef' (f : Notification → Option ObjRef) (n : ObjRef) :
    SV (getNtfnObjRef (Z := Unit) f n) := by
  unfold getNtfnObjRef; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_getNtfnObjRef' _ _)

theorem sck_setReplyObjRef' (f : (Option ObjRef → Option ObjRef) → Reply → Reply) (r : ObjRef) (v : Option ObjRef) :
    SV (setReplyObjRef (Z := Unit) f r v) := by
  unfold setReplyObjRef; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setReplyObjRef' _ _ _)

theorem sck_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    SV (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_handleFaultReply' _ _ _ _)


theorem scke_midF (t : ObjRef) (info : MessageInfo) (cptr : CapRef) : SVE (midF t info cptr) := by
  unfold midF; sck_auto2

theorem scke_midE (t : ObjRef) (info : MessageInfo) (cptr : CapRef) (a) : SVE (midE t info cptr a) := by
  obtain ⟨sl, cap, ex, buf⟩ := a
  unfold midE
  refine dke_bind (dke_liftE (sck_getMrs _ _ _)) fun _ => scke_decodeFirst _ _ _ _ _ _ _

end


/-! ## The perform frames and the IPC pieces -/

section
set_option maxRecDepth 20000

theorem scke_archPerform_nA (i : ArchInvocation) (h : ∀ x, i ≠ .invokeASIDControl x) :
    SVE (archPerformInvocation (Z := Unit) i) := by
  unfold archPerformInvocation; apply dke_liftE
  cases i
  all_goals first | exact absurd rfl (h _) | sck_auto

theorem scke_fl4ArchPerform_nA (i : Fl4ArchInvocation) (h : ∀ x, i ≠ .spec (.invokeASIDControl x)) :
    SVE (fl4ArchPerformInvocation (Z := Unit) i) := by
  cases i with
  | spec i => exact scke_archPerform_nA i (fun x e => h x (by rw [e]))
  | pml4Flush i => unfold fl4ArchPerformInvocation; apply dke_liftE; sck_auto; exact sck_performPml4Flush i
  | deriveSubframe i => unfold fl4ArchPerformInvocation; apply dke_liftE; sck_auto
  | testAndClearAccessed slot => unfold fl4ArchPerformInvocation; apply dke_liftE; sck_auto

theorem scke_invokeIRQControl (i : Fl4IrqControlInvocation) :
    SVE (invokeFl4IrqControl (Z := Unit) i) := scke_invokeFl4IrqControl' i

theorem sck_setThreadState (t : ObjRef) (ts : ThreadState) : SV (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_setThreadState _ _)

theorem sck_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    SV (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_tcbSchedAction _ _)

theorem sck_rescheduleRequired : SV (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_rescheduleRequired)

theorem sck_possibleSwitchTo (t : ObjRef) : SV (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_possibleSwitchTo _)

theorem sck_testReschedule (t : ObjRef) : SV (testReschedule (Z := Unit) t) := by
  unfold testReschedule; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_testReschedule _)

theorem sck_ifCond (o : Option ObjRef) (a b : Option Bool) : SV (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_ifCond _ _ _)

theorem sck_tcbEpDequeue (t e : ObjRef) : SV (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_tcbEpDequeue _ _)

theorem sck_tcbNtfnDequeue (t n : ObjRef) : SV (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_tcbNtfnDequeue _ _)

theorem sck_replyUnlinkTcb (t r : ObjRef) : SV (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_replyUnlinkTcb _ _)

theorem sck_replyUnlinkSc (s r : ObjRef) : SV (replyUnlinkSc (Z := Unit) s r) := by
  unfold replyUnlinkSc; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_replyUnlinkSc _ _)

theorem sck_cancelIpc (t : ObjRef) : SV (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_cancelIpc _)

theorem sck_sendIpcBlocked (t e : ObjRef) (b : Badge) (g gr call : Bool) :
    SV (sendIpcBlocked (Z := Unit) t e b g gr call) := by
  unfold sendIpcBlocked; sck_auto2
macro_rules | `(tactic| sck_leaf) => `(tactic| with_reducible exact sck_sendIpcBlocked _ _ _ _ _ _)

end

end

end Fl4Proofs.P3.MidRun
