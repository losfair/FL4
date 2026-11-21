/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch11 (1)): **the spec frame
"the current thread's state and fault are kept"** (spec side only), for
`JMidRunHyp` (XTopJointMidRun).

* `ctV ct σ`: the current thread and the state and fault of the TCB at `ct`
  (`none` if `ct` holds no TCB). `KF ct m` := `FK (ctV ct) m` (VsDom's
  generic projection frame, so VsDom's combinators and `dk_step0` apply):
  every outcome of `m` keeps the current thread and `ct`'s state and fault.
* Object-update leaves: `setObject` of a non-TCB object (`kf_setObject_nt`,
  by `set_object`'s type assertion a TCB is never replaced by another kind),
  `threadSet` with a function keeping state and fault (`kf_threadSet`), any
  `threadSet` / `setThreadState` of a thread `t ≠ ct` (`kf_threadSet_ne`,
  `kf_setThreadState`), `archThreadSet`, `asUser`, the machine and extended
  state.
* The rest: one lemma per spec function, bottom-up by `kf_auto`, mirroring
  VsDomOps / DomRecDel / TcbDom / AllDom's `DK` lemmas (generated: sch11gen/gen.py in the worktree root, untracked),
  with `t ≠ ct` premises where the function sets the state of its argument
  thread `t`.
-/
import Fl4Proofs.P3.VsDom
import Fl4Spec.Ext.ReplyError
open Classical

namespace Fl4Proofs.P3.MidRun
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The state and fault of a TCB (`none` for any other object or none). -/
def tsV : Option KernelObject → Option (ThreadState × Option Fault)
  | some (.tcb x) => some (x.tcbState, x.tcbFault)
  | _ => none

/-- The current thread and the state and fault of the TCB at `ct`. -/
def ctV (ct : ObjRef) (σ : State Unit) : ObjRef × Option (ThreadState × Option Fault) :=
  (σ.curThread, tsV (σ.kheap ct))

/-- Every outcome of `m` keeps the current thread and `ct`'s state and fault. -/
abbrev KF (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := FK (ctV ct) m

/-- `KF` for the exception monad. -/
abbrev KFE (ct : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE (ctV ct) m

theorem mem_getsThe' {α : Type} {f : State Unit → Option α} {σ : State Unit} {x : α × State Unit}
    (h : x ∈ (NonDet.getsThe f σ).1) : f σ = some x.1 ∧ x.2 = σ := by
  unfold NonDet.getsThe at h
  revert h
  cases e : f σ with
  | none => intro h; simp [NonDet.assertOpt, NonDet.fail] at h
  | some a =>
    intro h
    simp only [NonDet.assertOpt, NonDet.pure] at h
    rw [Set.mem_singleton_iff] at h
    subst h; exact ⟨rfl, rfl⟩

theorem getTcb_some {t : ObjRef} {σ : State Unit} {tcb : Tcb} (h : getTcb (Z := Unit) t σ = some tcb) :
    σ.kheap t = some (.tcb tcb) := by
  revert h
  unfold getTcb readObject
  rcases e : σ.kheap t with _ | k
  · simp
  · cases k <;> simp_all

theorem aType_eq_tcb {o : KernelObject} (h : aType o = .aTCB) : ∃ y, o = .tcb y := by
  cases o with
  | tcb y => exact ⟨y, rfl⟩
  | cnode sz cs => by_cases hw : wellFormedCnodeN sz cs <;> simp [aType, hw] at h
  | schedContext y n => by_cases hw : validSchedContextSize n <;> simp [aType, hw] at h
  | _ => simp [aType] at h

theorem mem_pure' {α : Type} {a : α} {s : State Unit} {x : α × State Unit}
    (h : x ∈ ((pure a : NonDet (State Unit) α) s).1) : x = (a, s) := h

theorem mem_get' {s : State Unit} {x : State Unit × State Unit}
    (h : x ∈ (NonDet.get s).1) : x = (s, s) := h

theorem mem_put' {s s' : State Unit} {x : Unit × State Unit}
    (h : x ∈ (NonDet.put s' s).1) : x = ((), s') := h

theorem setObject_out {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (setObject (Z := Unit) p o σ).1) :
    (∃ k, σ.kheap p = some k ∧ aType k = aType o) ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨⟨k, s1⟩, h1, ⟨u, s2⟩, h2, ⟨g, s3⟩, h3, hx⟩ := h
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨hA, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  have h3 := mem_get' h3
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hx := mem_put' hx
  subst hx
  exact ⟨⟨k, e1, hA⟩, rfl⟩

section
variable {ct : ObjRef}

theorem kf_setObject_nt (p : ObjRef) (o : KernelObject) (ho : ∀ y, o ≠ .tcb y) :
    KF ct (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨⟨k, hk, hA⟩, e⟩ := setObject_out hx
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc =>
    subst hc
    rw [hk]
    have h1 : tsV (some o) = none := by
      cases o <;> first | rfl | exact absurd rfl (ho _)
    have h2 : tsV (some k) = none := by
      cases k <;> first | rfl | (exfalso; obtain ⟨y, rfl⟩ := aType_eq_tcb hA.symm; exact ho y rfl)
    rw [h1, h2]
  · rfl

theorem kf_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbState = x.tcbState ∧ (f x).tcbFault = x.tcbFault) :
    KF ct (threadSet (Z := Unit) f t) := by
  intro σ x ⟨⟨tcb, s1⟩, h1, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨-, e⟩ := setObject_out hx
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc => subst hc; rw [getTcb_some e1]; simp [tsV, (hf tcb).1, (hf tcb).2]
  · rfl

theorem kf_threadSet_ne (f : Tcb → Tcb) (t : ObjRef) (ht : t ≠ ct) :
    KF ct (threadSet (Z := Unit) f t) := by
  intro σ x ⟨⟨tcb, s1⟩, h1, hx⟩
  obtain ⟨-, e1'⟩ := mem_getsThe' h1
  simp only at e1'
  subst e1'
  obtain ⟨-, e⟩ := setObject_out hx
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply, if_neg (fun h => ht h.symm)]

theorem kf_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : KF ct (archThreadSet (Z := Unit) f t) :=
  kf_threadSet (fun tcb => { tcb with tcbArch := f tcb.tcbArch }) t (fun _ => ⟨rfl, rfl⟩)

theorem kf_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : KF ct (asUser (Z := Unit) t u) := by
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
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc => subst hc; rw [getTcb_some e1]; simp [tsV]
  · rfl

theorem kf_doMachineOp {α : Type} (mop : NonDet MachineState α) : KF ct (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem kf_doExtendedOp (eop : DetExtMonad Unit) : KF ct (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

end

/-- A `KF` lemma of a spec function (extended below, one rule per lemma). -/
syntax "kf_leaf" : tactic
macro_rules | `(tactic| kf_leaf) => `(tactic| fail "no kf_leaf")
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_doMachineOp _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_doExtendedOp _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_asUser _ _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archThreadSet _ _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_threadSet _ _ (fun _ => ⟨rfl, rfl⟩))
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_threadSet_ne _ _ (by assumption))
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setObject_nt _ _ (fun _ h => by cases h))

macro "kf_auto" : tactic => `(tactic| repeat' (first | kf_leaf | dk_step0))

section
variable {ct : ObjRef}

theorem kf_setThreadState (t : ObjRef) (ts : ThreadState) (ht : t ≠ ct) :
    KF ct (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setThreadState _ _ (by assumption))

/-- A read of the object at `p`, a new object of the same state and fault
(state unchanged), written back. -/
theorem kf_get_set (p : ObjRef) (m : KernelObject → NonDet (State Unit) KernelObject)
    (hm : ∀ k s y, y ∈ (m k s).1 → y.2 = s ∧ tsV (some y.1) = tsV (some k)) :
    KF ct (getObject (Z := Unit) p >>= fun k => m k >>= fun o => setObject p o) := by
  intro σ x ⟨⟨k, s1⟩, h1, ⟨o, s2⟩, h2, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨rfl, ho⟩ := hm k s1 _ h2
  obtain ⟨-, e⟩ := setObject_out hx
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc => subst hc; simp only [readObject] at e1; rw [e1]; exact ho
  · rfl

theorem setObject_ctV_same {p : ObjRef} {o k : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (setObject (Z := Unit) p o σ).1) (hk : σ.kheap p = some k) (ho : tsV (some o) = tsV (some k)) :
    ctV ct x.2 = ctV ct σ := by
  obtain ⟨-, e⟩ := setObject_out h
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc => subst hc; rw [hk]; exact ho
  · rfl

theorem kf_getObject_bind {β : Type} (p : ObjRef) (m : KernelObject → NonDet (State Unit) β)
    (hm : ∀ k σ, σ.kheap p = some k → ∀ x ∈ (m k σ).1, ctV ct x.2 = ctV ct σ) :
    KF ct (getObject (Z := Unit) p >>= m) := by
  intro σ x ⟨⟨k, s1⟩, h1, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only [readObject] at e1 e1'
  subst e1'
  exact hm k _ e1 x hx

theorem kf_setCap (c : Cap) (sl : CslotPtr) : KF ct (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; dsimp only
  refine kf_getObject_bind o _ fun k σ hk x hx => ?_
  cases k
  all_goals dsimp only at hx
  all_goals repeat' split at hx
  all_goals first
    | exact hx.elim
    | (obtain ⟨y, hy, hx⟩ := hx; exact hy.elim)
    | (obtain ⟨y, hy, hx⟩ := hx
       have hy := mem_pure' hy; subst hy
       exact setObject_ctV_same hx hk rfl)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setCap _ _)

theorem kf_getCap (sl : CslotPtr) : KF ct (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getCap _)

theorem kf_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    KF ct (portOut (Z := Unit) f w) := by
  unfold portOut; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_portOut _ _)

theorem setObject_ctV {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (h : x ∈ (setObject (Z := Unit) p o σ).1) (hn : ∀ y, σ.kheap p ≠ some (.tcb y)) :
    ctV ct x.2 = ctV ct σ := by
  obtain ⟨⟨k, hk, hA⟩, e⟩ := setObject_out h
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc =>
    subst hc
    rw [hk]
    have h2 : tsV (some k) = none := by
      cases k <;> first | rfl | exact absurd hk (hn _)
    have h1 : tsV (some o) = none := by
      cases o <;> first | rfl | (exfalso; obtain ⟨y, rfl⟩ := aType_eq_tcb hA; exact hn y hk)
    rw [h1, h2]
  · rfl

theorem kf_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    KF ct (setSimpleKo (Z := Unit) C q e) := by
  intro σ x ⟨⟨obj, s1⟩, h1, ⟨u, s2⟩, h2, ⟨u', s3⟩, h3, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  obtain ⟨hS, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  obtain ⟨-, e3⟩ := h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨-, rfl⟩ := e3
  refine setObject_ctV hx fun y hy => ?_
  simp only [readObject] at e1
  rw [e1] at hy
  cases hy
  simp [isSimpleType, aType] at hS
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setSimpleKo _ _ _)

theorem kfe_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : KF ct m) :
    KFE ct (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kfe_withoutPreemption' ?_)

theorem kfe_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : KFE ct (f a)) :
    KFE ct (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  change x ∈ (NonDet.bind (ExceptT.run (NonDetE.returnOk a : NonDetE (State Unit) ε α)) _ σ).1 at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy := mem_pure' hy
  subst hy
  exact h σ x hx
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kfe_bind_returnOk' ?_)

theorem kf_getPt (ptr : ObjRef) : KF ct (getPt (Z := Unit) ptr) := by
  unfold getPt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPt _)

theorem kf_getPte (ptr : ObjRef) : KF ct (getPte (Z := Unit) ptr) := by
  unfold getPte; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPte _)

theorem kf_getPd (ptr : ObjRef) : KF ct (getPd (Z := Unit) ptr) := by
  unfold getPd; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPd _)

theorem kf_getPde (ptr : ObjRef) : KF ct (getPde (Z := Unit) ptr) := by
  unfold getPde; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPde _)

theorem kf_getPml4 (ptr : ObjRef) : KF ct (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPml4 _)

theorem kf_getPml4e (ptr : ObjRef) : KF ct (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPml4e _)

theorem kf_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : KFE ct (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupPdptSlot _ _)

theorem kf_getPdpt (ptr : ObjRef) : KF ct (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPdpt _)

theorem kf_getPdpte (ptr : ObjRef) : KF ct (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getPdpte _)

theorem kf_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : KFE ct (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupPdSlot _ _)

theorem kf_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : KFE ct (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupPtSlot _ _)

theorem kf_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : KF ct (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setPdpt _ _)

theorem kf_storePdpte (p : ObjRef) (pte : PDPTE) : KF ct (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storePdpte _ _)

theorem kf_getAsidPool (ptr : ObjRef) : KF ct (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getAsidPool _)

theorem kf_findVspaceForAsid (asid : Asid) : KFE ct (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_findVspaceForAsid _)

theorem kf_setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : KF ct (setPt (Z := Unit) ptr pt) := by
  unfold setPt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setPt _ _)

theorem kf_storePte (p : ObjRef) (pte : PTE) : KF ct (storePte (Z := Unit) p pte) := by
  unfold storePte; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storePte _ _)

theorem kf_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : KF ct (setPd (Z := Unit) ptr pd) := by
  unfold setPd; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setPd _ _)

theorem kf_storePde (p : ObjRef) (pde : PDE) : KF ct (storePde (Z := Unit) p pde) := by
  unfold storePde; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storePde _ _)

theorem kf_unmapPage (pgsz : VMPageSize) (asid : Asid) (vptr : VSpaceRef) (pptr : ObjRef) : KF ct (unmapPage (Z := Unit) pgsz asid vptr pptr) := by
  unfold unmapPage; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unmapPage _ _ _ _)

theorem kf_performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : KF ct (performPageInvocationUnmap (Z := Unit) cap ctSlot) := by
  unfold performPageInvocationUnmap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageInvocationUnmap _ _)

theorem kf_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : KF ct (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setAsidPool _ _)

theorem kf_flushTable (_pml4Ref : ObjRef) (vptr : VSpaceRef) (ptRef : ObjRef) (asid : Asid) : KF ct (flushTable (Z := Unit) _pml4Ref vptr ptRef asid) := by
  unfold flushTable; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_flushTable _ _ _ _)

theorem kf_setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : KF ct (setPml4 (Z := Unit) ptr pt) := by
  unfold setPml4; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setPml4 _ _)

theorem kf_setOriginal (slot : CslotPtr) (v : Bool) : KF ct (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setOriginal _ _)

theorem kf_updateCdt (f : Cdt → Cdt) : KF ct (updateCdt (Z := Unit) f) := by
  unfold updateCdt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateCdt _)

theorem kf_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : KF ct (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setUntypedCapAsFull _ _ _)

theorem kf_storePml4e (p : ObjRef) (pte : PML4E) : KF ct (storePml4e (Z := Unit) p pte) := by
  unfold storePml4e; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storePml4e _ _)

theorem kf_flushAll (vspace : ObjRef) (asid : Asid) : KF ct (flushAll (Z := Unit) vspace asid) := by
  unfold flushAll; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_flushAll _ _)

theorem kf_unmapPdpt (asid : Asid) (vaddr : VSpaceRef) (pdpt : ObjRef) : KF ct (unmapPdpt (Z := Unit) asid vaddr pdpt) := by
  unfold unmapPdpt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unmapPdpt _ _ _)

theorem kf_setIoportMask (f l : IoPort) (val : Bool) : KF ct (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setIoportMask _ _ _)

theorem kf_invalidatePageStructureCacheAsid (vspace : ObjRef) (asid : Asid) : KF ct (invalidatePageStructureCacheAsid (Z := Unit) vspace asid) := by
  unfold invalidatePageStructureCacheAsid; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_invalidatePageStructureCacheAsid _ _)

theorem kf_unmapPd (asid : Asid) (vaddr : VSpaceRef) (pd : ObjRef) : KF ct (unmapPd (Z := Unit) asid vaddr pd) := by
  unfold unmapPd; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unmapPd _ _ _)

theorem kf_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : KF ct (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_capInsert _ _ _)

theorem kf_portIn (f : MachineMonad Data) : KF ct (portIn (Z := Unit) f) := by
  unfold portIn; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_portIn _)

theorem kf_unmapPageTable (asid : Asid) (vaddr : VSpaceRef) (pt : ObjRef) : KF ct (unmapPageTable (Z := Unit) asid vaddr pt) := by
  unfold unmapPageTable; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unmapPageTable _ _ _)

theorem kf_storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) : KF ct (storeAsidPoolEntry (Z := Unit) poolPtr asid pml4base) := by
  unfold storeAsidPoolEntry; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storeAsidPoolEntry _ _ _)

theorem kf_performPageInvocation (iv : PageInvocation) : KF ct (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageInvocation _)

theorem kf_performPageTableInvocation (iv : PageTableInvocation) : KF ct (performPageTableInvocation (Z := Unit) iv) := by
  unfold performPageTableInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageTableInvocation _)

theorem kf_performPageDirectoryInvocation (iv : PageDirectoryInvocation) : KF ct (performPageDirectoryInvocation (Z := Unit) iv) := by
  unfold performPageDirectoryInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPageDirectoryInvocation _)

theorem kf_performPdptInvocation (iv : PdptInvocation) : KF ct (performPdptInvocation (Z := Unit) iv) := by
  unfold performPdptInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performPdptInvocation _)

theorem kf_performAsidPoolInvocation (iv : AsidPoolInvocation) : KF ct (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performAsidPoolInvocation _)

theorem kf_performIoPortInvocation (i : IoPortInvocation) : KF ct (performIoPortInvocation (Z := Unit) i) := by
  unfold performIoPortInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performIoPortInvocation _)

theorem kf_performIoportControlInvocation (i : IoPortControlInvocation) : KF ct (performIoportControlInvocation (Z := Unit) i) := by
  unfold performIoportControlInvocation; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performIoportControlInvocation _)

theorem kf_performDeriveSubframe (iv : Fl4SubframeInvocation) : KF ct (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performDeriveSubframe _)

theorem kf_performTestAndClearAccessed (_slot : ObjRef) : KF ct (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_performTestAndClearAccessed _)

theorem kf_performPml4Flush (i : Fl4Pml4Invocation) : KF ct (performPml4Flush (Z := Unit) i) := by
  cases i; unfold performPml4Flush; exact kf_flushAll _ _

theorem kf_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : KF ct (threadGet (Z := Unit) f t) := by
  unfold threadGet; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_threadGet' _ _)

theorem kf_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    KF ct (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getSimpleKo' _ _)

theorem kf_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    KF ct (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateSkObjRef' _ _ _ _)

theorem kf_getSchedContext' (q : ObjRef) : KF ct (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getSchedContext' _)

theorem kf_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    KF ct (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateSchedContext' _ _)

theorem kf_replyUnlinkTcb' (t r : ObjRef) (h_ne : t ≠ ct) : KF ct (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_replyUnlinkTcb' _ _ (by assumption))

theorem kf_getThreadState' (t : ObjRef) : KF ct (getThreadState (Z := Unit) t) := by
  unfold getThreadState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getThreadState' _)

theorem kf_cancelIpc' (t : ObjRef) (h_ne : t ≠ ct) : KF ct (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_cancelIpc' _ (by assumption))

theorem kf_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : KF ct (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getSkObjRef' _ _ _)

theorem kf_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : KF ct (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getScObjRef' _ _)

theorem kf_getIrqSlot' (irq : Irq) : KF ct (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getIrqSlot' _)

theorem kf_isFinalCap' (c : Cap) : KF ct (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_isFinalCap' _)

theorem kf_hwAsidInvalidate' (a : Asid) (v : ObjRef) : KF ct (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_hwAsidInvalidate' _ _)

theorem kf_getCurrentCr3' : KF ct (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getCurrentCr3' )

theorem kf_setCurrentCr3' (c : Cr3) : KF ct (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setCurrentCr3' _)

theorem kf_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : KF ct (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setCurrentVspaceRoot' _ _)

theorem kf_setVmRoot' (t : ObjRef) : KF ct (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setVmRoot' _)

theorem kf_freeIoportRange' (f l : IoPort) : KF ct (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_freeIoportRange' _ _)

theorem kf_setIrqState' (i : IrqState) (irq : Irq) : KF ct (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setIrqState' _ _)

theorem kf_deletedIrqHandler' (irq : Irq) : KF ct (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_deletedIrqHandler' _)

theorem kf_lookupIpcBuffer' (b : Bool) (t : ObjRef) : KF ct (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupIpcBuffer' _ _)

theorem kf_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, KF ct (g a b)) :
    ∀ l1 l2, KF ct (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => kf_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kf_zipWithMx' (fun _ _ => ?_) _ _)

theorem kf_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : KF ct (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_storeWordOffs' _ _ _)

theorem kf_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : KF ct (setMrs (Z := Unit) t b m) := by
  unfold setMrs
  intro σ x ⟨⟨tcb, s1⟩, h1, y2, h2, y3, h3, y4, h4, hx⟩
  obtain ⟨e1, e1'⟩ := mem_getsThe' h1
  simp only at e1 e1'
  subst e1'
  have h2 := mem_pure' h2; subst h2
  have h3 := mem_pure' h3; subst h3
  obtain ⟨-, e⟩ := setObject_out h4
  refine Eq.trans ((?_ : FK (ctV ct) _) _ _ hx) ?_
  · kf_auto
  rw [e]; unfold ctV
  simp only [Prod.mk.injEq, true_and]
  rw [Function.update_apply]
  split
  · next hc => subst hc; rw [getTcb_some e1]; simp [tsV]
  · rfl
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setMrs' _ _ _)

theorem kf_setMessageInfo' (t : ObjRef) (i : MessageInfo) : KF ct (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setMessageInfo' _ _)

theorem kf_saveFpuState' (t : ObjRef) : KF ct (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_saveFpuState' _)

theorem kf_loadFpuState' (t : ObjRef) : KF ct (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_loadFpuState' _)

theorem kf_setX64CurrentFpuOwner' (o : Option ObjRef) : KF ct (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setX64CurrentFpuOwner' _)

theorem kf_switchLocalFpuOwner' (o : Option ObjRef) : KF ct (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_switchLocalFpuOwner' _)

theorem kf_getTcbQueue' (d : Domain) (p : Priority) : KF ct (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getTcbQueue' _ _)

theorem kf_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : KF ct (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setTcbQueue' _ _ _)

theorem kf_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : KF ct (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbSchedAction' _ _)

theorem kf_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : KF ct (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getTcbObjRef' _ _)

theorem kf_setSchedulerAction' (a : SchedulerAction) : KF ct (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setSchedulerAction' _)

theorem kf_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : KF ct (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getScRefillSufficient' _ _)

theorem kf_getScRefillReady' (sc : ObjRef) : KF ct (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getScRefillReady' _)

theorem kf_tcbReleaseRemove' (t : ObjRef) : KF ct (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbReleaseRemove' _)

theorem kf_rescheduleRequired' : KF ct (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_rescheduleRequired' )

theorem kf_testReschedule' (t : ObjRef) : KF ct (testReschedule (Z := Unit) t) := by
  unfold testReschedule; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_testReschedule' _)

theorem kf_possibleSwitchTo' (t : ObjRef) : KF ct (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_possibleSwitchTo' _)

theorem kf_tcbEpDequeue' (t e : ObjRef) : KF ct (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbEpDequeue' _ _)

theorem kf_tcbNtfnDequeue' (t n : ObjRef) : KF ct (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbNtfnDequeue' _ _)

theorem kf_isRoundRobin' (sc : ObjRef) : KF ct (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_isRoundRobin' _)

theorem kf_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : KF ct (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateRefillHd' _ _)

theorem kf_getRefillHead' (sc : ObjRef) : KF ct (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getRefillHead' _)

theorem kf_refillPopHead' (sc : ObjRef) : KF ct (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillPopHead' _)

theorem kf_mergeOverlappingRefills' (sc : ObjRef) : KF ct (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_mergeOverlappingRefills' _)

theorem kf_refillHeadOverlappingLoop' (sc : ObjRef) : KF ct (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillHeadOverlappingLoop' _)

theorem kf_refillUnblockCheck' (sc : ObjRef) : KF ct (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillUnblockCheck' _)

theorem kf_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : KF ct (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_ifCondRefillUnblockCheck' _ _ _)

theorem kf_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : KF ct (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem kf_replyUnlinkSc' (sc r : ObjRef) : KF ct (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_replyUnlinkSc' _ _)

theorem kf_schedContextDonate' (sc t : ObjRef) : KF ct (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextDonate' _ _)

theorem kf_schedContextUpdateConsumed' (sc : ObjRef) : KF ct (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUpdateConsumed' _)

theorem kf_replyFromKernel' (t : ObjRef) (x : Data × List Data) : KF ct (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_replyFromKernel' _ _)

theorem kf_setConsumed' (sc t : ObjRef) : KF ct (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setConsumed' _ _)

theorem kf_schedContextCancelYieldTo' (t : ObjRef) : KF ct (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextCancelYieldTo' _)

theorem kf_fpuRelease' (t : ObjRef) : KF ct (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_fpuRelease' _)

theorem kf_deleteAsidPool' (b : Asid) (p : ObjRef) : KF ct (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_deleteAsidPool' _ _)

theorem kf_deleteAsid' (a : Asid) (p : ObjRef) : KF ct (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_deleteAsid' _ _)

theorem kf_archPostCapDeletion' (c : ArchCap) : KF ct (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archPostCapDeletion' _)

theorem kf_postCapDeletion' (c : Cap) : KF ct (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_postCapDeletion' _)

theorem kf_emptySlot' (sl : CslotPtr) (c : Cap) : KF ct (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_emptySlot' _ _)

theorem kf_schedContextMaybeUnbindNtfn' (n : ObjRef) : KF ct (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextMaybeUnbindNtfn' _)

theorem kf_unbindMaybeNotification' (n : ObjRef) : KF ct (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unbindMaybeNotification' _)

theorem kf_replyRemove' (t r : ObjRef) (h_ne : t ≠ ct) : KF ct (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_replyRemove' _ _ (by assumption))

theorem kf_unbindNotification' (t : ObjRef) : KF ct (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unbindNotification' _)

theorem kf_schedContextUnbindTcb' (sc : ObjRef) : KF ct (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUnbindTcb' _)

theorem kf_completeYieldTo' (t : ObjRef) : KF ct (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_completeYieldTo' _)

theorem kf_unbindFromSc' (t : ObjRef) : KF ct (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_unbindFromSc' _)

theorem kf_schedContextUnbindAllTcbs' (sc : ObjRef) : KF ct (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUnbindAllTcbs' _)

theorem kf_schedContextUnbindNtfn' (sc : ObjRef) : KF ct (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUnbindNtfn' _)

theorem kf_schedContextUnbindReply' (sc : ObjRef) : KF ct (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUnbindReply' _)

theorem kf_schedContextUnbindYieldFrom' (sc : ObjRef) : KF ct (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextUnbindYieldFrom' _)

theorem kf_schedContextSetInactive' (sc : ObjRef) : KF ct (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextSetInactive' _)

theorem kf_prepareThreadDelete' (t : ObjRef) : KF ct (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_prepareThreadDelete' _)

theorem kf_archFinaliseCap' (c : ArchCap) (x : Bool) : KF ct (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archFinaliseCap' _ _)

theorem kf_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : KF ct (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_capSwap' _ _ _ _)

theorem kf_capSwapForDelete' (s1 s2 : CslotPtr) : KF ct (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_capSwapForDelete' _ _)

theorem kf_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : KF ct (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_orderedInsert' _ _ _ _)

theorem kf_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : KF ct (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_readyTimesAppend' _ _)

theorem kf_tcbReleaseEnqueue' (t : ObjRef) : KF ct (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbReleaseEnqueue' _)

theorem kf_tcbAppend' (t : ObjRef) (q : List ObjRef) : KF ct (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbAppend' _ _)

theorem kf_postpone' (sc : ObjRef) : KF ct (postpone (Z := Unit) sc) := by
  unfold postpone; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_postpone' _)

theorem kf_threadSetPriority' (t : ObjRef) (p : Priority) : KF ct (threadSetPriority (Z := Unit) t p) := by
  unfold threadSetPriority; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_threadSetPriority' _ _)

theorem kf_reorderEp' (e t : ObjRef) : KF ct (reorderEp (Z := Unit) e t) := by
  unfold reorderEp; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_reorderEp' _ _)

theorem kf_reorderNtfn' (n t : ObjRef) : KF ct (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_reorderNtfn' _ _)

theorem kf_archPostModifyRegisters' (c t : ObjRef) : KF ct (archPostModifyRegisters (Z := Unit) c t) := by
  unfold archPostModifyRegisters; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archPostModifyRegisters' _ _)

theorem kf_schedContextResume' (sc : ObjRef) : KF ct (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextResume' _)

theorem kf_testPossibleSwitchTo' (t : ObjRef) : KF ct (testPossibleSwitchTo (Z := Unit) t) := by
  unfold testPossibleSwitchTo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_testPossibleSwitchTo' _)

theorem kf_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) : KF ct (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_ifSporadicCurScTestRefillUnblockCheck' _)

theorem kfe_rab (p : Cap × CapRef) : KFE ct (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (kf_getCap _)) fun nc => ?_
        split
        · exact kfe_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_rab _)

theorem kfe_resolveAddressBits (p : Cap × CapRef) : KFE ct (resolveAddressBits (Z := Unit) p) := kfe_rab p
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_resolveAddressBits _)

theorem kf_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : KFE ct (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupSlotForThread' _ _)

theorem kf_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : KFE ct (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupCapAndSlot' _ _)

theorem kf_lookupCap' (thread : ObjRef) (ref : CapRef) : KFE ct (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupCap' _ _)

theorem kf_captransferFromWords' (ptr : Word) : KF ct (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_captransferFromWords' _)

theorem kf_loadCapTransfer' (buffer : ObjRef) : KF ct (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_loadCapTransfer' _)

theorem kf_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : KF ct (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_setExtraBadge' _ _ _)

theorem kfe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : KFE ct m) :
    KFE ct (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kfe_lookupErrorOnFailure' _ ?_)

theorem kf_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : KFE ct (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupSlotForCnodeOp' _ _ _ _)

theorem kf_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : KFE ct (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact kf_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupTargetSlot' _ _ _)

theorem kf_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : KF ct (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archPostResetUntyped' _ _)

theorem kf_copyGlobalMappings' (newPm : ObjRef) : KF ct (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_copyGlobalMappings' _)

theorem kf_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : KF ct (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_createCap' _ _ _ _ _)

theorem kf_ensureNoChildren' (cslotPtr : CslotPtr) : KFE ct (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_ensureNoChildren' _)

theorem kf_getRefillTail' (scPtr : ObjRef) : KF ct (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getRefillTail' _)

theorem kf_getRefills' (scPtr : ObjRef) : KF ct (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getRefills' _)

theorem kf_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : KF ct (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillAddTail' _ _)

theorem kf_refillFull' (scPtr : ObjRef) : KF ct (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillFull' _)

theorem kf_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : KF ct (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateRefillTl' _ _)

theorem kf_scheduleUsed' (scPtr : ObjRef) (new : Refill) : KF ct (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_scheduleUsed' _ _)

theorem kf_refillSize' (scPtr : ObjRef) : KF ct (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillSize' _)

theorem kf_refillSingle' (scPtr : ObjRef) : KF ct (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillSingle' _)

theorem kf_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : KF ct (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_chargeEntireHeadRefill' _ _)

theorem kf_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : KF ct (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_mergeNonoverlappingHeadRefill' _)

theorem kf_updateIrqState' (irq : Irq) (irqState : X64IRQState) : KF ct (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_updateIrqState' _ _)

theorem kfe_archInvokeIrqControl' (i : ArchIrqControlInvocation) : KFE ct (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_archInvokeIrqControl' _)

theorem kf_invokeIrqControl' (i : IrqControlInvocation) : KFE ct (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_invokeIrqControl' _)

theorem kfe_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : KFE ct (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_invokeFl4IrqControl' _)

theorem kfe_archDeriveCap' (c : ArchCap) : KFE ct (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_archDeriveCap' _)

theorem kfe_deriveCap' (sl : CslotPtr) (c : Cap) : KFE ct (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kfe_deriveCap' _ _)

theorem kf_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : KF ct (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_makeArchFaultMsg' _ _)

theorem kfe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : KFE ct m) :
    KFE ct (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kfe_unifyFailure' ?_)

theorem kf_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : KFE ct m) :
    KF ct (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kf_emptyOnFailure' ?_)

theorem kf_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : KFE ct m) :
    KF ct (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kf_constOnFailure' _ ?_)

theorem kfe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : KFE ct m) :
    KFE ct (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible refine kfe_capFaultOnFailure' _ _ ?_)

theorem kf_loadWordOffs' (ptr : ObjRef) (offs : Nat) : KF ct (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact kf_doMachineOp _
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_loadWordOffs' _ _)

theorem kf_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : KF ct (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => kf_loadWordOffs' _ _) _)
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getExtraCptrs' _ _)

theorem kf_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : KF ct (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getReceiveSlots' _ _)

theorem kf_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      KF ct (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; kf_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := kf_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    kf_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_transferCapsLoop' _ _ _ _ _ _)

theorem kf_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : KFE ct (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_lookupExtraCaps' _ _ _)

theorem kf_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : KF ct (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_copyMrs' _ _ _ _ _)

theorem kf_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : KF ct (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_transferCaps' _ _ _ _ _)

theorem kf_makeFaultMsg' (f : Fault) (t : ObjRef) : KF ct (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_makeFaultMsg' _ _)

theorem kf_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : KF ct (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_handleOverrun' _ _)

theorem kf_headInsufficientLoop' (scPtr : ObjRef) : KF ct (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_headInsufficientLoop' _)

theorem kf_getMessageInfo' (thread : ObjRef) : KF ct (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getMessageInfo' _)

theorem kf_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : KF ct (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_tcbEpAppend' _ _ _)

theorem kf_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : KF ct (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_doNormalTransfer' _ _ _ _ _ _ _)

theorem kf_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : KF ct (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_doFaultTransfer' _ _ _ _)

theorem kf_bindScReply' (scPtr replyPtr : ObjRef) : KF ct (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_bindScReply' _ _)

theorem kf_isValidTimeoutHandler' (tptr : ObjRef) : KF ct (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_isValidTimeoutHandler' _)

theorem kf_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : KF ct (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_doIpcTransfer' _ _ _ _ _)

theorem kf_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) (h_ne : caller ≠ ct) : KF ct (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_replyPush' _ _ _ _ (by assumption))

theorem kf_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) (h_ne : thread ≠ ct) : KF ct (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_sendIpcBlocked' _ _ _ _ _ _ (by assumption))

theorem kf_refillBudgetCheckRoundRobin' (usage : Ticks) : KF ct (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillBudgetCheckRoundRobin' _)

theorem kf_refillBudgetCheck' (usage : Ticks) : KF ct (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillBudgetCheck' _)

theorem kf_maybeAddEmptyTail' (scPtr : ObjRef) : KF ct (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_maybeAddEmptyTail' _)

theorem kf_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : KF ct (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_maybeDonateSc' _ _)

theorem kf_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : KF ct (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getMrs' _ _ _)

theorem kf_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    KF ct (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_handleFaultReply' _ _ _ _)

theorem kf_returnConsumed' (scPtr : ObjRef) : KF ct (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_returnConsumed' _)

theorem kf_schedContextBindNtfn' (sc ntfn : ObjRef) : KF ct (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_schedContextBindNtfn' _ _)

theorem kf_getScActive' (scPtr : ObjRef) : KF ct (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_getScActive' _)

theorem kf_commitTime' : KF ct (commitTime (Z := Unit) ) := by
  unfold commitTime; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_commitTime' )

theorem kf_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : KF ct (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillNew' _ _ _ _)

theorem kf_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : KF ct (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_refillUpdate' _ _ _ _)

theorem kf_archInvokeIrqHandler' (i : IrqHandlerInvocation) : KF ct (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> kf_auto
macro_rules | `(tactic| kf_leaf) => `(tactic| with_reducible exact kf_archInvokeIrqHandler' _)

end

end

end Fl4Proofs.P3.MidRun
