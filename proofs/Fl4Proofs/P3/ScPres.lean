/-
P3 (DESIGN.md §9), scheduling contexts: **what the spec's scheduling-context
invocations keep** (spec side only).

`PK full o o'`: the kernel object `o` became `o'` without touching what the
CSpace relation reads (CNodes, TCB cap fields), the TCB's `tcb_mcpriority`,
the kind of the object or an SC's size; with `full`, also without touching
the yield-to links (`tcb_yield_to`, `sc_yield_from`) and the call stacks
(`sc_replies`, `reply_sc`, `reply_tcb`). `SOK full σ σ'`: every object of
`σ` is `PK`-related to the one of `σ'` (none where none), and the CDT, the
original-cap flags and the domain schedule are unchanged. `Pres full m`:
every outcome of `m` is `SOK`-related to its start.

The lemmas build `Pres` from the monad's combinators and the object
updates (`threadSet`, `archThreadSet`, `asUser`, `updateSchedContext`,
`updateSkObjRef`, `setObject` of a notification); `SOK.ksub`,
`SOK.cnode`, `SOK.tcb` and friends read off what the CSpace, MCP, yield
and call-stack relations need.
-/
import Fl4Proofs.P3.FinSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- An object step of the scheduling-context invocations (module docstring):
`f.1` keeps the yield-to links, `f.2` the call stacks. -/
def PK (f : Bool × Bool) : KernelObject → KernelObject → Prop
  | .tcb x, .tcb y => y.tcbCtable = x.tcbCtable ∧ y.tcbVtable = x.tcbVtable ∧ y.tcbIpcframe = x.tcbIpcframe ∧
      y.tcbFaultHandler = x.tcbFaultHandler ∧ y.tcbTimeoutHandler = x.tcbTimeoutHandler ∧ y.tcbEpt = x.tcbEpt ∧
      y.tcbMcpriority = x.tcbMcpriority ∧ (f.1 = true → y.tcbYieldTo = x.tcbYieldTo)
  | .schedContext x n, .schedContext y m =>
      m = n ∧ (f.1 = true → y.scYieldFrom = x.scYieldFrom) ∧ (f.2 = true → y.scReplies = x.scReplies)
  | .notification _, .notification _ => True
  | .reply x, .reply y => f.2 = true → y.replySc = x.replySc ∧ y.replyTcb = x.replyTcb
  | .cnode r cs, o => o = .cnode r cs
  | .endpoint x, o => o = .endpoint x
  | .archObj a, o => o = .archObj a
  | _, _ => False

theorem PK.refl (f : Bool × Bool) (o : KernelObject) : PK f o o := by
  cases o <;> simp [PK]

theorem PK.trans {f : Bool × Bool} {a b c : KernelObject} (h1 : PK f a b) (h2 : PK f b c) : PK f a c := by
  cases a <;> cases b <;> simp only [PK, reduceCtorEq] at h1 <;> (try subst h1) <;> cases c <;>
    simp only [PK, reduceCtorEq] at h2 ⊢
  all_goals first
    | trivial
    | exact h2
    | exact h2.trans h1
    | (obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1; obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
       exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
         fun h => (b8 h).trans (a8 h)⟩)
    | (obtain ⟨a1, a2, a3⟩ := h1; obtain ⟨b1, b2, b3⟩ := h2
       exact ⟨b1.trans a1, fun h => (b2 h).trans (a2 h), fun h => (b3 h).trans (a3 h)⟩)
    | (intro h; exact ⟨(h2 h).1.trans (h1 h).1, (h2 h).2.trans (h1 h).2⟩)

/-- Keeping more implies keeping less. -/
theorem PK.weaken {f f' : Bool × Bool} {a b : KernelObject} (h : PK f a b) (h1 : f'.1 = true → f.1 = true)
    (h2 : f'.2 = true → f.2 = true) : PK f' a b := by
  cases a <;> cases b <;> simp only [PK, reduceCtorEq] at h ⊢
  all_goals first
    | trivial
    | exact h
    | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, fun e => h.2.2.2.2.2.2.2 (h1 e)⟩
    | exact ⟨h.1, fun e => h.2.1 (h1 e), fun e => h.2.2 (h2 e)⟩
    | exact fun e => h (h2 e)

/-- `PK` lifted to optional objects: none stays none. -/
def ORel (f : Bool × Bool) : Option KernelObject → Option KernelObject → Prop
  | none, none => True
  | some a, some b => PK f a b
  | _, _ => False

theorem ORel.refl (f : Bool × Bool) (o : Option KernelObject) : ORel f o o := by
  cases o <;> simp [ORel, PK.refl]

theorem ORel.trans {f : Bool × Bool} {a b c : Option KernelObject} (h1 : ORel f a b) (h2 : ORel f b c) : ORel f a c := by
  cases a <;> cases b <;> cases c <;> simp only [ORel] at h1 h2 ⊢
  exact h1.trans h2

/-- **What the scheduling-context invocations keep** (module docstring). -/
structure SOK (f : Bool × Bool) (σ σ' : State Unit) : Prop where
  kh : ∀ p, ORel f (σ.kheap p) (σ'.kheap p)
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  dl : σ'.domainList = σ.domainList
  dsi : σ'.domainStartIndex = σ.domainStartIndex

theorem SOK.refl (f : Bool × Bool) (σ : State Unit) : SOK f σ σ := ⟨fun p => ORel.refl f _, rfl, rfl, rfl, rfl⟩

theorem SOK.trans {f : Bool × Bool} {σ1 σ2 σ3 : State Unit} (h1 : SOK f σ1 σ2) (h2 : SOK f σ2 σ3) : SOK f σ1 σ3 :=
  ⟨fun p => (h1.kh p).trans (h2.kh p), h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, h2.dl.trans h1.dl,
    h2.dsi.trans h1.dsi⟩

theorem SOK.weaken {f f' : Bool × Bool} {σ σ' : State Unit} (h : SOK f σ σ') (h1 : f'.1 = true → f.1 = true)
    (h2 : f'.2 = true → f.2 = true) : SOK f' σ σ' := by
  refine ⟨fun p => ?_, h.cdt, h.orig, h.dl, h.dsi⟩
  have := h.kh p
  revert this; cases σ.kheap p <;> cases σ'.kheap p <;> simp only [ORel] <;>
    first | exact id | exact fun h' => PK.weaken h' h1 h2

/-- An update of `σ` at `p` with `o'`, `PK`-related to the object there. -/
theorem SOK.upd {f : Bool × Bool} {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h : PK f o o') : SOK f σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  refine ⟨fun q => ?_, rfl, rfl, rfl, rfl⟩
  by_cases e : q = p
  · subst e; simp only [Function.update_self, hk, ORel]; exact h
  · simp only [Function.update_of_ne e]; exact ORel.refl f _

/-- Every outcome of `m` is `SOK`-related to its start. -/
def Pres (f : Bool × Bool) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SOK f σ x.2

theorem Pres.of_eq {f : Bool × Bool} {α : Type} {m : NonDet (State Unit) α} (hP : Pres f m) {σ σ' : State Unit}
    {a : α} (h : m σ = ({(a, σ')}, False)) : SOK f σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

section Comb

theorem Pres.weaken {f f' : Bool × Bool} {α : Type} {m : NonDet (State Unit) α} (h : Pres f m)
    (h1 : f'.1 = true → f.1 = true) (h2 : f'.2 = true → f.2 = true) : Pres f' m :=
  fun σ x hx => (h σ x hx).weaken h1 h2

variable {f : Bool × Bool}

theorem pres_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : Pres f m)
    (hg : ∀ a, Pres f (g a)) : Pres f (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem pres_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : Pres f m)
    (hg : ∀ a, Pres f (g a)) : Pres f (NonDet.bind m g) := pres_bind hm hg

theorem pres_pure {α : Type} (a : α) : Pres f (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SOK.refl f σ

theorem pres_pure' {α : Type} (a : α) : Pres f (NonDet.pure a : NonDet (State Unit) α) := pres_pure a

theorem pres_gets {α : Type} (g : State Unit → α) : Pres f (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SOK.refl f σ

theorem pres_get : Pres f (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SOK.refl f σ

theorem pres_assert (P : Prop) : Pres f (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact SOK.refl f σ

theorem pres_fail {α : Type} : Pres f (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem pres_assertOpt {α : Type} (o : Option α) : Pres f (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact pres_fail
  · exact pres_pure' _

theorem pres_getsThe {α : Type} (g : State Unit → Option α) : Pres f (NonDet.getsThe g) := by
  intro σ x hx; exact pres_assertOpt (g σ) σ x hx

theorem pres_selectF {α : Type} (S : Set α × Prop) : Pres f (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SOK.refl f σ

theorem pres_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : Pres f m1)
    (h2 : Pres f m2) : Pres f (if P then m1 else m2) := by
  split <;> assumption

theorem pres_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : Pres f m) :
    Pres f (NonDet.when P m) := by
  unfold NonDet.when; exact pres_ite P h (pres_pure' _)

theorem pres_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : Pres f m) :
    Pres f (NonDet.unless P m) := by
  unfold NonDet.unless; exact pres_ite P (pres_pure' _) h

theorem pres_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, Pres f (g a)) (o : Option α) :
    Pres f (NonDet.maybeM g o) := by
  cases o
  · exact pres_pure' _
  · exact h _

theorem pres_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : Pres f m) :
    Pres f (NonDet.liftM g m) := pres_bind' h fun _ => pres_pure' _

theorem pres_modify {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).cdt = σ.cdt ∧ (g σ).isOriginalCap = σ.isOriginalCap ∧
      (g σ).domainList = σ.domainList ∧ (g σ).domainStartIndex = σ.domainStartIndex) :
    Pres f (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg σ
  exact ⟨fun p => by rw [e1]; exact ORel.refl f _, e2, e3, e4, e5⟩

theorem pres_get_put {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).cdt = σ.cdt ∧ (g σ).isOriginalCap = σ.isOriginalCap ∧
      (g σ).domainList = σ.domainList ∧ (g σ).domainStartIndex = σ.domainStartIndex) :
    Pres f (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg σ
  exact ⟨fun p => by rw [e1]; exact ORel.refl f _, e2, e3, e4, e5⟩

theorem pres_getObject (p : ObjRef) : Pres f (getObject (Z := Unit) p) := pres_getsThe _

theorem pres_doMachineOp {α : Type} (mop : NonDet MachineState α) : Pres f (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine pres_bind (pres_gets _) (fun _ => pres_bind (pres_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact pres_bind (pres_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl⟩)) (fun _ => pres_pure _)

theorem pres_doExtendedOp (eop : DetExtMonad Unit) : Pres f (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine pres_bind pres_get (fun _ => pres_bind (pres_selectF _) (fun _ => ?_))
  split
  exact pres_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem pres_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, Pres f (B r)) (r : α) : Pres f (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact SOK.refl f _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem pres_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, Pres f (g a)) (xs : List α) :
    Pres f (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact pres_pure' _
  | cons a xs' ih => exact pres_bind' (h a) fun _ => ih

theorem pres_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, Pres f (g a)) (xs : List α) :
    Pres f (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact pres_pure' _
  | cons a xs' ih => exact pres_bind' (h a) fun _ => pres_bind' ih fun _ => pres_pure' _

theorem pres_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, Pres f (g a b)) :
    ∀ (xs : List α) (ys : List β), Pres f (NonDet.zipWithMx g xs ys)
  | a :: xs, b :: ys => by
    unfold NonDet.zipWithMx; exact pres_bind' (h a b) fun _ => pres_zipWithMx h xs ys
  | [], _ => by unfold NonDet.zipWithMx; exact pres_pure' _
  | _ :: _, [] => by unfold NonDet.zipWithMx; exact pres_pure' _

end Comb

/-! ## Object updates -/

section Obj
variable {f : Bool × Bool}

/-- The outcome of `set_object`: the object there had the same type. -/
theorem setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧ x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨k, hk, hty, rfl⟩

/-- `set_object` of an object that every object of its type steps to. -/
theorem pres_setObject {p : ObjRef} {o : KernelObject} (h : ∀ k, aType k = aType o → PK f k o) :
    Pres f (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_mem hx
  rw [e]; exact SOK.upd hk (h k hty)

/-- `set_object` of a notification. -/
theorem pres_setObject_ntfn (p : ObjRef) (n : Notification) : Pres f (setObject (Z := Unit) p (.notification n)) :=
  pres_setObject fun k hk => by
    cases k <;> simp only [aType, reduceCtorEq] at hk <;> first | trivial | (split_ifs at hk)

theorem getsThe_getTcb_mem {σ : State Unit} {p : ObjRef} {y : Tcb × State Unit}
    (hy : y ∈ (NonDet.getsThe (getTcb (Z := Unit) p) σ).1) : σ.kheap p = some (.tcb y.1) ∧ y.2 = σ := by
  unfold NonDet.getsThe getTcb readObject at hy
  cases h : σ.kheap p with
  | none => rw [h] at hy; exact hy.elim
  | some k =>
    rw [h] at hy
    cases k <;> simp only [NonDet.assertOpt] at hy
    all_goals first | exact hy.elim | skip
    rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩

/-- Reading a TCB, then writing it back changed by `g`. -/
theorem pres_tcb_rw {p : ObjRef} {g : Tcb → Tcb} (hg : ∀ x, PK f (.tcb x) (.tcb (g x))) :
    Pres f (NonDet.getsThe (getTcb (Z := Unit) p) >>= fun tcb => setObject p (.tcb (g tcb))) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact SOK.upd hk (hg _)

theorem pres_threadSet {g : Tcb → Tcb} (hg : ∀ x, PK f (.tcb x) (.tcb (g x))) (p : ObjRef) :
    Pres f (threadSet (Z := Unit) g p) := pres_tcb_rw hg

theorem pres_archThreadSet (g : ArchTcb → ArchTcb) (p : ObjRef) : Pres f (archThreadSet (Z := Unit) g p) :=
  pres_tcb_rw (g := fun tcb => { tcb with tcbArch := g tcb.tcbArch }) fun x => by simp [PK]

theorem pres_asUser {α : Type} (p : ObjRef) (u : UserMonad α) : Pres f (asUser (Z := Unit) p u) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨-, e3⟩ := hy3
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  simp only at e3 hy5
  rw [e3] at hy5
  obtain ⟨k, hk', -, e⟩ := setObject_mem hy5
  rw [hk] at hk'; cases hk'
  rw [e]; exact SOK.upd hk (by simp [PK])

theorem getObject_mem {σ : State Unit} {p : ObjRef} {y : KernelObject × State Unit}
    (hy : y ∈ (getObject (Z := Unit) p σ).1) : σ.kheap p = some y.1 ∧ y.2 = σ := by
  unfold getObject NonDet.getsThe readObject at hy
  cases h : σ.kheap p with
  | none => rw [h] at hy; exact hy.elim
  | some k => rw [h] at hy; rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩

theorem pres_updateSchedContext {g : SchedContext → SchedContext}
    (hg : ∀ x n, PK f (.schedContext x n) (.schedContext (g x) n)) (p : ObjRef) :
    Pres f (updateSchedContext (Z := Unit) p g) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst hs
  cases o
  all_goals first | exact hx.elim | skip
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact SOK.upd hk (hg _ _)

theorem partialInv_eq {α β : Type} [Nonempty α] {g : α → β} {b : β} {a : α} (h : partialInv g b = some a) :
    g a = b := by
  unfold partialInv at h
  split_ifs at h with hu
  cases h
  unfold The; rw [dite_eq_left hu]; exact (Classical.choose_spec hu).1

theorem pres_updateSkObjRef {α : Type} [Nonempty α] {C : α → KernelObject}
    {g : (Option ObjRef → Option ObjRef) → α → α} {new : Option ObjRef}
    (hg : ∀ a, PK f (C a) (C (g (fun _ => new) a))) (ref : ObjRef) :
    Pres f (updateSkObjRef (Z := Unit) C g ref new) := by
  intro σ x ⟨y, hy, hx⟩
  -- `get_simple_ko`
  obtain ⟨⟨o, σ1⟩, hy1, hy⟩ := hy
  obtain ⟨hk, hs⟩ := getObject_mem hy1
  simp only at hk hs; subst hs
  obtain ⟨y2, hy2, hy⟩ := hy
  obtain ⟨-, rfl⟩ := hy2
  cases he : partialInv C o with
  | none => simp only [he] at hy; exact hy.elim
  | some e =>
    simp only [he] at hy
    rw [Set.mem_singleton_iff.1 hy] at hx
    have hC := partialInv_eq he
    subst hC
    -- `set_simple_ko`
    obtain ⟨z1, hz1, hx⟩ := hx
    obtain ⟨hk1, hs1⟩ := getObject_mem hz1
    obtain ⟨z2, hz2, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz2
    obtain ⟨z3, hz3, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz3
    simp only at hx
    rw [hs1] at hx
    obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
    rw [e']; exact SOK.upd hk (hg e)

/-- `Pres` from states satisfying `P`. -/
def PresAt (f : Bool × Bool) {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → SOK f σ x.2

theorem PresAt.of_pres {α : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} (h : Pres f m) :
    PresAt f P m := fun σ _ x hx => h σ x hx

theorem presAt_pure_bind {α β : Type} {P : State Unit → Prop} (a : α) {k : α → NonDet (State Unit) β}
    (h : PresAt f P (k a)) : PresAt f P (pure a >>= k) := by
  intro σ hP x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ hP x hx

/-- Writing back the TCB that is there, `PK`-changed. -/
theorem presAt_setObject_tcb_bind {β : Type} {p : ObjRef} {x y : Tcb} {k : Unit → NonDet (State Unit) β}
    (hxy : PK f (.tcb x) (.tcb y)) (hk : ∀ u, Pres f (k u)) :
    PresAt f (fun σ => σ.kheap p = some (.tcb x)) (setObject p (.tcb y) >>= k) := by
  intro σ hP z ⟨w, hw, hz⟩
  obtain ⟨o, ho, -, e⟩ := setObject_mem hw
  rw [hP] at ho; cases ho
  rw [e] at hz
  exact (SOK.upd hP hxy).trans (hk w.1 _ z hz)

theorem pres_getTcb_bind {β : Type} {p : ObjRef} {m : Tcb → NonDet (State Unit) β}
    (h : ∀ x, PresAt f (fun σ => σ.kheap p = some (.tcb x)) (m x)) :
    Pres f (NonDet.getsThe (getTcb (Z := Unit) p) >>= m) := by
  intro σ z ⟨y, hy, hz⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hz
  exact h y.1 σ hk z hz

end Obj

end

end Fl4Proofs.P3.Sched
