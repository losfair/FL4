/-
P3 (DESIGN.md §9), scheduler: **the arch thread switch up to the FPU**
(KENTRY-PLAN.md sch4 (A)). Supersedes `ArchKeeps`/`ArchSw` (ScSwitchTo,
ScScheduleTop) for the top chain: their `σ'.kheap = σ.kheap` is FALSE
whenever the spec has an FPU owner (sch3).

The spec's `arch_switch_to_thread` (l4v `Arch_A.X64_A.arch_switch_to_thread`
= `set_vm_root t; lazy_fpu_restore t`) switches the FPU owner eagerly:
unless `t` has `fpuDisabled` or already owns the FPU,
`switch_local_fpu_owner (Some t)` saves the machine FPU image into the old
owner's `tcbArch` (`as_user owner (setFPUState v)`: the registers kept),
reads `t`'s image (`as_user t getFPUState`: `t`'s TCB rewritten with the
same context) and moves the `tcbCurFpu` ghost flag (`set_x64_current_fpu_owner`).
FL4 (fl4-arch-x86_64 `fpu.rs`) keeps the registers of the last thread that
ran with the FPU live until another such thread runs or traps (#NM,
`lazy_load`), each TCB's XSAVE image at `layout::tcb::FPU` in FL4's store;
`vspace::set_vm_root` touches the arch state only (`a.set_vspace`). No
relation reads the spec's saved FPU image or `tcbCurFpu` (relations read
TCBs' registers `userRegs` only; XTopFpuRel, XTopJointFpu), so the
correspondence is the frame below, not an FPU invariant (none exists: user
code runs between the save and the switch).

* `TcbFpuEq y x`: `y` is `x` but for `tcbArch`, with the registers kept;
  `HeapEqUpToFpu σ σ'`: the heaps equal but for `TcbFpuEq` TCBs (refl,
  trans, `of_eq`, `eq_trans`, `trans_eq`, `tcb`, `tcb_back`, `ntcb`).
* Frames: `Inv.fpu`, `NSC.fpu`, `schedulable_fpu`, `OffOK.fpu`,
  `IdleOK.fpu`, `SzKeep.fpu`, `newcur_ofF`, `newcur_of2F`, `RunW.of_new2F`.
* `FpuOwnOK σ` [J] (l4v X64 `valid_cur_fpu`: the current FPU owner is a
  TCB): what makes the spec's save to the owner not fail (`as_user`/
  `arch_thread_set` of a non-TCB fail). `OW m`: a spec computation keeps
  the FPU owner (the DI framework of ScNextDomB; `ow_awaken`,
  `ow_tcbSchedAction`); `FpuOwnOK.of`.
* `ArchKeepsF` (`ArchKeeps` with `HeapEqUpToFpu`), `ArchSwF` [P]: `ArchSw`
  with `ArchKeepsF` and `FpuOwnOK σ` in the thread part (the idle part,
  `set_vm_root` of the idle thread only, unchanged); `ArchSw.toF`.
* `switch_to_thread_refinesF`, `choose_thread_refinesF`: the posts with
  `HeapEqUpToFpu σ σ'` in place of `σ'.kheap = σ.kheap`.
-/
import Fl4Proofs.P3.ScYieldTo
import Fl4Proofs.P3.ScPres
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-! ## The heap up to the FPU -/

/-- `y` is `x` but for its arch part, the registers kept. -/
def TcbFpuEq (y x : Tcb) : Prop :=
  { y with tcbArch := default } = { x with tcbArch := default } ∧
    y.tcbArch.tcbContext.userRegs = x.tcbArch.tcbContext.userRegs

theorem TcbFpuEq.refl (x : Tcb) : TcbFpuEq x x := ⟨rfl, rfl⟩

theorem TcbFpuEq.trans {x y z : Tcb} (h1 : TcbFpuEq z y) (h2 : TcbFpuEq y x) : TcbFpuEq z x :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem TcbFpuEq.st {x y : Tcb} (h : TcbFpuEq y x) : y.tcbState = x.tcbState := by have e := congrArg Tcb.tcbState h.1; exact e
theorem TcbFpuEq.sc {x y : Tcb} (h : TcbFpuEq y x) : y.tcbSchedContext = x.tcbSchedContext :=
  by have e := congrArg Tcb.tcbSchedContext h.1; exact e
theorem TcbFpuEq.flt {x y : Tcb} (h : TcbFpuEq y x) : y.tcbFault = x.tcbFault := by have e := congrArg Tcb.tcbFault h.1; exact e

theorem TcbFpuEq.eq {x y : Tcb} (h : TcbFpuEq y x) : y = { x with tcbArch := y.tcbArch } := by
  obtain ⟨h1, -⟩ := h
  cases x; cases y; cases h1; rfl

/-- **The heap up to TCBs' FPU part** (module docstring). -/
def HeapEqUpToFpu (σ σ' : State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ TcbFpuEq y x

theorem HeapEqUpToFpu.refl (σ : State Unit) : HeapEqUpToFpu σ σ := fun _ => Or.inl rfl

theorem HeapEqUpToFpu.of_eq {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : HeapEqUpToFpu σ σ' :=
  fun p => Or.inl (congrFun h p)

section
variable {σ σ' : State Unit} (h : HeapEqUpToFpu σ σ')
include h

theorem HeapEqUpToFpu.tcb {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ TcbFpuEq y x := by
  rcases h p with e | ⟨a, b, ha, hb, e⟩
  · exact ⟨x, e.trans hk, TcbFpuEq.refl x⟩
  · rw [hk] at ha; cases ha; exact ⟨b, hb, e⟩

theorem HeapEqUpToFpu.tcb_back {p : ObjRef} {y : Tcb} (hk : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ TcbFpuEq y x := by
  rcases h p with e | ⟨a, b, ha, hb, e⟩
  · exact ⟨y, by rw [← e]; exact hk, TcbFpuEq.refl y⟩
  · rw [hk] at hb; cases hb; exact ⟨a, ha, e⟩

theorem HeapEqUpToFpu.ntcb {p : ObjRef} {o : KernelObject} (ho : ∀ x, o ≠ .tcb x) :
    σ'.kheap p = some o ↔ σ.kheap p = some o := by
  rcases h p with e | ⟨a, b, ha, hb, -⟩
  · rw [e]
  · rw [ha, hb]; constructor <;> intro h' <;> cases h' <;> exact absurd rfl (ho _)

theorem HeapEqUpToFpu.sc {p : ObjRef} {y : SchedContext} {n : Nat} :
    σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n) :=
  h.ntcb fun _ e => by cases e

end

theorem HeapEqUpToFpu.trans {σ1 σ2 σ3 : State Unit} (h1 : HeapEqUpToFpu σ1 σ2) (h2 : HeapEqUpToFpu σ2 σ3) :
    HeapEqUpToFpu σ1 σ3 := by
  intro p
  rcases h2 p with e2 | ⟨b, c, hb, hc, e2⟩
  · rcases h1 p with e1 | r1
    · exact Or.inl (e2.trans e1)
    · obtain ⟨a, b, ha, hb, e⟩ := r1; exact Or.inr ⟨a, b, ha, e2.trans hb, e⟩
  · obtain ⟨a, ha, e1⟩ := h1.tcb_back hb
    exact Or.inr ⟨a, c, ha, hc, e2.trans e1⟩

theorem HeapEqUpToFpu.eq_trans {σ1 σ2 σ3 : State Unit} (h1 : σ2.kheap = σ1.kheap) (h2 : HeapEqUpToFpu σ2 σ3) :
    HeapEqUpToFpu σ1 σ3 := (HeapEqUpToFpu.of_eq h1).trans h2

theorem HeapEqUpToFpu.trans_eq {σ1 σ2 σ3 : State Unit} (h1 : HeapEqUpToFpu σ1 σ2) (h2 : σ3.kheap = σ2.kheap) :
    HeapEqUpToFpu σ1 σ3 := h1.trans (HeapEqUpToFpu.of_eq h2)

/-! ## Frames -/

theorem Inv.fpu {σ σ' : State Unit} (hI : Inv σ) (h : HeapEqUpToFpu σ σ')
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    Inv σ' := by
  refine hI.tcbView (fun p => ?_) hq hr ht
  rcases h p with e | ⟨a, b, ha, hb, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨a, b, ha, hb, e.st, e.sc, Or.inl e.flt⟩

theorem NSC.fpu {N C : Set U64} {σ σ' : State Unit} (hN : NSC N C σ) (h : HeapEqUpToFpu σ σ') : NSC N C σ' :=
  fun n hn x p hx hp => hN n hn x p ((h.ntcb fun _ e => by cases e).1 hx) hp

theorem SzKeep.fpu {σ σ' : State Unit} (h : HeapEqUpToFpu σ σ') : SzKeep σ σ' :=
  fun p x n hp => ⟨x, h.sc.1 hp⟩

theorem schedulable_fpu {σ σ' : State Unit} (h : HeapEqUpToFpu σ σ') (e2 : σ'.releaseQueue = σ.releaseQueue)
    (u : ObjRef) : schedulable u σ' = schedulable u σ := by
  have hsc : ∀ p, scsOf σ' p = scsOf σ p := by
    intro p
    rcases h p with e | ⟨a, b, ha, hb, e⟩
    · simp only [scsOfKh, optMap, e]
    · simp only [scsOfKh, optMap, ha, hb]; rfl
  unfold Fl4Spec.schedulable
  apply decide_eq_decide.2
  rw [e2]
  rcases h u with e | ⟨a, b, ha, hb, e⟩
  · simp only [optPred, optMapSome, optMap, tcbsOfKh, e, hsc]
  · have h1 : tcbsOf σ u = some a := by simp only [tcbsOfKh, optMap, ha]; rfl
    have h2 : tcbsOf σ' u = some b := by simp only [tcbsOfKh, optMap, hb]; rfl
    simp only [optPred, optMapSome, optMap, h1, h2, hsc]
    rw [e.eq]

theorem OffOK.fpu {σ σ' : State Unit} (h : OffOK σ) (hk : HeapEqUpToFpu σ σ') (hcs : σ'.curSc = σ.curSc)
    (hcn : σ'.consumedTime = σ.consumedTime) (htm : σ'.curTime = σ.curTime)
    (hisc : σ'.idleSc = σ.idleSc := by first | rfl | assumption) : OffOK σ' := by
  intro h0 y n hy ha
  rw [hcn] at h0 ⊢; rw [htm]; rw [hcs] at hy; rw [hcs, hisc] at ha
  exact h h0 y n (hk.sc.1 hy) ha

theorem IdleOK.fpu {σ σ' : State Unit} (h : IdleOK σ) (hid : σ'.idleThread = σ.idleThread)
    (hk : HeapEqUpToFpu σ σ')
    (hr : σ.idleThread ∈ σ'.releaseQueue → σ.idleThread ∈ σ.releaseQueue)
    (hisc : σ'.idleSc = σ.idleSc := by first | rfl | assumption) : IdleOK σ' := by
  obtain ⟨x, h1, h2, h3, h4⟩ := h
  obtain ⟨y, hy, e⟩ := hk.tcb h1
  exact ⟨y, by rw [hid]; exact hy, by rw [hisc, e.sc]; exact h2, by rw [e.st]; exact h3,
    fun hm => h4 (hr (hid ▸ hm))⟩

theorem RunW.of_new2F {σ σ3 : State Unit}
    (h : σ3.curThread = σ.idleThread ∨ schedulable σ3.curThread σ = true)
    (hk : HeapEqUpToFpu σ σ3) (hid : σ3.idleThread = σ.idleThread) : RunW σ3 := by
  rcases h with h | h
  · exact Or.inr (h.trans hid.symm)
  · obtain ⟨x, scp, y, n, h1, h2, h3, -⟩ := schedulable_inv h
    refine Or.inl fun x' hx' => ?_
    obtain ⟨x0, hx0, e⟩ := hk.tcb_back hx'
    rw [h1] at hx0; cases hx0; rw [e.st]; exact h3

/-- `newcur_of` up to the FPU. -/
theorem newcur_ofF {σ σ' : State Unit} (h : σ'.curThread = σ.idleThread ∨ schedulable σ'.curThread σ = true ∨
      σ'.curThread = σ.curThread)
    (hk : HeapEqUpToFpu σ σ') (hr : σ'.releaseQueue = σ.releaseQueue) (hId : IdleOK σ) (hC : CurInv σ)
    (hisc : σ'.idleSc = σ.idleSc := by first | rfl | assumption) :
    ∃ xt scp, σ'.kheap σ'.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      NotIpcBlk xt.tcbState ∧ σ'.curThread ∉ σ'.releaseQueue ∧
      (scp ≠ σ'.idleSc → ∀ x n, σ'.kheap scp = some (.schedContext x n) → scActive x = true) := by
  obtain ⟨xt, scp, h1, h2, h3, h4, h5⟩ := newcur_of (σ' := { σ' with kheap := σ.kheap }) h rfl hr hId hC hisc
  obtain ⟨y, hy, e⟩ := hk.tcb h1
  exact ⟨y, scp, hy, by rw [e.sc]; exact h2, by rw [e.st]; exact h3, h4,
    fun hne x n hx => h5 hne x n (hk.sc.1 hx)⟩

/-- `newcur_of2` up to the FPU. -/
theorem newcur_of2F {σ σ' : State Unit} (h : σ'.curThread = σ.idleThread ∨ schedulable σ'.curThread σ = true)
    (hk : HeapEqUpToFpu σ σ') (hr : σ'.releaseQueue = σ.releaseQueue) (hId : IdleOK σ)
    (hisc : σ'.idleSc = σ.idleSc := by first | rfl | assumption) :
    ∃ xt scp, σ'.kheap σ'.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
      NotIpcBlk xt.tcbState ∧ σ'.curThread ∉ σ'.releaseQueue ∧
      (scp ≠ σ'.idleSc → ∀ x n, σ'.kheap scp = some (.schedContext x n) → scActive x = true) := by
  obtain ⟨xt, scp, h1, h2, h3, h4, h5⟩ := newcur_of2 (σ' := { σ' with kheap := σ.kheap }) h rfl hr hId hisc
  obtain ⟨y, hy, e⟩ := hk.tcb h1
  exact ⟨y, scp, hy, by rw [e.sc]; exact h2, by rw [e.st]; exact h3, h4,
    fun hne x n hx => h5 hne x n (hk.sc.1 hx)⟩

/-! ## The FPU owner -/

/-- **The current FPU owner is a TCB** [J] (l4v X64 `valid_cur_fpu`, part of
`valid_arch_state`: a reachable-state invariant, taken at the kernel entry
only and carried by the scheduling proofs; preserved by every spec step: a TCB is only deleted
after `fpu_release`, and only `lazy_fpu_restore`/`switch_local_fpu_owner`
set the owner, to a TCB or none). -/
def FpuOwnOK (σ : State Unit) : Prop :=
  ∀ o, σ.archState.x64CurrentFpuOwner = some o → ∃ x, σ.kheap o = some (.tcb x)

theorem FpuOwnOK.of {σ σ' : State Unit} (h : FpuOwnOK σ)
    (ho : σ'.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner) (hk : σ'.kheap = σ.kheap) :
    FpuOwnOK σ' := fun o e => by rw [hk]; exact h o (by rw [← ho]; exact e)


/-- Every outcome keeps the FPU owner. -/
def OW {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner

theorem OW.of_eq {α : Type} {m : NonDet (State Unit) α} (h : OW m) {σ σ' : State Unit} {a : α} {X : Prop}
    (he : m σ = ({(a, σ')}, X)) : σ'.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner :=
  h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)

theorem ow_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : OW m)
    (hg : ∀ a, OW (g a)) : OW (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm σ y hy)

theorem ow_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : OW m)
    (hg : ∀ a, OW (g a)) : OW (NonDet.bind m g) := ow_bind hm hg

theorem ow_pure {α : Type} (a : α) : OW (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem ow_pure' {α : Type} (a : α) : OW (NonDet.pure a : NonDet (State Unit) α) := ow_pure a

theorem ow_gets {α : Type} (g : State Unit → α) : OW (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem ow_get : OW (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem ow_assert (P : Prop) : OW (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem ow_fail {α : Type} : OW (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem ow_assertOpt {α : Type} (o : Option α) : OW (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact ow_fail
  · exact ow_pure' _

theorem ow_getsThe {α : Type} (g : State Unit → Option α) : OW (NonDet.getsThe g) := by
  intro σ x hx; exact ow_assertOpt (g σ) σ x hx

theorem ow_selectF {α : Type} (S : Set α × Prop) : OW (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem ow_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : OW m1)
    (h2 : OW m2) : OW (if P then m1 else m2) := by
  split <;> assumption

theorem ow_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : OW m) :
    OW (NonDet.when P m) := by
  unfold NonDet.when; exact ow_ite P h (ow_pure' _)

theorem ow_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, OW (g a)) (o : Option α) :
    OW (NonDet.maybeM g o) := by
  cases o
  · exact ow_pure' _
  · exact h _

theorem ow_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner) :
    OW (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem ow_setObject (p : ObjRef) (o : KernelObject) : OW (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := Sched.setObject_mem hx
  rw [e]

theorem ow_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, OW (B r)) (r : α) : OW (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => rfl
  | step _ hm _ ih => exact ih.trans (hB _ _ _ hm)

theorem ow_doExtendedOp (eop : DetExtMonad Unit) : OW (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine ow_bind ow_get (fun _ => ow_bind (ow_selectF _) (fun _ => ?_))
  split
  exact ow_modify (fun σ => rfl)

/-- One step of a `OW` proof. -/
macro "ow_step" : tactic => `(tactic| first
  | with_reducible exact ow_pure _ | with_reducible exact ow_pure' _ | with_reducible exact ow_fail
  | with_reducible exact ow_gets _ | with_reducible exact ow_get
  | with_reducible exact ow_assert _ | with_reducible exact ow_assertOpt _
  | with_reducible exact ow_getsThe _ | with_reducible exact ow_selectF _
  | with_reducible exact ow_setObject _ _ | with_reducible exact ow_getObject _ | with_reducible exact ow_doExtendedOp _
  | ((with_reducible apply ow_modify); intro _; rfl)
  | (with_reducible refine ow_bind ?_ (fun _ => ?_))
  | (with_reducible refine ow_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ow_ite) | (with_reducible apply ow_when)
  | (with_reducible refine ow_maybeM (fun _ => ?_) _)
  | (with_reducible refine ow_whileLoop (fun _ => ?_) _)
  | split
  | (dsimp only))

theorem ow_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : OW (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat ow_step

theorem ow_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    OW (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine ow_bind (ow_threadGet _ _) fun _ => ow_bind (ow_threadGet _ _) fun _ => ?_
  repeat ow_step

theorem ow_getObject (p : ObjRef) : OW (getObject (Z := Unit) p) := ow_getsThe _

theorem ow_getSchedContext (p : ObjRef) : OW (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine ow_bind (ow_getObject p) fun k => ?_
  split
  · exact ow_pure _
  · exact ow_fail

theorem ow_rescheduleRequired : OW (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  repeat (first | with_reducible exact ow_threadGet _ _ | with_reducible exact ow_getSchedContext _ | with_reducible exact ow_tcbSchedAction _ _ | ow_step)

theorem ow_tcbReleaseRemove (t : ObjRef) : OW (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue
  repeat (first | with_reducible exact ow_threadGet _ _ | with_reducible exact ow_getSchedContext _ | with_reducible exact ow_tcbSchedAction _ _ | ow_step)

theorem ow_possibleSwitchTo (t : ObjRef) : OW (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction
  repeat (first | with_reducible exact ow_threadGet _ _ | with_reducible exact ow_rescheduleRequired | with_reducible exact ow_tcbSchedAction _ _ | ow_step)

/-- **The spec's `awaken` keeps the FPU owner.** -/
theorem ow_awaken : OW (awaken (Z := Unit)) := by
  unfold awaken tcbReleaseDequeue
  repeat (first | with_reducible exact ow_tcbReleaseRemove _ | with_reducible exact ow_possibleSwitchTo _ | ow_step)

theorem ow_when' (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : OW m) :
    OW (NonDet.when P m) := ow_when P h

/-- What the arch part of a thread switch keeps, **up to the FPU**:
`ArchKeeps` with `HeapEqUpToFpu` for the heap equality. -/
def ArchKeepsF (σ σ' : State Unit) : Prop :=
  HeapEqUpToFpu σ σ' ∧ σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧
    σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.schedulerAction = σ.schedulerAction ∧ σ'.idleThread = σ.idleThread ∧
    σ'.curDomain = σ.curDomain ∧ σ'.domainTime = σ.domainTime ∧ σ'.idleSc = σ.idleSc

theorem ArchKeeps.toF {σ σ' : State Unit} (h : ArchKeeps σ σ') : ArchKeepsF σ σ' :=
  ⟨HeapEqUpToFpu.of_eq h.1, h.2⟩

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The arch hypotheses of a thread switch, up to the FPU** [P], at every
related state (module docstring): FL4's `set_vm_root` refines the spec's
`arch_switch_to_thread` (`set_vm_root; lazy_fpu_restore`) at a state whose
FPU owner is a TCB (`FpuOwnOK` [J]), keeping `ArchKeepsF` (the heap equal
but for the old and new owners' saved FPU image and `tcbCurFpu`, registers
kept); `set_kernel_vm_root` refines `arch_switch_to_idle_thread` (the
spec's `set_vm_root` of the idle thread: no FPU step) keeping `ArchKeeps`.
True at reachable states, up to what every arch premise assumes: one
outcome needs the opaque machine operations the switch runs
(`enableFpuImpl`, `writeFpuStateImpl`, `readFpuStateVal`, the CR3 write)
to have one outcome, as l4v's `corres` with the same machine operation on
both sides; FL4's lazy FPU switch lives behind `machine.Arch` and changes no
word of FL4's store, the spec's FPU fields are read by no relation.
Supersedes `ArchSw` (`ArchSw.toF`), whose `σ'.kheap = σ.kheap` is false
whenever the spec has an FPU owner other than `t`. -/
def ArchSwF (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (N T C : Set U64) (c : U64) : Prop :=
  (∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    FpuOwnOK σ →
    ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄) ∧
  (∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ →
    vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)

theorem ArchSw.toF {N T C : Set U64} {c : U64} (h : ArchSw st ar N T C c) : ArchSwF st ar N T C c :=
  ⟨fun s a σ hS hR _ t ht => WP.spec_mono (h.1 s a σ hS hR t ht) fun _ ⟨σ1, e1, e2, e3, e4⟩ =>
    ⟨σ1, e1, e2, e3, e4.toF⟩, h.2⟩

/-- **`switch_to_thread` refines l4v `switch_to_thread`, up to the FPU**:
`switch_to_thread_refines` with `ArchKeepsF` in the arch hypothesis and
`HeapEqUpToFpu σ σ'` in the post. -/
theorem switch_to_thread_refinesF {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    {t : U64} (ht : t ∈ T)
    (hvm : vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄) :
    sched.switch_to_thread st ar s a t ⦃ r => ∃ σ', Fl4Spec.switchToThread (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ (Inv σ → Inv σ') ∧
      σ'.curThread = t.bv ∧ σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  unfold sched.switch_to_thread
  refine WP.spec_bind (spec_and_eq hvm fun r hr => set_vm_root_s hr) ?_
  rintro ⟨s1, a1⟩ ⟨⟨σ1, h1, hS1, hR1, ek, eq, er, ect, esc, etm, ecn, eact, eid, ecd, edt, eisc⟩, hs1⟩
  simp only at hs1; subst s1
  obtain ⟨xt1, hkt1, -⟩ := ek.tcb hkt
  refine WP.spec_bind (WP.spec_and (dequeue_refines s σ1 hS1 t ht) (dequeue_sfoot hS1 ht)) ?_
  rintro s2 ⟨⟨σ2, h2, ek2, er2, hf2, hS2⟩, hw2⟩
  refine WP.spec_bind (sched.set_cur_thread.spec2 s2 t) ?_
  rintro s3 rfl
  rw [WP.spec_ok]
  show ∃ σ', _ ∧ SchedRel st N T C c (L.wr s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) t) σ' ∧ _
  rw [hS2.lists.choose_spec.choose_spec.1.cur]
  obtain ⟨hS3, hf3, -⟩ := hS2.set_cur_thread ht
  have hkv2 : KView σ1 σ2 := KView.of_kheap ek2
  have hR2 := hR1.frame hS1.placed hf2 hkv2
  rw [tcbSchedAction_gen hkt1] at h2
  have e2 := pair_eq h2
  refine ⟨{ σ2 with curThread := t.bv }, ?_, hS3, hR2.frame hS2.placed hf3 (KView.of_kheap rfl), ?_, ?_, rfl, ?_, ?_,
    ?_, ?_, ?_, WritesIn.sfoot_trans hw2 (sfoot_wr_node hS2.lists.choose_spec.choose_spec.1.node
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) t)⟩
  · unfold Fl4Spec.switchToThread
    rw [nd_bind_one (show Fl4Spec.NonDet.get (σ := Fl4Spec.State Unit) σ = ({(σ, σ)}, False) from rfl),
      nd_bind_one (assert_true (by simp [Fl4Spec.getTcb, Fl4Spec.readObject, hkt, Fl4Spec.Lookup.oreturn]) σ),
      nd_bind_one h1, nd_bind_one (tcbSchedAction_gen hkt1 _), ← e2]
    rfl
  · intro n hn x p hx hp; rw [ek2] at hx; exact hN n hn x p ((ek.ntcb fun _ e => by cases e).1 hx) hp
  · intro hI
    have hI1 : Inv σ1 := hI.fpu ek eq er etm
    rw [e2]
    exact (hI1.qchange (qchange_dequeue hkt1)).congr rfl rfl rfl rfl
  · rw [e2]; exact esc
  · rw [er2, er]
  · exact ek.trans_eq ek2
  · rw [e2]; exact eact
  · rw [e2]; exact ⟨etm, ecn, eid, ecd, edt, eisc⟩

/-- **`choose_thread` refines l4v `choose_thread`, up to the FPU**. -/
theorem choose_thread_refinesF {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hvm : ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄)
    (hvmi : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hidleT : (nodeW st s c layout.node.IDLE_THREAD).bv = σ.idleThread) :
    sched.choose_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.chooseThread (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.choose_thread
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  rw [hc.cur] at hcpu
  subst cpu
  unfold sched.bitmap_dom sched.l1_off
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok, lift]
  step with obj.node_get.spec as ⟨l1, hl1⟩
  have hl1' : l1 = L.l1W s c := by
    rw [hl1]; unfold LawfulStore.l1W; congr 2
    unfold layout.node.L1_BITMAP l1Off w64; rfl
  subst hl1'
  split
  · rename_i hne0
    have hne : L.l1W s c ≠ 0#u64 := by simpa using hne0
    refine choose_pick_k s σ hS hne _ _ ?_
    rintro t ⟨ht, hteq, p, hmem⟩
    refine WP.spec_mono (switch_to_thread_refinesF s a σ hS hR hN ht (hvm t ht)) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    obtain ⟨hsch, x, scp, hk, hsc, hdom⟩ := ready_sched hS hI hmem
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h10, h11, h12⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_neg (by rw [← choose_empty hS]; exact hne), ← hteq,
      guardedSwitchTo_eq hk hsc hsch hdom]
    exact h1
  · rename_i hne0
    have he : L.l1W s c = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hne0
    refine WP.spec_mono (switch_to_idle_thread_refines s a σ hS hR hN hidleT hvmi) ?_
    rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inl h6, h7, h8, HeapEqUpToFpu.of_eq h9, h10, h11, h12⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_pos ((choose_empty hS).1 he)]
    exact h1

end

end

end Fl4Proofs.P3.Sched
