/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr1, irq1 NEXT (1)): **spec
steps keep the machine fields of `MR`** (`MF`): the IRQ masks, the IRQ and
clock oracle positions and the last machine time, the four fields
XTopJointMachRel's `MachPlat.frame` says `MR` reads. A clone of ScFieldKeep's
`FK` family (combinators, leaves, `mf_step` / `mf_unf` / `mf_auto`) for this
field set; every spec operation that reaches no machine operation other than
the memory ones keeps them.

* `mf_chargeBudgetF`: `charge_budget` without a timeout fault (the
  non-schedulable branch of the preemption path, `preemptionPath`'s
  `chargeBudget consumed false`).
* `MachPlat.mfKeep`: `MR` moves along an `MF` step (with `MachPlat.frame`).
-/
import Fl4Proofs.P3.XTopJointMachRel
import Fl4Proofs.P3.ScFieldKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- The four machine fields `MR` reads (XTopJointMachRel's `MachPlat.frame`)
kept: the IRQ masks, the IRQ and clock oracle positions, the last machine
time. -/
def MF (σ σ' : State Unit) : Prop :=
  σ'.machineState.irqMasks = σ.machineState.irqMasks ∧ σ'.machineState.irqState = σ.machineState.irqState ∧
    σ'.machineState.timeState = σ.machineState.timeState ∧
    σ'.machineState.lastMachineTime = σ.machineState.lastMachineTime

theorem MF.refl (σ : State Unit) : MF σ σ := ⟨rfl, rfl, rfl, rfl⟩

theorem MF.trans {σ1 σ2 σ3 : State Unit} (h1 : MF σ1 σ2) (h2 : MF σ2 σ3) : MF σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- Every outcome keeps the current SC and the idle thread. -/
def MFA {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → MF σ x.2

theorem MFA.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : MFA m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : MF σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

section Comb

theorem mf_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : MFA m)
    (hg : ∀ a, MFA (g a)) : MFA (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem mf_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : MFA m)
    (hg : ∀ a, MFA (g a)) : MFA (NonDet.bind m g) := mf_bind hm hg

theorem mf_same {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : MFA m := by
  intro σ x hx; rw [h σ x hx]; exact MF.refl σ

theorem mf_pure {α : Type} (a : α) : MFA (pure a : NonDet (State Unit) α) :=
  mf_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mf_pure' {α : Type} (a : α) : MFA (NonDet.pure a : NonDet (State Unit) α) := mf_pure a

theorem mf_gets {α : Type} (g : State Unit → α) : MFA (NonDet.gets g) :=
  mf_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mf_get : MFA (NonDet.get : NonDet (State Unit) (State Unit)) :=
  mf_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mf_assert (P : Prop) : MFA (NonDet.assert P : NonDet (State Unit) Unit) :=
  mf_same fun _ x hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem mf_fail {α : Type} : MFA (NonDet.fail : NonDet (State Unit) α) := fun _ _ hx => hx.elim

theorem mf_assertOpt {α : Type} (o : Option α) : MFA (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact mf_fail
  · exact mf_pure' _

theorem mf_getsThe {α : Type} (g : State Unit → Option α) : MFA (NonDet.getsThe g) := by
  intro σ x hx; exact mf_assertOpt (g σ) σ x hx

theorem mf_selectF {α : Type} (S : Set α × Prop) : MFA (NonDet.selectF S : NonDet (State Unit) α) :=
  mf_same fun _ x hx => by obtain ⟨-, h⟩ := hx; exact h

theorem mf_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : MFA m1)
    (h2 : MFA m2) : MFA (if P then m1 else m2) := by
  split <;> assumption

theorem mf_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : MFA m) : MFA (NonDet.when P m) := by
  unfold NonDet.when; exact mf_ite P h (mf_pure' _)

theorem mf_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : MFA m) :
    MFA (NonDet.unless P m) := by
  unfold NonDet.unless; exact mf_ite P (mf_pure' _) h

theorem mf_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, MFA (g a)) (o : Option α) :
    MFA (NonDet.maybeM g o) := by
  cases o
  · exact mf_pure' _
  · exact h _

theorem mf_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : MFA m) : MFA (NonDet.liftM g m) :=
  mf_bind' h fun _ => mf_pure' _

theorem mf_modify {g : State Unit → State Unit} (hg : ∀ σ, MF σ (g σ)) : MFA (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem mf_get_put {g : State Unit → State Unit} (hg : ∀ σ, MF σ (g σ)) :
    MFA (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem mf_getObject (p : ObjRef) : MFA (getObject (Z := Unit) p) := mf_getsThe _

theorem mf_setObject (p : ObjRef) (o : KernelObject) : MFA (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := setObject_mem hx
  rw [e]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem mf_doExtendedOp (eop : DetExtMonad Unit) : MFA (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine mf_bind mf_get (fun _ => mf_bind (mf_selectF _) (fun _ => ?_))
  split
  exact mf_modify (fun σ => ⟨rfl, rfl, rfl, rfl⟩)

theorem mf_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, MFA (B r)) (r : α) : MFA (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact MF.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem mf_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MFA (g a)) (xs : List α) :
    MFA (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact mf_pure' _
  | cons a xs' ih => exact mf_bind' (h a) fun _ => ih

theorem mf_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MFA (g a)) (xs : List α) :
    MFA (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact mf_pure' _
  | cons a xs' ih => exact mf_bind' (h a) fun _ => mf_bind' ih fun _ => mf_pure' _

end Comb

macro "mf_step0" : tactic => `(tactic| first
  | with_reducible exact mf_pure _ | with_reducible exact mf_pure' _ | with_reducible exact mf_fail
  | with_reducible exact mf_gets _ | with_reducible exact mf_get
  | with_reducible exact mf_assert _ | with_reducible exact mf_assertOpt _
  | with_reducible exact mf_getObject _ | with_reducible exact mf_getsThe _
  | with_reducible exact mf_selectF _ | with_reducible exact mf_setObject _ _
  | ((with_reducible apply mf_modify); intro _; exact ⟨rfl, rfl, rfl, rfl⟩)
  | ((with_reducible apply mf_get_put); intro _; exact ⟨rfl, rfl, rfl, rfl⟩)
  | with_reducible exact mf_doExtendedOp _
  | (with_reducible refine mf_bind ?_ (fun _ => ?_))
  | (with_reducible refine mf_bind' ?_ (fun _ => ?_))
  | (with_reducible apply mf_ite) | (with_reducible apply mf_when) | (with_reducible apply mf_unless)
  | (with_reducible refine mf_maybeM (fun _ => ?_) _) | (with_reducible apply mf_liftM)
  | (with_reducible refine mf_whileLoop (fun _ => ?_) _)
  | (with_reducible refine mf_mapMx (fun _ => ?_) _)
  | (with_reducible refine mf_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))

section Ops

theorem mf_threadSet (g : Tcb → Tcb) (p : ObjRef) : MFA (threadSet (Z := Unit) g p) := by
  unfold threadSet; repeat mf_step0

theorem mf_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : MFA (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat mf_step0

theorem mf_getSchedContext (p : ObjRef) : MFA (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat mf_step0

theorem mf_updateSchedContext (p : ObjRef) (g : SchedContext → SchedContext) :
    MFA (updateSchedContext (Z := Unit) p g) := by
  unfold updateSchedContext; repeat mf_step0

theorem mf_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    MFA (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo; repeat mf_step0

theorem mf_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) (e : α) :
    MFA (setSimpleKo (Z := Unit) C p e) := by
  unfold setSimpleKo; repeat mf_step0

theorem mf_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (g : (Option ObjRef → Option ObjRef) → α → α) (p : ObjRef) (new : Option ObjRef) :
    MFA (updateSkObjRef (Z := Unit) C g p new) := by
  unfold updateSkObjRef
  exact mf_bind (mf_getSimpleKo _ _) fun _ => mf_setSimpleKo _ _ _

end Ops

macro "mf_step" : tactic => `(tactic| first
  | with_reducible exact mf_threadGet _ _ | with_reducible exact mf_threadSet _ _
  | with_reducible exact mf_getSchedContext _ | with_reducible exact mf_updateSchedContext _ _
  | with_reducible exact mf_getSimpleKo _ _ | with_reducible exact mf_setSimpleKo _ _ _
  | with_reducible exact mf_updateSkObjRef _ _ _ _
  | mf_step0)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

macro "mf_unf" : tactic => `(tactic| first
  | unfold getScObjRef | unfold tcbSchedAction | unfold getTcbQueue | unfold setTcbQueue
  | unfold rescheduleRequired | unfold setSchedulerAction | unfold getScRefillSufficient | unfold getScRefillReady
  | unfold tcbReleaseRemove | unfold setReleaseQueue | unfold tcbReleaseEnqueue | unfold readyTimesAppend
  | unfold orderedInsert | unfold postpone | unfold schedContextResume | unfold refillUnblockCheck
  | unfold isRoundRobin | unfold refillHeadOverlappingLoop | unfold mergeOverlappingRefills | unfold refillPopHead
  | unfold updateRefillHd | unfold getRefillHead | unfold ifCondRefillUnblockCheck | unfold schedContextBindTcb
  | unfold schedContextBindNtfn | unfold commitTime | unfold refillBudgetCheckRoundRobin | unfold refillBudgetCheck
  | unfold updateRefillTl | unfold refillAddTail | unfold getRefills | unfold getRefillTail | unfold refillFull
  | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill
  | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold getScActive
  | unfold maybeAddEmptyTail | unfold refillNew | unfold refillUpdate | unfold possibleSwitchTo
  | unfold getTcbObjRef | unfold getThreadState | unfold schedContextUnbindTcb | unfold schedContextUnbindNtfn
  | unfold returnConsumed | unfold schedContextUpdateConsumed | unfold setThreadStateAct | unfold scheduleTcb
  | unfold getSkObjRef | unfold getScReleased | unfold getNtfnObjRef | unfold getReplyObjRef)

macro "mf_auto" : tactic => `(tactic| repeat (first | mf_step | mf_unf))

theorem mf_chargeBudgetF (u : Ticks) : MFA (chargeBudget (Z := Unit) u false) := by
  unfold chargeBudget endTimeslice refillResetRr refillBudgetCheck handleOverrun chargeEntireHeadRefill
    headInsufficientLoop mergeNonoverlappingHeadRefill scheduleUsed refillPopHead updateRefillHd updateRefillTl
    refillAddTail isRoundRobin getRefillHead getRefillTail getRefills refillSingle refillSize refillFull
    getScRefillReady getScRefillSufficient getThreadState isValidTimeoutHandler getCap
  try simp only [Bool.false_eq_true, false_and, ↓reduceIte]
  repeat (any_goals (first | mf_step | mf_unf))

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3

section
variable {A : Type} {arI : fl4_core.machine.Arch A} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`MR` moves along an `MF` step.** -/
theorem MachPlat.mfKeep (hM : MachPlat arI MR) {a : A} {σ σ' : Fl4Spec.State Unit} (hR : MR a σ.machineState)
    (h : Sched.MF σ σ') : MR a σ'.machineState :=
  hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2

end

end Fl4Proofs.P3
