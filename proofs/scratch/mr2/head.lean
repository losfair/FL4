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

