/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **the spec steps keep the
machine fields `MR` reads, the interrupt table and the current time**
(spec side only; `MTK`). MachFieldFam's `MFK` family with `curTime` added to
the projection (`ValidMachineTime` reads it), and with the machine-operation
leaves MachFieldFam lacked: the TLB flushes (`invalidateASID`,
`invalidateTranslationSingleASID`, `invalidateLocalPageStructureCacheASID`)
and the lazy-FPU operations (`readFpuState`, `writeFpuState`, `enableFpu`,
`disableFpu`): `machine_op_lift`s of the machine's opaque rest plus the FPU
enable bit, none of the four machine fields `MR` reads. So the deletion's
finalisation (`finaliseCap`: FPU release, TLB flushes of the VSpace
unmaps) is in the family (`mtk_finaliseCap`).

* `msFT σ`: MachFieldFam's `msF σ` and `σ.curTime`; `MTK m := FK msFT m`.
* Leaves: MachFieldFam's `MKF` (`mtk_doMachineOp`), the new `mkf_*` above.
* The rest: one lemma per spec function by `mtk_auto`, VsDomOps / DomRecDel /
  TcbDom / AllDom's `DK` lemmas renamed (generated: scratch/mr6/mtgen.py +
  head/tail.lean + skip.txt, `sh scratch/mr6/mk.sh`); left out are the
  functions reaching `getActiveIRQ`, `getCurrentTime`, `maskInterrupt` (and
  `setIrqState`), `portOut`, `portIn`, `setDeadline`, `ackDeadlineIRQ`,
  `clearMemory`, `freeMemory`, and their dependents.
-/
import Fl4Proofs.P3.MachFieldFam

open Classical

namespace Fl4Proofs.P3.MachT
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF

noncomputable section

/-- `msF` and the current time. -/
def msFT (σ : State Unit) := (msF σ, σ.curTime)

/-- Every outcome of `m` keeps `msFT`. -/
abbrev MTK {α : Type} (m : NonDet (State Unit) α) : Prop := FK msFT m

/-- `MTK` for the exception monad. -/
abbrev MTKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE msFT m

section MKF

theorem mkf_stateAssert (P : MachineState → Prop) : MKF (NonDet.stateAssert P) := by
  intro ms x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem mkf_machineRestLift {α : Type} (f : MachineRestMonad α) : MKF (machineRestLift f) := by
  unfold machineRestLift
  exact mkf_bind (mkf_gets _) fun _ => mkf_bind (mkf_selectF _) fun _ => mkf_bind (mkf_modify fun _ => rfl)
    fun _ => mkf_pure _

theorem mkf_invalidateASID (v a : Word) : MKF (invalidateASID v a) := mkf_machineOpLift _

theorem mkf_invalidateTranslationSingleASID (v a : Word) : MKF (invalidateTranslationSingleASID v a) :=
  mkf_machineOpLift _

theorem mkf_invalidateLocalPageStructureCacheASID (v a : Word) :
    MKF (invalidateLocalPageStructureCacheASID v a) := mkf_machineOpLift _

theorem mkf_readFpuState : MKF readFpuState := by
  unfold readFpuState
  exact mkf_bind (mkf_stateAssert _) fun _ => mkf_machineRestLift _

theorem mkf_writeFpuState (v : FpuState) : MKF (writeFpuState v) := by
  unfold writeFpuState
  exact mkf_bind (mkf_stateAssert _) fun _ => mkf_machineOpLift _

theorem mkf_enableFpu : MKF enableFpu := by
  unfold enableFpu
  exact mkf_bind (mkf_machineOpLift _) fun _ => mkf_modify fun _ => rfl

theorem mkf_disableFpu : MKF disableFpu := by
  unfold disableFpu
  exact mkf_bind (mkf_machineOpLift _) fun _ => mkf_modify fun _ => rfl

theorem mkf_isFpuEnable : MKF isFpuEnable := mkf_gets _

theorem mkf_getFaultAddress : MKF getFaultAddress := mkf_gets _

theorem mkf_ackInterrupt (i : Irq) : MKF (ackInterrupt i) := mkf_pure _

end MKF

theorem mtk_doMachineOp {α : Type} {mop : NonDet MachineState α} (hm : MKF mop) :
    MTK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  have h := mfk_doMachineOp hm σ x hx
  have ht : x.2.curTime = σ.curTime := by
    unfold doMachineOp at hx
    obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 h1] at h2
    obtain ⟨-, e2⟩ := h2
    simp only [Prod.mk.injEq] at e2 h3
    obtain ⟨-, rfl⟩ := e2
    rw [Set.mem_singleton_iff.1 h3] at hx
    rw [Set.mem_singleton_iff.1 hx]
  show (msF x.2, x.2.curTime) = (msF σ, σ.curTime)
  rw [h, ht]

/-- A `MTK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "mtk_leaf" : tactic
macro_rules | `(tactic| mtk_leaf) => `(tactic| fail "no mtk_leaf")
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_loadWord _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_storeWord _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_machineOpLift _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateTranslationSingleASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_invalidateLocalPageStructureCacheASID _ _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_readFpuState)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_writeFpuState _))
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_enableFpu)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_disableFpu)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_isFpuEnable)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp mkf_getFaultAddress)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doMachineOp (mkf_ackInterrupt _))

macro "mtk_auto" : tactic => `(tactic| repeat' (first | mtk_leaf | dk_step0))

theorem mtk_doExtendedOp (eop : DetExtMonad Unit) : MTK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_doExtendedOp _)

theorem mtk_setObject (p : ObjRef) (o : KernelObject) : MTK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setObject _ _)

theorem mtk_setCap (c : Cap) (sl : CslotPtr) : MTK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_setCap _ _)

theorem mtk_getCap (sl : CslotPtr) : MTK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; mtk_auto
macro_rules | `(tactic| mtk_leaf) => `(tactic| with_reducible exact mtk_getCap _)

