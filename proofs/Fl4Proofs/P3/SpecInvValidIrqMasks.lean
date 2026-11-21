/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`ValidIrqMasks`
(l4v `valid_irq_masks`) as a spec-only invariant** (spec side only; outside the
`JAtZ` cone).

* `ValidIrqMasks σ`: an inactive line is masked. The same body as
  XTopJointMRPath's `ValidIrqMasks` (premise `hVI` of `kernel_entryJ26P`), which
  is in the `JAtZ` cone.
* Its leaves but the ack (`vim_view`, `vim_uts`, `vim_sis`, `vim_msk`):
  `updateTimeStamp` keeps the table and the masks (`uts_out`), `setIrqState`
  masks exactly the lines it makes inactive (l4v `set_irq_state` with
  `maskInterrupt`), and the machine operations of the kernel entry only mask
  (`MaskT`: `getActiveIRQ`, `maskInterrupt true`, the timer/port/memory
  operations).
* ReadFPU (invB's FINDING `readFpu_breaks_vim`, deleted by fpu1): the spec's
  step used to set the whole machine state, so it could unmask an inactive
  line; since fpu1 it is Ext/Tcb's `fl4FpuToFrame`, a `MaskT` operation
  (`mt_fl4FpuToFrame`), so `vim_msk` covers it.
* `wl_vim_of`: every leaf but the ack, so the entry theorem is
  `gk_fl4KernelEntrySyscall true c _ (wl_vim_of hA)` once the ack leaf `hA`
  is replaced.
* The remaining gap (`hA`): the IRQ ack. Its only caller is
  `invokeIrqHandler (.aCKIrq irq)` = `archInvokeIrqHandler (.aCKIrq irq)` =
  `doMachineOp (maskInterrupt false irq)` (Fl4Spec Interrupt.lean), reached
  after `decodeIrqHandlerInvocation` returned `.aCKIrq irq` for an
  `irqHandlerCap irq` invoked by the caller (Decode.lean). It unmasks without
  reading the line's state, so it keeps `ValidIrqMasks` only when
  `σ.interruptStates irq ≠ .irqInactive` at the perform's state; `hA` as
  stated (every state) is false. l4v gets the fact from `valid_irq_handlers`
  (every `IRQHandlerCap irq` in the CSpace has `irq` not inactive) and the
  decode's `cte_wp_at` of the invoked cap, carried to the perform. Needed:
  `ValidIrqHandlers σ` (every IRQ handler cap of the CSpace names a line that
  is not inactive) as a second invariant kept by the entry (writers:
  `invokeIrqControl` sets `irqSignal` before `capInsert`ing the handler cap;
  `postCapDeletion (.irqHandlerCap irq)` = `deletedIrqHandler` sets
  `irqInactive`, which l4v justifies by the deleted cap being final, i.e.
  no other handler cap for `irq`; cap copy/mint/move/derive of an IRQ handler
  cap name the same line), and the ack leaf restated at the decode's outcome
  instead of ∀-states (the `GK` kit's `WL.ack` would take the handler-cap
  fact as an argument). Stopped there.
* `boot_vim`: the spec's initial state (every line inactive and masked).
-/
import Fl4Proofs.P3.SpecInvValidMachineTime

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- **[J] l4v `valid_irq_masks`** (module docstring). -/
def ValidIrqMasks (σ : Fl4Spec.State Unit) : Prop :=
  ∀ i, σ.interruptStates i = .irqInactive → σ.machineState.irqMasks i = true

theorem vim_view : ∀ σ σ', vw σ' = vw σ → ValidIrqMasks σ → ValidIrqMasks σ' := by
  intro σ σ' e h i hi
  unfold vw at e; simp only [Prod.mk.injEq] at e
  rw [e.2.2.1] at hi; rw [e.2.2.2]; exact h i hi

theorem vim_uts : IK ValidIrqMasks (updateTimeStamp (Z := Unit)) := by
  intro σ h x hx i hi
  obtain ⟨-, -, e3, e4⟩ := uts_out hx
  rw [e3] at hi; rw [e4]; exact h i hi

theorem dmo_mask_out {σ : State Unit} {x : Unit × State Unit} (b : Bool) (i : Irq)
    (hx : x ∈ (doMachineOp (Z := Unit) (maskInterrupt b i) σ).1) :
    x.2.machineState.irqMasks = Function.update σ.machineState.irqMasks i b ∧
      x.2.interruptStates = σ.interruptStates := by
  have e : maskInterrupt b i σ.machineState =
      ({((), { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks i b })}, False) := rfl
  rw [dmo_single e] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨rfl, rfl⟩

theorem vim_sis (st : IrqState) (i : Irq) : IK ValidIrqMasks (setIrqState (Z := Unit) st i) := by
  intro σ h x hx j hj
  unfold setIrqState at hx
  rw [sv_bind_modify] at hx
  obtain ⟨e1, e2⟩ := dmo_mask_out _ i hx
  rw [e2] at hj; rw [e1]
  dsimp only at hj ⊢
  by_cases e : j = i
  · subst e
    simp only [Function.update_self] at hj ⊢
    simp [hj]
  · rw [Function.update_of_ne e] at hj ⊢
    exact h j hj

theorem vim_msk {α : Type} (mop : NonDet MachineState α) (hm : MaskT mop) :
    IK ValidIrqMasks (doMachineOp (Z := Unit) mop) := by
  intro σ h x hx j hj
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨h2a, e2⟩ := h2
  dsimp only at e2 h2a
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx] at hj ⊢
  rcases (hm _ _ h2a).2 j with e | e
  · exact e.trans (h j hj)
  · exact e

/-- **`ValidIrqMasks` kept by every leaf but the IRQ ack**, as a reduction:
given the ack leaf `hA` (the gap, module docstring: FALSE as a ∀-over-states
statement, since an ack of an inactive line unmasks it; l4v proves the ack
case from `valid_irq_handlers` at the decode's state), `WL ValidIrqMasks`.
Not a top theorem. -/
theorem wl_vim_of (hA : ∀ i, IK ValidIrqMasks (doMachineOp (Z := Unit) (maskInterrupt false i))) :
    WL ValidIrqMasks where
  view := vim_view
  uts := vim_uts
  sis := vim_sis
  msk := vim_msk
  ack := hA

/-- **`ValidIrqMasks` at boot** (`initIrqMasks`: every line masked). -/
theorem boot_vim : ValidIrqMasks (initASt (Z := Unit)) := fun _ _ => rfl

end

end Fl4Proofs.P3.SInvV
