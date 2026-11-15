/-
P3 (DESIGN.md §9), interrupts and IO ports: **`HandlersActive`,
`IoPortsAlloc` and `IrqSlotOK` from the spec's invariants**. These FL4-side
conditions (hypotheses of the IRQ control, IO port control and IRQ handler
refinements) follow, in related states (`StateRel`, `IrqRel`, `IoRel`),
from l4v's invariants of the abstract state: `valid_irq_handlers` with
`valid_cap`'s IRQ bound (`SpecIrqHandlers`), `valid_ioports` (`SpecIoPorts`),
and the IRQ node's slots holding notification caps or nothing
(`SpecIrqNode`).
-/
import Fl4Proofs.P3.IoControl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- l4v `valid_irq_handlers` with `valid_cap`'s bound: every IRQ handler cap
of the spec's CSpace is for an IRQ up to `maxIRQ` that is not inactive. -/
def SpecIrqHandlers (σ : Fl4Spec.State Unit) : Prop :=
  ∀ sl irq, Fl4Spec.getCap (Z := Unit) sl σ = ({(.irqHandlerCap irq, σ)}, False) →
    irq ≤ Fl4Spec.maxIRQ ∧ σ.interruptStates irq ≠ .irqInactive

/-- l4v `valid_ioports`: every IO port cap's ports are allocated. -/
def SpecIoPorts (σ : Fl4Spec.State Unit) : Prop :=
  ∀ sl f l, Fl4Spec.getCap (Z := Unit) sl σ = ({(.archObjectCap (.ioPortCap f l), σ)}, False) →
    f ≤ l ∧ ∀ p, f ≤ p → p ≤ l → σ.archState.x64AllocatedIoPorts p = true

/-- The IRQ node's slots hold notification caps or nothing. -/
def SpecIrqNode (σ : Fl4Spec.State Unit) : Prop :=
  ∀ irq a, Fl4Spec.getCap (Z := Unit) (σ.interruptIrqNode irq, []) σ = ({(a, σ)}, False) →
    a = .nullCap ∨ ∃ r b rs, a = .notificationCap r b rs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}

/-- **`HandlersActive` from l4v's `valid_irq_handlers`.** -/
theorem handlersActive_of_spec {s : S} {kb : U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hM : MdbLinks th (L.mem s) G) (hIR : IrqRel (L.mem s) kb σ)
    (hS : SpecIrqHandlers σ) : HandlersActive (L.mem s) kb G := by
  intro y hy i hi
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hy).1.abs
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc] at hi; subst hi
  have hwf : i.val < 256 := hca.1
  rw [hca.abs] at hg
  obtain ⟨h1, h2⟩ := hS ysl _ hg
  have hi8 : (BitVec.ofNat 8 i.val : BitVec 8).toNat = i.val := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hwf
  have h128 : i.val < 128 := by
    have : (BitVec.ofNat 8 i.val : BitVec 8).toNat ≤ (Fl4Spec.maxIRQ : BitVec 8).toNat := BitVec.le_def.1 h1
    rw [hi8] at this
    have hm : (Fl4Spec.maxIRQ : BitVec 8).toNat = 125 := rfl
    omega
  refine ⟨h128, fun h0 => h2 ?_⟩
  rw [hIR.st i h128, (irqSt_inactive _).2 h0]

/-- **`IoPortsAlloc` from l4v's `valid_ioports`.** -/
theorem ioPortsAlloc_of_spec {s : S} {kb : U64} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    (hR : StateRel th (L.mem s) σ) (hM : MdbLinks th (L.mem s) G) (hIo : IoRel (L.mem s) kb σ)
    (hS : SpecIoPorts σ) : IoPortsAlloc (L.mem s) kb G := by
  intro y hy f l owner hfl
  obtain ⟨ysl, hys, rfl⟩ := ((hM.members _).1 hy).1.abs
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hys
  rw [capV_of_capAt hc] at hfl; subst hfl
  obtain ⟨hf, hl⟩ := hca.1
  rw [hca.abs] at hg
  obtain ⟨h1, h2⟩ := hS ysl _ _ hg
  have e : ∀ x : U64, x.val < 2 ^ 16 → (BitVec.ofNat 16 x.val : BitVec 16).toNat = x.val := fun x hx => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hx
  have hle : f.val ≤ l.val := by
    have := BitVec.le_def.1 h1; rwa [e f hf, e l hl] at this
  refine ⟨hle, by simpa using hl, fun p hp1 hp2 => ?_⟩
  have hp : p < 65536 := by simp at hl; omega
  rw [← hIo p hp]
  apply h2
  · rw [BitVec.le_def, e f hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]; exact hp1
  · rw [BitVec.le_def, e l hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]; exact hp2

/-- **`IrqSlotOK` at every IRQ's node slot, from the spec's.** -/
theorem irqSlotOK_of_spec {s : S} {kb : U64} {σ : Fl4Spec.State Unit} (hL : IntLayout th kb)
    (hR : StateRel th (L.mem s) σ) (hIR : IrqRel (L.mem s) kb σ) (hS : SpecIrqNode σ)
    {irq : U64} (hirq : irq.val < 128) : IrqSlotOK (L.mem s) (nodeA kb irq) := by
  have hA : AbsSlot th ((nodeA kb irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node irq hirq)⟩
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hA
  rw [cslotAddr_nil] at hc
  rw [← hIR.node irq hirq] at hg
  unfold IrqSlotOK
  rw [capV_of_capAt hc]
  rcases hS _ ac hg with h | ⟨r, b, rs, h⟩
  · left; rw [hca.abs] at h; exact absCap_eq_null.1 h
  · right
    rw [hca.abs] at h
    cases c <;> simp [absCap] at h
    exact ⟨_, _, _, _, rfl⟩

end

end

end Fl4Proofs.P3
