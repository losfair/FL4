/-
P3 (line jboot, gen 1): **the IPI vectors 126 / 127 in P3's platform premises** (wit.md finding, `OpaqueW.ipi`).

Gen 1 found (`ipi_forces_oracle`, removed in collapse A, Q) that the old `MachPlat` (the platform reports the
spec's line; `mask_irq` could unmask *any* line `< 256`) with the old `IrqPlatA.noIpi` (at *every* arch state,
`take_pending_irq` never gives 126 / 127) and one `MR`-related pair forced the spec's opaque `irqOracle` to avoid
126 and 127 from that pair's oracle position on: the platform premises silently assumed a fact about an `opaque`
spec constant. The spec's `maxIRQ` is 125: the spec never has an IRQ handler for 126 / 127 (`IntInv`'s handler
bound `irq ≤ maxIRQ`), so the kernel never unmasks them, and with them masked `getActiveIRQ` never reports them,
whatever the oracle.

**The fix** (gen 1's proposal, irqfix's `MachPlatT` / `IrqPlatK`, written back into `MachPlat` / `IrqPlatA` by
collapse A, Q; `MachPlatF` and `IpiF` now live in XTopJointMachRel): `MachPlat.mask` unmasks only lines
`≤ maxIRQ` (the one unmask caller, XTopJointKEntry39's `IRQAckIRQ`, has a handler cap, whose IRQ is `≤ maxIRQ`
by `IntInv`; the IRQ control issues pass the decode's bound), and `noIpi` is `MachPlat.noIpi : IpiF`, at
`MR`-related states. Here:
* **`modelArch_machPlatF`** / **`modelArch_ipiF`**: the model arch with `ipiMR := modelMR ∧ 126, 127 masked` meets
  both, **with no assumption on `irqOracle`** (`OpaqueW.ipi` is not needed);
* `MachPlatF.mask`: `MachPlat.mask`'s shape for lines `≤ maxIRQ`, what the unmask caller reads.

No sorry; no premises.
-/
import Fl4Proofs.P3.XTopJointMRPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

section
variable {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

theorem toNat_sw8 (w : U64) (hw : w.val < 256) : (w.bv.setWidth 8).toNat = w.val := by
  rw [BitVec.toNat_setWidth]
  show w.bv.toNat % 2 ^ 8 = w.bv.toNat
  exact Nat.mod_eq_of_lt (by have : w.bv.toNat = w.val := rfl; omega)

theorem sw8_ne {w : U64} {v : Irq} (hw : w.val < 256) (hv : v.toNat ≠ w.val) : w.bv.setWidth 8 ≠ v := by
  intro e
  have e2 := congrArg BitVec.toNat e
  rw [toNat_sw8 w hw] at e2
  exact hv e2.symm

/-! ## The fix -/

/-- `MachPlatF`'s mask of an IRQ handler's line (`IntInv`: `irq ≤ maxIRQ`), in `MachPlat.mask`'s shape: what the
unmask caller (XTopJointKEntry39, `IRQAckIRQ`) needs. -/
theorem MachPlatF.mask (h : MachPlatF arI MR) (a : A) (w : U64) (m : Bool) (ms : Fl4Spec.MachineState)
    (hR : MR a ms) (hw : w.val ≤ 125) : arI.mask_irq a w m ⦃ a' =>
      MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m } ⦄ := by
  cases m
  · exact h.mask0 a w ms hR hw
  · exact h.mask1 a w ms hR (by omega)

end

/-! ## The model meets the fix with no oracle assumption -/

/-- The model's relation with the IPI vectors masked. -/
def ipiMR (a ms : Fl4Spec.MachineState) : Prop :=
  modelMR a ms ∧ ms.irqMasks 126 = true ∧ ms.irqMasks 127 = true

theorem gaiLine_some_unmasked {ms : Fl4Spec.MachineState} {i : Irq} (h : gaiLine true ms = some i) :
    ms.irqMasks i = false := by
  unfold gaiLine at h
  split_ifs at h with hc
  cases h
  simp only [not_or] at hc
  simpa using hc.1

theorem upd_keep (f : Irq → Bool) (w : U64) (m : Bool) (v : Irq) (hv : f v = true) (hw : w.val ≤ 125)
    (hv' : v.toNat = 126 ∨ v.toNat = 127) : Function.update f (w.bv.setWidth 8) m v = true := by
  rw [Function.update_of_ne (sw8_ne (by omega) (by omega)).symm]; exact hv

theorem upd_true (f : Irq → Bool) (x v : Irq) (hv : f v = true) : Function.update f x true v = true := by
  rw [Function.update_apply]; split_ifs <;> simp_all

/-- **The model arch meets `MachPlatF` at `ipiMR`.** -/
theorem modelArch_machPlatF : MachPlatF modelArch ipiMR where
  now a ms := fun ⟨h, h6, h7⟩ => WP.spec_mono (modelArch_machPlat.now a ms h) fun _ ⟨e, hr⟩ => ⟨e, hr, h6, h7⟩
  irqPending a ms := fun ⟨h, h6, h7⟩ =>
    WP.spec_mono (modelArch_machPlat.irqPending a ms h) fun _ ⟨e, hr⟩ => ⟨e, hr, h6, h7⟩
  take a ms := fun ⟨h, h6, h7⟩ =>
    WP.spec_mono (modelArch_machPlat.take a ms h) fun _ ⟨e1, e2, hr⟩ => ⟨e1, e2, hr, h6, h7⟩
  mask1 a w ms := fun ⟨h, h6, h7⟩ hw =>
    WP.spec_mono (modelArch_machPlat.mask1 a w ms h hw) fun _ hr =>
      ⟨hr, upd_true _ _ _ h6, upd_true _ _ _ h7⟩
  mask0 a w ms := fun ⟨h, h6, h7⟩ hw =>
    WP.spec_mono (modelArch_machPlat.mask0 a w ms h hw) fun _ hr =>
      ⟨hr, upd_keep _ w false 126 h6 hw (Or.inl rfl), upd_keep _ w false 127 h7 hw (Or.inr rfl)⟩
  ack a w ms := fun ⟨h, h6, h7⟩ => WP.spec_mono (modelArch_machPlat.ack a w ms h) fun _ hr => ⟨hr, h6, h7⟩
  frame a ms ms' := fun ⟨h, h6, h7⟩ e1 e2 e3 e4 =>
    ⟨modelArch_machPlat.frame a ms ms' h e1 e2 e3 e4, by rw [e1]; exact h6, by rw [e1]; exact h7⟩

/-- **The model arch meets `IpiF` at `ipiMR`, whatever the oracle** (module docstring). -/
theorem modelArch_ipiF : IpiF modelArch ipiMR := by
  rintro a ms ⟨⟨h1, -, -, -⟩, h6, h7⟩
  show (ok (modelTake a, gaiState a) : Result (U64 × Fl4Spec.MachineState)) ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄
  rw [WP.spec_ok]
  show (modelTake a).val ≠ 126 ∧ (modelTake a).val ≠ 127
  cases e : gaiLine true a with
  | none =>
    rw [modelTake_none e]
    have hn : syscall.NO_IRQ.val = 2 ^ 64 - 1 := by
      show syscall.NO_IRQ.bv.toNat = _
      rw [no_irq_bv, BitVec.toNat_allOnes]
    rw [hn]
    exact ⟨by norm_num, by norm_num⟩
  | some i =>
    rw [(modelTake_some e).2]
    have hm := gaiLine_some_unmasked e
    rw [h1] at hm
    have n6 : i ≠ 126 := fun h => by rw [h, h6] at hm; cases hm
    have n7 : i ≠ 127 := fun h => by rw [h, h7] at hm; cases hm
    exact ⟨fun h => n6 (BitVec.eq_of_toNat_eq (by rw [h]; rfl)),
      fun h => n7 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))⟩

end

end Fl4Proofs.P3
