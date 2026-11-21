
/-- **The platform premises of `kernel_entryJ13P` are satisfiable by a
platform that raises interrupts** (module docstring): the model platform
(`modelArch`, arch state = spec machine state, `modelMR`) satisfies
`MachPlat` and `MRKeep`, and its `take_pending_irq` reports the spec's line
whenever the spec has one (unlike `IrqPlat.take`/`PPPlat`, which only a
platform that never interrupts satisfies, and `PPPlat.now`, which none does). -/
theorem j13P_platform :
    MachPlat modelArch modelMR ∧ MRKeep modelArch modelMR ∧
      ∀ (ms : Fl4Spec.MachineState) (i : Fl4Spec.Irq), gaiLine true ms = some i →
        modelArch.take_pending_irq ms ⦃ r => r.1 ≠ syscall.NO_IRQ ∧ r.1.val = i.toNat ⦄ :=
  ⟨modelArch_machPlat, modelArch_mrKeep modelMR, fun _ _ h => modelArch_take_some h⟩

end

end

end Fl4Proofs.P3
