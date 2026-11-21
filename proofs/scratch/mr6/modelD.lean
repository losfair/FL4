/-- **The model platform satisfies `MRKeepD`** for every predicate. -/
theorem modelArch_mrKeepD {C : Type} (AR : Fl4Spec.MachineState → C → Prop) : MRKeepD modelArch AR where
  set_deadline _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  send_reschedule _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  remote_stall _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_flush _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_release _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_sanitise _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  fpu_reload _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  vcpu_barrier _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_ept _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_page _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_asid _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  invalidate_page_structures _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  set_vspace _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  dma_frame _ _ _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h
  irq_free _ _ _ h := by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h

