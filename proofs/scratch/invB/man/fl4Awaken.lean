/-- **FL4's TCB timer step keeps every `GK` predicate**: each fired timer is
a `sendSignal` (MachFieldFamT's frame) and the timer reprogram flag. -/
theorem gk_fl4Awaken : GK (fl4Awaken (Z := Unit)) := by
  intro P L σ h x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  show P s'
  clear hx
  induction hx' with
  | refl => exact h
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    have h2 : P σ1 := by
      rcases h1 with rfl | ⟨n, b, e⟩
      · exact ih
      · exact gk_of_mtk (mtk_sendSignal' n b) P L _ ih ((), σ1) (by rw [e]; exact Set.mem_singleton _)
    exact L.view σ1 _ rfl h2
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible exact gk_fl4Awaken)
