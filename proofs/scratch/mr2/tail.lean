
/-! ### The MCS budget check (not in the `DK` list) -/

theorem mfk_chargeBudget (u : Ticks) (b : Bool) : MFK (chargeBudget (Z := Unit) u b) := by
  unfold chargeBudget endTimeslice refillResetRr tcbSchedAppend
  mfk_auto
macro_rules | `(tactic| mfk_leaf) => `(tactic| with_reducible exact mfk_chargeBudget _ _)

theorem mfk_checkBudget : MFK (checkBudget (Z := Unit)) := by
  unfold checkBudget
  mfk_auto
