theorem gk_archNoReturn {m : SMonad Unit Unit} (h : GK m) : GK (archNoReturn (Z := Unit) m) := by
  unfold archNoReturn; exact gk_bind h fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_archNoReturn ?_)
