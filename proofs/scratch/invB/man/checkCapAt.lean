theorem gk_checkCapAt (cap : Cap) (slot : CslotPtr) {m : SMonad Unit Unit} (h : GK m) :
    GK (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; gk_auto; all_goals exact h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_checkCapAt _ _ ?_)
