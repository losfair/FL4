theorem gk_decodeIrqControlInvocationWith {check : Data → SEMonad Unit Unit} (h : ∀ d, GKE (check d))
    (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) :
    GKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; gk_auto; all_goals exact h _
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_decodeIrqControlInvocationWith (fun _ => ?_) _ _ _ _)
