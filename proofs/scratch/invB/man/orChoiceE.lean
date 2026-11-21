theorem gk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) {f g : NonDetE (State Unit) ε α} (hf : GKE f)
    (hg : GKE g) : GKE (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE
  refine gke_bind (gke_liftE gk_get) fun _ => gke_bind (gke_liftE (gk_selectF _)) fun r => ?_
  obtain ⟨rv, _⟩ := r
  try dsimp only
  exact gke_ite _ hf hg
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible refine gk_orChoiceE _ ?_ ?_)
