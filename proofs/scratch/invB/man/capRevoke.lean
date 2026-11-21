/-- One step of `cap_revoke` keeps every `GK` predicate, its recursive calls keeping them. -/
theorem gk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, GK (f k)) (sl : CslotPtr) : GKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, GKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF selectExt
  gk_auto
  all_goals exact hrec' _

/-- **`cap_revoke` keeps every `GK` predicate.** -/
theorem gk_capRevoke (sl : CslotPtr) : GKE (capRevoke (Z := Unit) sl) := by
  intro P L σ h x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | ∀ P, WL P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gk_capRevokeF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf sl σ).1 hx P L h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_capRevoke)
