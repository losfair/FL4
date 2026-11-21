/-- One step of `rec_del` keeps every `GK` predicate, its recursive calls keeping them. -/
theorem gk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, GK (f k)) (k : RecDelCall) : GKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, GKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k <;> (unfold recDelF; gk_auto) <;> exact hrec' _

/-- **`rec_del` keeps every `GK` predicate** (the pre-fixed point of DomRecDel's `dk_recDel`). -/
theorem gk_recDel (c : RecDelCall) : GKE (recDel (Z := Unit) c) := by
  intro P L σ h x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | ∀ P, WL P → P t → P y.2}, True)
  have hf : ∀ k t, (fun r c => recDelF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy P' L' ht => gk_recDelF (f := f) (fun _ P'' L'' _ hs _ hz => hz P'' L'' hs) k P' L' t ht y hy,
      fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf c σ).1 hx P L h
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_recDel)
