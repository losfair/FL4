/-- At a thread cap. -/
theorem gk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : GKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeTcbInvocation)
