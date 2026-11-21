/-- At a thread cap. -/
theorem gk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    GKE (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excaps buffer) := by
  unfold fl4DecodeTcbInvocation; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_fl4DecodeTcbInvocation)
