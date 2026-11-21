/-- At a thread cap (as `gk_decodeReadRegisters`). -/
theorem gk_decodeCopyRegisters (data : List Data) (p : ObjRef) (ec : List Cap) :
    GKE (decodeCopyRegisters (Z := Unit) data (.threadCap p) ec) := by
  unfold decodeCopyRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeCopyRegisters)
