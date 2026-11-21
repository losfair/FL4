/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gk_decodeReadRegisters (data : List Data) (p : ObjRef) : GKE (decodeReadRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeReadRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeReadRegisters)
