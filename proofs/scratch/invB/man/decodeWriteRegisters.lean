/-- At a thread cap (its only caller, `decodeTcbInvocation` from the thread-cap
branch of `fl4DecodeInvocation`; the non-thread-cap branch is l4v's `undefined`). -/
theorem gk_decodeWriteRegisters (data : List Data) (p : ObjRef) : GKE (decodeWriteRegisters (Z := Unit) data (.threadCap p)) := by
  unfold decodeWriteRegisters; gk_auto
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_decodeWriteRegisters)
