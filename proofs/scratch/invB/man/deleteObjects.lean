theorem gk_deleteObjects (ptr : Word) (bits : Nat) : GK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact gk_bind (gk_doMachineOp (mt_freeMemory _ _)) fun _ => gk_modify fun _ => rfl
macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_deleteObjects)
