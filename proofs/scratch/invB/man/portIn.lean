theorem gk_portIn {f : MachineMonad Data} (h : MaskT f) : GK (portIn (Z := Unit) f) := by
  unfold portIn; exact gk_bind (gk_doMachineOp h) fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| (with_reducible refine gk_portIn ?_); mt_auto; done)

theorem gk_portOut {n : Nat} {f : BitVec n → MachineMonad Unit} (h : ∀ w, MaskT (f w)) (w : BitVec n) :
    GK (portOut (Z := Unit) f w) := by
  unfold portOut; exact gk_bind (gk_doMachineOp (h w)) fun _ => gk_pure _
macro_rules | `(tactic| gk_leaf) => `(tactic| (with_reducible refine gk_portOut (fun _ => ?_) _); mt_auto; done)
