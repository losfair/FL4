/-- The syscall event of FL4's `handle_event`. -/
theorem gk_fl4HandleEvent_sys (rep : Bool) (c : Syscall) :
    GKE (fl4HandleEvent (Z := Unit) rep (.syscallEvent c)) := by
  unfold fl4HandleEvent; gk_auto

/-- The interrupt event (l4v's `handle_event Interrupt`). -/
theorem gk_fl4HandleEvent_irq (rep : Bool) : GKE (fl4HandleEvent (Z := Unit) rep .interrupt) := by
  unfold fl4HandleEvent handleEvent; gk_auto
