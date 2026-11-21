theorem fg_switchToThread (t : ObjRef) : FGK Fq Sq (fun _ => True) (switchToThread (Z := Unit) t) := by
  unfold switchToThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchToThread _)

theorem fg_guardedSwitchTo (thread : ObjRef) : FGK Fq Sq (fun _ => True) (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_guardedSwitchTo _)

theorem fg_switchToIdleThread  : FGK Fq Sq (fun _ => True) (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchToIdleThread)

theorem fg_chooseThread  : FGK Fq Sq (fun _ => True) (chooseThread (Z := Unit)) := by
  unfold chooseThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_chooseThread)

theorem fg_scheduleChooseNewThread  : FGK Fq Sq (fun _ => True) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scheduleChooseNewThread)

theorem fg_schedule  : FGK Fq Sq (fun _ => True) (schedule (Z := Unit)) := by
  unfold schedule; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedule)
