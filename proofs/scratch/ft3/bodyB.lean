theorem b_fastFinalise (a0 : Cap) (a1 : Bool) : BK L E K C (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_fastFinalise _ _)

theorem b_capDeleteOne (slot : CslotPtr) : BK L E K C (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_capDeleteOne _)

theorem b_deletingIrqHandler (irq : Irq) : BK L E K C (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_deletingIrqHandler _)

theorem b_finaliseCap (a0 : Cap) (a1 : Bool) : BK L E K C (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_finaliseCap _ _)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem b_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, BK L E K C (f k)) (k : RecDelCall) : BKE L E K C (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, BKE L E K C (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; b_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; b_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> b_auto
    all_goals exact hrec' _

theorem b_recDel (c : RecDelCall) : BKE L E K C (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => b_recDelF hf k) c
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_recDel _)

theorem b_capDelete (slot : CslotPtr) : BKE L E K C (capDelete (Z := Unit) slot) := by
  unfold capDelete; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_capDelete _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem b_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, BK L E K C (f k)) (sl : CslotPtr) : BKE L E K C (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, BKE L E K C (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  b_auto
  all_goals exact hrec' _

theorem b_capRevoke (sl : CslotPtr) : BKE L E K C (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => b_capRevokeF hf k) sl
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_capRevoke _)

theorem b_handleInterrupt (irq : Irq) : BK L E K C (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_handleInterrupt _)

theorem b_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : BKE L E K C (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_installTcbCap _ _ _ _)

theorem b_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : BKE L E K C (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_installTcbFrameCap _ _ _)

theorem b_invokeCnode (i : CnodeInvocation) : BKE L E K C (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_invokeCnode _)

theorem b_invokeIrqHandler (a0 : IrqHandlerInvocation) : BK L E K C (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_invokeIrqHandler _)

theorem b_invokeTcb (a0 : TcbInvocation) : BKE L E K C (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_invokeTcb _)

theorem b_maybeHandleInterrupt (inKernel : Bool) : BK L E K C (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; b_auto
macro_rules | `(tactic| b_leaf) => `(tactic| with_reducible exact b_maybeHandleInterrupt _)
