theorem si_fastFinalise (a0 : Cap) (a1 : Bool) : SIK (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_fastFinalise _ _)

theorem si_capDeleteOne (slot : CslotPtr) : SIK (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_capDeleteOne _)

theorem si_deletingIrqHandler (irq : Irq) : SIK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_deletingIrqHandler _)

theorem si_schedContextUnbindAllTcbs (scPtr : ObjRef) : SIK (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_schedContextUnbindAllTcbs _)

theorem si_unbindFromSc (tcbPtr : ObjRef) : SIK (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_unbindFromSc _)

theorem si_finaliseCap (a0 : Cap) (a1 : Bool) : SIK (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_finaliseCap _ _)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem si_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, SIK (f k)) (k : RecDelCall) : SIKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, SIKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; si_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; si_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> si_auto
    all_goals exact hrec' _

theorem si_recDel (c : RecDelCall) : SIKE (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => si_recDelF hf k) c
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_recDel _)

theorem si_capDelete (slot : CslotPtr) : SIKE (capDelete (Z := Unit) slot) := by
  unfold capDelete; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_capDelete _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem si_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, SIK (f k)) (sl : CslotPtr) : SIKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, SIKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  si_auto
  all_goals exact hrec' _

theorem si_capRevoke (sl : CslotPtr) : SIKE (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => si_capRevokeF hf k) sl
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_capRevoke _)

theorem si_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : SIK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_sendFaultIpc _ _ _ _)

theorem si_handleTimeout (tptr : ObjRef) (ex : Fault) : SIK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_handleTimeout _ _)

theorem si_endTimeslice (canTimeout : Bool) : SIK (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_endTimeslice _)

theorem si_chargeBudget (consumed : Ticks) (canTimeout : Bool) : SIK (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_chargeBudget _ _)

theorem si_checkBudget  : SIK (checkBudget (Z := Unit)) := by
  unfold checkBudget; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_checkBudget)

theorem si_checkBudgetRestart  : SIK (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_checkBudgetRestart)

theorem si_completeSignal (ntfnptr tptr : ObjRef) : SIK (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_completeSignal _ _)

theorem si_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : SIK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_doReplyTransfer _ _ _)

theorem si_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : SIK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_updateWaitingNtfn _ _ _)

theorem si_sendSignal (ntfnptr : ObjRef) (badge : Badge) : SIK (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_sendSignal _ _)

theorem si_fl4Awaken : SIK (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact si_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_fl4Awaken)

theorem si_handleFault (thread : ObjRef) (ex : Fault) : SIK (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_handleFault _ _)

theorem si_handleInterrupt (irq : Irq) : SIK (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_handleInterrupt _)

theorem si_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    SIK (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  intro σ hσ x hx
  unfold receiveIpc at hx
  obtain ⟨⟨⟨epptr, rts⟩, s1⟩, hy1, hx⟩ := hx
  have hb1 := br_mem_of_sbk (fun _ => by sb_auto) hy1
  try dsimp only at hx
  obtain ⟨y2, hb2, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨⟨ep, s3⟩, hy3, hx⟩ := hx
  have hb3 := br_mem_of_sbk (fun _ => by sb_auto) hy3
  obtain ⟨y4, hb4, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y5, hb5, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  have hI5 : ScInv y5.2 := scInv_of_br hσ (BR.trans hb1 (BR.trans hb2 (BR.trans hb3 (BR.trans hb4 hb5))))
  try dsimp only at hx
  split at hx
  · exact si_completeSignal _ _ _ hI5 _ hx
  · obtain ⟨y6, hy6, hx⟩ := hx
    have hI6 : ScInv y6.2 := (ik_when _ (sik_maybeReturnSc _ _)) _ hI5 _ hy6
    cases ep with
    | sendEP q => (try dsimp only at hx); exact sik_receiveIpc_send _ _ _ _ _ hI6 _ hx
    | _ => (try dsimp only at hx); exact sik_fin (fun _ => by sb_auto) hI6 hx
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_receiveIpc _ _ _ _)

theorem si_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : SIK (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_receiveSignalBlocked _ _ _)

theorem si_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : SIK (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_receiveSignal _ _ _)

theorem si_handleRecv (isBlocking canReply : Bool) : SIK (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_handleRecv _ _)

theorem si_handleYield  : SIK (handleYield (Z := Unit)) := by
  unfold handleYield; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_handleYield)

theorem si_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : SIKE (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_installTcbCap _ _ _ _)

theorem si_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : SIKE (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_installTcbFrameCap _ _ _)

theorem si_invokeCnode (i : CnodeInvocation) : SIKE (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_invokeCnode _)

theorem si_invokeIrqHandler (a0 : IrqHandlerInvocation) : SIK (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_invokeIrqHandler _)

theorem si_maybeHandleInterrupt (inKernel : Bool) : SIK (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_maybeHandleInterrupt _)

theorem si_preemptionPath  : SIK (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; si_auto
macro_rules | `(tactic| si_leaf) => `(tactic| with_reducible exact si_preemptionPath)
