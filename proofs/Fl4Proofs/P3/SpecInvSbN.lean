/-
P3 (DESIGN.md §9), invariant line G1 (sb2): **the performs outside the gap and
the non-syscall events, one lemma per constructor** (spec side only; imports
SpecInvSbX2). Each arm is stated after `cases` and `simp only` of the
dispatcher at that arm, then closed by the SIK leaves (ut8 / nq3's recipe: no
automation over the whole `fl4PerformInvocation` / `handleEvent` match).
-/
import Fl4Proofs.P3.SpecInvSbX2
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `invoke_sched_context` -/

theorem si_scConsumed (c : ObjRef) : SIK (invokeSchedContext (Z := Unit) (.invokeSchedContextConsumed c)) := by
  simp only [invokeSchedContext]; exact sik_of_sbk fun _ => sb_returnConsumed _

theorem si_scUnbindObject (c : ObjRef) (cap : Cap) :
    SIK (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbindObject c cap)) := by
  cases cap
  case threadCap t =>
    simp only [invokeSchedContext]; exact ik_bind (sik_schedContextUnbindTcb _) fun _ => ik_pure _
  case notificationCap n b r =>
    simp only [invokeSchedContext]
    exact sik_of_sbk fun _ => ik_bind (sb_schedContextUnbindNtfn _) fun _ => ik_pure _
  all_goals (simp only [invokeSchedContext]; exact ik_fail)

theorem si_scUnbind (c : ObjRef) : SIK (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbind c)) := by
  simp only [invokeSchedContext]
  exact ik_bind (si_schedContextUnbindAllTcbs _) fun _ => sik_of_sbk fun _ =>
    ik_bind (sb_schedContextUnbindNtfn _) fun _ => ik_bind (sb_schedContextUnbindReply _) fun _ => ik_pure _

theorem si_scYieldTo (c : ObjRef) : SIK (invokeSchedContext (Z := Unit) (.invokeSchedContextYieldTo c)) := by
  simp only [invokeSchedContext]; exact sik_of_sbk fun _ => sb_schedContextYieldTo _

/-- `invoke_sched_context` but Bind. -/
theorem si_invokeSchedContextNB (i : SchedContextInvocation) (h : ∀ c cap, i ≠ .invokeSchedContextBind c cap) :
    SIK (invokeSchedContext (Z := Unit) i) := by
  cases i with
  | invokeSchedContextConsumed c => exact si_scConsumed c
  | invokeSchedContextBind c cap => exact absurd rfl (h c cap)
  | invokeSchedContextUnbindObject c cap => exact si_scUnbindObject c cap
  | invokeSchedContextUnbind c => exact si_scUnbind c
  | invokeSchedContextYieldTo c => exact si_scYieldTo c

/-! ## `invoke_tcb` -/

theorem si_tcbSuspend (t : ObjRef) : SIKE (invokeTcb (Z := Unit) (.suspend t)) := by
  simp only [invokeTcb]; exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_suspend _) fun _ => ik_pure _)

theorem si_tcbResume (t : ObjRef) : SIKE (invokeTcb (Z := Unit) (.resume t)) := by
  simp only [invokeTcb]; exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_restart _) fun _ => ik_pure _)

theorem si_tcbCaps (t : ObjRef) (sl : CslotPtr) (fh th cr vr : Option (Cap × CslotPtr))
    (buf : Option (VSpaceRef × Option (Cap × CslotPtr))) :
    SIKE (invokeTcb (Z := Unit) (.threadControlCaps t sl fh th cr vr buf)) := by
  simp only [invokeTcb]
  exact ike_bind (si_installTcbCap _ _ _ _) fun _ => ike_bind (si_installTcbCap _ _ _ _) fun _ =>
    ike_bind (si_installTcbCap _ _ _ _) fun _ => ike_bind (si_installTcbCap _ _ _ _) fun _ =>
    ike_bind (si_installTcbFrameCap _ _ _) fun _ => ike_returnOk _

theorem si_tcbCopy (d s : ObjRef) (a b c e : Bool) (ar : ArchCopyRegisterSets) :
    SIKE (invokeTcb (Z := Unit) (.copyRegisters d s a b c e ar)) := by
  simp only [invokeTcb]; exact ike_liftE (sik_of_sbk fun _ => by sb_auto)

theorem si_tcbRead (s : ObjRef) (a : Bool) (n : Word) (ar : ArchCopyRegisterSets) :
    SIKE (invokeTcb (Z := Unit) (.readRegisters s a n ar)) := by
  simp only [invokeTcb]; exact ike_liftE (sik_of_sbk fun _ => by sb_auto)

theorem si_tcbWrite (d : ObjRef) (a : Bool) (vs : List Word) (ar : ArchCopyRegisterSets) :
    SIKE (invokeTcb (Z := Unit) (.writeRegisters d a vs ar)) := by
  simp only [invokeTcb]; exact ike_liftE (sik_of_sbk fun _ => by sb_auto)

theorem si_tcbNtfn (t : ObjRef) (n : Option ObjRef) :
    SIKE (invokeTcb (Z := Unit) (.notificationControl t n)) := by
  cases n
  · simp only [invokeTcb]
    exact ike_liftE (sik_of_sbk fun _ => ik_bind (sb_unbindNotification _) fun _ => ik_pure _)
  · simp only [invokeTcb]
    exact ike_liftE (sik_of_sbk fun _ => ik_bind (sb_bindNotification _ _) fun _ => ik_pure _)

theorem si_tcbTls (t : ObjRef) (b : Word) : SIKE (invokeTcb (Z := Unit) (.setTLSBase t b)) := by
  simp only [invokeTcb]; exact ike_liftE (sik_of_sbk fun _ => by sb_auto)

theorem si_tcbFlags (t : ObjRef) (c s : TcbFlags) : SIKE (invokeTcb (Z := Unit) (.setFlags t c s)) := by
  simp only [invokeTcb]; exact ike_liftE (sik_of_sbk fun _ => by sb_auto)

/-- `invoke_tcb` but threadControlSched. -/
theorem si_invokeTcbNS (i : TcbInvocation) (h : ∀ a b c d e f, i ≠ .threadControlSched a b c d e f) :
    SIKE (invokeTcb (Z := Unit) i) := by
  cases i with
  | threadControlSched a b c d e f => exact absurd rfl (h a b c d e f)
  | suspend t => exact si_tcbSuspend t
  | resume t => exact si_tcbResume t
  | threadControlCaps t sl fh th cr vr buf => exact si_tcbCaps t sl fh th cr vr buf
  | copyRegisters d s a b c e ar => exact si_tcbCopy d s a b c e ar
  | readRegisters s a n ar => exact si_tcbRead s a n ar
  | writeRegisters d a vs ar => exact si_tcbWrite d a vs ar
  | notificationControl t n => exact si_tcbNtfn t n
  | setTLSBase t b => exact si_tcbTls t b
  | setFlags t c s => exact si_tcbFlags t c s

/-! ## `perform_invocation` arms -/

section Perf
variable (blk call don : Bool)

theorem si_pfEndpoint (ep : ObjRef) (b : Word) (g gr : Bool) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeEndpoint ep b g gr)) := by
  simp only [fl4PerformInvocation, withoutPreemption]
  exact ike_liftE (ik_bind (ik_gets _) fun _ => ik_bind (sik_sendIpc _ _ _ _ _ _ _ _) fun _ => ik_pure _)

theorem si_pfNtfn (n : ObjRef) (b : Word) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeNotification n b)) := by
  simp only [fl4PerformInvocation, withoutPreemption]
  exact ike_bind (ike_liftE (si_sendSignal _ _)) fun _ => ike_returnOk _

theorem si_pfReply (r : ObjRef) (g : Bool) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeReply r g)) := by
  simp only [fl4PerformInvocation]
  exact ike_liftE (ik_bind (ik_gets _) fun _ => ik_bind (si_doReplyTransfer _ _ _) fun _ => ik_pure _)

theorem si_pfTcb (i : TcbInvocation) (h : ∀ a b c d e f, i ≠ .threadControlSched a b c d e f) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeTCB i)) := by
  simp only [fl4PerformInvocation]; exact si_invokeTcbNS i h

theorem si_pfFl4Tcb (i : Fl4TcbInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeFl4TCB i)) := by
  simp only [fl4PerformInvocation]; exact sike_of_sbke fun _ => sb_invokeFl4Tcb _

theorem si_pfDomain (i : DomainInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain i)) := by
  simp only [fl4PerformInvocation]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_invokeDomain _) fun _ => ik_pure _)

theorem si_pfSc (i : SchedContextInvocation) (h : ∀ c cap, i ≠ .invokeSchedContextBind c cap) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedContext i)) := by
  simp only [fl4PerformInvocation, withoutPreemption]; exact ike_liftE (si_invokeSchedContextNB i h)

theorem si_pfSchedControl (i : SchedControlInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedControl i)) := by
  simp only [fl4PerformInvocation]
  exact ike_bind (ike_liftE (si_invokeSchedControlConfigureFlags _)) fun _ => ike_returnOk _

theorem si_pfCnode (i : CnodeInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeCNode i)) := by
  simp only [fl4PerformInvocation]; exact ike_bind (si_invokeCnode _) fun _ => ike_returnOk _

theorem si_pfIrqC (i : Fl4IrqControlInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQControl i)) := by
  simp only [fl4PerformInvocation]
  exact ike_bind (sike_of_sbke fun _ => sb_invokeFl4IrqControl _) fun _ => ike_returnOk _

theorem si_pfIrqH (i : IrqHandlerInvocation) :
    SIKE (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQHandler i)) := by
  simp only [fl4PerformInvocation]; exact ike_bind (ike_liftE (si_invokeIrqHandler _)) fun _ => ike_returnOk _

end Perf

/-! ## The other events -/

theorem si_evInterrupt : SIKE (handleEvent (Z := Unit) .interrupt) := by
  simp only [handleEvent, withoutPreemption]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_updateTimeStamp) fun _ =>
    ik_bind si_checkBudget fun _ => si_maybeHandleInterrupt _)

theorem si_evUnknown (n : Nat) : SIKE (handleEvent (Z := Unit) (.unknownSyscall n)) := by
  simp only [handleEvent, withoutPreemption]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_updateTimeStamp) fun _ =>
    ik_bind si_checkBudgetRestart fun _ => ik_when _ (ik_bind (ik_gets _) fun _ => si_handleFault _ _))

theorem si_evUser (w1 w2 : Word) : SIKE (handleEvent (Z := Unit) (.userLevelFault w1 w2)) := by
  simp only [handleEvent, withoutPreemption]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_updateTimeStamp) fun _ =>
    ik_bind si_checkBudgetRestart fun _ => ik_when _ (ik_bind (ik_gets _) fun _ => si_handleFault _ _))

theorem si_evVm (ft : VMFaultType) : SIKE (handleEvent (Z := Unit) (.vmFaultEvent ft)) := by
  simp only [handleEvent, withoutPreemption]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_updateTimeStamp) fun _ =>
    ik_bind si_checkBudgetRestart fun _ => ik_when _ (ik_bind (ik_gets _) fun _ =>
      ik_catch (sike_of_sbke fun _ => sb_handleVmFault _ _) fun _ => si_handleFault _ _))

theorem si_evHyp (ht : HypFaultType) : SIKE (handleEvent (Z := Unit) (.hypervisorEvent ht)) := by
  simp only [handleEvent, withoutPreemption]
  exact ike_liftE (ik_bind (sik_of_sbk fun _ => sb_updateTimeStamp) fun _ =>
    ik_bind si_checkBudgetRestart fun _ => ik_when _ (ik_bind (ik_gets _) fun _ =>
      sik_of_sbk fun _ => sb_handleHypervisorFault _ _))

theorem si_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) : SIKE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | interrupt => exact si_evInterrupt
  | unknownSyscall n => exact si_evUnknown n
  | userLevelFault w1 w2 => exact si_evUser w1 w2
  | vmFaultEvent ft => exact si_evVm ft
  | hypervisorEvent ht => exact si_evHyp ht

end

end Fl4Proofs.P3.SInvB
