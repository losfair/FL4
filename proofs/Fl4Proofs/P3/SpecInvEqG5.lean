
/- epq1: generated frames `PZK` (sg1's SpecInvSgI5 renamed, the refill writers and the configure path removed; see SpecInvEqG1). -/
import Fl4Proofs.P3.SpecInvEqG4
open Classical

namespace Fl4Proofs.P3.SInvE
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000


theorem pz_subframeNode (nodeCap : Cap) (index depth : Data) : PZKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_subframeNode _ _ _)

theorem pz_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : PZKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeDeriveSubframe _ _ _ _)

theorem pz_decodeDomainScheduleConfigure (args : List Data) : PZKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeDomainScheduleConfigure _)

theorem pz_decodeDomainScheduleSetStart (args : List Data) : PZKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeDomainScheduleSetStart _)

theorem pz_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : PZKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeDomainSet _ _)

theorem pz_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : PZKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeDomainInvocation _ _ _)

theorem pz_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : PZK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4GetMr _ _ _)

theorem pz_fl4Arg (buf : Option ObjRef) (i : Nat) : PZKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4Arg _ _)

theorem pz_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : PZKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4ConfigureSingleStepping _ _)

theorem pz_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : PZKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4FpuTransfer _ _ _ _)

theorem pz_fl4CheckBpNum (bp : Data) : PZKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4CheckBpNum _)

theorem pz_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : PZKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4GetBreakpoint _ _)

theorem pz_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, PZKE (check x0)) : PZKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; pz_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible refine pz_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem pz_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : PZKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeIrqControlRemapped _ _ _)

theorem pz_fl4ArchCheckIrq (irq : Data) : PZKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4ArchCheckIrq _)

theorem pz_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : PZKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4IrqControl _ _ _ _ _)

theorem pz_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : PZKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4SetBreakpoint _ _)

theorem pz_decodeFl4SetFlags (args : List Data) (t : ObjRef) : PZKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4SetFlags _ _)

theorem pz_decodeFl4SetTimer (args : List Data) (t : ObjRef) : PZKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4SetTimer _ _)

theorem pz_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : PZKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4UnsetBreakpoint _ _)

theorem pz_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : PZKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeFl4TcbExt _ _ _ _ _)

theorem pz_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : PZKE (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeIrqControlInvocation _ _ _ _)

theorem pz_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : PZKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeIrqHandlerInvocation _ _ _)

theorem pz_getScReleased (scPtr : ObjRef) : PZK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getScReleased _)

theorem pz_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : PZKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSchedContextBind _ _)

theorem pz_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : PZKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSchedContextUnbindObject _ _)

theorem pz_decodeSchedContextYieldTo (scPtr : ObjRef) : PZKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSchedContextYieldTo _)

theorem pz_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : PZKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSchedContextInvocation _ _ _)

theorem pz_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : PZKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSchedControlInvocationFlags _ _ _)

theorem pz_rangeCheck (v minV maxV : Word) : PZKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_rangeCheck _ _ _)

theorem pz_decodeSetFlags (args : List Data) (cap : Cap) : PZKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetFlags _ _)

theorem pz_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : PZKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetIpcBuffer _ _ _ _)

theorem pz_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetMcpriority _ _ _ _)

theorem pz_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetPriority _ _ _ _)

theorem pz_isBlocked (thread : ObjRef) : PZK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_isBlocked _)

theorem pz_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : PZKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeUpdateSc _ _ _)

theorem pz_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetSchedParams _ _ _ _)

theorem pz_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : PZKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetSpace _ _ _ _)

theorem pz_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetTimeoutEp _ _ _)

theorem pz_decodeSetTlsBase (args : List Data) (cap : Cap) : PZKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeSetTlsBase _ _)

theorem pz_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : PZKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeTcbConfigure _ _ _ _)

theorem pz_decodeUnbindNotification (cap : Cap) : PZKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem pz_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : PZKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeTcbInvocation _ _ _ _ _)

theorem pz_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : PZKE (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeUntypedInvocation _ _ _ _ _)

theorem pz_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : PZKE (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeInvocation _ _ _ _ _ _ _ _)

theorem pz_decodePml4Flush (cap : ArchCap) : PZKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodePml4Flush _)

theorem pz_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : PZKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_frameMappingSlot _ _ _ _)

theorem pz_decodeTestAndClearAccessed (cap : ArchCap) : PZKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeTestAndClearAccessed _)

theorem pz_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : PZKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem pz_doNbrecvFailedTransfer (thread : ObjRef) : PZK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_doNbrecvFailedTransfer _)

theorem pz_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : PZK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_getMrs _ _ _)

theorem pz_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : PZK (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleArchFaultReply _ _ _ _)

theorem pz_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : PZK (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_handleFaultReply _ _ _ _)

theorem pz_testPossibleSwitchTo (tcbPtr : ObjRef) : PZK (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_testPossibleSwitchTo _)

theorem pz_restart (thread : ObjRef) : PZK (restart (Z := Unit) thread) := by
  unfold restart; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_restart _)

theorem pz_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : PZK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_doReplyTransfer _ _ _)

theorem pz_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : PZK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_domainScheduleConfigure _ _ _)

theorem pz_setNextInterrupt  : PZK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_setNextInterrupt)

theorem pz_switchSchedContext  : PZK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_switchSchedContext)

theorem pz_scAndTimer  : PZK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_scAndTimer)

theorem pz_scheduleChooseNewThread  : PZK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  refine ik_bind (ik_gets _) fun _ => ik_bind (ik_when _ (ik_bind (by pz_auto) fun _ => by pz_auto)) fun _ => ?_
  exact ik_bind pz_chooseThread fun _ => by unfold setSchedulerAction; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_scheduleChooseNewThread)

theorem pz_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : PZK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_scheduleSwitchThreadFastfail _ _ _ _)

theorem pz_schedule  : PZK (schedule (Z := Unit)) := by
  unfold schedule; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_schedule)

theorem pz_domainSetStart (index : Nat) : PZK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_domainSetStart _)

theorem pz_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : PZKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem pz_performDeriveSubframe (iv : Fl4SubframeInvocation) : PZK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performDeriveSubframe _)

theorem pz_performPml4Flush (a0 : Fl4Pml4Invocation) : PZK (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performPml4Flush _)

theorem pz_performTestAndClearAccessed (_slot : ObjRef) : PZK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_performTestAndClearAccessed _)

theorem pz_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : PZKE (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; pz_auto
macro_rules | `(tactic| pz_leaf) => `(tactic| with_reducible exact pz_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvE
