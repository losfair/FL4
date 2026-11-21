/- g1c: OnlyIdle frame lemmas, part 5 (generated; see SpecInvAllO1). -/
import Fl4Proofs.P3.SpecInvAllO4
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem oi_subframeNode (nodeCap : Cap) (index depth : Data) : OIKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_subframeNode _ _ _)

theorem oi_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDeriveSubframe _ _ _ _)

theorem oi_decodeDomainScheduleConfigure (args : List Data) : OIKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainScheduleConfigure _)

theorem oi_decodeDomainScheduleSetStart (args : List Data) : OIKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainScheduleSetStart _)

theorem oi_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : OIKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainSet _ _)

theorem oi_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : OIKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeDomainInvocation _ _ _)

theorem oi_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : OIK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4GetMr _ _ _)

theorem oi_fl4Arg (buf : Option ObjRef) (i : Nat) : OIKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4Arg _ _)

theorem oi_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4ConfigureSingleStepping _ _)

theorem oi_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4FpuTransfer _ _ _ _)

theorem oi_fl4CheckBpNum (bp : Data) : OIKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4CheckBpNum _)

theorem oi_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4GetBreakpoint _ _)

theorem oi_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, OIKE N (check x0)) : OIKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; oi_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible refine oi_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem oi_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqControlRemapped _ _ _)

theorem oi_fl4ArchCheckIrq (irq : Data) : OIKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchCheckIrq _)

theorem oi_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4IrqControl _ _ _ _ _)

theorem oi_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetBreakpoint _ _)

theorem oi_decodeFl4SetFlags (args : List Data) (t : ObjRef) : OIKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetFlags _ _)

theorem oi_decodeFl4SetTimer (args : List Data) (t : ObjRef) : OIKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4SetTimer _ _)

theorem oi_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OIKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4UnsetBreakpoint _ _)

theorem oi_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : OIKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeFl4TcbExt _ _ _ _ _)

theorem oi_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OIKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqControlInvocation _ _ _ _)

theorem oi_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : OIKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeIrqHandlerInvocation _ _ _)

theorem oi_getScReleased (scPtr : ObjRef) : OIK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getScReleased _)

theorem oi_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextBind _ _)

theorem oi_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextUnbindObject _ _)

theorem oi_decodeSchedContextYieldTo (scPtr : ObjRef) : OIKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextYieldTo _)

theorem oi_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : OIKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedContextInvocation _ _ _)

theorem oi_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : OIKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSchedControlInvocationFlags _ _ _)

theorem oi_rangeCheck (v minV maxV : Word) : OIKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_rangeCheck _ _ _)

theorem oi_decodeSetFlags (args : List Data) (cap : Cap) : OIKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetFlags _ _)

theorem oi_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : OIKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetIpcBuffer _ _ _ _)

theorem oi_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetMcpriority _ _ _ _)

theorem oi_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetPriority _ _ _ _)

theorem oi_isBlocked (thread : ObjRef) : OIK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_isBlocked _)

theorem oi_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : OIKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUpdateSc _ _ _)

theorem oi_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetSchedParams _ _ _ _)

theorem oi_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OIKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetSpace _ _ _ _)

theorem oi_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetTimeoutEp _ _ _)

theorem oi_decodeSetTlsBase (args : List Data) (cap : Cap) : OIKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeSetTlsBase _ _)

theorem oi_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OIKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTcbConfigure _ _ _ _)

theorem oi_decodeUnbindNotification (cap : Cap) : OIKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem oi_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : OIKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTcbInvocation _ _ _ _ _)

theorem oi_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OIKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUntypedInvocation _ _ _ _ _)

theorem oi_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : OIKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeInvocation _ _ _ _ _ _ _ _)

theorem oi_decodePml4Flush (cap : ArchCap) : OIKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodePml4Flush _)

theorem oi_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : OIKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_frameMappingSlot _ _ _ _)

theorem oi_decodeTestAndClearAccessed (cap : ArchCap) : OIKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeTestAndClearAccessed _)

theorem oi_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OIKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem oi_doNbrecvFailedTransfer (thread : ObjRef) : OIK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doNbrecvFailedTransfer _)

theorem oi_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : OIK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_getMrs _ _ _)

theorem oi_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : OIK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleArchFaultReply _ _ _ _)

theorem oi_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : OIK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_handleFaultReply _ _ _ _)

theorem oi_testPossibleSwitchTo (tcbPtr : ObjRef) : OIK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_testPossibleSwitchTo _)

theorem oi_restart (thread : ObjRef) : OIK N (restart (Z := Unit) thread) := by
  unfold restart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_restart _)

theorem oi_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : OIK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_doReplyTransfer _ _ _)

theorem oi_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : OIK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_domainScheduleConfigure _ _ _)

theorem oi_setNextInterrupt  : OIK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_setNextInterrupt)

theorem oi_switchSchedContext  : OIK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_switchSchedContext)

theorem oi_scAndTimer  : OIK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scAndTimer)

theorem oi_scheduleChooseNewThread  : OIK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleChooseNewThread)

theorem oi_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : OIK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_scheduleSwitchThreadFastfail _ _ _ _)

theorem oi_schedule  : OIK N (schedule (Z := Unit)) := by
  unfold schedule; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_schedule)

theorem oi_domainSetStart (index : Nat) : OIK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_domainSetStart _)

theorem oi_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OIKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem oi_performDeriveSubframe (iv : Fl4SubframeInvocation) : OIK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performDeriveSubframe _)

theorem oi_performPml4Flush (a0 : Fl4Pml4Invocation) : OIK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performPml4Flush _)

theorem oi_performTestAndClearAccessed (_slot : ObjRef) : OIK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_performTestAndClearAccessed _)

theorem oi_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : OIKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; oi_auto
macro_rules | `(tactic| oi_leaf) => `(tactic| with_reducible exact oi_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvAll
