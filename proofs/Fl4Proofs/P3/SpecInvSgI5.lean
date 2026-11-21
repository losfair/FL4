/- sg1: idle-thread frame lemmas `IdK t` (ut7's SpecInvUtNK5 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvSgI4
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem idk_subframeNode (nodeCap : Cap) (index depth : Data) : IdKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_subframeNode _ _ _)

theorem idk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : IdKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeDeriveSubframe _ _ _ _)

theorem idk_decodeDomainScheduleConfigure (args : List Data) : IdKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeDomainScheduleConfigure _)

theorem idk_decodeDomainScheduleSetStart (args : List Data) : IdKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeDomainScheduleSetStart _)

theorem idk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : IdKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeDomainSet _ _)

theorem idk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : IdKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeDomainInvocation _ _ _)

theorem idk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : IdK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4GetMr _ _ _)

theorem idk_fl4Arg (buf : Option ObjRef) (i : Nat) : IdKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4Arg _ _)

theorem idk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : IdKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4ConfigureSingleStepping _ _)

theorem idk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : IdKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4FpuTransfer _ _ _ _)

theorem idk_fl4CheckBpNum (bp : Data) : IdKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4CheckBpNum _)

theorem idk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IdKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4GetBreakpoint _ _)

theorem idk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, IdKE N (check x0)) : IdKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; idk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible refine idk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem idk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IdKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeIrqControlRemapped _ _ _)

theorem idk_fl4ArchCheckIrq (irq : Data) : IdKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4ArchCheckIrq _)

theorem idk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IdKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4IrqControl _ _ _ _ _)

theorem idk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IdKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4SetBreakpoint _ _)

theorem idk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : IdKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4SetFlags _ _)

theorem idk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : IdKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4SetTimer _ _)

theorem idk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IdKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4UnsetBreakpoint _ _)

theorem idk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : IdKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeFl4TcbExt _ _ _ _ _)

theorem idk_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IdKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeIrqControlInvocation _ _ _ _)

theorem idk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : IdKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeIrqHandlerInvocation _ _ _)

theorem idk_getScReleased (scPtr : ObjRef) : IdK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getScReleased _)

theorem idk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : IdKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSchedContextBind _ _)

theorem idk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : IdKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSchedContextUnbindObject _ _)

theorem idk_decodeSchedContextYieldTo (scPtr : ObjRef) : IdKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSchedContextYieldTo _)

theorem idk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : IdKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSchedContextInvocation _ _ _)

theorem idk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : IdKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSchedControlInvocationFlags _ _ _)

theorem idk_rangeCheck (v minV maxV : Word) : IdKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_rangeCheck _ _ _)

theorem idk_decodeSetFlags (args : List Data) (cap : Cap) : IdKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetFlags _ _)

theorem idk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : IdKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetIpcBuffer _ _ _ _)

theorem idk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetMcpriority _ _ _ _)

theorem idk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetPriority _ _ _ _)

theorem idk_isBlocked (thread : ObjRef) : IdK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_isBlocked _)

theorem idk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : IdKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeUpdateSc _ _ _)

theorem idk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetSchedParams _ _ _ _)

theorem idk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IdKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetSpace _ _ _ _)

theorem idk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetTimeoutEp _ _ _)

theorem idk_decodeSetTlsBase (args : List Data) (cap : Cap) : IdKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeSetTlsBase _ _)

theorem idk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IdKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeTcbConfigure _ _ _ _)

theorem idk_decodeUnbindNotification (cap : Cap) : IdKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem idk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : IdKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeTcbInvocation _ _ _ _ _)

theorem idk_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IdKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeUntypedInvocation _ _ _ _ _)

theorem idk_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : IdKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeInvocation _ _ _ _ _ _ _ _)

theorem idk_decodePml4Flush (cap : ArchCap) : IdKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodePml4Flush _)

theorem idk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : IdKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_frameMappingSlot _ _ _ _)

theorem idk_decodeTestAndClearAccessed (cap : ArchCap) : IdKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeTestAndClearAccessed _)

theorem idk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IdKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem idk_doNbrecvFailedTransfer (thread : ObjRef) : IdK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_doNbrecvFailedTransfer _)

theorem idk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : IdK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_getMrs _ _ _)

theorem idk_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : IdK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleArchFaultReply _ _ _ _)

theorem idk_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : IdK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_handleFaultReply _ _ _ _)

theorem idk_testPossibleSwitchTo (tcbPtr : ObjRef) : IdK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_testPossibleSwitchTo _)

theorem idk_restart (thread : ObjRef) : IdK N (restart (Z := Unit) thread) := by
  unfold restart; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_restart _)

theorem idk_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IdK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_doReplyTransfer _ _ _)

theorem idk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : IdK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_domainScheduleConfigure _ _ _)

theorem idk_setNextInterrupt  : IdK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_setNextInterrupt)

theorem idk_switchSchedContext  : IdK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_switchSchedContext)

theorem idk_scAndTimer  : IdK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_scAndTimer)

theorem idk_scheduleChooseNewThread  : IdK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_scheduleChooseNewThread)

theorem idk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : IdK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_scheduleSwitchThreadFastfail _ _ _ _)

theorem idk_schedule  : IdK N (schedule (Z := Unit)) := by
  unfold schedule; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_schedule)

theorem idk_domainSetStart (index : Nat) : IdK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_domainSetStart _)

theorem idk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IdKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem idk_performDeriveSubframe (iv : Fl4SubframeInvocation) : IdK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performDeriveSubframe _)

theorem idk_performPml4Flush (a0 : Fl4Pml4Invocation) : IdK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performPml4Flush _)

theorem idk_performTestAndClearAccessed (_slot : ObjRef) : IdK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_performTestAndClearAccessed _)

theorem idk_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : IdKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; idk_auto
macro_rules | `(tactic| idk_leaf) => `(tactic| with_reducible exact idk_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvG
