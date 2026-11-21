/- sl1: idle-SC frame lemmas `IsK t` (sg1 SpecInvSgI5 renamed; see SpecInvSlI1). -/
import Fl4Proofs.P3.SpecInvSlI4
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem isk_subframeNode (nodeCap : Cap) (index depth : Data) : IsKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_subframeNode _ _ _)

theorem isk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : IsKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeDeriveSubframe _ _ _ _)

theorem isk_decodeDomainScheduleConfigure (args : List Data) : IsKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeDomainScheduleConfigure _)

theorem isk_decodeDomainScheduleSetStart (args : List Data) : IsKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeDomainScheduleSetStart _)

theorem isk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : IsKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeDomainSet _ _)

theorem isk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : IsKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeDomainInvocation _ _ _)

theorem isk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : IsK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4GetMr _ _ _)

theorem isk_fl4Arg (buf : Option ObjRef) (i : Nat) : IsKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4Arg _ _)

theorem isk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : IsKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4ConfigureSingleStepping _ _)

theorem isk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : IsKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4FpuTransfer _ _ _ _)

theorem isk_fl4CheckBpNum (bp : Data) : IsKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4CheckBpNum _)

theorem isk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IsKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4GetBreakpoint _ _)

theorem isk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, IsKE N (check x0)) : IsKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; isk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible refine isk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem isk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IsKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeIrqControlRemapped _ _ _)

theorem isk_fl4ArchCheckIrq (irq : Data) : IsKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4ArchCheckIrq _)

theorem isk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IsKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4IrqControl _ _ _ _ _)

theorem isk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IsKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4SetBreakpoint _ _)

theorem isk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : IsKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4SetFlags _ _)

theorem isk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : IsKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4SetTimer _ _)

theorem isk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IsKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4UnsetBreakpoint _ _)

theorem isk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : IsKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeFl4TcbExt _ _ _ _ _)

theorem isk_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IsKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeIrqControlInvocation _ _ _ _)

theorem isk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : IsKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeIrqHandlerInvocation _ _ _)

theorem isk_getScReleased (scPtr : ObjRef) : IsK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getScReleased _)

theorem isk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : IsKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSchedContextBind _ _)

theorem isk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : IsKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSchedContextUnbindObject _ _)

theorem isk_decodeSchedContextYieldTo (scPtr : ObjRef) : IsKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSchedContextYieldTo _)

theorem isk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : IsKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSchedContextInvocation _ _ _)

theorem isk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : IsKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSchedControlInvocationFlags _ _ _)

theorem isk_rangeCheck (v minV maxV : Word) : IsKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_rangeCheck _ _ _)

theorem isk_decodeSetFlags (args : List Data) (cap : Cap) : IsKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetFlags _ _)

theorem isk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : IsKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetIpcBuffer _ _ _ _)

theorem isk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetMcpriority _ _ _ _)

theorem isk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetPriority _ _ _ _)

theorem isk_isBlocked (thread : ObjRef) : IsK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_isBlocked _)

theorem isk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : IsKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeUpdateSc _ _ _)

theorem isk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetSchedParams _ _ _ _)

theorem isk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IsKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetSpace _ _ _ _)

theorem isk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetTimeoutEp _ _ _)

theorem isk_decodeSetTlsBase (args : List Data) (cap : Cap) : IsKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeSetTlsBase _ _)

theorem isk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IsKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeTcbConfigure _ _ _ _)

theorem isk_decodeUnbindNotification (cap : Cap) : IsKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem isk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : IsKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeTcbInvocation _ _ _ _ _)

theorem isk_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IsKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeUntypedInvocation _ _ _ _ _)

theorem isk_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : IsKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeInvocation _ _ _ _ _ _ _ _)

theorem isk_decodePml4Flush (cap : ArchCap) : IsKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodePml4Flush _)

theorem isk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : IsKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_frameMappingSlot _ _ _ _)

theorem isk_decodeTestAndClearAccessed (cap : ArchCap) : IsKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeTestAndClearAccessed _)

theorem isk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IsKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem isk_doNbrecvFailedTransfer (thread : ObjRef) : IsK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_doNbrecvFailedTransfer _)

theorem isk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : IsK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_getMrs _ _ _)

theorem isk_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : IsK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleArchFaultReply _ _ _ _)

theorem isk_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : IsK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_handleFaultReply _ _ _ _)

theorem isk_testPossibleSwitchTo (tcbPtr : ObjRef) : IsK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_testPossibleSwitchTo _)

theorem isk_restart (thread : ObjRef) : IsK N (restart (Z := Unit) thread) := by
  unfold restart; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_restart _)

theorem isk_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IsK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_doReplyTransfer _ _ _)

theorem isk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : IsK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_domainScheduleConfigure _ _ _)

theorem isk_setNextInterrupt  : IsK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_setNextInterrupt)

theorem isk_switchSchedContext  : IsK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_switchSchedContext)

theorem isk_scAndTimer  : IsK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_scAndTimer)

theorem isk_scheduleChooseNewThread  : IsK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_scheduleChooseNewThread)

theorem isk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : IsK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_scheduleSwitchThreadFastfail _ _ _ _)

theorem isk_schedule  : IsK N (schedule (Z := Unit)) := by
  unfold schedule; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_schedule)

theorem isk_domainSetStart (index : Nat) : IsK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_domainSetStart _)

theorem isk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IsKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem isk_performDeriveSubframe (iv : Fl4SubframeInvocation) : IsK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performDeriveSubframe _)

theorem isk_performPml4Flush (a0 : Fl4Pml4Invocation) : IsK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performPml4Flush _)

theorem isk_performTestAndClearAccessed (_slot : ObjRef) : IsK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_performTestAndClearAccessed _)

theorem isk_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : IsKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; isk_auto
macro_rules | `(tactic| isk_leaf) => `(tactic| with_reducible exact isk_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvL
