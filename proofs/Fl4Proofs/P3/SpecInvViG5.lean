
/- vi1: generated frames `IK (VIT N S T b)` (sg1's SpecInvSgI5 renamed, the idle-relevant writers removed; see SpecInvViG1). -/
import Fl4Proofs.P3.SpecInvViG4
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}

theorem vi_subframeNode (nodeCap : Cap) (index depth : Data) : IKE (VIT N S T b) (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_subframeNode _ _ _)

theorem vi_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeDeriveSubframe _ _ _ _)

theorem vi_decodeDomainScheduleConfigure (args : List Data) : IKE (VIT N S T b) (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeDomainScheduleConfigure _)

theorem vi_decodeDomainScheduleSetStart (args : List Data) : IKE (VIT N S T b) (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeDomainScheduleSetStart _)

theorem vi_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeDomainSet _ _)

theorem vi_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeDomainInvocation _ _ _)

theorem vi_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : IK (VIT N S T b) (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4GetMr _ _ _)

theorem vi_fl4Arg (buf : Option ObjRef) (i : Nat) : IKE (VIT N S T b) (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4Arg _ _)

theorem vi_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4ConfigureSingleStepping _ _)

theorem vi_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4FpuTransfer _ _ _ _)

theorem vi_fl4CheckBpNum (bp : Data) : IKE (VIT N S T b) (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4CheckBpNum _)

theorem vi_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4GetBreakpoint _ _)

theorem vi_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, IKE (VIT N S T b) (check x0)) : IKE (VIT N S T b) (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; vi_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem vi_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IKE (VIT N S T b) (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeIrqControlRemapped _ _ _)

theorem vi_fl4ArchCheckIrq (irq : Data) : IKE (VIT N S T b) (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4ArchCheckIrq _)

theorem vi_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IKE (VIT N S T b) (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4IrqControl _ _ _ _ _)

theorem vi_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4SetBreakpoint _ _)

theorem vi_decodeFl4SetFlags (args : List Data) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4SetFlags _ _)

theorem vi_decodeFl4SetTimer (args : List Data) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4SetTimer _ _)

theorem vi_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IKE (VIT N S T b) (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4UnsetBreakpoint _ _)

theorem vi_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : IKE (VIT N S T b) (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeFl4TcbExt _ _ _ _ _)

theorem vi_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IKE (VIT N S T b) (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeIrqControlInvocation _ _ _ _)

theorem vi_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeIrqHandlerInvocation _ _ _)

theorem vi_getScReleased (scPtr : ObjRef) : IK (VIT N S T b) (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getScReleased _)

theorem vi_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : IKE (VIT N S T b) (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSchedContextBind _ _)

theorem vi_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : IKE (VIT N S T b) (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSchedContextUnbindObject _ _)

theorem vi_decodeSchedContextYieldTo (scPtr : ObjRef) : IKE (VIT N S T b) (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSchedContextYieldTo _)

theorem vi_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : IKE (VIT N S T b) (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSchedContextInvocation _ _ _)

theorem vi_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : IKE (VIT N S T b) (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSchedControlInvocationFlags _ _ _)

theorem vi_rangeCheck (v minV maxV : Word) : IKE (VIT N S T b) (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_rangeCheck _ _ _)

theorem vi_decodeSetFlags (args : List Data) (cap : Cap) : IKE (VIT N S T b) (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetFlags _ _)

theorem vi_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetIpcBuffer _ _ _ _)

theorem vi_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetMcpriority _ _ _ _)

theorem vi_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetPriority _ _ _ _)

theorem vi_isBlocked (thread : ObjRef) : IK (VIT N S T b) (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isBlocked _)

theorem vi_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : IKE (VIT N S T b) (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeUpdateSc _ _ _)

theorem vi_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetSchedParams _ _ _ _)

theorem vi_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetSpace _ _ _ _)

theorem vi_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetTimeoutEp _ _ _)

theorem vi_decodeSetTlsBase (args : List Data) (cap : Cap) : IKE (VIT N S T b) (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeSetTlsBase _ _)

theorem vi_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeTcbConfigure _ _ _ _)

theorem vi_decodeUnbindNotification (cap : Cap) : IKE (VIT N S T b) (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem vi_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : IKE (VIT N S T b) (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeTcbInvocation _ _ _ _ _)

theorem vi_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IKE (VIT N S T b) (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeUntypedInvocation _ _ _ _ _)

theorem vi_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : IKE (VIT N S T b) (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeInvocation _ _ _ _ _ _ _ _)

theorem vi_decodePml4Flush (cap : ArchCap) : IKE (VIT N S T b) (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodePml4Flush _)

theorem vi_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : IKE (VIT N S T b) (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_frameMappingSlot _ _ _ _)

theorem vi_decodeTestAndClearAccessed (cap : ArchCap) : IKE (VIT N S T b) (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeTestAndClearAccessed _)

theorem vi_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IKE (VIT N S T b) (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem vi_doNbrecvFailedTransfer (thread : ObjRef) : IK (VIT N S T b) (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_doNbrecvFailedTransfer _)

theorem vi_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : IK (VIT N S T b) (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getMrs _ _ _)

theorem vi_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : IK (VIT N S T b) (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleArchFaultReply _ _ _ _)

theorem vi_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : IK (VIT N S T b) (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_handleFaultReply _ _ _ _)

theorem vi_testPossibleSwitchTo (tcbPtr : ObjRef) : IK (VIT N S T b) (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_testPossibleSwitchTo _)

theorem vi_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : IK (VIT N S T b) (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_domainScheduleConfigure _ _ _)

theorem vi_setNextInterrupt  : IK (VIT N S T b) (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_setNextInterrupt)

theorem vi_switchSchedContext  : IK (VIT N S T b) (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_switchSchedContext)

theorem vi_scAndTimer  : IK (VIT N S T b) (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_scAndTimer)

theorem vi_scheduleChooseNewThread  : IK (VIT N S T false) (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_scheduleChooseNewThread)

theorem vi_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : IK (VIT N S T b) (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_scheduleSwitchThreadFastfail _ _ _ _)

theorem vi_schedule  : IK (VIT N S T false) (schedule (Z := Unit)) := by
  unfold schedule; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedule)

theorem vi_domainSetStart (index : Nat) : IK (VIT N S T b) (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_domainSetStart _)

theorem vi_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IKE (VIT N S T b) (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem vi_performDeriveSubframe (iv : Fl4SubframeInvocation) : IK (VIT N S T b) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performDeriveSubframe _)

theorem vi_performPml4Flush (a0 : Fl4Pml4Invocation) : IK (VIT N S T b) (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performPml4Flush _)

theorem vi_performTestAndClearAccessed (_slot : ObjRef) : IK (VIT N S T b) (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_performTestAndClearAccessed _)

end

end Fl4Proofs.P3.SInvI
