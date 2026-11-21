/- invA: NativeScope frame lemmas, part 5 (generated; see SpecInvNativeScopeF1). -/
import Fl4Proofs.P3.SpecInvNativeScopeF4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem ns_subframeNode (nodeCap : Cap) (index depth : Data) : NSKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_subframeNode _ _ _)

theorem ns_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NSKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDeriveSubframe _ _ _ _)

theorem ns_decodeDomainScheduleConfigure (args : List Data) : NSKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainScheduleConfigure _)

theorem ns_decodeDomainScheduleSetStart (args : List Data) : NSKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainScheduleSetStart _)

theorem ns_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NSKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainSet _ _)

theorem ns_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NSKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeDomainInvocation _ _ _)

theorem ns_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NSK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4GetMr _ _ _)

theorem ns_fl4Arg (buf : Option ObjRef) (i : Nat) : NSKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4Arg _ _)

theorem ns_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4ConfigureSingleStepping _ _)

theorem ns_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NSKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4FpuTransfer _ _ _ _)

theorem ns_fl4CheckBpNum (bp : Data) : NSKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4CheckBpNum _)

theorem ns_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4GetBreakpoint _ _)

theorem ns_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NSKE (check x0)) : NSKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ns_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible refine ns_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ns_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqControlRemapped _ _ _)

theorem ns_fl4ArchCheckIrq (irq : Data) : NSKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchCheckIrq _)

theorem ns_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4IrqControl _ _ _ _ _)

theorem ns_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetBreakpoint _ _)

theorem ns_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NSKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetFlags _ _)

theorem ns_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NSKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4SetTimer _ _)

theorem ns_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NSKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4UnsetBreakpoint _ _)

theorem ns_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NSKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeFl4TcbExt _ _ _ _ _)

theorem ns_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NSKE (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqControlInvocation _ _ _ _)

theorem ns_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NSKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeIrqHandlerInvocation _ _ _)

theorem ns_getScReleased (scPtr : ObjRef) : NSK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getScReleased _)

theorem ns_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextBind _ _)

theorem ns_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextUnbindObject _ _)

theorem ns_decodeSchedContextYieldTo (scPtr : ObjRef) : NSKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextYieldTo _)

theorem ns_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NSKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedContextInvocation _ _ _)

theorem ns_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NSKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSchedControlInvocationFlags _ _ _)

theorem ns_rangeCheck (v minV maxV : Word) : NSKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_rangeCheck _ _ _)

theorem ns_decodeSetFlags (args : List Data) (cap : Cap) : NSKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetFlags _ _)

theorem ns_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NSKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetIpcBuffer _ _ _ _)

theorem ns_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetMcpriority _ _ _ _)

theorem ns_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetPriority _ _ _ _)

theorem ns_isBlocked (thread : ObjRef) : NSK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_isBlocked _)

theorem ns_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NSKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUpdateSc _ _ _)

theorem ns_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetSchedParams _ _ _ _)

theorem ns_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NSKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetSpace _ _ _ _)

theorem ns_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetTimeoutEp _ _ _)

theorem ns_decodeSetTlsBase (args : List Data) (cap : Cap) : NSKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeSetTlsBase _ _)

theorem ns_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NSKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTcbConfigure _ _ _ _)

theorem ns_decodeUnbindNotification (cap : Cap) : NSKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ns_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NSKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTcbInvocation _ _ _ _ _)

theorem ns_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NSKE (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUntypedInvocation _ _ _ _ _)

theorem ns_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NSKE (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeInvocation _ _ _ _ _ _ _ _)

theorem ns_decodePml4Flush (cap : ArchCap) : NSKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodePml4Flush _)

theorem ns_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NSKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_frameMappingSlot _ _ _ _)

theorem ns_decodeTestAndClearAccessed (cap : ArchCap) : NSKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeTestAndClearAccessed _)

theorem ns_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NSKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ns_doNbrecvFailedTransfer (thread : ObjRef) : NSK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doNbrecvFailedTransfer _)

theorem ns_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NSK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_getMrs _ _ _)

theorem ns_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NSK (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleArchFaultReply _ _ _ _)

theorem ns_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NSK (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_handleFaultReply _ _ _ _)

theorem ns_testPossibleSwitchTo (tcbPtr : ObjRef) : NSK (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_testPossibleSwitchTo _)

theorem ns_restart (thread : ObjRef) : NSK (restart (Z := Unit) thread) := by
  unfold restart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_restart _)

theorem ns_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : NSK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_doReplyTransfer _ _ _)

theorem ns_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NSK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_domainScheduleConfigure _ _ _)

theorem ns_setNextInterrupt  : NSK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_setNextInterrupt)

theorem ns_switchSchedContext  : NSK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_switchSchedContext)

theorem ns_scAndTimer  : NSK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scAndTimer)

theorem ns_scheduleChooseNewThread  : NSK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleChooseNewThread)

theorem ns_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NSK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_scheduleSwitchThreadFastfail _ _ _ _)

theorem ns_schedule  : NSK (schedule (Z := Unit)) := by
  unfold schedule; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_schedule)

theorem ns_domainSetStart (index : Nat) : NSK (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_domainSetStart _)

theorem ns_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NSKE (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ns_performDeriveSubframe (iv : Fl4SubframeInvocation) : NSK (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performDeriveSubframe _)

theorem ns_performPml4Flush (a0 : Fl4Pml4Invocation) : NSK (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performPml4Flush _)

theorem ns_performTestAndClearAccessed (_slot : ObjRef) : NSK (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_performTestAndClearAccessed _)

theorem ns_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : NSKE (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; ns_auto
macro_rules | `(tactic| ns_leaf) => `(tactic| with_reducible exact ns_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInv
