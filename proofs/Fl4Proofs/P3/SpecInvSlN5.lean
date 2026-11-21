/- sl2: NtfnScB family lemmas, part 5 (generated; see SpecInvSlN1). -/
import Fl4Proofs.P3.SpecInvSlN4
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

theorem nb_subframeNode (nodeCap : Cap) (index depth : Data) : NBKE (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_subframeNode _ _ _)

theorem nb_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NBKE (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDeriveSubframe _ _ _ _)

theorem nb_decodeDomainScheduleConfigure (args : List Data) : NBKE (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainScheduleConfigure _)

theorem nb_decodeDomainScheduleSetStart (args : List Data) : NBKE (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainScheduleSetStart _)

theorem nb_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NBKE (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainSet _ _)

theorem nb_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NBKE (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeDomainInvocation _ _ _)

theorem nb_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NBK (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4GetMr _ _ _)

theorem nb_fl4Arg (buf : Option ObjRef) (i : Nat) : NBKE (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4Arg _ _)

theorem nb_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4ConfigureSingleStepping _ _)

theorem nb_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NBKE (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4FpuTransfer _ _ _ _)

theorem nb_fl4CheckBpNum (bp : Data) : NBKE (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4CheckBpNum _)

theorem nb_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4GetBreakpoint _ _)

theorem nb_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NBKE (check x0)) : NBKE (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; nb_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible refine nb_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem nb_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqControlRemapped _ _ _)

theorem nb_fl4ArchCheckIrq (irq : Data) : NBKE (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_fl4ArchCheckIrq _)

theorem nb_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4IrqControl _ _ _ _ _)

theorem nb_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetBreakpoint _ _)

theorem nb_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NBKE (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetFlags _ _)

theorem nb_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NBKE (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4SetTimer _ _)

theorem nb_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NBKE (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4UnsetBreakpoint _ _)

theorem nb_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NBKE (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeFl4TcbExt _ _ _ _ _)

theorem nb_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NBKE (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqControlInvocation _ _ _ _)

theorem nb_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NBKE (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeIrqHandlerInvocation _ _ _)

theorem nb_getScReleased (scPtr : ObjRef) : NBK (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getScReleased _)

theorem nb_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextBind _ _)

theorem nb_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextUnbindObject _ _)

theorem nb_decodeSchedContextYieldTo (scPtr : ObjRef) : NBKE (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextYieldTo _)

theorem nb_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NBKE (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedContextInvocation _ _ _)

theorem nb_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NBKE (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSchedControlInvocationFlags _ _ _)

theorem nb_rangeCheck (v minV maxV : Word) : NBKE (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_rangeCheck _ _ _)

theorem nb_decodeSetFlags (args : List Data) (cap : Cap) : NBKE (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetFlags _ _)

theorem nb_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NBKE (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetIpcBuffer _ _ _ _)

theorem nb_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetMcpriority _ _ _ _)

theorem nb_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetPriority _ _ _ _)

theorem nb_isBlocked (thread : ObjRef) : NBK (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_isBlocked _)

theorem nb_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NBKE (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUpdateSc _ _ _)

theorem nb_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetSchedParams _ _ _ _)

theorem nb_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NBKE (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetSpace _ _ _ _)

theorem nb_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetTimeoutEp _ _ _)

theorem nb_decodeSetTlsBase (args : List Data) (cap : Cap) : NBKE (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeSetTlsBase _ _)

theorem nb_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NBKE (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTcbConfigure _ _ _ _)

theorem nb_decodeUnbindNotification (cap : Cap) : NBKE (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem nb_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NBKE (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTcbInvocation _ _ _ _ _)

theorem nb_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NBKE (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUntypedInvocation _ _ _ _ _)

theorem nb_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NBKE (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeInvocation _ _ _ _ _ _ _ _)

theorem nb_decodePml4Flush (cap : ArchCap) : NBKE (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodePml4Flush _)

theorem nb_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NBKE (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_frameMappingSlot _ _ _ _)

theorem nb_decodeTestAndClearAccessed (cap : ArchCap) : NBKE (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeTestAndClearAccessed _)

theorem nb_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NBKE (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem nb_doNbrecvFailedTransfer (thread : ObjRef) : NBK (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doNbrecvFailedTransfer _)

theorem nb_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NBK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_getMrs _ _ _)

theorem nb_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NBK (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleArchFaultReply _ _ _ _)

theorem nb_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NBK (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_handleFaultReply _ _ _ _)

theorem nb_schedContextResume (scPtr : ObjRef) : NBK (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_schedContextResume _)

theorem nb_testPossibleSwitchTo (tcbPtr : ObjRef) : NBK (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_testPossibleSwitchTo _)

theorem nb_restart (thread : ObjRef) : NBK (restart (Z := Unit) thread) := by
  unfold restart; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_restart _)

theorem nb_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : NBK (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_doReplyTransfer _ _ _)

theorem nb_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NBK (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_domainScheduleConfigure _ _ _)

theorem nb_setNextInterrupt  : NBK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_setNextInterrupt)

theorem nb_switchSchedContext  : NBK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_switchSchedContext)

theorem nb_scAndTimer  : NBK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scAndTimer)

theorem nb_scheduleChooseNewThread  : NBK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleChooseNewThread)

theorem nb_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NBK (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; nb_auto
macro_rules | `(tactic| nb_leaf) => `(tactic| with_reducible exact nb_scheduleSwitchThreadFastfail _ _ _ _)
end

end Fl4Proofs.P3.SInvL
