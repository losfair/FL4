/- ut7: IRQ-node frame lemmas `NK N`, part 5 (invA's NativeScope scripts renamed; see SpecInvUtNK1). -/
import Fl4Proofs.P3.SpecInvUtNK4
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef}

theorem nk_subframeNode (nodeCap : Cap) (index depth : Data) : NKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_subframeNode _ _ _)

theorem nk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeDeriveSubframe _ _ _ _)

theorem nk_decodeDomainScheduleConfigure (args : List Data) : NKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeDomainScheduleConfigure _)

theorem nk_decodeDomainScheduleSetStart (args : List Data) : NKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeDomainScheduleSetStart _)

theorem nk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeDomainSet _ _)

theorem nk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeDomainInvocation _ _ _)

theorem nk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4GetMr _ _ _)

theorem nk_fl4Arg (buf : Option ObjRef) (i : Nat) : NKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4Arg _ _)

theorem nk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4ConfigureSingleStepping _ _)

theorem nk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4FpuTransfer _ _ _ _)

theorem nk_fl4CheckBpNum (bp : Data) : NKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4CheckBpNum _)

theorem nk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4GetBreakpoint _ _)

theorem nk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NKE N (check x0)) : NKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; nk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible refine nk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem nk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeIrqControlRemapped _ _ _)

theorem nk_fl4ArchCheckIrq (irq : Data) : NKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4ArchCheckIrq _)

theorem nk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4IrqControl _ _ _ _ _)

theorem nk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4SetBreakpoint _ _)

theorem nk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4SetFlags _ _)

theorem nk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4SetTimer _ _)

theorem nk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4UnsetBreakpoint _ _)

theorem nk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeFl4TcbExt _ _ _ _ _)

theorem nk_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeIrqControlInvocation _ _ _ _)

theorem nk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeIrqHandlerInvocation _ _ _)

theorem nk_getScReleased (scPtr : ObjRef) : NK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getScReleased _)

theorem nk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSchedContextBind _ _)

theorem nk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSchedContextUnbindObject _ _)

theorem nk_decodeSchedContextYieldTo (scPtr : ObjRef) : NKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSchedContextYieldTo _)

theorem nk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSchedContextInvocation _ _ _)

theorem nk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSchedControlInvocationFlags _ _ _)

theorem nk_rangeCheck (v minV maxV : Word) : NKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_rangeCheck _ _ _)

theorem nk_decodeSetFlags (args : List Data) (cap : Cap) : NKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetFlags _ _)

theorem nk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetIpcBuffer _ _ _ _)

theorem nk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetMcpriority _ _ _ _)

theorem nk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetPriority _ _ _ _)

theorem nk_isBlocked (thread : ObjRef) : NK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_isBlocked _)

theorem nk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeUpdateSc _ _ _)

theorem nk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetSchedParams _ _ _ _)

theorem nk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetSpace _ _ _ _)

theorem nk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetTimeoutEp _ _ _)

theorem nk_decodeSetTlsBase (args : List Data) (cap : Cap) : NKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeSetTlsBase _ _)

theorem nk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeTcbConfigure _ _ _ _)

theorem nk_decodeUnbindNotification (cap : Cap) : NKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem nk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeTcbInvocation _ _ _ _ _)

theorem nk_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeUntypedInvocation _ _ _ _ _)

theorem nk_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeInvocation _ _ _ _ _ _ _ _)

theorem nk_decodePml4Flush (cap : ArchCap) : NKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodePml4Flush _)

theorem nk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_frameMappingSlot _ _ _ _)

theorem nk_decodeTestAndClearAccessed (cap : ArchCap) : NKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeTestAndClearAccessed _)

theorem nk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem nk_doNbrecvFailedTransfer (thread : ObjRef) : NK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_doNbrecvFailedTransfer _)

theorem nk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_getMrs _ _ _)

theorem nk_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleArchFaultReply _ _ _ _)

theorem nk_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_handleFaultReply _ _ _ _)

theorem nk_testPossibleSwitchTo (tcbPtr : ObjRef) : NK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_testPossibleSwitchTo _)

theorem nk_restart (thread : ObjRef) : NK N (restart (Z := Unit) thread) := by
  unfold restart; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_restart _)

theorem nk_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : NK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_doReplyTransfer _ _ _)

theorem nk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_domainScheduleConfigure _ _ _)

theorem nk_setNextInterrupt  : NK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_setNextInterrupt)

theorem nk_switchSchedContext  : NK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_switchSchedContext)

theorem nk_scAndTimer  : NK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_scAndTimer)

theorem nk_scheduleChooseNewThread  : NK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_scheduleChooseNewThread)

theorem nk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_scheduleSwitchThreadFastfail _ _ _ _)

theorem nk_schedule  : NK N (schedule (Z := Unit)) := by
  unfold schedule; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_schedule)

theorem nk_domainSetStart (index : Nat) : NK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_domainSetStart _)

theorem nk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem nk_performDeriveSubframe (iv : Fl4SubframeInvocation) : NK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performDeriveSubframe _)

theorem nk_performPml4Flush (a0 : Fl4Pml4Invocation) : NK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performPml4Flush _)

theorem nk_performTestAndClearAccessed (_slot : ObjRef) : NK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_performTestAndClearAccessed _)

theorem nk_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : NKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; nk_auto
macro_rules | `(tactic| nk_leaf) => `(tactic| with_reducible exact nk_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvU
