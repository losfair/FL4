/- nq1: the current-thread frame `CTK c` (the current thread stays `c`) for every spec function reachable from the syscall entry except the scheduler, part 4 (generated: proofs/scratch/nq1/mkck.sh). -/
import Fl4Proofs.P3.SpecInvNtfnQC3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {cq : ObjRef}

theorem ct_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetPriority _ _ _ _)

theorem ct_isBlocked (thread : ObjRef) : CTK cq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isBlocked _)

theorem ct_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : CTKE cq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeUpdateSc _ _ _)

theorem ct_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetSchedParams _ _ _ _)

theorem ct_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : CTKE cq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetSpace _ _ _ _)

theorem ct_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetTimeoutEp _ _ _)

theorem ct_decodeSetTlsBase (args : List Data) (cap : Cap) : CTKE cq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetTlsBase _ _)

theorem ct_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeTcbConfigure _ _ _ _)

theorem ct_decodeUnbindNotification (cap : Cap) : CTKE cq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ct_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : CTKE cq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeTcbInvocation _ _ _ _ _)

theorem ct_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : CTKE cq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeUntypedInvocation _ _ _ _ _)

theorem ct_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : CTKE cq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeInvocation _ _ _ _ _ _ _ _)

theorem ct_decodePml4Flush (cap : ArchCap) : CTKE cq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodePml4Flush _)

theorem ct_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : CTKE cq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_frameMappingSlot _ _ _ _)

theorem ct_decodeTestAndClearAccessed (cap : ArchCap) : CTKE cq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeTestAndClearAccessed _)

theorem ct_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : CTKE cq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ct_doNbrecvFailedTransfer (thread : ObjRef) : CTK cq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doNbrecvFailedTransfer _)

theorem ct_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : CTK cq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getMrs _ _ _)

theorem ct_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : CTK cq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleArchFaultReply _ _ _ _)

theorem ct_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : CTK cq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleFaultReply _ _ _ _)

theorem ct_testPossibleSwitchTo (tcbPtr : ObjRef) : CTK cq (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_testPossibleSwitchTo _)

theorem ct_restart (thread : ObjRef) : CTK cq (restart (Z := Unit) thread) := by
  unfold restart; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_restart _)

theorem ct_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : CTK cq (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doReplyTransfer _ _ _)

theorem ct_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : CTK cq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_domainScheduleConfigure _ _ _)

theorem ct_setNextInterrupt  : CTK cq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setNextInterrupt)

theorem ct_switchSchedContext  : CTK cq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_switchSchedContext)

theorem ct_scAndTimer  : CTK cq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_scAndTimer)

theorem ct_nextDomain  : CTK cq (nextDomain (Z := Unit)) := by
  unfold nextDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_nextDomain)

theorem ct_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : CTK cq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_scheduleSwitchThreadFastfail _ _ _ _)

theorem ct_domainSetStart (index : Nat) : CTK cq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_domainSetStart _)

theorem ct_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ct_performDeriveSubframe (iv : Fl4SubframeInvocation) : CTK cq (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performDeriveSubframe _)

theorem ct_performPml4Flush (a0 : Fl4Pml4Invocation) : CTK cq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performPml4Flush _)

theorem ct_performTestAndClearAccessed (_slot : ObjRef) : CTK cq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performTestAndClearAccessed _)

theorem ct_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : CTKE cq (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4ArchPerformInvocation _)

theorem ct_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : CTK cq (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateWaitingNtfn _ _ _)

theorem ct_sendSignal (ntfnptr : ObjRef) (badge : Badge) : CTK cq (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_sendSignal _ _)

theorem ct_fl4Awaken : CTK cq (fl4Awaken (Z := Unit)) := by
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
    · exact ct_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ct_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    CTKE cq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ct_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : CTKE cq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ct_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : CTK cq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_initArchObjects _ _ _ _ _ _)

theorem ct_resetUntypedCap (srcSlot : CslotPtr) : CTKE cq (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_resetUntypedCap _)

theorem ct_retypeRegionWith (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : CTK cq (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_retypeRegionWith _ _ _ _ _ _)

theorem ct_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : CTKE cq (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeUntypedWith _ _)

theorem ct_invokeCnode (i : CnodeInvocation) : CTKE cq (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeCnode _)

theorem ct_threadSetDomain (tptr : ObjRef) (domain : Domain) : CTK cq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_threadSetDomain _ _)

theorem ct_setDomain (tptr : ObjRef) (newDom : Domain) : CTK cq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setDomain _ _)

theorem ct_invokeSetDomain (thread : ObjRef) (domain : Domain) : CTK cq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeSetDomain _ _)

theorem ct_invokeDomain (domInv : DomainInvocation) : CTK cq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeDomain _)

theorem ct_invokeIrqControl (a0 : IrqControlInvocation) : CTKE cq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeIrqControl _)

theorem ct_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : CTKE cq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeFl4IrqControl _)

theorem ct_invokeFl4Tcb (a0 : Fl4TcbInvocation) : CTKE cq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeFl4Tcb _)

theorem ct_invokeIrqHandler (a0 : IrqHandlerInvocation) : CTK cq (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeIrqHandler _)

theorem ct_returnConsumed (scPtr : ObjRef) : CTK cq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_returnConsumed _)

theorem ct_schedContextBindNtfn (sc ntfn : ObjRef) : CTK cq (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextBindNtfn _ _)

theorem ct_schedContextBindTcb (scPtr tcbPtr : ObjRef) : CTK cq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextBindTcb _ _)

theorem ct_schedContextYieldTo (scPtr : ObjRef) : CTK cq (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextYieldTo _)

theorem ct_invokeSchedContext (iv : SchedContextInvocation) : CTK cq (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeSchedContext _)

theorem ct_maybeAddEmptyTail (scPtr : ObjRef) : CTK cq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_maybeAddEmptyTail _)

theorem ct_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : CTK cq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillNew _ _ _ _)

theorem ct_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : CTK cq (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillUpdate _ _ _ _)

theorem ct_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : CTK cq (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeSchedControlConfigureFlags _)

theorem ct_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : CTKE cq (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_installTcbCap _ _ _ _)

theorem ct_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : CTKE cq (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_installTcbFrameCap _ _ _)

theorem ct_setFlags (ref : ObjRef) (flags : TcbFlags) : CTK cq (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setFlags _ _)

theorem ct_setMcpriority (ref : ObjRef) (mcp : Priority) : CTK cq (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setMcpriority _ _)

theorem ct_reorderEp (epPtr tptr : ObjRef) : CTK cq (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_reorderEp _ _)

theorem ct_reorderNtfn (ntfnPtr tptr : ObjRef) : CTK cq (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_reorderNtfn _ _)

theorem ct_threadSetPriority (tptr : ObjRef) (prio : Priority) : CTK cq (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_threadSetPriority _ _)

theorem ct_setPriority (tptr : ObjRef) (prio : Priority) : CTK cq (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setPriority _ _)

theorem ct_invokeTcb (a0 : TcbInvocation) : CTKE cq (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeTcb _)

theorem ct_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : CTKE cq (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4PerformInvocation _ _ _ _)

theorem ct_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : CTK cq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4ReplyFromKernelError _ _ _)

theorem ct_handleNoFault (tptr : ObjRef) : CTK cq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleNoFault _)

theorem ct_handleFault (thread : ObjRef) (ex : Fault) : CTK cq (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleFault _ _)

theorem ct_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : CTKE cq mFault) (h_hFault : ∀ x0, CTK cq (hFault x0)) (h_mError : ∀ x0, CTKE cq (mError x0)) (h_hError : ∀ x0, CTK cq (hError x0)) (h_mFinalise : ∀ x0, CTKE cq (mFinalise x0)) : CTKE cq (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ct_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ct_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : CTKE cq (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4HandleInvocationR _ _ _ _ _ _)

theorem ct_getCapReg (reg : Register) : CTK cq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getCapReg _)

theorem ct_lookupReply  : CTKE cq (lookupReply (Z := Unit)) := by
  unfold lookupReply; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupReply)

theorem ct_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : CTK cq (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_maybeReturnSc _ _)

theorem ct_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : CTK cq (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem ct_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    CTK cq (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_receiveIpc _ _ _ _)

theorem ct_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : CTK cq (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbNtfnAppend _ _)

theorem ct_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : CTK cq (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_receiveSignalBlocked _ _ _)

theorem ct_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : CTK cq (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_receiveSignal _ _ _)

theorem ct_handleRecv (isBlocking canReply : Bool) : CTK cq (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleRecv _ _)

theorem ct_handleYield  : CTK cq (handleYield (Z := Unit)) := by
  unfold handleYield; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleYield)

theorem ct_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : CTKE cq (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4HandleSyscall _ _)

theorem ct_invokeUntyped (ui : UntypedInvocation) : CTKE cq (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_invokeUntyped _)

theorem ct_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : CTKE cq (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_performInvocation _ _ _ _)

theorem ct_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : CTKE cq (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleInvocation _ _ _ _ _)

theorem ct_handleCall  : CTKE cq (handleCall (Z := Unit)) := by
  unfold handleCall; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleCall)

theorem ct_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : CTK cq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleHypervisorFault _ _)

theorem ct_handleSend (bl : Bool) : CTKE cq (handleSend (Z := Unit) bl) := by
  unfold handleSend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleSend _)

theorem ct_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : CTKE cq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleVmFault _ _)

theorem ct_handleReservedIrq (_irq : Irq) : CTK cq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleReservedIrq _)

theorem ct_handleInterrupt (irq : Irq) : CTK cq (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleInterrupt _)

theorem ct_handleSpuriousIrq  : CTK cq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleSpuriousIrq)

theorem ct_maybeHandleInterrupt (inKernel : Bool) : CTK cq (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_maybeHandleInterrupt _)

theorem ct_handleEvent (a0 : Event) : CTKE cq (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleEvent _)

theorem ct_fl4HandleEvent (rep : Bool) (a0 : Event) : CTKE cq (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4HandleEvent _ _)

theorem ct_fl4SyscallFaultIP (thread : ObjRef) : CTK cq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4SyscallFaultIP _)

theorem ct_preemptionPath  : CTK cq (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_preemptionPath)

end

end Fl4Proofs.P3.SInv
