/- invA2: FaultTcbsS frame lemmas, part 5 (generated; see SpecInvFaultTcbsF1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsF4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem ft_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : FTKE L (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUpdateSc _ _ _)

theorem ft_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetSchedParams _ _ _ _)

theorem ft_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetSpace _ _ _ _)

theorem ft_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetTimeoutEp _ _ _)

theorem ft_decodeSetTlsBase (args : List Data) (cap : Cap) : FTKE L (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetTlsBase _ _)

theorem ft_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTcbConfigure _ _ _ _)

theorem ft_decodeUnbindNotification (cap : Cap) : FTKE L (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ft_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : FTKE L (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTcbInvocation _ _ _ _ _)

theorem ft_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FTKE L (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUntypedInvocation _ _ _ _ _)

theorem ft_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : FTKE L (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeInvocation _ _ _ _ _ _ _ _)

theorem ft_decodePml4Flush (cap : ArchCap) : FTKE L (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodePml4Flush _)

theorem ft_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : FTKE L (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_frameMappingSlot _ _ _ _)

theorem ft_decodeTestAndClearAccessed (cap : ArchCap) : FTKE L (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeTestAndClearAccessed _)

theorem ft_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FTKE L (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ft_deletedIrqHandler (irq : Irq) : FTK L (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deletedIrqHandler _)

theorem ft_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : FTK L (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_makeArchFaultMsg _ _)

theorem ft_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : FTK L (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_makeFaultMsg _ _)

theorem ft_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : FTK L (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doFaultTransfer _ _ _ _)

theorem ft_getMessageInfo (thread : ObjRef) : FTK L (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getMessageInfo _)

theorem ft_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : FTK L (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ft_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getExtraCptrs _ _)

theorem ft_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : FTKE L (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSlotForThread _ _)

theorem ft_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : FTKE L (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupCapAndSlot _ _)

theorem ft_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : FTKE L (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupExtraCaps _ _ _)

theorem ft_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : FTKE L m) : FTK L (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_emptyOnFailure _ ?_)

theorem ft_loadCapTransfer (buffer : ObjRef) : FTK L (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadCapTransfer _)

theorem ft_lookupCap (thread : ObjRef) (ref : CapRef) : FTKE L (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupCap _ _)

theorem ft_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : FTKE L m) : FTKE L (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_unifyFailure _ ?_)

theorem ft_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : FTK L (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getReceiveSlots _ _)

theorem ft_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : FTK L (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setExtraBadge _ _ _)

theorem ft_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      FTK L (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ft_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ft_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ft_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_transferCapsLoop _ _ _ _ _ _)

theorem ft_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : FTK L (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_transferCaps _ _ _ _ _)

theorem ft_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : FTK L (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doNormalTransfer _ _ _ _ _ _ _)

theorem ft_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : FTK L (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doIpcTransfer _ _ _ _ _)

theorem ft_doNbrecvFailedTransfer (thread : ObjRef) : FTK L (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_doNbrecvFailedTransfer _)

theorem ft_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : FTK L (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_domainScheduleConfigure _ _ _)

theorem ft_setNextInterrupt  : FTK L (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setNextInterrupt)

theorem ft_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : FTK L (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_ifCondRefillUnblockCheck _ _ _)

theorem ft_switchSchedContext  : FTK L (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_switchSchedContext)

theorem ft_scAndTimer  : FTK L (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scAndTimer)

theorem ft_scheduleChooseNewThread  : FTK L (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleChooseNewThread)

theorem ft_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : FTK L (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_scheduleSwitchThreadFastfail _ _ _ _)

theorem ft_schedule  : FTK L (schedule (Z := Unit)) := by
  unfold schedule; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedule)

theorem ft_domainSetStart (index : Nat) : FTK L (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_domainSetStart _)

theorem ft_postCapDeletion (cap : Cap) : FTK L (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_postCapDeletion _)

theorem ft_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : FTK L (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_emptySlot _ _)

theorem ft_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ft_performDeriveSubframe (iv : Fl4SubframeInvocation) : FTK L (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performDeriveSubframe _)

theorem ft_performPml4Flush (a0 : Fl4Pml4Invocation) : FTK L (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performPml4Flush _)

theorem ft_performTestAndClearAccessed (_slot : ObjRef) : FTK L (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_performTestAndClearAccessed _)

theorem ft_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : FTKE L (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchPerformInvocation _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ft_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    FTKE L (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ft_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : FTKE L (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ft_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : FTK L (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ReplyFromKernelError _ _ _)

theorem ft_fl4SyscallFaultIP (thread : ObjRef) : FTK L (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4SyscallFaultIP _)

theorem ft_getCapReg (reg : Register) : FTK L (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getCapReg _)

theorem ft_getIrqSlot (irq : Irq) : FTK L (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getIrqSlot _)

theorem ft_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : FTK L (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getMrs _ _ _)

theorem ft_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : FTK L (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleArchFaultReply _ _ _ _)

theorem ft_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : FTK L (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleFaultReply _ _ _ _)

theorem ft_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : FTK L (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_handleHypervisorFault _ _)
end

end Fl4Proofs.P3.SInv
