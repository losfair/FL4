/- sl1: ScLive family lemmas, part 5 (generated; see SpecInvSlF1). -/
import Fl4Proofs.P3.SpecInvSlF4
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Iq : ObjRef × ObjRef} {Kq : List ObjRef}

theorem sl_decodePml4Flush (cap : ArchCap) : SLKE Iq Kq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodePml4Flush _)

theorem sl_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : SLKE Iq Kq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_frameMappingSlot _ _ _ _)

theorem sl_decodeTestAndClearAccessed (cap : ArchCap) : SLKE Iq Kq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTestAndClearAccessed _)

theorem sl_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem sl_deletedIrqHandler (irq : Irq) : SLK Iq Kq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deletedIrqHandler _)

theorem sl_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : SLK Iq Kq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_makeArchFaultMsg _ _)

theorem sl_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : SLK Iq Kq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_makeFaultMsg _ _)

theorem sl_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : SLK Iq Kq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doFaultTransfer _ _ _ _)

theorem sl_getMessageInfo (thread : ObjRef) : SLK Iq Kq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getMessageInfo _)

theorem sl_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : SLK Iq Kq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; sl_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getExtraCptrs _ _)

theorem sl_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : SLKE Iq Kq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupSlotForThread _ _)

theorem sl_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : SLKE Iq Kq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupCapAndSlot _ _)

theorem sl_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SLKE Iq Kq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupExtraCaps _ _ _)

theorem sl_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : SLKE Iq Kq m) : SLK Iq Kq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_emptyOnFailure _ ?_)

theorem sl_loadCapTransfer (buffer : ObjRef) : SLK Iq Kq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadCapTransfer _)

theorem sl_lookupCap (thread : ObjRef) (ref : CapRef) : SLKE Iq Kq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupCap _ _)

theorem sl_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : SLKE Iq Kq m) : SLKE Iq Kq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; sl_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_unifyFailure _ ?_)

theorem sl_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : SLK Iq Kq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getReceiveSlots _ _)

theorem sl_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : SLK Iq Kq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setExtraBadge _ _ _)

theorem sl_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      SLK Iq Kq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; sl_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => sl_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | sl_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_transferCapsLoop _ _ _ _ _ _)

theorem sl_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : SLK Iq Kq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_transferCaps _ _ _ _ _)

theorem sl_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SLK Iq Kq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doNormalTransfer _ _ _ _ _ _ _)

theorem sl_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : SLK Iq Kq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doIpcTransfer _ _ _ _ _)

theorem sl_doNbrecvFailedTransfer (thread : ObjRef) : SLK Iq Kq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_doNbrecvFailedTransfer _)

theorem sl_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : SLK Iq Kq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_domainScheduleConfigure _ _ _)

theorem sl_setNextInterrupt  : SLK Iq Kq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setNextInterrupt)

theorem sl_switchSchedContext  : SLK Iq Kq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_switchSchedContext)

theorem sl_scAndTimer  : SLK Iq Kq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scAndTimer)

theorem sl_scheduleChooseNewThread  : SLK Iq Kq (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleChooseNewThread)

theorem sl_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : SLK Iq Kq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_scheduleSwitchThreadFastfail _ _ _ _)

theorem sl_schedule  : SLK Iq Kq (schedule (Z := Unit)) := by
  unfold schedule; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_schedule)

theorem sl_domainSetStart (index : Nat) : SLK Iq Kq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_domainSetStart _)

theorem sl_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem sl_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SLKE Iq Kq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem sl_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : SLKE Iq Kq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem sl_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : SLK Iq Kq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ReplyFromKernelError _ _ _)

theorem sl_fl4SyscallFaultIP (thread : ObjRef) : SLK Iq Kq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4SyscallFaultIP _)

theorem sl_getCapReg (reg : Register) : SLK Iq Kq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getCapReg _)

theorem sl_getIrqSlot (irq : Irq) : SLK Iq Kq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getIrqSlot _)

theorem sl_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SLK Iq Kq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getMrs _ _ _)

theorem sl_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : SLK Iq Kq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleArchFaultReply _ _ _ _)

theorem sl_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : SLK Iq Kq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleFaultReply _ _ _ _)

theorem sl_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : SLK Iq Kq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleHypervisorFault _ _)

theorem sl_handleNoFault (tptr : ObjRef) : SLK Iq Kq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleNoFault _)

theorem sl_handleReservedIrq (_irq : Irq) : SLK Iq Kq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleReservedIrq _)

theorem sl_handleSpuriousIrq  : SLK Iq Kq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleSpuriousIrq)

theorem sl_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : SLKE Iq Kq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_handleVmFault _ _)

theorem sl_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : SLK Iq Kq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_initArchObjects _ _ _ _ _ _)

theorem sl_threadSetDomain (tptr : ObjRef) (domain : Domain) : SLK Iq Kq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_threadSetDomain _ _)

theorem sl_setDomain (tptr : ObjRef) (newDom : Domain) : SLK Iq Kq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_setDomain _ _)

theorem sl_invokeSetDomain (thread : ObjRef) (domain : Domain) : SLK Iq Kq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeSetDomain _ _)

theorem sl_invokeDomain (domInv : DomainInvocation) : SLK Iq Kq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeDomain _)

theorem sl_invokeIrqControl (a0 : IrqControlInvocation) : SLKE Iq Kq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeIrqControl _)

theorem sl_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : SLKE Iq Kq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeFl4IrqControl _)

theorem sl_invokeFl4Tcb (a0 : Fl4TcbInvocation) : SLKE Iq Kq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_invokeFl4Tcb _)

theorem sl_maybeAddEmptyTail (scPtr : ObjRef) : SLK Iq Kq (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_maybeAddEmptyTail _)

theorem sl_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : SLK Iq Kq (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_refillNew _ _ _ _)
end

end Fl4Proofs.P3.SInvL
