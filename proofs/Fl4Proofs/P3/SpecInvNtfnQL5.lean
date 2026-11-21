/- il1: IfLiveT family lemmas, part 5 (generated; see SpecInvNtfnQL1). -/
import Fl4Proofs.P3.SpecInvNtfnQL4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem il_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : ILKE Kq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_frameMappingSlot _ _ _ _)

theorem il_decodeTestAndClearAccessed (cap : ArchCap) : ILKE Kq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeTestAndClearAccessed _)

theorem il_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : ILKE Kq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem il_deletedIrqHandler (irq : Irq) : ILK Kq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_deletedIrqHandler _)

theorem il_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : ILK Kq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_makeArchFaultMsg _ _)

theorem il_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : ILK Kq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_makeFaultMsg _ _)

theorem il_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : ILK Kq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doFaultTransfer _ _ _ _)

theorem il_getMessageInfo (thread : ObjRef) : ILK Kq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getMessageInfo _)

theorem il_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : ILK Kq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; il_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getExtraCptrs _ _)

theorem il_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : ILKE Kq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupSlotForThread _ _)

theorem il_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : ILKE Kq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupCapAndSlot _ _)

theorem il_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : ILKE Kq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupExtraCaps _ _ _)

theorem il_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : ILKE Kq m) : ILK Kq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_emptyOnFailure _ ?_)

theorem il_loadCapTransfer (buffer : ObjRef) : ILK Kq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_loadCapTransfer _)

theorem il_lookupCap (thread : ObjRef) (ref : CapRef) : ILKE Kq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupCap _ _)

theorem il_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : ILKE Kq m) : ILKE Kq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_unifyFailure _ ?_)

theorem il_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : ILK Kq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getReceiveSlots _ _)

theorem il_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : ILK Kq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setExtraBadge _ _ _)

theorem il_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      ILK Kq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; il_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => il_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | il_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_transferCapsLoop _ _ _ _ _ _)

theorem il_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : ILK Kq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_transferCaps _ _ _ _ _)

theorem il_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : ILK Kq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doNormalTransfer _ _ _ _ _ _ _)

theorem il_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : ILK Kq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doIpcTransfer _ _ _ _ _)

theorem il_doNbrecvFailedTransfer (thread : ObjRef) : ILK Kq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_doNbrecvFailedTransfer _)

theorem il_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : ILK Kq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_domainScheduleConfigure _ _ _)

theorem il_setNextInterrupt  : ILK Kq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setNextInterrupt)

theorem il_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : ILK Kq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_ifCondRefillUnblockCheck _ _ _)

theorem il_switchSchedContext  : ILK Kq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_switchSchedContext)

theorem il_scAndTimer  : ILK Kq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_scAndTimer)

theorem il_scheduleChooseNewThread  : ILK Kq (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_scheduleChooseNewThread)

theorem il_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : ILK Kq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_scheduleSwitchThreadFastfail _ _ _ _)

theorem il_schedule  : ILK Kq (schedule (Z := Unit)) := by
  unfold schedule; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedule)

theorem il_domainSetStart (index : Nat) : ILK Kq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_domainSetStart _)

theorem il_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem il_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    ILKE Kq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem il_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : ILKE Kq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem il_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : ILK Kq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4ReplyFromKernelError _ _ _)

theorem il_fl4SyscallFaultIP (thread : ObjRef) : ILK Kq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4SyscallFaultIP _)

theorem il_getCapReg (reg : Register) : ILK Kq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getCapReg _)

theorem il_getIrqSlot (irq : Irq) : ILK Kq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getIrqSlot _)

theorem il_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : ILK Kq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getMrs _ _ _)

theorem il_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : ILK Kq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleArchFaultReply _ _ _ _)

theorem il_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : ILK Kq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleFaultReply _ _ _ _)

theorem il_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : ILK Kq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleHypervisorFault _ _)

theorem il_handleNoFault (tptr : ObjRef) : ILK Kq (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleNoFault _)

theorem il_handleReservedIrq (_irq : Irq) : ILK Kq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleReservedIrq _)

theorem il_handleSpuriousIrq  : ILK Kq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleSpuriousIrq)

theorem il_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : ILKE Kq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_handleVmFault _ _)

theorem il_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : ILK Kq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_initArchObjects _ _ _ _ _ _)

theorem il_threadSetDomain (tptr : ObjRef) (domain : Domain) : ILK Kq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_threadSetDomain _ _)

theorem il_setDomain (tptr : ObjRef) (newDom : Domain) : ILK Kq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_setDomain _ _)

theorem il_invokeSetDomain (thread : ObjRef) (domain : Domain) : ILK Kq (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeSetDomain _ _)

theorem il_invokeDomain (domInv : DomainInvocation) : ILK Kq (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeDomain _)

theorem il_invokeIrqControl (a0 : IrqControlInvocation) : ILKE Kq (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeIrqControl _)

theorem il_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : ILKE Kq (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeFl4IrqControl _)

theorem il_invokeFl4Tcb (a0 : Fl4TcbInvocation) : ILKE Kq (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_invokeFl4Tcb _)

theorem il_returnConsumed (scPtr : ObjRef) : ILK Kq (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_returnConsumed _)

theorem il_schedContextBindNtfn (sc ntfn : ObjRef) : ILK Kq (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextBindNtfn _ _)

theorem il_schedContextBindTcb (scPtr tcbPtr : ObjRef) : ILK Kq (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_schedContextBindTcb _ _)
end

end Fl4Proofs.P3.SInv
