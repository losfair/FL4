/- nq1: NtfnQB family lemmas, part 5 (generated; see SpecInvNtfnQF1). -/
import Fl4Proofs.P3.SpecInvNtfnQF4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeTcbConfigure _ _ _ _)

theorem nq_decodeUnbindNotification (cap : Cap) : NQKE Kq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem nq_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : NQKE Kq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeTcbInvocation _ _ _ _ _)

theorem nq_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NQKE Kq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeUntypedInvocation _ _ _ _ _)

theorem nq_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : NQKE Kq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeInvocation _ _ _ _ _ _ _ _)

theorem nq_decodePml4Flush (cap : ArchCap) : NQKE Kq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodePml4Flush _)

theorem nq_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : NQKE Kq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_frameMappingSlot _ _ _ _)

theorem nq_decodeTestAndClearAccessed (cap : ArchCap) : NQKE Kq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeTestAndClearAccessed _)

theorem nq_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : NQKE Kq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem nq_deletedIrqHandler (irq : Irq) : NQK Kq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_deletedIrqHandler _)

theorem nq_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : NQK Kq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_makeArchFaultMsg _ _)

theorem nq_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : NQK Kq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_makeFaultMsg _ _)

theorem nq_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : NQK Kq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doFaultTransfer _ _ _ _)

theorem nq_getMessageInfo (thread : ObjRef) : NQK Kq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getMessageInfo _)

theorem nq_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : NQK Kq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; nq_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getExtraCptrs _ _)

theorem nq_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : NQKE Kq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupSlotForThread _ _)

theorem nq_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : NQKE Kq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupCapAndSlot _ _)

theorem nq_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : NQKE Kq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupExtraCaps _ _ _)

theorem nq_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : NQKE Kq m) : NQK Kq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_emptyOnFailure _ ?_)

theorem nq_loadCapTransfer (buffer : ObjRef) : NQK Kq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_loadCapTransfer _)

theorem nq_lookupCap (thread : ObjRef) (ref : CapRef) : NQKE Kq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupCap _ _)

theorem nq_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : NQKE Kq m) : NQKE Kq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_unifyFailure _ ?_)

theorem nq_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : NQK Kq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getReceiveSlots _ _)

theorem nq_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : NQK Kq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setExtraBadge _ _ _)

theorem nq_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      NQK Kq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; nq_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => nq_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | nq_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_transferCapsLoop _ _ _ _ _ _)

theorem nq_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : NQK Kq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_transferCaps _ _ _ _ _)

theorem nq_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : NQK Kq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doNormalTransfer _ _ _ _ _ _ _)

theorem nq_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : NQK Kq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doIpcTransfer _ _ _ _ _)

theorem nq_doNbrecvFailedTransfer (thread : ObjRef) : NQK Kq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_doNbrecvFailedTransfer _)

theorem nq_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : NQK Kq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_domainScheduleConfigure _ _ _)

theorem nq_setNextInterrupt  : NQK Kq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setNextInterrupt)

theorem nq_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : NQK Kq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_ifCondRefillUnblockCheck _ _ _)

theorem nq_switchSchedContext  : NQK Kq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_switchSchedContext)

theorem nq_scAndTimer  : NQK Kq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_scAndTimer)

theorem nq_scheduleChooseNewThread  : NQK Kq (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_scheduleChooseNewThread)

theorem nq_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : NQK Kq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_scheduleSwitchThreadFastfail _ _ _ _)

theorem nq_schedule  : NQK Kq (schedule (Z := Unit)) := by
  unfold schedule; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedule)

theorem nq_domainSetStart (index : Nat) : NQK Kq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_domainSetStart _)

theorem nq_postCapDeletion (cap : Cap) : NQK Kq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_postCapDeletion _)

theorem nq_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : NQK Kq (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_emptySlot _ _)

theorem nq_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4ArchDecodeInvocation _ _ _ _ _ _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem nq_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    NQKE Kq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem nq_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : NQKE Kq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem nq_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : NQK Kq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4ReplyFromKernelError _ _ _)

theorem nq_fl4SyscallFaultIP (thread : ObjRef) : NQK Kq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4SyscallFaultIP _)

theorem nq_getCapReg (reg : Register) : NQK Kq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getCapReg _)

theorem nq_getIrqSlot (irq : Irq) : NQK Kq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getIrqSlot _)

theorem nq_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : NQK Kq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getMrs _ _ _)

theorem nq_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : NQK Kq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleArchFaultReply _ _ _ _)

theorem nq_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : NQK Kq (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleFaultReply _ _ _ _)

theorem nq_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : NQK Kq (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleHypervisorFault _ _)

/-- `handle_no_fault` of a thread in no queue. -/
theorem nq_handleNoFault (t : ObjRef) (ht : t ∈ Kq) : NQK Kq (handleNoFault (Z := Unit) t) := by
  unfold handleNoFault; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| ((with_reducible refine nq_handleNoFault _ ?_); nq_mem))

theorem nq_handleReservedIrq (_irq : Irq) : NQK Kq (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleReservedIrq _)

theorem nq_handleSpuriousIrq  : NQK Kq (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleSpuriousIrq)

theorem nq_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : NQKE Kq (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_handleVmFault _ _)

theorem nq_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : NQK Kq (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_initArchObjects _ _ _ _ _ _)

theorem nq_threadSetDomain (tptr : ObjRef) (domain : Domain) : NQK Kq (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_threadSetDomain _ _)

theorem nq_setDomain (tptr : ObjRef) (newDom : Domain) : NQK Kq (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setDomain _ _)
end

end Fl4Proofs.P3.SInv
