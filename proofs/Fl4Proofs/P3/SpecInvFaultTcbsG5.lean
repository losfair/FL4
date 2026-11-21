/- ft2: generic frame lemmas, part 5 (generated; see SpecInvFaultTcbsG1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsG4
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Fq : FQ} {Sq : Set ObjRef} {Cq : ObjRef → Prop}

theorem fg_isBlocked (thread : ObjRef) : FGK Fq Sq Cq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_isBlocked _)

theorem fg_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : FGKE Fq Sq Cq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUpdateSc _ _ _)

theorem fg_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetSchedParams _ _ _ _)

theorem fg_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetSpace _ _ _ _)

theorem fg_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetTimeoutEp _ _ _)

theorem fg_decodeSetTlsBase (args : List Data) (cap : Cap) : FGKE Fq Sq Cq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetTlsBase _ _)

theorem fg_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTcbConfigure _ _ _ _)

theorem fg_decodeUnbindNotification (cap : Cap) : FGKE Fq Sq Cq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem fg_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTcbInvocation _ _ _ _ _)

theorem fg_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUntypedInvocation _ _ _ _ _)

theorem fg_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : FGKE Fq Sq Cq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeInvocation _ _ _ _ _ _ _ _)

theorem fg_decodePml4Flush (cap : ArchCap) : FGKE Fq Sq Cq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodePml4Flush _)

theorem fg_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : FGKE Fq Sq Cq (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_frameMappingSlot _ _ _ _)

theorem fg_decodeTestAndClearAccessed (cap : ArchCap) : FGKE Fq Sq Cq (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeTestAndClearAccessed _)

theorem fg_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem fg_deletedIrqHandler (irq : Irq) : FGK Fq Sq Cq (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deletedIrqHandler _)

theorem fg_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : FGK Fq Sq Cq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_makeArchFaultMsg _ _)

theorem fg_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : FGK Fq Sq Cq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_makeFaultMsg _ _)

theorem fg_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : FGK Fq Sq Cq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doFaultTransfer _ _ _ _)

theorem fg_getMessageInfo (thread : ObjRef) : FGK Fq Sq Cq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getMessageInfo _)

theorem fg_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : FGK Fq Sq Cq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; fg_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getExtraCptrs _ _)

theorem fg_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : FGKE Fq Sq Cq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupSlotForThread _ _)

theorem fg_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : FGKE Fq Sq Cq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupCapAndSlot _ _)

theorem fg_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : FGKE Fq Sq Cq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupExtraCaps _ _ _)

theorem fg_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : FGKE Fq Sq Cq m) : FGK Fq Sq Cq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_emptyOnFailure _ ?_)

theorem fg_loadCapTransfer (buffer : ObjRef) : FGK Fq Sq Cq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadCapTransfer _)

theorem fg_lookupCap (thread : ObjRef) (ref : CapRef) : FGKE Fq Sq Cq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupCap _ _)

theorem fg_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : FGKE Fq Sq Cq m) : FGKE Fq Sq Cq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_unifyFailure _ ?_)

theorem fg_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : FGK Fq Sq Cq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getReceiveSlots _ _)

theorem fg_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : FGK Fq Sq Cq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setExtraBadge _ _ _)

theorem fg_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      FGK Fq Sq Cq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; fg_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => fg_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | fg_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_transferCapsLoop _ _ _ _ _ _)

theorem fg_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : FGK Fq Sq Cq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_transferCaps _ _ _ _ _)

theorem fg_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : FGK Fq Sq Cq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doNormalTransfer _ _ _ _ _ _ _)

theorem fg_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : FGK Fq Sq Cq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doIpcTransfer _ _ _ _ _)

theorem fg_doNbrecvFailedTransfer (thread : ObjRef) : FGK Fq Sq Cq (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_doNbrecvFailedTransfer _)

theorem fg_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : FGK Fq Sq Cq (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_domainScheduleConfigure _ _ _)

theorem fg_setNextInterrupt  : FGK Fq Sq Cq (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setNextInterrupt)

theorem fg_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : FGK Fq Sq Cq (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_ifCondRefillUnblockCheck _ _ _)

theorem fg_switchSchedContext  : FGK Fq Sq Cq (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_switchSchedContext)

theorem fg_scAndTimer  : FGK Fq Sq Cq (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scAndTimer)

theorem fg_nextDomain  : FGK Fq Sq Cq (nextDomain (Z := Unit)) := by
  unfold nextDomain; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_nextDomain)

theorem fg_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : FGK Fq Sq Cq (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_scheduleSwitchThreadFastfail _ _ _ _)

theorem fg_domainSetStart (index : Nat) : FGK Fq Sq Cq (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_domainSetStart _)

theorem fg_postCapDeletion (cap : Cap) : FGK Fq Sq Cq (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_postCapDeletion _)

theorem fg_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : FGK Fq Sq Cq (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_emptySlot _ _)

theorem fg_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem fg_performDeriveSubframe (iv : Fl4SubframeInvocation) : FGK Fq Sq Cq (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performDeriveSubframe _)

theorem fg_performPml4Flush (a0 : Fl4Pml4Invocation) : FGK Fq Sq Cq (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performPml4Flush _)

theorem fg_performTestAndClearAccessed (_slot : ObjRef) : FGK Fq Sq Cq (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_performTestAndClearAccessed _)

theorem fg_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : FGKE Fq Sq Cq (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchPerformInvocation _)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem fg_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    FGKE Fq Sq Cq (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem fg_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : FGKE Fq Sq Cq (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem fg_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : FGK Fq Sq Cq (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ReplyFromKernelError _ _ _)

theorem fg_fl4SyscallFaultIP (thread : ObjRef) : FGK Fq Sq Cq (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4SyscallFaultIP _)

theorem fg_getCapReg (reg : Register) : FGK Fq Sq Cq (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getCapReg _)

theorem fg_getIrqSlot (irq : Irq) : FGK Fq Sq Cq (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getIrqSlot _)

theorem fg_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : FGK Fq Sq Cq (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getMrs _ _ _)

theorem fg_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : FGK Fq Sq Cq (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_handleArchFaultReply _ _ _ _)
end

end Fl4Proofs.P3.SInv
