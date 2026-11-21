/- nq1: the current-thread frame `CTK c` (the current thread stays `c`) for every spec function reachable from the syscall entry except the scheduler, part 3 (generated: proofs/scratch/nq1/mkck.sh). -/
import Fl4Proofs.P3.SpecInvNtfnQC2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {cq : ObjRef}

theorem ct_captransferFromWords (ptr : Word) : CTK cq (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_captransferFromWords _)

theorem ct_isValidTimeoutHandler (tptr : ObjRef) : CTK cq (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_isValidTimeoutHandler _)

theorem ct_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : CTK cq (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_makeArchFaultMsg _ _)

theorem ct_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : CTK cq (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_makeFaultMsg _ _)

theorem ct_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : CTK cq (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doFaultTransfer _ _ _ _)

theorem ct_loadWordOffs (ptr : ObjRef) (offs : Nat) : CTK cq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_loadWordOffs _ _)

theorem ct_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : CTK cq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_copyMrs _ _ _ _ _)

theorem ct_getMessageInfo (thread : ObjRef) : CTK cq (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getMessageInfo _)

theorem ct_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : CTK cq (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ct_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getExtraCptrs _ _)

theorem ct_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : CTKE cq (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupSlotForThread _ _)

theorem ct_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : CTKE cq (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupCapAndSlot _ _)

theorem ct_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : CTKE cq (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupExtraCaps _ _ _)

theorem ct_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : CTKE cq m) : CTK cq (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_emptyOnFailure _ ?_)

theorem ct_loadCapTransfer (buffer : ObjRef) : CTK cq (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_loadCapTransfer _)

theorem ct_lookupCap (thread : ObjRef) (ref : CapRef) : CTKE cq (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupCap _ _)

theorem ct_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : CTKE cq m) : CTKE cq (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_unifyFailure _ ?_)

theorem ct_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : CTK cq (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getReceiveSlots _ _)

theorem ct_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : CTKE cq m) : CTK cq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_constOnFailure _ _ ?_)

theorem ct_deriveCap (slot : CslotPtr) (cap : Cap) : CTKE cq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_deriveCap _ _)

theorem ct_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : CTK cq (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_setExtraBadge _ _ _)

theorem ct_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      CTK cq (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ct_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ct_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ct_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_transferCapsLoop _ _ _ _ _ _)

theorem ct_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : CTK cq (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_transferCaps _ _ _ _ _)

theorem ct_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : CTK cq (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doNormalTransfer _ _ _ _ _ _ _)

theorem ct_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : CTK cq (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_doIpcTransfer _ _ _ _ _)

theorem ct_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : CTK cq (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_replyPush _ _ _ _)

theorem ct_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : CTK cq (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_orderedInsert _ _ _ _)

theorem ct_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : CTK cq (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbAppend _ _)

theorem ct_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : CTK cq (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbEpAppend _ _ _)

theorem ct_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : CTK cq (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_sendIpcBlocked _ _ _ _ _ _)

theorem ct_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : CTK cq (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_sendIpc _ _ _ _ _ _ _ _)

theorem ct_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : CTK cq (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_sendFaultIpc _ _ _ _)

theorem ct_handleTimeout (tptr : ObjRef) (ex : Fault) : CTK cq (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleTimeout _ _)

theorem ct_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : CTK cq (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_readyTimesAppend _ _)

theorem ct_tcbReleaseEnqueue (tcbPtr : ObjRef) : CTK cq (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_tcbReleaseEnqueue _)

theorem ct_postpone (scPtr : ObjRef) : CTK cq (postpone (Z := Unit) scPtr) := by
  unfold postpone; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_postpone _)

theorem ct_endTimeslice (canTimeout : Bool) : CTK cq (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_endTimeslice _)

theorem ct_getRefills (scPtr : ObjRef) : CTK cq (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getRefills _)

theorem ct_refillSize (scPtr : ObjRef) : CTK cq (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillSize _)

theorem ct_refillSingle (scPtr : ObjRef) : CTK cq (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillSingle _)

theorem ct_getRefillTail (scPtr : ObjRef) : CTK cq (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getRefillTail _)

theorem ct_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : CTK cq (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillAddTail _ _)

theorem ct_refillFull (scPtr : ObjRef) : CTK cq (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillFull _)

theorem ct_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : CTK cq (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_updateRefillTl _ _)

theorem ct_scheduleUsed (scPtr : ObjRef) (new : Refill) : CTK cq (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_scheduleUsed _ _)

theorem ct_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : CTK cq (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_chargeEntireHeadRefill _ _)

theorem ct_handleOverrun (scPtr : ObjRef) (usage : Ticks) : CTK cq (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_handleOverrun _ _)

theorem ct_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : CTK cq (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_mergeNonoverlappingHeadRefill _)

theorem ct_headInsufficientLoop (scPtr : ObjRef) : CTK cq (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_headInsufficientLoop _)

theorem ct_refillBudgetCheck (usage : Ticks) : CTK cq (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillBudgetCheck _)

theorem ct_refillResetRr (cscPtr : ObjRef) : CTK cq (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillResetRr _)

theorem ct_chargeBudget (consumed : Ticks) (canTimeout : Bool) : CTK cq (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_chargeBudget _ _)

theorem ct_checkBudget  : CTK cq (checkBudget (Z := Unit)) := by
  unfold checkBudget; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkBudget)

theorem ct_checkBudgetRestart  : CTK cq (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkBudgetRestart)

theorem ct_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : CTK cq m) : CTK cq (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ct_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_checkCapAt _ _ _ ?_)

theorem ct_checkDomainTime  : CTK cq (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkDomainTime)

theorem ct_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : CTKE cq (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkHandlerEp _ _)

theorem ct_checkPrio (newPrio : Data) (authTcb : ObjRef) : CTKE cq (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkPrio _ _)

theorem ct_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : CTKE cq (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_checkValidIpcBuffer _ _)

theorem ct_refillBudgetCheckRoundRobin (usage : Ticks) : CTK cq (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_refillBudgetCheckRoundRobin _)

theorem ct_commitTime  : CTK cq (commitTime (Z := Unit)) := by
  unfold commitTime; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_commitTime)

theorem ct_schedContextResume (scPtr : ObjRef) : CTK cq (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_schedContextResume _)

theorem ct_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : CTK cq (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_maybeDonateSc _ _)

theorem ct_completeSignal (ntfnptr tptr : ObjRef) : CTK cq (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_completeSignal _ _)

theorem ct_copyGlobalMappings (newPm : ObjRef) : CTK cq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_copyGlobalMappings _)

theorem ct_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : CTK cq (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_createCap _ _ _ _ _)

theorem ct_dataToObjType (type : Data) : CTKE cq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_dataToObjType _)

theorem ct_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeBindNotification _ _)

theorem ct_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : CTKE cq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupPivotSlot _ _ _)

theorem ct_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : CTKE cq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_lookupSourceSlot _ _ _)

theorem ct_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : CTKE cq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeCnodeInvocation _ _ _ _)

theorem ct_slotCapLongRunningDelete (slot : CslotPtr) : CTK cq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_slotCapLongRunningDelete _)

theorem ct_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : CTKE cq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeCvSpace _ _ _ _)

theorem ct_subframeNode (nodeCap : Cap) (index depth : Data) : CTKE cq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_subframeNode _ _ _)

theorem ct_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : CTKE cq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeDeriveSubframe _ _ _ _)

theorem ct_decodeDomainScheduleConfigure (args : List Data) : CTKE cq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeDomainScheduleConfigure _)

theorem ct_decodeDomainScheduleSetStart (args : List Data) : CTKE cq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeDomainScheduleSetStart _)

theorem ct_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : CTKE cq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeDomainSet _ _)

theorem ct_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : CTKE cq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeDomainInvocation _ _ _)

theorem ct_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : CTK cq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4GetMr _ _ _)

theorem ct_fl4Arg (buf : Option ObjRef) (i : Nat) : CTKE cq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4Arg _ _)

theorem ct_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : CTKE cq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4ConfigureSingleStepping _ _)

theorem ct_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : CTKE cq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4FpuTransfer _ _ _ _)

theorem ct_fl4CheckBpNum (bp : Data) : CTKE cq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4CheckBpNum _)

theorem ct_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : CTKE cq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4GetBreakpoint _ _)

theorem ct_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, CTKE cq (check x0)) : CTKE cq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ct_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible refine ct_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ct_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : CTKE cq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeIrqControlRemapped _ _ _)

theorem ct_fl4ArchCheckIrq (irq : Data) : CTKE cq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_fl4ArchCheckIrq _)

theorem ct_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : CTKE cq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4IrqControl _ _ _ _ _)

theorem ct_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : CTKE cq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4SetBreakpoint _ _)

theorem ct_decodeFl4SetFlags (args : List Data) (t : ObjRef) : CTKE cq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4SetFlags _ _)

theorem ct_decodeFl4SetTimer (args : List Data) (t : ObjRef) : CTKE cq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4SetTimer _ _)

theorem ct_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : CTKE cq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4UnsetBreakpoint _ _)

theorem ct_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : CTKE cq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeFl4TcbExt _ _ _ _ _)

theorem ct_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : CTKE cq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeIrqControlInvocation _ _ _ _)

theorem ct_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : CTKE cq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeIrqHandlerInvocation _ _ _)

theorem ct_getScReleased (scPtr : ObjRef) : CTK cq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_getScReleased _)

theorem ct_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : CTKE cq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSchedContextBind _ _)

theorem ct_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : CTKE cq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSchedContextUnbindObject _ _)

theorem ct_decodeSchedContextYieldTo (scPtr : ObjRef) : CTKE cq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSchedContextYieldTo _)

theorem ct_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : CTKE cq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSchedContextInvocation _ _ _)

theorem ct_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : CTKE cq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSchedControlInvocationFlags _ _ _)

theorem ct_rangeCheck (v minV maxV : Word) : CTKE cq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_rangeCheck _ _ _)

theorem ct_decodeSetFlags (args : List Data) (cap : Cap) : CTKE cq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetFlags _ _)

theorem ct_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : CTKE cq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetIpcBuffer _ _ _ _)

theorem ct_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : CTKE cq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ct_auto
macro_rules | `(tactic| ct_leaf) => `(tactic| with_reducible exact ct_decodeSetMcpriority _ _ _ _)
end

end Fl4Proofs.P3.SInv
