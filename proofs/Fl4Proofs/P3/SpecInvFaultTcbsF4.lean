/- invA2: FaultTcbsS frame lemmas, part 4 (generated; see SpecInvFaultTcbsF1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsF3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem ft_mergeOverlappingRefills (scPtr : ObjRef) : FTK L (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_mergeOverlappingRefills _)

theorem ft_refillHeadOverlappingLoop (scPtr : ObjRef) : FTK L (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillHeadOverlappingLoop _)

theorem ft_refillUnblockCheck (scPtr : ObjRef) : FTK L (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_refillUnblockCheck _)

theorem ft_completeSignal (ntfnptr tptr : ObjRef) : FTK L (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_completeSignal _ _)

theorem ft_schedContextCancelYieldTo (thread : ObjRef) : FTK L (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextCancelYieldTo _)

theorem ft_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : FTK L (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupIpcBuffer _ _)

theorem ft_setMessageInfo (thread : ObjRef) (info : MessageInfo) : FTK L (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setMessageInfo _ _)

theorem ft_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : FTK L (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_storeWordOffs _ _ _)

theorem ft_replyFromKernel (thread : ObjRef) (x : Data × List Data) : FTK L (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_replyFromKernel _ _)

theorem ft_schedContextUpdateConsumed (scPtr : ObjRef) : FTK L (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_schedContextUpdateConsumed _)

theorem ft_setConsumed (scPtr tcbPtr : ObjRef) : FTK L (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_setConsumed _ _)

theorem ft_completeYieldTo (tcbPtr : ObjRef) : FTK L (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_completeYieldTo _)

theorem ft_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : FTKE L m) : FTK L (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ft_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_constOnFailure _ _ ?_)

theorem ft_copyGlobalMappings (newPm : ObjRef) : FTK L (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_copyGlobalMappings _)

theorem ft_loadWordOffs (ptr : ObjRef) (offs : Nat) : FTK L (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_loadWordOffs _ _)

theorem ft_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : FTK L (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_copyMrs _ _ _ _ _)

theorem ft_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : FTK L (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_createCap _ _ _ _ _)

theorem ft_dataToObjType (type : Data) : FTKE L (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_dataToObjType _)

theorem ft_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeBindNotification _ _)

theorem ft_deriveCap (slot : CslotPtr) (cap : Cap) : FTKE L (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_deriveCap _ _)

theorem ft_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupPivotSlot _ _ _)

theorem ft_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FTKE L (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_lookupSourceSlot _ _ _)

theorem ft_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : FTKE L (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeCnodeInvocation _ _ _ _)

theorem ft_slotCapLongRunningDelete (slot : CslotPtr) : FTK L (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_slotCapLongRunningDelete _)

theorem ft_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeCvSpace _ _ _ _)

theorem ft_subframeNode (nodeCap : Cap) (index depth : Data) : FTKE L (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_subframeNode _ _ _)

theorem ft_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDeriveSubframe _ _ _ _)

theorem ft_decodeDomainScheduleConfigure (args : List Data) : FTKE L (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainScheduleConfigure _)

theorem ft_decodeDomainScheduleSetStart (args : List Data) : FTKE L (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainScheduleSetStart _)

theorem ft_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : FTKE L (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainSet _ _)

theorem ft_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : FTKE L (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeDomainInvocation _ _ _)

theorem ft_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : FTK L (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4GetMr _ _ _)

theorem ft_fl4Arg (buf : Option ObjRef) (i : Nat) : FTKE L (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4Arg _ _)

theorem ft_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4ConfigureSingleStepping _ _)

theorem ft_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : FTKE L (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4FpuTransfer _ _ _ _)

theorem ft_fl4CheckBpNum (bp : Data) : FTKE L (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4CheckBpNum _)

theorem ft_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4GetBreakpoint _ _)

theorem ft_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, FTKE L (check x0)) : FTKE L (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ft_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible refine ft_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ft_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqControlRemapped _ _ _)

theorem ft_fl4ArchCheckIrq (irq : Data) : FTKE L (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_fl4ArchCheckIrq _)

theorem ft_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4IrqControl _ _ _ _ _)

theorem ft_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetBreakpoint _ _)

theorem ft_decodeFl4SetFlags (args : List Data) (t : ObjRef) : FTKE L (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetFlags _ _)

theorem ft_decodeFl4SetTimer (args : List Data) (t : ObjRef) : FTKE L (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4SetTimer _ _)

theorem ft_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FTKE L (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4UnsetBreakpoint _ _)

theorem ft_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : FTKE L (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeFl4TcbExt _ _ _ _ _)

theorem ft_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FTKE L (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqControlInvocation _ _ _ _)

theorem ft_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : FTKE L (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeIrqHandlerInvocation _ _ _)

theorem ft_getScReleased (scPtr : ObjRef) : FTK L (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_getScReleased _)

theorem ft_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextBind _ _)

theorem ft_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextUnbindObject _ _)

theorem ft_decodeSchedContextYieldTo (scPtr : ObjRef) : FTKE L (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextYieldTo _)

theorem ft_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : FTKE L (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedContextInvocation _ _ _)

theorem ft_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : FTKE L (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSchedControlInvocationFlags _ _ _)

theorem ft_rangeCheck (v minV maxV : Word) : FTKE L (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_rangeCheck _ _ _)

theorem ft_decodeSetFlags (args : List Data) (cap : Cap) : FTKE L (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetFlags _ _)

theorem ft_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : FTKE L (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetIpcBuffer _ _ _ _)

theorem ft_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetMcpriority _ _ _ _)

theorem ft_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FTKE L (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_decodeSetPriority _ _ _ _)

theorem ft_isBlocked (thread : ObjRef) : FTK L (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ft_auto
macro_rules | `(tactic| ft_leaf) => `(tactic| with_reducible exact ft_isBlocked _)
end

end Fl4Proofs.P3.SInv
