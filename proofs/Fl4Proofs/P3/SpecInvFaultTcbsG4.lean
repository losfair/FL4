/- ft2: generic frame lemmas, part 4 (generated; see SpecInvFaultTcbsG1). -/
import Fl4Proofs.P3.SpecInvFaultTcbsG3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Fq : FQ} {Sq : Set ObjRef} {Cq : ObjRef → Prop}

theorem fg_refillHeadOverlappingLoop (scPtr : ObjRef) : FGK Fq Sq Cq (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillHeadOverlappingLoop _)

theorem fg_refillUnblockCheck (scPtr : ObjRef) : FGK Fq Sq Cq (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_refillUnblockCheck _)

theorem fg_completeSignal (ntfnptr tptr : ObjRef) : FGK Fq Sq Cq (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_completeSignal _ _)

theorem fg_schedContextCancelYieldTo (thread : ObjRef) : FGK Fq Sq Cq (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextCancelYieldTo _)

theorem fg_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : FGK Fq Sq Cq (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupIpcBuffer _ _)

theorem fg_setMessageInfo (thread : ObjRef) (info : MessageInfo) : FGK Fq Sq Cq (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setMessageInfo _ _)

theorem fg_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : FGK Fq Sq Cq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_storeWordOffs _ _ _)

theorem fg_replyFromKernel (thread : ObjRef) (x : Data × List Data) : FGK Fq Sq Cq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_replyFromKernel _ _)

theorem fg_schedContextUpdateConsumed (scPtr : ObjRef) : FGK Fq Sq Cq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_schedContextUpdateConsumed _)

theorem fg_setConsumed (scPtr tcbPtr : ObjRef) : FGK Fq Sq Cq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_setConsumed _ _)

theorem fg_completeYieldTo (tcbPtr : ObjRef) : FGK Fq Sq Cq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_completeYieldTo _)

theorem fg_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : FGKE Fq Sq Cq m) : FGK Fq Sq Cq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; fg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_constOnFailure _ _ ?_)

theorem fg_copyGlobalMappings (newPm : ObjRef) : FGK Fq Sq Cq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_copyGlobalMappings _)

theorem fg_loadWordOffs (ptr : ObjRef) (offs : Nat) : FGK Fq Sq Cq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_loadWordOffs _ _)

theorem fg_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : FGK Fq Sq Cq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_copyMrs _ _ _ _ _)

theorem fg_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : FGK Fq Sq Cq (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_createCap _ _ _ _ _)

theorem fg_dataToObjType (type : Data) : FGKE Fq Sq Cq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_dataToObjType _)

theorem fg_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeBindNotification _ _)

theorem fg_deriveCap (slot : CslotPtr) (cap : Cap) : FGKE Fq Sq Cq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_deriveCap _ _)

theorem fg_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FGKE Fq Sq Cq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupPivotSlot _ _ _)

theorem fg_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : FGKE Fq Sq Cq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_lookupSourceSlot _ _ _)

theorem fg_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : FGKE Fq Sq Cq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeCnodeInvocation _ _ _ _)

theorem fg_slotCapLongRunningDelete (slot : CslotPtr) : FGK Fq Sq Cq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_slotCapLongRunningDelete _)

theorem fg_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeCvSpace _ _ _ _)

theorem fg_subframeNode (nodeCap : Cap) (index depth : Data) : FGKE Fq Sq Cq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_subframeNode _ _ _)

theorem fg_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDeriveSubframe _ _ _ _)

theorem fg_decodeDomainScheduleConfigure (args : List Data) : FGKE Fq Sq Cq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainScheduleConfigure _)

theorem fg_decodeDomainScheduleSetStart (args : List Data) : FGKE Fq Sq Cq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainScheduleSetStart _)

theorem fg_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainSet _ _)

theorem fg_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeDomainInvocation _ _ _)

theorem fg_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : FGK Fq Sq Cq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4GetMr _ _ _)

theorem fg_fl4Arg (buf : Option ObjRef) (i : Nat) : FGKE Fq Sq Cq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4Arg _ _)

theorem fg_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4ConfigureSingleStepping _ _)

theorem fg_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4FpuTransfer _ _ _ _)

theorem fg_fl4CheckBpNum (bp : Data) : FGKE Fq Sq Cq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4CheckBpNum _)

theorem fg_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4GetBreakpoint _ _)

theorem fg_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, FGKE Fq Sq Cq (check x0)) : FGKE Fq Sq Cq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; fg_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible refine fg_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem fg_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqControlRemapped _ _ _)

theorem fg_fl4ArchCheckIrq (irq : Data) : FGKE Fq Sq Cq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_fl4ArchCheckIrq _)

theorem fg_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4IrqControl _ _ _ _ _)

theorem fg_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetBreakpoint _ _)

theorem fg_decodeFl4SetFlags (args : List Data) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetFlags _ _)

theorem fg_decodeFl4SetTimer (args : List Data) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4SetTimer _ _)

theorem fg_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : FGKE Fq Sq Cq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4UnsetBreakpoint _ _)

theorem fg_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : FGKE Fq Sq Cq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeFl4TcbExt _ _ _ _ _)

theorem fg_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : FGKE Fq Sq Cq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqControlInvocation _ _ _ _)

theorem fg_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeIrqHandlerInvocation _ _ _)

theorem fg_getScReleased (scPtr : ObjRef) : FGK Fq Sq Cq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_getScReleased _)

theorem fg_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextBind _ _)

theorem fg_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextUnbindObject _ _)

theorem fg_decodeSchedContextYieldTo (scPtr : ObjRef) : FGKE Fq Sq Cq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextYieldTo _)

theorem fg_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedContextInvocation _ _ _)

theorem fg_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : FGKE Fq Sq Cq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSchedControlInvocationFlags _ _ _)

theorem fg_rangeCheck (v minV maxV : Word) : FGKE Fq Sq Cq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_rangeCheck _ _ _)

theorem fg_decodeSetFlags (args : List Data) (cap : Cap) : FGKE Fq Sq Cq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetFlags _ _)

theorem fg_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetIpcBuffer _ _ _ _)

theorem fg_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetMcpriority _ _ _ _)

theorem fg_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : FGKE Fq Sq Cq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; fg_auto
macro_rules | `(tactic| fg_leaf) => `(tactic| with_reducible exact fg_decodeSetPriority _ _ _ _)
end

end Fl4Proofs.P3.SInv
