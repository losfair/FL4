/- il1: IfLiveT family lemmas, part 4 (generated; see SpecInvNtfnQL1). -/
import Fl4Proofs.P3.SpecInvNtfnQL3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem il_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : ILKE Kq m) : ILK Kq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; il_auto
  all_goals first | exact h_m
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_constOnFailure _ _ ?_)

theorem il_copyGlobalMappings (newPm : ObjRef) : ILK Kq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_copyGlobalMappings _)

theorem il_loadWordOffs (ptr : ObjRef) (offs : Nat) : ILK Kq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_loadWordOffs _ _)

theorem il_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : ILK Kq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_copyMrs _ _ _ _ _)

theorem il_dataToObjType (type : Data) : ILKE Kq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_dataToObjType _)

theorem il_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeBindNotification _ _)

theorem il_deriveCap (slot : CslotPtr) (cap : Cap) : ILKE Kq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_deriveCap _ _)

theorem il_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : ILKE Kq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupPivotSlot _ _ _)

theorem il_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : ILKE Kq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_lookupSourceSlot _ _ _)

theorem il_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : ILKE Kq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeCnodeInvocation _ _ _ _)

theorem il_slotCapLongRunningDelete (slot : CslotPtr) : ILK Kq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_slotCapLongRunningDelete _)

theorem il_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : ILKE Kq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeCvSpace _ _ _ _)

theorem il_subframeNode (nodeCap : Cap) (index depth : Data) : ILKE Kq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_subframeNode _ _ _)

theorem il_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : ILKE Kq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeDeriveSubframe _ _ _ _)

theorem il_decodeDomainScheduleConfigure (args : List Data) : ILKE Kq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeDomainScheduleConfigure _)

theorem il_decodeDomainScheduleSetStart (args : List Data) : ILKE Kq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeDomainScheduleSetStart _)

theorem il_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : ILKE Kq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeDomainSet _ _)

theorem il_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : ILKE Kq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeDomainInvocation _ _ _)

theorem il_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : ILK Kq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4GetMr _ _ _)

theorem il_fl4Arg (buf : Option ObjRef) (i : Nat) : ILKE Kq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4Arg _ _)

theorem il_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : ILKE Kq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4ConfigureSingleStepping _ _)

theorem il_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : ILKE Kq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4FpuTransfer _ _ _ _)

theorem il_fl4CheckBpNum (bp : Data) : ILKE Kq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4CheckBpNum _)

theorem il_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : ILKE Kq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4GetBreakpoint _ _)

theorem il_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, ILKE Kq (check x0)) : ILKE Kq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; il_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible refine il_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem il_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : ILKE Kq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeIrqControlRemapped _ _ _)

theorem il_fl4ArchCheckIrq (irq : Data) : ILKE Kq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_fl4ArchCheckIrq _)

theorem il_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : ILKE Kq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4IrqControl _ _ _ _ _)

theorem il_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : ILKE Kq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4SetBreakpoint _ _)

theorem il_decodeFl4SetFlags (args : List Data) (t : ObjRef) : ILKE Kq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4SetFlags _ _)

theorem il_decodeFl4SetTimer (args : List Data) (t : ObjRef) : ILKE Kq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4SetTimer _ _)

theorem il_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : ILKE Kq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4UnsetBreakpoint _ _)

theorem il_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : ILKE Kq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeFl4TcbExt _ _ _ _ _)

theorem il_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : ILKE Kq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeIrqControlInvocation _ _ _ _)

theorem il_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : ILKE Kq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeIrqHandlerInvocation _ _ _)

theorem il_getScReleased (scPtr : ObjRef) : ILK Kq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_getScReleased _)

theorem il_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : ILKE Kq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSchedContextBind _ _)

theorem il_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : ILKE Kq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSchedContextUnbindObject _ _)

theorem il_decodeSchedContextYieldTo (scPtr : ObjRef) : ILKE Kq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSchedContextYieldTo _)

theorem il_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : ILKE Kq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSchedContextInvocation _ _ _)

theorem il_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : ILKE Kq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSchedControlInvocationFlags _ _ _)

theorem il_rangeCheck (v minV maxV : Word) : ILKE Kq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_rangeCheck _ _ _)

theorem il_decodeSetFlags (args : List Data) (cap : Cap) : ILKE Kq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetFlags _ _)

theorem il_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : ILKE Kq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetIpcBuffer _ _ _ _)

theorem il_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetMcpriority _ _ _ _)

theorem il_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetPriority _ _ _ _)

theorem il_isBlocked (thread : ObjRef) : ILK Kq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_isBlocked _)

theorem il_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : ILKE Kq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeUpdateSc _ _ _)

theorem il_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetSchedParams _ _ _ _)

theorem il_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : ILKE Kq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetSpace _ _ _ _)

theorem il_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetTimeoutEp _ _ _)

theorem il_decodeSetTlsBase (args : List Data) (cap : Cap) : ILKE Kq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeSetTlsBase _ _)

theorem il_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : ILKE Kq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeTcbConfigure _ _ _ _)

theorem il_decodeUnbindNotification (cap : Cap) : ILKE Kq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem il_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : ILKE Kq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeTcbInvocation _ _ _ _ _)

theorem il_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : ILKE Kq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeUntypedInvocation _ _ _ _ _)

theorem il_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : ILKE Kq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodeInvocation _ _ _ _ _ _ _ _)

theorem il_decodePml4Flush (cap : ArchCap) : ILKE Kq (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; il_auto
macro_rules | `(tactic| il_leaf) => `(tactic| with_reducible exact il_decodePml4Flush _)
end

end Fl4Proofs.P3.SInv
