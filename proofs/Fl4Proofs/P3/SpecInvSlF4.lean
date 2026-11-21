/- sl1: ScLive family lemmas, part 4 (generated; see SpecInvSlF1). -/
import Fl4Proofs.P3.SpecInvSlF3
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Iq : ObjRef × ObjRef} {Kq : List ObjRef}

theorem sl_copyGlobalMappings (newPm : ObjRef) : SLK Iq Kq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_copyGlobalMappings _)

theorem sl_loadWordOffs (ptr : ObjRef) (offs : Nat) : SLK Iq Kq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_loadWordOffs _ _)

theorem sl_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : SLK Iq Kq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_copyMrs _ _ _ _ _)

theorem sl_dataToObjType (type : Data) : SLKE Iq Kq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_dataToObjType _)

theorem sl_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeBindNotification _ _)

theorem sl_deriveCap (slot : CslotPtr) (cap : Cap) : SLKE Iq Kq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_deriveCap _ _)

theorem sl_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SLKE Iq Kq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupPivotSlot _ _ _)

theorem sl_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : SLKE Iq Kq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_lookupSourceSlot _ _ _)

theorem sl_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeCnodeInvocation _ _ _ _)

theorem sl_slotCapLongRunningDelete (slot : CslotPtr) : SLK Iq Kq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_slotCapLongRunningDelete _)

theorem sl_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeCvSpace _ _ _ _)

theorem sl_subframeNode (nodeCap : Cap) (index depth : Data) : SLKE Iq Kq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_subframeNode _ _ _)

theorem sl_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDeriveSubframe _ _ _ _)

theorem sl_decodeDomainScheduleConfigure (args : List Data) : SLKE Iq Kq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainScheduleConfigure _)

theorem sl_decodeDomainScheduleSetStart (args : List Data) : SLKE Iq Kq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainScheduleSetStart _)

theorem sl_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainSet _ _)

theorem sl_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeDomainInvocation _ _ _)

theorem sl_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : SLK Iq Kq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4GetMr _ _ _)

theorem sl_fl4Arg (buf : Option ObjRef) (i : Nat) : SLKE Iq Kq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4Arg _ _)

theorem sl_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4ConfigureSingleStepping _ _)

theorem sl_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4FpuTransfer _ _ _ _)

theorem sl_fl4CheckBpNum (bp : Data) : SLKE Iq Kq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4CheckBpNum _)

theorem sl_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4GetBreakpoint _ _)

theorem sl_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, SLKE Iq Kq (check x0)) : SLKE Iq Kq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; sl_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible refine sl_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem sl_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqControlRemapped _ _ _)

theorem sl_fl4ArchCheckIrq (irq : Data) : SLKE Iq Kq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_fl4ArchCheckIrq _)

theorem sl_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4IrqControl _ _ _ _ _)

theorem sl_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetBreakpoint _ _)

theorem sl_decodeFl4SetFlags (args : List Data) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetFlags _ _)

theorem sl_decodeFl4SetTimer (args : List Data) (t : ObjRef) : SLKE Iq Kq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4SetTimer _ _)

theorem sl_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : SLKE Iq Kq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4UnsetBreakpoint _ _)

theorem sl_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : SLKE Iq Kq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeFl4TcbExt _ _ _ _ _)

theorem sl_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : SLKE Iq Kq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqControlInvocation _ _ _ _)

theorem sl_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeIrqHandlerInvocation _ _ _)

theorem sl_getScReleased (scPtr : ObjRef) : SLK Iq Kq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScReleased _)

theorem sl_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextBind _ _)

theorem sl_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : SLK Iq Kq (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_getScObjRef _ _)

theorem sl_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextUnbindObject _ _)

theorem sl_decodeSchedContextYieldTo (scPtr : ObjRef) : SLKE Iq Kq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextYieldTo _)

theorem sl_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : SLKE Iq Kq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedContextInvocation _ _ _)

theorem sl_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : SLKE Iq Kq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSchedControlInvocationFlags _ _ _)

theorem sl_rangeCheck (v minV maxV : Word) : SLKE Iq Kq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_rangeCheck _ _ _)

theorem sl_decodeSetFlags (args : List Data) (cap : Cap) : SLKE Iq Kq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetFlags _ _)

theorem sl_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetIpcBuffer _ _ _ _)

theorem sl_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetMcpriority _ _ _ _)

theorem sl_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetPriority _ _ _ _)

theorem sl_isBlocked (thread : ObjRef) : SLK Iq Kq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_isBlocked _)

theorem sl_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : SLKE Iq Kq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUpdateSc _ _ _)

theorem sl_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetSchedParams _ _ _ _)

theorem sl_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetSpace _ _ _ _)

theorem sl_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetTimeoutEp _ _ _)

theorem sl_decodeSetTlsBase (args : List Data) (cap : Cap) : SLKE Iq Kq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeSetTlsBase _ _)

theorem sl_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTcbConfigure _ _ _ _)

theorem sl_decodeUnbindNotification (cap : Cap) : SLKE Iq Kq (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem sl_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : SLKE Iq Kq (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeTcbInvocation _ _ _ _ _)

theorem sl_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : SLKE Iq Kq (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeUntypedInvocation _ _ _ _ _)

theorem sl_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : SLKE Iq Kq (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; sl_auto
macro_rules | `(tactic| sl_leaf) => `(tactic| with_reducible exact sl_decodeInvocation _ _ _ _ _ _ _ _)
end

end Fl4Proofs.P3.SInvL
