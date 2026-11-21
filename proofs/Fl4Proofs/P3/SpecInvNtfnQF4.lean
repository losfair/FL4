/- nq1: NtfnQB family lemmas, part 4 (generated; see SpecInvNtfnQF1). -/
import Fl4Proofs.P3.SpecInvNtfnQF3
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {Kq : List ObjRef}

theorem nq_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : NQK Kq (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_storeWordOffs _ _ _)

theorem nq_replyFromKernel (thread : ObjRef) (x : Data × List Data) : NQK Kq (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_replyFromKernel _ _)

theorem nq_schedContextUpdateConsumed (scPtr : ObjRef) : NQK Kq (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_schedContextUpdateConsumed _)

theorem nq_setConsumed (scPtr tcbPtr : ObjRef) : NQK Kq (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_setConsumed _ _)

theorem nq_completeYieldTo (tcbPtr : ObjRef) : NQK Kq (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_completeYieldTo _)

theorem nq_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : NQKE Kq m) : NQK Kq (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; nq_auto
  all_goals first | exact h_m
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_constOnFailure _ _ ?_)

theorem nq_copyGlobalMappings (newPm : ObjRef) : NQK Kq (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_copyGlobalMappings _)

theorem nq_loadWordOffs (ptr : ObjRef) (offs : Nat) : NQK Kq (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_loadWordOffs _ _)

theorem nq_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : NQK Kq (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_copyMrs _ _ _ _ _)

theorem nq_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : NQK Kq (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_createCap _ _ _ _ _)

theorem nq_dataToObjType (type : Data) : NQKE Kq (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_dataToObjType _)

theorem nq_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeBindNotification _ _)

theorem nq_deriveCap (slot : CslotPtr) (cap : Cap) : NQKE Kq (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_deriveCap _ _)

theorem nq_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NQKE Kq (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupPivotSlot _ _ _)

theorem nq_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : NQKE Kq (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_lookupSourceSlot _ _ _)

theorem nq_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : NQKE Kq (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeCnodeInvocation _ _ _ _)

theorem nq_slotCapLongRunningDelete (slot : CslotPtr) : NQK Kq (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_slotCapLongRunningDelete _)

theorem nq_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NQKE Kq (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeCvSpace _ _ _ _)

theorem nq_subframeNode (nodeCap : Cap) (index depth : Data) : NQKE Kq (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_subframeNode _ _ _)

theorem nq_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : NQKE Kq (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeDeriveSubframe _ _ _ _)

theorem nq_decodeDomainScheduleConfigure (args : List Data) : NQKE Kq (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeDomainScheduleConfigure _)

theorem nq_decodeDomainScheduleSetStart (args : List Data) : NQKE Kq (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeDomainScheduleSetStart _)

theorem nq_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : NQKE Kq (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeDomainSet _ _)

theorem nq_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : NQKE Kq (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeDomainInvocation _ _ _)

theorem nq_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : NQK Kq (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4GetMr _ _ _)

theorem nq_fl4Arg (buf : Option ObjRef) (i : Nat) : NQKE Kq (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4Arg _ _)

theorem nq_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : NQKE Kq (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4ConfigureSingleStepping _ _)

theorem nq_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : NQKE Kq (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4FpuTransfer _ _ _ _)

theorem nq_fl4CheckBpNum (bp : Data) : NQKE Kq (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4CheckBpNum _)

theorem nq_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NQKE Kq (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4GetBreakpoint _ _)

theorem nq_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, NQKE Kq (check x0)) : NQKE Kq (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; nq_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible refine nq_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem nq_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NQKE Kq (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeIrqControlRemapped _ _ _)

theorem nq_fl4ArchCheckIrq (irq : Data) : NQKE Kq (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_fl4ArchCheckIrq _)

theorem nq_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NQKE Kq (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4IrqControl _ _ _ _ _)

theorem nq_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NQKE Kq (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4SetBreakpoint _ _)

theorem nq_decodeFl4SetFlags (args : List Data) (t : ObjRef) : NQKE Kq (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4SetFlags _ _)

theorem nq_decodeFl4SetTimer (args : List Data) (t : ObjRef) : NQKE Kq (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4SetTimer _ _)

theorem nq_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : NQKE Kq (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4UnsetBreakpoint _ _)

theorem nq_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : NQKE Kq (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeFl4TcbExt _ _ _ _ _)

theorem nq_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : NQKE Kq (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeIrqControlInvocation _ _ _ _)

theorem nq_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : NQKE Kq (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeIrqHandlerInvocation _ _ _)

theorem nq_getScReleased (scPtr : ObjRef) : NQK Kq (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_getScReleased _)

theorem nq_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : NQKE Kq (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSchedContextBind _ _)

theorem nq_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : NQKE Kq (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSchedContextUnbindObject _ _)

theorem nq_decodeSchedContextYieldTo (scPtr : ObjRef) : NQKE Kq (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSchedContextYieldTo _)

theorem nq_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : NQKE Kq (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSchedContextInvocation _ _ _)

theorem nq_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : NQKE Kq (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSchedControlInvocationFlags _ _ _)

theorem nq_rangeCheck (v minV maxV : Word) : NQKE Kq (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_rangeCheck _ _ _)

theorem nq_decodeSetFlags (args : List Data) (cap : Cap) : NQKE Kq (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetFlags _ _)

theorem nq_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : NQKE Kq (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetIpcBuffer _ _ _ _)

theorem nq_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetMcpriority _ _ _ _)

theorem nq_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetPriority _ _ _ _)

theorem nq_isBlocked (thread : ObjRef) : NQK Kq (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_isBlocked _)

theorem nq_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : NQKE Kq (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeUpdateSc _ _ _)

theorem nq_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetSchedParams _ _ _ _)

theorem nq_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : NQKE Kq (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetSpace _ _ _ _)

theorem nq_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : NQKE Kq (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetTimeoutEp _ _ _)

theorem nq_decodeSetTlsBase (args : List Data) (cap : Cap) : NQKE Kq (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; nq_auto
macro_rules | `(tactic| nq_leaf) => `(tactic| with_reducible exact nq_decodeSetTlsBase _ _)
end

end Fl4Proofs.P3.SInv
