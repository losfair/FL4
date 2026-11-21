
/- vi1: generated frames `IK (VIT N S T b)` (sg1's SpecInvSgI3 renamed, the idle-relevant writers removed; see SpecInvViG1). -/
import Fl4Proofs.P3.SpecInvViG2
open Classical

namespace Fl4Proofs.P3.SInvI
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N S T : ObjRef} {b : Bool}

theorem vi_isRoundRobin (scPtr : ObjRef) : IK (VIT N S T b) (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isRoundRobin _)

theorem vi_getRefillHead (scPtr : ObjRef) : IK (VIT N S T b) (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getRefillHead _)

theorem vi_refillPopHead (scPtr : ObjRef) : IK (VIT N S T b) (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillPopHead _)

theorem vi_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : IK (VIT N S T b) (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateRefillHd _ _)

theorem vi_mergeOverlappingRefills (scPtr : ObjRef) : IK (VIT N S T b) (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_mergeOverlappingRefills _)

theorem vi_refillHeadOverlappingLoop (scPtr : ObjRef) : IK (VIT N S T b) (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillHeadOverlappingLoop _)

theorem vi_refillUnblockCheck (scPtr : ObjRef) : IK (VIT N S T b) (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_refillUnblockCheck _)

theorem vi_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : IK (VIT N S T b) (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_ifCondRefillUnblockCheck _ _ _)

theorem vi_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : IK (VIT N S T b) (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getSkObjRef _ _ _)

theorem vi_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : IK (VIT N S T b) (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_capSwap _ _ _ _)

theorem vi_capSwapForDelete (slot1 slot2 : CslotPtr) : IK (VIT N S T b) (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_capSwapForDelete _ _)

theorem vi_deletedIrqHandler (irq : Irq) : IK (VIT N S T b) (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_deletedIrqHandler _)

theorem vi_postCapDeletion (cap : Cap) : IK (VIT N S T b) (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_postCapDeletion _)

theorem vi_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : IK (VIT N S T b) (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_emptySlot _ _)

theorem vi_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : IK (VIT N S T b) (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getScObjRef _ _)

theorem vi_testReschedule (fromTptr : ObjRef) : IK (VIT N S T b) (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_testReschedule _)

theorem vi_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : IK (VIT N S T b) (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextMaybeUnbindNtfn _)

theorem vi_getIrqSlot (irq : Irq) : IK (VIT N S T b) (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getIrqSlot _)

theorem vi_prepareThreadDelete (threadPtr : ObjRef) : IK (VIT N S T b) (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_prepareThreadDelete _)

theorem vi_schedContextSetInactive (scPtr : ObjRef) : IK (VIT N S T b) (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextSetInactive _)

theorem vi_schedContextUnbindNtfn (scPtr : ObjRef) : IK (VIT N S T b) (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_schedContextUnbindNtfn _)

theorem vi_updateRestartPc (threadPtr : ObjRef) : IK (VIT N S T b) (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateRestartPc _)

theorem vi_getScActive (scPtr : ObjRef) : IK (VIT N S T b) (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getScActive _)

theorem vi_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IKE (VIT N S T b) f) (h_g : IKE (VIT N S T b) g) : IKE (VIT N S T b) (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; vi_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_orChoiceE _ _ _ ?_ ?_)

theorem vi_updateTimeStamp  : IK (VIT N S T b) (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_updateTimeStamp)

theorem vi_preemptionPoint  : IKE (VIT N S T b) (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_preemptionPoint)


theorem vi_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IKE (VIT N S T b) m) : IKE (VIT N S T b) (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; vi_auto
  all_goals first | exact h_m
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible refine vi_capFaultOnFailure _ _ _ ?_)

theorem vi_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : IK (VIT N S T b) (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_capMove _ _ _)


theorem vi_captransferFromWords (ptr : Word) : IK (VIT N S T b) (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_captransferFromWords _)

theorem vi_isValidTimeoutHandler (tptr : ObjRef) : IK (VIT N S T b) (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_isValidTimeoutHandler _)

theorem vi_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : IK (VIT N S T b) (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_makeArchFaultMsg _ _)

theorem vi_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : IK (VIT N S T b) (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_makeFaultMsg _ _)

theorem vi_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : IK (VIT N S T b) (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_doFaultTransfer _ _ _ _)

theorem vi_loadWordOffs (ptr : ObjRef) (offs : Nat) : IK (VIT N S T b) (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_loadWordOffs _ _)

theorem vi_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : IK (VIT N S T b) (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_copyMrs _ _ _ _ _)

theorem vi_getMessageInfo (thread : ObjRef) : IK (VIT N S T b) (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; vi_auto
macro_rules | `(tactic| vi_leaf) => `(tactic| with_reducible exact vi_getMessageInfo _)
end

end Fl4Proofs.P3.SInvI
