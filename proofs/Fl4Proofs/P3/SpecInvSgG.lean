/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, sg1): **`S N M` kept by the
cap-writing ancestors that need no decode fact** (ut7's generated SpecInvUtO3,
family `IK (P3 N)` prefix `un`, mechanically renamed to family `IK (S N M)` prefix
`sg`): deletion (`cap_revoke` by the least fixed point over `cap_delete`), IPC
incl. the cap transfer, faults, timeouts and budget, the TCB invocations, plus the
combinators with monadic parameters. Leaves (SpecInvSgA): the `UK` frames
(`s_of_uk`), `cap_delete_one`, `rec_del` / `cap_delete`, the TCB installs,
`do_normal_transfer`.
-/
import Fl4Proofs.P3.SpecInvSgA
open Classical

namespace Fl4Proofs.P3.SInvG
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N M : Irq → ObjRef}

syntax "sg_leaf" : tactic
macro_rules | `(tactic| sg_leaf) => `(tactic| fail "no sg_leaf")
macro_rules | `(tactic| sg_leaf) => `(tactic| (refine s_of_uk fun _ => ?_; uk_leaf; done))
macro_rules | `(tactic| sg_leaf) => `(tactic| (refine se_of_uk fun _ => ?_; uk_leaf; done))
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_capDeleteOne _)
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_recDel_cte _ _)
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_recDel_fin _ _)
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_capDelete _)
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_doNormalTransfer _ _ _ _ _ _ _)
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_installTcbCap _ _ _ _ (by decide))
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_checkCapAt_ins _ _ _ _ _ (by decide))

macro "sg_auto" : tactic => `(tactic| repeat' (first | sg_leaf | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem sg_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IKE (S N M) m) : IKE (S N M) (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_capFaultOnFailure _ _ _ ?_)

theorem sg_deletingIrqHandler (irq : Irq) : IK (S N M) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_deletingIrqHandler _)

theorem sg_finaliseCap (a0 : Cap) (a1 : Bool) : IK (S N M) (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_finaliseCap _ _)

theorem sg_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IKE (S N M) f) (h_g : IKE (S N M) g) : IKE (S N M) (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; sg_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_orChoiceE _ _ _ ?_ ?_)

theorem sg_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IK (S N M) m) : IKE (S N M) (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_withoutPreemption _ ?_)


/-- One step of `cap_revoke`, its recursive calls keeping `S N M`. -/
theorem sg_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (S N M) (f k)) (sl : CslotPtr) : IKE (S N M) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (S N M) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  sg_auto
  all_goals exact hrec' _

theorem sg_capRevoke (sl : CslotPtr) : IKE (S N M) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => sg_capRevokeF hf k) sl
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_capRevoke _)

theorem sg_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IKE (S N M) m) : IK (S N M) (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_emptyOnFailure _ ?_)

theorem sg_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : IKE (S N M) m) : IKE (S N M) (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_lookupErrorOnFailure _ _ ?_)

theorem sg_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IKE (S N M) m) : IKE (S N M) (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_unifyFailure _ ?_)

theorem sg_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IKE (S N M) m) : IK (S N M) (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; sg_auto
  all_goals first | exact h_m
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible refine sg_constOnFailure _ _ ?_)

theorem sg_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IK (S N M) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_doIpcTransfer _ _ _ _ _)

theorem sg_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IK (S N M) (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_sendIpc _ _ _ _ _ _ _ _)

theorem sg_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IK (S N M) (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_sendFaultIpc _ _ _ _)

theorem sg_handleTimeout (tptr : ObjRef) (ex : Fault) : IK (S N M) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_handleTimeout _ _)

theorem sg_endTimeslice (canTimeout : Bool) : IK (S N M) (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_endTimeslice _)

theorem sg_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IK (S N M) (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_chargeBudget _ _)

theorem sg_checkBudget  : IK (S N M) (checkBudget (Z := Unit)) := by
  unfold checkBudget; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_checkBudget)

theorem sg_checkBudgetRestart  : IK (S N M) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_checkBudgetRestart)

theorem sg_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IK (S N M) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_doReplyTransfer _ _ _)

theorem sg_handleFault (thread : ObjRef) (ex : Fault) : IK (S N M) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem sg_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IK (S N M) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_receiveIpc _ _ _ _)

theorem sg_handleRecv (isBlocking canReply : Bool) : IK (S N M) (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_handleRecv _ _)

theorem sg_handleYield  : IK (S N M) (handleYield (Z := Unit)) := by
  unfold handleYield; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_handleYield)

theorem sg_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : IKE (S N M) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_installTcbFrameCap _ _ _)

theorem sg_invokeTcb (a0 : TcbInvocation) : IKE (S N M) (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_invokeTcb _)

theorem sg_preemptionPath  : IK (S N M) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; sg_auto
macro_rules | `(tactic| sg_leaf) => `(tactic| with_reducible exact sg_preemptionPath)

end

end Fl4Proofs.P3.SInvG
