/- sl5: `IK (KS σ0)` for the IPC, fault, timeout, budget and preemption paths of the syscall entry
(generated: SpecInvVfhG (proofs/scratch/vfh2/mkvfh.sh) with `VS σ0` replaced by `KS σ0` and `vfhg_` by `skg_`;
the leaves are SpecInvSlKA/KB: every cap these write goes through `do_normal_transfer`, `ks_doNormalTransfer`). -/
import Fl4Proofs.P3.SpecInvSlKB
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {σ0 : State Unit}

theorem skg_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IK (KS σ0) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_doIpcTransfer _ _ _ _ _)

theorem skg_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IK (KS σ0) (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_sendIpc _ _ _ _ _ _ _ _)

theorem skg_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IK (KS σ0) (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_sendFaultIpc _ _ _ _)

theorem skg_handleTimeout (tptr : ObjRef) (ex : Fault) : IK (KS σ0) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_handleTimeout _ _)

theorem skg_endTimeslice (canTimeout : Bool) : IK (KS σ0) (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_endTimeslice _)

theorem skg_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IK (KS σ0) (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_chargeBudget _ _)

theorem skg_checkBudget  : IK (KS σ0) (checkBudget (Z := Unit)) := by
  unfold checkBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_checkBudget)

theorem skg_checkBudgetRestart  : IK (KS σ0) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_checkBudgetRestart)

theorem skg_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IK (KS σ0) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_doReplyTransfer _ _ _)

theorem skg_handleFault (thread : ObjRef) (ex : Fault) : IK (KS σ0) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem skg_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IK (KS σ0) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_receiveIpc _ _ _ _)

theorem skg_handleRecv (isBlocking canReply : Bool) : IK (KS σ0) (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_handleRecv _ _)

theorem skg_handleYield  : IK (KS σ0) (handleYield (Z := Unit)) := by
  unfold handleYield; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_handleYield)

theorem skg_preemptionPath  : IK (KS σ0) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact skg_preemptionPath)

end

end Fl4Proofs.P3.SInvL
