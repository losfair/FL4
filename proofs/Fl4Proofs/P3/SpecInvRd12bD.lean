/-
P3 (DESIGN.md §9), invariant line G1 (rd12b, KENTRY-PLAN rd11a goal 2):
**per-arm `PerfA` instances** (spec side only; SpecInvRd12bC's obligation).

* `sv_invokeDomain` / `cfk_invokeDomain`: the Domain arm (set_domain with its
  dequeue / enqueue / reschedule, domain_set_start, the schedule configure)
  keeps every object's scheduler view and `cfS`.
* **`perfA_domain`**: `PerfA` for the Domain arm from `KP σ0 ∧ CB0` at the
  Restart state (SpecInvRd12bC's `kpc_restart`).
-/
import Fl4Proofs.P3.SpecInvRd12bC
open Classical

namespace Fl4Proofs.P3.SInvR.A12b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

theorem sv_fpuRelease (t : ObjRef) : SVK.SVM (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease switchLocalFpuOwner saveFpuState loadFpuState setX64CurrentFpuOwner
  sv_auto
  all_goals (unfold NonDet.maybeM; split <;> sv_auto)

macro "sv12_rest" : tactic => `(tactic| all_goals first
  | exact sv_fpuRelease _
  | (unfold threadSetDomain; refine SVK.sv_threadSet' _ ?_ _; intro _; rfl)
  | (unfold rescheduleRequired; sv_auto; done))

theorem sv_invokeDomain (d : DomainInvocation) : SVK.SVM (invokeDomain (Z := Unit) d) := by
  unfold invokeDomain; split
  · unfold invokeSetDomain archPrepareSetDomain setDomain; sv_auto; sv12_rest
  · unfold domainSetStart; sv_auto; sv12_rest
  · unfold domainScheduleConfigure; sv_auto; sv12_rest

theorem cfk_invokeDomain (d : DomainInvocation) : CFK (invokeDomain (Z := Unit) d) := by
  unfold invokeDomain; split
  · unfold invokeSetDomain archPrepareSetDomain setDomain; cfk_auto
    all_goals (unfold threadSetDomain; exact cfk_threadSet' _ _)
  · unfold domainSetStart; cfk_auto
  · unfold domainScheduleConfigure; cfk_auto

/-- **The Domain arm.** -/
theorem perfA_domain {σ0 s : State Unit} (bl call don : Bool) (d : DomainInvocation) (hK : A11.KP σ0 s)
    (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeDomain d) s :=
  perfA_svm (m := invokeDomain (Z := Unit) d) (fun _ => rfl) (sv_invokeDomain d) (cfk_invokeDomain d) hK hb

end

end Fl4Proofs.P3.SInvR.A12b
