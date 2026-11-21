/-
P3 (DESIGN.md §9), INV-PLAN §4 G1 assembly (g1a): **`ValidMachineTime` across
`fl4CallKernel` for every event** (spec side only; outside the `JAtZ` cone).

invB proved `GK` (every `WL` predicate kept) for the syscall and interrupt
events only (`gk_fl4CallKernel_sys` / `gk_fl4CallKernel_irq`). The fault events
(`unknownSyscall`, `userLevelFault`, `vmFaultEvent`, `hypervisorEvent`) are
`withoutPreemption (updateTimeStamp; checkBudgetRestart; when … handleFault …)`
over leaves that SpecInvValidMachineTimeGen already covers (`gk_updateTimeStamp`,
`gk_checkBudgetRestart`, `gk_handleFault`, the MTK fallback for
`handleVmFault` / `handleHypervisorFault`), so `gk_auto` composes them: no new
field proof.

* `gk_fl4HandleEvent_all`, `gk_fl4CallKernel_all` (every event).
* `kcall_validMachineTime rep ev`: no side condition.
-/
import Fl4Proofs.P3.SpecInvValidMachineTime

open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- The VM fault handler (not reached by the syscall / interrupt entries, so invB's
generator left it out): the fault address (an MTK leaf), a register read, a throw. -/
theorem gk_handleVmFault (thread : ObjRef) (ft : VMFaultType) : GKE (handleVmFault (Z := Unit) thread ft) := by
  cases ft <;> (unfold handleVmFault; gk_auto)

macro_rules | `(tactic| gk_leaf) => `(tactic| with_reducible apply gk_handleVmFault)

/-- FL4's `handle_event`, every event. -/
theorem gk_fl4HandleEvent_all (rep : Bool) (ev : Event) : GKE (fl4HandleEvent (Z := Unit) rep ev) := by
  cases ev with
  | syscallEvent c => exact gk_fl4HandleEvent_sys rep c
  | interrupt => exact gk_fl4HandleEvent_irq rep
  | _ => unfold fl4HandleEvent handleEvent; gk_auto

/-- FL4's `call_kernel`, every event. -/
theorem gk_fl4CallKernel_all (rep : Bool) (ev : Event) : GK (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  exact gk_bind (gke_handleE (gk_fl4HandleEvent_all rep ev) fun _ => gke_withoutPreemption gk_preemptionPath)
    fun _ => gk_bind gk_fl4Awaken fun _ => gk_bind gk_schedule fun _ => gk_activateThread

/-- **`ValidMachineTime` across every kernel event** (no side condition). -/
theorem kcall_validMachineTime (rep : Bool) (ev : Event) {σ : State Unit} (h : ValidMachineTime σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ValidMachineTime y.2 :=
  gk_fl4CallKernel_all rep ev _ wl_vmt σ h

end

end Fl4Proofs.P3.SInvAll
