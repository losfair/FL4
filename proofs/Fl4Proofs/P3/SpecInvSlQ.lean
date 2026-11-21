/-
P3 (DESIGN.md §9), invariant line G1 (sl2): **ScLive and NtfnScB across the
interrupt and timer signals** (sl1 handoff 1; spec side only): `SLI` (SL,
NtfnScB, il2's `ILN`) is kept by `send_signal` (SpecInvSlS + il2's
`iln_sendSignal`), hence by the timer wake-ups (`fl4_awaken`: a chain of
signals), `handle_interrupt` and `maybe_handle_interrupt`.
-/
import Fl4Proofs.P3.SpecInvSlB
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

section Q
variable {I : ObjRef × ObjRef} {K L : List ObjRef}

theorem sli_ik {α : Type} {m : NonDet (State Unit) α} (h1 : SLK I K m) (h2 : NBK m) (h3 : ILK L m)
    (h4 : NQK [] m) : IK (SLI I K L) m :=
  fun σ h x hx => ⟨⟨h1 σ h.1.1 x hx, h2 σ h.1.2 x hx⟩, h3 σ h.2.1 x hx, h4 σ h.2.2 x hx⟩

theorem sli_sendSignal (n : ObjRef) (badge : Badge) : IK (SLI I K L) (sendSignal (Z := Unit) n badge) :=
  fun σ h x hx => ⟨sln_sendSignal n badge σ h x hx, iln_sendSignal n badge σ h.2 x hx⟩

theorem sli_fl4Awaken : IK (SLI I K L) (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact sli_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)

theorem sli_handleInterrupt (irq : Irq) : IK (SLI I K L) (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt
  split
  · exact sli_ik (by sl_auto) (by nb_auto) (by il_auto) (by nq_auto)
  · refine ik_bind (sli_ik (by sl_auto) (by nb_auto) (by il_auto) (by nq_auto)) fun st => ?_
    cases st <;> dsimp only
    case irqSignal =>
      refine ik_bind (sli_ik (by sl_auto) (by nb_auto) (il_getIrqSlot _) (nq_getIrqSlot _)) fun s => ?_
      refine ik_bind (sli_ik (by sl_auto) (by nb_auto) (by il_auto) (by nq_auto)) fun c => ?_
      refine ik_bind (ik_when _ (sli_sendSignal _ _)) fun _ => ?_
      exact ik_bind (sli_ik (by sl_auto) (by nb_auto) (il_archMaskIrqSignal _) (nq_archMaskIrqSignal _)) fun _ =>
        sli_ik (by sl_auto) (by nb_auto) (il_doMachineOp _) (nq_doMachineOp _)
    all_goals exact sli_ik (by sl_auto) (by nb_auto) (by il_auto) (by nq_auto)

theorem sli_maybeHandleInterrupt (inKernel : Bool) : IK (SLI I K L) (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt
  refine ik_bind (sli_ik (by sl_auto) (by nb_auto) (by il_auto) (by nq_auto)) fun o => ?_
  cases o
  · exact sli_ik (by sl_auto) (by nb_auto) il_handleSpuriousIrq nq_handleSpuriousIrq
  · exact sli_handleInterrupt _

end Q

end

end Fl4Proofs.P3.SInvL
