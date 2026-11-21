/-
P3 (DESIGN.md §9), invariant line G1 (rd14f): **rd8w's `SInvW` tops over
rd14f F's interface `ArmAKD`** (spec side only).

* `curSc_ne_idleSc` (vi3's `ValidIdle`: no TCB but the idle thread is bound to
  the idle SC; ct ≠ idle is bound to cur_sc by `CurScT`).
* **`qd_ofW`**: rd14f F's `QD C c σ` at a syscall entry from `SInvW σ` and
  rd14c's `InvRc C c σ` (T1 / EB true by ctq17's `evp_start` on the syscall's
  `SysF`, IdleScOutV / VfhAll from `EV10`); `qd_fip` the same at the FaultIP
  outcome (rd13a's `fip_evp`, rd15a's `fip_eo`).
* **`kcall_rdyOffD`** / **`kentry_rdyOffD`**: rd8w's `kcall_rdyOffW` /
  `kentry_rdyOffW` with `QR := QD C` (bridge rd14f F's `brR_kd`), so the only
  perform-arm input is `InvRc C` (PerfA outside `C`); `kcall_rdyOff14f` /
  `kentry_rdyOff14f` for today's covered set `C14f2`.
-/
import Fl4Proofs.P3.SpecInvRd14fG
open Classical

namespace Fl4Proofs.P3.SInvR.A14f
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19
open Fl4Proofs.P3.SInvR.B8w

noncomputable section

set_option maxHeartbeats 1000000

variable {σ : State Unit}

/-- cur_sc is not the idle SC when ct ≠ idle runs bound to it (vi3's `ValidIdle`). -/
theorem curSc_ne_idleSc (hv : SInvI.ValidIdle σ) (hE : A8.EF σ) : σ.curSc ≠ σ.idleSc := by
  obtain ⟨xt, hct, -⟩ := hE.ct
  have hb := hE.cs xt hct
  obtain ⟨-, -, -, -, -, h6⟩ := hv
  have ho := h6 σ.curThread _ hct
  intro e
  rw [e] at hb
  exact ho.2.1 hE.ni hb

/-- **rd14f F's `QD C c σ` at a syscall entry.** -/
theorem qd_ofW {C : Fl4Invocation → Prop} {ev : Event} (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (c : Syscall) (e : ev = .syscallEvent c)
    (hP : A14c.InvRc C c σ) : QD C c σ := by
  have hE := ef_ofW h (hev (by rw [e]; intro h; cases h))
  have hX10 := ev10_ofW h
  obtain ⟨hIu, hIL, hJ, -, -, -⟩ := sysF_ofW h hev c e
  have hσ := evp_start h.1.1.1.1.2.1 h.1.1.1.1.2.2.1 h.1.1.1.1.2.2.2 hX10.vi hX10.eo h.sb.1.2 hIu hIL hJ
  have hEB : SInvQ.EB true σ := hσ.1.1.1
  exact ⟨hP, curSc_ne_idleSc hX10.vi hE, SInvQ.tq_t1 hEB.1.1.1.1, hEB, hX10.isc, hX10.eo.vfh⟩

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across every kernel event** with `PerfA` asked only outside `C` (`ArmAKD C`). -/
theorem kcall_rdyOffD {C : Fl4Invocation → Prop} (hA : ArmAKD C) (hnd : numDomains = 1) (rep : Bool) (ev : Event)
    (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc C c σ) (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_kd hA) bF (fun c e => qd_ofW h hev c e (hP c e)) hF

/-- **`QD` at the FaultIP outcome.** -/
theorem qd_fip {C : Fl4Invocation → Prop} (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc C c w.2 → QD C c w.2 := by
  intro w hw hP
  have hE := ef_ofW h hct
  have hX10 := ev10_ofW h
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ h.sb hct).ctAct
  obtain ⟨hJ, hEF, -, hIu⟩ := sl_entryFacts c h.a.sl.1 (slE_of h.sb) ⟨x0, hx0, ha0⟩
    (fun _ => ctSc_of_curScT h.1.1.1.1.2.1.2.2.2)
  have hF := A13a.fip_evp h.1.1.1.1.2.1 h.1.1.1.1.2.2.1 h.1.1.1.1.2.2.2 hX10.vi hX10.eo h.sb.1.2
    (SInvAll.act_all (P := fun x => activeSt x.tcbState) ⟨x0, hx0, ha0⟩) hIu hJ.1.2.1 hJ w hw
  have hO := A15a.fip_eo hX10.eo hX10.isc w hw
  have hEB : SInvQ.EB true w.2 := hF.1.1.1.1
  have hc : cfS w.2 = cfS σ :=
    (by unfold fl4SyscallFaultIP; cfk_auto : CFK (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ w hw
  have ecs : w.2.curSc = σ.curSc := congrArg (fun p => p.2.1) hc
  have eis : w.2.idleSc = σ.idleSc := congrArg (fun p => p.2.2.2.2.1) hc
  refine ⟨hP, ?_, SInvQ.tq_t1 hEB.1.1.1.1, hEB, hO.2.1, hO.1.vfh⟩
  rw [ecs, eis]; exact curSc_ne_idleSc hX10.vi hE

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across the syscall entry** with `PerfA` asked only outside `C` (`ArmAKD C`). -/
theorem kentry_rdyOffD {C : Fl4Invocation → Prop} (hA : ArmAKD C) (hnd : numDomains = 1) (c : Syscall)
    (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc C c w.2 ∧ QF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffW hnd c h hct (brR_kd hA) bF fun w hw => ⟨qd_fip c h hct w hw (hW w hw).1, (hW w hw).2⟩

/-- **Today's tops**: `PerfA` asked only outside rd14f's covered set `C14f2`. -/
theorem kcall_rdyOff14f (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc C14f2 c σ) (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffD armAKD_c14f2 hnd rep ev h hev bF hP hF

theorem kentry_rdyOff14f (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    {QF : Syscall → State Unit → Prop} (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc C14f2 c w.2 ∧ QF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffD armAKD_c14f2 hnd c h hct bF hW

end

end Fl4Proofs.P3.SInvR.A14f
