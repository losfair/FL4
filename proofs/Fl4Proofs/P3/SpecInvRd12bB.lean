/-
P3 (DESIGN.md §9), invariant line G1 (rd12b, KENTRY-PLAN rd11a goal 2):
**`OsBody` for the invocation syscalls and the tops** (spec side only).

* `ebx_fip`: rd11b's `sq4_fip` returning the whole EBX (ctq's `CB` and `NQ []`
  at every event-part outcome from the FaultIP state).
* `ev_of_body`: a body outcome after a `true` front is an event-part outcome.
* **`osBody_inv`**: `OsBody` from EBX at the event part and `CB → SS4` at the
  body outcomes.
* `InvP c σ` (the per-arm obligation `PerfH` of SpecInvRd12bA at the shell's
  run from every `true` front outcome: rd12b's open part), `RecvT rep c σ`
  (rd12a's receive tail after the send half: `RecvQ`), `RecvC c` (the four
  receive syscalls).
* **`osBody4`**: `OsBody` for every syscall other than Yield from EBX,
  `InvP`, `RecvT`, and (receive syscalls only) rd12a's `OsBody`.
* Tops **`kcall_rdyOff4` / `kentry_rdyOff4`**: rd11b's `kcall_rdyOff3j` /
  `kentry_rdyOff3j` with `hOsB` discharged for the six invocation syscalls
  (`osq_send` / `osq_sendHalf`), modulo `InvP` / `RecvT`; the receive
  syscalls' `OsBody` kept as rd12a's named hypothesis.
-/
import Fl4Proofs.P3.SpecInvRd12bA
open Classical

namespace Fl4Proofs.P3.SInvR.A12b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Body outcomes are event-part outcomes -/

/-- A body outcome after a `true` front is an outcome of the event part. -/
theorem ev_of_body {rep : Bool} {c : Syscall} {σ : State Unit} {v : Bool × State Unit}
    {y : Except Unit Unit × State Unit} (hv : v ∈ (A8.front σ).1) (ht : v.1 = true)
    (hy : y ∈ (A8.bodyRun rep c v.2).1) : y ∈ (A8.evRun rep (.syscallEvent c) σ).1 := by
  obtain ⟨w, hw, hv2⟩ := hv
  obtain ⟨b, s⟩ := v
  simp only at ht; subst ht
  dsimp only [A8.bodyRun] at hy
  dsimp only [A8.evRun]
  unfold NonDetE.handleE at hy ⊢
  rw [ExceptT.run_mk] at hy ⊢
  obtain ⟨z, hz, hy⟩ := hy
  refine ⟨z, ?_, hy⟩
  simp only [fl4HandleEvent]
  refine mem_bindE_ok (mem_liftE hw) (mem_bindE_ok (mem_liftE hv2) ?_)
  unfold NonDetE.whenE
  rw [if_pos rfl]
  exact hz

/-- **`OsBody` from EBX and `CB → SS4` at the body outcomes.** -/
theorem osBody_inv (rep : Bool) (c : Syscall) {σ : State Unit} {N S : ObjRef}
    (hE : ∀ y ∈ (A8.evRun rep (.syscallEvent c) σ).1, EBX N S false y.2)
    (hQ : ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1, CB y.2 → A10.SS4 y.2) :
    A9.OsBody rep c σ := by
  intro v hv ht y hy
  obtain ⟨hE1, hN1, -⟩ := hE y (ev_of_body hv ht hy)
  have h := hQ v hv ht y hy hE1.2.2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hN1⟩

/-! ## The pinned obligations -/

/-- **rd12b's open part**: the per-arm obligation `PerfH` at the shell's run
from every `true` front outcome (send syscalls and the send half). -/
def InvP (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true →
    (∀ r cl bl dn, sendArgs c = some (r, cl, bl, dn) →
      ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfH cl bl dn false g.1 g.2) ∧
    (∀ r cr, srArgs c = some (r, cr) → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, PerfH false false true true g.1 g.2)

/-- **rd12a's receive tail** after the send half, at every `true` front outcome. -/
def RecvT (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, srArgs c = some (r, cr) → RecvQ rep r cr v.2

/-- The four receive syscalls (rd12a's line). -/
def RecvC (c : Syscall) : Prop := c = .sysRecv ∨ c = .sysWait ∨ c = .sysNBWait ∨ c = .sysNBRecv

/-- **`OsBody` for every syscall other than Yield**: the six invocation
syscalls by `osq_send` / `osq_sendHalf`, the receive syscalls by rd12a's. -/
theorem osBody4 (rep : Bool) (c : Syscall) {σ : State Unit} {N S : ObjRef} (hEF : A8.EF σ)
    (hE : ∀ y ∈ (A8.evRun rep (.syscallEvent c) σ).1, EBX N S false y.2)
    (hP : InvP c σ) (hRT : RecvT rep c σ) (hOsR : RecvC c → A9.OsBody rep c σ) (hy : c ≠ .sysYield) :
    A9.OsBody rep c σ := by
  by_cases hr : RecvC c
  · exact hOsR hr
  refine osBody_inv rep c hE fun v hv ht => ?_
  obtain ⟨hB, hS⟩ := A10.bs_front hEF hv ht
  cases c <;> first
    | exact osq_send hB hS rep _ rfl ((hP v hv ht).1 _ _ _ _ rfl)
    | exact osq_sendHalf hB hS rep _ rfl ((hP v hv ht).2 _ _ rfl) (hRT v hv ht _ _ rfl)
    | exact absurd rfl hy
    | exact absurd (by simp [RecvC]) hr

/-! ## EBX at the FaultIP state -/

section Q
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

set_option maxHeartbeats 8000000 in
/-- rd11b's `sq4_fip` returning ctq's whole EBX. -/
theorem ebx_fip (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit}
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hV : SInvI.ValidIdle σ) (hEO : SInvB.EntryOK σ)
    (hCX : SInvAll.CtExit σ) (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hO : SInvG.IdleOutV σ) (hI : SInvI.IdleScOutV σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, EBX w.2.idleThread w.2.idleSc false y.2 := by
  intro w hw y hy
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨fN, fS, fC⟩ := hf
  have hX' : SInvQ.EX w.2 :=
    ⟨⟨tq_fl4SyscallFaultIP _ σ hX.1.1 w hw, sa_fl4SyscallFaultIP _ σ hX.1.2 w hw⟩,
      ctQ_arch σ hX.2.1 w hw, simple_arch σ hX.2.2.1 w hw, curScT_fip σ hX.2.2.2 w hw⟩
  have hR' : RB w.2 := rb_fl4SyscallFaultIP _ σ hR w hw
  have h4' : T4 w.2 := q4_fl4SyscallFaultIP _ σ h4 w hw
  have hV' : SInvI.ValidIdle w.2 := by
    have h := SInvI.vi_fl4SyscallFaultIP (N := σ.idleThread) (S := σ.idleSc) (T := σ.idleThread) (b := false)
      σ.curThread σ hV w hw
    unfold SInvI.ValidIdle; rw [fN, fS]; exact h
  have hEO' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hEO hu
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    (vfh_fip σ hEO.vfh w hw)
  have hCX' : SInvAll.CtExit w.2 := ctExit_arch σ hCX w hw
  have ha' := act_arch σ ha w hw
  have hIu' : Iu σ.curThread w.2 :=
    (show IK (Iu σ.curThread) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by iu_auto) σ hIu w hw
  have hIL' : IL [σ.curThread] w.2 := il_fl4SyscallFaultIP _ σ hIL w hw
  have hJ' : Js I σ.curThread d Nq σ w.2 :=
    (show IK (Js I σ.curThread d Nq σ) (fl4SyscallFaultIP (Z := Unit) σ.curThread) by js_auto) σ hJ w hw
  have hE' : EF Nq w.2 := by
    refine ⟨?_, ?_, ?_, vfh_fip σ hE.2.2.2 w hw⟩
    · show P3V Nq (uV w.2); rw [hu]; exact hE.1
    · show ScKindV (uV w.2); rw [hu]; exact hE.2.1
    · show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hE.2.2.1
  rw [← fC] at hIu' hIL' hJ'
  exact (A11b.ebx_sys hnd rep c hX' hR' h4' hV' hEO' hCX' ha' hIu' hIL' (js_rebase hJ') hE'
    (by rw [fS]; exact hI2) (by rw [hu]; exact hI1)
    (by show IrqOutV (fun _ => w.2.idleThread) (uV w.2); rw [hu, fN]; exact hO)
    (by show IrqOutV (fun _ => w.2.idleSc) (uV w.2); rw [hu, fS]; exact hI)
    (fun _ => ctSc_of_curScT hX'.2.2.2) y hy)

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd12b top): rd11b's
`kcall_rdyOff3j` with `hOsB` discharged for the six invocation syscalls.
Remaining named hypotheses (pinned to the given entry's outcomes): `hRdB`
(rd8e/f / rd8h), `hRdF` (rd8e/f), `hP` (`InvP`: the per-arm obligation of
the invocation perform, rd12b's open part), `hRT` (`RecvT`: rd12a's receive
tail after the send half), `hOsR` (rd12a's `OsBody` for the four receive
syscalls); the rest carried entry facts. -/
theorem kcall_rdyOff4 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → InvP c σ)
    (hRT : ∀ c, ev = .syscallEvent c → RecvT rep c σ)
    (hOsR : ∀ c, ev = .syscallEvent c → RecvC c → A9.OsBody rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A11b.kcall_rdyOff3j hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB
    (fun c e hy => by
      subst e
      obtain ⟨hIu, hIL, hJ, hE, hI2, hI1⟩ := hS c rfl
      exact osBody4 rep c (hEF (by intro h; cases h))
        (A11b.ebx_sys hnd rep c hX hR h4 hX10.vi hX10.eo hCX
          (fun x hx => (ha x hx).resolve_right fun e => by cases e)
          hIu hIL hJ hE hI2 hI1 hX10.io hX10.isc (fun _ => ctSc_of_curScT hX.2.2.2))
        (hP c rfl) (hRT c rfl) (hOsR c rfl) hy)
    hRdF

set_option maxHeartbeats 4000000 in
/-- **The syscall entry** (rd12b top): rd11b's `kentry_rdyOff3j` with the
invocation syscalls' `OsBody` discharged; `hW` keeps rd8e/f's `RdBody`, this
line's `InvP`, rd12a's `RecvT` and receive `OsBody` at the FaultIP outcome. -/
theorem kentry_rdyOff4 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ InvP c w.2 ∧ RecvT rep c w.2 ∧ (RecvC c → A9.OsBody rep c w.2)) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A11b.kentry_rdyOff3j hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, fun hy => osBody4 rep c (A8.ef_fip h w hw)
      (ebx_fip hnd rep c hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ hE hI2 hI1 hX10.io hX10.isc w hw)
      (hW w hw).2.1 (hW w hw).2.2.1 (hW w hw).2.2.2 hy⟩

end Q

end

end Fl4Proofs.P3.SInvR.A12b
