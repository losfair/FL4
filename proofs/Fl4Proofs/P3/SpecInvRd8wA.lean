/-
P3 (DESIGN.md §9), invariant line G1 (rd8w, KENTRY-PLAN rd8v handoff 1 / 3):
**rd8v's `kcall_rdyOffV` / `kentry_rdyOffV` with only rd14c's covered-set inputs**
(spec side only, outside the JAtZ cone).

* **`b0_front`** (rd8l's body-start bundle `B0` across the front's `true`
  outcomes: `update_time_stamp`, then the read-only branch of
  `check_budget_restart`), **`b0_of`** (`B0` from the entry facts: BSA, sb2's
  `EntryOK`, IdleScOutV, CnDom, rd7's `CAx`, ct ≠ idle, ct not ipc-queued),
  **`b0_fip`** (`B0` across the FaultIP write);
* **`invInB_of r fp (B0 σ.idleSc σ) (EntryOK σ) : B8v.InvInB r fp σ`**: rd8v's
  Reply input from rd8l's `bsa_restart` (`SJ` at every shell start reached by
  the front and `get_cap_reg`, via rd8l's `b0_getCapReg`; `calling := true`
  so `SJ`'s donation clause is vacuous);
* **`BrR Q`** / **`BrF Q`** (a run-pinned input `Q` with its bridge, from rd8a's
  `EF`, to rd12b's `InvR` / rd14b's `InvF`), `brR_c` / `brF_c` (rd14c's `InvRc C` /
  `InvFc C` by `invR_ofC` / `invF_ofC`); rd14d's `ArmAK` / `ArmAKB` forms plug in
  by their `invR_ofK` / `invR_ofKB` the same way;
* **`kcall_rdyOffR`** / **`kentry_rdyOffR`**: rd8t's `kcall_rdyOffT` /
  `kentry_rdyOffT` taking `InvR` itself (no `invR_of` from `InvRo`);
* tops **`kcall_rdyOffX`** / **`kentry_rdyOffX`**: rd8v's tops without
  `hPs` / `hPr` (`invInB_of`, with `BSA σ` and `CnDom σ` at the entry, then rd8v's
  `invIn_of`), `RecvTC` by rd14c's `recvTC_of ∘ recvF_of` from `QF`, `InvR` from
  `QR`; the only perform-arm inputs are `QR` / `QF` with bridges.
-/
import Fl4Proofs.P3.SpecInvRd8vD
import Fl4Proofs.P3.SpecInvRd14cB
import Fl4Proofs.P3.SpecInvRd14cC
open Classical

namespace Fl4Proofs.P3.SInvR.B8w
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `B0` along the front, the FaultIP write, and from the entry facts -/

section B
open Fl4Proofs.P3.SInvR.B8l Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g
  Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k

/-- **rd8l's `B0` across the front's `true` outcomes** (`ba_fl4HandleEvent_sys`'s prefix). -/
theorem b0_front (I : ObjRef) {σ : State Unit} (h : B0 I σ) (hE : SInvB.EntryOK σ)
    {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1) (ht : v.1 = true) :
    B0 I v.2 ∧ v.2.curThread = σ.curThread := by
  obtain ⟨z1, hz1, hv'⟩ := hv
  rw [SInvB.checkBudgetRestart_true_eq hv' ht]
  have hE1 : SInvB.EntryOK z1.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_updateTimeStamp) hz1)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hz1)
    ((show SInvU.NK σ.interruptIrqNode (updateTimeStamp (Z := Unit)) from SInvU.nk_updateTimeStamp) σ rfl z1 hz1)
    ((show IK VfhAll (updateTimeStamp (Z := Unit)) by unfold updateTimeStamp; kh_auto) σ hE.vfh z1 hz1)
  obtain ⟨hk, hct⟩ := kc_updateTimeStamp σ.kheap σ.curThread σ.interruptIrqNode σ ⟨rfl, rfl⟩ z1 hz1
  have hcnb := cnb_heap hk ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [← hct] at hcnb
  exact ⟨⟨⟨ba_updateTimeStamp σ h.1.1 z1 hz1,
    SInvU.io_of_uk (fun _ => SInvU.uk_updateTimeStamp) σ h.1.2.1 z1 hz1,
    SInvL.isk_updateTimeStamp σ h.1.2.2 z1 hz1⟩, hE1.sc, hcnb.1,
    (show IK SInv.VfC (updateTimeStamp (Z := Unit)) by vfc_auto) σ h.2.2.2.1 z1 hz1, hcnb.2.1, hcnb.2.2⟩, hct⟩

/-- **`B0` from the entry facts** (`kcall_bsa`'s construction). -/
theorem b0_of {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ)
    (hCD : CnDom σ) (hA : CAx σ) (hni : σ.curThread ≠ σ.idleThread) (hNQ : NotQ σ.curThread σ) :
    B0 σ.idleSc σ := by
  obtain ⟨x, c', y, n, hx, hc, -, -⟩ := hA hni
  exact ⟨⟨hB, hO, rfl⟩, hE.sc, cba_of_actB (hA hni), ⟨(vfhV_iff σ).2 hE.vfh, hCD⟩, hNQ, ⟨x, c', hx, hc⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`B0` across the FaultIP write** (`kentry_bsa`'s construction). -/
theorem b0_fip {σ : State Unit} (h : B0 σ.idleSc σ) (hE : SInvB.EntryOK σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, B0 w.2.idleSc w.2 := by
  intro w hw
  have hE' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh w hw)
  have hz : A12b.KZ σ w.2 := (show A12b.KZK σ (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
    unfold fl4SyscallFaultIP; exact A12b.kz_asUser _ _) σ rfl w hw
  have hctw : w.2.curThread = σ.curThread := A12b.kz_curThread hz
  have hSV := svs_of_kz hz
  have hidle : w.2.idleSc = σ.idleSc := congrArg (fun x => x.2.2.2.2.1) (A12b.kz_parts hz).2.2.1
  refine ⟨⟨(show BAK (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; ba_auto) σ h.1.1 w hw, ?_, rfl⟩, hE'.sc, ?_,
    (show IK SInv.VfC (fl4SyscallFaultIP (Z := Unit) σ.curThread) by unfold fl4SyscallFaultIP; vfc_auto) σ
      h.2.2.2.1 w hw, ?_, ?_⟩
  · rw [hidle]; exact SInvU.io_of_uk (fun _ => SInvU.uk_fl4SyscallFaultIP _) σ h.1.2.1 w hw
  · rw [hctw]; exact cba_sv h.2.2.1 hSV
  · rw [hctw]; exact nq_kz hz h.2.2.2.2.1
  · rw [hctw]; exact bd_sv h.2.2.2.2.2 hSV

/-- **rd8v's `InvInB` (Reply's `BlockedScActive` at the perform) from `B0` and
sb2's `EntryOK` at the entry**: rd8l's `bsa_restart` at every shell start. -/
theorem invInB_of (r : Register) (fp : Bool) {σ : State Unit} (h : B0 σ.idleSc σ) (hE : SInvB.EntryOK σ) :
    B8v.InvInB r fp σ := by
  intro v hv ht g hg
  have h1 := (b0_front σ.idleSc h hE hv ht).1
  obtain ⟨h2, -⟩ := b0_getCapReg r σ.idleSc v.2 h1 g hg
  intro w0 hw0 a s b s' ha hb u hu
  have hJ : SJ g.2.curThread σ.idleSc (true = false ∧ true = true) g.2 :=
    ⟨h2.1, h2.2.1, h2.2.2.1, rfl, h2.2.2.2.1, fun hd => by cases hd.1⟩
  have hB := bsa_restart true true fp g.1 σ.idleSc g.2 hJ w0 hw0 a s b s' ha hb u hu
  cases b <;> first | exact hB | exact True.intro

end B

/-! ## The tops -/

section T
open Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- **A run-pinned perform-arm input with its bridge to rd12b's `InvR`** (any interface:
rd14c's `InvRc C` by `invR_ofC`, rd14d's `ArmAK` / `ArmAKB` forms by `invR_ofK` / `invR_ofKB`). -/
abbrev BrR (Q : Syscall → State Unit → Prop) : Prop := ∀ c σ, A8.EF σ → Q c σ → A12b.InvR c σ

/-- **A run-pinned first-phase input with its bridge to rd14b's `InvF`.** -/
abbrev BrF (Q : Syscall → State Unit → Prop) : Prop := ∀ c σ, A8.EF σ → Q c σ → A14b.InvF c σ

theorem brR_c {C : Fl4Invocation → Prop} (hA : A14c.ArmA C) : BrR (A14c.InvRc C) :=
  fun _ _ hE h => A14c.invR_ofC hA hE h

theorem brF_c {C : Fl4Invocation → Prop} (hA : A14c.ArmF C) : BrF (A14c.InvFc C) :=
  fun _ _ hE h => A14c.invF_ofC hA hE h

set_option maxHeartbeats 4000000 in
/-- **rd8t's `kcall_rdyOffT` with rd12b's `InvR` itself as the input** (no `invR_of`), so any
covered-set interface plugs in through its own bridge. -/
theorem kcall_rdyOffR (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRS : SInvQ.RS σ)
    (hPs : ∀ c, ev = .syscallEvent c → ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) →
      B8j.InvIn r false σ)
    (hPr : ∀ c, ev = .syscallEvent c → ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hC : ∀ c, ev = .syscallEvent c → A15a.RecvTC rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧
      EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ ∧ σ.curThread ≠ σ.idleThread := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    exact ⟨hEF (by intro h; cases h), evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ,
      ne_idle_of_active hX10.vi hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)⟩
  exact A14a.kcall_rdyOff7 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS
    (fun c e => B8t.rdBody_c hnd rep c σ (key c e).1 hX10.isc hX10.eo (key c e).2.1 (key c e).2.2 hRS
      (hS c e) (hPs c e) (hPr c e) (hC c e))
    hP
    (fun c e => A15a.recvTB_of (key c e).1 (key c e).2.1 hX10.isc hX10.eo.vfh hX10.eo (hPr c e) (hC c e))
    (fun _ hni => B8h.rd_handleFault ev σ (hEF hni) (SInvQ.tq_t1 hX.1.1.1))

set_option maxHeartbeats 4000000 in
/-- **rd8t's `kentry_rdyOffT` with `InvR` as the input.** -/
theorem kentry_rdyOffR (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : SInvU.IrqOutV (fun _ => I.1) (SInvU.uV σ))
    (hRS : SInvQ.RS σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false w.2) ∧
      (∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true w.2) ∧
      A15a.RecvTC rep c w.2 ∧ A12b.InvR c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A14a.kentry_rdyOff7 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := A13a.fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := A15a.fip_eo hX10.eo hX10.isc w hw
    have hS := B8t.fip_sys hRS hIu hIL hJ hE hI2 hI1 w hw
    have hw' := A8.ef_fip h w hw
    ⟨B8t.rdBody_c hnd rep c w.2 hw' hO.2.1 hO.1 hF.1 hF.2 hS.2 hS.1 (hW w hw).1 (hW w hw).2.1
        (hW w hw).2.2.1,
      (hW w hw).2.2.2,
      A15a.recvTB_of hw' hF.1 hO.2.1 hO.2.2 hO.1 (hW w hw).2.1 (hW w hw).2.2.1⟩

set_option maxHeartbeats 4000000 in
/-- **rd8v's `kcall_rdyOffV` without `hPs` / `hPr`, the perform-arm inputs abstract**:
`InvInB` by `invInB_of` (BSA and CnDom at the entry), then rd8v's `invIn_of`; `RecvTC`
from `QF` (bridge `BrF`, rd14c's `recvTC_of ∘ recvF_of`); `InvR` from `QR` (bridge `BrR`). -/
theorem kcall_rdyOffX (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRS : SInvQ.RS σ) (hVB : B8n.VB σ) (hUF : B8n.UF σ) (hB : B8g.BSA σ) (hCD : CnDom σ)
    {QR QF : Syscall → State Unit → Prop} (bR : BrR QR) (bF : BrF QF)
    (hP : ∀ c, ev = .syscallEvent c → QR c σ) (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have hE : ∀ c, ev = .syscallEvent c → A8.EF σ := fun c e => hEF (by rw [e]; intro h; cases h)
  have hB0 : ∀ c, ev = .syscallEvent c → B8l.B0 σ.idleSc σ := fun c e =>
    b0_of hB hX10.eo hX10.isc hCD (hE c e).ca (hE c e).ni fun x hx =>
      B8l.nq_st (ev := ev) (Or.inl ((ha x hx).resolve_right (by rw [e]; intro h; cases h)))
  have key : ∀ c, ev = .syscallEvent c → SInvQ.EB true σ ∧ SInvQ.T1 σ := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    have hσ := evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ
    have hEB : SInvQ.EB true σ := hσ.1.1.1
    exact ⟨hEB, SInvQ.tq_t1 hEB.1.1.1.1⟩
  exact kcall_rdyOffR hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRS
    (fun c e r _ _ _ _ => B8v.invIn_of r false (hE c e) (key c e).2 (key c e).1 hX10.isc hX10.eo.vfh hVB hUF
      (invInB_of r false (hB0 c e) hX10.eo))
    (fun c e r _ _ => B8v.invIn_of r true (hE c e) (key c e).2 (key c e).1 hX10.isc hX10.eo.vfh hVB hUF
      (invInB_of r true (hB0 c e) hX10.eo))
    (fun c e => A14c.recvTC_of (A14b.recvF_of rep (hE c e) (bF c σ (hE c e) (hF c e))))
    (fun c e => bR c σ (hE c e) (hP c e))

set_option maxHeartbeats 4000000 in
/-- **rd8v's `kentry_rdyOffV` without the `InvInB` inputs**, the perform-arm inputs abstract
(`QR` / `QF` at the FaultIP outcome). -/
theorem kentry_rdyOffX (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : SInvU.IrqOutV (fun _ => I.1) (SInvU.uV σ))
    (hRS : SInvQ.RS σ) (hVB : B8n.VB σ) (hUF : B8n.UF σ) (hB : B8g.BSA σ) (hCD : CnDom σ)
    {QR QF : Syscall → State Unit → Prop} (bR : BrR QR) (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, QR c w.2 ∧ QF c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  have hB0 : B8l.B0 σ.idleSc σ := b0_of hB hX10.eo hX10.isc hCD h.ca h.ni fun x hx =>
    B8l.nq_st (ev := .syscallEvent c) (Or.inl (ha x hx))
  kentry_rdyOffR hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 hRS fun w hw =>
    have hF := A13a.fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := A15a.fip_eo hX10.eo hX10.isc w hw
    have hw' := A8.ef_fip h w hw
    have hEB : SInvQ.EB true w.2 := hF.1.1.1.1
    have h1 : SInvQ.T1 w.2 := SInvQ.tq_t1 hEB.1.1.1.1
    have hVw : B8n.VB w.2 :=
      B8q.vb_ve.2 ((by unfold fl4SyscallFaultIP; ve_auto : B8q.VEK (fun _ => False)
        (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ (B8q.vb_ve.1 hVB) w hw)
    have hUw := B8v.uf_fip hUF w hw
    have hb := b0_fip hB0 hX10.eo w hw
    ⟨fun r _ _ _ _ => B8v.invIn_of r false hw' h1 hEB hO.2.1 hO.1.vfh hVw hUw (invInB_of r false hb hO.1),
      fun r _ _ => B8v.invIn_of r true hw' h1 hEB hO.2.1 hO.1.vfh hVw hUw (invInB_of r true hb hO.1),
      A14c.recvTC_of (A14b.recvF_of rep hw' (bF c w.2 hw' (hW w hw).2)),
      bR c w.2 hw' (hW w hw).1⟩

end T

end

end Fl4Proofs.P3.SInvR.B8w
