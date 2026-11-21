/-
P3 (DESIGN.md §9), invariant line G1 (rd8t, KENTRY-PLAN rd8r "Not done" and
rd8m handoff 1, 4, 5): **the syscall entry without `RdBody` / `PreR`, and one
pair of tops collecting the latest `rdyOff*` line** (spec side only, outside
the JAtZ cone).

* **`rcvIn_of`** (rd8m handoff 1): rd8m's `RcvIn` (`ScInv ∧ ct ¬BlkR ∧ RT ct`
  at the ok first-phase outcomes) from rd15a's pinned `RecvTC` (the last two
  conjuncts) and rd15a's `sc_first` (ScInv over the whole
  `fl4HandleInvocationR`, from ctq17's `EvP` and sb2's `EntryOK`). So the two
  pinned inputs `RcvIn` (rd8m) and `RecvTC` (rd15a) are one.
* **`rdBody_p` / `rdBody_c`**: rd9's `RdBody` from carried facts and the pinned
  inputs only: rd8m's `rdBody_all` with rd8r's `preR_of2` (its `JE` from
  `EvP`'s components, as `kcall_rdyOff6p`), `RcvIn` given (`_p`) or from
  `RecvTC` (`_c`).
* **`fip_sys`**: ctq's `SysF` and ctq20's `RS` at every FaultIP outcome
  (ctq19's `kentry_tq` preamble; `RS` by `ik_arch_fip`: an `as_user` leaves
  `scheduler_action` alone).
* **`kentry_rdyOff6p`** (goal 1): rd13a's `kentry_rdyOff6` with `RdBody` at
  the FaultIP outcomes discharged by `rdBody_p` there (rd8r's kcall analog;
  `fip_evp` gives `EvP` and ct ≠ idle, rd15a's `fip_eo` EntryOK / IdleScOutV /
  VfhAll, `fip_sys` SysF / RS, rd8a's `ef_fip` EF).
* **`kcall_rdyOffT` / `kentry_rdyOffT`** (goal 3, rd8m handoff 4 and 5): rd14a's
  `*rdyOff7` with `hRdB` by `rdBody_c`, `InvR` from rd14b's `InvRo`
  (`invR_of`), `RecvTB` by rd15a's `recvTB_of`, `RdF` by rd8h's
  `rd_handleFault` (EF, T1), `IdleScOutV` from `EV10.isc` (no separate
  input), `RS` as ctq20's `SInvQ.RS` (the second component of `SInvCR`).
  Named inputs left, all pinned to the given entry's run (none ∀-states, none
  [J]/[P]/[W]/[S]): rd8j's `InvIn` (send and first-phase), rd15a's `RecvTC`,
  rd14b's `InvRo`.
-/
import Fl4Proofs.P3.SpecInvRd8rS
import Fl4Proofs.P3.SpecInvRd15aA
import Fl4Proofs.P3.SpecInvRd14bD
import Fl4Proofs.P3.SpecInvRd8hF
open Classical

namespace Fl4Proofs.P3.SInvR.B8t
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `RcvIn` and `RdBody` -/

/-- **rd8m's `RcvIn` from rd15a's `RecvTC`** (ScInv by rd15a's `sc_first`). -/
theorem rcvIn_of {rep : Bool} {c : Syscall} {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop}
    {Nq : Irq → ObjRef} {σe σ : State Unit} (hEO : SInvB.EntryOK σe) (hσ : EvP C N S I d Nq σe σ)
    (hC : A15a.RecvTC rep c σ) : B8m.RcvIn rep c σ := by
  intro v hv ht r cr hc g hg t ht' hok
  have hg' : EvP C N S I d Nq σe g.2 := A13a.evp_getCapReg r v.2 (A13a.evp_front hσ hv ht) g hg
  obtain ⟨hT, hR⟩ := hC v hv ht r cr hc g hg t ht' hok
  exact ⟨A15a.sc_first hEO hg' rep false false true true g.1 t ht', hT, hR⟩

/-- **rd9's `RdBody` from carried facts, rd8j's `InvIn` and rd8m's `RcvIn`**:
`rdBody_all` with `preR_of2`. -/
theorem rdBody_p (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : A8.EF σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hE : SInvB.EntryOK σ)
    (hσ : EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ) (hCN : σ.curThread ≠ σ.idleThread)
    (hRS : SInvQ.RS σ) (hF : SysF I d Nq σ)
    (hPs : ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hRc : B8m.RcvIn rep c σ) : A9.RdBody rep c σ := by
  have hEB : SInvQ.EB true σ := hσ.1.1.1
  have h1 : SInvQ.T1 σ := SInvQ.tq_t1 hEB.1.1.1.1
  exact B8m.rdBody_all hnd rep c σ hEF h1 hEB hIO hE.vfh hσ hCN hRS hPs hPr
    (B8r.preR_of2 rep c σ hEF h1 hEB hIO hE.vfh hE hPs hPr hF ⟨hσ.2.2.2.1, hσ.1.1.1, hσ.1.1.2.2.1⟩) hRc

/-- **`RdBody` with `RecvTC`** in place of `RcvIn` (`rcvIn_of`). -/
theorem rdBody_c (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : A8.EF σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hE : SInvB.EntryOK σ)
    (hσ : EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ) (hCN : σ.curThread ≠ σ.idleThread)
    (hRS : SInvQ.RS σ) (hF : SysF I d Nq σ)
    (hPs : ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hC : A15a.RecvTC rep c σ) : A9.RdBody rep c σ :=
  rdBody_p hnd rep c σ hEF hIO hE hσ hCN hRS hF hPs hPr (rcvIn_of hE hσ hC)

/-! ## The FaultIP outcome -/

/-- **ctq's `SysF` and ctq20's `RS` at every FaultIP outcome** (ctq19's
`kentry_tq` preamble). -/
theorem fip_sys {σ : State Unit} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hRS : SInvQ.RS σ) (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ)
    (hJ : Js I σ.curThread d Nq σ σ) (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc)
    (hI1 : IrqOutV (fun _ => I.1) (uV σ)) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, SysF I d Nq w.2 ∧ SInvQ.RS w.2 := by
  intro w hw
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨-, fS, fC⟩ := hf
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
  have hRS' : SInvQ.RS w.2 :=
    ik_arch_fip (P := SInvQ.RS) (fun _ _ _ _ _ h => h) σ.curThread σ hRS w hw
  rw [← fC] at hIu' hIL' hJ'
  exact ⟨⟨hIu', hIL', js_rebase hJ', hE', by rw [fS]; exact hI2, by rw [hu]; exact hI1⟩, hRS'⟩

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **The syscall entry without `RdBody`** (goal 1): rd13a's `kentry_rdyOff6`
with `RdBody` at the FaultIP outcomes from `rdBody_p` (rd8r's `kcall_rdyOff6p`
analog). Pinned inputs at the FaultIP outcome: rd8j's `InvIn`, rd8m's `RcvIn`,
rd12b's `InvR`, rd13a's `RecvTA`; carried: ctq20's `RS`. -/
theorem kentry_rdyOff6p (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hRS : SInvQ.RS σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false w.2) ∧
      (∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true w.2) ∧
      B8m.RcvIn rep c w.2 ∧ A12b.InvR c w.2 ∧ A13a.RecvTA rep c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A13a.kentry_rdyOff6 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := A13a.fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := A15a.fip_eo hX10.eo hX10.isc w hw
    have hS := fip_sys hRS hIu hIL hJ hE hI2 hI1 w hw
    ⟨rdBody_p hnd rep c w.2 (A8.ef_fip h w hw) hO.2.1 hO.1 hF.1 hF.2 hS.2 hS.1 (hW w hw).1
        (hW w hw).2.1 (hW w hw).2.2.1,
      (hW w hw).2.2.2.1, (hW w hw).2.2.2.2⟩

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event, the latest line in one
statement** (goal 3): rd14a's `kcall_rdyOff7` with `RdBody` (`rdBody_c`),
`InvR` (rd14b's `invR_of` from `InvRo`), `RecvTB` (rd15a's `recvTB_of`) and
`RdF` (rd8h's `rd_handleFault`) discharged. Named inputs left, pinned to the
given entry's run: `hPs` / `hPr` (rd8j's `InvIn`: `PerfIn`), `hC` (rd15a's
`RecvTC`), `hP` (rd14b's `InvRo`). Carried entry facts: the rest, with
ctq20's `RS` (`SInvCR.2`) and `IdleScOutV` from `EV10`. -/
theorem kcall_rdyOffT (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
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
    (hP : ∀ c, ev = .syscallEvent c → A14b.InvRo c σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧
      EvP σ.curThread σ.idleThread σ.idleSc I d Nq σ σ ∧ σ.curThread ≠ σ.idleThread := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    exact ⟨hEF (by intro h; cases h), evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ,
      ne_idle_of_active hX10.vi hCX (fun x hx => (ha x hx).resolve_right fun e => by cases e)⟩
  exact A14a.kcall_rdyOff7 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS
    (fun c e => rdBody_c hnd rep c σ (key c e).1 hX10.isc hX10.eo (key c e).2.1 (key c e).2.2 hRS
      (hS c e) (hPs c e) (hPr c e) (hC c e))
    (fun c e => A14b.invR_of (key c e).1 (hP c e))
    (fun c e => A15a.recvTB_of (key c e).1 (key c e).2.1 hX10.isc hX10.eo.vfh hX10.eo (hPr c e) (hC c e))
    (fun _ hni => B8h.rd_handleFault ev σ (hEF hni) (SInvQ.tq_t1 hX.1.1.1))

set_option maxHeartbeats 4000000 in
/-- **The syscall entry, the latest line in one statement** (goal 3): rd14a's
`kentry_rdyOff7` with every FaultIP-outcome input but the pinned ones
discharged (as `kcall_rdyOffT`, at the FaultIP outcome). Named inputs left at
the FaultIP outcome: rd8j's `InvIn`, rd15a's `RecvTC`, rd14b's `InvRo`;
carried: ctq20's `RS`. -/
theorem kentry_rdyOffT (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hRS : SInvQ.RS σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false w.2) ∧
      (∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true w.2) ∧
      A15a.RecvTC rep c w.2 ∧ A14b.InvRo c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A14a.kentry_rdyOff7 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := A13a.fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := A15a.fip_eo hX10.eo hX10.isc w hw
    have hS := fip_sys hRS hIu hIL hJ hE hI2 hI1 w hw
    have hw' := A8.ef_fip h w hw
    ⟨rdBody_c hnd rep c w.2 hw' hO.2.1 hO.1 hF.1 hF.2 hS.2 hS.1 (hW w hw).1 (hW w hw).2.1
        (hW w hw).2.2.1,
      A14b.invR_of hw' (hW w hw).2.2.2,
      A15a.recvTB_of hw' hF.1 hO.2.1 hO.2.2 hO.1 (hW w hw).2.1 (hW w hw).2.2.1⟩

end

end Fl4Proofs.P3.SInvR.B8t
