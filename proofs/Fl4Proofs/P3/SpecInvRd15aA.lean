/-
P3 (DESIGN.md §9), invariant line G1 (rd15a, KENTRY-PLAN rd14a handoff 1-2):
**rd14a's `RecvTB` from carries: `Rdy` and `ScInv` at every first-phase
invocation outcome; tops `kcall_rdyOff8` / `kentry_rdyOff8`** (spec side only).

* **`rdy_first`**: `Rdy` at EVERY outcome of the first-phase
  `fl4HandleInvocationR` (fp = true, non-blocking, non-calling) after a `true`
  front, from rd8j's `front_facts` (EF, T1, EB true, IdleScOutV, VfhAll at the
  entry) and `rd_shellAt` with rd8j's pinned perform inputs `InvIn r true`
  (`PerfIn` at every `get_cap_reg` outcome).
* **`sc_first`**: `ScInv` at EVERY outcome of any `fl4HandleInvocationR` run
  from a state carrying ctq17's `EvP` (its `SH` gives `ScInv`, its `Js` gives
  sb2's `Rel σe`), by sb2's shell `sb_handleInvocationR` with `scGap`
  (EntryOK at the entry σe: ScInv, UtInv3, VfhAll, ScLive).
* `RecvTC rep c σ` (**the one pinned per-arm fact**): at every `ok`
  first-phase outcome, ct is a TCB not `BlkR` and rd8d's `RT ct`. No carried
  family gives ct's thread state or ct's SC readiness across the perform arms
  (rd14b may add `RT ct ∧ ¬BlkR ct` to `PerfA`'s ok outcomes).
* **`recvTB_of`**: `InvP1 ∧ RecvTC ⇒` rd14a's `RecvTB`.
* `fip_eo`: EntryOK and IdleScOutV at the FaultIP outcome.
* Tops **`kcall_rdyOff8` / `kentry_rdyOff8`**: rd14a's `*rdyOff7` with
  `RecvTB` replaced by `InvP1` (rd8j's PerfIn) and `RecvTC`.
-/
import Fl4Proofs.P3.SpecInvRd14aB
import Fl4Proofs.P3.SpecInvRd8jC
import Fl4Proofs.P3.SpecInvSbT
open Classical

namespace Fl4Proofs.P3.SInvR.A15a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.A11 Fl4Proofs.P3.SInvR.A12a
  Fl4Proofs.P3.SInvR.A13a Fl4Proofs.P3.SInvR.A14a

noncomputable section

set_option maxHeartbeats 1000000

/-- **rd8j's perform inputs at the first phase** of the given entry (`PerfIn`
at every `get_cap_reg` outcome after a `true` front, for the send half of
ReplyRecv / NBSendRecv / NBSendWait). -/
def InvP1 (c : Syscall) (σ : State Unit) : Prop :=
  ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ

/-- **The pinned per-arm fact**: at every `ok` first-phase invocation outcome
of the given entry, ct is a TCB not blocked on receive / notification / send
and rd8d's `RT ct` (bound ⇒ its SC active with a ready head). True in
reachable states (KENTRY-PLAN rd14a): the first phase is non-blocking, so ct
ends Running / Restart, or Inactive (it suspended itself); ct unbound
(passive server after reply_remove's donation, NBSendRecv's donation, SC
unbind / deletion) makes `RT` vacuous; ct still bound to cur_sc keeps its
ready head (rd11a's frame) or gets it back at cur_time (configure of cur_sc:
commit_time then refill_new / refill_update); a bind needs an unbound TCB.
l4v: `invoke_*_valid_sched` / `ct_active` after a non-blocking invocation. -/
def RecvTC (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ r cr, A12b.srArgs c = some (r, cr) →
    ∀ g ∈ (getCapReg (Z := Unit) r v.2).1,
      ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, t.1 = .ok () →
        (∃ x, t.2.kheap t.2.curThread = some (.tcb x) ∧ ∀ f, ¬ BlkR x.tcbState f) ∧
          B8d.RT t.2 t.2.curThread

/-- **`Rdy` at every first-phase invocation outcome** (module docstring). -/
theorem rdy_first {σ : State Unit} (hEF : A8.EF σ) (h1 : SInvQ.T1 σ) (hEB : SInvQ.EB true σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (rep : Bool) {r : Register}
    (hP : B8j.InvIn r true σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1) (ht : v.1 = true)
    {g : CapRef × State Unit} (hg : g ∈ (getCapReg (Z := Unit) r v.2).1) :
    ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep false false true true g.1).run g.2).1, Rdy t.2 := by
  obtain ⟨hRB, hRT, hO, hS, hF⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  exact B8j.rd_shellAt hRB hRT hO hS hF rep false false true true r hg (hP v hv ht g hg)

section P
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P12 Fl4Proofs.P3.SInvQ.P13
  Fl4Proofs.P3.SInvQ.P15 Fl4Proofs.P3.SInvQ.P17

/-- **`ScInv` at every invocation outcome** from ctq17's `EvP` (module docstring). -/
theorem sc_first {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef} {σe s : State Unit}
    (hEO : SInvB.EntryOK σe) (hs : EvP C N S I d Nq σe s) (rep calling blocking don fp : Bool) (cptr : CapRef) :
    ∀ t ∈ ((fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr).run s).1, SInvB.ScInv t.2 :=
  SInvB.sb_handleInvocationR SInvB.scGap rep calling blocking don fp cptr σe hEO s hs.1.2.1
    ⟨hs.2.2.2.1.2.2.2.2.2.1, hs.2.2.2.1.2.2.2.2.2.2⟩

/-- **rd14a's `RecvTB` from rd8j's perform inputs and the pinned `RecvTC`.** -/
theorem recvTB_of {rep : Bool} {c : Syscall} {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop}
    {Nq : Irq → ObjRef} {σe σ : State Unit} (hEF : A8.EF σ) (hσ : EvP C N S I d Nq σe σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (hEO : SInvB.EntryOK σe)
    (hP : InvP1 c σ) (hC : RecvTC rep c σ) : RecvTB rep c σ := by
  intro v hv ht r cr hc g hg t ht' hok
  have hg' : EvP C N S I d Nq σe g.2 := evp_getCapReg r v.2 (evp_front hσ hv ht) g hg
  have hEB : SInvQ.EB true σ := hσ.1.1.1
  obtain ⟨hT, hR⟩ := hC v hv ht r cr hc g hg t ht' hok
  exact ⟨rdy_first hEF (SInvQ.tq_t1 hEB.1.1.1.1) hEB hIO hV rep (hP r cr hc) hv ht hg t ht',
    sc_first hEO hg' rep false false true true g.1 t ht', hT, hR⟩

end P

/-! ## The tops -/

section Q
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

/-- EntryOK and IdleScOutV at the FaultIP outcome (rd13a's `fip_evp` preamble). -/
theorem fip_eo {σ : State Unit} (hEO : SInvB.EntryOK σ) (hI : SInvI.IdleScOutV σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      SInvB.EntryOK w.2 ∧ SInvU.IO (fun _ => w.2.idleSc) w.2 ∧ VfhAll w.2 := by
  intro w hw
  have hu : uV w.2 = uV σ := SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw
  have hf : (w.2.idleThread, w.2.idleSc, w.2.curThread) = (σ.idleThread, σ.idleSc, σ.curThread) :=
    fld_arch _ σ rfl w hw
  simp only [Prod.mk.injEq] at hf
  obtain ⟨-, fS, -⟩ := hf
  have hEO' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hEO hu
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    (vfh_fip σ hEO.vfh w hw)
  refine ⟨hEO', ?_, hEO'.vfh⟩
  show IrqOutV (fun _ => w.2.idleSc) (uV w.2)
  rw [hu, fS]; exact hI

set_option maxHeartbeats 4000000 in
/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd15a top): rd14a's
`kcall_rdyOff7` with `RecvTB` discharged up to rd8j's perform inputs (`hInv`:
`PerfIn` at the first phase) and the pinned per-arm fact `hC` (`RecvTC`: ct
a TCB, not BlkR, `RT ct` at the ok first-phase outcomes). Remaining named
hypotheses, pinned to the given entry's run: `hRdB` (rd8j), `hP` (`InvR`,
rd14b), `hInv` (`PerfIn`, rd8j), `hC` (`RecvTC`), `hRdF` (rd8j); the rest are
carried entry facts. -/
theorem kcall_rdyOff8 (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hInv : ∀ c, ev = .syscallEvent c → InvP1 c σ)
    (hC : ∀ c, ev = .syscallEvent c → RecvTC rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine A14a.kcall_rdyOff7 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB hP (fun c e => ?_) hRdF
  subst e
  obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS _ rfl
  exact recvTB_of (hEF (by intro h; cases h))
    (evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ)
    hX10.isc hX10.eo.vfh hX10.eo (hInv _ rfl) (hC _ rfl)

set_option maxHeartbeats 4000000 in
/-- **The syscall entry** (rd15a top): rd14a's `kentry_rdyOff7` with `RecvTB`
replaced by rd8j's first-phase `PerfIn` (`InvP1`) and the pinned `RecvTC`
at the FaultIP outcome. -/
theorem kentry_rdyOff8 (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ A12b.InvR c w.2 ∧ InvP1 c w.2 ∧ RecvTC rep c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A14a.kentry_rdyOff7 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    have hF := fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := fip_eo hX10.eo hX10.isc w hw
    ⟨(hW w hw).1, (hW w hw).2.1,
      recvTB_of (A8.ef_fip h w hw) hF.1 hO.2.1 hO.2.2 hO.1 (hW w hw).2.2.1 (hW w hw).2.2.2⟩

end Q

end

end Fl4Proofs.P3.SInvR.A15a
