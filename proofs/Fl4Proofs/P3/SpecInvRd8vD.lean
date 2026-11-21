/-
P3 (DESIGN.md §9), invariant line G1 (rd8v): **the UF / VB wiring of rd8j's `InvIn`** (KENTRY-PLAN
rd8n handoff 2, rd8s handoff 4; spec side only, outside the JAtZ cone).

rd8j's `InvIn r fp σ` (rd8n's Untyped / ASIDControl `Rdy`, DomainSet's `SR t`, Reply's
`BlockedScActive` at every Restart state of the shell's run from every front / `get_cap_reg`
outcome) is reduced to its Reply part `InvInB` (rd8n's `PerfInB` at those shell starts):

* `uts_idle` (update_time_stamp keeps the idle pointers), **`uf_front`** (rd8n's `UF` across the
  true front: the cap view by ut's `uk_updateTimeStamp`, `ScLiveT` by sl's `sl_updateTimeStamp`,
  check_budget_restart's true outcome is its read-only branch), **`uf_js`** (UF along rd8j's `JS`),
  **`vb_cap`** (VB from the entry to the shell start: rd8q's `VEK ⊥` family);
* **`invIn_of … (VB σ) (UF σ) (InvInB r fp σ) : InvIn r fp σ`** (rd8j's `front_facts` /
  `js_getCapReg` for RB / RdyT / OffReady / Suff, rd8n's `perfInN_of` / `perfIn_of`);
* tops **`kcall_rdyOffV`** / **`kentry_rdyOffV`**: rd8t's `kcall_rdyOffT` / `kentry_rdyOffT` with
  `VB ∧ UF` at the entry state (carried: rd8v's `kcall_vb`, ut8 / sl / sg) and `InvInB` in place
  of `InvIn` (`uf_fip`: UF across the FaultIP write).
-/
import Fl4Proofs.P3.SpecInvRd8vC
import Fl4Proofs.P3.SpecInvRd8tA
open Classical

namespace Fl4Proofs.P3.SInvR.B8v
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR
open Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

noncomputable section

set_option maxHeartbeats 1000000

/-! ## UF across the front and the lookups -/

open Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvV in
/-- `update_time_stamp` keeps the idle thread and the idle SC. -/
theorem uts_idle {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) :
    x.2.idleThread = σ.idleThread ∧ x.2.idleSc = σ.idleSc := by
  unfold updateTimeStamp at hx
  rw [sv_bind_gets, sv_bind_single (dmo_single (getCurrentTime_single σ.machineState))] at hx
  dsimp only at hx
  rw [sv_bind_pure, sv_bind_modify, sv_bind_modify, sv_bind_gets] at hx
  have key : ∀ {m : NonDet (State Unit) Unit} {s : State Unit},
      Vs.FK (fun s : State Unit => (s.idleThread, s.idleSc)) m → x ∈ (m s).1 →
        (x.2.idleThread, x.2.idleSc) = (s.idleThread, s.idleSc) :=
    fun hm h => hm _ _ h
  have e := key (by dk_auto0) hx
  simp only [Prod.mk.injEq] at e
  exact e

/-- **rd8n's `UF` across the true front** (update_time_stamp, then the read-only branch of
check_budget_restart). -/
theorem uf_front {σ : State Unit} (hF : B8n.UF σ) {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1)
    (ht : v.1 = true) : B8n.UF v.2 := by
  obtain ⟨w, hw, hv'⟩ := hv
  rw [SInvB.checkBudgetRestart_true_eq hv' ht]
  have hu : SInvU.uV w.2 = SInvU.uV σ :=
    (SInvU.uk_updateTimeStamp : SInvU.UK (SInvU.uV σ) (updateTimeStamp (Z := Unit))) σ rfl w hw
  obtain ⟨eit, eis⟩ := uts_idle hw
  obtain ⟨hU, hL, hI⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · show SInvU.UtInv''V _; rw [hu]; exact hU
  · rw [eit, eis]
    exact (SInvL.sl_updateTimeStamp (Iq := (σ.idleThread, σ.idleSc)) (Kq := []) σ
      ⟨hL, fun _ h => by simp at h⟩ w hw).1
  · show SInvU.IrqOutV (fun _ => w.2.idleThread) (SInvU.uV w.2)
    rw [hu, eit]; exact hI

/-- **`UF` along rd8j's `JS`** (rd8n's `uf_restart` without the Restart write). -/
theorem uf_js {C I : ObjRef} {σ s' : State Unit} (hF : B8n.UF σ) (hJ : B8j.JS C I σ s') : B8n.UF s' := by
  obtain ⟨hz, hv, -⟩ := hJ
  have hc : cfS s' = cfS σ := B8j.kz_cfS hz
  have eit : s'.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) hc
  have eis : s'.idleSc = σ.idleSc := congrArg (fun p => p.2.2.2.2.1) hc
  obtain ⟨hU, hL, hI⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · show SInvU.UtInv''V _; rw [hv]; exact hU
  · rw [eit, eis]; exact B8n.scLiveT_kz hL hz hv
  · show SInvU.IrqOutV (fun _ => s'.idleThread) (SInvU.uV s')
    rw [hv, eit]; exact hI

/-- **`VB` from the entry to the shell start** (the front and `get_cap_reg`). -/
theorem vb_cap {σ : State Unit} (hV : B8n.VB σ) {r : Register} {v : Bool × State Unit} (hv : v ∈ (A8.front σ).1)
    {g : CapRef × State Unit} (hg : g ∈ (getCapReg (Z := Unit) r v.2).1) : B8n.VB g.2 :=
  B8q.vb_ve.2 ((by ve_auto : B8q.VEK (fun _ => False) (getCapReg (Z := Unit) r)) v.2
    ((by ve_auto : B8q.VEK (fun _ => False) (A8.front)) σ (B8q.vb_ve.1 hV) v hv) g hg)

/-! ## `InvIn` reduced to its Reply part -/

/-- **The Reply part of rd8j's `InvIn`** (rd8n's `PerfInB`, pinned to the entry's run). -/
def InvInB (r : Register) (fp : Bool) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ g ∈ (getCapReg (Z := Unit) r v.2).1, B8n.PerfInB fp g.1 g.2

/-- **rd8j's `InvIn` from `VB`, `UF` and its Reply part.** -/
theorem invIn_of (r : Register) (fp : Bool) {σ : State Unit} (hEF : A8.EF σ) (h1 : SInvQ.T1 σ)
    (hEB : SInvQ.EB true σ) (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : VfhAll σ) (hVB : B8n.VB σ)
    (hUF : B8n.UF σ) (hB : InvInB r fp σ) : B8j.InvIn r fp σ := by
  intro v hv ht g hg
  obtain ⟨hRB, hRT, hO, hS, -⟩ := B8j.front_facts hEF h1 hEB hIO hV hv ht
  have hJ : B8j.JS v.2.curThread σ.idleSc v.2 g.2 := B8j.js_getCapReg r v.2 ⟨rfl, rfl, hRB⟩ g hg
  have ect : g.2.curThread = v.2.curThread := A12b.kz_curThread hJ.1
  have hS1 := B8j.svs_kz hJ.1
  have hc1 := B8j.kz_cfS hJ.1
  have hRB' : B8f.RB g.2.curThread σ.idleSc g.2 := by rw [ect]; exact hJ.2.2
  exact B8n.perfIn_of fp g.1 σ.idleSc g.2 hRB' (uf_js (uf_front hUF hv ht) hJ)
    (B8n.perfInN_of fp g.1 σ.idleSc g.2 hRB' (by rw [ect]; exact rdyT_svs hRT hS1)
      (B8j.offReady_svcf hO hS1 hc1) (B8j.suff_svcf hS hS1 hc1) (vb_cap hVB hv hg) (hB v hv ht g hg))

/-! ## Tops -/

/-- **rd8t's `kcall_rdyOffT` with rd8j's `InvIn` reduced to `InvInB`**: `VB` and rd8n's `UF` are
carried facts at the entry state. -/
theorem kcall_rdyOffV (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRS : SInvQ.RS σ) (hVB : B8n.VB σ) (hUF : B8n.UF σ)
    (hPs : ∀ c, ev = .syscallEvent c → ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → InvInB r false σ)
    (hPr : ∀ c, ev = .syscallEvent c → ∀ r cr, A12b.srArgs c = some (r, cr) → InvInB r true σ)
    (hC : ∀ c, ev = .syscallEvent c → A15a.RecvTC rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A14b.InvRo c σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have key : ∀ c, ev = .syscallEvent c → A8.EF σ ∧ SInvQ.EB true σ ∧ SInvQ.T1 σ := by
    intro c e
    subst e
    obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS c rfl
    have hσ := SInvQ.P17.evp_start hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ
    have hEB : SInvQ.EB true σ := hσ.1.1.1
    exact ⟨hEF (by intro h; cases h), hEB, SInvQ.tq_t1 hEB.1.1.1.1⟩
  exact B8t.kcall_rdyOffT hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRS
    (fun c e r cl bl dn hc => invIn_of r false (key c e).1 (key c e).2.2 (key c e).2.1 hX10.isc hX10.eo.vfh
      hVB hUF (hPs c e r cl bl dn hc))
    (fun c e r cr hc => invIn_of r true (key c e).1 (key c e).2.2 (key c e).2.1 hX10.isc hX10.eo.vfh
      hVB hUF (hPr c e r cr hc))
    hC hP

/-- `UF` across the FaultIP write (one TCB's registers). -/
theorem uf_fip {σ : State Unit} (hF : B8n.UF σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, B8n.UF w.2 := by
  intro w hw
  have hu : SInvU.uV w.2 = SInvU.uV σ :=
    (by unfold fl4SyscallFaultIP; uk_auto : SInvU.UK (SInvU.uV σ) (fl4SyscallFaultIP (Z := Unit) σ.curThread))
      σ rfl w hw
  have hc : cfS w.2 = cfS σ := (by unfold fl4SyscallFaultIP; cfk_auto : CFK (fl4SyscallFaultIP (Z := Unit) σ.curThread))
    σ w hw
  have eit : w.2.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) hc
  have eis : w.2.idleSc = σ.idleSc := congrArg (fun p => p.2.2.2.2.1) hc
  obtain ⟨hU, hL, hI⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · show SInvU.UtInv''V _; rw [hu]; exact hU
  · rw [eit, eis]
    exact ((by unfold fl4SyscallFaultIP; sl_auto :
      SInvL.SLK (σ.idleThread, σ.idleSc) [] (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ
      ⟨hL, fun _ h => by simp at h⟩ w hw).1
  · show SInvU.IrqOutV (fun _ => w.2.idleThread) (SInvU.uV w.2)
    rw [hu, eit]; exact hI

/-- **rd8t's `kentry_rdyOffT` with rd8j's `InvIn` reduced to `InvInB`** (`VB` and `UF` at the
entry state; `InvInB` at every FaultIP outcome). -/
theorem kentry_rdyOffV (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : SInvU.IrqOutV (fun _ => I.1) (SInvU.uV σ))
    (hRS : SInvQ.RS σ) (hVB : B8n.VB σ) (hUF : B8n.UF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      (∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → InvInB r false w.2) ∧
      (∀ r cr, A12b.srArgs c = some (r, cr) → InvInB r true w.2) ∧
      A15a.RecvTC rep c w.2 ∧ A14b.InvRo c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  B8t.kentry_rdyOffT hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 hRS fun w hw =>
    have hF := A13a.fip_evp (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX ha hIu hIL hJ w hw
    have hO := A15a.fip_eo hX10.eo hX10.isc w hw
    have hw' := A8.ef_fip h w hw
    have hEB : SInvQ.EB true w.2 := hF.1.1.1.1
    have h1 : SInvQ.T1 w.2 := SInvQ.tq_t1 hEB.1.1.1.1
    have hVw : B8n.VB w.2 :=
      B8q.vb_ve.2 ((by unfold fl4SyscallFaultIP; ve_auto : B8q.VEK (fun _ => False)
        (fl4SyscallFaultIP (Z := Unit) σ.curThread)) σ (B8q.vb_ve.1 hVB) w hw)
    have hUw := uf_fip hUF w hw
    ⟨fun r cl bl dn hc => invIn_of r false hw' h1 hEB hO.2.1 hO.1.vfh hVw hUw ((hW w hw).1 r cl bl dn hc),
      fun r cr hc => invIn_of r true hw' h1 hEB hO.2.1 hO.1.vfh hVw hUw ((hW w hw).2.1 r cr hc),
      (hW w hw).2.2.1, (hW w hw).2.2.2⟩

end

end Fl4Proofs.P3.SInvR.B8v
