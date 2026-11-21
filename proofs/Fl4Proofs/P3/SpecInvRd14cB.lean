/-
P3 (DESIGN.md §9), invariant line G1 (rd14c, KENTRY-PLAN rd14b handoff 3):
**the bridges from rd14b's first-phase fact `FPO` to the consumers' pinned
inputs** (spec side only, outside the JAtZ cone).

* **`recvTC_of`**: rd14b's `RecvF` gives rd15a's `RecvTC` (its first half);
  **`rcvIn_of`**: with rd15a's `sc_first`, rd8m's `RcvIn`.
* rd8l's `RR` (`RP` of the ReplyRecv-type arm) is asked by rd8l's shells at
  EVERY `update_time_stamp` outcome, but the body runs only on the front's
  `true` outcomes, where `check_budget_restart` left the state unchanged
  (sb2's `checkBudgetRestart_true_eq`). The getCapReg adaptation: rd8l's
  `ba_fl4HandleEvent_sysF` / `ba_fl4CallKernelF` / `kcall_bsa` / `kentry_bsa`
  restated with `RRF rep c σ` (`RR` at the front's `true` outcomes only), same
  proofs (**`ba_fl4HandleEvent_sysF`**, **`ba_fl4CallKernelF`**,
  **`kcall_bsaF`**, **`kentry_bsaF`**), and **`rrF_of`** (`RecvF ⇒ RRF`).
* Tops with `InvF` (rd14b's per-arm first-phase obligation) in place of the
  pinned inputs: **`kcall_rdyOff8f`** / **`kentry_rdyOff8f`** (rd15a's
  `hC : RecvTC` gone), **`kcall_rdyOff6f`** (rd8m's `hRc : RcvIn` gone),
  **`kcall_bsaI`** / **`kentry_bsaI`**, **`kcall_sinvCRBI`** /
  **`kentry_sinvCRBI`** (rd8l's `RR` gone).
-/
import Fl4Proofs.P3.SpecInvRd14bE
import Fl4Proofs.P3.SpecInvRd15aA
import Fl4Proofs.P3.SpecInvRd8mE
import Fl4Proofs.P3.SpecInvRd8lD
open Classical

namespace Fl4Proofs.P3.SInvR.A14c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
open Fl4Proofs.P3.SInvR.B8l Fl4Proofs.P3.SInvR.B8c Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g
  Fl4Proofs.P3.SInvR.B8i Fl4Proofs.P3.SInvR.B8k Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvE Fl4Proofs.P3.SInvB

noncomputable section

set_option maxHeartbeats 1000000

/-! ## rd8l's shells with `RR` at the front's `true` outcomes -/

/-- rd8l's `RR` at the front's `true` outcomes only. -/
def RRF (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → RR rep v.2 c

/-- **The syscall event** from `B0` and sb2's `EntryOK` at its start. -/
theorem ba_fl4HandleEvent_sysF (rep : Bool) (c : Syscall) (I : ObjRef) (σ : State Unit) (h : B0 I σ)
    (hE : SInvB.EntryOK σ) (hR : RRF rep c σ) :
    ∀ y ∈ ((fl4HandleEvent (Z := Unit) rep (.syscallEvent c)).run σ).1, BSA y.2 := by
  simp only [fl4HandleEvent]
  intro y hy
  obtain ⟨z, hz, ⟨u, -, hy⟩ | ⟨e, he0, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz; cases he0
  obtain ⟨z1, hz1, rfl⟩ := SInvU.mem_liftE' hz
  have hE1 : SInvB.EntryOK z1.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_updateTimeStamp) hz1)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hz1)
    ((show SInvU.NK σ.interruptIrqNode (updateTimeStamp (Z := Unit)) from SInvU.nk_updateTimeStamp) σ rfl z1 hz1)
    ((show IK VfhAll (updateTimeStamp (Z := Unit)) by unfold updateTimeStamp; kh_auto) σ hE.vfh z1 hz1)
  obtain ⟨hk, hct⟩ := kc_updateTimeStamp σ.kheap σ.curThread σ.interruptIrqNode σ ⟨rfl, rfl⟩ z1 hz1
  have hcnb := cnb_heap hk ⟨h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [← hct] at hcnb
  have h1 : B0 I z1.2 := ⟨⟨ba_updateTimeStamp σ h.1.1 z1 hz1,
    SInvU.io_of_uk (fun _ => SInvU.uk_updateTimeStamp) σ h.1.2.1 z1 hz1,
    SInvL.isk_updateTimeStamp σ h.1.2.2 z1 hz1⟩, hE1.sc, hcnb.1,
    (show IK SInv.VfC (updateTimeStamp (Z := Unit)) by vfc_auto) σ h.2.2.2.1 z1 hz1, hcnb.2.1, hcnb.2.2⟩
  obtain ⟨z2, hz2, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := SInvU.mem_bindE' hy
  swap
  · obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2; cases he
  obtain ⟨x, hx, rfl⟩ := SInvU.mem_liftE' hz2
  simp only [Except.ok.injEq] at hr; subst hr
  unfold NonDetE.whenE at hy
  split at hy
  · rename_i ht
    have e := SInvB.checkBudgetRestart_true_eq hx ht
    rw [e] at hy
    have hR1 := hR x ⟨z1, hz1, hx⟩ ht
    rw [e] at hR1
    exact ba_fl4HandleSyscall rep c I z1.2 h1 hE1 hR1 y hy
  · rw [Set.mem_singleton_iff.1 hy]
    exact ba_checkBudgetRestart_p z1.2 hE1.sc h1.1.1 x hx

set_option maxHeartbeats 4000000 in
/-- **`BlockedScActive` across `fl4CallKernel`** from the event start's facts. -/
theorem ba_fl4CallKernelF (rep : Bool) (ev : Event) (σ : State Unit) (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hV : SInv.VfC σ) (hC : ev ≠ .interrupt → CBa σ.curThread σ)
    (hN : ∀ c, ev = .syscallEvent c → NotQ σ.curThread σ ∧ Bd σ.curThread σ)
    (hR : ∀ c, ev = .syscallEvent c → RRF rep c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, BSA y.2 := by
  unfold fl4CallKernel
  intro y hy
  obtain ⟨z, hz, hy⟩ := hy
  have hz' : BSA z.2 := by
    unfold NonDetE.handleE at hz
    rw [ExceptT.run_mk] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hwB : BSA w.2 := by
      by_cases hs : ∃ c, ev = .syscallEvent c
      · obtain ⟨c, rfl⟩ := hs
        obtain ⟨hn, hd⟩ := hN c rfl
        exact ba_fl4HandleEvent_sysF rep c σ.idleSc σ ⟨⟨hB, hO, rfl⟩, hE.sc, hC (by intro e; cases e), hV, hn, hd⟩
          hE (hR c rfl) w hw
      · rw [fl4HandleEvent_other rep ev fun c e => hs ⟨c, e⟩] at hw
        exact ba_handleEvent_other ev (fun c e => hs ⟨c, e⟩) σ hB hE.sc hC w hw
    have hwI := SInvB.sb_fl4HandleEvent SInvB.scGap rep ev σ hE w hw
    obtain ⟨r, s⟩ := w
    cases r with
    | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hwB
    | error e =>
      unfold withoutPreemption at hz
      obtain ⟨v, hv, rfl⟩ := SInvU.mem_liftE' hz
      exact ba_preemptionPath_p s hwI hwB v hv
  exact (show BAK (do fl4Awaken (Z := Unit); schedule; activateThread) by ba_auto) z.2 hz' y hy

/-- **`BlockedScActive` across every kernel event.** Premises (all carried or
entry facts): BSA (this line), sb2's `EntryOK` (ScInv, UtInv3, VfhAll,
ScLive [J]), IdleScOutV (vi3 / ut7), CnDom (vfh), rd7's `CAx`; ct not
ipc-queued (from rd8a's `EF.ct` or SInvAll's `EntryJ.ctAct`: Running / Restart /
idle) and ct ≠ idle for a non-interrupt event (l4v `call_kernel`'s
`ct_running s ∨ (ev = Interrupt ∧ ct_idle s)`; rd8a's `EF.ni`); and
the pinned `RR` of a ReplyRecv / NBSendRecv / NBSendWait syscall. -/
theorem kcall_bsaF (rep : Bool) (ev : Event) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hR : ∀ c, ev = .syscallEvent c → RRF rep c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, BSA y.2 := by
  refine ba_fl4CallKernelF rep ev σ hB hE hO ⟨(vfhV_iff σ).2 hE.vfh, hCD⟩
    (fun h => cba_of_actB (hA (hni h))) (fun c e => ⟨hNQ, ?_⟩) hR
  obtain ⟨x, c', y, n, hx, hc, -, -⟩ := hA (hni (by rw [e]; intro h; cases h))
  exact ⟨x, c', hx, hc⟩

set_option maxHeartbeats 4000000 in
/-- **`BlockedScActive` across the syscall entry** (the FaultIP write, then
the syscall event); premises as `kcall_bsa` with ct ≠ idle, `RR` pinned at the
FaultIP outcome. -/
theorem kentry_bsaF (c : Syscall) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : σ.curThread ≠ σ.idleThread)
    (hR : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, RRF true c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, BSA y.2 := by
  unfold fl4KernelEntrySyscall
  intro y ⟨z, hz, hy⟩
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hy⟩ := hy
  have hE' : SInvB.EntryOK w.2 := SInvB.entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw)
    (SInvB.br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh w hw)
  have hz : A12b.KZ σ w.2 := (show A12b.KZK σ (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
    unfold fl4SyscallFaultIP; exact A12b.kz_asUser _ _) σ rfl w hw
  have hctw : w.2.curThread = σ.curThread := A12b.kz_curThread hz
  obtain ⟨x, c', y0, n, hx, hc, hy0, ha⟩ := hA hni
  have hSV := svs_of_kz hz
  have hidle : w.2.idleSc = σ.idleSc := congrArg (fun x => x.2.2.2.2.1) (A12b.kz_parts hz).2.2.1
  refine ba_fl4CallKernelF true _ w.2 ((show BAK (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; ba_auto) σ hB w hw) hE'
    (by rw [hidle]; exact SInvU.io_of_uk (fun _ => SInvU.uk_fl4SyscallFaultIP _) σ hO w hw)
    ((show IK SInv.VfC (fl4SyscallFaultIP (Z := Unit) σ.curThread) by unfold fl4SyscallFaultIP; vfc_auto) σ
      ⟨(vfhV_iff σ).2 hE.vfh, hCD⟩ w hw)
    (fun _ => by rw [hctw]; exact cba_sv (cba_of_actB (hA hni)) hSV)
    (fun _ _ => ⟨by rw [hctw]; exact nq_kz hz hNQ, by rw [hctw]; exact bd_sv ⟨x, c', hx, hc⟩ hSV⟩)
    (fun c0 e => by cases e; exact hR w hw) y hy


/-! ## The bridges -/

/-- **rd8l's `RR` at the front's `true` outcomes from rd14b's `RecvF`.** -/
theorem rrF_of {rep : Bool} {c : Syscall} {σ : State Unit} (h : A14b.RecvF rep c σ) : RRF rep c σ := by
  intro v hv ht
  have key : ∀ r cr, A12b.srArgs c = some (r, cr) → RP rep false false true true r v.2 :=
    fun r cr hc w hw y hy hu => by
      obtain ⟨u, hu⟩ := hu
      cases u
      exact (h v hv ht r cr hc w hw y hy hu).2
  cases c <;> first | trivial | exact key _ _ rfl

/-- **rd15a's `RecvTC` from rd14b's `RecvF`.** -/
theorem recvTC_of {rep : Bool} {c : Syscall} {σ : State Unit} (h : A14b.RecvF rep c σ) : A15a.RecvTC rep c σ :=
  fun v hv ht r cr hc g hg t ht' hok => (h v hv ht r cr hc g hg t ht' hok).1

/-- **rd8m's `RcvIn` from rd14b's `RecvF`** (`ScInv` by rd15a's `sc_first`). -/
theorem rcvIn_of {rep : Bool} {c : Syscall} {C N S : ObjRef} {I : ObjRef × ObjRef} {d : Prop}
    {Nq : Irq → ObjRef} {σe σ : State Unit} (hσ : P17.EvP C N S I d Nq σe σ) (hEO : SInvB.EntryOK σe)
    (h : A14b.RecvF rep c σ) : B8m.RcvIn rep c σ := by
  intro v hv ht r cr hc g hg t ht' hok
  have hg' := A13a.evp_getCapReg r v.2 (A13a.evp_front hσ hv ht) g hg
  exact ⟨A15a.sc_first hEO hg' rep false false true true g.1 t ht', (h v hv ht r cr hc g hg t ht' hok).1⟩

/-! ## The tops with `InvF` -/

section Q
open Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

set_option maxHeartbeats 4000000 in
/-- **rd15a's `kcall_rdyOff8` with `hC : RecvTC` replaced by rd14b's per-arm
first-phase obligation `InvF`.** -/
theorem kcall_rdyOff8f (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hInv : ∀ c, ev = .syscallEvent c → A15a.InvP1 c σ)
    (hF : ∀ c, ev = .syscallEvent c → A14b.InvF c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A15a.kcall_rdyOff8 hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hRdB hP hInv
    (fun c e => recvTC_of (A14b.recvF_of rep (hEF (by rw [e]; intro h; cases h)) (hF c e))) hRdF

set_option maxHeartbeats 4000000 in
/-- **rd15a's `kentry_rdyOff8` with `InvF` in place of `RecvTC`.** -/
theorem kentry_rdyOff8f (hnd : numDomains = 1) (rep : Bool) (c : Syscall) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (h : A8.EF σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState)
    (hIu : Iu σ.curThread σ) (hIL : IL [σ.curThread] σ) (hJ : Js I σ.curThread d Nq σ σ)
    (hE : EF Nq σ) (hI2 : I.2 = σ.idleSc) (hI1 : IrqOutV (fun _ => I.1) (uV σ))
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ A12b.InvR c w.2 ∧ A15a.InvP1 c w.2 ∧ A14b.InvF c w.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  A15a.kentry_rdyOff8 hnd rep c σ h hX10 hX hR h4 hCX ha hIu hIL hJ hE hI2 hI1 fun w hw =>
    ⟨(hW w hw).1, (hW w hw).2.1, (hW w hw).2.2.1,
      recvTC_of (A14b.recvF_of rep (A8.ef_fip h w hw) (hW w hw).2.2.2)⟩

set_option maxHeartbeats 4000000 in
/-- **rd8m's `kcall_rdyOff6m` with `hRc : RcvIn` replaced by `InvF`.** -/
theorem kcall_rdyOff6f (hnd : numDomains = 1) (rep : Bool) (ev : Event) (σ : State Unit)
    {I : ObjRef × ObjRef} {d : Prop} {Nq : Irq → ObjRef}
    (hEF : ev ≠ .interrupt → A8.EF σ) (hEFI : ev = .interrupt → A10.EFI σ) (hX10 : A10.EV10 σ)
    (hX : SInvQ.EX σ) (hR : RB σ) (h4 : T4 σ) (hCX : SInvAll.CtExit σ)
    (ha : ∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt)
    (hN : NQ [σ.curThread] σ) (hS : ∀ c, ev = .syscallEvent c → SysF I d Nq σ)
    (hIO : SInvU.IO (fun _ => σ.idleSc) σ) (hRS : σ.schedulerAction = .resumeCurThread)
    (hPs : ∀ c, ev = .syscallEvent c → ∀ r cl bl dn, A12b.sendArgs c = some (r, cl, bl, dn) → B8j.InvIn r false σ)
    (hPr : ∀ c, ev = .syscallEvent c → ∀ r cr, A12b.srArgs c = some (r, cr) → B8j.InvIn r true σ)
    (hPre : ∀ c, ev = .syscallEvent c → B8j.PreR rep c σ)
    (hF : ∀ c, ev = .syscallEvent c → A14b.InvF c σ)
    (hP : ∀ c, ev = .syscallEvent c → A12b.InvR c σ)
    (hRA : ∀ c, ev = .syscallEvent c → A13a.RecvTA rep c σ)
    (hRdF : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt → A11b.RdF ev σ) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine B8m.kcall_rdyOff6m hnd rep ev σ hEF hEFI hX10 hX hR h4 hCX ha hN hS hIO hRS hPs hPr hPre
    (fun c e => ?_) hP hRA hRdF
  subst e
  obtain ⟨hIu, hIL, hJ, -, -, -⟩ := hS _ rfl
  exact rcvIn_of (P17.evp_start (I := I) (d := d) (Nq := Nq) hX hR h4 hX10.vi hX10.eo hCX hIu hIL hJ) hX10.eo
    (A14b.recvF_of rep (hEF (by intro h; cases h)) (hF _ rfl))

end Q

/-- **rd8l's `kcall_bsa` with `RR` replaced by `InvF`** (with rd8a's `EF` at a
syscall event). -/
theorem kcall_bsaI (rep : Bool) (ev : Event) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hF : ∀ c, ev = .syscallEvent c → A8.EF σ ∧ A14b.InvF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, BSA y.2 :=
  kcall_bsaF rep ev hB hE hO hCD hA hNQ hni fun c e => rrF_of (A14b.recvF_of rep (hF c e).1 (hF c e).2)

/-- **rd8l's `kentry_bsa` with `RR` replaced by `InvF`** at the FaultIP outcome. -/
theorem kentry_bsaI (c : Syscall) {σ : State Unit} (hB : BSA σ) (hE : SInvB.EntryOK σ)
    (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hCD : CnDom σ) (hA : CAx σ)
    (hNQ : NotQ σ.curThread σ)
    (hni : σ.curThread ≠ σ.idleThread) (hEF : A8.EF σ)
    (hF : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14b.InvF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, BSA y.2 :=
  kentry_bsaF c hB hE hO hCD hA hNQ hni fun w hw => rrF_of (A14b.recvF_of true (A8.ef_fip hEF w hw) (hF w hw))

/-- **rd8l's `kentry_sinvCRB` with `RR` replaced by `InvF`.** -/
theorem kentry_sinvCRBI (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCRB σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hEF : A8.EF σ) (hF : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14b.InvF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCRB y.2 := by
  have hA' := h.1.1.1.1.1
  have hNQ : NotQ σ.curThread σ := nq_of_ev (ev := .syscallEvent c) (SInvAll.SInvB.entryJEv h.1.1.1 fun _ => hct)
  exact fun y hy => ⟨SInvAll.kentry_sinvCR_ofCA hnd c h.1 hct hCA y hy,
    kentry_bsaI c h.2 ⟨hI, hA'.ut, hA'.vfh, hL⟩ hO hA'.cnDom hA hNQ hct hEF hF y hy⟩

/-- **rd8l's `kcall_sinvCRB` with `RR` replaced by `InvF`.** -/
theorem kcall_sinvCRBI (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCRB σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hCA : ∀ r ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvR.CAx r.2)
    (hI : SInvB.ScInv σ) (hL : SInvB.ScLive σ) (hO : SInvU.IO (fun _ => σ.idleSc) σ) (hA : SInvR.CAx σ)
    (hF : ∀ c, ev = .syscallEvent c → A8.EF σ ∧ A14b.InvF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCRB y.2 := by
  have hA' := h.1.1.1.1.1
  have hNQ : NotQ σ.curThread σ := nq_of_ev (SInvAll.SInvB.entryJEv h.1.1.1 hev)
  exact fun y hy => ⟨SInvAll.kcall_sinvCR_ofCA hnd rep ev h.1 hev hCA y hy,
    kcall_bsaI rep ev h.2 ⟨hI, hA'.ut, hA'.vfh, hL⟩ hO hA'.cnDom hA hNQ hev hF y hy⟩

end

end Fl4Proofs.P3.SInvR.A14c
