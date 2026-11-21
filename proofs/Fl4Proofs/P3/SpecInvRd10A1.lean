/-
P3 (DESIGN.md §9), invariant line G1 (rd10, KENTRY-PLAN rd9 handoff 3-4):
**`hCS` removed, `hSc` / `hVI` wired, `hAW` narrowed** (spec side only).

* **`hCS` (cur_sc is an SC at `schedule`'s start) is not needed.** `sc_and_timer`'s
  `switch_sched_context` reads `get_sched_context cur_sc`, which fails (no outcome)
  unless `cur_sc` is an SC: **`sat_curSc`** (the outcome-side twin of rd4's
  `sat_bound`). `schedule` keeps the heap view and `cur_sc` up to `sc_and_timer`
  (RdY's `SE` / `FK`), so `cur_sc` is an SC at `schedule`'s start whenever
  `schedule` has an outcome. Hence `rd_exitSE10` / `rd_scheduleOff10` (rd4's
  lemmas without `hk0`), `XS10` (rd8a's `XS` without its last conjunct),
  `exit_top10`, `kcall_of_ev10`, `kcall_rdyOff10a` (rd9's `kcall_rdyOff9b` with
  `XS10`). No new carried fact, no premise.
* **`hSc`**: sb2's `ScInv` at every outcome of the event part (`sc_evRun`, sb2's
  `sb_fl4HandleEvent scGap` + `si_preemptionPath`) from sb2's carried
  `EntryOK`.
* **`hVI`**: vi3's `ValidIdle` at every outcome of the event part (`vi_ev`, the
  event part of vi3's `vi_callKernel_of`; syscalls by `vi_fl4HandleEvent_sys
  viGap` from vi3's `W` relation, the pinned thread = ct, `CtSc` from ctq5's
  `CurScT`; the other events as vi3's `kcall_validIdle_of`).
* **`hAW` narrowed to `SQ4` at the event-part outcomes** (`SchedQ ∧ T4`, the
  ctq17/18 event carry): ctq's `sq4_fl4Awaken` (no premise) and `aw_of` with
  ValidIdle after fl4Awaken.
* Tops **`kcall_rdyOff3a` / `kentry_rdyOff3a`**: remaining hypotheses `hRdB`
  (rd8e/f), `hOsB` / `hEvO` (this line, later modules) and `hQ4` (ctq).
-/
import Fl4Proofs.P3.SpecInvRd9A4
import Fl4Proofs.P3.SpecInvSbT
import Fl4Proofs.P3.SpecInvViM
import Fl4Proofs.P3.SpecInvCqL
open Classical

namespace Fl4Proofs.P3.SInvR.A10
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `cur_sc` is an SC at every `sc_and_timer` outcome -/

/-- **`switch_sched_context` reads `cur_sc` as an SC** (`get_sched_context` fails otherwise). -/
theorem sat_curSc {s : State Unit} {r : Unit × State Unit} (hr : r ∈ (scAndTimer (Z := Unit) s).1) :
    ∃ x n, s.kheap s.curSc = some (.schedContext x n) := by
  unfold scAndTimer at hr
  obtain ⟨z, hz, -⟩ := hr
  unfold switchSchedContext at hz
  rw [Notif.nd_gets_bind, Notif.nd_gets_bind] at hz
  obtain ⟨w, hw, hz⟩ := hz
  obtain ⟨xt, -, rfl⟩ := q1_mem_threadGet hw
  obtain ⟨v, hv, hz⟩ := hz
  obtain ⟨-, ev⟩ := cq5_mem_assertOpt hv
  obtain ⟨u, hu, -⟩ := hz
  obtain ⟨eu, n, hn⟩ := SInvB.mem_getSchedContext' hu
  rw [ev] at hn
  exact ⟨u.1, n, hn⟩

/-- rd4's `rd_exitSE` without `hk0` (read off the outcome, `sat_curSc`). -/
theorem rd_exitSE10 {σ s : State Unit} (hS : SE σ s)
    (hOS0 : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ σ.schedulerAction ≠ .resumeCurThread) ∨ OI σ)
    (hB : SInvB.ScBackS σ) (hRN : SInvB.RNE σ) (hV : SInvI.ValidIdle σ) (hIH : IdleHd σ)
    (hRC : σ.schedulerAction = .resumeCurThread → ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      x.tcbSchedContext = some σ.curSc)
    {r : Unit × State Unit} (hr : r ∈ (scAndTimer (Z := Unit) s).1) : Rdy r.2 ∧ Sched.OffReady r.2 := by
  obtain ⟨x, n, hk⟩ := sat_curSc hr
  have hk0 : σ.kheap σ.curSc = some (.schedContext x n) := by
    obtain ⟨⟨hFk, hc, -⟩, -⟩ := hS
    rw [hc] at hk
    exact (hv_sc (hFk _)).1 hk
  exact rd_exitSE hS hk0 hOS0 hB hRN hV hIH hRC hr

/-- rd4's `rd_scheduleOff` without `hk0`. -/
theorem rd_scheduleOff10 (σ : State Unit) (hσ : Rdy σ) (hRN : SInvB.RNE σ)
    (hC : CtR σ) (hAW : AW σ)
    (hOS0 : (Sched.OffReady σ ∧ Suff σ) ∨ (σ.consumedTime = 0 ∧ σ.schedulerAction ≠ .resumeCurThread) ∨ OI σ)
    (hB : SInvB.ScBackS σ) (hV : SInvI.ValidIdle σ) (hIH : IdleHd σ)
    (hRC : σ.schedulerAction = .resumeCurThread → ∀ x, σ.kheap σ.curThread = some (.tcb x) →
      x.tcbSchedContext = some σ.curSc) :
    ∀ r ∈ (schedule (Z := Unit) σ).1, Rdy r.2 ∧ Sched.OffReady r.2 :=
  rd_scheduleSE (Q := fun s => Rdy s ∧ Sched.OffReady s) σ
    (fun _ hs _ hr => rd_exitSE10 hs hOS0 hB hRN hV hIH hRC hr) hσ hRN hC hAW

/-- rd8a's `XS` without "cur_sc is an SC". -/
abbrev XS10 (s : State Unit) : Prop :=
  SInvB.RNE s ∧ SInvB.ScBackS s ∧ SInvI.ValidIdle s ∧ AW s

/-- rd8a's `exit_top` from `XS10`. -/
theorem exit_top10 {s : State Unit} (h : A8.SS s) (hx : XS10 s) :
    ∀ r ∈ ((schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) s).1,
      Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  obtain ⟨hR, hO, hA, hC, hH⟩ := h
  obtain ⟨hRN, hB, hV, hAW⟩ := hx
  intro r hr
  have hc := A8.cax_exit s hR hRN hC hAW hA r hr
  obtain ⟨z, hz, hr'⟩ := hr
  obtain ⟨h1, h2⟩ := rd_scheduleOff10 s hR hRN hC hAW hO hB hV hR.2.2.2.2.2 hH z hz
  exact ⟨rd_activateThread z.2 h1 r hr', A8.or_activateThread z.2 h2 r hr', hc⟩

/-- rd8a's `kcall_of_ev` from `XS10`. -/
theorem kcall_of_ev10 (rep : Bool) (ev : Event) (σ : State Unit)
    (hE : ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hAw : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
      A8.RCA y2.2 ∧ CtR y2.2 ∧ A8.HRC y2.2)
    (hX : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS10 y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r hr
  unfold fl4CallKernel at hr
  obtain ⟨y1, h1, hr⟩ := hr
  obtain ⟨y2, h2, hr⟩ := hr
  obtain ⟨hS, hN⟩ := hE y1 h1
  obtain ⟨hR2, hO2, -⟩ := A8.ro_fl4Awaken y1.2 ⟨hS.1, hS.2.1, hN⟩ y2 h2
  obtain ⟨hA2, hC2, hH2⟩ := hAw y1 h1 y2 h2
  exact exit_top10 ⟨hR2, hO2, hA2, hC2, hH2⟩ (hX y1 h1 y2 h2) r hr

/-- rd9's `kcall_rdyOff9b` from `XS10`. -/
theorem kcall_rdyOff10a (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ)
    (hBody : ∀ c, ev = .syscallEvent c → ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1,
      A8.SS y.2 ∧ NQ [] y.2)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hSc : ∀ y ∈ (A8.evRun rep ev σ).1, SInvB.ScInv y.2)
    (hX : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, XS10 y2.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  have hE : ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2 := by
    by_cases hs : ∃ c, ev = .syscallEvent c
    · obtain ⟨c, rfl⟩ := hs
      exact A8.ev_sys rep c σ (hEF c rfl) (A8.hCtRc_of (hEF c rfl) A9.tmoNR) (hBody c rfl)
    · exact hEvO fun c e => hs ⟨c, e⟩
  refine kcall_of_ev10 rep ev σ hE (fun y hy y2 hy2 => ?_) hX
  obtain ⟨⟨hR, hO, hA, hC, hH⟩, hN⟩ := hE y hy
  obtain ⟨-, -, a1, a2, a3⟩ := A9.aw_fl4Awaken y.2 ⟨⟨hR, hO, hN⟩, hSc y hy, hA, hC, hH⟩ y2 hy2
  exact ⟨a1, a2, a3⟩

/-! ## `ScInv` at the event part's outcomes (sb2) -/

section
open Fl4Proofs.P3.SInvB

/-- sb2's ScInv at every outcome of the event part (with the preemption path). -/
theorem sc_evRun (rep : Bool) (ev : Event) (σ : State Unit) (hE : EntryOK σ) :
    ∀ y ∈ (A8.evRun rep ev σ).1, ScInv y.2 := by
  intro z hz
  dsimp only [A8.evRun] at hz
  unfold NonDetE.handleE at hz
  rw [ExceptT.run_mk] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hw' := sb_fl4HandleEvent scGap rep ev σ hE w hw
  obtain ⟨r, s⟩ := w
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hw'
  | error e => exact (ike_liftE si_preemptionPath : SIKE (withoutPreemption (Z := Unit) preemptionPath)) s hw' z hz

/-- sb2's EntryOK survives the FaultIP write (sb2's `kentry_scInv_of`). -/
theorem entryOK_fip {σ : State Unit} (hE : EntryOK σ) :
    ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, EntryOK w.2 := fun w hw =>
  entryOK_keep hE (SInvU.uk_mem (fun _ => SInvU.uk_fl4SyscallFaultIP _) hw)
    (br_mem_of_sbk (fun _ => by sb_auto) hw)
    ((show SInvU.NK σ.interruptIrqNode (fl4SyscallFaultIP (Z := Unit) σ.curThread) from
      SInvU.nk_fl4SyscallFaultIP _) σ rfl w hw)
    ((show IK VfhAll (fl4SyscallFaultIP (Z := Unit) σ.curThread) by
      unfold fl4SyscallFaultIP; exact ti_asUser _ _ (fun _ _ h => h)) σ hE.vfh w hw)

end

/-! ## `ValidIdle` at the event part's outcomes (vi3) -/

section
open Fl4Proofs.P3.SInvI Fl4Proofs.P3.SInvU

/-- The event part of vi3's `vi_callKernel_of`. -/
theorem vi_ev {N S : ObjRef} {b : Bool} (rep : Bool) (ev : Event) {σ : State Unit}
    (hE : ∀ z ∈ ((fl4HandleEvent (Z := Unit) rep ev).run σ).1, VI N S b z.2) :
    ∀ y ∈ (A8.evRun rep ev σ).1, VI N S b y.2 := by
  intro z hz
  dsimp only [A8.evRun] at hz
  unfold NonDetE.handleE at hz
  rw [ExceptT.run_mk] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hw' := hE w hw
  obtain ⟨r, s⟩ := w
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hz]; exact hw'
  | error e => exact (show IKE (VI N S b) (withoutPreemption (Z := Unit) preemptionPath) by vi_auto) s hw' z hz

theorem validIdle_ev {σ : State Unit} {b : Bool} {rep : Bool} {ev : Event} {σw : State Unit}
    (hE : ∀ y ∈ (A8.evRun rep ev σw).1, VI σ.idleThread σ.idleSc b y.2) :
    ∀ y ∈ (A8.evRun rep ev σw).1, ValidIdle y.2 := fun y hy =>
  validIdle_of (σ := σ) (vit_false (hE y hy))

/-- `CtSc` (vi2) from ctq5's `CurScT`. -/
theorem ctSc_of {σ : State Unit} (h : CurScT σ) : CtSc σ := fun x hx h0 => by
  rw [h x hx] at h0; cases h0

/-- ValidIdle at the event part's outcomes of a syscall, from a `W`-related state. -/
theorem vi_evSys (rep : Bool) (c : Syscall) {σ0 σ : State Unit}
    (hW : W σ0.idleThread σ0.idleSc σ0.curThread σ0 σ) (hS : SInvG.IdleOutV σ0) (hI : IdleScOutV σ0)
    (hU : UtInv3 σ0) : ∀ y ∈ (A8.evRun rep (.syscallEvent c) σ).1, ValidIdle y.2 :=
  validIdle_ev (σ := σ0) (vi_ev rep _ (vi_fl4HandleEvent_sys viGap rep c hW hS hI hU.1 (fun _ => rfl)))

/-- ValidIdle at the event part's outcomes of every event (vi3's `kcall_validIdle_of`). -/
theorem vi_evRun (rep : Bool) (ev : Event) {σ : State Unit} (hV : ValidIdle σ)
    (hS : SInvG.IdleOutV σ) (hI : IdleScOutV σ) (hU : UtInv3 σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hct : ∀ c, ev = .syscallEvent c → CurScT σ) :
    ∀ y ∈ (A8.evRun rep ev σ).1, ValidIdle y.2 := by
  by_cases hi : ev = .interrupt
  · subst hi
    refine validIdle_ev (σ := σ) (b := false) (vi_ev rep _ ?_)
    rw [fl4HandleEvent_other rep _ fun c e => by cases e]
    exact vi_handleEvent_irq σ hV
  · have hV1 : VI σ.idleThread σ.idleSc true σ := vit_true hV (hni hi)
    by_cases hs : ∃ c, ev = .syscallEvent c
    · obtain ⟨c, rfl⟩ := hs
      exact vi_evSys rep c ⟨vit_of_vi hV1 (ctSc_of (hct c rfl)), rfl, rfl⟩ hS hI hU
    · refine validIdle_ev (σ := σ) (b := true) (vi_ev rep _ ?_)
      rw [fl4HandleEvent_other rep _ fun c e => hs ⟨c, e⟩]
      exact vi_handleEvent_fault ev (fun c e => hs ⟨c, e⟩) hi σ hV1

end

/-! ## The tops -/

/-- The other lines' entry facts the tops read (all carried): sb2's `EntryOK`,
vi3's `ValidIdle` / `IdleScOutV`, sg1's `IdleOutV`. -/
structure EV10 (σ : State Unit) : Prop where
  eo : SInvB.EntryOK σ
  vi : SInvI.ValidIdle σ
  io : SInvG.IdleOutV σ
  isc : SInvI.IdleScOutV σ

/-- The facts at `schedule`'s start from the event part's outcomes. -/
theorem xs10_of {y : State Unit} (hSc : SInvB.ScInv y) (hVI : SInvI.ValidIdle y) (hQ : SQ4 y) :
    ∀ y2 ∈ (fl4Awaken (Z := Unit) y).1, XS10 y2.2 := fun y2 hy2 =>
  have hS2 := SInvB.si_fl4Awaken y hSc y2 hy2
  have hV2 := A9.vi_awaken y hVI y2 hy2
  have hQ2 := sq4_fl4Awaken y hQ y2 hy2
  ⟨hS2.2, hS2.1.1, hV2, aw_of hQ2.1 hQ2.2 hV2⟩

/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event**, the event-part facts as
hypotheses: the body (`hRdB` rd8e/f, `hOsB` this line), the other events
(`hEvO`), sb2's ScInv, vi3's ValidIdle and ctq's SQ4 there. -/
theorem kcall_rdyOff10 (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hSc : ∀ y ∈ (A8.evRun rep ev σ).1, SInvB.ScInv y.2)
    (hVI : ∀ y ∈ (A8.evRun rep ev σ).1, SInvI.ValidIdle y.2)
    (hQ4 : ∀ y ∈ (A8.evRun rep ev σ).1, SQ4 y.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine kcall_rdyOff10a rep ev σ hEF (fun c e v hv hvt y hy => ?_) hEvO hSc
    (fun y hy => xs10_of (hSc y hy) (hVI y hy) (hQ4 y hy))
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOsB c e v hv hvt y hy
  exact ⟨⟨hRdB c e v hv hvt y hy, h1, h2, h3, h4⟩, h5⟩

/-- **Every kernel event** from the carried entry facts (`EF` for syscalls, `EV10`,
ct not idle unless an interrupt); remaining: `hRdB`, `hOsB`, `hEvO`, `hQ4`. -/
theorem kcall_rdyOff3a (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ) (hX : EV10 σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hQ4 : ∀ y ∈ (A8.evRun rep ev σ).1, SQ4 y.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 :=
  kcall_rdyOff10 rep ev σ hEF hRdB hOsB hEvO (sc_evRun rep ev σ hX.eo)
    (vi_evRun rep ev hX.vi hX.io hX.isc hX.eo.ut hni fun c e => (hEF c e).cs) hQ4

/-- **The syscall entry** from the carried entry facts; remaining: `hRdB`, `hOsB`
and `hQ4` at the FaultIP write's outcome. -/
theorem kentry_rdyOff3a (rep : Bool) (c : Syscall) (σ : State Unit) (h : A8.EF σ) (hX : EV10 σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      A9.RdBody rep c w.2 ∧ A9.OsBody rep c w.2 ∧ ∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SQ4 y.2) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r ⟨y1, h1, hr⟩
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨hR, hO, hQ⟩ := hW w hw
  have hV1 : SInvI.VI σ.idleThread σ.idleSc true σ := SInvI.vit_true hX.vi h.ni
  have hW0 : SInvI.W σ.idleThread σ.idleSc σ.curThread σ σ :=
    ⟨SInvI.vit_of_vi hV1 (ctSc_of h.cs), rfl, rfl⟩
  have hWw := SInvI.w_stepN (by unfold fl4SyscallFaultIP; exact SInvI.vi_asUser _ _)
    (fun _ => SInvU.uk_fl4SyscallFaultIP _) (fun _ => ct_fl4SyscallFaultIP _) hW0 w hw
  exact kcall_rdyOff10 rep _ w.2 (fun _ e => by cases e; exact A8.ef_fip h w hw) (fun _ e => by cases e; exact hR)
    (fun _ e => by cases e; exact hO) (fun hne => absurd rfl (hne c)) (sc_evRun rep _ w.2 (entryOK_fip hX.eo w hw))
    (vi_evSys rep c hWw hX.io hX.isc hX.eo.ut) hQ r hr

end

end Fl4Proofs.P3.SInvR.A10
