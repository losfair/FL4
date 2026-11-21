/-
P3 (DESIGN.md §9), invariant line G1 (rd10, KENTRY-PLAN rd9 handoff 2):
**`hEvO` for the interrupt event** (spec side only).

* `aw9_sendSignal` (rd9's AW9 step of `aw_fl4Awaken`, exported),
  **`aw9_handleInterrupt` / `aw9_maybeHandleInterrupt`**: every interrupt
  handler keeps AW9 (`Rdy ∧ OS ∧ NQ [] ∧ ScInv ∧ RCA ∧ CtR ∧ HRC`): a
  signal-bound IRQ runs send_signal, the rest are machine operations, reads and
  the `reprogram_timer` write.
* `charge_rdy` (Rdy after charge_budget from the body-start facts, RdJ's
  `rd_chargeBudget`).
* **The idle thread's check_budget** (`cb_idle`): with `cur_sc = idle_sc` and ct
  not schedulable, charge_budget only zeroes the consumed time.
* `EFI` (rd8a's `EF` without `ct ≠ idle`, with ValidIdle), **`aw9_cb`** (AW9
  after update_time_stamp ; check_budget, ct idle or not), **`ev_irq`**: `SS ∧
  NQ []` at every outcome of the interrupt event's part. No premise.
* Tops **`kcall_rdyOff3i`**: rd10's `kcall_rdyOff3` with `hEvO` only for the
  fault events (unknown syscall, user-level / VM / hypervisor faults).
-/
import Fl4Proofs.P3.SpecInvRd10A2
open Classical

namespace Fl4Proofs.P3.SInvR.A10
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The interrupt handlers -/

/-- rd9's send_signal step of `aw_fl4Awaken`. -/
theorem aw9_sendSignal (n : ObjRef) (bd : Badge) : IK A9.AW9 (sendSignal (Z := Unit) n bd) := by
  intro b0 hb y hy
  obtain ⟨hRO, hSc, hA, hC, hH⟩ := hb
  have hN : SInv.NtfnQB b0 := ((nq_nil_iff b0).1 hRO.2.2).1
  obtain ⟨a1, a2, a3⟩ := A9.aw_sendSignal n bd b0 hRO.1 hN hSc hA hC hH y hy
  exact ⟨A8.ro_sendSignal n bd b0 hRO y hy, SInvB.si_sendSignal n bd b0 hSc y hy, a1, a2, a3⟩

theorem aw9_doMachineOp {α : Type} (mop : NonDet MachineState α) : IK A9.AW9 (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) _

/-- **Every interrupt handler keeps AW9.** -/
theorem aw9_handleInterrupt (irq : Irq) : IK A9.AW9 (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt
  split
  · exact aw9_doMachineOp _
  · refine ik_bind ?_ fun st => ?_
    · unfold getIrqState; repeat' (first | ik_step0 | ik_unfold)
    · dsimp only
      split
      · refine ik_bind ?_ fun sl => ?_
        · unfold getIrqSlot; repeat' (first | ik_step0 | ik_unfold)
        refine ik_bind ?_ fun cap => ?_
        · intro σ0 hσ y hy
          have e1 : y.2 = σ0 := SInvQ.cq5_ro (fun _ => by
            obtain ⟨o, r⟩ := sl; unfold getCap; repeat' (first | ik_step0 | ik_unfold | split)) hy
          rw [e1]; exact hσ
        refine ik_bind ?_ fun _ => ?_
        · unfold NonDet.when
          split
          · exact aw9_sendSignal _ _
          · exact ik_pure _
        refine ik_bind ?_ fun _ => aw9_doMachineOp _
        unfold archMaskIrqSignal; exact aw9_doMachineOp _
      · refine ik_bind (aw9_doMachineOp _) fun _ => ?_
        refine ik_bind (ik_modify (fun _ h => h)) fun _ => aw9_doMachineOp _
      · exact ik_bind ik_fail fun _ => aw9_doMachineOp _
      · refine ik_bind ?_ fun _ => aw9_doMachineOp _
        unfold handleReservedIrq; exact ik_pure _

theorem aw9_maybeHandleInterrupt (b : Bool) : IK A9.AW9 (maybeHandleInterrupt (Z := Unit) b) := by
  unfold maybeHandleInterrupt
  refine ik_bind (aw9_doMachineOp _) fun o => ?_
  cases o with
  | none => unfold handleSpuriousIrq; exact ik_pure _
  | some irq => exact aw9_handleInterrupt irq

/-! ## `check_budget` at the interrupt -/

/-- Rdy after `charge_budget` from the body-start facts. -/
theorem charge_rdy {s : State Unit} (h : BS s) (u : Ticks) (c : Bool) {z : Unit × State Unit}
    (hz : z ∈ (chargeBudget (Z := Unit) u c s).1) : Rdy z.2 := by
  obtain ⟨xt, hct, hst⟩ := h.ct
  obtain ⟨xa, c0, y, n, hxa, hca, hky, hact⟩ := h.ca h.ni
  rw [hct] at hxa; cases hxa
  have hb : xt.tcbSchedContext = some s.curSc := h.cs xt hct
  rw [hb] at hca; cases hca
  obtain ⟨y0, k0, hy0, -, hne⟩ := h.sc.back s.curThread xt s.curSc hct hb
  rw [hky] at hy0; cases hy0
  exact (rd_chargeBudget h.rdy hky hact (hne (Or.inr hact))
    (fun _ _ => excl_entry h.sc.back h.cs hct hst h.q h.si) hct hb h.sc.fwd u c hz).1

/-- **charge_budget on the idle SC with ct not schedulable** only zeroes the consumed time. -/
theorem cb_idle {s : State Unit} (hi : s.curSc = s.idleSc) {xt : Tcb}
    (hct : s.kheap s.curThread = some (.tcb xt)) (hst : xt.tcbState = .idleThreadState)
    (u : Ticks) (c : Bool) {z : Unit × State Unit} (hz : z ∈ (chargeBudget (Z := Unit) u c s).1) :
    z.2 = ({ s with consumedTime := 0 } : State Unit) := by
  unfold chargeBudget at hz
  rw [nd_gets_bind, nd_gets_bind] at hz
  obtain ⟨y1, hy1, hz⟩ := hz
  beta_reduce at hz
  rw [SInvV.sv_bind_modify] at hz
  have hci : ¬ s.curSc ≠ s.idleSc := fun h => h hi
  rw [NonDet.when, if_neg hci] at hy1
  obtain rfl : y1 = ((), s) := hy1
  have hns : schedulable ({ s with consumedTime := 0 } : State Unit).curThread
      ({ s with consumedTime := 0 } : State Unit) = false := by
    cases hsb : schedulable ({ s with consumedTime := 0 } : State Unit).curThread
        ({ s with consumedTime := 0 } : State Unit) with
    | false => rfl
    | true =>
      have := SInv.sched_runnable hsb xt hct
      rw [hst] at this; cases this
  exact (cbTail_cf (c := c) hz).2 hns

/-- rd8a's `EF` without `ct ≠ idle`, with ValidIdle (the interrupt entry). -/
structure EFI (σ : State Unit) : Prop where
  rdy : Rdy σ
  off : Sched.OffReady σ
  vmt : SInvV.ValidMachineTime σ
  sc : SInvB.ScInv σ
  cs : SInvQ.CurScT σ
  ct : ∃ xt, σ.kheap σ.curThread = some (.tcb xt) ∧ (xt.tcbState = .running ∨ xt.tcbState = .idleThreadState)
  q : SInvQ.CtQ σ
  si : SInvQ.Simple σ
  cb : SInvQ.CB σ
  hb : σ.schedulerAction = .resumeCurThread → σ.curThread ∉ σ.releaseQueue
  ca : CAx σ
  nq : NQ [] σ
  vi : SInvI.ValidIdle σ

theorem efi_of {σ : State Unit} (h : A8.EF σ) (hv : SInvI.ValidIdle σ) : EFI σ :=
  ⟨h.rdy, h.off, h.vmt, h.sc, h.cs, h.ct, h.q, h.si, h.cb, h.hb, h.ca, h.nq, hv⟩

/-- **AW9 after `update_time_stamp ; check_budget`** at the interrupt entry. -/
theorem aw9_cb {σ : State Unit} (h : EFI σ) {y : Unit × State Unit} (hy : y ∈ (updateTimeStamp (Z := Unit) σ).1)
    {z : Bool × State Unit} (hz : z ∈ (checkBudget (Z := Unit) y.2).1) : A9.AW9 z.2 := by
  obtain ⟨ek, ec, -, -⟩ := SInvO.uts_off hy
  obtain ⟨et, eit⟩ := ci_updateTimeStamp σ.curThread σ.idleThread σ ⟨rfl, rfl⟩ y hy
  obtain ⟨-, -, -, ei⟩ := qa_updateTimeStamp σ.readyQueues σ.schedulerAction σ.releaseQueue σ.idleSc σ
    ⟨rfl, rfl, rfl, rfl⟩ y hy
  have hSy : SInvB.ScInv y.2 := by
    unfold SInvB.ScInv SInvB.ScSym SInvB.ScBackS SInvB.ScFwd SInvB.RNE; rw [ek]; exact h.sc
  have hNy : NQ [] y.2 := nq_updateTimeStamp σ h.nq y hy
  have hSz : SInvB.ScInv z.2 := SInvB.si_checkBudget y.2 hSy z hz
  have hNz : NQ [] z.2 := nq_checkBudget y.2 hNy z hz
  by_cases hni : σ.curThread = σ.idleThread
  · -- the idle thread: cur_sc is the idle SC, ct not runnable
    obtain ⟨xi, hxi, hsti, -, hsci, -⟩ := SInvI.vi_idle h.vi
    have hcs0 : σ.curSc = σ.idleSc := by
      have := h.cs xi (by rw [hni]; exact hxi)
      rw [hsci] at this; exact (Option.some.inj this).symm
    have hR : Rdy y.2 := rdy_updateTimeStamp h.vmt h.rdy hy
    have hO : Sched.OffReady y.2 := SInvO.offReady_updateTimeStamp h.vmt h.off hy
    have hcs : SInvQ.CurScT y.2 := by intro x hx; rw [ek, et] at hx; rw [ec]; exact h.cs x hx
    have hi : y.2.curSc = y.2.idleSc := by rw [ec, ei]; exact hcs0
    have hid : y.2.curThread = y.2.idleThread := by rw [et, eit]; exact hni
    have hct : y.2.kheap y.2.curThread = some (.tcb xi) := by rw [ek, et, hni]; exact hxi
    have hnr : ∀ x, y.2.kheap y.2.curThread = some (.tcb x) → runnable x.tcbState = false := by
      intro x hx; rw [hct] at hx; cases hx; rw [hsti]; rfl
    rcases checkBudget_cases hz with ⟨e, hsf⟩ | ⟨-, hc⟩
    · rw [e]
      refine ⟨⟨hR, Or.inl ⟨hO, hsf⟩, hNy⟩, hSy, fun _ hne => absurd hid hne, ?_, fun _ => hcs⟩
      intro x hx hrun; rw [hnr x hx] at hrun; cases hrun
    · have e := cb_idle hi hct hsti _ true hc
      have hNz' := hNz; have hSz' := hSz
      rw [e] at hNz' hSz' ⊢
      refine ⟨⟨rdy_consumed0 hR, Or.inl ⟨?_, ?_⟩, hNz'⟩, hSz', fun _ hne => absurd hid hne, ?_, fun _ => hcs⟩
      · intro y' n' hy'
        have h1 := hO y' n' hy'
        show (refillHd y').rTime.toNat + (0 : Ticks).toNat ≤ y.2.curTime.toNat
        rw [show (0 : Ticks).toNat = 0 from rfl, Nat.add_zero]
        exact Nat.le_trans (Nat.le_add_right _ _) h1
      · intro y' n' _ _ hne; exact absurd hi hne
      · intro x hx hrun; rw [hnr x hx] at hrun; cases hrun
  · have hB := bs_uts ⟨h.rdy, h.off, h.vmt, h.sc, h.cs, h.ct, h.q, h.si, h.cb, h.hb, h.ca, hni, h.nq⟩ hy
    rcases checkBudget_cases hz with ⟨e, hsf⟩ | ⟨-, hc⟩
    · rw [e]
      obtain ⟨a1, a2, a3, a4⟩ := ss4_of_bs hB hsf
      exact ⟨⟨hB.rdy, a1, hB.nq⟩, hB.sc, a2, a3, a4⟩
    · obtain ⟨a1, a2, a3, a4⟩ := charge_ss4 hB _ true hc
      exact ⟨⟨charge_rdy hB _ true hc, a1, hNz⟩, hSz, a2, a3, a4⟩

/-- **`hEvO` for the interrupt event**: `SS ∧ NQ []` at every outcome of its event part. -/
theorem ev_irq (rep : Bool) {σ : State Unit} (h : EFI σ) :
    ∀ y ∈ (A8.evRun rep .interrupt σ).1, A8.SS y.2 ∧ NQ [] y.2 := by
  intro y hy
  dsimp only [A8.evRun] at hy
  rw [fl4HandleEvent_other rep _ (fun c e => by cases e)] at hy
  simp only [handleEvent] at hy
  obtain ⟨w, hw, e⟩ := mem_handleE_wp hy
  rw [e]
  obtain ⟨y1, hy1, hw⟩ := hw
  obtain ⟨z, hz, hw⟩ := hw
  obtain ⟨⟨hR, hO, hN⟩, -, hA, hC, hH⟩ := aw9_maybeHandleInterrupt false z.2 (aw9_cb h hy1 hz) w hw
  exact ⟨⟨hR, hO, hA, hC, hH⟩, hN⟩

/-! ## The top -/

/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event** (rd10 top with the
interrupt event discharged): remaining `hRdB`, `hOsB` (syscalls other than
Yield), `hEvO` for the fault events only, `hQ4`. -/
theorem kcall_rdyOff3i (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ) (hEFI : ev = .interrupt → EFI σ) (hX : EV10 σ)
    (hni : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hRdB : ∀ c, ev = .syscallEvent c → A9.RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → c ≠ .sysYield → A9.OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt →
      ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hQ4 : ∀ y ∈ (A8.evRun rep ev σ).1, SQ4 y.2) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine kcall_rdyOff3 rep ev σ hEF hX hni hRdB hOsB (fun hs => ?_) hQ4
  by_cases hi : ev = .interrupt
  · subst hi; exact ev_irq rep (hEFI rfl)
  · exact hEvO hs hi

end

end Fl4Proofs.P3.SInvR.A10
