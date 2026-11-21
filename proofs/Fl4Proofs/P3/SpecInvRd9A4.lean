/-
P3 (DESIGN.md §9), invariant line G1 (rd9, KENTRY-PLAN rd8a handoff 3-4):
**the tops `kcall_rdyOff2` / `kentry_rdyOff2`** (spec side only).

* `hX` (A8's `XS` at `schedule`'s start) wired: RNE / ScBackS from sb's
  ScInv after the event part carried by `SInvB.si_fl4Awaken`; ValidIdle from
  vi's ValidIdle after the event part carried by `vi_awaken` (vi2's
  `vi_fl4Awaken` + `validIdle_of`); `AW` and "cur_sc is an SC" stay
  hypotheses at the awaken outcomes (ctq line: `aw_of` from SchedQ / T4 /
  ValidIdle there).
* The syscall body (`hBody`) split: **`RdBody`** (Rdy at every body outcome
  after a true front: rd8c's eventual `rd_fl4HandleSyscall`-style lemma) and
  **`OsBody`** (OS / RCA / CtR / HRC / NQ [] there: this line's remaining body
  carry, NQ from nq3's `nq_fl4HandleSyscall` family).
-/
import Fl4Proofs.P3.SpecInvRd9A3
import Fl4Proofs.P3.SpecInvViH
open Classical

namespace Fl4Proofs.P3.SInvR.A9
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

theorem vi_awaken : IK SInvI.ValidIdle (fl4Awaken (Z := Unit)) := fun σ h y hy =>
  SInvI.validIdle_of (SInvI.vi_fl4Awaken (N := σ.idleThread) (S := σ.idleSc) (b := false) σ h y hy)

theorem xs_of {s : State Unit} (hS : SInvB.ScInv s) (hV : SInvI.ValidIdle s) (hA : AW s)
    (hC : ∃ x n, s.kheap s.curSc = some (.schedContext x n)) : A8.XS s :=
  ⟨hS.2, hS.1.1, hV, hA, hC⟩

/-- rd8c's part of the body: `Rdy` at every outcome of the syscall body (with
the preemption path) after a `true` front. -/
abbrev RdBody (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1, Rdy y.2

/-- This line's part of the body (NOT done): OS / RCA / CtR / HRC (and nq3's
NQ []) at every outcome of the syscall body after a `true` front. -/
abbrev OsBody (rep : Bool) (c : Syscall) (σ : State Unit) : Prop :=
  ∀ v ∈ (A8.front σ).1, v.1 = true → ∀ y ∈ (A8.bodyRun rep c v.2).1,
    OS y.2 ∧ A8.RCA y.2 ∧ CtR y.2 ∧ A8.HRC y.2 ∧ NQ [] y.2

/-- **`Rdy ∧ OffReady ∧ CAx` after every kernel event**; remaining hypotheses:
the entry facts, the body (rd8c / this line), the other events, and the
other lines' facts (sb ScInv, vi ValidIdle after the event part; ctq AW and
cur_sc an SC after fl4Awaken). -/
theorem kcall_rdyOff2 (rep : Bool) (ev : Event) (σ : State Unit)
    (hEF : ∀ c, ev = .syscallEvent c → A8.EF σ)
    (hRdB : ∀ c, ev = .syscallEvent c → RdBody rep c σ)
    (hOsB : ∀ c, ev = .syscallEvent c → OsBody rep c σ)
    (hEvO : (∀ c, ev ≠ .syscallEvent c) → ∀ y ∈ (A8.evRun rep ev σ).1, A8.SS y.2 ∧ NQ [] y.2)
    (hSc : ∀ y ∈ (A8.evRun rep ev σ).1, SInvB.ScInv y.2)
    (hVI : ∀ y ∈ (A8.evRun rep ev σ).1, SInvI.ValidIdle y.2)
    (hAW : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, AW y2.2)
    (hCS : ∀ y ∈ (A8.evRun rep ev σ).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
      ∃ x n, y2.2.kheap y2.2.curSc = some (.schedContext x n)) :
    ∀ r ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  refine kcall_rdyOff9b rep ev σ hEF (fun c e v hv hvt y hy => ?_) hEvO hSc (fun y hy y2 hy2 => ?_)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hOsB c e v hv hvt y hy
    exact ⟨⟨hRdB c e v hv hvt y hy, h1, h2, h3, h4⟩, h5⟩
  · exact xs_of (SInvB.si_fl4Awaken y.2 (hSc y hy) y2 hy2) (vi_awaken y.2 (hVI y hy) y2 hy2) (hAW y hy y2 hy2)
      (hCS y hy y2 hy2)

/-- **The syscall entry**: the same through the FaultIP write (the
hypotheses at its outcome). -/
theorem kentry_rdyOff2 (rep : Bool) (c : Syscall) (σ : State Unit) (h : A8.EF σ)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      RdBody rep c w.2 ∧ OsBody rep c w.2 ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SInvB.ScInv y.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, SInvI.ValidIdle y.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1, AW y2.2) ∧
      (∀ y ∈ (A8.evRun rep (.syscallEvent c) w.2).1, ∀ y2 ∈ (fl4Awaken (Z := Unit) y.2).1,
        ∃ x n, y2.2.kheap y2.2.curSc = some (.schedContext x n))) :
    ∀ r ∈ (fl4KernelEntrySyscall (Z := Unit) rep c σ).1, Rdy r.2 ∧ Sched.OffReady r.2 ∧ CAx r.2 := by
  intro r ⟨y1, h1, hr⟩
  obtain rfl := Set.mem_singleton_iff.1 h1
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨hR, hO, hSc, hVI, hAW, hCS⟩ := hW w hw
  exact kcall_rdyOff2 rep _ w.2 (fun _ e => by cases e; exact A8.ef_fip h w hw) (fun _ e => by cases e; exact hR)
    (fun _ e => by cases e; exact hO) (fun hne => absurd rfl (hne c)) hSc hVI hAW hCS r hr

end

end Fl4Proofs.P3.SInvR.A9
