/-
P3 (DESIGN.md §9), invariant line G1 (sl5): **the bundle with `ScKindR`** and
the tops without sl4's `SlE.kind` premise (spec side only).

* `boot_scKindR` (every cap of `initASt` is null; non-vacuity only, as the other
  boot lemmas).
* `SlB2 σ := SlB σ ∧ ScKindR σ`, `SlE2` (sl4's `SlE` without `kind`; `ScKind` is
  read off `ScKindR` by sl4's `scKind_of_R`).
* `kentry_slB2_of` / `kcall_slB2_of` / `kentry_scLive2_of` / `kcall_scLive2_of`
  (given SpecInvSlKE's `KrGap`, the retype performs). sl4's tops are kept.
-/
import Fl4Proofs.P3.SpecInvSlKE
open Classical

namespace Fl4Proofs.P3.SInvL
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 2000000

/-- **ScKindR at boot**: every cap of `initASt` is null. -/
theorem boot_scKindR : ScKindR (initASt (Z := Unit)) := by
  intro s r b s' c' h1 _ _
  exfalso
  have hc : capOpt ((initASt (Z := Unit)).kheap s.1) s.2 = some (.schedContextCap r b) := by
    rw [← vfh_capAt]; exact h1
  obtain ⟨o, l⟩ := s
  dsimp only at hc
  simp only [initASt, initKheap, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)

/-- The line's bundle with the range form of `ScKind`. -/
def SlB2 (σ : State Unit) : Prop := SlB σ ∧ ScKindR σ

/-- The other lines' carried facts the tops read (sl4's `SlE` without `kind`). -/
structure SlE2 (σ : State Unit) : Prop where
  ut : UtInv3 σ
  vfh : VfhAll σ
  sg : SInvG.SpecGlobS σ ∧ SInvG.IdleOutV σ
  nq : NtfnQB σ ∧ EpQB σ
  il : IfLiveT σ

theorem SlE2.toSlE {σ : State Unit} (hE : SlE2 σ) (hK : ScKindR σ) : SlE σ :=
  ⟨hE.ut, hE.vfh, hE.sg, hE.nq, hE.il, scKind_of_R hK⟩

/-- **ScLiveT ∧ NtfnScB kept by the syscall entry**, no `ScKind` premise. -/
theorem kentry_scLive2_of (hG : KrGap) (c : Syscall) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 :=
  kentry_scLive c h.1 (hE.toSlE h.2) ha hct

/-- **ScLiveT ∧ NtfnScB kept by every kernel event**, no `ScKind` premise. -/
theorem kcall_scLive2_of (hG : KrGap) (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ScLiveT (idleP y.2) y.2 ∧ NtfnScB y.2 :=
  kcall_scLive rep ev h.1 (hE.toSlE h.2) ha hct

/-- **The bundle `SlB ∧ ScKindR` kept by the syscall entry.** -/
theorem kentry_slB2_of (hG : KrGap) (c : Syscall) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ activeSt x.tcbState) (hct : SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SlB2 y.2 := fun y hy =>
  ⟨kentry_slB c h.1 (hE.toSlE h.2) ha hct y hy, kentry_scKindR_of hG c h.2 hE.ut y hy⟩

/-- **The bundle `SlB ∧ ScKindR` kept by every kernel event.** -/
theorem kcall_slB2_of (hG : KrGap) (rep : Bool) (ev : Event) {σ : State Unit} (h : SlB2 σ) (hE : SlE2 σ)
    (ha : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
      (activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState)))
    (hct : ∀ c, ev = .syscallEvent c → SInvI.Pinned c → SInvI.CtSc σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SlB2 y.2 := fun y hy =>
  ⟨kcall_slB rep ev h.1 (hE.toSlE h.2) ha hct y hy, kcall_scKindR_of hG rep ev h.2 hE.ut y hy⟩

end

end Fl4Proofs.P3.SInvL
