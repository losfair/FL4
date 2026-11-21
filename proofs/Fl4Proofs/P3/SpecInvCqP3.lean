/-
P3 (DESIGN.md §9), invariant line G1 (ctq19): **the ready-queue bundle at
boot** (spec side only, outside the JAtZ cone): ctq5's `EX` (SchedQ by
`boot_schedQ`, CtQ / Simple from the empty ready queues and
`resume_cur_thread`, CurScT as SpecInvAll's `boot_curScT`), ctq6's `RB`
(`boot_rb`) and ctnq1's `T4` (`boot_t4`) at Fl4Spec's `initASt`; and the
tops with `SInvB` (g1c) carried: **`kentry_tqB`** / **`kcall_tqB`** take, besides
the bundle `EX ∧ RB ∧ T4` itself, only `hnd` [P] and SInvB's own per-entry
premise (`ct ≠ idle`, for every event but the interrupt). The shell facts of
the syscall events (sl3's `Js`, `EF`, sb2's `EntryOK`, nq3's `Iu`, il2's `IL`)
come from SInvB by sl4's `sl_entryFacts`, ct active from g1a's `EntryJ` /
`EntryJEv`, `NQ [ct]` from NtfnQB / EpQB and ct's state (as sl4's
`kcall_scLive`).
-/
import Fl4Proofs.P3.SpecInvCqP2
import Fl4Proofs.P3.SpecInvQDom
import Fl4Proofs.P3.SpecInvAllB
open Classical

namespace Fl4Proofs.P3.SInvQ.P19
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL

noncomputable section

/-- CurScT at boot: the idle thread is bound to the idle SC, `cur_sc`. -/
theorem boot_curScT' : CurScT (initASt (Z := Unit)) := by
  intro x hx
  change initKheap idleThreadPtr = some (.tcb x) at hx
  exact (SInvB.init_tcb hx).2

/-- **ctq5's `EX` at boot.** -/
theorem boot_ex : EX (initASt (Z := Unit)) :=
  ⟨boot_schedQ, ⟨fun _ _ h => by simp [initASt] at h, ⟨fun _ h => by simp [initASt] at h, boot_curScT'⟩⟩⟩

/-- **The ready-queue bundle at boot**: `EX`, `RB` and `T4`. -/
theorem boot_tq : EX (initASt (Z := Unit)) ∧ RB (initASt (Z := Unit)) ∧ T4 (initASt (Z := Unit)) :=
  ⟨boot_ex, boot_rb true, boot_t4⟩

/-! ## The tops with `SInvB` carried -/

/-- sl4's `SlE` from `SInvB`. -/
theorem slE_of {σ : State Unit} (h : SInvAll.SInvB σ) : SlE σ :=
  ⟨h.1.1.ut, h.1.1.vfh, ⟨h.1.1.sg, h.1.1.idleOut⟩, ⟨h.1.1.nq, h.1.1.epq⟩, h.1.1.live, scKind_of_R h.1.1.sl.2⟩

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across the syscall entry, `SInvB` carried.**
Premises: `hnd` [P], `hct : ct ≠ idle` (SInvB's own, `kentry_sinvB`), the bundle. -/
theorem kentry_tqB (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvAll.SInvB σ)
    (hct : σ.curThread ≠ σ.idleThread) (hX : EX σ) (hR : RB σ) (h4 : T4 σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, EX y.2 ∧ RB y.2 := by
  have hA := h.1.1
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ h hct).ctAct
  obtain ⟨hJ, hEF, hEO, hIu⟩ := sl_entryFacts c hA.sl.1 (slE_of h) ⟨x0, hx0, ha0⟩
    (fun _ => ctSc_of_curScT hX.2.2.2)
  exact kentry_tq hnd c hX hR h4 hA.vi hEO h.1.2
    (SInvAll.act_all (P := fun x => activeSt x.tcbState) ⟨x0, hx0, ha0⟩) hIu hJ.1.2.1 hJ hEF rfl hA.idleOut
    hA.idleOut hA.sl.1.2.1

set_option maxHeartbeats 4000000 in
/-- **The ready-queue bundle across every kernel event, `SInvB` carried.**
Premises: `hnd` [P], `hev : ev ≠ interrupt → ct ≠ idle` (SInvB's own,
`kcall_sinvB`), the bundle. -/
theorem kcall_tqB (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvAll.SInvB σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hX : EX σ) (hR : RB σ) (h4 : T4 σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, EX y.2 ∧ RB y.2 := by
  have hA := h.1.1
  have hE := slE_of h
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJEv h hev).ctAct
  have hN : NQ [σ.curThread] σ := by
    refine nq_cons ((nq_nil_iff σ).2 ⟨hA.nq, hA.epq⟩) fun x hx => ?_
    rw [hx0] at hx; cases hx
    rcases ha0 with h1 | ⟨-, h1⟩
    · exact ok_of_active h1
    · rw [h1]; exact ⟨fun h => h, rfl⟩
  refine kcall_tq (I := idleP σ) (d := ∃ c, ev = .syscallEvent c ∧ SInvI.Pinned c) (Nq := σ.interruptIrqNode)
    hnd rep ev hX hR h4 hA.vi (entryOK_of hA.sl.1 hE) h.1.2
    (SInvAll.act_all (P := fun x => activeSt x.tcbState ∨ ev = .interrupt)
      ⟨x0, hx0, ha0.imp id And.left⟩) hN hA.idleOut hA.sl.1.2.1 ?_
  intro c e
  subst e
  have ha1 : activeSt x0.tcbState := ha0.resolve_right fun ⟨e, _⟩ => by cases e
  obtain ⟨hJ, hEF, -, hIu⟩ := sl_entryFacts c hA.sl.1 hE ⟨x0, hx0, ha1⟩ (fun _ => ctSc_of_curScT hX.2.2.2)
  refine ⟨hIu, hJ.1.2.1, js_weak (fun h' => ?_) hJ, hEF, rfl, hA.idleOut⟩
  obtain ⟨c', e', hp⟩ := h'
  cases e'
  exact hp

end

end Fl4Proofs.P3.SInvQ.P19
