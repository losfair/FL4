/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, g1c): **`SInvB` = g1b's
`SInvA'` with `OnlyIdle` carried** (spec side only, namespace SInvAll, outside
the JAtZ cone).

* `SInvB σ := SInvA' σ ∧ OnlyIdle σ` (`SInvA' = SInvA ∧ CtExit`, SpecInvAllC).
* `kentry_sinvB (hnd : numDomains = 1) c (h : SInvB σ) (hct : ct ≠ idle)`;
  `kcall_sinvB hnd rep ev h (hev : ev ≠ .interrupt → ct ≠ idle)` (every event);
  `kcall_sinvB_sys`; `boot_sinvB : SInvB initASt` (non-vacuity).
* The only per-entry facts left: `hnd` [P] (g1a: `kernelConfig` is opaque) and
  `ct ≠ idle` (a syscall / trap / fault comes from a user thread; `JReach.step`
  has it; an interrupt may arrive in the idle thread). g1b's `hoi` [J] is gone
  (SpecInvAllO: `kentry_onlyIdle` / `kcall_onlyIdle`).
* `SInvB.entryJ` / `SInvB.entryJEv`: g1a's `EntryJ` / `EntryJEv` from the bundle.
-/
import Fl4Proofs.P3.SpecInvAllO

open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

/-- **`SInvB`**: g1a's bundle, the exit fact and `only_idle`. -/
abbrev SInvB (σ : State Unit) : Prop := SInvA' σ ∧ OnlyIdle σ

theorem SInvB.entryJ {σ : State Unit} (h : SInvB σ) (hct : σ.curThread ≠ σ.idleThread) : EntryJ σ :=
  entryJ_of h.1.2 hct h.2

theorem SInvB.entryJEv {ev : Event} {σ : State Unit} (h : SInvB σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) : EntryJEv ev σ :=
  entryJEv_of h.1.2 hev h.2

/-- **`SInvB` across the syscall entry.** Premises: `hnd` [P], `hct : ct ≠ idle`. -/
theorem kentry_sinvB (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvB σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvB y.2 :=
  fun y hy => ⟨kentry_sinvA' hnd c h.1 hct h.2 y hy, kentry_onlyIdle c h.2 y hy⟩

/-- **`SInvB` across every kernel event.** Premises: `hnd` [P],
`hev : ev ≠ interrupt → ct ≠ idle`. -/
theorem kcall_sinvB (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvB σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvB y.2 :=
  fun y hy => ⟨kcall_sinvA' hnd rep ev h.1 hev h.2 y hy, kcall_onlyIdle rep ev h.2 y hy⟩

theorem kcall_sinvB_sys (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit} (h : SInvB σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) σ).1, SInvB y.2 :=
  kcall_sinvB hnd rep _ h fun _ => hct

/-- **`SInvB` at boot** (non-vacuity). -/
theorem boot_sinvB : SInvB (initASt (Z := Unit)) := ⟨boot_sinvA', boot_onlyIdle⟩

end

end Fl4Proofs.P3.SInvAll
