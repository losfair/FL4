/-
P3 (DESIGN.md §9), invariant line G1 (g1d): **the ready-queue bundle added to
`SInvB`** (spec side only, outside the JAtZ cone). Composed only from the
existing tops; nothing is re-proved.

* `SInvCQ σ := SInvB σ ∧ EX σ ∧ RB σ ∧ T4 σ` (g1c's SInvB, ctq5's `EX`,
  ctq6's `RB`, ctnq1's `T4`): **carried** across the syscall entry and every
  event (`kentry_sinvCQ` / `kcall_sinvCQ`: g1c's `kentry_sinvB` / `kcall_sinvB`,
  ctq19's `kentry_tqB` / `kcall_tqB`, SpecInvQDom's `kentry_t4` / `kcall_t4`)
  and at boot (`boot_sinvCQ`: `boot_sinvB`, `boot_tq`). Premises exactly
  `hnd : numDomains = 1` [P] and SInvB's own per-entry `ct ≠ idle`.
* `SInvC σ := SInvCQ σ ∧ RPos σ` (epq2's `RPos`): `boot_sinvC` holds. **Not
  carried yet**: epq2's `kentry_rpos` / `kcall_rpos` read `RV`, a conjunct of
  rd's `SInvR.Rdy` (only `Rdy.2.2.2.1` is used), which `SInvC` does not
  supply (the rd line is still finishing `Rdy`). `kentry_sinvC_ofRdy` /
  `kcall_sinvC_ofRdy` show that `Rdy σ` at the entry is the only thing missing;
  they take it **by name** as the open gap, not as a premise of the bundle.
* `SInvCQ.ctQ`: the current thread is in no ready queue (l4v
  `ct_not_in_q`), = `EX`'s `CtQ`; it is `kernel_entryJ30`'s `hQ`.
-/
import Fl4Proofs.P3.SpecInvCqP3
import Fl4Proofs.P3.SpecInvEqS
open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec Fl4Proofs.P3.SInvQ

noncomputable section

/-- **`SInvB` with the ready-queue bundle** (`EX ∧ RB ∧ T4`). -/
abbrev SInvCQ (σ : State Unit) : Prop := SInvB σ ∧ EX σ ∧ RB σ ∧ T4 σ

/-- **`SInvCQ` with epq2's `RPos`** (the brief's `SInvC`). -/
abbrev SInvC (σ : State Unit) : Prop := SInvCQ σ ∧ SInvE.RPos σ

/-- l4v `ct_not_in_q`: `EX`'s `CtQ`. -/
theorem SInvCQ.ctQ {σ : State Unit} (h : SInvCQ σ) : ∀ d p, σ.curThread ∉ σ.readyQueues d p :=
  h.2.1.2.1

theorem SInvC.ctQ {σ : State Unit} (h : SInvC σ) : ∀ d p, σ.curThread ∉ σ.readyQueues d p :=
  h.1.ctQ

set_option maxHeartbeats 1000000 in
/-- **`SInvCQ` across the syscall entry.** Premises: `hnd` [P], `hct : ct ≠ idle`
(SInvB's own, `kentry_sinvB`). -/
theorem kentry_sinvCQ (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvCQ σ)
    (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvCQ y.2 := fun y hy =>
  have hq := P19.kentry_tqB hnd c h.1 hct h.2.1 h.2.2.1 h.2.2.2 y hy
  ⟨kentry_sinvB hnd c h.1 hct y hy, hq.1, hq.2, kentry_t4 hnd h.2.2.2 y hy⟩

set_option maxHeartbeats 1000000 in
/-- **`SInvCQ` across every kernel event.** Premises: `hnd` [P], `hev : ev ≠
interrupt → ct ≠ idle` (SInvB's own, `kcall_sinvB`). -/
theorem kcall_sinvCQ (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvCQ σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvCQ y.2 := fun y hy =>
  have hq := P19.kcall_tqB hnd rep ev h.1 hev h.2.1 h.2.2.1 h.2.2.2 y hy
  ⟨kcall_sinvB hnd rep ev h.1 hev y hy, hq.1, hq.2, kcall_t4 hnd rep ev h.2.2.2 y hy⟩

/-- **`SInvCQ` at boot.** -/
theorem boot_sinvCQ : SInvCQ (initASt (Z := Unit)) := ⟨boot_sinvB, P19.boot_tq⟩

/-- **`SInvC` at boot** (`boot_rpos`). -/
theorem boot_sinvC : SInvC (initASt (Z := Unit)) := ⟨boot_sinvCQ, SInvE.boot_rpos⟩

/-- **The open gap, by name**: `SInvC` across the syscall entry given rd's
`Rdy σ` (only its `RV` is read, by epq2's `kentry_rpos`). Not a top of the
bundle: it becomes `kentry_sinvC` once `Rdy` (or `RV`) is a field. -/
theorem kentry_sinvC_ofRdy (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvC σ)
    (hct : σ.curThread ≠ σ.idleThread) (hRd : SInvR.Rdy σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvC y.2 := fun y hy =>
  ⟨kentry_sinvCQ hnd c h.1 hct y hy, SInvE.kentry_rpos true c h.2 hRd h.1.1.1.1.scInv y hy⟩

/-- **The open gap, by name**, for every event (as `kentry_sinvC_ofRdy`). -/
theorem kcall_sinvC_ofRdy (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvC σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hRd : SInvR.Rdy σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvC y.2 := fun y hy =>
  ⟨kcall_sinvCQ hnd rep ev h.1 hev y hy, SInvE.kcall_rpos rep ev h.2 hRd h.1.1.1.1.scInv y hy⟩

end

end Fl4Proofs.P3.SInvAll
