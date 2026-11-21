/-
P3 (DESIGN.md §9), invariant line G1 (rd8w, KENTRY-PLAN rd8v handoff 2):
**the readiness line at the bundle level** (spec side only, outside the JAtZ
cone).

* **`RdL σ := Rdy σ ∧ OffReady σ ∧ CAx σ`** (what the rdyOff line concludes),
  **`SInvW σ := SInvCRBV σ ∧ RdL σ`**, `boot_sinvW` (non-vacuity only).
* Every entry fact of rd8w A's `kcall_rdyOffX` / `kentry_rdyOffX` and of
  rd14c's `kcall_sinvCRBI` / `kentry_sinvCRBI` is a projection of `SInvW` (and
  the event-scope `ct ≠ idle`): **`ef_ofW`** (rd8a's `EF`), **`efi_ofW`**
  (rd10's `EFI`), **`ev10_ofW`**, **`uf_ofW`** (rd8n's `UF`: ut8's `UtInv''`,
  sl's `ScLiveT`, sg's `IdleOutV`), **`scLive_ofW`** (sb2's `ScLive` [J] from
  sl's typed form), `nq_ofW` / `ha_ofW` / `sysF_ofW` (ctq19's `kcall_tqB`
  construction).
* Tops **`kcall_rdyOffW`** / **`kentry_rdyOffW`**: `SInvW` at the entry, the
  run-pinned perform-arm inputs `QR` / `QF` with bridges `BrR` / `BrF` (rd8w A;
  rd14c's `InvRc` / `InvFc`, rd14d's `ArmAK` / `ArmAKB` forms), conclusion `SInvW` after (`RdL` by `kcall_rdyOffX`,
  `SInvCRB` by rd14c's `kcall_sinvCRBI` with rd's `CAx` at every exit taken
  from that conclusion, `VB` by rd8v's `kcall_vb`).
* `kcall_rdyOffWc` / `kentry_rdyOffWc` (rd14c's interface, any `CR` / `CF`),
  `kcall_rdyOffW14c` (today's `C14c` / `CovC`);
* **`kcall_rdyOffW_all`** / **`kentry_rdyOffW_all`**: once the covered sets
  are everything (`ArmA (fun _ => True)`, `ArmF (fun _ => True)`: rd14d's
  remaining arms), `InvRc` / `InvFc` hold trivially (`invRc_true`,
  `invFc_true`) and the tops have no run-pinned input.
-/
import Fl4Proofs.P3.SpecInvRd8wA
open Classical

namespace Fl4Proofs.P3.SInvR.B8w
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif
open Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvQ.P17 Fl4Proofs.P3.SInvQ.P19

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The bundle -/

/-- **What the readiness line concludes** (rd5 / rd7 / rd8t's tops). -/
abbrev RdL (σ : State Unit) : Prop := Rdy σ ∧ Sched.OffReady σ ∧ CAx σ

/-- **rd8v's `SInvCRBV` with the readiness line.** -/
abbrev SInvW (σ : State Unit) : Prop := B8v.SInvCRBV σ ∧ RdL σ

/-- **`SInvW` at boot** (non-vacuity only). -/
theorem boot_sinvW : SInvW (initASt (Z := Unit)) :=
  ⟨B8v.boot_sinvCRBV, boot_rdy, SInvV.boot_offReady, boot_cAx⟩

/-! ## The entry facts as projections -/

variable {σ : State Unit}

theorem SInvW.sb (h : SInvW σ) : SInvAll.SInvB σ := h.1.1.1.1.1

theorem SInvW.a (h : SInvW σ) : SInvAll.SInvA σ := h.1.1.1.1.1.1.1

theorem entryOK_ofW (h : SInvW σ) : SInvB.EntryOK σ := entryOK_of h.a.sl.1 (slE_of h.sb)

/-- **rd8a's `EF`** at a state with ct ≠ idle. -/
theorem ef_ofW (h : SInvW σ) (hni : σ.curThread ≠ σ.idleThread) : A8.EF σ :=
  ⟨h.2.1, h.2.2.1, h.a.vmt, h.a.scInv, h.a.cs, h.sb.1.2, h.1.1.1.1.2.1.2.1, h.1.1.1.1.2.1.2.2.1,
    h.1.1.1.1.2.2.1.2, h.1.1.1.1.2.2.1.1.2.2, h.2.2.2, hni, (nq_nil_iff σ).2 ⟨h.a.nq, h.a.epq⟩⟩

/-- **rd10's `EFI`** (any current thread). -/
theorem efi_ofW (h : SInvW σ) : A10.EFI σ :=
  ⟨h.2.1, h.2.2.1, h.a.vmt, h.a.scInv, h.a.cs, h.sb.1.2, h.1.1.1.1.2.1.2.1, h.1.1.1.1.2.1.2.2.1,
    h.1.1.1.1.2.2.1.2, h.1.1.1.1.2.2.1.1.2.2, h.2.2.2, (nq_nil_iff σ).2 ⟨h.a.nq, h.a.epq⟩, h.a.vi⟩

theorem ev10_ofW (h : SInvW σ) : A10.EV10 σ := ⟨entryOK_ofW h, h.a.vi, h.a.idleOut, h.a.idleSc⟩

/-- **rd8n's `UF`**: ut8's `UtInv''`, sl's `ScLiveT`, sg's `IdleOutV`. -/
theorem uf_ofW (h : SInvW σ) : B8n.UF σ := ⟨h.a.ut.1, h.a.sl.1.1, h.a.idleOut⟩

/-- **sb2's `ScLive` [J]** from sl's typed form (`scLive_of`). -/
theorem scLive_ofW (h : SInvW σ) : SInvB.ScLive σ := scLive_of h.a.sl.1.1 h.a.idleOut h.a.sl.1.2.1

/-- ctq19's `kcall_tqB` construction: ct's state and `NQ [ct]`. -/
theorem nq_ofW {ev : Event} (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState ∨ ev = .interrupt) ∧ NQ [σ.curThread] σ := by
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJEv h.sb hev).ctAct
  refine ⟨SInvAll.act_all (P := fun x => activeSt x.tcbState ∨ ev = .interrupt)
    ⟨x0, hx0, ha0.imp id And.left⟩, ?_⟩
  refine nq_cons ((nq_nil_iff σ).2 ⟨h.a.nq, h.a.epq⟩) fun x hx => ?_
  rw [hx0] at hx; cases hx
  rcases ha0 with h1 | ⟨-, h1⟩
  · exact ok_of_active h1
  · rw [h1]; exact ⟨fun h => h, rfl⟩

/-- ctq19's `kcall_tqB` construction: the shell facts of a syscall event. -/
theorem sysF_ofW {ev : Event} (h : SInvW σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ c, ev = .syscallEvent c →
      SysF (idleP σ) (∃ c, ev = .syscallEvent c ∧ SInvI.Pinned c) σ.interruptIrqNode σ := by
  intro c e
  subst e
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJEv h.sb hev).ctAct
  have ha1 : activeSt x0.tcbState := ha0.resolve_right fun ⟨e, _⟩ => by cases e
  obtain ⟨hJ, hEF, -, hIu⟩ := sl_entryFacts c h.a.sl.1 (slE_of h.sb) ⟨x0, hx0, ha1⟩
    (fun _ => ctSc_of_curScT h.1.1.1.1.2.1.2.2.2)
  refine ⟨hIu, hJ.1.2.1, js_weak (fun h' => ?_) hJ, hEF, rfl, h.a.idleOut⟩
  obtain ⟨c', e', hp⟩ := h'
  cases e'
  exact hp

/-! ## The tops -/

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across every kernel event.** Entry: `SInvW σ`, the event scope
`ev ≠ interrupt → ct ≠ idle` (l4v `ct_running ∨ (Interrupt ∧ ct_idle)`), `hnd`
[P]; run-pinned: the perform-arm inputs `QR` / `QF` with their bridges to rd12b's
`InvR` / rd14b's `InvF` (rd14c: `InvRc CR` / `InvFc CF`, `brR_c` / `brF_c`;
rd14d: its `ArmAK` / `ArmAKB` forms). -/
theorem kcall_rdyOffW (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    {QR QF : Syscall → State Unit → Prop} (bR : BrR QR) (bF : BrF QF)
    (hP : ∀ c, ev = .syscallEvent c → QR c σ) (hF : ∀ c, ev = .syscallEvent c → QF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 := by
  have hE : ∀ c, ev = .syscallEvent c → A8.EF σ := fun c e => ef_ofW h (hev (by rw [e]; intro h; cases h))
  obtain ⟨ha, hN⟩ := nq_ofW h hev
  have hRO := kcall_rdyOffX hnd rep ev σ (fun hi => ef_ofW h (hev hi)) (fun _ => efi_ofW h) (ev10_ofW h)
    h.1.1.1.1.2.1 h.1.1.1.1.2.2.1 h.1.1.1.1.2.2.2 h.sb.1.2 ha hN (sysF_ofW h hev) h.1.1.1.2 h.1.2 (uf_ofW h)
    h.1.1.2 h.a.cnDom bR bF hP hF
  intro y hy
  exact ⟨⟨A14c.kcall_sinvCRBI hnd rep ev h.1.1 hev (fun r hr => (hRO r hr).2.2) h.a.scInv (scLive_ofW h)
      h.a.idleSc h.2.2.2 (fun c e => ⟨hE c e, bF c σ (hE c e) (hF c e)⟩) y hy,
    B8v.kcall_vb rep ev h.1.2 h.a.scInv y hy⟩, hRO y hy⟩

set_option maxHeartbeats 4000000 in
/-- **`SInvW` across the syscall entry.** Entry: `SInvW σ`, ct ≠ idle, `hnd`
[P]; run-pinned at the FaultIP outcome: `QR` / `QF` with their bridges. -/
theorem kentry_rdyOffW (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ)
    (hct : σ.curThread ≠ σ.idleThread)
    {QR QF : Syscall → State Unit → Prop} (bR : BrR QR) (bF : BrF QF)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, QR c w.2 ∧ QF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 := by
  have hE := ef_ofW h hct
  obtain ⟨x0, hx0, ha0⟩ := (SInvAll.SInvB.entryJ h.sb hct).ctAct
  obtain ⟨hJ, hEF, -, hIu⟩ := sl_entryFacts c h.a.sl.1 (slE_of h.sb) ⟨x0, hx0, ha0⟩
    (fun _ => ctSc_of_curScT h.1.1.1.1.2.1.2.2.2)
  have hRO := kentry_rdyOffX hnd true c σ hE (ev10_ofW h) h.1.1.1.1.2.1 h.1.1.1.1.2.2.1 h.1.1.1.1.2.2.2
    h.sb.1.2 (SInvAll.act_all (P := fun x => activeSt x.tcbState) ⟨x0, hx0, ha0⟩) hIu hJ.1.2.1 hJ hEF rfl
    h.a.idleOut h.1.1.1.2 h.1.2 (uf_ofW h) h.1.1.2 h.a.cnDom bR bF hW
  intro y hy
  exact ⟨⟨A14c.kentry_sinvCRBI hnd c h.1.1 hct (fun r hr => (hRO r hr).2.2) h.a.scInv (scLive_ofW h)
      h.a.idleSc h.2.2.2 hE (fun w hw => bF c w.2 (A8.ef_fip hE w hw) (hW w hw).2) y hy,
    B8v.kentry_vb true c h.1.2 h.a.scInv y hy⟩, hRO y hy⟩

/-! ## Instances: rd14c's covered sets, and full coverage -/

/-- **`kcall_rdyOffW` for rd14c's interface** (`InvRc CR` / `InvFc CF`; today
`CR := C14c`, `CF := CovC`). -/
theorem kcall_rdyOffWc {CR CF : Fl4Invocation → Prop} (hAR : A14c.ArmA CR) (hAF : A14c.ArmF CF)
    (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc CR c σ) (hF : ∀ c, ev = .syscallEvent c → A14c.InvFc CF c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffW hnd rep ev h hev (brR_c hAR) (brF_c hAF) hP hF

/-- **`kentry_rdyOffW` for rd14c's interface.** -/
theorem kentry_rdyOffWc {CR CF : Fl4Invocation → Prop} (hAR : A14c.ArmA CR) (hAF : A14c.ArmF CF)
    (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, A14c.InvRc CR c w.2 ∧ A14c.InvFc CF c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffW hnd c h hct (brR_c hAR) (brF_c hAF) hW

/-- **The tops as they stand today** (rd14c's `C14c` / `CovC`). -/
theorem kcall_rdyOffW14c (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread)
    (hP : ∀ c, ev = .syscallEvent c → A14c.InvRc A14c.C14c c σ)
    (hF : ∀ c, ev = .syscallEvent c → A14c.InvFc A14c.CovC c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffWc A14c.armA_c14c A14c.armF_covC hnd rep ev h hev hP hF

theorem invRc_true (c : Syscall) (σ : State Unit) : A14c.InvRc (fun _ => True) c σ :=
  fun _ _ _ => ⟨fun _ _ _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ => Or.inl trivial,
    fun _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ => Or.inl trivial⟩

theorem invFc_true (c : Syscall) (σ : State Unit) : A14c.InvFc (fun _ => True) c σ :=
  fun _ _ _ _ _ _ _ _ => fun _ _ _ _ _ _ _ _ _ _ => Or.inl trivial

/-- **`kcall_rdyOffW` once every perform arm is covered** (the target of rd14d /
rd14e): no run-pinned input. -/
theorem kcall_rdyOffW_all (hAR : A14c.ArmA fun _ => True) (hAF : A14c.ArmF fun _ => True)
    (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvW y.2 :=
  kcall_rdyOffWc hAR hAF hnd rep ev h hev (fun c _ => invRc_true c σ) (fun c _ => invFc_true c σ)

/-- **`kentry_rdyOffW` once every perform arm is covered.** -/
theorem kentry_rdyOffW_all (hAR : A14c.ArmA fun _ => True) (hAF : A14c.ArmF fun _ => True)
    (hnd : numDomains = 1) (c : Syscall) (h : SInvW σ) (hct : σ.curThread ≠ σ.idleThread) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvW y.2 :=
  kentry_rdyOffWc hAR hAF hnd c h hct fun w _ => ⟨invRc_true c w.2, invFc_true c w.2⟩

end

end Fl4Proofs.P3.SInvR.B8w
