/-
P3 (DESIGN.md §9), INV-PLAN §4 **G1 assembly** (g1a): the carried spec invariant
`SInvA σ` of every FINISHED G1 field, kept by the syscall entry and by every
kernel event, composed from the existing whole-entry tops (no new field proof).
Spec side only (outside the `JAtZ` cone); namespace `Fl4Proofs.P3.SInvAll`.

* **`SInvA σ`** bundles (l4v counterpart, line that proved the top):
  `VfhAll ∧ CnDom` (valid_tcb fault handler slice; vfh3), `FaultTcbsS ∧ NQB`
  (fault_tcbs_valid_states + valid_ntfn queue slice; ft3), `NativeScopeS` ([S]
  no VT-x state; invA), `SpecGlobS ∧ IdleOutV` (valid_irq_node / valid_global_refs;
  sg1), `DomListOK` (valid_domain_list; invC), `ValidIrqMasks ∧ ValidIrqHandlers`
  (valid_irq_masks / valid_irq_handlers; vih3), `ValidMachineTime`
  (valid_machine_time; invB), `UtInv3` (untyped invariants; ut8),
  `NtfnQB ∧ EpQB ∧ IfLiveT` (valid_ntfn / valid_ep queues, if_live_then_nonz_cap at
  TCBs; nq3 / il2), `ValidIdle` (valid_idle; vi3), `FT` (valid_cur_fpu, carried
  form; fo1), `SlB2 = (ScLiveT ∧ IdleScOutV ∧ NtfnScB ∧ ScInv) ∧ ScKindR` (sb2 / sl5),
  `CurScT` (cur_sc_tcb_are_bound; ctq5).
  Derived, not carried: `FpuOwnOKS` (`SInvA.fo`), `ScInv` (`SInvA.scInv`), vi3's
  `IdleScOutV` (`SInvA.idleSc`: sl's form, definitionally the same), vi2's `CtSc`
  (`SInvA.ctSc`, from `CurScT` by ctq5's `ctSc_of_curScT`), sl5's `SlE2`
  (`SInvA.slE`).
* **`EntryJ σ`** (syscall entry) / **`EntryJEv ev σ`** (any event): the only J-layer
  per-entry fact the tops read, `ctAct` [J] (l4v `ct_active`; for an interrupt l4v's
  `ct_running ∨ ct_idle`). ft3's `CtEntry` comes from it by nq1's `ctEntry_of`
  (`NtfnQB`), and its event form `CtEntryEv` by `ctEntryEv_of_J`. CtSc for the pinned
  syscalls is NOT a premise: it comes from the carried `CurScT`.
* `hnd : numDomains = 1` [P] (FL4's one-domain configuration; `kernelConfig` is
  opaque, so it is not provable here) is the one non-J premise: it is read only by
  invC's `DomListOK` tops (`DomListOK.dom` asks every schedule entry's domain to be 0,
  and the DomainSetStart decode checks `domain < numDomains`). It is the same
  constant as `JEntryGlob.nd` / INV-PLAN T11.
* **`kentry_sinvA hnd c h hJ : ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, SInvA y.2`**,
  **`kcall_sinvA hnd rep ev h hJ : ∀ y ∈ (fl4CallKernel rep ev σ).1, SInvA y.2`**,
  **`boot_sinvA : SInvA initASt`** (non-vacuity only, lead decision 2026-11-20: the
  induction starts from any state satisfying `SInvA`). New boot facts here:
  `boot_validIdle`, `boot_ifLiveT`, `boot_ntfnScB`, `boot_curScT`.
* **Slot for the fields still in progress** (NOT hypotheses of the tops): `OffReady` /
  `Rdy` (rd5), `SchedQ` / `CtNQR` (ctq7), `EpQAll` (epq1). Each will be added as a
  field of `SInvA` (or of a successor `SInvB ⊇ SInvA`) with its own whole-entry top,
  whose extra hypotheses must again be projections of the bundle or of `EntryJ`.
-/
import Fl4Proofs.P3.SpecInvAllV
import Fl4Proofs.P3.SpecInvVfhE
import Fl4Proofs.P3.SpecInvFaultTcbsH10
import Fl4Proofs.P3.SpecInvNativeScope
import Fl4Proofs.P3.SpecInvSgE
import Fl4Proofs.P3.SpecInvDom
import Fl4Proofs.P3.SpecInvValidIrqHandlersS
import Fl4Proofs.P3.SpecInvUtP6
import Fl4Proofs.P3.SpecInvNtfnQLX
import Fl4Proofs.P3.SpecInvViM
import Fl4Proofs.P3.SpecInvFoS
import Fl4Proofs.P3.SpecInvSlKV
import Fl4Proofs.P3.SpecInvCqW
import Fl4Proofs.P3.SpecInvSbE

open Classical

namespace Fl4Proofs.P3.SInvAll
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The bundle -/

/-- **The carried spec invariant of the finished G1 fields** (module docstring). -/
structure SInvA (σ : State Unit) : Prop where
  vfh : SInv.VfhAll σ
  cnDom : SInv.CnDom σ
  fts : SInv.FaultTcbsS σ
  nqb : SInv.NQB σ
  ns : SInv.NativeScopeS σ
  sg : SInvG.SpecGlobS σ
  idleOut : SInvG.IdleOutV σ
  dom : DomListOK σ
  vim : SInvV.ValidIrqMasks σ
  vih : SInvV.ValidIrqHandlers σ
  vmt : SInvV.ValidMachineTime σ
  ut : SInvU.UtInv3 σ
  nq : SInv.NtfnQB σ
  epq : SInv.EpQB σ
  live : SInv.IfLiveT σ
  vi : SInvI.ValidIdle σ
  ft : SInvF.FT σ
  sl : SInvL.SlB2 σ
  cs : SInvQ.CurScT σ

/-- **[J] The per-entry fact of a syscall entry.** -/
structure EntryJ (σ : State Unit) : Prop where
  /-- [J] l4v `ct_active` (with `cur_tcb`): the current thread is a TCB whose state is
  Running or Restart. True at every syscall entry: a thread traps only while running
  (the idle thread never traps, [S] event scope). -/
  ctAct : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ SInv.activeSt x.tcbState

/-- **[J] The per-entry fact of an event** (`fl4CallKernel rep ev`). -/
structure EntryJEv (ev : Event) (σ : State Unit) : Prop where
  /-- [J] l4v `ct_active` for traps and faults; for an interrupt l4v's
  `ct_running ∨ ct_idle` (an interrupt may arrive while the idle thread runs). -/
  ctAct : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧
    (SInv.activeSt x.tcbState ∨ (ev = .interrupt ∧ x.tcbState = .idleThreadState))

/-! ## Bridges -/

theorem act_all {σ : State Unit} {P : Tcb → Prop} (h : ∃ x, σ.kheap σ.curThread = some (.tcb x) ∧ P x) :
    ∀ x, σ.kheap σ.curThread = some (.tcb x) → P x := by
  obtain ⟨x0, h0, hp⟩ := h
  intro x hx
  rw [h0] at hx
  cases hx
  exact hp

theorem EntryJ.toEv {σ : State Unit} (hJ : EntryJ σ) (ev : Event) : EntryJEv ev σ := by
  obtain ⟨x, hx, ha⟩ := hJ.ctAct
  exact ⟨x, hx, Or.inl ha⟩

/-- ft3's `CtEntry` from `EntryJ` (nq1's `ctEntry_of`). -/
theorem ctEntry_of_J {σ : State Unit} (hJ : EntryJ σ) (hN : SInv.NtfnQB σ) : SInv.CtEntry σ :=
  SInv.ctEntry_of (act_all hJ.ctAct) hN

/-- ft3's `CtEntryEv ev` from `EntryJEv ev` (`ctEntryI_of` for the interrupt). -/
theorem ctEntryEv_of_J {ev : Event} {σ : State Unit} (hJ : EntryJEv ev σ) (hN : SInv.NtfnQB σ) :
    SInv.CtEntryEv ev σ := by
  have ha := act_all hJ.ctAct
  unfold SInv.CtEntryEv
  split
  · exact SInv.ctEntryI_of (fun x hx => (ha x hx).imp id And.right) hN
  · rename_i hne
    exact SInv.ctEntry_of (fun x hx => (ha x hx).resolve_right fun h => hne h.1) hN

/-- sl's `IdleScOutV` is vi3's (the same body). -/
theorem idleSc_L_I {σ : State Unit} (h : SInvL.IdleScOutV σ) : SInvI.IdleScOutV σ := h

theorem idleSc_I_L {σ : State Unit} (h : SInvI.IdleScOutV σ) : SInvL.IdleScOutV σ := h

theorem SInvA.idleSc {σ : State Unit} (h : SInvA σ) : SInvI.IdleScOutV σ := idleSc_L_I h.sl.1.2.1

theorem SInvA.scInv {σ : State Unit} (h : SInvA σ) : SInvB.ScInv σ := h.sl.1.2.2.2

theorem SInvA.fo {σ : State Unit} (h : SInvA σ) : SInvF.FpuOwnOKS σ := SInvF.fpuOwnOK_of_ft h.ft

/-- vi2's `CtSc` [J] is no premise: ctq5's `CurScT` gives it. -/
theorem SInvA.ctSc {σ : State Unit} (h : SInvA σ) : SInvI.CtSc σ := SInvQ.ctSc_of_curScT h.cs

theorem SInvA.slE {σ : State Unit} (h : SInvA σ) : SInvL.SlE2 σ :=
  ⟨h.ut, h.vfh, ⟨h.sg, h.idleOut⟩, ⟨h.nq, h.epq⟩, h.live⟩

/-! ## The tops -/

/-- **`SInvA` across the syscall entry.** Premises: the bundle, `hJ : EntryJ σ` [J]
(l4v `ct_active`) and `hnd : numDomains = 1` [P] (module docstring). -/
theorem kentry_sinvA (hnd : numDomains = 1) (c : Syscall) {σ : State Unit} (h : SInvA σ) (hJ : EntryJ σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, SInvA y.2 := by
  intro y hy
  have haF := act_all hJ.ctAct
  have hvf := SInv.kentry_vfhAll c h.vfh h.cnDom h.ut y hy
  have hft := SInv.kentry_faultTcbsS true c (ctEntry_of_J hJ h.nq) ⟨h.fts, h.nqb⟩ y hy
  have hns := SInv.kentry_nativeScope c h.ns y hy
  have hsg := SInvG.kentry_specGlob c h.sg h.idleOut h.ut y hy
  have hdom := SInvDom.kentry_domListOK hnd h.dom y hy
  have hvi := SInvV.kentry_validIrqMasks h.vim h.vih y hy
  have hvmt := SInvV.kentry_validMachineTime h.vmt y hy
  have hut := SInvU.kentry_utInv2 c h.ut y hy
  have hnq := SInv.kentry_nqIL true c hJ.ctAct ⟨h.nq, h.epq⟩ h.ut h.live y hy
  have hid := SInvI.kentry_validIdle c h.vi ⟨h.sg, h.idleOut⟩ h.idleSc h.ut haF (fun _ => h.ctSc) y hy
  have hfo := SInvF.kentry_fpuOwnOK true c hJ.ctAct ⟨h.nq, h.epq⟩ h.ut h.live h.ft y hy
  have hsl := SInvL.kentry_slB2 c h.sl h.slE hJ.ctAct (fun _ => h.ctSc) y hy
  have hcs := SInvQ.kentry_curScT c σ y hy
  exact ⟨hvf.1, hvf.2, hft.1, hft.2, hns, hsg.1, hsg.2, hdom, hvi.1, hvi.2, hvmt, hut, hnq.1, hnq.2.1,
    hnq.2.2, hid.1, hfo.2, hsl, hcs⟩

/-- **`SInvA` across every kernel event** (`fl4CallKernel rep ev`). Premises: the
bundle, `hJ : EntryJEv ev σ` [J] and `hnd` [P]. -/
theorem kcall_sinvA (hnd : numDomains = 1) (rep : Bool) (ev : Event) {σ : State Unit} (h : SInvA σ)
    (hJ : EntryJEv ev σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, SInvA y.2 := by
  intro y hy
  have haF := act_all hJ.ctAct
  have hvf := SInv.kcall_vfhAll rep ev h.vfh h.cnDom h.ut y hy
  have hft := SInv.kcall_faultTcbsS rep ev (ctEntryEv_of_J hJ h.nq) ⟨h.fts, h.nqb⟩ y hy
  have hns := SInv.kcall_nativeScope rep ev h.ns y hy
  have hsg := SInvG.kcall_specGlob rep ev h.sg h.idleOut h.ut y hy
  have hdom := SInvDom.dp_fl4CallKernel hnd rep ev σ y h.dom hy
  have hvi := SInvV.vi_fl4CallKernel rep ev σ ⟨h.vim, h.vih, trivial⟩ y hy
  have hvmt := kcall_validMachineTime rep ev h.vmt y hy
  have hut := SInvU.kcall_utInv2 rep ev h.ut y hy
  have hnq := SInv.kcall_nqIL rep ev hJ.ctAct ⟨h.nq, h.epq⟩ h.ut h.live y hy
  have hid := SInvI.kcall_validIdle rep ev h.vi ⟨h.sg, h.idleOut⟩ h.idleSc h.ut
    (fun x hx => (haF x hx).imp id And.left) (fun _ _ _ => h.ctSc) y hy
  have hfo := SInvF.kcall_fpuOwnOK rep ev hJ.ctAct ⟨h.nq, h.epq⟩ h.ut h.live h.ft y hy
  have hsl := SInvL.kcall_slB2 rep ev h.sl h.slE hJ.ctAct (fun _ _ _ => h.ctSc) y hy
  have hcs := SInvQ.kcall_curScT rep ev σ y hy
  exact ⟨hvf.1, hvf.2, hft.1, hft.2, hns, hsg.1, hsg.2, hdom, hvi.1, hvi.2.1, hvmt, hut, hnq.1, hnq.2.1,
    hnq.2.2, hid.1, hfo.2, hsl, hcs⟩

/-- The syscall entry as an event-level corollary: `kentry_sinvA` with `EntryJ`. -/
theorem kcall_sinvA_sys (hnd : numDomains = 1) (rep : Bool) (c : Syscall) {σ : State Unit} (h : SInvA σ)
    (hJ : EntryJ σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep (.syscallEvent c)) σ).1, SInvA y.2 :=
  kcall_sinvA hnd rep _ h (hJ.toEv _)

/-! ## Boot (non-vacuity only) -/

/-- **valid_idle at boot**: the idle TCB / SC of `initKheap`. -/
theorem boot_validIdle : SInvI.ValidIdle (initASt (Z := Unit)) := by
  obtain ⟨x0, h0, -⟩ := SInvB.initKheap_idleThread
  unfold SInvI.ValidIdle SInvI.VI SInvI.VIT
  refine ⟨rfl, rfl, fun e => absurd e Bool.false_ne_true, ⟨x0, h0⟩, ⟨_, 0, SInvV.initKheap_idleSc⟩, ?_⟩
  intro p o hp
  change initKheap p = some o at hp
  change SInvI.ObjOK idleThreadPtr idleScPtr idleThreadPtr p o
  cases o with
  | tcb x =>
    obtain ⟨rfl, -⟩ := SInvB.init_tcb hp
    unfold initKheap at hp
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self] at hp
    cases hp
    exact ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun e => absurd rfl e, fun _ => Option.some_ne_none _⟩
  | schedContext sc n =>
    obtain ⟨rfl, -, -⟩ := SInvB.init_sc hp
    rw [SInvV.initKheap_idleSc] at hp
    cases hp
    exact ⟨fun _ => ⟨rfl, rfl, by unfold validSchedContextSize minSchedContextBits untypedMaxBits; omega⟩,
      fun e => absurd rfl e⟩
  | endpoint ep =>
    exfalso
    unfold initKheap at hp
    simp only [Function.update_apply] at hp
    split_ifs at hp <;> cases hp
  | notification nt =>
    exfalso
    unfold initKheap at hp
    simp only [Function.update_apply] at hp
    split_ifs at hp <;> cases hp
  | _ => trivial

/-- **IfLiveT at boot**: the only TCB is the idle thread, which is not live. -/
theorem boot_ifLiveT : SInv.IfLiveT (initASt (Z := Unit)) := by
  intro t y ht hl
  change initKheap t = some (.tcb y) at ht
  obtain ⟨rfl, -⟩ := SInvB.init_tcb ht
  unfold initKheap at ht
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self] at ht
  cases ht
  exact False.elim hl

/-- **NtfnScB at boot** (no notification exists). -/
theorem boot_ntfnScB : SInvL.NtfnScB (initASt (Z := Unit)) := by
  intro n ntf c hn _
  exfalso
  change initKheap n = some (.notification ntf) at hn
  unfold initKheap at hn
  simp only [Function.update_apply] at hn
  split_ifs at hn <;> cases hn

/-- **CurScT at boot**: the idle thread is bound to the idle SC, `cur_sc`. -/
theorem boot_curScT : SInvQ.CurScT (initASt (Z := Unit)) := by
  intro x hx
  change initKheap idleThreadPtr = some (.tcb x) at hx
  exact (SInvB.init_tcb hx).2

/-- **`SInvA` at Fl4Spec's initial state** (non-vacuity of the bundle only). -/
theorem boot_sinvA : SInvA (initASt (Z := Unit)) where
  vfh := SInv.boot_vfhAll
  cnDom := SInv.boot_cnDom
  fts := SInv.boot_faultTcbsS
  nqb := SInv.boot_nqb
  ns := SInv.boot_nativeScope
  sg := SInvG.boot_specGlob.1
  idleOut := SInvG.boot_specGlob.2
  dom := SInvDom.domListOK_init
  vim := SInvV.boot_vim
  vih := SInvV.boot_vih
  vmt := SInvV.boot_vmt
  ut := SInvU.boot_utInv3
  nq := SInv.boot_ntfnQB
  epq := SInv.boot_epQB
  live := boot_ifLiveT
  vi := boot_validIdle
  ft := SInvF.boot_ft
  sl := ⟨⟨SInvL.boot_scLiveT, SInvL.boot_idleScOutV, boot_ntfnScB, SInvB.boot_scInv⟩, SInvL.boot_scKindR⟩
  cs := boot_curScT

end

end Fl4Proofs.P3.SInvAll
