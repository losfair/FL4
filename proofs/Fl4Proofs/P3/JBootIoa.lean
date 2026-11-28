/-
P3 (line p3J, gen 5): **the jboot witness with one IOAPIC** — `kernel_entry_reachU38` / `U39` apply to the
witness platform with their start condition `IoaRel` met.

* **`warI1`**: jboot's witness arch `warI` (P2/WitPlat) with only `num_ioapics` / `ioapic_pins` changed: one
  IOAPIC (`num_ioapics = 1`) of 24 pins (`ioapic_pins i = 24` for `i < 1`, `0` otherwise, as FL4's
  `ioapic::pins`), i.e. FL4's x86_64 backend on a one-IOAPIC machine and the spec's `init_arch_state`
  (`x64_num_ioapics = 1`, `x64_ioapic_nirqs = ioapicIRQLines = 24`). `modelArch` / `warI` are not changed.
* **`jAtZ_w0I1`**, **`jReachU34_w0I1`**: jboot's start state at `warI1` (`ipiMR`). `JAtZ` names the arch only in
  `kern` (`JKern.tdx`, `TdxRel`: `tdx_active` / `dma_ram`, unchanged) and `utc` (`UtCapP3`, phantom); the other
  fields are jboot's, verbatim.
* **`u34_w0I1`**: every global premise of `kernel_entry_reachU34` at `wst` / `warI1` / `wAR` / `ipiMR` with
  `jReachU34_w0I1` (`u34_w0I`'s proof, renamed: no part of it reads the IOAPIC counts).
* **`warI1_ioaRel : IoaRel warI1 fInitASt`**; **`jReachU38_w0I1`**; **`u38_w0I1`**: every premise of
  `kernel_entry_reachU38` (= U34's global ones) with its start `jReachU38_w0I1`. Left: only the per-entry
  syscall / event [J]s in U38's conclusion antecedents (`KDispHypsKVU38`, `JDecMRLK`, `KFinAtR13`, `KFinEv13`).
* **`warI1_ioaMap : IoaMap warI1`** (U39's new global premise: `ioapic_map` / `ioapic_map_remapped` always answer
  `true`, as `modelArch`'s); **`u39_w0I1`**: every premise of `kernel_entry_reachU39` with its start.
* Contrast: **`warI_not_ioaRel : ¬ IoaRel warI fInitASt`** (`warI` answers 0 IOAPICs).

Named premises: **`OpaqueWK`** [P] (JBootU34: the opaque Fl4Spec constants) only. No [J], no [W].
Caveats (jboot's): idle-only boot, one core.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootU34
import Fl4Proofs.P3.XTopJointKEntryU39
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **The witness arch with one IOAPIC of 24 pins** (module docstring): `warI` with `num_ioapics` and
`ioapic_pins` set. -/
def warI1 : machine.Arch Fl4Spec.MachineState :=
  { warI with
    num_ioapics := fun _ => ok 1#u64
    ioapic_pins := fun _ i => ok (if i.val < 1 then 24#u64 else 0#u64) }

theorem warI1_total : P0.ArchTotal warI1 where
  private_device_frame _ _ := (WP.spec_ok _).2 trivial
  dma_ram _ _ _ := (WP.spec_ok _).2 trivial
  dma_frame _ _ _ _ := (WP.spec_ok _).2 trivial
  virtualization _ := (WP.spec_ok _).2 trivial
  vcpu_capability _ _ := (WP.spec_ok _).2 trivial
  vcpu_barrier _ := (WP.spec_ok _).2 trivial
  vcpu_sync _ _ _ := (WP.spec_ok _).2 trivial
  vcpu_release _ _ := (WP.spec_ok _).2 trivial
  invalidate_ept _ _ _ := (WP.spec_ok _).2 trivial
  tdx_active _ := (WP.spec_ok _).2 trivial
  tdx_report _ _ _ _ _ _ _ _ _ _ := (WP.spec_ok _).2 trivial
  tdx_extend_rtmr _ _ _ _ _ _ _ _ := (WP.spec_ok _).2 trivial
  tdx_get_quote _ _ _ := (WP.spec_ok _).2 trivial
  now _ := (WP.spec_ok _).2 trivial
  set_deadline _ _ := (WP.spec_ok _).2 trivial
  us_to_ticks _ _ := (WP.spec_ok _).2 trivial
  ticks_to_us _ _ := (WP.spec_ok _).2 trivial
  max_us _ := (WP.spec_ok _).2 trivial
  kernel_wcet_ticks _ := (WP.spec_ok _).2 trivial
  irq_pending _ := (WP.spec_ok _).2 trivial
  take_pending_irq _ := (WP.spec_ok _).2 trivial
  mask_irq _ _ _ := (WP.spec_ok _).2 trivial
  ack_irq _ _ := (WP.spec_ok _).2 trivial
  irq_free _ _ := (WP.spec_ok _).2 trivial
  set_vspace _ _ _ := (WP.spec_ok _).2 trivial
  invalidate_page _ _ _ := (WP.spec_ok _).2 trivial
  invalidate_asid _ _ := (WP.spec_ok _).2 trivial
  invalidate_page_structures _ _ := (WP.spec_ok _).2 trivial
  ioapic_map _ _ _ _ _ _ := (WP.spec_ok _).2 trivial
  ioapic_map_remapped _ _ _ _ _ _ _ := (WP.spec_ok _).2 trivial
  num_ioapics _ := (WP.spec_ok _).2 trivial
  ioapic_pins _ _ := (WP.spec_ok _).2 trivial
  port_in _ _ _ := (WP.spec_ok _).2 trivial
  port_out _ _ _ _ := (WP.spec_ok _).2 trivial
  fpu_flush _ _ := (WP.spec_ok _).2 trivial
  fpu_sanitise _ _ := (WP.spec_ok _).2 trivial
  fpu_reload _ _ := (WP.spec_ok _).2 trivial
  fpu_release _ _ := (WP.spec_ok _).2 trivial
  remote_stall _ _ := (WP.spec_ok _).2 trivial
  send_reschedule _ _ := (WP.spec_ok _).2 trivial
  putc _ _ := (WP.spec_ok _).2 trivial
  get_char _ := (WP.spec_ok _).2 trivial
  halt _ := (WP.spec_ok _).2 trivial

/-- `JKern` at `warI1`: `warI`'s, its TDX clause read through the unchanged `tdx_active` / `dma_ram`. -/
theorem w0_jkernI1 : JKern (L := wL) warI1 Hw Csw Dw thW w0 fInitASt :=
  { orig := w0_jkern.orig, cur := w0_jkern.cur, curT := w0_jkern.curT, act := w0_jkern.act,
    dwAl := w0_jkern.dwAl, dwObj := w0_jkern.dwObj, dwNe := w0_jkern.dwNe, head := w0_jkern.head,
    gpm := w0_jkern.gpm, ga := w0_jkern.ga, gf := w0_jkern.gf, heap := w0_jkern.heap, h0 := w0_jkern.h0,
    hks := w0_jkern.hks, hksIn := w0_jkern.hksIn, hnd := w0_jkern.hnd, ksbFit := w0_jkern.ksbFit,
    ksbAl := w0_jkern.ksbAl, nodeFit := w0_jkern.nodeFit, cpuCs := w0_jkern.cpuCs, curH := w0_jkern.curH,
    cscH := w0_jkern.cscH, csLt := w0_jkern.csLt, cs0 := w0_jkern.cs0, csN := w0_jkern.csN,
    tdx := w0_jkern.tdx }

/-- **`JAtZ.utc`** at `warI1` (vacuous: no slot holds an untyped cap). -/
theorem w0_utcI1 : ∀ sl p sb fi dev, AbsSlot thW sl →
    capAt (wL.mem w0) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := wL) warI1 thW w0 fInitASt Gw sl p sb fi := by
  intro sl p sb fi dev hs h _
  rw [capAt_slot hs.isSlot] at h
  cases ok_inj h

theorem jAtZ_w0I1 (a : MachineState) :
    JAtZ (L := wL) warI1 wAR Zw Hw Csw C0 (fun _ => []) Dw w0 a fInitASt where
  xtop :=
    { fin := ⟨⟨w0_othersRel a, w0_topPlaced⟩, w0_vsRel, w0_ptRel, w0_poolsIn, w0_curOK⟩
      rel := ⟨placed_thW, w0_crel, w0_finInv, w0_domRel, w0_mdbOKV, w0_ipcApart, w0_scApart⟩
      ipc := w0_ipc
      esa := w0_esa }
  call := w0_call
  rfree := w0_rfree
  rrecv := w0_rrecv
  yld := w0_yld
  mcp := w0_mcp
  buf := w0_buf
  ks := w0_ks
  thT := thT_thW
  thk := thk_thW
  ip := w0_ip
  rp := w0_rp
  apart := w0_apart
  nk := w0_nk
  nodeB := w0_nodeB
  jpl := w0_jpl
  cover := w0_cover
  obj := fInit_obj
  zH := w0_zH
  sfree := w0_sfree
  hset := w0_hset
  hscC := w0_hscC
  jcov := w0_jcov
  kern := w0_jkernI1
  del := w0_delInv
  ut := w0_utInv
  bound := w0_delBound
  finM := w0_finM
  utc := w0_utcI1
  nsc := fInit_nsc
  inv := fInit_inv
  cur := Or.inr fInit_curInv
  own := fInit_own
  off := fInit_off
  act := fInit_act
  c0 := w0_c0
  bsa := fInit_bsa
  sv := fInit_sv
  isorted := fInit_isorted
  slink := fInit_slink
  curRun := fInit_curRun
  blk := w0_blk
  intL := intL_thW
  vsc := w0_vsc
  bok := w0_bok
  fcov := w0_fcov
  fcap := w0_fcap
  ext := w0_ext
  live := w0_live
  zD := w0_zD
  carry := w0_carry

/-- **The witness starts `JReachU3` at `warI1` / `ipiMR`.** -/
theorem jReachU3_w0I1 : JReachU3 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  .start (jAtZ_w0I1 _) Zw_vx fInit_sinvX fInit_sinvIP fInit_ipiMR fInit_utPgR

/-- **`JReachU34` at the witness, arch `warI1`, at `ipiMR`.** -/
theorem jReachU34_w0I1 : JReachU34 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨jReachU3_w0I1, fInit_gpmOut, fInit_idleVtS, fInit_devRangeS⟩, fInit_irqStB⟩

/-- **`MachPlatF` for the witness arch at `ipiMR`** (its clock and interrupt operations are `modelArch`'s). -/
theorem warI1_machPlatF : MachPlatF warI1 ipiMR :=
  ⟨modelArch_machPlatF.now, modelArch_machPlatF.irqPending, modelArch_machPlatF.take,
    modelArch_machPlatF.mask1, modelArch_machPlatF.mask0, modelArch_machPlatF.ack, modelArch_machPlatF.frame⟩

/-- **`IpiF` for the witness arch at `ipiMR`, whatever the oracle.** -/
theorem warI1_ipiF : IpiF warI1 ipiMR := modelArch_ipiF

theorem warI1_max_periodK (O : OpaqueWK) (a : Fl4Spec.MachineState) :
    sporadic.max_period_us warI1 a ⦃ v => v.bv = Fl4Spec.MAX_PERIOD_US ⦄ := by
  have e : warI1.max_us a = ok (⟨(Fl4Spec.MAX_PERIOD_US * 8 : BitVec 64)⟩ : U64) := rfl
  unfold sporadic.max_period_us
  simp only [e, bind_ok]
  obtain ⟨v, hv, hvv⟩ := spec_exists (U64.div_spec (x := (⟨(Fl4Spec.MAX_PERIOD_US * 8 : BitVec 64)⟩ : U64)) (y := 8#u64)
    (by decide))
  rw [hv, WP.spec_ok]
  apply BitVec.eq_of_toNat_eq
  have hp := O.per
  have h1 : (Fl4Spec.MAX_PERIOD_US * 8).toNat = Fl4Spec.MAX_PERIOD_US.toNat * 8 := by
    rw [BitVec.toNat_mul]
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    rw [h8]
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
    rw [h64]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : v.bv.toNat = (Fl4Spec.MAX_PERIOD_US * 8).toNat / 8 := hvv
  rw [h2, h1]
  omega

theorem warI1_timeAgreeK (O : OpaqueWK) : TimeAgree warI1 where
  maxPeriod a := warI1_max_periodK O a
  usToTicks _ _ _ := (WP.spec_ok _).2 rfl
  kernelWcet _ := (WP.spec_ok _).2 rfl
  wcetUs := O.wcet
  timerUnit := O.unit

/-- **Every premise of `kernel_entry_reachU34` at the witness platform** (`wst`, `warI1`, `wAR`, `ipiMR`) and its
start state `jReachU34_w0I`, under `OpaqueWK` [P] (no `irqOracle` fact). The `PlainStore wst` instance is wit's
`wP`. -/
theorem u34_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      JReachU34 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨⟨fun _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial⟩,
    fun _ _ _ _ _ => trivial⟩,
   warI1_total, O.nd, warI1_machPlatF, warI1_ipiF,
   ⟨fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h, fun a _ h => (WP.spec_ok _).2 h,
    fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h, fun a _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ _ h => (WP.spec_ok _).2 h, fun a _ _ _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ _ _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h, fun a _ _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h,
    fun a _ _ _ h => (WP.spec_ok _).2 h⟩,
   ⟨fun a _ _ _ h => (WP.spec_ok _).2 h, fun a _ _ _ _ h => (WP.spec_ok _).2 h⟩,
   ⟨fun _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h, fun _ _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h⟩,
   fun _ _ _ => (WP.spec_ok _).2 trivial,
   ⟨fun _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial⟩,
   warI1_timeAgreeK O, O.max, fun _ _ => (WP.spec_ok _).2 rfl,
   ⟨fun _ _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ _ => (WP.spec_ok _).2 trivial,
    fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ _ => (WP.spec_ok _).2 trivial,
    fun _ _ _ _ => (WP.spec_ok _).2 trivial⟩,
   by
    intro a a' p z v hv σ _
    have e : (ok (pinF p z, a) : Result (U64 × Fl4Spec.MachineState)) = ok (v, a') := hv
    have ev : pinF p z = v := (Prod.mk.inj (ok_inj e)).1
    rw [← ev]
    exact pinF_ok O.pin p z σ,
   wst_ext,
   fun _ ms _ d x y hx hy => O.dl d ms.machineStateRest x y hx hy,
   jReachU34_w0I1⟩

/-- **`IoaRel` at the witness**: `warI1`'s one IOAPIC of 24 pins is `fInitASt`'s (`init_arch_state`). -/
theorem warI1_ioaRel : IoaRel warI1 fInitASt := by
  refine ⟨1#u64, fun _ => rfl, rfl, fun a i hi => ⟨24#u64, ?_, rfl, by decide⟩⟩
  have e : (1#u64).val = 1 := rfl
  have h1 : i.val < 1 := by omega
  show ok (if i.val < 1 then 24#u64 else 0#u64) = ok 24#u64
  rw [if_pos h1]

/-- **`warI` does not meet `IoaRel` at the witness** (it answers 0 IOAPICs; the spec boots with 1). -/
theorem warI_not_ioaRel : ¬ IoaRel warI fInitASt := by
  rintro ⟨nA, hn, hb, -⟩
  have h0 : warI.num_ioapics fInitASt.machineState = ok 0#u64 := rfl
  have e : nA = 0#u64 := eq_of_ok_eq ((hn _).symm.trans h0)
  have h1 : fInitASt.archState.x64NumIoapics = 1 := rfl
  subst e
  rw [h1] at hb
  exact absurd hb (by decide)

/-- **`JReachU38` at the witness** (arch `warI1`, `ipiMR`). -/
theorem jReachU38_w0I1 : JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU34_w0I1, warI1_ioaRel⟩

/-- **Every premise of `kernel_entry_reachU38` at the witness platform** (`wst`, `warI1`, `wAR`, `ipiMR`) with
its start state `jReachU38_w0I1`, under `OpaqueWK` [P]. Only U38's per-entry [J]s remain. -/
theorem u38_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩ := u34_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, jReachU38_w0I1⟩

/-- **`IoaMap` at `warI1`**: its routing always answers `true` (`modelArch`'s). -/
theorem warI1_ioaMap : IoaMap warI1 :=
  ⟨fun a _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨a, rfl⟩, fun a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨a, rfl⟩⟩

/-- **Every premise of `kernel_entry_reachU39` at the witness platform** with its start state, under
`OpaqueWK` [P]: U38's (`u38_w0I1`) and `IoaMap` (`warI1_ioaMap`). Only U39's per-entry [J]s remain. -/
theorem u39_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧ IoaMap warI1 ∧
      JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := u38_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, warI1_ioaMap, h18⟩

end

end Fl4Proofs.P3.JBoot
