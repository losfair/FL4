/-
P3 (int21): **`JReachU34` at jboot's witness**: the start hypothesis `hJ : JReachU34 …` of
`kernel_entry_reachU34` is satisfiable, and at the witness's platform every other premise of U34 holds as well,
with no assumption on the opaque `irqOracle`.

* **`jReachU34_w0`**: `JReachU34 warI wAR wMR w0 fInitASt.machineState fInitASt` (`wMR = modelMR`), from
  `jReachU17_w0` (JBootJAt) and irqfix's `fInit_irqStB` (`JReachU34.of_boot`).
* What lines up and what does not: `JReachU34` is stated for any `arI` / `AR` / `MR`, so `jReachU34_w0` is
  exactly its instance at jboot's platform (`wst`, `warI`, `wAR = True`, `wMR = modelMR`). U34's platform
  premises `MachPlatF` + `IpiF` are met by the model arch at **`ipiMR`** (`modelMR` with lines 126, 127 masked,
  JBootIpi), not at `modelMR`: at `modelMR` `IpiF` would again need the oracle fact (`OpaqueW.ipi`). Since every
  line is masked at boot (`initIrqMasks = fun _ => true`), the witness also starts the reachable set at `ipiMR`:
  **`jReachU34_w0I`** (`JAtZ` does not mention `MR`; only the start rule's `MR a σ.machineState` changes,
  `fInit_ipiMR`).
* **`warI_machPlatF`**, **`warI_ipiF`**: the witness arch meets `MachPlatF` / `IpiF` at `ipiMR` whatever the
  oracle (its interrupt and clock operations are `modelArch`'s).
* **`u34_w0I`**: every premise of `kernel_entry_reachU34` at `wst` / `warI` / `wAR` / `ipiMR` together with
  `jReachU34_w0I`, under **`OpaqueWK`** [P] = wit's `OpaqueW` without its `ipi` field (the opaque Fl4Spec
  constants: one domain, `maxTicksToUs`, WCET, timer unit, the period bound, `setDeadlineImpl` determinism, a
  port-read value). So U34 applies to the witness with no `irqOracle` premise.

Caveats (as jboot's): the boot is idle-only (no root server), one core.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootJAt
import Fl4Proofs.P3.XTopJointKEntryU34
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **`JReachU34` at the witness** (`wMR = modelMR`): the start hypothesis of `kernel_entry_reachU34` is
satisfiable. -/
theorem jReachU34_w0 : JReachU34 (L := wL) warI wAR wMR w0 fInitASt.machineState fInitASt :=
  JReachU34.of_boot (L := wL) warI wAR wMR jReachU17_w0

/-- Every IRQ line is masked at boot, so `ipiMR` relates the boot machine state to itself. -/
theorem fInit_ipiMR : ipiMR fInitASt.machineState fInitASt.machineState :=
  ⟨fInit_mr, rfl, rfl⟩

/-- **The witness starts `JReachU3` at `ipiMR`.** -/
theorem jReachU3_w0I : JReachU3 (L := wL) warI wAR ipiMR w0 fInitASt.machineState fInitASt :=
  .start (jAtZ_w0 _) Zw_vx fInit_sinvX fInit_sinvIP fInit_ipiMR fInit_utPgR

/-- **`JReachU34` at the witness at `ipiMR`** (the relation U34's platform premises hold at). -/
theorem jReachU34_w0I : JReachU34 (L := wL) warI wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨jReachU3_w0I, fInit_gpmOut, fInit_idleVtS, fInit_devRangeS⟩, fInit_irqStB⟩

/-- **`MachPlatF` for the witness arch at `ipiMR`** (its clock and interrupt operations are `modelArch`'s). -/
theorem warI_machPlatF : MachPlatF warI ipiMR :=
  ⟨modelArch_machPlatF.now, modelArch_machPlatF.irqPending, modelArch_machPlatF.take,
    modelArch_machPlatF.mask1, modelArch_machPlatF.mask0, modelArch_machPlatF.ack, modelArch_machPlatF.frame⟩

/-- **`IpiF` for the witness arch at `ipiMR`, whatever the oracle.** -/
theorem warI_ipiF : IpiF warI ipiMR := modelArch_ipiF

/-- **wit's `OpaqueW` without `ipi`** [P]: the facts about Fl4Spec's opaque constants the witness platform
needs (WitPlat's docstrings give each one's source). No `irqOracle` fact. -/
structure OpaqueWK : Prop where
  /-- [P] one scheduling domain. -/
  nd : Fl4Spec.numDomains = 1
  /-- [P] `maxTicksToUs = U64::MAX`. -/
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  /-- [P] kernel WCET 10 µs. -/
  wcet : Fl4Spec.kernelWCETUs = 10
  /-- [P] whole ticks per µs. -/
  unit : Fl4Spec.timerUnit = 1
  /-- [P] `MAX_PERIOD_US · 8` fits a `u64`. -/
  per : Fl4Spec.MAX_PERIOD_US.toNat < 2305843009213693952
  /-- [P] `setDeadlineImpl` is deterministic. -/
  dl : ∀ (d : Fl4Spec.Word64) (mr : Fl4Spec.MachineStateRest) (x y : Unit × Fl4Spec.MachineStateRest),
    x ∈ (Fl4Spec.setDeadlineImpl d mr).1 → y ∈ (Fl4Spec.setDeadlineImpl d mr).1 → x = y
  /-- [P] a port-read value possible at every spec state. -/
  pin : ∃ f, PinOK f

theorem warI_max_periodK (O : OpaqueWK) (a : Fl4Spec.MachineState) :
    sporadic.max_period_us warI a ⦃ v => v.bv = Fl4Spec.MAX_PERIOD_US ⦄ := by
  have e : warI.max_us a = ok (⟨(Fl4Spec.MAX_PERIOD_US * 8 : BitVec 64)⟩ : U64) := rfl
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

theorem warI_timeAgreeK (O : OpaqueWK) : TimeAgree warI where
  maxPeriod a := warI_max_periodK O a
  usToTicks _ _ _ := (WP.spec_ok _).2 rfl
  kernelWcet _ := (WP.spec_ok _).2 rfl
  wcetUs := O.wcet
  timerUnit := O.unit

/-- **Every premise of `kernel_entry_reachU34` at the witness platform** (`wst`, `warI`, `wAR`, `ipiMR`) and its
start state `jReachU34_w0I`, under `OpaqueWK` [P] (no `irqOracle` fact). The `PlainStore wst` instance is wit's
`wP`. -/
theorem u34_w0I (O : OpaqueWK) :
    ARIface warI wAR ∧ P0.ArchTotal warI ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI ipiMR ∧ IpiF warI ipiMR ∧
      MRKeepD warI ipiMR ∧ MRKeepIo warI ipiMR ∧ MRKeepIoapic warI ipiMR ∧
      (∀ a c, wAR a c → warI.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatA warI wAR ∧ TimeAgree warI ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI wAR ∧ PortInValMR warI ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      JReachU34 (L := wL) warI wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨⟨fun _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial,
      fun _ _ _ => (WP.spec_ok _).2 trivial, fun _ _ _ _ => (WP.spec_ok _).2 trivial⟩,
    fun _ _ _ _ _ => trivial⟩,
   warI_total, O.nd, warI_machPlatF, warI_ipiF,
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
   warI_timeAgreeK O, O.max, fun _ _ => (WP.spec_ok _).2 rfl,
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
   jReachU34_w0I⟩

end

end Fl4Proofs.P3.JBoot
