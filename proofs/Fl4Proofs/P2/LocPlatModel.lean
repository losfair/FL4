/-
# P2 (line p3mc, gen 32): a concrete arch instance of `LocPlat` and `MRKeepIoapic`, conditional on the opaque constants

`LocPlat st arI AR MR` (P2/E2EVFl4W3, P3's platform bundle) and `hIoa : MRKeepIoapic arI MR` are premises of every
P2 top (V13, V14). Gen 31 (handoff §36c) planned a minimal arch model. P3 already has the machine part
(P3/XTopJointMachRel `modelArch`: arch state = the spec's machine state, `now` / `irq_pending` / `take_pending_irq`
run `getCurrentTime` / `getActiveIRQ`, `mask_irq` updates the masks; `modelMR` = agreement on the four fields
`irqMasks` / `irqState` / `timeState` / `lastMachineTime`; `modelArch_machPlat`). Its timer operations are
placeholders (`us_to_ticks = id`, `max_us = 0`, `kernel_wcet_ticks = 0`), which break `TimeAgree`.

## The instance
* **`archT`**: `modelArch` with the timer operations computed by the spec's own formulas (`us_to_ticks u =
  usToTicks u`, `ticks_to_us v = ticksToUs v`, `kernel_wcet_ticks = kernelWCETTicks`, `max_us = 8 * MAX_PERIOD_US`,
  FL4's `max_period_us = max_us / 8`, `sporadic.rs`). `AR := fun _ _ => True` (`ART`), `MR := modelMR`.
* Every device / TLB / FPU / VCPU / IOAPIC / port / TDX operation keeps the arch state; `port_in` returns 0.
* **`locPlat_archT`**: `LocPlat st archT ART modelMR`, **`mrKeepIoapic_archT`**: `MRKeepIoapic archT modelMR`,
  **`modelMR_refl`**: `modelMR ms ms` (the relation is inhabited at every machine state, so `MR` is not vacuous).

## The hypotheses (`OpaqueH`), all about opaque spec constants
No Lean model can decide these (each constant is `opaque` in Fl4Spec/Machine); they are stated, not proved:
1. `nd : numDomains = 1` (`kernelConfig`, l.169);
2. `max : maxTicksToUs = U64.MAX` (l.253);
3. `wcetUs : kernelWCETUs = 10` and 4. `timerUnit : timerUnit = 1` (`timeConsts`, l.309) — the four of handoff §36c;
and, found here, four more that `LocPlat`'s non-opaque-looking fields need:
5. `maxP : MAX_PERIOD_US < 2^61` (`timeConsts`): `TimeAgree.maxPeriod` asks some `max_us` value `x` with
   `x / 8 = MAX_PERIOD_US` in `U64`, which exists iff `MAX_PERIOD_US ≤ (2^64 - 1) / 8`; `TimeConsts`' axioms give
   only `5 * MAX_PERIOD_US * ticksPerTimerUnit < 2^64 - 1` (`getCurrentTime_buffer_bound`), i.e. `< 2^64 / 5`, which
   does not imply it. So `TimeAgree` is satisfiable by no arch at all unless this holds.
6. `ipi : ∀ n, irqOracle n ∉ {126, 127}` (`irqOracle`, l.497): `MachPlat.noIpi` (`IpiF`) asks `take_pending_irq`
   to avoid FL4's IPI vectors at every `modelMR`-related state, and `MachPlat.take` forces the taken line to be the
   oracle's unmasked line; `modelMR` keeps no line masked. (Collapse A, Q: before it, the old `IrqPlatA.noIpi` asked
   this at every arch state. A relation keeping 126 / 127 masked needs no oracle fact: JBootIpi's `ipiMR`.)
7. `dl : setDeadlineImpl` is deterministic (l.664): `SetDlDetR` asks it of every `MR`-related state, and `MR` may
   not read `machineStateRest` (`MachPlat.frame`), so it is a property of the opaque operation itself.
8. `pin0`: the spec's I/O-port read (`archPerformInvocation … invokeIOPort … ioPortIn*`, through the opaque
   `in8Impl` / `in8Val`, `in16*`, `in32*`, l.868) has an outcome with value 0 keeping the memory: `PortInValMR` asks
   that the spec allow the value `port_in` returns, which depends on the opaque post-state of `machineStateRest`,
   invisible to any `MR`. (Any fixed value would do; 0 is `archT`'s.)
Plus `sx : StoreExt st`, a property of the store, not of the arch.

## `kernelWCETUs`: the default instance and FL4's configuration
`timeConsts` is `opaque`; its `Inhabited` default (`kernelWCETUs := 100`, `ticksPerTimerUnit := 50`,
`timerUnit := 1`, Fl4Spec/Machine l.293–296) is not its value as far as the logic knows, so `wcetUs` is neither
provable nor refutable — not false. But the default does not match FL4's build: FL4 fixes the kernel WCET at 10 µs
(`KERNEL_WCET_US = 10`, `crates/fl4-arch-x86_64/src/timer.rs` l.22 and `crates/fl4-arch-aarch64/src/timer.rs` l.12,
used by `kernel_wcet_ticks` in `crates/fl4-arch-x86_64/src/arch.rs` l.86–87; `sporadic::min_budget_us` is the literal
`2 * 10`, Fl4Core/Funs l.42060). So instantiating `timeConsts` with its default would make
`LocPlat.TimeAgree.wcetUs` false; the spec constant must be 10 for FL4. Likewise `ticksPerTimerUnit` must be FL4's
TSC MHz (`us_to_ticks = us * tsc_mhz`, calibrated at boot, default 1000 in `timer.rs` l.15), not the default 50.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPV13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.LocPlatM
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P2.PathObl
open Fl4Spec (MachineState)

noncomputable section
open Classical

/-- **The model arch with the spec's timer formulas** (module docstring). -/
def archT : machine.Arch MachineState :=
  { modelArch with
    us_to_ticks := fun _ u => ok ⟨Fl4Spec.usToTicks u.bv⟩
    ticks_to_us := fun _ v => ok ⟨Fl4Spec.ticksToUs v.bv⟩
    max_us := fun _ => ok ⟨Fl4Spec.MAX_PERIOD_US * 8#64⟩
    kernel_wcet_ticks := fun _ => ok ⟨Fl4Spec.kernelWCETTicks⟩ }

/-- The trivial CR3 relation. -/
def ART : MachineState → Fl4Spec.Cr3 → Prop := fun _ _ => True

/-- **`modelMR` is inhabited at every machine state.** -/
theorem modelMR_refl (ms : MachineState) : modelMR ms ms := ⟨rfl, rfl, rfl, rfl⟩

/-- **The hypotheses on opaque spec constants** (module docstring, items 1–8). -/
structure OpaqueH : Prop where
  nd : Fl4Spec.numDomains = 1
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  wcetUs : Fl4Spec.kernelWCETUs = 10
  timerUnit : Fl4Spec.timerUnit = 1
  maxP : Fl4Spec.MAX_PERIOD_US.toNat < 2 ^ 61
  ipi : ∀ n, (Fl4Spec.irqOracle n).toNat ≠ 126 ∧ (Fl4Spec.irqOracle n).toNat ≠ 127
  dl : ∀ (d : Fl4Spec.Word64) (mr : Fl4Spec.MachineStateRest) (x y : Unit × Fl4Spec.MachineStateRest),
    x ∈ (Fl4Spec.setDeadlineImpl d mr).1 → y ∈ (Fl4Spec.setDeadlineImpl d mr).1 → x = y
  pin0 : ∀ (p z : U64) (σ : Fl4Spec.State Unit), ∃ ms : MachineState,
    ms.underlyingMemory = σ.machineState.underlyingMemory ∧
    (.ok [(0#u64 : U64).bv], { σ with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
      (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1

/-- Close `ok x ⦃ P ⦄` by `P x` from the context or trivially. -/
macro "okc" : tactic =>
  `(tactic| ((show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]) <;> first | trivial | assumption | exact ⟨trivial, trivial⟩))

theorem archT_total : P0.ArchTotal archT where
  private_device_frame _ _ := by okc
  dma_ram _ _ _ := by okc
  dma_frame _ _ _ _ := by okc
  virtualization _ := by okc
  vcpu_capability _ _ := by okc
  vcpu_barrier _ := by okc
  vcpu_sync _ _ _ := by okc
  vcpu_release _ _ := by okc
  invalidate_ept _ _ _ := by okc
  tdx_active _ := by okc
  tdx_report _ _ _ _ _ _ _ _ _ _ := by okc
  tdx_extend_rtmr _ _ _ _ _ _ _ _ := by okc
  tdx_get_quote _ _ _ := by okc
  now _ := by okc
  set_deadline _ _ := by okc
  us_to_ticks _ _ := by okc
  ticks_to_us _ _ := by okc
  max_us _ := by okc
  kernel_wcet_ticks _ := by okc
  irq_pending _ := by okc
  take_pending_irq _ := by okc
  mask_irq _ _ _ := by okc
  ack_irq _ _ := by okc
  irq_free _ _ := by okc
  set_vspace _ _ _ := by okc
  invalidate_page _ _ _ := by okc
  invalidate_asid _ _ := by okc
  invalidate_page_structures _ _ := by okc
  ioapic_map _ _ _ _ _ _ := by okc
  ioapic_map_remapped _ _ _ _ _ _ _ := by okc
  num_ioapics _ := by okc
  ioapic_pins _ _ := by okc
  port_in _ _ _ := by okc
  port_out _ _ _ _ := by okc
  fpu_flush _ _ := by okc
  fpu_sanitise _ _ := by okc
  fpu_reload _ _ := by okc
  fpu_release _ _ := by okc
  remote_stall _ _ := by okc
  send_reschedule _ _ := by okc
  putc _ _ := by okc
  get_char _ := by okc
  halt _ := by okc

theorem archT_ari : ARIface archT ART where
  now _ _ _ := by okc
  set_deadline _ _ _ _ := by okc
  send_reschedule _ _ _ _ := by okc
  remote_stall _ _ _ _ := by okc
  fpu_flush _ _ _ _ := by okc
  fpu_release _ _ _ _ := by okc
  fpu_sanitise _ _ _ _ := by okc
  fpu_reload _ _ _ _ := by okc
  vcpu_barrier _ _ _ := by okc
  vcpu_release _ _ _ _ := by okc
  mask _ _ _ _ _ := trivial


theorem archT_kd : MRKeepD archT modelMR where
  set_deadline _ _ _ h := by okc
  send_reschedule _ _ _ h := by okc
  remote_stall _ _ _ h := by okc
  fpu_flush _ _ _ h := by okc
  fpu_release _ _ _ h := by okc
  fpu_sanitise _ _ _ h := by okc
  fpu_reload _ _ _ h := by okc
  vcpu_barrier _ _ h := by okc
  vcpu_release _ _ _ h := by okc
  invalidate_ept _ _ _ _ h := by okc
  invalidate_page _ _ _ _ h := by okc
  invalidate_asid _ _ _ h := by okc
  invalidate_page_structures _ _ _ h := by okc
  set_vspace _ _ _ _ h := by okc
  dma_frame _ _ _ _ _ h := by okc
  irq_free _ _ _ h := by okc
  tdx_report _ _ _ _ _ _ _ _ _ _ _ h := by okc
  tdx_extend_rtmr _ _ _ _ _ _ _ _ _ h := by okc
  tdx_get_quote _ _ _ _ h := by okc

theorem archT_io : MRKeepIo archT modelMR where
  port_in _ _ _ _ h := by okc
  port_out _ _ _ _ _ h := by okc

/-- **`hIoa` for the model.** -/
theorem mrKeepIoapic_archT : MRKeepIoapic archT modelMR where
  map _ _ _ _ _ _ _ h := by okc
  mapr _ _ _ _ _ _ _ _ h := by okc

theorem archT_ref : ArchRefines archT ART where
  setVspace _ _ _ _ _ := by okc
  invPage _ _ _ _ _ := by okc
  invAsid _ _ _ _ := by okc
  invEpt _ _ _ _ _ := by okc
  invPS _ _ _ _ := by okc

theorem archT_time (O : OpaqueH) : TimeAgree archT where
  maxPeriod a := by
    unfold sporadic.max_period_us
    show (do let i ← (ok (⟨Fl4Spec.MAX_PERIOD_US * 8#64⟩ : U64) : Result U64); i / 8#u64) ⦃ _ ⦄
    simp only [bind_ok]
    refine WP.spec_mono (U64.div_spec (x := ⟨Fl4Spec.MAX_PERIOD_US * 8#64⟩) (y := 8#u64) (by decide)) ?_
    intro z hz
    have hM := O.maxP
    have h1 : (⟨Fl4Spec.MAX_PERIOD_US * 8#64⟩ : U64).val = Fl4Spec.MAX_PERIOD_US.toNat * 8 := by
      show (Fl4Spec.MAX_PERIOD_US * 8#64).toNat = _
      rw [BitVec.toNat_mul]
      have e8 : (8#64 : BitVec 64).toNat = 8 := rfl
      rw [e8]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_right hM (by decide)) (by norm_num))
    have h8 : (8#u64 : U64).val = 8 := rfl
    rw [h1, h8, Nat.mul_div_cancel _ (by decide : 0 < 8)] at hz
    exact BitVec.eq_of_toNat_eq hz
  usToTicks _ _ _ := by okc
  kernelWcet _ := by okc
  wcetUs := O.wcetUs
  timerUnit := O.timerUnit

theorem archT_pa (O : OpaqueH) : PPPlatA archT ART where
  irqAR _ _ _ := by okc
  minBudget a := (archT_time O).mb a

theorem no_irq_val : syscall.NO_IRQ.val = 2 ^ 64 - 1 := by
  show syscall.NO_IRQ.bv.toNat = _
  rw [no_irq_bv, BitVec.toNat_allOnes]

/-- **`MachPlat` for the model** (`MachPlatF` from `modelArch_machPlat`; `IpiF` at `modelMR`, which keeps no line
masked, from the oracle fact `O.ipi`). -/
theorem archT_machPlat (O : OpaqueH) : MachPlat archT modelMR := by
  refine MachPlatF.toT ⟨modelArch_machPlat.now, modelArch_machPlat.irqPending, modelArch_machPlat.take,
    modelArch_machPlat.mask1, modelArch_machPlat.mask0, modelArch_machPlat.ack, modelArch_machPlat.frame⟩ ?_
  intro a _ _
  show (ok (modelTake a, gaiState a) : Result (U64 × MachineState)) ⦃ _ ⦄
  rw [WP.spec_ok]
  dsimp only
  cases e : gaiLine true a with
  | none =>
    rw [modelTake_none e, no_irq_val]
    constructor <;> decide
  | some i =>
    rw [(modelTake_some e).2]
    have hi : i = Fl4Spec.irqOracle (a.irqState + 1) := by
      unfold gaiLine at e
      split at e
      · cases e
      · exact (Option.some.inj e).symm
    rw [hi]
    exact O.ipi _

theorem archT_ia (O : OpaqueH) : IrqPlatA archT ART where
  takeAR _ _ _ := by okc
  ackAR _ _ _ _ := by okc

theorem archT_pi (O : OpaqueH) : PortInValMR archT modelMR := by
  intro a a' p z v hv σ _
  have e : ((0#u64 : U64), a) = (v, a') := by
    have h2 : (ok ((0#u64 : U64), a) : Result (U64 × MachineState)) = ok (v, a') := hv
    simpa using h2
  obtain ⟨rfl, -⟩ := Prod.mk.inj e
  exact O.pin0 p z σ

theorem archT_dr (O : OpaqueH) : Fl4Proofs.P3.SInvR.G5.SetDlDetR (A := MachineState) modelMR :=
  fun _ ms _ d x y hx hy => O.dl d ms.machineStateRest x y hx hy

/-- **`LocPlat` for the model** (module docstring): every field from the concrete arch, given the opaque-constant
hypotheses `OpaqueH` and the store's `StoreExt`. -/
theorem locPlat_archT {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (O : OpaqueH)
    (sx : P1.StoreExt st) : LocPlat st archT ART modelMR where
  ari := archT_ari
  tot := archT_total
  nd := O.nd
  mach := archT_machPlat O
  kd := archT_kd
  io := archT_io
  pa := archT_pa O
  ia := archT_ia O
  t := archT_time O
  max := O.max
  tu _ _ := by okc
  ref := archT_ref
  pi := archT_pi O
  sx := sx
  dr := archT_dr O

end
end Fl4Proofs.P2.LocPlatM
