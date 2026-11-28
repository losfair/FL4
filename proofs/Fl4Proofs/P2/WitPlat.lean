/-
# P2 (line wit, gen 1): a concrete platform for `serializable_fl4_localU2`

Audit F4 (audU.md): nobody had built a `LocPlat` (or any concrete `machine.Store` with `LawfulStore`). This module
gives one, so the platform / glue premises of `serializable_fl4_localU2` are shown jointly satisfiable:

* **`wst : machine.Store WSt`**: a word-addressed memory of `2^61` aligned 64-bit words (`WSt.w`), a kernel-state
  base and a CPU number. Instances `LawfulStore wst` (`wL`), `PlainStore wst`, and **`wst_ext : StoreExt wst`**
  (P3's `sx`: equal aligned words, base and CPU give equal states — true because the state *is* its aligned words).
* **`warI : machine.Arch Fl4Spec.MachineState`**: P3's `modelArch` (its clock and interrupt reads run the spec's
  machine operations, `modelArch_machPlat`) with the timer conversions, the period bound and the port read set from
  the spec's constants. `wAR := fun _ _ => True`, `wMR := modelMR`.
* **`wit_locPlat : OpaqueW → LocPlat wst warI wAR wMR`**, **`wit_ioapic : MRKeepIoapic warI wMR`**,
  **`warI_total : ArchTotal warI`**.

## What cannot be proved: properties of opaque `Fl4Spec` constants (`OpaqueW`)

Several `LocPlat` fields are statements about `opaque` constants of `Fl4Spec` (l4v's unspecified `consts` /
`Kernel_Config`). No Lean term can prove or refute them; any value of the constant's type is a model. They are
collected in **`OpaqueW`** [P] (platform facts, each the configuration FL4 runs with):
* `nd`: `numDomains = 1` (`opaque kernelConfig`) — `LocPlat.nd`;
* `max`: `maxTicksToUs = U64::MAX` (`opaque maxTicksToUs`) — `LocPlat.max`;
* `wcet`, `unit`: `kernelWCETUs = 10`, `timerUnit = 1` (`opaque timeConsts`) — `TimeAgree.wcetUs` / `.timerUnit`;
* `per`: `MAX_PERIOD_US < 2^61` (`opaque timeConsts`) — needed for `TimeAgree.maxPeriod`: FL4's `max_period_us` is
  `max_us / 8`, so `MAX_PERIOD_US` must be some `u64 / 8`; `TimeConsts`' own bound gives only `< 2^64 / 5`;
* `ipi`: the IRQ oracle never yields the IPI vectors 126 / 127 (`opaque irqOracle`) — `MachPlat.take` (the platform
  reports the spec's line) and `IrqPlatA.noIpi` (never 126 / 127) together force it;
* `dl`: `setDeadlineImpl` has at most one outcome (`opaque setDeadlineImpl`) — `SetDlDetR` (`LocPlat.dr`; `MR`
  cannot restrict the machine-state rest, `MachPlat.frame`);
* `pin`: some value function of (port, size) is a possible result of the spec's port `In` at **every** spec state
  (`opaque in8Impl` / `in8Val` …) — `PortInValMR` (`LocPlat.pi`; again `MR` cannot restrict the rest of the
  machine state, so the read value must be possible whatever the device state).

`OpaqueW` is consistent with the types of the constants (`opaqueW_types`: a `KernelConfig` with one domain and a
`TimeConsts` with `kernelWCETUs = 10`, `timerUnit = 1`, `MAX_PERIOD_US < 2^61` exist, an oracle avoiding 126/127
exists). `ipi`, `dl` and `pin` are strong — `pin` holds only for a port model whose values do not depend on the
device state — but they are what P3's `MachPlat` / `IrqPlatA` / `PortInValMR` / `SetDlDetR` [P]s already ask of
the opaque constants (findings, see the line handoff wit.md).

No sorry. New module; no existing statement changed.

**Collapse A, Q:** `warI_machPlat`, `warI_take_ne`, `warI_max_period`, `warI_timeAgree`, `wit_locPlat` and
`wit_ioapic` are removed together with U2 (`serializable_fl4_localU2`) and its witnesses (P2/WitExec,
P2/WitUncond). With `MachPlat` narrowed (`noIpi : IpiF` at related states), `LocPlat` at `wMR = modelMR` would
need `OpaqueW.ipi` inside `MachPlat`; jboot's `ipiMR` witness (P2/WitU34 `wit_locPlatK`) needs no oracle fact.
The store, the arch and `OpaqueW` stay (jboot's witnesses use them).
-/
import Fl4Proofs.P2.E2EPU2P
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P2.PathObl

noncomputable section
open Classical

/-! ## The store -/

/-- A store state: the aligned words, the kernel-state base, the CPU. -/
structure WSt where
  w : Fin 2305843009213693952 → U64
  kb : U64
  cpu : U64

/-- The word index of an address. -/
def widx (a : U64) : Fin 2305843009213693952 :=
  ⟨a.val / 8, by
    have h : a.val < 18446744073709551616 := a.bv.isLt
    omega⟩

def wmem (s : WSt) (a : U64) : U64 := s.w (widx a)

def wwr (s : WSt) (a v : U64) : WSt := { s with w := Function.update s.w (widx a) v }

def wzr (s : WSt) (a n : U64) : WSt :=
  { s with w := fun i => if a.val ≤ 8 * i.val ∧ 8 * i.val < a.val + n.val then 0#u64 else s.w i }

/-- **The concrete store.** -/
def wst : machine.Store WSt where
  frame_masks _ := ok (0#u64, 0#u64)
  read s a := ok (wmem s a)
  read_pair s a := ok (wmem s a, wmem s (core.num.U64.wrapping_add a 8#u64))
  write s a v := ok (wwr s a v)
  fetch_and s a m := ok (wmem s a, wwr s a (wmem s a &&& m))
  zero s a n := ok (wzr s a n)
  clear_free s a n := ok (wzr s a n)
  ks_base s := ok s.kb
  cur_cpu s := ok s.cpu

theorem widx_inj {a b : U64} (ha : Aligned a) (hb : Aligned b) (h : widx a = widx b) : a = b := by
  have h1 : a.val / 8 = b.val / 8 := congrArg Fin.val h
  apply UScalar.eq_of_val_eq
  have ha' : a.val % 8 = 0 := ha
  have hb' : b.val % 8 = 0 := hb
  omega

theorem widx_mul (b : U64) (hb : Aligned b) : 8 * (widx b).val = b.val := by
  have hb' : b.val % 8 = 0 := hb
  show 8 * (b.val / 8) = b.val
  omega

/-- **`wst` is lawful.** -/
instance wL : LawfulStore wst where
  frame_masks_total _ := (WP.spec_ok _).2 trivial
  mem := wmem
  wr := wwr
  zr := wzr
  ksb s := s.kb
  cpu s := s.cpu
  read_eq _ _ := rfl
  read_pair_eq _ _ := rfl
  write_eq _ _ _ := rfl
  zero_eq _ _ _ := rfl
  clear_free_eq _ _ _ := rfl
  ks_base_eq _ := rfl
  cur_cpu_eq _ := rfl
  fetch_and_eq _ _ _ := rfl
  mem_wr s a v b ha hb := by
    show Function.update s.w (widx a) v (widx b) = if a = b then v else s.w (widx b)
    by_cases e : a = b
    · subst e; simp
    · rw [if_neg e, Function.update_apply, if_neg (fun h => e (widx_inj hb ha h).symm)]
  mem_zr s a n b _ _ _ hb := by
    show (if a.val ≤ 8 * (widx b).val ∧ 8 * (widx b).val < a.val + n.val then 0#u64 else s.w (widx b)) = _
    rw [widx_mul b hb]
    try rfl
  ksb_wr _ _ _ := rfl
  cpu_wr _ _ _ := rfl
  ksb_zr _ _ _ := rfl
  cpu_zr _ _ _ := rfl

instance wP : PlainStore wst where
  frame_masks_eq _ := rfl

/-- The aligned address of word `i`. -/
def wad (i : Fin 2305843009213693952) : U64 :=
  ⟨BitVec.ofNatLT (8 * i.val) (by have := i.isLt; show 8 * i.val < 18446744073709551616; omega)⟩

theorem wad_val (i : Fin 2305843009213693952) : (wad i).val = 8 * i.val := BitVec.toNat_ofNatLT _ _

theorem wad_aligned (i : Fin 2305843009213693952) : Aligned (wad i) := by
  show (wad i).val % 8 = 0
  rw [wad_val]; omega

theorem widx_wad (i : Fin 2305843009213693952) : widx (wad i) = i := by
  apply Fin.ext
  show (wad i).val / 8 = i.val
  rw [wad_val]; omega

/-- **P3's `StoreExt` holds of `wst`** (`LocPlat.sx`): a state is its aligned words, base and CPU. -/
theorem wst_ext : StoreExt wst := by
  rintro ⟨w, kb, c⟩ ⟨w', kb', c'⟩ hm hk hc
  have hw : w = w' := by
    funext i
    have h := hm (wad i) (wad_aligned i)
    change w (widx (wad i)) = w' (widx (wad i)) at h
    rwa [widx_wad] at h
  have hk' : kb = kb' := hk
  have hc' : c = c' := hc
  subst hw hk' hc'
  rfl

/-! ## The opaque-constant premises -/

/-- The spec's port `In` can give `f p z` at every spec state (`PortInValMR` at every `MR`). -/
def PinOK (f : U64 → U64 → U64) : Prop :=
  ∀ (p z : U64) (σ : Fl4Spec.State Unit), ∃ ms : Fl4Spec.MachineState,
    ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [(f p z).bv], { σ with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1

/-- **The facts about opaque `Fl4Spec` constants a `LocPlat` needs** [P] (module docstring: each is a property of
an `opaque` constant, neither provable nor refutable in Lean; they are FL4's platform configuration). -/
structure OpaqueW : Prop where
  /-- [P] one scheduling domain (`opaque kernelConfig`). -/
  nd : Fl4Spec.numDomains = 1
  /-- [P] `maxTicksToUs = U64::MAX` (`opaque maxTicksToUs`). -/
  max : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv
  /-- [P] kernel WCET 10 µs (`opaque timeConsts`). -/
  wcet : Fl4Spec.kernelWCETUs = 10
  /-- [P] whole ticks per µs (`opaque timeConsts`). -/
  unit : Fl4Spec.timerUnit = 1
  /-- [P] `MAX_PERIOD_US · 8` fits a `u64` (`opaque timeConsts`; FL4's `max_period_us = max_us / 8`). -/
  per : Fl4Spec.MAX_PERIOD_US.toNat < 2305843009213693952
  /-- [P] the IRQ oracle never delivers the IPI vectors (`opaque irqOracle`). -/
  ipi : ∀ n, Fl4Spec.irqOracle n ≠ 126 ∧ Fl4Spec.irqOracle n ≠ 127
  /-- [P] the timer's `setDeadlineImpl` is deterministic (`opaque setDeadlineImpl`). -/
  dl : ∀ (d : Fl4Spec.Word64) (mr : Fl4Spec.MachineStateRest) (x y : Unit × Fl4Spec.MachineStateRest),
    x ∈ (Fl4Spec.setDeadlineImpl d mr).1 → y ∈ (Fl4Spec.setDeadlineImpl d mr).1 → x = y
  /-- [P] a port-read value possible at every spec state (`opaque in8Impl` / `in8Val` / …). -/
  pin : ∃ f, PinOK f

/-- A `TimeConsts` value with FL4's WCET (10 µs) and timer unit (1), l4v's one-hour period. -/
def wTC : Fl4Spec.TimeConsts :=
    { maxPeriodUs := 60 * 60 * 1000 * 1000,
      kernelWCETUs := 10, ticksPerTimerUnit := 50, timerUnit := 1,
      kernelWCET_us_pos2 := by decide
      MIN_BUDGET_le_MAX_PERIOD := by decide
      ticks_per_timer_unit_non_zero := by decide
      MIN_BUDGET_bound := by decide
      getCurrentTime_buffer_bound := by decide
      kernelWCET_pos' := by decide
      MIN_BUDGET_pos' := by decide
      init_domain_time_pos := by decide
      init_domain_time_bound := by decide
      getCurrentTime_buffer_pos := by decide }

/-- **`OpaqueW` asks nothing of the constants' types that no value meets** (consistency of `nd` / `wcet` / `unit` /
`per` / `ipi` with `KernelConfig`, `TimeConsts` and the oracle's type). -/
theorem opaqueW_types :
    (∃ kc : Fl4Spec.KernelConfig, kc.numDomains = 1) ∧
    (∃ tc : Fl4Spec.TimeConsts, tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧
      tc.maxPeriodUs.toNat < 2305843009213693952) ∧
    (∃ o : Nat → Fl4Spec.Word8, ∀ n, o n ≠ 126 ∧ o n ≠ 127) :=
  ⟨⟨⟨1, by decide, by decide, 8, 256⟩, rfl⟩, ⟨wTC, rfl, rfl, by decide⟩, ⟨fun _ => 0, fun _ => (by decide : (0 : Fl4Spec.Word8) ≠ 126 ∧ (0 : Fl4Spec.Word8) ≠ 127)⟩⟩

/-! ## The arch -/

/-- The port-read value: `OpaqueW.pin`'s function (a choice), `0` if none exists. -/
def pinF : U64 → U64 → U64 := if h : ∃ f, PinOK f then Classical.choose h else fun _ _ => 0#u64

theorem pinF_ok (h : ∃ f, PinOK f) : PinOK pinF := by
  unfold pinF; rw [dif_pos h]; exact Classical.choose_spec h

/-- **The concrete arch**: `modelArch` with the timer conversions, the period bound, the WCET and the port read set
from the spec. -/
def warI : machine.Arch Fl4Spec.MachineState :=
  { modelArch with
    us_to_ticks := fun _ x => ok ⟨Fl4Spec.usToTicks x.bv⟩
    ticks_to_us := fun _ x => ok ⟨Fl4Spec.ticksToUs x.bv⟩
    max_us := fun _ => ok ⟨(Fl4Spec.MAX_PERIOD_US * 8 : BitVec 64)⟩
    kernel_wcet_ticks := fun _ => ok ⟨Fl4Spec.kernelWCETTicks⟩
    port_in := fun a p z => ok (pinF p z, a) }

/-- The CR3 relation: none needed. -/
def wAR : Fl4Spec.MachineState → Fl4Spec.Cr3 → Prop := fun _ _ => True

/-- The machine relation: `modelMR` (the four fields the reads use agree). -/
abbrev wMR : Fl4Spec.MachineState → Fl4Spec.MachineState → Prop := modelMR

theorem warI_total : P0.ArchTotal warI where
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

end
end Fl4Proofs.P2.Wit
