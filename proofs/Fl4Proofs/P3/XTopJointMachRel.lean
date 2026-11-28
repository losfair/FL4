/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN irq1): **the platform reads
against the spec's machine state** (`MachPlat` [P] over a relation `MR`
between FL4's arch state and the spec's `MachineState`), replacing the
∀-spec-state platform premises `PPPlat.now`/`PPPlat.irq`/`IrqPlat.take`.

* FINDING (`PPPlat.false`, after the inv1 planning line's
  `nowAgree_all_false`): `PPPlat.now : ∀ a σ, NowAgree arI a σ` is FALSE for
  every platform: at a spec state whose `curTime` is `allOnes` the spec's
  `getCurrentTime` value is capped at `-(getCurrentTimeBuffer + 1)` <
  `allOnes` (`getCurrentTime_buffer_pos`), so `σ.curTime ≤ r` fails. Hence
  `PPPlat arI AR → A → False` and every theorem taking `PPPlat` and an arch
  state (the preemption path, `dispatch_all*`, `kernel_entryJ*` up to J8) is
  vacuous. `IrqPlat.take` / `PPPlat.irq` are not false but force a platform
  that never reports a line (`IrqPlat.noIrq`, sch13).
* The spec's clock and interrupt reads are deterministic functions of the
  machine state (`getCurrentTime_eq`, `getActiveIRQ_eq`: l4v's `time_oracle`
  / `irq_oracle` indexed by `time_state` / `irq_state`). `MachPlat arI MR`
  [P] says each FL4 platform read returns what the spec's read returns from
  a related machine state, and moves the relation along with it (l4v: the
  machine state is shared between the abstract and the concrete level; the
  oracles stand for the devices):
  - `now`: `now a` returns `gctVal ms` and `MR` holds after at `gctState ms`
    (`getCurrentTime`);
  - `irqPending` / `take`: the line of `getActiveIRQ true` at `ms` (`NO_IRQ`
    ↔ `none`, otherwise its number), `MR` after at `gaiState ms`;
  - `mask`: `mask_irq a w m` with `maskInterrupt m w`; `ack`: `ack_irq` with
    `ackInterrupt` (a no-op on the machine state);
  - `frame`: `MR` reads only the four machine fields the reads depend on
    (masks, IRQ oracle position, clock position, last machine time), so a spec
    step that keeps them (memory writes, TLB / deadline `machineStateRest`
    ops) keeps `MR`.
  Nothing is stated for all spec states: each read is related only at a
  machine state `MR` relates to the arch state at hand.
* `ValidMachineTime σ` [J] (l4v `valid_machine_time`: `cur_time ≤
  last_machine_time`, and the last machine time is below `getCurrentTime`'s
  cap, which `getCurrentTime` keeps): with `MR` it gives the old per-state
  `NowAgree arI a σ` (`MachPlat.nowAgree`, the `σ.curTime ≤ r` conjunct comes
  from the spec invariant, not from the platform), and is kept by
  `updateTimeStamp` (`validMachineTime_gct`).
* `MachPlat.irqAt` / `MachPlat.takeAt`: the old per-state shapes of
  `PPPlat.irq` / `IrqPlat.take` at a spec state whose machine state `MR`
  relates, plus `MR` after.
* Satisfiable by a platform that reports interrupts (`modelArch`, the arch
  state being the spec's machine state: `modelArch_machPlat`): its
  `take_pending_irq` reports exactly the spec's line (`modelArch_take_some`),
  and it reports `NO_IRQ` from every state only if the spec's oracle never
  reports a line (`modelArch_noIrq_iff`), so `MachPlat` does not imply
  `noIrq` (unlike `IrqPlat`); likewise `PPPlat` itself is unsatisfiable while
  `MachPlat` holds for `modelArch`.
-/
import Fl4Proofs.P3.XTopJointIrqZI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

theorem ndm_bind_single {σ α β : Type} {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {x : α × σ}
    (h : m s = ({x}, False)) : (m >>= f) s = f x.1 x.2 := by
  show NonDet.bind m f s = _
  unfold NonDet.bind
  rw [h]
  refine Prod.ext ?_ ?_
  · ext r; simp
  · simp

theorem ndm_bind_gets {σ α β : Type} (g : σ → α) (f : α → NonDet σ β) (s : σ) :
    (NonDet.gets g >>= f) s = f (g s) s := ndm_bind_single (m := NonDet.gets g) (x := (g s, s)) rfl

theorem ndm_bind_modify {σ β : Type} (g : σ → σ) (f : Unit → NonDet σ β) (s : σ) :
    (NonDet.modify g >>= f) s = f () (g s) := ndm_bind_single (m := NonDet.modify g) (x := ((), g s)) rfl

theorem ndm_bind_pure {σ α β : Type} (a : α) (f : α → NonDet σ β) (s : σ) :
    ((pure a : NonDet σ α) >>= f) s = f a s := ndm_bind_single (m := pure a) (x := (a, s)) rfl

/-- The cap of the spec's clock. -/
abbrev timeCap : Nat := unat (-(getCurrentTimeBuffer + 1))

/-- The value `getCurrentTime` computes at a machine state (as a number). -/
def gctNat (ms : MachineState) : Nat :=
  min timeCap (unat ms.lastMachineTime + timeOracle (ms.timeState + 1))

/-- The value `getCurrentTime` returns at a machine state. -/
def gctVal (ms : MachineState) : Word64 := BitVec.ofNat 64 (gctNat ms)

/-- The machine state after `getCurrentTime`. -/
def gctState (ms : MachineState) : MachineState :=
  { ms with timeState := ms.timeState + 1, lastMachineTime := gctVal ms }

/-- **`getCurrentTime` is deterministic** (l4v `time_oracle`). -/
theorem getCurrentTime_eq (ms : MachineState) : getCurrentTime ms = ({(gctVal ms, gctState ms)}, False) := by
  unfold getCurrentTime
  rw [ndm_bind_modify, ndm_bind_gets, ndm_bind_gets, ndm_bind_pure, ndm_bind_pure, ndm_bind_modify]
  rfl

/-- The line `getActiveIRQ b` reports at a machine state. -/
def gaiLine (b : Bool) (ms : MachineState) : Option Irq :=
  if ms.irqMasks (irqOracle (ms.irqState + 1)) ∨ irqOracle (ms.irqState + 1) = 0xFF ∨
      (b ∧ irqOracle (ms.irqState + 1) ∈ nonKernelIRQs)
  then none else some (irqOracle (ms.irqState + 1))

/-- The machine state after `getActiveIRQ`. -/
def gaiState (ms : MachineState) : MachineState := { ms with irqState := ms.irqState + 1 }

/-- **`getActiveIRQ` is deterministic** (l4v `irq_oracle`). -/
theorem getActiveIRQ_eq (b : Bool) (ms : MachineState) :
    getActiveIRQ b ms = ({(gaiLine b ms, gaiState ms)}, False) := by
  unfold getActiveIRQ
  rw [ndm_bind_gets, ndm_bind_modify, ndm_bind_gets]
  unfold gaiLine gaiState
  dsimp only [Function.comp]
  split <;> rfl

/-- A reported line is not masked. -/
theorem gaiLine_unmasked {b : Bool} {ms : MachineState} {i : Irq} (h : gaiLine b ms = some i) :
    ms.irqMasks i = false := by
  unfold gaiLine at h
  split at h
  · cases h
  · rename_i hn
    cases h
    cases e : ms.irqMasks (irqOracle (ms.irqState + 1))
    · rfl
    · exact absurd (Or.inl e) hn

/-- A machine operation's singleton outcome, at the state level. -/
theorem doMachineOp_single {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {v : α}
    {ms' : MachineState} (h : mop σ.machineState = ({(v, ms')}, False)) :
    doMachineOp (Z := Unit) mop σ = ({(v, { σ with machineState := ms' })}, False) := by
  unfold doMachineOp
  rw [ndm_bind_gets]
  have hs : NonDet.selectF (mop σ.machineState) σ = ({((v, ms'), σ)}, False) := by
    unfold NonDet.selectF
    rw [h]
    refine Prod.ext ?_ rfl
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [ndm_bind_single hs]
  dsimp only
  rw [ndm_bind_modify]
  rfl

/-- The clock value is at most the cap. -/
theorem gctNat_le (ms : MachineState) : gctNat ms ≤ timeCap := Nat.min_le_left _ _

theorem gctVal_toNat (ms : MachineState) : (gctVal ms).toNat = gctNat ms := by
  unfold gctVal
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (gctNat_le ms) (-(getCurrentTimeBuffer + 1)).isLt)

/-- The cap is below `allOnes` (`getCurrentTime_buffer_pos`). -/
theorem timeCap_lt : timeCap < 2 ^ 64 - 1 := by
  have hb : getCurrentTimeBuffer ≠ 0 := by
    have := getCurrentTime_buffer_pos
    intro e; unfold getCurrentTimeBuffer timeBufferConst MAX_PERIOD at e; rw [e] at this
    exact (BitVec.lt_irrefl _) this
  have hc : timeCap ≠ 2 ^ 64 - 1 := by
    intro e
    apply hb
    have e2 : -(getCurrentTimeBuffer + 1) = BitVec.allOnes 64 :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_allOnes]; exact e)
    have e3 : getCurrentTimeBuffer + 1 = 1 := by
      have := congrArg (fun x => -x) e2
      simp only [BitVec.neg_neg] at this
      rw [this]; decide
    have e4 := congrArg (fun x => x - 1) e3
    simpa using e4
  have hlt : timeCap < 2 ^ 64 := (-(getCurrentTimeBuffer + 1)).isLt
  omega

/-- **l4v `valid_machine_time`** [J]: the current time is at most the last
machine time, which is at most the clock's cap (`getCurrentTime` keeps the
bound: `gctNat_le`). -/
def ValidMachineTime (σ : State Unit) : Prop :=
  σ.curTime ≤ σ.machineState.lastMachineTime ∧ unat σ.machineState.lastMachineTime ≤ timeCap

/-- Under `ValidMachineTime` the clock does not go back. -/
theorem vmt_le_gct {σ : State Unit} (hV : ValidMachineTime σ) : σ.curTime ≤ gctVal σ.machineState := by
  obtain ⟨h1, h2⟩ := hV
  have h3 : unat σ.machineState.lastMachineTime ≤ gctNat σ.machineState :=
    le_min h2 (Nat.le_add_right _ _)
  rw [BitVec.le_def] at h1 ⊢
  rw [gctVal_toNat]
  exact le_trans h1 h3

/-- `getCurrentTime` (and the time stamp it gives) keeps
`ValidMachineTime`: the new last machine time is the clock value, below the
cap, and the new current time is that value. -/
theorem validMachineTime_gct (σ : State Unit) :
    ValidMachineTime { σ with curTime := gctVal σ.machineState, machineState := gctState σ.machineState } :=
  ⟨BitVec.le_refl _, by show (gctVal σ.machineState).toNat ≤ _; rw [gctVal_toNat]; exact gctNat_le _⟩

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **FINDING: `PPPlat` is unsatisfiable** (module docstring; inv1's
`nowAgree_all_false`): `PPPlat.now` at a spec state with `curTime =
allOnes` asks for a clock value above the spec clock's cap. -/
theorem PPPlat.false (hP : PPPlat arI AR) (a : A) : False := by
  let σ0 : Fl4Spec.State Unit := Classical.choice inferInstance
  let σ1 : Fl4Spec.State Unit := { σ0 with curTime := BitVec.allOnes 64 }
  obtain ⟨r, -, ms, he, hle, -⟩ := spec_exists (hP.now a σ1)
  rw [doMachineOp_single (getCurrentTime_eq σ1.machineState)] at he
  have e := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj he).1)).1
  have hv : r.1.bv.toNat = gctNat σ1.machineState := by rw [← e, gctVal_toNat]
  have hle' : (BitVec.allOnes 64).toNat ≤ r.1.bv.toNat := BitVec.le_def.1 hle
  rw [BitVec.toNat_allOnes, hv] at hle'
  have := gctNat_le σ1.machineState
  have := timeCap_lt
  omega

variable (arI) in
/-- **`IrqPlatA.noIpi` at related states** (JBootIpi's `IpiF`, moved here in collapse A, Q): from an `MR`-related
state, `take_pending_irq` never gives an IPI vector 126 / 127. -/
def IpiF (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄

variable (arI) in
/-- **The platform reads against the spec's machine state** [P] (module
docstring). `MR a ms`: the arch state `a` and the spec machine state `ms`
agree on what the platform reads depend on (IRQ masks and pending lines,
the clock). l4v: the machine state is shared between the levels and the
devices are the oracles (`irq_oracle`, `time_oracle`); the FL4 arch op ↔ the
spec machine op it implements. -/
structure MachPlat (MR : A → Fl4Spec.MachineState → Prop) : Prop where
  /-- `now` is `getCurrentTime`. -/
  now : ∀ a ms, MR a ms → arI.now a ⦃ r => r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄
  /-- `irq_pending` is `getActiveIRQ true` (whether it reports a line). -/
  irqPending : ∀ a ms, MR a ms → arI.irq_pending a ⦃ r =>
    (r.1 = true ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄
  /-- `take_pending_irq` is `getActiveIRQ true` (the line, `NO_IRQ` for
  none). -/
  take : ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r =>
    (r.1 = syscall.NO_IRQ ↔ gaiLine true ms = none) ∧
    (∀ i, gaiLine true ms = some i → r.1.val = i.toNat) ∧ MR r.2 (gaiState ms) ⦄
  /-- `mask_irq w m` is `maskInterrupt m w` (`mask = true` masks): masking any line `< 256`, unmasking a line
  `≤ maxIRQ = 125` (`cond m 256 126`; collapse A, Q: irqfix's `MachPlatT.mask`). -/
  mask : ∀ a (w : U64) m ms, MR a ms → w.val < cond m 256 126 → arI.mask_irq a w m ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m } ⦄
  /-- `ack_irq` is `ackInterrupt` (no machine-state change). -/
  ack : ∀ a w ms, MR a ms → arI.ack_irq a w ⦃ a' => MR a' ms ⦄
  /-- `MR` reads only the masks, the oracle positions and the last machine
  time. -/
  frame : ∀ a ms ms', MR a ms → ms'.irqMasks = ms.irqMasks → ms'.irqState = ms.irqState →
    ms'.timeState = ms.timeState → ms'.lastMachineTime = ms.lastMachineTime → MR a ms'
  /-- `IpiF`: no IPI vector (126 / 127) from an `MR`-related state (collapse A, Q: irqfix's `MachPlatT.noIpi`). -/
  noIpi : IpiF arI MR

variable (arI) in
/-- **`MachPlat` with the mask split** (JBootIpi's fix, moved here in collapse A, Q): masking any line, unmasking
the spec's IRQs only (`≤ maxIRQ = 125`); no `noIpi`. With `IpiF` it is `MachPlat` (`MachPlatF.toT`). -/
structure MachPlatF (MR : A → Fl4Spec.MachineState → Prop) : Prop where
  now : ∀ a ms, MR a ms → arI.now a ⦃ r => r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄
  irqPending : ∀ a ms, MR a ms → arI.irq_pending a ⦃ r =>
    (r.1 = true ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄
  take : ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r =>
    (r.1 = syscall.NO_IRQ ↔ gaiLine true ms = none) ∧
    (∀ i, gaiLine true ms = some i → r.1.val = i.toNat) ∧ MR r.2 (gaiState ms) ⦄
  /-- Masking: any line. -/
  mask1 : ∀ a (w : U64) ms, MR a ms → w.val < 256 → arI.mask_irq a w true ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) true } ⦄
  /-- Unmasking: the spec's IRQs only (`≤ maxIRQ = 125`). -/
  mask0 : ∀ a (w : U64) ms, MR a ms → w.val ≤ 125 → arI.mask_irq a w false ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) false } ⦄
  ack : ∀ a w ms, MR a ms → arI.ack_irq a w ⦃ a' => MR a' ms ⦄
  frame : ∀ a ms ms', MR a ms → ms'.irqMasks = ms.irqMasks → ms'.irqState = ms.irqState →
    ms'.timeState = ms.timeState → ms'.lastMachineTime = ms.lastMachineTime → MR a ms'

/-- `MachPlatF` and `IpiF` give `MachPlat`. -/
theorem MachPlatF.toT {MR : A → Fl4Spec.MachineState → Prop} (h : MachPlatF arI MR) (hI : IpiF arI MR) :
    MachPlat arI MR :=
  ⟨h.now, h.irqPending, h.take, fun a w m ms hR hw => by
    cases m
    · exact h.mask0 a w ms hR (by simp at hw; omega)
    · exact h.mask1 a w ms hR (by simpa using hw), h.ack, h.frame, hI⟩

/-- `MR` is independent of the memory (the joint relation moves the spec's
memory with FL4's). -/
theorem MachPlat.mem {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) {a : A}
    {ms : Fl4Spec.MachineState} (h : MR a ms) (m : Fl4Spec.Word64 → Fl4Spec.Word8) :
    MR a { ms with underlyingMemory := m } :=
  hM.frame a ms _ h rfl rfl rfl rfl

/-- **`NowAgree` at a related state** (module docstring): the platform's
clock read is the spec's at `σ`, and `σ.curTime ≤ r` from
`ValidMachineTime`. -/
theorem MachPlat.nowAgree {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) (hV : ValidMachineTime σ) : NowAgree arI a σ := by
  unfold NowAgree
  refine WP.spec_mono (hM.now a _ hR) ?_
  rintro r ⟨hv, -⟩
  refine ⟨gctState σ.machineState, ?_, ?_, rfl⟩
  · rw [hv]; exact doMachineOp_single (getCurrentTime_eq _)
  · rw [hv]; exact vmt_le_gct hV

/-- **`now` at a related state, with `MR` and `ValidMachineTime` after**
(the time stamp sets `curTime` to the value read). -/
theorem MachPlat.nowAt {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) :
    arI.now a ⦃ r => Fl4Spec.doMachineOp (Z := Unit) Fl4Spec.getCurrentTime σ =
      ({(r.1.bv, { σ with machineState := gctState σ.machineState })}, False) ∧
      MR r.2 (gctState σ.machineState) ∧
      ValidMachineTime { σ with curTime := r.1.bv, machineState := gctState σ.machineState } ⦄ := by
  refine WP.spec_mono (hM.now a _ hR) ?_
  rintro r ⟨hv, hR'⟩
  refine ⟨?_, hR', ?_⟩
  · rw [hv]; exact doMachineOp_single (getCurrentTime_eq _)
  · rw [hv]; exact validMachineTime_gct σ

/-- **`PPPlat.irq`'s shape at a related state**, with `MR` after. -/
theorem MachPlat.irqAt {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) :
    arI.irq_pending a ⦃ r => ∃ irq ms,
      Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
      (r.1 = true ↔ irq ≠ none) ∧ ms.underlyingMemory = σ.machineState.underlyingMemory ∧ MR r.2 ms ⦄ := by
  refine WP.spec_mono (hM.irqPending a _ hR) ?_
  rintro r ⟨h1, h2⟩
  exact ⟨_, _, doMachineOp_single (getActiveIRQ_eq true _), h1, rfl, h2⟩

/-- **`IrqPlat.take`'s shape at a related state**, with `MR` after. -/
theorem MachPlat.takeAt {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) {a : A}
    {σ : Fl4Spec.State Unit} (hR : MR a σ.machineState) :
    arI.take_pending_irq a ⦃ r => ∃ irq ms,
      Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.getActiveIRQ true) σ = ({(irq, { σ with machineState := ms })}, False) ∧
      (r.1 = syscall.NO_IRQ ↔ irq = none) ∧
      (∀ i, irq = some i → r.1.val = i.toNat ∧ ms.irqMasks i = false) ∧
      ms.underlyingMemory = σ.machineState.underlyingMemory ∧ MR r.2 ms ⦄ := by
  refine WP.spec_mono (hM.take a _ hR) ?_
  rintro r ⟨h1, h2, h3⟩
  exact ⟨_, _, doMachineOp_single (getActiveIRQ_eq true _), h1, fun i hi => ⟨h2 i hi, gaiLine_unmasked (b := true) (ms := σ.machineState) hi⟩, rfl, h3⟩

end

section Model
open Fl4Spec

theorem no_irq_bv : syscall.NO_IRQ.bv = BitVec.allOnes 64 := by
  unfold syscall.NO_IRQ
  rfl

/-- The model platform's pending line. -/
def modelTake (ms : MachineState) : U64 :=
  match gaiLine true ms with
  | none => syscall.NO_IRQ
  | some i => ⟨i.setWidth 64⟩

/-- **A model platform** whose arch state is the spec's machine state: the
clock and the interrupt reads run the spec's machine operations. -/
def modelArch : machine.Arch MachineState where
  private_device_frame _ _ := ok false
  dma_ram _ _ _ := ok false
  dma_frame a _ _ _ := ok a
  virtualization _ := ok 0#u64
  vcpu_capability _ _ := ok 0#u64
  vcpu_barrier a := ok a
  vcpu_sync a _ _ := ok a
  vcpu_release a _ := ok a
  invalidate_ept a _ _ := ok a
  tdx_active _ := ok false
  tdx_report a _ _ _ _ _ _ _ _ _ := ok (core.num.U64.MAX, a)
  tdx_extend_rtmr a _ _ _ _ _ _ _ := ok (core.num.U64.MAX, a)
  tdx_get_quote a _ _ := ok (core.num.U64.MAX, a)
  now ms := ok (⟨gctVal ms⟩, gctState ms)
  set_deadline a _ := ok a
  us_to_ticks _ x := ok x
  ticks_to_us _ x := ok x
  max_us _ := ok 0#u64
  kernel_wcet_ticks _ := ok 0#u64
  irq_pending ms := ok ((gaiLine true ms).isSome, gaiState ms)
  take_pending_irq ms := ok (modelTake ms, gaiState ms)
  mask_irq ms w m := ok { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m }
  ack_irq ms _ := ok ms
  irq_free a _ := ok a
  set_vspace a _ _ := ok a
  invalidate_page a _ _ := ok a
  invalidate_asid a _ := ok a
  invalidate_page_structures a _ := ok a
  ioapic_map a _ _ _ _ _ := ok (true, a)
  ioapic_map_remapped a _ _ _ _ _ _ := ok (true, a)
  num_ioapics _ := ok 0#u64
  ioapic_pins _ _ := ok 0#u64
  port_in a _ _ := ok (0#u64, a)
  port_out a _ _ _ := ok a
  fpu_flush a _ := ok a
  fpu_sanitise a _ := ok a
  fpu_reload a _ := ok a
  fpu_release a _ := ok a
  remote_stall a _ := ok a
  send_reschedule a _ := ok a
  putc a _ := ok a
  get_char a := ok (0#u64, a)
  halt a := ok a

/-- The model's relation: the four machine fields the reads depend on agree. -/
def modelMR (a ms : MachineState) : Prop :=
  a.irqMasks = ms.irqMasks ∧ a.irqState = ms.irqState ∧ a.timeState = ms.timeState ∧
    a.lastMachineTime = ms.lastMachineTime

theorem gaiLine_congr {b : Bool} {a ms : MachineState} (h1 : a.irqMasks = ms.irqMasks)
    (h2 : a.irqState = ms.irqState) : gaiLine b a = gaiLine b ms := by
  unfold gaiLine; rw [h1, h2]

theorem gctVal_congr {a ms : MachineState} (h3 : a.timeState = ms.timeState)
    (h4 : a.lastMachineTime = ms.lastMachineTime) : gctVal a = gctVal ms := by
  unfold gctVal gctNat; rw [h3, h4]

theorem modelTake_some {ms : MachineState} {i : Irq} (h : gaiLine true ms = some i) :
    modelTake ms ≠ syscall.NO_IRQ ∧ (modelTake ms).val = i.toNat := by
  unfold modelTake
  rw [h]
  have hv : (⟨i.setWidth 64⟩ : U64).bv.toNat = i.toNat := by
    show (i.setWidth 64).toNat = i.toNat
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (lt_trans i.isLt (by decide))
  refine ⟨fun e => ?_, hv⟩
  have e2 := congrArg (fun x : U64 => x.bv.toNat) e
  simp only at e2
  rw [hv, no_irq_bv, BitVec.toNat_allOnes] at e2
  have := i.isLt
  omega

theorem modelTake_none {ms : MachineState} (h : gaiLine true ms = none) : modelTake ms = syscall.NO_IRQ := by
  unfold modelTake; rw [h]

/-- **The model satisfies `MachPlatF`** (no oracle fact; `MachPlat` adds `IpiF`, which at `modelMR` needs the
oracle to avoid 126 / 127: P2/LocPlatModel `archT_machPlat`). -/
theorem modelArch_machPlat : MachPlatF modelArch modelMR where
  now a ms := by
    rintro ⟨h1, h2, h3, h4⟩
    show (ok ((⟨gctVal a⟩ : U64), gctState a) : Result (U64 × MachineState)) ⦃ _ ⦄
    rw [WP.spec_ok]
    refine ⟨gctVal_congr h3 h4, h1, h2, by show a.timeState + 1 = ms.timeState + 1; rw [h3], gctVal_congr h3 h4⟩
  irqPending a ms := by
    rintro ⟨h1, h2, h3, h4⟩
    show (ok ((gaiLine true a).isSome, gaiState a) : Result (Bool × MachineState)) ⦃ _ ⦄
    rw [WP.spec_ok, gaiLine_congr h1 h2]
    refine ⟨?_, h1, by show a.irqState + 1 = ms.irqState + 1; rw [h2], h3, h4⟩
    cases gaiLine true ms <;> simp
  take a ms := by
    rintro ⟨h1, h2, h3, h4⟩
    show (ok (modelTake a, gaiState a) : Result (U64 × MachineState)) ⦃ _ ⦄
    rw [WP.spec_ok]
    have hl := gaiLine_congr (b := true) h1 h2
    refine ⟨?_, fun i hi => (modelTake_some (hl.trans hi)).2, h1,
      by show a.irqState + 1 = ms.irqState + 1; rw [h2], h3, h4⟩
    show modelTake a = syscall.NO_IRQ ↔ _
    rw [← hl]
    cases e : gaiLine true a with
    | none => exact ⟨fun _ => rfl, fun _ => modelTake_none e⟩
    | some i => exact ⟨fun h => absurd h (modelTake_some e).1, fun h => by cases h⟩
  mask1 a w ms := by
    rintro ⟨h1, h2, h3, h4⟩ -
    show (ok _ : Result MachineState) ⦃ _ ⦄
    rw [WP.spec_ok]
    exact ⟨by show Function.update a.irqMasks _ true = Function.update ms.irqMasks _ true; rw [h1], h2, h3, h4⟩
  mask0 a w ms := by
    rintro ⟨h1, h2, h3, h4⟩ -
    show (ok _ : Result MachineState) ⦃ _ ⦄
    rw [WP.spec_ok]
    exact ⟨by show Function.update a.irqMasks _ false = Function.update ms.irqMasks _ false; rw [h1], h2, h3, h4⟩
  ack a w ms := by
    intro h
    show (ok a : Result MachineState) ⦃ _ ⦄
    rw [WP.spec_ok]; exact h
  frame a ms ms' := by
    rintro ⟨h1, h2, h3, h4⟩ e1 e2 e3 e4
    exact ⟨h1.trans e1.symm, h2.trans e2.symm, h3.trans e3.symm, h4.trans e4.symm⟩

end Model

end

end Fl4Proofs.P3
