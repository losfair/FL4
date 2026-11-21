/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`ValidMachineTime`
is kept by the syscall entry** (spec side only; outside the `JAtZ` cone).

* `ValidMachineTime σ` [J] (l4v `valid_machine_time`): `cur_time ≤
  last_machine_time ≤` the clock's cap. The same body as XTopJointMachRel's
  `ValidMachineTime` (the premise `hR`/`MachPlat.nowAgree` of
  `kernel_entryJ26P` reads), which is in the `JAtZ` cone; the two are
  definitionally equal (`Iff.rfl` at the wiring site).
* `uts_out`: `updateTimeStamp` sets the current time and the last machine time
  to the clock value (`getCurrentTime` returns the new last machine time) and
  keeps the interrupt table and the masks.
* `wl_vmt`: every leaf (`setIrqState`, the masking machine operations and
  the ack keep both times; `updateTimeStamp` by `uts_out`).
* `kentry_validMachineTime` / `kirq_validMachineTime`: the whole syscall
  entry and the interrupt entry keep `ValidMachineTime`
  (SpecInvValidMachineTimeGen's `gk_fl4KernelEntrySyscall`,
  `gk_fl4CallKernel_irq`), with no side condition.
* History (invB's FINDING, fixed by fpu1): the spec's ReadFPU used to set the
  WHOLE machine state to any value (`doMachineOp (select univ >>= modify
  (fun _ => ms))`), so it could set the last machine time above the clock's
  cap (`readFpu_breaks_vmt`, deleted with that step). FL4 writes only the
  frame's 2696 bytes, and the spec's step is now Ext/Tcb's `fl4FpuToFrame`
  (only the user memory, only those bytes), a masking machine operation
  (`mt_fl4FpuToFrame`).
* `boot_vmt`: the spec's initial state (`Init.initASt`).
-/
import Fl4Proofs.P3.SpecInvValidMachineTimeGen

open Classical

namespace Fl4Proofs.P3.SInvV
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The cap of the spec's clock (`getCurrentTime`). -/
abbrev timeCapS : Nat := unat (-(getCurrentTimeBuffer + 1))

/-- **[J] l4v `valid_machine_time`** (module docstring). -/
def ValidMachineTime (σ : State Unit) : Prop :=
  σ.curTime ≤ σ.machineState.lastMachineTime ∧ unat σ.machineState.lastMachineTime ≤ timeCapS

/-! ## Monad facts -/

theorem sv_bind_single {σ α β : Type} {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {x : α × σ}
    (h : m s = ({x}, False)) : (m >>= f) s = f x.1 x.2 := by
  show NonDet.bind m f s = _
  unfold NonDet.bind
  rw [h]
  refine Prod.ext ?_ ?_
  · ext r; simp
  · simp

theorem sv_bind_gets {σ α β : Type} (g : σ → α) (f : α → NonDet σ β) (s : σ) :
    (NonDet.gets g >>= f) s = f (g s) s := sv_bind_single (m := NonDet.gets g) (x := (g s, s)) rfl

theorem sv_bind_modify {σ β : Type} (g : σ → σ) (f : Unit → NonDet σ β) (s : σ) :
    (NonDet.modify g >>= f) s = f () (g s) := sv_bind_single (m := NonDet.modify g) (x := ((), g s)) rfl

theorem sv_bind_pure {σ α β : Type} (a : α) (f : α → NonDet σ β) (s : σ) :
    ((pure a : NonDet σ α) >>= f) s = f a s := sv_bind_single (m := pure a) (x := (a, s)) rfl

/-- The value `getCurrentTime` computes (as a number). -/
def gctN (ms : MachineState) : Nat :=
  min timeCapS (unat ms.lastMachineTime + timeOracle (ms.timeState + 1))

/-- The machine state after `getCurrentTime`. -/
def gctS (ms : MachineState) : MachineState :=
  { ms with timeState := ms.timeState + 1, lastMachineTime := BitVec.ofNat 64 (gctN ms) }

theorem getCurrentTime_single (ms : MachineState) :
    getCurrentTime ms = ({(BitVec.ofNat 64 (gctN ms), gctS ms)}, False) := by
  unfold getCurrentTime
  rw [sv_bind_modify, sv_bind_gets, sv_bind_gets, sv_bind_pure, sv_bind_pure, sv_bind_modify]
  rfl

theorem dmo_single {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {v : α}
    {ms' : MachineState} (h : mop σ.machineState = ({(v, ms')}, False)) :
    doMachineOp (Z := Unit) mop σ = ({(v, { σ with machineState := ms' })}, False) := by
  unfold doMachineOp
  rw [sv_bind_gets]
  have hs : NonDet.selectF (mop σ.machineState) σ = ({((v, ms'), σ)}, False) := by
    unfold NonDet.selectF
    rw [h]
    refine Prod.ext ?_ rfl
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [sv_bind_single hs]
  dsimp only
  rw [sv_bind_modify]
  rfl

theorem gctN_le (ms : MachineState) : gctN ms ≤ timeCapS := Nat.min_le_left _ _

theorem gctN_toNat (ms : MachineState) : (BitVec.ofNat 64 (gctN ms)).toNat = gctN ms := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (gctN_le ms) (-(getCurrentTimeBuffer + 1)).isLt)

/-- **`updateTimeStamp`'s outcome** (module docstring). -/
theorem uts_out {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) :
    x.2.curTime = BitVec.ofNat 64 (gctN σ.machineState) ∧
      x.2.machineState.lastMachineTime = BitVec.ofNat 64 (gctN σ.machineState) ∧
      x.2.interruptStates = σ.interruptStates ∧ x.2.machineState.irqMasks = σ.machineState.irqMasks := by
  unfold updateTimeStamp at hx
  rw [sv_bind_gets, sv_bind_single (dmo_single (getCurrentTime_single σ.machineState))] at hx
  dsimp only at hx
  rw [sv_bind_pure, sv_bind_modify, sv_bind_modify, sv_bind_gets] at hx
  have key : ∀ {m : NonDet (State Unit) Unit} {s : State Unit}, FK vw m → x ∈ (m s).1 → vw x.2 = vw s :=
    fun hm h => hm _ _ h
  have e := key (by dk_auto0) hx
  unfold vw at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  exact ⟨e1, e2, e3, e4⟩

/-! ## The leaves -/

/-- The current time and the last machine time. -/
def tl (σ : State Unit) := (σ.curTime, σ.machineState.lastMachineTime)

theorem fk_tl_dmo {α : Type} {mop : NonDet MachineState α}
    (h : ∀ ms x, x ∈ (mop ms).1 → x.2.lastMachineTime = ms.lastMachineTime) : FK tl (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨h2a, e2⟩ := h2
  dsimp only at e2 h2a
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact Prod.ext rfl (h _ _ h2a)

theorem ik_of_tl {P : State Unit → Prop} (hP : ∀ σ σ', tl σ' = tl σ → P σ → P σ') {α : Type}
    {m : NonDet (State Unit) α} (h : FK tl m) : IK P m :=
  fun σ hσ x hx => hP σ x.2 (h σ x hx) hσ

theorem vmt_tl : ∀ σ σ' : State Unit, tl σ' = tl σ → ValidMachineTime σ → ValidMachineTime σ' := by
  intro σ σ' e h
  unfold tl at e; simp only [Prod.mk.injEq] at e
  unfold ValidMachineTime; rw [e.1, e.2]; exact h

theorem mask_lmt (m : Bool) (i : Irq) : ∀ ms x, x ∈ (maskInterrupt m i ms).1 →
    x.2.lastMachineTime = ms.lastMachineTime := by
  intro ms x hx; unfold maskInterrupt at hx; rw [Set.mem_singleton_iff.1 hx]

/-- The cap is below `allOnes` (`getCurrentTime_buffer_pos`). -/
theorem timeCapS_lt : timeCapS < 2 ^ 64 - 1 := by
  have hb : getCurrentTimeBuffer ≠ 0 := by
    have := getCurrentTime_buffer_pos
    intro e; unfold getCurrentTimeBuffer timeBufferConst MAX_PERIOD at e; rw [e] at this
    exact (BitVec.lt_irrefl _) this
  have hc : timeCapS ≠ 2 ^ 64 - 1 := by
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
  have hlt : timeCapS < 2 ^ 64 := (-(getCurrentTimeBuffer + 1)).isLt
  omega

/-- **The leaves of `ValidMachineTime`**: `updateTimeStamp` by `uts_out`,
`setIrqState`, the masking machine operations (the spec's ReadFPU step
`fl4FpuToFrame` among them since fpu1: `mt_fl4FpuToFrame`) and the IRQ ack
keep both times. -/
theorem wl_vmt : WL ValidMachineTime where
  view σ σ' e h := by
    refine vmt_tl σ σ' ?_ h
    unfold vw at e; simp only [Prod.mk.injEq] at e
    unfold tl; rw [e.1, e.2.1]
  uts σ _ x hx := by
    obtain ⟨e1, e2, -, -⟩ := uts_out hx
    refine ⟨by rw [e1, e2]; exact BitVec.le_refl _, ?_⟩
    show (x.2.machineState.lastMachineTime).toNat ≤ _
    rw [e2, gctN_toNat]; exact gctN_le _
  sis st i := by
    refine ik_of_tl vmt_tl ?_
    unfold setIrqState
    exact dk_bind (dk_modify fun _ => rfl) fun _ => fk_tl_dmo (mask_lmt _ i)
  msk mop h := ik_of_tl vmt_tl (fk_tl_dmo fun ms x hx => (h ms x hx).1)
  ack i := ik_of_tl vmt_tl (fk_tl_dmo (mask_lmt false i))

/-- **`ValidMachineTime` is kept by the spec's syscall entry** (no side
condition). -/
theorem kentry_validMachineTime {c : Syscall} {σ : State Unit} (h : ValidMachineTime σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ValidMachineTime y.2 :=
  gk_fl4KernelEntrySyscall true c _ wl_vmt σ h

/-- **`ValidMachineTime` is kept by the spec's interrupt entry**
(`fl4CallKernel true .interrupt`; Ext/Entry's step relation has only the
syscall entry). -/
theorem kirq_validMachineTime {σ : State Unit} (h : ValidMachineTime σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) true .interrupt) σ).1, ValidMachineTime y.2 :=
  gk_fl4CallKernel_irq true _ wl_vmt σ h

/-- **`ValidMachineTime` at boot** (`initASt`: both times 0). -/
theorem boot_vmt : ValidMachineTime (initASt (Z := Unit)) :=
  ⟨BitVec.le_refl _, by show (0 : Nat) ≤ _; exact Nat.zero_le _⟩

end

end Fl4Proofs.P3.SInvV
