/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, off1): **`OffReady`
(l4v `cur_sc_offset_ready`) across the entry's time stamp** (spec side only;
outside the `JAtZ` cone).

* `uts_off`: `updateTimeStamp` keeps the heap and the current SC, sets the
  current time to the clock value `gctN` and adds `now - prev` to the consumed
  time.
* `offReady_updateTimeStamp`: with `ValidMachineTime` (l4v
  `valid_machine_time`: `cur_time ≤ last_machine_time ≤` the cap, so the clock
  does not go back), `updateTimeStamp` keeps `OffReady`: `head + consumed ≤
  prev` gives `head + consumed + (now - prev) ≤ now`, with no wrap-around
  (everything stays below `now < 2^64`). l4v: the `update_time_stamp` step of
  `cur_sc_offset_ready` (the time increase is charged as consumed time).

This is the first writer of the off1 writer list (KENTRY-PLAN "off1"). The
other writers need the ready-queue / scheduler-action slices of l4v's
`valid_sched` (KENTRY-PLAN "off1"), so `OffReady` is not yet carried as a
whole-entry field.
-/
import Fl4Proofs.P3.SpecInvOffReady

open Classical

namespace Fl4Proofs.P3.SInvO
open Fl4Spec Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvV

noncomputable section

/-- The fields `OffReady` reads. -/
def offV (σ : State Unit) := (σ.kheap, σ.curSc, σ.curTime, σ.consumedTime)

/-- **`updateTimeStamp`'s effect on what `OffReady` reads.** -/
theorem uts_off {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) :
    x.2.kheap = σ.kheap ∧ x.2.curSc = σ.curSc ∧ x.2.curTime = BitVec.ofNat 64 (gctN σ.machineState) ∧
      x.2.consumedTime = σ.consumedTime + (BitVec.ofNat 64 (gctN σ.machineState) - σ.curTime) := by
  unfold updateTimeStamp at hx
  rw [sv_bind_gets, sv_bind_single (dmo_single (getCurrentTime_single σ.machineState))] at hx
  dsimp only at hx
  rw [sv_bind_pure, sv_bind_modify, sv_bind_modify, sv_bind_gets] at hx
  have key : ∀ {m : NonDet (State Unit) Unit} {s : State Unit}, FK offV m → x ∈ (m s).1 → offV x.2 = offV s :=
    fun hm h => hm _ _ h
  have e := key (by dk_auto0) hx
  unfold offV at e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  exact ⟨e1, e2, e3, e4⟩

/-- **`updateTimeStamp` keeps `OffReady`** under `ValidMachineTime` (module
docstring). -/
theorem offReady_updateTimeStamp {σ : State Unit} (hv : ValidMachineTime σ) (h : Sched.OffReady σ)
    {x : Unit × State Unit} (hx : x ∈ (updateTimeStamp (Z := Unit) σ).1) : Sched.OffReady x.2 := by
  obtain ⟨ek, es, et, ec⟩ := uts_off hx
  intro y n hy
  rw [ek, es] at hy
  have h1 := h y n hy
  have a1 : σ.curTime.toNat ≤ σ.machineState.lastMachineTime.toNat := BitVec.le_def.mp hv.1
  have a2 : σ.machineState.lastMachineTime.toNat ≤ gctN σ.machineState := by
    unfold gctN; exact le_min hv.2 (Nat.le_add_right _ _)
  have hN := gctN_le σ.machineState
  have hcap := timeCapS_lt
  have hp := σ.curTime.isLt
  have hc := σ.consumedTime.isLt
  rw [ec, et, BitVec.toNat_add, BitVec.toNat_sub, gctN_toNat]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  simp only [h64] at hcap hp hc ⊢
  have e1 : (18446744073709551616 - σ.curTime.toNat + gctN σ.machineState) % 18446744073709551616 =
      gctN σ.machineState - σ.curTime.toNat := by
    rw [show 18446744073709551616 - σ.curTime.toNat + gctN σ.machineState =
        (gctN σ.machineState - σ.curTime.toNat) + 18446744073709551616 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [e1, Nat.mod_eq_of_lt (by omega)]
  omega

end

end Fl4Proofs.P3.SInvO
