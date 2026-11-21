/-
P3 (DESIGN.md §9), invariant line G1 (ctq16, item 5 (b)): **`CKN` over
`delete_objects`**, the one hand leaf the generated family SpecInvCqHF3 needs
for `reset_untyped_cap` (spec side only, outside the JAtZ cone).

`detype` only removes objects: if the current thread's TCB survives it is
unchanged, and `cur_sc` / `cur_thread` are untouched (if ct's TCB goes,
`CKN` is vacuous there).
-/
import Fl4Proofs.P3.SpecInvCqHC
open Classical

namespace Fl4Proofs.P3.SInvQ.R16
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvQ.R14

noncomputable section

theorem ck_detype (S : Set ObjRef) {σ : State Unit} (h : CKN σ) : CKN (detype S σ) := by
  intro x hx
  change (if σ.curThread ∈ S then none else σ.kheap σ.curThread) = some (.tcb x) at hx
  split at hx
  · cases hx
  · exact h x hx

/-- **`delete_objects` keeps `CKN`.** -/
theorem ck_deleteObjects (ptr : Word) (bits : Nat) : CKK (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact ik_bind (ik_doMachineOp (fun _ _ h => h) _) fun _ => ik_modify fun σ h => ck_detype _ h

macro_rules | `(tactic| ck_leaf) => `(tactic| with_reducible exact R16.ck_deleteObjects _ _)

end

end Fl4Proofs.P3.SInvQ.R16
