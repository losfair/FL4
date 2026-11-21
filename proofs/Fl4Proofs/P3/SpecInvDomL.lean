/-
P3 (DESIGN.md §9), invariant line G1 (invC): the least fixed point below a
pre-fixed point (CnodeRevoke's `lfp_le_prefixed`, verbatim; CnodeRevoke's cone
reaches FL4's side).
-/
import Fl4Spec.Monad
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice.Order
open Classical

namespace Fl4Proofs.P3.SInvDomL

section
variable {σ α ι : Type}

/-- `lfp` below a pre-fixed point (CnodeRevoke's `lfp_le_prefixed`, verbatim;
stated before `open Fl4Spec`). -/
theorem lfp_le_prefixed' (F : (ι → Fl4Spec.NonDet σ α) → ι → Fl4Spec.NonDet σ α) (f : ι → Fl4Spec.NonDet σ α)
    (hf : ∀ k t, F f k t ≤ f k t) (i : ι) (s : σ) : Fl4Spec.NonDet.lfp F i s ≤ f i s := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : Fl4Spec.NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  rw [hl]
  exact (sInf_le (show (f : ι → σ → Set (α × σ) × Prop) ∈ S from hf) : sInf S ≤ _) i s

end

end Fl4Proofs.P3.SInvDomL

