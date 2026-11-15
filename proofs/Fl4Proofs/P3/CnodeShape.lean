/-
P3 (DESIGN.md §9), CSpace: the caps CNode Copy, Mint, Move and Mutate put
in the destination have the source's shape and badge (or, for Mint, a
fresh badge from an unbadged source), come from a non-zombie, and from an
untyped cap only when it has no children (`copied_shape`) — what
`insert_full` and `move_full` need to keep `MdbInv`.
-/
import Fl4Proofs.P3.MdbFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem mask_shape {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c') :
    shape c' = shape c ∧ badgeF c' = badgeF c := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; simp [shape, badgeF])
  all_goals (repeat' split at h) <;> (simp at h; subst h; simp [shape, badgeF])

theorem update_shape {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hn : c' ≠ .Null) : shape c' = shape c ∧ (badgeF c' = badgeF c ∨ (badgeF c = 0#u64 ∧ pr = false)) := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; exact absurd rfl hn
    · rw [shr_eq _ _ (by decide) (by decide), objects_mask_eq] at h
      obtain ⟨m, hm, -⟩ := spec_exists (mask_spec (d &&& 63#u64) (by
        have : (d &&& 63#u64).val = d.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod d.val 6
        rw [this]; omega))
      rw [hm] at h; simp at h; subst h; simp [shape, badgeF]
  all_goals (repeat' split at h) <;> (simp at h; subst h; first | exact absurd rfl hn | simp_all [shape, badgeF])

section
variable {S : Type} {st : machine.Store S}

theorem derive_shape {s : S} {σ : Fl4Spec.State Unit} {slot : U64} {sl : Fl4Spec.CslotPtr} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hn : c' ≠ .Null)
    (hnc : NoChildrenRel (st := st) s σ slot sl) :
    shape c' = shape c ∧ badgeF c' = badgeF c ∧ isZb c = false ∧ (isUt c = true → ¬ ∃ x, σ.cdt x = some sl) := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    rw [hnc] at h
    by_cases hx : ∃ x, σ.cdt x = some sl
    · simp [hx, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from] at h
    · simp [hx, core.result.Result.Insts.CoreOpsTry.branch] at h
      subst h; simp [shape, badgeF, isZb, hx]
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h) <;>
    first | exact absurd rfl hn | simp_all [shape, badgeF, isZb, isUt]

theorem bind_ok_inv {α β : Type} {m : Result α} {f : α → Result β} {v : β} (h : Std.bind m f = ok v) :
    ∃ x, m = ok x ∧ f x = ok v := by
  cases m <;> simp_all

/-- The cap `copied_cap` produces, when not null, against the source cap. -/
theorem copied_shape {s : S} {σ : Fl4Spec.State Unit} {lbl length buf src : U64} {sl : Fl4Spec.CslotPtr}
    {srcC nc : capability.Cap} {mv : Bool}
    (h : cnode.copied_cap st s lbl length buf src srcC = ok (.Ok (nc, mv))) (hn : nc ≠ .Null)
    (hnc : NoChildrenRel (st := st) s σ src sl) :
    shape nc = shape srcC ∧ (mv = true → badgeF nc = badgeF srcC) ∧
      (mv = false → (badgeF nc = badgeF srcC ∨ badgeF srcC = 0#u64) ∧ isZb srcC = false ∧
        (isUt srcC = true → ¬ ∃ x, σ.cdt x = some sl)) := by
  unfold cnode.copied_cap at h
  obtain ⟨ct, -, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · simp [error.truncated] at h
    obtain ⟨i, -, h⟩ := bind_ok_inv h
    obtain ⟨r, -, h⟩ := bind_ok_inv h
    obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
    obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
    cases r1 with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
    | Ok v =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := derive_shape hr1 hn hnc
      obtain ⟨h5, h6⟩ := mask_shape hc1
      refine ⟨h1.trans h5, by simp, fun _ => ⟨Or.inl (h2.trans h6), by rw [← isZb_of_shape h5]; exact h3,
        fun hu => h4 (by rw [isUt_of_shape h5]; exact hu)⟩⟩
  · split at h
    · split at h
      · simp [error.truncated] at h
      obtain ⟨i, -, h⟩ := bind_ok_inv h
      obtain ⟨r, -, h⟩ := bind_ok_inv h
      obtain ⟨d, -, h⟩ := bind_ok_inv h
      obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
      obtain ⟨c2, hc2, h⟩ := bind_ok_inv h
      obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3, h4⟩ := derive_shape hr1 hn hnc
        have hn2 : c2 ≠ .Null := by
          intro e; subst e; simp [objects.derive_cap] at hr1; exact hn hr1.symm
        obtain ⟨h5, h6⟩ := update_shape hc2 hn2
        obtain ⟨h7, h8⟩ := mask_shape hc1
        refine ⟨h1.trans (h5.trans h7), by simp, fun _ => ⟨?_, by rw [← isZb_of_shape (h5.trans h7)]; exact h3,
          fun hu => h4 (by rw [isUt_of_shape (h5.trans h7)]; exact hu)⟩⟩
        rcases h6 with e | ⟨e, -⟩
        · exact Or.inl (h2.trans (e.trans h8))
        · rw [h8] at e; exact Or.inr e
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
      · split at h
        · simp [error.truncated] at h
        obtain ⟨d, -, h⟩ := bind_ok_inv h
        obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h5, h6⟩ := update_shape hc1 hn
        refine ⟨h5, fun _ => ?_, by simp⟩
        rcases h6 with e | ⟨-, e⟩
        · exact e
        · cases e
end

end

end Fl4Proofs.P3
