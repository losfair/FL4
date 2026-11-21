/-
P3: **retype's word-level write frames** (for P1's `RetypeP1Step`): the
object loop of the types whose objects need no initialisation writes only
slot words (`create_loop_frame`); the reset writes only its region, the
untyped cap's slot and the preemption point's words (`reset_frame`).
-/
import Fl4Proofs.P3.UntypedTcbLoop
import Fl4Proofs.P3.UntypedResetRetype
import Fl4Proofs.P3.UntypedPml4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]


end

/-! ## The reset -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The words a reset may write: its region, the untyped cap's two cap
words, and the preemption point's words `PW`. -/
def ResetW (p sb x : U64) (PW : U64 → Prop) (w : U64) : Prop :=
  (p.val ≤ w.val ∧ w.val < p.val + 2 ^ sb.val) ∨ (x.val ≤ w.val ∧ w.val < x.val + 16) ∨ PW w

/-- **The reset's write frame**: `reset_untyped` on the slot `x` of an
untyped cap `Untyped p sb fi dev` writes only `ResetW p sb x PW`, given a
preemption point that writes only `PW` and keeps a property `Q` that the
zeroing and the slot's write keep. -/
theorem reset_frame {A' : Type} (arI : machine.Arch A') (s : S) (a : A') (x : U64) {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) x = ok (.Untyped p sb fi dev)) (hp8 : p.val % 8 = 0) (hsb4 : 4 ≤ sb.val)
    (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfib : fi.val ≤ 2 ^ sb.val)
    (hx : x.val % 8 = 0) (hxf : x.val + 16 ≤ 2 ^ 64)
    {Q : S → Prop} (hQk : EKept (L := L) Q p sb x) (hQ : Q s) {PW : U64 → Prop}
    (hPPF : ∀ (s1 : S) (a1 : A'), Q s1 → sched.preemption_point st arI s1 a1 ⦃ r => WFrame (L := L) s1 r.2.1 PW ∧ Q r.2.1 ⦄) :
    untyped.reset_untyped st arI s a x ⦃ res => WFrame (L := L) s res.2.1 (ResetW p sb x PW) ∧ Q res.2.1 ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb4; simpa using this
  have hcapW : ∀ (s1 : S) c, Q s1 → WFrame (L := L) s s1 (ResetW p sb x PW) →
      obj.Slot.set_cap st x s1 c ⦃ s' => WFrame (L := L) s s' (ResetW p sb x PW) ∧ Q s' ⦄ := fun s1 c hq hw =>
    WP.spec_mono (WP.spec_and (set_cap_frame s1 x c hx hxf) (hQk.2 s1 c hq)) fun s' ⟨h1, h2⟩ =>
      ⟨hw.trans (h1.mono fun w h => Or.inr (Or.inl h)), h2⟩
  unfold untyped.reset_untyped
  rw [slot_cap_eq, hcap]
  simp only [bind_ok, untyped.as_untyped]
  by_cases hfi0 : fi = 0#u64
  · simp only [hfi0, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨WFrame.refl _ _, hQ⟩
  simp only [hfi0, ↓reduceIte]
  have hfi0v : fi.val ≠ 0 := fun e => hfi0 (UScalar.eq_of_val_eq e)
  cases dev
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hsm : sb < untyped.RESET_CHUNK_BITS
    · rw [if_pos hsm]
      have h63 : (sb &&& 63#u64).val = sb.val := by
        have : (sb &&& 63#u64).val = sb.val % 64 := by
          simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
        rw [this]; omega
      obtain ⟨i1, hi1, hv1, -⟩ := spec_exists (UScalar.ShiftLeft_spec (1#u64 : U64) (sb &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      have hi1v : i1.val = 2 ^ sb.val := by
        rw [hv1, h63, Nat.shiftLeft_eq]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]
        exact Nat.pow_lt_pow_right (by decide) hsb
      simp only [lift, bind_ok, hi1, L.clear_free_eq]
      have hz := zr_frame (L := L) s p i1 hp8 (by rw [hi1v]; omega) (by rw [hi1v]; omega)
      have hq1 : Q (L.zr s p i1) := hQk.1 _ _ _ hp8 (by rw [hi1v]; omega) (le_refl _) (by rw [hi1v]) hQ
      refine WP.spec_bind (hcapW _ _ hq1 (hz.mono fun w h => Or.inl (by rw [hi1v] at h; exact h)))
        fun s2 h2 => (WP.spec_ok _).2 h2
    · rw [if_neg hsm]
      have hsb16 : 16 ≤ sb.val := by rw [reset_chunk_bits_eq] at hsm; exact Nat.le_of_not_lt hsm
      have hC : untyped.RESET_CHUNK.val = 65536 := by rw [reset_chunk_eq]; rfl
      obtain ⟨i, hi, hiv, -⟩ := spec_exists (U64.sub_spec (x := fi) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this]; omega))
      obtain ⟨i1, hi1, hi1v, -⟩ := spec_exists (U64.sub_spec (x := untyped.RESET_CHUNK) (y := 1#u64)
        (by have : (1#u64 : U64).val = 1 := rfl; rw [this, hC]; omega))
      rw [hi, hi1]
      simp only [bind_ok, lift]
      have hi1v' : i1.val = 65535 := by rw [hi1v, hC]; rfl
      have hov : (i &&& ~~~i1).val = (fi.val - 1) / 65536 * 65536 := by
        rw [and_not_mask i i1 hi1v', hiv]; rfl
      have hdv : 65536 ∣ 2 ^ sb.val := by
        have := Nat.pow_dvd_pow 2 hsb16; simpa using this
      obtain ⟨t, ht⟩ := hdv
      have hq : (fi.val - 1) / 65536 < t := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      unfold untyped.reset_untyped_loop
      refine loop.spec_decr_nat (measure := fun y => y.2.2.val)
        (inv := fun y => y.2.2.val % 65536 = 0 ∧ y.2.2.val + 65536 ≤ 2 ^ sb.val ∧
          WFrame (L := L) s y.1 (ResetW p sb x PW) ∧ Q y.1) _ _ _ ?_ ?_
      rotate_left
      · exact ⟨by rw [hov]; omega, by rw [hov, ht]; nlinarith, WFrame.refl _ _, hQ⟩
      rintro ⟨s1, a1, o⟩ ⟨ho1, ho2, hW1, hQ1⟩
      simp only at ho1 ho2 hW1 hQ1 ⊢
      unfold untyped.reset_untyped_loop.body
      have hiv' : (core.num.U64.wrapping_add p o).val = p.val + o.val := by
        rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      simp only [lift, bind_ok, L.clear_free_eq]
      have hz := zr_frame (L := L) s1 (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK
        (by unfold P1.Aligned; rw [hiv']; omega) (by rw [hC]) (by rw [hiv', hC]; omega)
      have hq1 := hQk.1 s1 _ _ (by unfold P1.Aligned; rw [hiv']; omega) (by rw [hC])
        (by rw [hiv']; omega) (by rw [hiv', hC]; omega) hQ1
      have hW1z : WFrame (L := L) s (L.zr s1 (core.num.U64.wrapping_add p o) untyped.RESET_CHUNK) (ResetW p sb x PW) :=
        hW1.trans (hz.mono fun w h => Or.inl (by rw [hiv', hC] at h; omega))
      refine WP.spec_bind (hcapW _ _ hq1 hW1z) fun s2 ⟨hW2, hQ2⟩ => ?_
      by_cases ho0 : o = 0#u64
      · rw [if_pos ho0]; exact (WP.spec_ok _).2 ⟨hW2, hQ2⟩
      rw [if_neg ho0]
      have ho0' : o.val ≠ 0 := fun e => ho0 (UScalar.eq_of_val_eq e)
      -- #52: the cap read back; `none` (a doomed transaction) ends the loop.
      rw [slot_cap_eq, capAt_capV]; simp only [bind_ok]
      have hU : ∀ c, untyped.as_untyped c ⦃ _ => True ⦄ := fun c => by
        cases c <;> exact (WP.spec_ok _).2 trivial
      refine WP.spec_bind (hU _) fun o' _ => ?_
      refine p0_if _ _ _ _ (fun _ => (WP.spec_ok _).2 ⟨hW2, hQ2⟩) (fun _ => ?_)
      refine WP.spec_bind (hPPF s2 a1 hQ2) ?_
      rintro ⟨r, s3, a2⟩ ⟨hW3, hQ3⟩
      simp only at hW3 hQ3
      have hW3' : WFrame (L := L) s s3 (ResetW p sb x PW) := hW2.trans (hW3.mono fun w h => Or.inr (Or.inr h))
      cases r with
      | Ok u =>
        simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
        have hsv : (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val = o.val - 65536 := by
          show (BitVec.ofNat 64 (max 0 (o.val - untyped.RESET_CHUNK.val))).toNat = _
          rw [hC]; simp; omega
        refine (WP.spec_ok _).2 ⟨⟨by rw [hsv]; omega, by rw [hsv]; omega, hW3', hQ3⟩, ?_⟩
        show (core.num.U64.saturating_sub o untyped.RESET_CHUNK).val < o.val
        rw [hsv]; omega
      | Err e =>
        simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
        simp only [bind_tc_ok, bind_ok]
        exact (WP.spec_ok _).2 ⟨hW3', hQ3⟩
  · simp only [↓reduceIte, bind_ok]
    refine WP.spec_bind (hcapW _ _ hQ (WFrame.refl _ _)) fun s2 h2 => (WP.spec_ok _).2 h2

end


end Fl4Proofs.P3
