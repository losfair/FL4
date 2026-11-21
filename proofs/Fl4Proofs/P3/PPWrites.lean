/-
P3: **the preemption point's write frame from the layout alone**
(`pp_writes`): P1's `sched.preemption_point.pp` without `BlkOK`, for frames
of steps whose intermediate states keep no P1 invariant (the reset's chunk
loop, UtDom).
-/
import Fl4Proofs.P1.QueueKeeps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type _} {ar : machine.Arch A}

/-- **The preemption point's write frame** from the layout alone (no
`BlkOK`): `WORK_UNITS` and the current core's `CUR_TIME` and `CONSUMED`. -/
theorem pp_writes (hA : P0.ArchTotal ar) (s : S) (a : A)
    (hN : NodePlaced st ∅ s (L.cpu s)) :
    sched.preemption_point st ar s a ⦃ r => WritesIn st s r.2.1 (PPW st s) ⦄ := by
  have hk8 : (L.ksb s).val % 8 = 0 := by have := hN.align; simp only [LawfulStore.nodeBase] at this; omega
  have hf := hN.fits
  simp only [LawfulStore.nodeBase] at hf
  have hv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS).val = (L.ksb s).val + 40 := by
    simp [core.num.U64.wrapping_add_val_eq, layout.ks.WORK_UNITS, U64.size_def, U64.numBits]; omega
  have ha : Aligned (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) := by
    unfold Aligned; rw [hv]; omega
  unfold sched.preemption_point
  step with obj.ks_get.spec as ⟨i, _⟩
  step as ⟨w, _⟩
  step with obj.ks_set.spec as ⟨s1, e1⟩
  subst e1
  have W1 : WritesIn st s (L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w) (PPW st s) :=
    (writesIn_wr ha).mono fun b e => Or.inl e
  split
  · step with obj.ks_set.spec as ⟨s2, e2⟩
    subst e2
    try simp only [LawfulStore.ksb_wr]
    have W2 := (writesIn_wr (st := st) (s := L.wr s (core.num.U64.wrapping_add (L.ksb s) layout.ks.WORK_UNITS) w)
      (v := 0#u64) ha).mono fun b e => (Or.inl e : PPW st s b)
    have W12 := (W1.trans W2).mono fun b hb => hb.elim id id
    have hN2 := hN.ksb W12.1
    rw [← W12.2.1] at hN2
    refine WP.spec_bind (sched.update_timestamp.w (T := ∅) hA _ a hN2) ?_
    rintro ⟨s3, a1⟩ w3
    simp only at w3 ⊢
    have W := (W12.trans w3).mono fun b hb => hb.elim id (PPW.of W12.1 W12.2.1)
    have ip := hA.irq_pending
    have sf := sporadic.sufficient.ok (st := st) hA
    have hS : P0.StoreTotal st := L.total
    refine WP.spec_bind (ip a1) ?_
    rintro ⟨irq, a2⟩ -
    try dsimp only
    step*
    all_goals
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> first | exact sf _ _ _ _ | exact (WP.spec_ok _).2 trivial)
        fun ok1 _ => ?_
      split
      · exact (WP.spec_ok _).2 W
      · refine WP.spec_bind (P0.sched.is_cur_domain_expired.p0 st _ hS) fun b1 _ => ?_
        split
        · exact (WP.spec_ok _).2 W
        · split <;> exact (WP.spec_ok _).2 W
  · exact (WP.spec_ok _).2 W1

end
end Fl4Proofs.P3
