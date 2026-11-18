/-
P3 (DESIGN.md §9), CSpace: **FL4's `delete_deferred` refines l4v's
`cte_delete slot False`** (`rec_del (CTEDeleteCall slot False)`):
`finalise_slot_deferred`, then `empty_slot` if it succeeded.
-/
import Fl4Proofs.P3.DelEmpty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- What `delete_deferred` ends with. -/
def DDPost (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' G', DState (L := L) th res.2.1 σ' G' ∧ (nnS G').card ≤ (nnS G).card ∧
    psiD (L.mem res.2.1) G' ≤ psiD (L.mem s) G ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s) (L.mem res.2.1) y) ∧
    StrictChg th (L.mem s) (L.mem res.2.1) G G' (cslotAddr sl) ∧ MdbStep (L.mem s) G (L.mem res.2.1) G' ∧
    ((res.1 = .Ok () ∧ (∃ v, RD (.cTEDeleteCall sl false) σ (.ok v, σ')) ∧
        (capV (L.mem res.2.1) (cslotAddr sl) = .Null ∨ HomeZ (L.mem res.2.1) (cslotAddr sl))) ∨
      (res.1 = .Err .Preempted ∧ RD (.cTEDeleteCall sl false) σ (.error (), σ'))) ∧
    WPost W Wp res.1 res.2.1 res.2.2 σ' G'

theorem delete_deferred_refines [Fl4Proofs.P1.PlainStore st] (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap)
    (hP : Placed th) (hF : FinalHyp (L := L) th) (hH : DelHypsWR (L := L) arI W Wp Rd th)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hW : W s a σ G) (hfuel : psiD (L.mem s) G < 2 ^ 64 - 1) :
    cdt.delete_deferred st arI s a (cslotAddr sl) ⦃ res => DDPost (L := L) W Wp th s σ G sl res ⦄ := by
  unfold cdt.delete_deferred cdt.finalise_slot_deferred
  have hWF : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
  apply WP.spec_bind (deferred_loop arI W Wp Rd th hP hF hH sl hA s σ G s a layout.WALK_FUEL
    ⟨σ, G, hDS, by simp only; rw [hWF]; exact hfuel, le_refl _, le_refl _, fun _ h => h,
      fun _ _ _ => ChgOK.refl _ _, StrictChg.refl _ _ _, MdbStep.refl hDS.1.2.2.1, hW⟩)
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, hcd1, hps1, hch1, hsc1, hmS1, hres, hW1⟩
  simp only [uncurry_apply_pair] at hDS1 hcd1 hps1 hch1 hsc1 hmS1 hres hW1 ⊢
  rcases hres with ⟨f, rfl, hcl, hclw, hsf, hRd1, hrd⟩ | ⟨rfl, hrd⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases hs : f.success
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rw [hs] at hrd
      obtain ⟨v, hv⟩ := rd_cte_ok (σ2 := σ1) hrd (by simp only [Bool.false_eq_true, or_self]; rfl)
      exact ⟨σ1, G1, hDS1, hcd1, hps1, hch1, hsc1, hmS1, Or.inl ⟨rfl, ⟨v, hv⟩, Or.inr (hsf hs)⟩, hW1⟩
    · simp only [↓reduceIte]
      rw [hs] at hrd
      simp only [↓reduceIte] at hrd
      apply WP.spec_bind (empty_stepWR' arI W Rd th hP (fun _ => hH.post) hH.empty s1 a1 σ1 G1 hDS1 hW1 hA
        (hRd1 hs) hcl hclw)
      rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth2, hps2, hcd2, hlt2, hmS2, hW2⟩
      simp only [uncurry_apply_pair] at hes hDS2 hx2 hoth2 hps2 hcd2 hlt2 hmS2 hW2 ⊢
      rw [WP.spec_ok]
      obtain ⟨v, hv⟩ := rd_cte_ok (σ2 := σ2) hrd (by simp only [or_true, Fl4Spec.NonDet.when, ↓reduceIte]; exact hes)
      refine ⟨σ2, G2, hDS2, le_trans hcd2 hcd1, le_trans hps2 hps1,
        fun y hy hyx => (hch1 y hy hyx).trans (Or.inl (hoth2 y hy hyx)), ?_, hmS1.trans hmS2,
        Or.inl ⟨rfl, ⟨v, hv⟩, Or.inl hx2⟩, hW2⟩
      refine hsc1.trans (fun y hy hne _ => ?_) hps1 hps2
      by_cases hyx : y = cslotAddr sl
      · subst hyx
        by_cases hn : capV (L.mem s1) (cslotAddr sl) = .Null
        · rw [hx2, hn] at hne; exact absurd rfl hne
        · exact (hlt2 hn).2
      · exact absurd (hoth2 y hy hyx) hne
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σ1, G1, hDS1, hcd1, hps1, hch1, hsc1, hmS1, Or.inr ⟨rfl, rd_cte_err hrd⟩, hW1⟩

end

end

end Fl4Proofs.P3
