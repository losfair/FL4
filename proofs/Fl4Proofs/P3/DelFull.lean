/-
P3 (DESIGN.md §9), CSpace: **FL4's `delete(slot, true)` refines l4v's
`cap_delete`** (`rec_del (CTEDeleteCall slot True)`): `finalise_slot
_immediate`, then `empty_slot` with the cleanup cap, for any cap, with
zombies, given the hypotheses of `DelRound` (`FinalHyp`, `FinObjHyp`,
`PPHypD`, `PostDelHyp`) and a bound `K` on CNode sizes with
`(psiD + 1) * (K + 1) < 2 ^ 64` (the fuel then suffices).

When it succeeds, the measure `psiD` is strictly smaller. The number of
MDB slots need not be: deleting a zombie stored in its own CNode can move
it to the CNode's first slot and leave every other slot as it was.
-/
import Fl4Proofs.P3.DelImm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`delete(slot, true)` refines `cap_delete`**, with `W` and the
readiness `Rd` threaded. -/
theorem delete_fullWR [Fl4Proofs.P1.PlainStore st] (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsWR (L := L) arI W Wp Rd th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hWs : W s a σ G) (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hbound : psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => ∃ σ' G', DState (L := L) th r.2.1 σ' G' ∧
      psiD (L.mem r.2.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
      MdbStep (L.mem s) G (L.mem r.2.1) G' ∧
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
          psiD (L.mem r.2.1) G' < psiD (L.mem s) G ∧ capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
          ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s) (L.mem r.2.1) y) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1)) ∧
      WPost W Wp r.1 r.2.1 r.2.2 σ' G' ⦄ := by
  unfold cdt.delete cdt.finalise_slot_immediate
  simp only [↓reduceIte]
  have hW : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
  have hnu := nuX_le hK hK6 hDS.2.1 hA.isSlot (K := K)
  apply WP.spec_bind (immediate_loop arI W Wp Rd th hP hF hH K hK hK6 sl hA s σ G s a layout.WALK_FUEL
    ⟨σ, G, hDS, by simp only; rw [hW]; omega, le_refl _, le_refl _, fun h => absurd h hxn, fun _ h => h,
      fun _ _ _ => ChgZ.refl _ _, MdbStep.refl hDS.1.2.2.1, hWs⟩
    (by rw [hW]))
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, hcd1, hps1, hnul1, hmS1, hres, hW1⟩
  simp only [uncurry_apply_pair] at hDS1 hcd1 hps1 hnul1 hmS1 hres hW1 ⊢
  rcases hres with ⟨f, rfl, hcl, hclw, hrd, hcz, hRd1⟩ | ⟨rfl, hrd⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (empty_stepWR' arI W Rd th hP (fun _ => hH.post) hH.empty s1 a1 σ1 G1 hDS1 hW1 hA hRd1 hcl
      hclw)
    rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth2, hps2, hcd2, hlt2, hmS2, hW2⟩
    simp only [uncurry_apply_pair] at hes hDS2 hx2 hoth2 hps2 hcd2 hlt2 hmS2 hW2 ⊢
    rw [WP.spec_ok]
    obtain ⟨v, hv⟩ := rd_cte_ok (σ2 := σ2) hrd (by simp only [true_or, Fl4Spec.NonDet.when, ↓reduceIte]; exact hes)
    refine ⟨σ2, G2, hDS2, le_trans hps2 hps1, le_trans hcd2 hcd1, hmS1.trans hmS2, Or.inl ⟨rfl, capDelete_ok hv, ?_, hx2,
      fun y hy hyx => (hcz y hy hyx).trans (ChgZ.of_eq (hoth2 y hy hyx))⟩, hW2⟩
    by_cases hn : capV (L.mem s1) (cslotAddr sl) = .Null
    · exact lt_of_le_of_lt hps2 (hnul1 hn)
    · exact lt_of_lt_of_le (hlt2 hn).2 hps1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σ1, G1, hDS1, hps1, hcd1, hmS1, Or.inr ⟨by trivial, capDelete_err (rd_cte_err hrd)⟩, hW1⟩

/-- **`delete(slot, true)` refines `cap_delete`**, with `W` threaded. -/
theorem delete_fullW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsW (L := L) arI W th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hWs : W s a σ G) (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hbound : psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => ∃ σ' G', DState (L := L) th r.2.1 σ' G' ∧
      psiD (L.mem r.2.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
      MdbStep (L.mem s) G (L.mem r.2.1) G' ∧
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
          psiD (L.mem r.2.1) G' < psiD (L.mem s) G ∧ capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
          ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s) (L.mem r.2.1) y) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1)) ∧
      W r.2.1 r.2.2 σ' G' ⦄ :=
  WP.spec_mono (delete_fullWR arI W W RdT th hP hF (hH.toR arI) K hK hK6 sl hA s a σ G hDS hWs hxn hbound)
    fun _ ⟨σ', G', h1, h2, h3, h4, h5, h6⟩ => ⟨σ', G', h1, h2, h3, h4, h5, WPost_self.1 h6⟩

/-- **`delete(slot, true)` refines `cap_delete`.** -/
theorem delete_full [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hbound : psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => ∃ σ' G', DState (L := L) th r.2.1 σ' G' ∧
      psiD (L.mem r.2.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
      MdbStep (L.mem s) G (L.mem r.2.1) G' ∧
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
          psiD (L.mem r.2.1) G' < psiD (L.mem s) G ∧ capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
          ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s) (L.mem r.2.1) y) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1)) ⦄ :=
  WP.spec_mono (delete_fullW arI WTrue th hP hF (delHypsW_true arI hO hPP hPD) K hK hK6 sl hA s a σ G hDS trivial
    hxn hbound) fun _ ⟨σ', G', h1, h2, h3, h4, h5, _⟩ => ⟨σ', G', h1, h2, h3, h4, h5⟩

/-! ## `DelHyp` discharged -/

theorem psiD_links_eq {th : TypedHeap} {m : U64 → U64} {G1 G2 : MdbGhost} (h1 : MdbLinks th m G1)
    (h2 : MdbLinks th m G2) : psiD m G1 = psiD m G2 :=
  le_antisymm (psiD_le h2 h1 (fun _ _ h => h) (fun _ _ _ h => h)) (psiD_le h1 h2 (fun _ _ h => h) (fun _ _ _ h => h))

/-- The invariant `DelHyp` needs: `DelInv`, the bound on `psiD` for the
fuel, and `FinInv` (for any ghost of the links). -/
def DelE (th : TypedHeap) (K : Nat) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  DelInv th (L.mem s) ∧ (∀ G, MdbLinks th (L.mem s) G → psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1) ∧
    KTyped th σ ∧ ∀ G, MdbLinks th (L.mem s) G → FinM (L.mem s) G

theorem MdbLinks.of_same_symm {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m' G)
    (hS : SlotsSame th m m') : MdbLinks th m G := by
  refine hM.of_same (fun x hx => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hS x hx
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm⟩

theorem finM_same {th : TypedHeap} {m m' : U64 → U64} (hF : ∀ G, MdbLinks th m G → FinM m G)
    (hS : SlotsSame th m m') : ∀ G, MdbLinks th m' G → FinM m' G := fun G hM =>
  (hF G (hM.of_same_symm hS)).of_caps hM.tree.nodup (fun z hz => hS.capV ((hM.members z).1 hz).1)

theorem psiD_slotsSame {th : TypedHeap} : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → psiD m' G = psiD m G :=
  fun _ _ _ hM hS => psiD_same hM (hM.of_same hS) hS

/-- **`DelHyp` holds** for the measure `psiD` and the invariant `DelE`,
from the hypotheses on finality, the object-specific finalisations, the
preemption points and `post_cap_deletion`. -/
theorem delHyp_full [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) :
    DelHyp (L := L) arI psiD th (DelE (L := L) th K) := by
  intro s a σ G c hCR ⟨hD, hB, hKT, hFM⟩ hA hxm
  have hxn : capV (L.mem s) (cslotAddr c) ≠ .Null := ((mem_nnS hCR.2.2.1 _).1 (List.mem_toFinset.2 hxm)).2
  refine WP.spec_mono (delete_full arI th hP hF hO hPP hPD K hK hK6 c hA s a σ G
    ⟨hCR, hD, hKT, hFM G hCR.2.2.1⟩ hxn (hB G hCR.2.2.1)) ?_
  rintro r ⟨σ', G', ⟨hCR', hD', hFI'⟩, hps', -, hmS', hcase⟩
  refine ⟨σ', G', ?_, hCR', ⟨hD', fun G'' hM'' => ?_, hFI'.kt,
    fun G'' hM'' => FinM.of_links hP hCR'.2.2.1 hM'' hFI'.fm⟩, hmS'⟩
  · rcases hcase with ⟨h1, h2, h3, -⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩
  · have := hB G hCR.2.2.1
    rw [psiD_links_eq hM'' hCR'.2.2.1]
    have := Nat.mul_le_mul_right (K + 1) hps'
    omega

/-- **`DelHypW` holds** for the measure `psiD` and the invariant `DelE` with
`W` (W-threading, with the readiness `Rd`). -/
theorem delHyp_fullWR [Fl4Proofs.P1.PlainStore st] (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsWR (L := L) arI W Wp Rd th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) :
    DelHypW (L := L) arI psiD th (fun s a σ G => DelE (L := L) th K s σ ∧ W s a σ G)
      (fun s a σ G => DelE (L := L) th K s σ ∧ Wp s a σ G) := by
  intro s a σ G c hCR ⟨⟨hD, hB, hKT, hFM⟩, hWs⟩ hA hxm
  have hxn : capV (L.mem s) (cslotAddr c) ≠ .Null := ((mem_nnS hCR.2.2.1 _).1 (List.mem_toFinset.2 hxm)).2
  refine WP.spec_mono (delete_fullWR arI W Wp Rd th hP hF hH K hK hK6 c hA s a σ G
    ⟨hCR, hD, hKT, hFM G hCR.2.2.1⟩ hWs hxn (hB G hCR.2.2.1)) ?_
  rintro r ⟨σ', G', ⟨hCR', hD', hFI'⟩, hps', -, hmS', hcase, hW'⟩
  refine ⟨σ', G', ?_, hCR', WPost.andL (P := fun s _ σ _ => DelE (L := L) th K s σ) ⟨hD', fun G'' hM'' => ?_, hFI'.kt,
    fun G'' hM'' => FinM.of_links hP hCR'.2.2.1 hM'' hFI'.fm⟩ hW', hmS'⟩
  · rcases hcase with ⟨h1, h2, h3, -⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩
  · have := hB G hCR.2.2.1
    rw [psiD_links_eq hM'' hCR'.2.2.1]
    have := Nat.mul_le_mul_right (K + 1) hps'
    omega

/-- **`DelHypW` holds** for the measure `psiD` and the invariant `DelE` with
`W` (W-threading). -/
theorem delHyp_fullW [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsW (L := L) arI W th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K) :
    DelHypW (L := L) arI psiD th (fun s a σ G => DelE (L := L) th K s σ ∧ W s a σ G)
      (fun s a σ G => DelE (L := L) th K s σ ∧ W s a σ G) :=
  delHyp_fullWR arI W W RdT th hP hF (hH.toR arI) K hK hK6

/-- The preemption point keeps `DelE` and `W`. -/
theorem rppHyp_fullW (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (K : Nat)
    (hPP : PPHypDW (L := L) arI W Wp th) :
    RPPHypW (L := L) arI th (fun s a σ G => DelE (L := L) th K s σ ∧ W s a σ G)
      (fun s a σ G => DelE (L := L) th K s σ ∧ Wp s a σ G) := by
  intro s a σ G hCR ⟨⟨hD, hB, hKT, hFM⟩, hWs⟩
  refine WP.spec_mono (hPP s a σ G ⟨hCR, hD, hKT, hFM G hCR.2.2.1⟩ hWs) ?_
  rintro r ⟨hS, σ', hcase, hCR', hW'⟩
  refine ⟨hS, σ', hcase, hCR', WPost.andL (P := fun s _ σ _ => DelE (L := L) th K s σ)
    ⟨hD.of_same hS, fun G'' hM'' => ?_, hKT.sub (pp_ksub hcase), finM_same hFM hS⟩ hW'⟩
  rw [psiD_links_eq hM'' (hCR.2.2.1.of_same hS), psiD_same hCR.2.2.1 (hCR.2.2.1.of_same hS) hS]
  exact hB G hCR.2.2.1

/-- The preemption point keeps `DelE`. -/
theorem rppHyp_full (th : TypedHeap) (K : Nat) (hPP : PPHypD (L := L) arI th) :
    RPPHyp (L := L) arI th (DelE (L := L) th K) := by
  intro s a σ G hCR ⟨hD, hB, hKT, hFM⟩
  refine WP.spec_mono (hPP s a σ G ⟨hCR, hD, hKT, hFM G hCR.2.2.1⟩) ?_
  rintro r ⟨hS, σ', hcase, hCR'⟩
  refine ⟨hS, σ', hcase, hCR', hD.of_same hS, fun G'' hM'' => ?_, hKT.sub (pp_ksub hcase), finM_same hFM hS⟩
  rw [psiD_links_eq hM'' (hCR.2.2.1.of_same hS), psiD_same hCR.2.2.1 (hCR.2.2.1.of_same hS) hS]
  exact hB G hCR.2.2.1

end

end

end Fl4Proofs.P3
