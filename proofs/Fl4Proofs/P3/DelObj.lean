/-
P3 (DESIGN.md §9), CSpace: **`FinObjHyp` from the finalisations that do
work** (`finObjHyp_of`). Finalisation leaves the state unchanged for non-final caps without a guest
I/O grant, unmapped frames, and unbound IO-port caps. These cases are proved
here with the slots and ghost tree unchanged (`MdbStep.refl`). `FinWorkHyp`
covers the other final object caps, mapped frames, and IO-port caps carrying
a VCPU grant, whose grant is revoked on every cap finalisation.
-/
import Fl4Proofs.P3.DelRound
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The finalisations that do work: a final object cap but an IO port or a
frame, a mapped frame, or an IO port cap carrying a guest grant. -/
def FinWork (c : capability.Cap) (b : Bool) : Prop :=
  ((b = true ∨ ∃ f l owner, c = .IoPort f l owner ∧ owner ≠ 0#u64) ∧
    isFrame c = false ∧ ∀ f l, c ≠ .IoPort f l 0#u64) ∨
    ∃ p sz r d ep asid va, c = .Frame p sz r d true ep asid va

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`FinObjHyp` for the finalisations that do work.** -/
def FinWorkHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄

/-- The finalisations without work: FL4's and the spec's return their caps
and leave the state as it is. -/
theorem fin_idle [P1.PlainStore st] (s : S) (a : A) (σ : Fl4Spec.State Unit) (c : capability.Cap) (hk : FinObjKind c) (b : Bool)
    (hn : ¬ FinWork c b) :
    ∃ cl, objects.finalise_cap st arI s a c b false = ok ((.Null, cl), s, a) ∧
      ((absCap .Null, absCap cl), σ) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
      (cl = .Null ∨ cl = c) ∧ finRem c b = .Null ∧ ((∀ f l, c ≠ .IoPort f l 0#u64) → cl = .Null) := by
  unfold FinWork at hn
  cases c <;> simp only [FinObjKind] at hk
  case Frame p sz r d m ept asid va =>
    cases m
    · refine ⟨.Null, ?_, ?_, Or.inl rfl, rfl, fun _ => rfl⟩
      · simp [objects.finalise_cap, objects.finalise_cap_object, fl4_core.vcpu.finalise]
      · cases b <;> exact Set.mem_singleton _
    · exact absurd (Or.inr ⟨p, sz, r, d, ept, asid, va, rfl⟩) hn
  case IoPort f l owner =>
    have hv : owner = 0#u64 := by
      by_contra hv
      exact hn (Or.inl ⟨Or.inr ⟨f, l, owner, rfl, hv⟩, rfl,
        fun f' l' he => by cases he; exact hv rfl⟩)
    subst owner
    cases b
    · refine ⟨.Null, ?_, Set.mem_singleton _, Or.inl rfl, rfl, fun h => absurd rfl (h f l)⟩
      simp [objects.finalise_cap, objects.finalise_cap_object, fl4_core.vcpu.revoke_ports]
    · refine ⟨.IoPort f l 0#u64, ?_, Set.mem_singleton _, Or.inr rfl, rfl, fun h => absurd rfl (h f l)⟩
      simp [objects.finalise_cap, objects.finalise_cap_object, fl4_core.vcpu.revoke_ports]
  all_goals
    cases b
    case true => exact absurd (Or.inl ⟨Or.inl rfl, rfl, fun _ _ h => by cases h⟩) hn
    refine ⟨.Null, ?_, ?_, Or.inl rfl, rfl, fun _ => rfl⟩
    · simp [objects.finalise_cap, objects.finalise_cap_object, fl4_core.vcpu.finalise]
    · first
        | exact Set.mem_singleton _
        | (simp only [absCap, Fl4Spec.finaliseCap, Fl4Spec.archFinaliseCap, Fl4Spec.NonDet.when,
            Fl4Spec.NonDet.liftM, Bool.false_eq_true, ↓reduceIte]
           repeat (first
             | exact Set.mem_singleton _
             | exact mem_bind_nd (x := ((), σ)) (Set.mem_singleton _) (Set.mem_singleton _)
             | refine mem_bind_nd (x := ((), σ)) (Set.mem_singleton _) ?_
             | (split_ifs <;> exact Set.mem_singleton _)))

/-- **`FinObjHyp` from `FinWorkHyp`.** -/
theorem finObjHyp_of [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hW : FinWorkHyp (L := L) arI th) : FinObjHyp (L := L) arI th := by
  intro s a σ G sl c hDS hA hc hk
  by_cases hw : FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ))
  · exact hW s a σ G sl c hDS hA hc hk hw
  obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk _ hw
  rw [he, WP.spec_ok]
  have hcw : CapWf c := by
    obtain ⟨c', a', hc', hca, -⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc'; cases eq_of_ok_eq hc'; exact hca.1
  refine ⟨hrem.symm, ?_, ?_, σ, G, hmem, hDS, capV_of_capAt hc, fun _ _ _ => Or.inl rfl,
    MdbStep.refl hDS.1.2.2.1⟩
  · rcases hcl with h | h
    · rw [h]; trivial
    · by_cases hio : ∃ f l, c = .IoPort f l 0#u64
      · obtain ⟨f, l, rfl⟩ := hio; rw [h]; trivial
      · rw [hnio (fun f l e => hio ⟨f, l, e⟩)]; trivial
  · rcases hcl with h | h
    · rw [h]; trivial
    · rw [h]; exact hcw

end

end

end Fl4Proofs.P3
