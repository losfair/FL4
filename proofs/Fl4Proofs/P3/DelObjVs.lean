/-
P3 (DESIGN.md §9), CSpace: **`FinWorkAt FinRestK` from the VSpace side**
(`finWorkAt_rest`): the caps left by `finWorkHyp_split` are the native
VSpace caps (`Vs.IsVsFin`: frames not mapped in an EPT, page tables,
directories, PDPTs, PML4s and ASID pools), whose finalisation `Vs.vs_fin`
proves, given the VSpace context at the state (`VsFinCoupling`: the ghost
sets with `Vs.VsFinHyps` and `Vs.VsFinCtx`).
-/
import Fl4Proofs.P3.DelObjK
import Fl4Proofs.P3.VsFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VSpace context at every related state** (the VSpace ghost sets,
the finalisations' hypotheses `Vs.VsFinHyps` and context `Vs.VsFinCtx`). -/
def VsFinCoupling (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost), DState (L := L) th s σ G →
    ∃ (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop),
      Vs.VsFinHyps st A arI th P L4 L3 L2 L1 SR ∧ Vs.VsFinCtx st th P L4 L3 L2 L1 SR s a σ G

/-- The caps of `FinRestK` among the finalised ones are the native VSpace
caps. -/
theorem isVsFin_of_rest {c : capability.Cap} (hk : FinRestK c) (hf : FinObjKind c) : Vs.IsVsFin c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hk
  cases c <;> simp only [FinObjKind] at hf <;> simp only [Vs.IsVsFin]
  case Endpoint => exact h3 ⟨_, _, _, _, _, _, rfl⟩
  case Notification => exact h1 ⟨_, _, _, _, rfl⟩
  case Reply => exact h2 ⟨_, _, rfl⟩
  case Thread => exact h4 ⟨_, rfl⟩
  case SchedContext => exact h5 ⟨_, _, rfl⟩
  case IrqHandler => exact h6 ⟨_, rfl⟩
  case Vcpu => exact h7 (Or.inl ⟨_, rfl⟩)
  case Ept => exact h7 (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))
  case IoPort => exact h8 ⟨_, _, _, rfl⟩
  case Frame p sz r d m ep a v =>
    cases ep
    · rfl
    · exact (h7 (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, rfl⟩))).elim

/-- **The VSpace caps' case of `FinWorkHyp`.** -/
theorem finWorkAt_rest [Fl4Proofs.P1.PlainStore st] (th : TypedHeap) (hV : VsFinCoupling (L := L) arI th) :
    FinWorkAt (L := L) arI FinRestK th := by
  intro s a σ G sl c hk hDS hA hc hfk hw
  obtain ⟨P, L4, L3, L2, L1, SR, hH, hX⟩ := hV s a σ G hDS
  exact WP.spec_mono (Vs.vs_fin hH s a σ G sl hDS hA hX c hc (isVsFin_of_rest hk hfk) _ hw)
    (fun r h => h.1.base)

end

end

end Fl4Proofs.P3
