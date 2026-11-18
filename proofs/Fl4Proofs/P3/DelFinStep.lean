/-
P3 (DESIGN.md §9), CSpace: **FL4's `finalise_cap` against the spec's**, for
every cap: the always-trivial caps, CNode caps (to a zombie when final),
zombies (unchanged; the spec asserts they are final), and the object caps
(`FinObjHyp`).
-/
import Fl4Proofs.P3.DelW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The caps whose finalisation does nothing, final or not. -/
def TrivFin : capability.Cap → Prop
  | .Untyped .. | .Domain | .IrqControl | .SchedControl _ | .AsidControl | .IoPortControl => True
  | _ => False

theorem cap_cases (c : capability.Cap) (hc : c ≠ .Null) :
    TrivFin c ∨ (∃ p r gs g, c = .CNode p r gs g) ∨ (∃ p zt n, c = .Zombie p zt n) ∨ FinObjKind c := by
  cases c <;> simp [TrivFin, FinObjKind] at hc ⊢

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- What one finalisation of the cap `c` at `x` gives. -/
def FinPost (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (x : U64) (c : capability.Cap)
    (r : (capability.Cap × capability.Cap) × S × A) : Prop :=
  ∃ σ1 G1, ((absCap r.1.1, absCap r.1.2), σ1) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
    DState (L := L) th r.2.1 σ1 G1 ∧ capV (L.mem r.2.1) x = c ∧
    (∀ y, IsSlot th y → y ≠ x → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
      (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
    CleanCap r.1.2 ∧ CapWf r.1.2 ∧ (isZb c = true → r.1.1 = c) ∧
    (r.1.1 = .Null ∨ ∃ p zt n, r.1.1 = .Zombie p zt n ∧ ZCond th (L.mem r.2.1) G1 x p zt n) ∧
    MdbStep (L.mem s) G (L.mem r.2.1) G1 ∧ W r.2.1 r.2.2 σ1 G1 ∧ Rd r.2.1 r.2.2 σ1 G1 x

theorem finalise_triv (s : S) (a : A) (c : capability.Cap) (fin : Bool) (h : TrivFin c) :
    objects.finalise_cap st arI s a c fin false = ok ((.Null, .Null), s, a) := by
  cases c <;> simp only [TrivFin] at h <;> simp [objects.finalise_cap, objects.finalise_cap_object]

theorem finaliseCap_trivF (σ : Fl4Spec.State Unit) (c : capability.Cap) (fin : Bool) (h : TrivFin c) :
    Fl4Spec.finaliseCap (Z := Unit) (absCap c) fin σ = ({((.nullCap, .nullCap), σ)}, False) := by
  cases c <;> simp only [TrivFin] at h <;> first | rfl | (cases fin <;> rfl)

theorem mem_single {α σ : Type} {m : Fl4Spec.NonDet σ α} {s : σ} {x : α × σ} (h : m s = ({x}, False)) :
    x ∈ (m s).1 := by rw [h]; rfl

/-- On the native memory model a frame cap's finalisation only unmaps it. -/
theorem finalise_cap_frame_fin [Fl4Proofs.P1.PlainStore st] (s : S) (a : A) {c : capability.Cap} (hc : isFrame c = true) (b b' : Bool) :
    objects.finalise_cap st arI s a c b false = objects.finalise_cap st arI s a c b' false := by
  cases c <;> simp [isFrame] at hc
  simp [objects.finalise_cap, objects.finalise_cap_object, P1.plain_retire]

/-- **`finalise_cap` refines the spec's `finalise_cap`**, for every non-null
cap of a slot of the typed heap. -/
theorem fin_step [Fl4Proofs.P1.PlainStore st] (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap)
    (hO : FinObjHypWR (L := L) arI W Rd th) (hRT : RdTrivHyp (L := L) W Rd th) (hF : FinalHyp (L := L) th)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hW : W s a σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hcn : c ≠ .Null)
    (b : Bool) (hb : NeedsFin c → b = decide (Fl4Spec.isFinalCap' (absCap c) σ)) :
    objects.finalise_cap st arI s a c b false ⦃ r =>
      FinPost (L := L) W Rd th s σ G (cslotAddr sl) c r ⦄ := by
  have hRd : ¬ FinObjKind c → Rd s a σ G (cslotAddr sl) := hRT s a σ G sl c hDS hW hA hc hcn
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS
  have hcvx := capV_of_capAt hc
  have hcv := hV.abs hA hc
  have hen : EncWf c := by rw [capAt_words] at hc; exact decode_encWf hc
  obtain ⟨c', ac, hc', hca, -⟩ := hR.abs_cap hA
  rw [hc] at hc'; cases eq_of_ok_eq hc'
  have hsame : ∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s) y = capV (L.mem s) y ∨
      (capV (L.mem s) y = .Null ∧ isZb (capV (L.mem s) y) = false) := fun _ _ _ => Or.inl rfl
  rcases cap_cases c hcn with ht | ⟨p, r, gs, g, rfl⟩ | ⟨p, zt, n, rfl⟩ | ho
  · rw [finalise_triv arI s a c b ht, WP.spec_ok]
    refine ⟨σ, G, mem_single (finaliseCap_trivF σ c _ ht), ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcvx, hsame,
      trivial, trivial, fun h => ?_, Or.inl rfl, MdbStep.refl hM, hW, hRd ?_⟩
    · cases c <;> simp [TrivFin] at ht <;> simp [isZb] at h
    · cases c <;> simp [TrivFin] at ht <;> simp [FinObjKind]
  · -- a CNode cap
    rw [hb (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))]
    obtain ⟨hcvp, -⟩ := hcv
    have hr : r.val < 64 := hca.1.1
    by_cases hfin : Fl4Spec.isFinalCap' (absCap (.CNode p r gs g)) σ
    · obtain ⟨z, hz, hzv⟩ := shl_radix hr
      rw [decide_eq_true hfin]
      have e : objects.finalise_cap st arI s a (.CNode p r gs g) true
          false = ok ((.Zombie p r z, .Null), s, a) := by
        simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte, lift, hz, uncurry_apply_pair]
      rw [e, WP.spec_ok]
      refine ⟨σ, G, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcvx, hsame, trivial, trivial, fun h => by simp [isZb] at h,
        Or.inr ⟨p, r, z, rfl, cnode_zcond hR hP hM hA hc hfin hcvp hr hen.1 z hzv⟩, MdbStep.refl hM, hW,
        hRd (by simp [FinObjKind])⟩
      rw [decide_eq_true hfin]
      have hzb : zombieBits r = some r.val := zombieBits_cnode (by omega)
      simp only [absCap, Fl4Spec.finaliseCap, ↓reduceIte, hzb, hzv]; rfl
    · rw [decide_eq_false hfin]
      have e : objects.finalise_cap st arI s a (.CNode p r gs g) false
          false = ok ((.Null, .Null), s, a) := by
        simp [objects.finalise_cap, objects.finalise_cap_object]
      rw [e, WP.spec_ok]
      refine ⟨σ, G, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcvx, hsame, trivial, trivial, fun h => by simp [isZb] at h,
        Or.inl rfl, MdbStep.refl hM, hW, hRd (by simp [FinObjKind])⟩
      rw [decide_eq_false hfin]
      simp only [absCap, Fl4Spec.finaliseCap, Bool.false_eq_true, ↓reduceIte]; rfl
  · -- a zombie
    have hfz : Fl4Spec.isFinalCap' (absCap (.Zombie p zt n)) σ :=
      (hF s σ G sl _ ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hA hc hcn).choose_spec.2.2 rfl
    have e : objects.finalise_cap st arI s a (.Zombie p zt n) b
        false = ok ((.Zombie p zt n, .Null), s, a) := by
      simp [objects.finalise_cap, objects.finalise_cap_object]
    rw [e, WP.spec_ok]
    refine ⟨σ, G, ?_, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcvx, hsame, trivial, trivial, fun _ => rfl,
      Or.inr ⟨p, zt, n, rfl, ?_⟩, MdbStep.refl hM, hW, hRd (by simp [FinObjKind])⟩
    · rw [decide_eq_true hfz]
      show _ ∈ ((Fl4Spec.NonDet.assert _ >>= fun _ => pure _) σ).1
      exact mem_bind_nd (x := ((), σ)) ⟨rfl, rfl⟩ rfl
    · refine ⟨hca.1, hen, hD.zwf _ hA.isSlot _ _ _ hcvx, fun y hy hyx p' zt' n' e' => ?_, by rw [hcvx]; rfl,
        by rw [hcvx]; rfl, fun y _ _ => by rw [hcvx], fun y _ _ => by rw [hcvx, srB_zombie], ?_, ?_, ?_⟩
      · exact hD.zu y _ hy hA.isSlot hyx _ _ _ _ _ _ e' hcvx
      · rintro ⟨zt', n', e'⟩; rw [hcvx] at e'; cases e'; rfl
      · exact hFI.zombie_alone hM hA.isSlot hcvx
      · rw [hcvx]; exact CapAlike.refl _
  · -- an object cap
    have hbe : objects.finalise_cap st arI s a c b false =
        objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false := by
      by_cases hfr : isFrame c = true
      · exact finalise_cap_frame_fin arI s a hfr _ _
      · rw [hb (Or.inl ⟨ho, by simpa using hfr⟩)]
    rw [hbe]
    refine WP.spec_mono (hO s a σ G sl c ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hW hA hc ho trivial) ?_
    rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨hrem, hcl, hclw, σ1, G1, hmem, hDS1, hx1, hch, hst, hW1, hRd1⟩
    refine ⟨σ1, G1, hmem, hDS1, hx1, hch, hcl, hclw, fun h => ?_, ?_, hst, hW1, hRd1⟩
    · cases c <;> simp [FinObjKind] at ho <;> simp [isZb] at h
    simp only at hrem ⊢
    cases c with
    | Thread t =>
      by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Thread t)) σ
      · simp only [finRem, hfin, decide_true, ↓reduceIte] at hrem
        subst hrem
        exact Or.inr ⟨t, _, _, rfl, thread_zcond hR hP hDS1.1.2.2.1 hA hc hfin hcv hen hx1 hch⟩
      · simp only [finRem, hfin, decide_false, Bool.false_eq_true, ↓reduceIte] at hrem
        exact Or.inl hrem
    | _ => simp only [finRem] at hrem; first | exact Or.inl hrem | (simp [FinObjKind] at ho)

end

end

end Fl4Proofs.P3
