/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut2): **`cap_insert` of a
cap that is not untyped keeps `UtInv'`** (spec side only), with no decode fact:
`cap_insert` itself asserts that the destination holds a null cap, so by CdtOK
it is a CDT leaf, and its new parent (the source when `should_be_parent_of`,
whose `same_region_as` makes the source cap non-null, or the source's parent)
holds a non-null cap. `set_untyped_cap_as_full` is a no-op for such a cap.
Covers CNode Copy/Mint/Mutate of non-untyped caps, the IPC grant, the TCB cap
installs, IRQ handler issue and the ASID pool cap of MakePool.
-/
import Fl4Proofs.P3.SpecInvUtI
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem hv_assert_bind {P Q : UView → Prop} {β : Type} {A : Prop} {k : Unit → NonDet (State Unit) β}
    (h : A → HV P Q (k ())) : HV P Q (NonDet.assert A >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hA, rfl⟩ := hy
  exact h hA σ hσ x hx

theorem hv_updateCdt (f : Cdt → Cdt) (w : UView) : HV (· = w) (· = vCdt (f w.2.2.1) w) (updateCdt (Z := Unit) f) := by
  unfold updateCdt
  refine hv_gets_bind (fun w => w.2.2.1) (fun _ => rfl) fun w1 hw1 => ?_
  subst w1
  exact hv_setCdt _ _

theorem sameRegionAs_nn {c c' : Cap} (h : sameRegionAs c c') : c ≠ .nullCap := by
  intro e; subst e; exact h

/-- The view after writing a non-untyped cap at a CDT leaf `dest` with new parent `v`. -/
theorem utInv'_leaf {w : UView} (hI : UtInv'V w) {dest : CslotPtr} {v : Option CslotPtr} {o : Bool} {c : Cap}
    (hk : ∀ x, w.2.2.1 x ≠ some dest) (hv : ∀ p, v = some p → p ≠ dest ∧ ∃ c', w.2.1 p = some c' ∧ c' ≠ .nullCap)
    (hnu : ∀ d b n f, c ≠ .untypedCap d b n f) :
    UtInv'V (vOrig dest o (vCdt (Function.update w.2.2.1 dest v) (vCap dest c w))) := by
  obtain ⟨hU, hO, hA⟩ := hI
  have hv' : v ≠ some dest := fun e => (hv dest e).1 rfl
  have hcap : ∀ sl, sl ≠ dest → (vOrig dest o (vCdt (Function.update w.2.2.1 dest v) (vCap dest c w))).2.1 sl = w.2.1 sl :=
    fun sl h => by show (vCap dest c w).2.1 sl = _; rw [vCap_cap, if_neg h]
  have hnd : ∀ sl d b n f, (vOrig dest o (vCdt (Function.update w.2.2.1 dest v) (vCap dest c w))).2.1 sl =
      some (.untypedCap d b n f) → sl ≠ dest := by
    intro sl d b n f h e; subst e
    have h' : (vCap sl c w).2.1 sl = _ := h
    rw [vCap_cap, if_pos rfl] at h'; exact hnu d b n f (Option.some.inj h')
  refine ⟨utInvV_shrinkD (w := w) ⟨fun p hp => Or.inl hp, fun sl d b n f h => ?_,
    fun s1 s2 d1 b1 n1 f1 d2 b2 n2 f2 h1 h2 hd => ?_, fun sl d b n f h ho => ?_⟩ hU, fun x q h => ?_,
    lu_acyc hk hv' hA⟩
  · rw [hcap sl (hnd sl d b n f h)] at h; exact same_capV hU.2.1 h
  · exact (lu_tg hk hv' (hnd s2 _ _ _ _ h2)).2 hd
  · show Function.update w.2.2.2 dest o sl = true
    rw [Function.update_of_ne (hnd sl d b n f h)]; exact ho
  · have h' : Function.update w.2.2.1 dest v x = some q := h
    by_cases e : x = dest
    · subst e; rw [Function.update_self] at h'
      obtain ⟨hq, c', hc', hcn⟩ := hv q h'
      exact ⟨c', by rw [hcap q hq]; exact hc', hcn⟩
    · rw [Function.update_of_ne e] at h'
      have hq : q ≠ dest := fun e' => hk x (e' ▸ h')
      obtain ⟨c', hc', hcn⟩ := hO x q h'
      exact ⟨c', by rw [hcap q hq]; exact hc', hcn⟩

/-- **`cap_insert` of a cap that is not untyped keeps `UtInv'`.** -/
theorem hv_capInsert_nonUt (c : Cap) (hnu : ∀ d b n f, c ≠ .untypedCap d b n f) (src dest : CslotPtr) :
    HV UtInv'V UtInv'V (capInsert (Z := Unit) c src dest) := by
  have hnu' : isUntypedCap c = false := by
    cases c <;> first | rfl | exact absurd rfl (hnu _ _ _ _)
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hw.2.1 x dest hx; rw [hoc] at hc'; cases hc'; exact hcn rfl
  unfold setUntypedCapAsFull
  rw [if_neg (fun h => by rw [hnu'] at h; exact Bool.false_ne_true h.2.1)]
  refine hv_pure_bind ?_
  refine hv_bind (hv_setCap _ _ _) fun _ => ?_
  refine hv_gets_bind (fun w => w.2.2.2) (fun _ => rfl) fun w2 hw2 => ?_
  subst w2
  refine hv_pure_bind ?_
  refine hv_gets_bind (fun w => w.2.2.1 src) (fun _ => rfl) fun w3 hw3 => ?_
  subst w3
  refine hv_gets_bind (fun w => w.2.2.1 dest) (fun _ => rfl) fun w4 hw4 => ?_
  subst w4
  refine hv_bind (hv_updateCdt _ _) fun _ => ?_
  refine hv_bind (hv_doExtendedOp _) fun _ => ?_
  refine hv_mono (hv_setOriginal _ _ _) fun w' e => ?_
  subst e
  refine utInv'_leaf hw hk (fun p hp => ?_) hnu
  split at hp
  · rename_i hpar
    obtain rfl := Option.some.inj hp
    have hsr := (of_decide_eq_true hpar).2.1
    have hnn := sameRegionAs_nn hsr
    refine ⟨fun e => ?_, sc, hsc, hnn⟩
    subst e; rw [hoc] at hsc; cases hsc; exact hnn rfl
  · have hp' : w.2.2.1 src = some p := hp
    refine ⟨fun e => hk src (e ▸ hp'), hw.2.1 src p hp'⟩

theorem ik_capInsert_nonUt (c : Cap) (hnu : ∀ d b n f, c ≠ .untypedCap d b n f) (src dest : CslotPtr) :
    IK UtInv' (capInsert (Z := Unit) c src dest) := hv_capInsert_nonUt c hnu src dest

end

end Fl4Proofs.P3.SInvU
