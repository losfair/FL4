/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut6): **`cap_insert` into a
`PosOK` slot, and the TCB installs** (spec side only; imports SpecInvUtN6).

* `utN_leafP` / **`hv_capInsertP`**: ut4's `utN_leaf` / `hv_capInsertN` with the
  destination fact weakened from `DestRefV` (a lookup's slot) to `PosOK` (ut5:
  IfUnsafe + CnShape for that position; `posOK_of_destRef`), so the IRQ-node
  slot of SetIRQHandler (outside every untyped region, no cap to its object)
  is a destination too.
* `refRel_of_sameObj`: `same_object_as c c0` gives `RefRel c0 c` (same covered
  range, same shape, never a Zombie or untyped); `sameObj_thread`.
* **`ikN_checkCapAt_ins`**: the TCB installs' `check_cap_at newCap src
  (check_cap_at (ThreadCap t) slot (cap_insert newCap src (t, tcbCnodeIndex n)))`
  keeps `UtInv''` for `n < 6` with no premise: the two re-reads give `RefRel`
  for the new cap and the thread cap that makes the destination `DestRefV`.
-/
import Fl4Proofs.P3.SpecInvUtN6
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem utN_leafP {w w' : UView} (hI : UtInv'V w) (hN : UtNV w) {src dest : CslotPtr} {c0 c : Cap}
    {v : Option CslotPtr} (hd : w.2.1 dest = some .nullCap) (hs : w.2.1 src = some c0) (hR : RefRel c0 c)
    (hv : v = some src ∨ v = w.2.2.1 src) (hvd : v ≠ some dest) (hP : PosOK w dest)
    (h1 : w'.2.1 = Function.update w.2.1 dest (some c)) (h2 : w'.2.2.1 = Function.update w.2.2.1 dest v) :
    UtNV w' := by
  obtain ⟨-, hO, -⟩ := hI
  obtain ⟨hC, hU, hF, hK, hS, hZ, hB⟩ := hN
  obtain ⟨hRo, hRs, hRz, hRz0, hRu⟩ := hR
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hO x dest hx; rw [hd] at hc'; cases hc'; exact hcn rfl
  have hcap : ∀ sl x, w'.2.1 sl = some x → (sl = dest ∧ x = c) ∨ (sl ≠ dest ∧ w.2.1 sl = some x) :=
    fun sl x h => upd_cap (h1 ▸ h)
  have hold : ∀ sl, sl ≠ dest → w'.2.1 sl = w.2.1 sl := fun sl e => by rw [h1]; exact Function.update_of_ne e _ _
  have hut : ∀ u d b n f, w'.2.1 u = some (.untypedCap d b n f) → u ≠ dest ∧ w.2.1 u = some (.untypedCap d b n f) := by
    intro u d b n f h
    rcases hcap u _ h with ⟨-, e⟩ | h'
    · exact absurd e.symm (hRu d b n f)
    · exact h'
  have htg : ∀ x y, y ≠ dest → Relation.TransGen (parentOf w.2.2.1) x y →
      Relation.TransGen (parentOf w'.2.2.1) x y := fun x y hy h => by rw [h2]; exact (lu_tg hk hvd hy).2 h
  have hsd : ∀ r, r ∈ capRng c → src ≠ dest := by
    intro r hr e; subst e; rw [hd] at hs; cases hs; exact absurd (hRo hr) (by simp [capRng, objRefs])
  have hsR : ∀ r, r ∈ sRefs c → r ∈ sRefs c0 := by
    intro r hr
    obtain ⟨x, hx⟩ := shp_of_sRefs hr
    exact sRefs_of_shp (objRefs_of_capRng_shp (hRo (sRefs_sub_capRng c hr)) (hRs ▸ hx)) (hRs ▸ hx)
  have hz0 : ∀ r, r ∈ capRng c → ∀ a b n, c0 ≠ .zombie a b n := fun r hr a b n e => by
    rw [hRz0 a b n e] at hr; exact hr.elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- UtCh
    intro u d b n f hu s' c' r hs' hr hrd
    obtain ⟨hud, hu⟩ := hut u d b n f hu
    rcases hcap s' c' hs' with ⟨e, rfl⟩ | ⟨hne, hs'⟩
    · rw [e]
      have hsrc : Relation.TransGen (parentOf w.2.2.1) u src := hC u d b n f hu src c0 r hs (hRo hr) hrd
      have hsd' := hsd r hr
      have hdp : w'.2.2.1 dest = v := by rw [h2]; exact Function.update_self _ _ _
      show Relation.TransGen (parentOf w'.2.2.1) u dest
      rcases hv with hv | hv
      · exact Relation.TransGen.tail (htg u src hsd' hsrc) (show w'.2.2.1 dest = some src by rw [hdp, hv])
      · obtain ⟨b', hb0, hb'⟩ := Relation.TransGen.tail'_iff.1 hsrc
        have hb'' : w.2.2.1 src = some b' := hb'
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 hb0 with e | hb
        · rw [e] at hb''
          exact Relation.TransGen.single (show w'.2.2.1 dest = some u by rw [hdp, hv]; exact hb'')
        · have hb'' : w.2.2.1 src = some b' := hb'
          have hbd : b' ≠ dest := fun e => hk src (e ▸ hb'')
          exact Relation.TransGen.tail (htg u b' hbd hb) (show w'.2.2.1 dest = some b' by rw [hdp, hv]; exact hb'')
    · exact htg u s' hne (hC u d b n f hu s' c' r hs' hr hrd)
  · -- IfUnsafe
    intro p cp hp hne hin
    have hin' : InUtV w p.1 := by
      obtain ⟨u, d, b, n, f, hu, hr⟩ := hin; exact ⟨u, d, b, n, f, (hut u d b n f hu).2, hr⟩
    have hold' : ∀ s0 c0', w.2.1 s0 = some c0' → p.1 ∈ sRefs c0' → ∃ s c', w'.2.1 s = some c' ∧ p.1 ∈ sRefs c' :=
      fun s0 c0' hs0 hr0 => by
        have hs0d : s0 ≠ dest := fun e => by
          subst e; rw [hd] at hs0; cases hs0; exact sRefs_nn hr0 rfl
        exact ⟨s0, c0', (hold s0 hs0d).trans hs0, hr0⟩
    rcases hcap p cp hp with ⟨rfl, -⟩ | ⟨hpd, hp⟩
    · obtain ⟨s0, c0', hs0, hr0⟩ := hP.1 hin'
      exact hold' s0 c0' hs0 hr0
    · obtain ⟨s0, c0', hs0, hr0⟩ := hU p cp hp hne hin'
      have hs0d : s0 ≠ dest := fun e => by
        subst e; rw [hd] at hs0; cases hs0; exact sRefs_nn hr0 rfl
      exact ⟨s0, c0', (hold s0 hs0d).trans hs0, hr0⟩
  · -- CapFree
    intro u d b n f hu s' c' r hs' hr
    have hu' := (hut u d b n f hu).2
    rcases hcap s' c' hs' with ⟨-, rfl⟩ | ⟨-, hs'⟩
    · exact hF u d b n f hu' src c0 r hs (hRo hr)
    · exact hF u d b n f hu' s' c' r hs' hr
  · -- CapKind
    intro sa ca sb cb r ha hb hra hrb
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩ <;> rcases hcap sb cb hb with ⟨-, rfl⟩ | ⟨-, hb'⟩
    · rfl
    · rw [hRs]; exact hK src c0 sb cb r hs hb' (hRo hra) hrb
    · rw [hRs]; exact hK sa ca src c0 r ha' hs hra (hsR r hrb)
    · exact hK sa ca sb cb r ha' hb' hra hrb
  · -- CnShape
    intro sa ca r ha hr i c' hi hne
    rcases hcap (r, i) c' hi with ⟨e, rfl⟩ | ⟨hid, hi'⟩
    · -- the written slot
      subst e
      rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · have hr0 := hsR r hr
        have hz0' := hz0 r (sRefs_sub_capRng _ hr)
        exact slotShape_shp hRs.symm hz0' hRz (hP.2 src c0 hs hr0) (shp_of_sRefs hr0)
      · exact hP.2 sa ca ha' hr
    · rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
      · have hr0 := hsR r hr
        have hz0' := hz0 r (sRefs_sub_capRng _ hr)
        exact slotShape_shp hRs.symm hz0' hRz (hS src c0 r hs hr0 i c' hi' hne) (shp_of_sRefs hr0)
      · exact hS sa ca r ha' hr i c' hi' hne
  · -- ZFinal
    intro sz r b n hz s' c' hne hs'
    rcases hcap sz _ hz with ⟨-, e⟩ | ⟨hzd, hz'⟩
    · exact absurd e.symm (hRz r b n)
    · rcases hcap s' c' hs' with ⟨rfl, rfl⟩ | ⟨-, hs''⟩
      · intro hr
        by_cases e : src = sz
        · subst e; rw [hz'] at hs; cases hs; exact hz0 r (objRefs_sub_capRng _ hr) r b n rfl
        · have hrc : r ∈ capRng c0 := hRo (objRefs_sub_capRng _ hr)
          have hsh : shp c0 = some b := hK src c0 sz _ r hs hz' hrc (by simp [sRefs])
          exact hZ sz r b n hz' src c0 e hs (objRefs_of_capRng_shp hrc hsh)
      · exact hZ sz r b n hz' s' c' hne hs''
  · -- CnBits
    intro sa ca ha
    rcases hcap sa ca ha with ⟨-, rfl⟩ | ⟨-, ha'⟩
    · intro b hb; exact hB src c0 hs b (by rw [← hRs]; exact hb)
    · exact hB sa ca ha'

/-- **`cap_insert` of a derived non-untyped cap into a `PosOK` slot keeps `UtInv''`**. -/
theorem hv_capInsertP (c : Cap) (src dest : CslotPtr) :
    HV (fun w => UtInv''V w ∧ (∀ c0, w.2.1 src = some c0 → RefRel c0 c) ∧ PosOK w dest) UtInv''V
      (capInsert (Z := Unit) c src dest) := by
  unfold capInsert
  refine hv_getCap_bind fun w sc hw hsc => ?_
  obtain ⟨hw, hrr, hD⟩ := hw
  have hR := hrr sc hsc
  have hnu := hR.2.2.2.2
  have hnu' : isUntypedCap c = false := by
    cases c <;> first | rfl | exact absurd rfl (hnu _ _ _ _)
  refine hv_pure_bind ?_
  refine hv_getCap_bind fun w1 oc hw1 hoc => ?_
  subst w1
  refine hv_assert_bind fun hnull => ?_
  subst hnull
  have hk : ∀ x, w.2.2.1 x ≠ some dest := by
    intro x hx; obtain ⟨c', hc', hcn⟩ := hw.1.2.1 x dest hx; rw [hoc] at hc'; cases hc'; exact hcn rfl
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
  refine ⟨utInv'_leaf hw.1 hk ?hv hnu, utN_leafP hw.1 hw.2 hoc hsc hR ?hor ?hnd hD rfl rfl⟩
  case hv =>
    intro p hp
    split at hp
    · rename_i hpar
      obtain rfl := Option.some.inj hp
      have hnn := sameRegionAs_nn (of_decide_eq_true hpar).2.1
      refine ⟨fun e => ?_, sc, hsc, hnn⟩
      subst e; rw [hoc] at hsc; cases hsc; exact hnn rfl
    · have hp' : w.2.2.1 src = some p := hp
      exact ⟨fun e => hk src (e ▸ hp'), hw.1.2.1 src p hp'⟩
  case hor =>
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  case hnd =>
    intro hp
    split at hp
    · rename_i hpar
      have hnn := sameRegionAs_nn (of_decide_eq_true hpar).2.1
      obtain rfl := Option.some.inj hp
      rw [hoc] at hsc; cases hsc; exact hnn rfl
    · exact hk src hp


/-! ## `same_object_as` -/

set_option maxHeartbeats 4000000 in
theorem refRel_of_sameObj {c c0 : Cap} (h : sameObjectAs c c0) : RefRel c0 c := by
  cases c with
  | archObjectCap a =>
    cases c0 with
    | archObjectCap a0 =>
      refine ⟨?_, rfl, fun _ _ _ e => (by cases e), fun _ _ _ e => (by cases e), fun _ _ _ _ e => (by cases e)⟩
      cases a <;> cases a0 <;> simp_all [sameObjectAs, sameAobjectAs, archSameRegionAs, capRng, acRng, aobjRef]
    | _ => simp [sameObjectAs, sameRegionAs] at h
  | _ =>
    cases c0 <;> simp_all [sameObjectAs, sameRegionAs, RefRel, capRng, objRefs, shp, isEpCap, isNtfnCap,
      isCnodeCap, isThreadCap, isSchedContextCap, objRefOf, bitsOf]

theorem sameObj_thread {t : ObjRef} {c : Cap} (h : sameObjectAs (.threadCap t) c) : c = .threadCap t := by
  cases c <;> simp_all [sameObjectAs, sameRegionAs, isThreadCap, objRefOf]

/-! ## The TCB installs -/

/-- **The TCB installs' checked insert keeps `UtInv''`** (no premise). -/
theorem ikN_checkCapAt_ins (c : Cap) (src : CslotPtr) (t : ObjRef) (sl : CslotPtr) (n : Nat) (hn : n < 6) :
    IK UtInv'' (checkCapAt (Z := Unit) c src (checkCapAt (.threadCap t) sl
      (capInsert c src (t, tcbCnodeIndex n)))) := by
  show HV UtInv''V UtInv''V _
  unfold checkCapAt
  refine hv_getCap_bind fun w c' hw hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    refine hv_getCap_bind fun w1 c'' hw1 hc'' => ?_
    subst hw1
    split
    · rename_i hso2
      have e2 := sameObj_thread hso2
      subst e2
      refine hv_pre (hv_capInsertP c src _) fun w' e => ?_
      subst e
      refine ⟨hw, fun c0 h0 => ?_, posOK_of_destRef hw.2 ⟨sl, _, hc'', by simp [sRefs],
        fun _ _ _ e => (by cases e), ⟨n, hn, rfl⟩⟩⟩
      rw [hc'] at h0; cases h0; exact refRel_of_sameObj hso
    · exact hv_ret _ hw
  · exact hv_ret _ hw

end

end Fl4Proofs.P3.SInvU
