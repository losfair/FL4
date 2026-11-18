/-
P3 (DESIGN.md §9), CSpace: **`delete_one` of a notification cap at `XTop`**
(`XDelNtfnHyp` from the notification's finalisation at `XTop`,
`xDelNtfnHyp_of`).

* `WXZ Z`: the deletion's invariant at the sets `Z` (any ghost tree), kept by
  the slot edits (`slotHypW_XZ`), the cleanup (`postDelHypW_XZ`) and the
  notification's finalisation (`finNtfnW_XZ`, from `XFinHyps.ntfn`'s shape
  `XFinAt FinNtfnK`; a non-final cap's finalisation does nothing).
* `delete_one_xtop`: DelOne's `delete_one_refines` at `WXZ Z`: an outcome
  of the spec's `cap_delete_one` with `XTopAt` there.
* `xDelNtfnHyp_of`: that outcome is the one `XDelNtfnHyp` is handed, the
  spec's notification `cap_delete_one` having one outcome
  (`detAt_capDeleteOne_ntfn`, SpecDet).
-/
import Fl4Proofs.P3.SpecDet
import Fl4Proofs.P3.DelOne
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The deletion's invariant at the sets `Z`** (`WX` with the sets fixed). -/
def WXZ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (kb : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) : Prop :=
  (∃ V, XTopAt (L := L) AR (Z.mv G V) s a σ) ∧ KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s) ∧
    (∀ t, Z.th t = some .tcb → t ∈ Z.T) ∧ L.ksb s = kb

theorem slotHypW_XZ (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (kb : U64) :
    SlotHypW (L := L) (A := A) (WXZ (L := L) AR Z kb) Z.th := by
  rintro s s' a σ σ' G G' ⟨⟨V, hX⟩, hK, hTh, hkb⟩ - ⟨hCR', -, hFI'⟩ hF hcn hSt
  have hMO := hSt.okv hX.rel.2.2.2.2.1
  have hct : σ'.curThread = σ.curThread := by have e := congrArg Fl4Spec.AbstractState.curThread hcn.1; exact e
  have hCO := CurOK.of_inv' hX.fin.2.2.2.2 hct hCR'.2.2.1 hMO.2.2
  exact ⟨⟨V, XTopAt.slotStepT hX (SlotFrame2.writesIn hF) hcn hCR' hFI' hMO hCO⟩, by rw [hF.1]; exact hK, hTh,
    by rw [hF.1]; exact hkb⟩

theorem postDelHypW_XZ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {kb : U64}
    (hXD : XPostDelHyp (L := L) arI AR Z.th) :
    PostDelHypW (L := L) arI (WXZ (L := L) AR Z kb) Z.th := by
  rintro s a σ G cl hDS ⟨⟨V, hX⟩, hK, hTh, hkb⟩ h1 h2 h3
  refine WP.spec_mono (hXD (Z.mv G V) s a σ cl rfl hX hK hTh hDS h1 h2 h3) ?_
  rintro r ⟨hS, hk', σ', hm, hCR, hX'⟩
  exact ⟨hS, σ', hm, hCR, ⟨V, hX'⟩, by rw [hk']; exact hK, hTh, by rw [hk']; exact hkb⟩

/-- **A notification cap's finalisation at `WXZ Z`**: when final, from
`XFinAt FinNtfnK`; otherwise it does nothing (`fin_idle`). -/
theorem finNtfnW_XZ [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {kb : U64} (hN : XFinAt (L := L) arI FinNtfnK AR Z.th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool)
    (hDS : DState (L := L) Z.th s σ G) (hW : WXZ (L := L) AR Z kb s a σ G) (hA : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r)) :
    objects.finalise_cap st arI s a (.Notification p b w r)
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) false ⦃ res =>
      res.1.1 = finRem (.Notification p b w r) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) ∧
      CleanCap res.1.2 ∧ CapWf res.1.2 ∧
      ∃ σ' G', ((absCap res.1.1, absCap res.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit)
          (absCap (.Notification p b w r)) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 ∧
        DState (L := L) Z.th res.2.1 σ' G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G' ∧
        WXZ (L := L) AR Z kb res.2.1 res.2.2 σ' G' ⦄ := by
  obtain ⟨⟨V, hX⟩, hK, hTh, hkb⟩ := hW
  set c : capability.Cap := .Notification p b w r
  by_cases hw : FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ))
  · refine WP.spec_mono (hN (Z.mv G V) s a σ sl c rfl hX hK hTh ⟨p, b, w, r, rfl⟩ hDS hA hc trivial hw) ?_
    rintro res ⟨h1, h2, h3, σ', G', h4, h5, -, -, h8, ⟨V', hX'⟩, hk'⟩
    exact ⟨h1, h2, h3, σ', G', h4, h5, h8, ⟨V', hX'⟩, by rw [hk']; exact hK, hTh, by rw [hk']; exact hkb⟩
  obtain ⟨cl, he, hmem, hcl, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c trivial _ hw
  rw [he, WP.spec_ok]
  have hcw : CapWf c := by
    obtain ⟨c', a', hc', hca, -⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc'; cases eq_of_ok_eq hc'; exact hca.1
  refine ⟨hrem.symm, ?_, ?_, σ, G, hmem, hDS, MdbStep.refl hDS.1.2.2.1, ⟨V, hX⟩, hK, hTh, hkb⟩
  · rcases hcl with h | h
    · rw [h]; trivial
    · rw [hnio (fun f l e => absurd e (by simp [c]))]; trivial
  · rcases hcl with h | h
    · rw [h]; trivial
    · rw [h]; exact hcw

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of a notification cap at `XTop`**: DelOne's
`delete_one_refines` with the invariant `WXZ Z` carried. -/
theorem delete_one_xtop [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {kb : U64} (hN : XFinAt (L := L) arI FinNtfnK AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR Z.th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hDS : DState (L := L) Z.th s σ Z.G)
    (hW : WXZ (L := L) AR Z kb s a σ Z.G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hk : capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ res =>
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ WXZ (L := L) AR Z kb res.1 res.2 σ' G' ⦄ := by
  have hP := (Classical.choose_spec hW.1).rel.1
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rw [hcv] at hk; subst hk
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full Z.th hP s σ Z.G sl _ hDS hA hc hcn
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  rw [hbf2 hNF] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  apply WP.spec_bind (finNtfnW_XZ arI hN s a σ Z.G sl p b w r hDS hW hA hc)
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨hrem, hcl, -, σ1, G1, hmem, hDS1, -, hW1⟩
  simp only [uncurry_apply_pair]
  refine WP.spec_mono (empty_stepW arI (WXZ (L := L) AR Z kb) Z.th hP (postDelHypW_XZ arI hXD) (slotHypW_XZ AR Z kb)
    s1 a1 σ1 G1 hDS1 hW1 hA .Null trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, -, -, -, -, -, -, -, hW2⟩
  refine ⟨σ2, G2, ?_, hW2⟩
  unfold Fl4Spec.capDeleteOne
  refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
  simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
  refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
  refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
  exact hes

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of a notification cap at `XTop`, the slots**: with the
notification's finalisation keeping every slot's cap (DelOne's
`NtfnKeepHyp`), the slot emptied, the others kept, the CSpace state and the
ghost step. -/
theorem delete_one_xtopK [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {kb : U64}
    (hN : XFinAt (L := L) arI FinNtfnK AR Z.th) (hXD : XPostDelHyp (L := L) arI AR Z.th)
    (hKeep : NtfnKeepHyp (L := L) arI Z.th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hDS : DState (L := L) Z.th s σ Z.G)
    (hW : WXZ (L := L) AR Z kb s a σ Z.G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {w r : Bool}
    (hk : capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ res =>
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ DState (L := L) Z.th res.1 σ' G' ∧
        capV (L.mem res.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem res.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) Z.G (L.mem res.1) G' ∧ WXZ (L := L) AR Z kb res.1 res.2 σ' G' ⦄ := by
  have hP := (Classical.choose_spec hW.1).rel.1
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rw [hcv] at hk; subst hk
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full Z.th hP s σ Z.G sl _ hDS hA hc hcn
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  rw [hbf2 hNF] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  apply WP.spec_bind (WP.spec_and (finNtfnW_XZ arI hN s a σ Z.G sl p b w r hDS hW hA hc)
    (hKeep s a σ Z.G sl p b w r _ hDS hA hc))
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨hrem, hcl, -, σ1, G1, hmem, hDS1, hm1, hW1⟩, hkeep⟩
  simp only [uncurry_apply_pair]
  refine WP.spec_mono (empty_stepW arI (WXZ (L := L) AR Z kb) Z.th hP (postDelHypW_XZ arI hXD) (slotHypW_XZ AR Z kb)
    s1 a1 σ1 G1 hDS1 hW1 hA .Null trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth, -, -, -, hm2, hW2⟩
  refine ⟨σ2, G2, ?_, hDS2, hx2, fun y hy hyx => by rw [hoth y hy hyx, hkeep y hy], hm1.trans hm2, hW2⟩
  unfold Fl4Spec.capDeleteOne
  refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
  simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
  refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
  refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
  exact hes

/-- **`XDelNtfnHyp` holds**, from the notification's finalisation at `XTop`
(`XFinAt FinNtfnK`, `XFinHyps.ntfn`'s shape), the cleanup at `XTop`
(`XPostDelHyp`) and `DelInv` at the `XTopAt` states [J]. -/
theorem xDelNtfnHyp_of [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hN : ∀ Z : XSets, Z.th = th → XFinAt (L := L) arI FinNtfnK AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR th)
    (hDI : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → DelInv th (L.mem s)) :
    XDelNtfnHyp (L := L) arI AR th := by
  intro Z s s' a a' σ σ' sl p b w r hth hX hK hTh hA hc hd hm
  subst hth
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨hX.rel.2.1, hDI Z s a σ rfl hX, hX.rel.2.2.1⟩
  have hW : WXZ (L := L) AR Z (L.ksb s) s a σ Z.G := ⟨⟨Z.vs, hX⟩, hK, hTh, rfl⟩
  have h := delete_one_xtop arI (hN Z rfl) hXD s a σ hDS hW hA hc
  rw [hd, WP.spec_ok] at h
  obtain ⟨σ2, G2, hm2, ⟨V2, hX2⟩, -, -, hk2⟩ := h
  obtain ⟨c, ac, hcA, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  rw [capV_of_capAt hcA] at hc
  subst hc
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm2 hm
  have e2 : σ2 = σ' := congrArg Prod.snd e
  subst e2
  exact ⟨G2, V2, hX2, hk2⟩

end

end

end Fl4Proofs.P3
