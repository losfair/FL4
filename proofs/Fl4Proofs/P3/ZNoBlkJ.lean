/-
P3 (DESIGN.md §9), KENTRY-PLAN g2i: **`ZNoBlk` from `SpecGlob` at a `JAtZ`**
(moved unchanged from XTopJointLiveCn, so that the `Steps.jat` callers with
`SpecGlob` at hand supply XTopJointStep's `ZNoBlk` premise).
-/
import Fl4Proofs.P3.SpecGlob
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
  {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`ZNoBlk` from `SpecGlob` at `J`** (module docstring). -/
theorem JAtZ.zNoBlk {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hsg : SpecGlob σ) : ZNoBlk Z.th (L.mem s) (L.ksb s) := by
  intro y hy p zt n hz k hk hb
  obtain ⟨hb1, hb2⟩ := hb
  have hP := J.xtop.rel.1
  have hIA := J.xtop.rel.2.2.2.2.2.1
  rcases J.del.zwf y hy p zt n hz with ⟨-, ht, -⟩ | ⟨-, hc, -⟩
  · rw [ht] at hk; cases hk
    have h1 := J.kern.hks p .tcb (J.zH.1 p (J.thT p ht)) (fun _ e => by cases e)
    have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
    rw [e12] at h1
    simp only [objSize] at hb2
    omega
  · rw [hc] at hk; cases hk
    have hfit := hP.fits p _ hc
    simp only [objSize] at hb2 hfit
    have hp1 : 1 ≤ 2 ^ zt.val := Nat.one_le_two_pow
    have hs0 : IsSlot Z.th (slotOf p 0) := ⟨p, 0, Or.inl ⟨zt.val, hc, by omega⟩, rfl⟩
    have hv0 : (slotOf p 0).val = p.val := by rw [slotOf_val (by omega)]; simp
    by_cases hin : p.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ p.val
    · exact hIA.ks p hb1 (by omega) hin _ hs0 ⟨by omega, by omega⟩
    · push_neg at hin
      obtain ⟨hin1, hin2⟩ := hin
      have hkf := J.intL.fit
      let i : U64 := ⟨BitVec.ofNat 64 ((p.val - (L.ksb s).val - 1248) / 32)⟩
      have hiv : i.val = (p.val - (L.ksb s).val - 1248) / 32 := by
        show (BitVec.ofNat 64 _).toNat = _; simp; omega
      have hi128 : i.val < 128 := by omega
      have hn := J.intL.node i hi128
      have hnv := nodeA_val hkf hi128
      have hpn : p = nodeA (L.ksb s) i := by
        by_contra hne
        rcases hP.disj p _ _ _ hc hn hne with h | h <;> simp only [objSize, pow_zero, mul_one] at h <;> omega
      obtain ⟨sl, hA, hsl⟩ := hy.abs
      obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := J.xtop.rel.2.1.1.abs_cap hA
      rw [hca0.abs] at hg0
      have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
      rw [hsl] at hc0
      have e0 : c0 = .Zombie p zt n := (capV_of_capAt hc0).symm.trans hz
      subst e0
      apply hsg.ref sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap]) (BitVec.ofNat 8 i.val)
      rw [J.xtop.fin.1.1.2.2.2.1.node i hi128, ← hpn]
      simp [absCap, Fl4Spec.objRefs]

end

end

end Fl4Proofs.P3
