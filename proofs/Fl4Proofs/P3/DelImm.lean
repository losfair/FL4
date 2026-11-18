/-
P3 (DESIGN.md §9), CSpace: **FL4's `finalise_slot_immediate` refines l4v's
`finalise_slot slot True`** (`rec_del (FinaliseSlotCall slot True)`): each
round finalises the cap; a zombie that is not removable deletes its last
slot (`delete_deferred`, l4v `reduce_zombie slot True`: `cte_delete
end_slot False`) and, if the slot still holds it, counts down; then the
preemption point. The rounds are bounded: `psiD` does not grow, and the
zombie's count goes down, or `psiD` does.
-/
import Fl4Proofs.P3.DelDelete
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## A zombie's last slot -/

theorem natToCref_tcb {i : Nat} (hi : i < tcbSlots) : Fl4Spec.natToCref 3 i = Fl4Spec.tcbCnodeIndex i := by
  rw [natToCref_eq _ _ (by decide)]
  unfold tcbSlots at hi
  interval_cases i <;> rfl

/-- The spec's slot `i` of a zombie's object. -/
abbrev zSlot (p zt : U64) (i : Nat) : Fl4Spec.CslotPtr :=
  (p.bv, Fl4Spec.natToCref (Fl4Spec.zombieCteBits (zombieBits zt)) i)

theorem cnode_radix_lt {th : TypedHeap} (hP : Placed th) {p : U64} {r : Nat} (h : th p = some (.cnode r)) : r < 60 := by
  have := hP.fits p _ h
  simp only [objSize] at this
  by_contra hc
  have : 2 ^ 60 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem zSlot_abs {th : TypedHeap} (hP : Placed th) {p zt n : U64} (h : ZOK th p zt n) {i : Nat} (hi : i < n.val) :
    AbsSlot th (zSlot p zt i) ∧ cslotAddr (zSlot p zt i) = slotAddr p.bv (BitVec.ofNat 64 i) := by
  rcases h with ⟨h65, ht, hn⟩ | ⟨h65, hc, hn⟩
  · have hz : zombieBits zt = none := zombieBits_tcb h65
    have hi5 : i < tcbSlots := by omega
    refine ⟨⟨p, rfl, Or.inr ⟨ht, i, hi5, ?_⟩⟩, ?_⟩
    · show Fl4Spec.natToCref (Fl4Spec.zombieCteBits (zombieBits zt)) i = _
      rw [hz]; exact natToCref_tcb hi5
    · show cslotAddr (p.bv, Fl4Spec.natToCref (Fl4Spec.zombieCteBits (zombieBits zt)) i) = _
      rw [hz]
      exact cslotAddr_natToCref _ 3 i (by decide) (by unfold tcbSlots at hi5; omega)
  · have hz : zombieBits zt = some zt.val := zombieBits_cnode h65
    have hr : zt.val ≤ 64 := by have := cnode_radix_lt hP hc; omega
    refine ⟨⟨p, rfl, Or.inl ?_⟩, ?_⟩
    · show th p = some (.cnode (Fl4Spec.natToCref (Fl4Spec.zombieCteBits (zombieBits zt)) i).length)
      rw [hz]; simpa [Fl4Spec.zombieCteBits, natToCref_length _ _ hr] using hc
    · show cslotAddr (p.bv, Fl4Spec.natToCref (Fl4Spec.zombieCteBits (zombieBits zt)) i) = _
      rw [hz]
      exact cslotAddr_natToCref _ zt.val i hr (by omega)

theorem absCap_zombie_inj {c : capability.Cap} (hc : CapWf c) {p zt n : U64} (hz : CapWf (.Zombie p zt n))
    (h : absCap c = absCap (.Zombie p zt n)) : c = .Zombie p zt n := by
  cases c <;> simp [absCap] at h
  case Zombie p' zt' n' =>
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : p' = p := bv_inj h1
    have e3 : n' = n := UScalar.eq_of_val_eq h3
    have e2 : zt' = zt := by
      apply UScalar.eq_of_val_eq
      simp only [CapWf] at hc hz
      unfold zombieBits at h2
      split_ifs at h2 with ha hb hb <;> simp_all <;> omega
    rw [e1, e2, e3]

theorem wsub1 (n : U64) (h : 1 ≤ n.val) : (core.num.U64.wrapping_sub n 1#u64).val = n.val - 1 := by
  rw [core.num.U64.wrapping_sub_val_eq]
  have hb : n.val < 2 ^ 64 := n.hBounds
  have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size, U64.numBits]
  rw [hs, show (1#u64 : U64).val = 1 from rfl]
  rw [show n.val + (2 ^ 64 - 1) = (n.val - 1) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The immediate loop -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The count of the zombie at `x`, or `K`. -/
def nuX (K : Nat) (mem : U64 → U64) (x : U64) : Nat :=
  match capV mem x with
  | .Zombie _ _ n => n.val
  | _ => K

/-- A slot's cap kept, emptied, or a zombie at its home slot (`HomeZ`: what
the other slots' caps become in an immediate finalisation). -/
def ChgZ (mem0 mem : U64 → U64) (y : U64) : Prop :=
  capV mem y = capV mem0 y ∨ capV mem y = .Null ∨ HomeZ mem y

theorem ChgZ.refl (mem : U64 → U64) (y : U64) : ChgZ mem mem y := Or.inl rfl

theorem ChgZ.trans {m0 m1 m2 : U64 → U64} {y : U64} (h1 : ChgZ m0 m1 y) (h2 : ChgZ m1 m2 y) : ChgZ m0 m2 y := by
  rcases h2 with e | h | h
  · rcases h1 with e1 | n1 | ⟨zt, n, z1⟩
    · exact Or.inl (e.trans e1)
    · exact Or.inr (Or.inl (e.trans n1))
    · exact Or.inr (Or.inr ⟨zt, n, e.trans z1⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem ChgZ.of_eq {m0 m1 : U64 → U64} {y : U64} (h : capV m1 y = capV m0 y) : ChgZ m0 m1 y := Or.inl h

theorem ChgZ.of_chgOK {m0 m1 : U64 → U64} {y : U64} (h : ChgOK m0 m1 y) : ChgZ m0 m1 y := by
  rcases h with e | ⟨h | ⟨zt, n, e⟩, -⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨zt, n, e⟩)

theorem ChgZ.of_fin {m0 m1 : U64 → U64} {y : U64}
    (h : capV m1 y = capV m0 y ∨ (capV m1 y = .Null ∧ isZb (capV m0 y) = false)) : ChgZ m0 m1 y := by
  rcases h with e | ⟨e, -⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)

def ImmInv (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (K : Nat) (th : TypedHeap) (sl : Fl4Spec.CslotPtr) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (x : S × A × U64) : Prop :=
  ∃ σ G, DState (L := L) th x.1 σ G ∧
    psiD (L.mem x.1) G * (K + 1) + nuX K (L.mem x.1) (cslotAddr sl) < x.2.2.val ∧
    (nnS G).card ≤ (nnS G0).card ∧ psiD (L.mem x.1) G ≤ psiD (L.mem s0) G0 ∧
    (capV (L.mem x.1) (cslotAddr sl) = .Null → psiD (L.mem x.1) G < psiD (L.mem s0) G0) ∧
    (∀ y, RD (.finaliseSlotCall sl true) σ y → RD (.finaliseSlotCall sl true) σ0 y) ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem x.1) y) ∧
    MdbStep (L.mem s0) G0 (L.mem x.1) G ∧ W x.1 x.2.1 σ G

def ImmPost (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (sl : Fl4Spec.CslotPtr) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (res : core.result.Result cdt.Finalised error.Exc × S × A) : Prop :=
  ∃ σ' G', DState (L := L) th res.2.1 σ' G' ∧ (nnS G').card ≤ (nnS G0).card ∧
    psiD (L.mem res.2.1) G' ≤ psiD (L.mem s0) G0 ∧
    (capV (L.mem res.2.1) (cslotAddr sl) = .Null → psiD (L.mem res.2.1) G' < psiD (L.mem s0) G0) ∧
    MdbStep (L.mem s0) G0 (L.mem res.2.1) G' ∧
    ((∃ f, res.1 = .Ok f ∧ CleanCap f.cleanup ∧ CapWf f.cleanup ∧
        RD (.finaliseSlotCall sl true) σ0 (.ok (true, absCap f.cleanup), σ') ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem res.2.1) y) ∧
        (capV (L.mem res.2.1) (cslotAddr sl) ≠ .Null → Rd res.2.1 res.2.2 σ' G' (cslotAddr sl))) ∨
      (res.1 = .Err .Preempted ∧ RD (.finaliseSlotCall sl true) σ0 (.error (), σ'))) ∧
    WPost W Wp res.1 res.2.1 res.2.2 σ' G'

theorem nuX_zombie {K : Nat} {mem : U64 → U64} {x p zt n : U64} (h : capV mem x = .Zombie p zt n) :
    nuX K mem x = n.val := by unfold nuX; rw [h]

theorem nuX_le {K : Nat} {th : TypedHeap} (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    {mem : U64 → U64} (hD : DelInv th mem) {x : U64} (hx : IsSlot th x) : nuX K mem x ≤ K := by
  unfold nuX
  split
  · rename_i p zt n h
    rcases hD.zwf x hx p zt n h with ⟨-, -, hn⟩ | ⟨-, hc, hn⟩
    · unfold tcbSlots at hn; omega
    · exact le_trans hn (hK p _ hc)
  · exact le_refl _

/-- **FL4's immediate finalisation loop refines `finalise_slot slot True`.** -/
theorem immediate_loop [Fl4Proofs.P1.PlainStore st] (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsWR (L := L) arI W Wp Rd th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK6 : 6 ≤ K)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (s : S) (a : A) (fuel : U64) (hinv : ImmInv (L := L) (A := A) W K th sl s0 σ0 G0 (s, a, fuel))
    (hfuel : fuel.val ≤ 2 ^ 64 - 1) :
    cdt.finalise_slot_immediate_loop st arI s a (cslotAddr sl) fuel ⦃ res =>
      ImmPost (L := L) W Wp Rd th sl s0 σ0 G0 res ⦄ := by
  unfold cdt.finalise_slot_immediate_loop
  refine loop.spec_decr_nat (fun x => x.2.2.val)
    (fun x => ImmInv (L := L) W K th sl s0 σ0 G0 x ∧ x.2.2.val ≤ 2 ^ 64 - 1) _ _ _ ?_ ⟨hinv, hfuel⟩
  rintro ⟨s, a, fuel⟩ ⟨⟨σ, G, hDS, hlt, hcd, hps, hnul, htr, hcz, hmS, hW⟩, hfu⟩
  simp only at hlt hcd hps hnul htr hcz hmS hW hfu ⊢
  unfold cdt.finalise_slot_immediate_loop.body
  have hf : fuel > 0#u64 := by scalar_tac
  obtain ⟨fuel1, hv, hv1⟩ := spec_exists (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  have hv1' : fuel1.val + 1 = fuel.val := by scalar_tac
  simp only [hf, ↓reduceIte, hv, bind_ok, slot_cap_eq]
  obtain ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ := hDS
  have hxs := hA.isSlot
  obtain ⟨c, ac, hc, hca, hg⟩ := hR.abs_cap hA
  rw [hc]; simp only [bind_ok]
  by_cases hcn : c = .Null
  · subst hcn
    rw [cap_is_null_null]; simp only [bind_ok, ↓reduceIte, WP.spec_ok]
    have ha : ac = .nullCap := hca.abs
    subst ha
    exact ⟨σ, G, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcd, hps, hnul, hmS, Or.inl ⟨_, rfl, trivial, trivial,
      htr _ (rd_fin_null hg), hcz, fun h => absurd (capV_of_capAt hc) h⟩, hW⟩
  rw [cap_is_null_ne hcn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf1, hbf2, -⟩ := hF s σ G sl c ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hA hc hcn
  rw [is_final_with_cap_eq _ _ _ hc, hbf1]; simp only [bind_ok]
  rw [hca.abs] at hg
  have hcan : absCap c ≠ .nullCap := fun h => hcn (absCap_eq_null.1 h)
  have hcvx : capV (L.mem s) (cslotAddr sl) = c := capV_of_capAt hc
  apply WP.spec_bind (fin_step arI W Rd th hH.fin hH.triv hF hP s a σ G ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hW hA hc hcn
    bf hbf2)
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨σ1, G1, hmem, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, hx1, hch1, hcl, hclw, hzr, hrem,
    hfs1, hW1, hRd1⟩
  simp only [uncurry_apply_pair] at hmem hx1 hch1 hcl hclw hzr hrem hfs1 hW1 ⊢
  dsimp only at hR1 hV1 hM1 hC1 hI1 hD1 hmem hx1 hch1 hcl hclw hzr hrem hfs1 hW1 ⊢
  have hmS1 := hmS.trans hfs1
  obtain ⟨hps1, hcd1⟩ := psiD_fin hM hM1 (by rw [hx1, hcvx]) hch1
  have hcz1 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s1) y :=
    fun y hy hyx => (hcz y hy hyx).trans (ChgZ.of_fin (hch1 y hy hyx))
  rcases hrem with rfl | ⟨p, zt, n, rfl, hz⟩
  · simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, le_trans hcd1 hcd, le_trans hps1 hps,
      fun h => absurd (h.symm.trans (by rw [hx1])) (Ne.symm hcn), hmS1, Or.inl ⟨_, rfl, hcl, hclw,
      htr _ (rd_fin_removable hg hcan hmem trivial), hcz1, fun _ => hRd1⟩, hW1⟩
  obtain ⟨hrm, hrmS⟩ := removable_zombie hP hz.zok hA
  rw [hrm]; simp only [bind_ok]
  by_cases hrmv : n.val = 0 ∨ (n.val = 1 ∧ p = cslotAddr sl)
  · simp only [hrmv, decide_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, le_trans hcd1 hcd, le_trans hps1 hps,
      fun h => absurd (h.symm.trans (by rw [hx1])) (Ne.symm hcn), hmS1, Or.inl ⟨_, rfl, hcl, hclw,
      htr _ (rd_fin_removable hg hcan hmem (hrmS.2 hrmv)), hcz1, fun _ => hRd1⟩, hW1⟩
  simp only [hrmv, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hn1 : 1 ≤ n.val := by omega
  have hnrm : ¬ Fl4Spec.capRemoveable (absCap (.Zombie p zt n)) sl := fun h => hrmv (hrmS.1 h)
  have hxn1 : capV (L.mem s1) (cslotAddr sl) ≠ .Null := by rw [hx1]; exact hcn
  -- the zombie's count bounds the round
  have hnle : n.val ≤ nuX K (L.mem s) (cslotAddr sl) := by
    by_cases hzc : isZb c = true
    · rw [nuX_zombie (by rw [hcvx, hzr hzc])]
    · have : nuX K (L.mem s) (cslotAddr sl) = K := by
        unfold nuX; rw [hcvx]; cases c <;> simp [isZb] at hzc ⊢
      rw [this]
      rcases hz.zok with ⟨-, -, hn⟩ | ⟨-, hc', hn⟩
      · unfold tcbSlots at hn; omega
      · exact le_trans hn (hK p _ hc')
  apply WP.spec_bind (WP.spec_and (set_zombie th s1 σ1 G1 hR1 hV1 hP hM1 hC1 hI1 hD1 hA hxn1 hz.wf hz.enc hz.zok
    hz.zu hz.bx hz.bf hz.h1 hz.h2 hz.home) (set_zombie_frame hP s1 hxs _))
  rintro s2 ⟨⟨σ2, hsc2, ⟨hR2, hV2, hM2, hC2, hI2⟩, hD2, hps2, hx2, hoth2, hrv2⟩, hF2⟩
  have hrc2 : MdbStep (L.mem s1) G1 (L.mem s2) G1 := MdbStep.recap hM1 _ (by rw [hx2]; exact hz.al)
    (by rw [hx2]; exact fun _ _ _ _ _ _ => trivial)
    (fun z hz' hzx => hoth2 z ((hM1.members z).1 hz').1 hzx) (fun z hz' => hrv2 z ((hM1.members z).1 hz').1)
  have hmS2 : MdbStep (L.mem s0) G0 (L.mem s2) G1 := hmS1.trans hrc2
  have hFI2 := hFI1.set_zombie hM1 (ksub_of_eq (nks_setCap _ _) hsc2) hx2 hoth2 hz.zf
  have hW2 : W s2 a1 σ2 G1 := hH.zomb s1 s2 a1 σ1 σ2 G1 sl p zt n hW1 ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩
    ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hD2, hFI2⟩ hF2 hsc2 hA hxn1 hx2 hz.al hoth2 hrc2
  have hcz2 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s2) y :=
    fun y hy hyx => (hcz1 y hy hyx).trans (ChgZ.of_eq (hoth2 y hy hyx))
  -- the zombie's last slot
  have hwv := wsub1 n hn1
  set m := n.val - 1 with hm
  have hmn : m < n.val := by omega
  obtain ⟨hEa, hEaddr⟩ := zSlot_abs hP hz.zok hmn
  have hidx : obj.Slot.index p (core.num.U64.wrapping_sub n 1#u64) = ok (cslotAddr (zSlot p zt m)) := by
    rw [show obj.Slot.index p (core.num.U64.wrapping_sub n 1#u64) =
      ok (slotAddr p.bv (core.num.U64.wrapping_sub n 1#u64).bv) from spec_eq_ok (slot_index_spec _ _), hEaddr]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := n.hBounds; omega)]
    exact hwv
  simp only [lift, bind_ok, hidx]
  have hmul : psiD (L.mem s) G ≤ psiD (L.mem s) G * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hfuel2 : psiD (L.mem s2) G1 < 2 ^ 64 - 1 :=
    lt_of_le_of_lt (le_trans hps2 (le_trans hps1 hmul)) (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_lt_of_le hlt hfu))
  apply WP.spec_bind (delete_deferred_refines arI W Wp Rd th hP hF hH _ hEa s2 a1 σ2 G1
    ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hD2, hFI2⟩ hW2 hfuel2)
  rintro ⟨r3, s3, a3⟩ ⟨σ3, G3, ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩, hcd3, hps3, hch3, hsc3, hmS3, hres3, hW3⟩
  simp only [uncurry_apply_pair] at hcd3 hps3 hch3 hsc3 hmS3 hres3 hW3 ⊢
  dsimp only at hR3 hV3 hM3 hC3 hI3 hD3 hcd3 hps3 hch3 hsc3 hmS3 hres3 hW3 ⊢
  have hmS3' := hmS2.trans hmS3
  have hzS : absCap (.Zombie p zt n) = .zombie p.bv (zombieBits zt) (m + 1) := by
    show Fl4Spec.Cap.zombie p.bv (zombieBits zt) n.val = _; rw [show n.val = m + 1 by omega]
  have hcy' : ¬ (Fl4Spec.capCyclicZombie (absCap (.Zombie p zt n)) sl ∧ true = false) := fun h => by simp at h
  rcases hres3 with ⟨rfl, ⟨v3, hrd3⟩, hxend⟩ | ⟨rfl, hrd3⟩
  swap
  · -- the deletion of the last slot was preempted
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    have hz3 : RD (.reduceZombieCall (absCap (.Zombie p zt n)) sl true) σ2 (.error (), σ3) := by
      rw [hzS]; exact rd_reduce_true_err hrd3
    refine ⟨σ3, G3, ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩, le_trans hcd3 (le_trans hcd1 hcd),
      le_trans hps3 (le_trans hps2 (le_trans hps1 hps)), fun h => ?_, hmS3', Or.inr ⟨rfl,
      htr _ (rd_fin_reduce_err hg hcan hmem hnrm hcy' hsc2 hz3)⟩, hW3⟩
    have hne : capV (L.mem s3) (cslotAddr sl) ≠ capV (L.mem s2) (cslotAddr sl) := by rw [h, hx2]; simp
    have := hsc3 (cslotAddr sl) hxs hne (by
      by_cases he : cslotAddr sl = cslotAddr (zSlot p zt m)
      · right; rw [← he, hx2]; rfl
      · left; exact he)
    show psiD (L.mem s3) G3 < _
    exact lt_of_lt_of_le this (le_trans hps2 (le_trans hps1 hps))
  -- the last slot deleted: the cap in the slot now
  have hcz3 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s3) y := by
    intro y hy hyx
    by_cases hye : y = cslotAddr (zSlot p zt m)
    · subst hye
      rcases hxend with h | ⟨zt', n', h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨zt', n', h⟩)
    · exact (hcz2 y hy hyx).trans (ChgZ.of_chgOK (hch3 y hy hye))
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, slot_cap_eq, capAt_capV]
  have hps2' : psiD (L.mem s2) G1 ≤ psiD (L.mem s) G := le_trans hps2 hps1
  have hmulle : ∀ q, q ≤ psiD (L.mem s) G → q * (K + 1) ≤ psiD (L.mem s) G * (K + 1) :=
    fun q h => Nat.mul_le_mul_right _ h
  have hmullt : ∀ q, q < psiD (L.mem s) G → q * (K + 1) + (K + 1) ≤ psiD (L.mem s) G * (K + 1) := by
    intro q h
    have := Nat.mul_le_mul_right (K + 1) (show q + 1 ≤ psiD (L.mem s) G by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  obtain ⟨c3, ac3, hc3, hca3, hg3⟩ := hR3.abs_cap hA
  have hcv3 := capV_of_capAt hc3
  rw [hcv3]
  by_cases hun : c3 = .Zombie p zt n
  · -- unchanged: count the zombie down
    subst hun
    simp only [↓reduceIte, lift, bind_ok]
    set w := core.num.U64.wrapping_sub n 1#u64 with hwdef
    have hZw' : CapWf (capability.Cap.Zombie p zt w) := hz.wf
    have hZe' : EncWf (capability.Cap.Zombie p zt w) := hz.enc
    have hzok3 := hD3.zwf _ hxs _ _ _ hcv3
    have hZok' : ZOK th p zt w := by
      rcases hzok3 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨h1, h2, by rw [hwv]; omega⟩
      · exact Or.inr ⟨h1, h2, by rw [hwv]; omega⟩
    have hxn3 : capV (L.mem s3) (cslotAddr sl) ≠ .Null := by rw [hcv3]; simp
    simp only [Std.bind_assoc, bind_ok, uncurry_apply_pair]
    apply WP.spec_bind (WP.spec_and (set_zombie th s3 σ3 G3 hR3 hV3 hP hM3 hC3 hI3 hD3 hA hxn3 hZw' hZe' hZok'
      (fun y hy hyx p' zt' n' e => hD3.zu y _ hy hxs hyx _ _ _ _ _ _ e hcv3)
      (by rw [hcv3]; rfl) (by rw [hcv3]; rfl)
      (fun y hy hyx => by
        rw [hcv3]
        cases hu : isUt (capV (L.mem s3) y)
        · rw [srB_nonut_zombie hu, srB_nonut_zombie hu]
        · obtain ⟨q, sb, fi, d, e⟩ : ∃ q sb fi d, capV (L.mem s3) y = .Untyped q sb fi d := by
            cases h : capV (L.mem s3) y <;> rw [h] at hu <;> simp [isUt] at hu
            exact ⟨_, _, _, _, rfl⟩
          rw [e]; exact srB_ut_zombie_zombie q sb fi d p zt n w)
      (fun y _ _ => by rw [hcv3, srB_zombie])
      (fun hh => by obtain ⟨zt', n', e⟩ := hh; rw [hcv3] at e; cases e; rfl)) (set_zombie_frame hP s3 hxs _))
    rintro s4 ⟨⟨σ4, hsc4, hCR4, hD4, hps4, hx4, hoth4, hrv4⟩, hF4⟩
    have hrc4 : MdbStep (L.mem s3) G3 (L.mem s4) G3 := MdbStep.recap hM3 _
      (by rw [hx4, hcv3]; exact capAlike_zombie_zombie) (by rw [hx4]; exact fun _ _ _ _ _ _ => trivial)
      (fun z hz' hzx => hoth4 z ((hM3.members z).1 hz').1 hzx) (fun z hz' => hrv4 z ((hM3.members z).1 hz').1)
    have hmS4 : MdbStep (L.mem s0) G0 (L.mem s4) G3 := hmS3'.trans hrc4
    have hFI4 := hFI3.set_zombie hM3 (ksub_of_eq (nks_setCap _ _) hsc4) hx4 hoth4 (hFI3.zombie_alone hM3 hxs hcv3)
    have hW4 : W s4 a3 σ4 G3 := hH.zomb s3 s4 a3 σ3 σ4 G3 sl p zt w hW3 ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩
      ⟨hCR4, hD4, hFI4⟩ hF4 hsc4 hA hxn3 hx4 (by rw [hcv3]; exact capAlike_zombie_zombie) hoth4 hrc4
    have hcz4 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s4) y :=
      fun y hy hyx => (hcz3 y hy hyx).trans (ChgZ.of_eq (hoth4 y hy hyx))
    obtain ⟨v4, hz4⟩ := rd_reduce_true_dec (ptr := p.bv) (bits := zombieBits zt) (n := m) (sl := sl)
      (σ := σ2) (σ1 := σ3) (σ2 := σ4) hrd3 (by rw [← hzS]; rw [hca3.abs] at hg3; exact hg3)
      (by
        have : absCap (capability.Cap.Zombie p zt w) = .zombie p.bv (zombieBits zt) m := by
          show Fl4Spec.Cap.zombie p.bv (zombieBits zt) w.val = _; rw [hwv]
        rw [← this]; exact hsc4)
    rw [← hzS] at hz4
    have hphi : psiD (L.mem s4) G3 * (K + 1) + nuX K (L.mem s4) (cslotAddr sl) + 1 ≤
        psiD (L.mem s) G * (K + 1) + nuX K (L.mem s) (cslotAddr sl) := by
      rw [nuX_zombie hx4, hwv]
      have := hmulle _ (le_trans hps4 (le_trans hps3 hps2'))
      omega
    have hnul4 : capV (L.mem s4) (cslotAddr sl) = .Null → psiD (L.mem s4) G3 < psiD (L.mem s) G :=
      fun h => by rw [hx4] at h; cases h
    have hDS4 : DState (L := L) th s4 σ4 G3 := ⟨hCR4, hD4, hFI4⟩
    obtain ⟨⟨hR4, hV4, hM4, hC4, hI4⟩, hD4, hFI4⟩ := hDS4
    apply WP.spec_bind (hH.pp s4 a3 σ4 G3 ⟨⟨hR4, hV4, hM4, hC4, hI4⟩, hD4, hFI4⟩ hW4)
    rintro ⟨r5, s5, a5⟩ ⟨hS5, σ5, hcase, hCR5, hW5⟩
    simp only [uncurry_apply_pair] at hS5 hcase hCR5 hW5 ⊢
    have hD5 := hD4.of_same hS5
    have hmS5 := hmS4.same_right hM4 hS5
    have hcz5 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s5) y :=
      fun y hy hyx => (hcz4 y hy hyx).trans (ChgZ.of_eq (hS5.capV hy))
    have hFI5 := hFI4.of_same hM4 hS5 (pp_ksub hcase)
    have hps5 := psiD_same hM4 hCR5.2.2.1 hS5
    have hnu5 : nuX K (L.mem s5) (cslotAddr sl) = nuX K (L.mem s4) (cslotAddr sl) := by
      unfold nuX; rw [hS5.capV hxs]
    have hps5' : psiD (L.mem s5) G3 ≤ psiD (L.mem s0) G0 := by
      rw [hps5]; exact le_trans hps4 (le_trans hps3 (le_trans hps2' hps))
    have hnul5 : capV (L.mem s5) (cslotAddr sl) = .Null → psiD (L.mem s5) G3 < psiD (L.mem s0) G0 := by
      intro h; rw [hS5.capV hxs] at h; rw [hps5]; exact lt_of_lt_of_le (hnul4 h) hps
    rcases hcase with ⟨rfl, hpm⟩ | ⟨rfl, hpm⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      refine ⟨⟨⟨σ5, G3, ⟨hCR5, hD5, hFI5⟩, ?_, le_trans hcd3 (le_trans hcd1 hcd), hps5', hnul5, fun y hy => ?_,
        hcz5, hmS5, hW5⟩, by omega⟩,
        by omega⟩
      · show psiD (L.mem s5) G3 * (K + 1) + nuX K (L.mem s5) (cslotAddr sl) < fuel1.val
        rw [hps5, hnu5]; omega
      · exact htr _ (rd_fin_reduce hg hcan hmem hnrm hcy' hsc2 hz4 hpm hy)
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ5, G3, ⟨hCR5, hD5, hFI5⟩, le_trans hcd3 (le_trans hcd1 hcd), hps5', hnul5, hmS5, Or.inr ⟨rfl,
        htr _ (rd_fin_pp_err hg hcan hmem hnrm hcy' hsc2 hz4 hpm)⟩, hW5⟩

  · -- changed: the spec's assertion
    have hcw3 : CapWf c3 := hca3.1
    apply WP.spec_bind (Pₘ := fun r => r = (s3, a3)) (by
      cases c3 <;> simp only [WP.spec_ok]
      case Zombie p2 t2 n2 =>
        split_ifs with h1 h2 h3
        · exact absurd (by rw [h1, h2, h3]) hun
        · simp only [bind_ok, WP.spec_ok]
        · simp only [WP.spec_ok]
        · simp only [WP.spec_ok])
    rintro _ rfl
    simp only [uncurry_apply_pair]
    have hnc : absCap c3 ≠ .zombie p.bv (zombieBits zt) (m + 1) := by
      rw [← hzS]; intro h; exact hun (absCap_zombie_inj hcw3 hz.wf h)
    have hzx2 : capV (L.mem s2) (cslotAddr sl) = .Zombie p zt n := hx2
    have hpx_of : ¬ HomeZ (L.mem s2) (cslotAddr sl) → p ≠ cslotAddr sl := by
      intro hh e; apply hh; exact ⟨zt, n, by rw [hzx2, e]⟩
    have hchg : (c3 = .Null ∨ HomeZ (L.mem s3) (cslotAddr sl)) ∧ p ≠ cslotAddr sl := by
      by_cases he : cslotAddr sl = cslotAddr (zSlot p zt m)
      · rw [← he, hcv3] at hxend
        refine ⟨hxend, ?_⟩
        intro hpx
        have hm0 : m = 0 := by
          have hHa : cslotAddr (homeSl p zt) = p := home_addr p _
          have e1 : cslotAddr (homeSl p zt) = cslotAddr (zSlot p zt m) := by rw [hHa]; exact hpx.trans he
          have := cslotAddr_inj hP (home_abs hz.zok) hEa e1
          have e2 : slotOf p 0 = slotOf p m := by
            have h0 : cslotAddr (zSlot p zt 0) = slotAddr p.bv (BitVec.ofNat 64 0) :=
              (zSlot_abs hP hz.zok (show 0 < n.val by omega)).2
            have hz0 : zSlot p zt 0 = homeSl p zt := by
              obtain ⟨-, hE0⟩ := zSlot_abs hP hz.zok (show 0 < n.val by omega)
              exact cslotAddr_inj hP (zSlot_abs hP hz.zok (show 0 < n.val by omega)).1 (home_abs hz.zok)
                (by rw [hE0, hHa]; show (⟨p.bv + BitVec.ofNat 64 0 * 32#64⟩ : U64) = p; simp)
            show slotAddr p.bv (BitVec.ofNat 64 0) = slotAddr p.bv (BitVec.ofNat 64 m)
            rw [← h0, ← hEaddr, hz0, this]
          have hs0 : IsSlotAt th p 0 := by
            rcases hz.zok with ⟨-, ht, -⟩ | ⟨-, hc', -⟩
            · exact Or.inr ⟨ht, by decide⟩
            · exact Or.inl ⟨_, hc', by positivity⟩
          have hsm : IsSlotAt th p m := by
            rcases hz.zok with ⟨-, ht, hn⟩ | ⟨-, hc', hn⟩
            · exact Or.inr ⟨ht, by omega⟩
            · exact Or.inl ⟨_, hc', by omega⟩
          exact ((slotOf_inj hP hs0 hsm e2).2).symm
        exact hrmv (Or.inr ⟨by omega, hpx⟩)
      · rcases hch3 _ hxs he with e | ⟨h, hh⟩
        · rw [hcv3, hzx2] at e; exact absurd e hun
        · rw [hcv3] at h; exact ⟨h, hpx_of hh⟩
    have ha : absCap c3 = .nullCap ∨ Fl4Spec.isZombie (absCap c3) ∧ Fl4Spec.firstCslotOf (absCap c3) = sl ∧
        Fl4Spec.firstCslotOf (.zombie p.bv (zombieBits zt) (m + 1)) ≠ sl := by
      obtain ⟨h1, hpx⟩ := hchg
      rcases h1 with rfl | ⟨zt', n', e⟩
      · exact Or.inl rfl
      · rw [hcv3] at e; subst e
        have hz3 := hD3.zwf _ hxs _ _ _ hcv3
        refine Or.inr ⟨rfl, (homeSl_eq_iff hP hz3 hA).2 rfl, fun h => hpx ((homeSl_eq_iff hP hz.zok hA).1 h)⟩
    obtain ⟨v4, hz4⟩ := rd_reduce_true_chg (ptr := p.bv) (bits := zombieBits zt) (n := m) (sl := sl)
      (σ := σ2) (σ1 := σ3) hrd3 (by rw [hca3.abs] at hg3; exact hg3) hnc ha
    rw [← hzS] at hz4
    have hstr : psiD (L.mem s3) G3 < psiD (L.mem s2) G1 := by
      refine hsc3 _ hxs (by rw [hcv3, hzx2]; exact hun) ?_
      by_cases he : cslotAddr sl = cslotAddr (zSlot p zt m)
      · right; rw [← he, hzx2]; rfl
      · left; exact he
    have hphi : psiD (L.mem s3) G3 * (K + 1) + nuX K (L.mem s3) (cslotAddr sl) + 1 ≤
        psiD (L.mem s) G * (K + 1) + nuX K (L.mem s) (cslotAddr sl) := by
      have := hmullt _ (lt_of_lt_of_le hstr hps2')
      have := nuX_le hK hK6 hD3 hxs (K := K)
      omega
    have hps4 : psiD (L.mem s3) G3 ≤ psiD (L.mem s3) G3 := le_refl _
    have hnul4 : capV (L.mem s3) (cslotAddr sl) = .Null → psiD (L.mem s3) G3 < psiD (L.mem s) G :=
      fun _ => lt_of_lt_of_le hstr hps2'
    have hDS3' : DState (L := L) th s3 σ3 G3 := ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩
    obtain ⟨⟨hR3', hV3', hM3', hC3', hI3'⟩, hD3', hFI3'⟩ := hDS3'
    apply WP.spec_bind (hH.pp s3 a3 σ3 G3 ⟨⟨hR3', hV3', hM3', hC3', hI3'⟩, hD3', hFI3'⟩ hW3)
    rintro ⟨r5, s5, a5⟩ ⟨hS5, σ5, hcase, hCR5, hW5⟩
    simp only [uncurry_apply_pair] at hS5 hcase hCR5 hW5 ⊢
    have hD5 := hD3'.of_same hS5
    have hmS5 := hmS3'.same_right hM3' hS5
    have hcz5 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgZ (L.mem s0) (L.mem s5) y :=
      fun y hy hyx => (hcz3 y hy hyx).trans (ChgZ.of_eq (hS5.capV hy))
    have hFI5 := hFI3'.of_same hM3' hS5 (pp_ksub hcase)
    have hps5 := psiD_same hM3' hCR5.2.2.1 hS5
    have hnu5 : nuX K (L.mem s5) (cslotAddr sl) = nuX K (L.mem s3) (cslotAddr sl) := by
      unfold nuX; rw [hS5.capV hxs]
    have hps5' : psiD (L.mem s5) G3 ≤ psiD (L.mem s0) G0 := by
      rw [hps5]; exact le_trans hps4 (le_trans hps3 (le_trans hps2' hps))
    have hnul5 : capV (L.mem s5) (cslotAddr sl) = .Null → psiD (L.mem s5) G3 < psiD (L.mem s0) G0 := by
      intro h; rw [hS5.capV hxs] at h; rw [hps5]; exact lt_of_lt_of_le (hnul4 h) hps
    rcases hcase with ⟨rfl, hpm⟩ | ⟨rfl, hpm⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      refine ⟨⟨⟨σ5, G3, ⟨hCR5, hD5, hFI5⟩, ?_, le_trans hcd3 (le_trans hcd1 hcd), hps5', hnul5, fun y hy => ?_,
        hcz5, hmS5, hW5⟩, by omega⟩,
        by omega⟩
      · show psiD (L.mem s5) G3 * (K + 1) + nuX K (L.mem s5) (cslotAddr sl) < fuel1.val
        rw [hps5, hnu5]; omega
      · exact htr _ (rd_fin_reduce hg hcan hmem hnrm hcy' hsc2 hz4 hpm hy)
    · simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨σ5, G3, ⟨hCR5, hD5, hFI5⟩, le_trans hcd3 (le_trans hcd1 hcd), hps5', hnul5, hmS5, Or.inr ⟨rfl,
        htr _ (rd_fin_pp_err hg hcan hmem hnrm hcy' hsc2 hz4 hpm)⟩, hW5⟩


end

end

end Fl4Proofs.P3
