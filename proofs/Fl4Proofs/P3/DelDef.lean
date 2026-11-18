/-
P3 (DESIGN.md §9), CSpace: **FL4's `finalise_slot_deferred` refines l4v's
`finalise_slot slot False`** (`rec_del (FinaliseSlotCall slot False)`): each
round finalises the cap; a zombie that is not removable and not cyclic is
swapped into its first slot (`reduce_zombie slot False`), then the
preemption point. The fuel never runs out: each such round takes a slot out
of `mzS` (`psiD` decreases).
-/
import Fl4Proofs.P3.DelFinStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Removable and cyclic zombies -/

section
variable {th : TypedHeap}

theorem homeSl_eq_iff (hP : Placed th) {p zt n : U64} (hz : ZOK th p zt n) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot th sl) : homeSl p zt = sl ↔ p = cslotAddr sl := by
  constructor
  · intro h; rw [← h, home_addr]
  · intro h; exact cslotAddr_inj hP (home_abs hz) hA (by rw [home_addr]; exact h)

theorem removable_zombie (hP : Placed th) {p zt n : U64} (hz : ZOK th p zt n) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot th sl) :
    cdt.cap_removable (.Zombie p zt n) (cslotAddr sl) = ok (decide (n.val = 0 ∨ (n.val = 1 ∧ p = cslotAddr sl))) ∧
      (Fl4Spec.capRemoveable (absCap (.Zombie p zt n)) sl ↔ (n.val = 0 ∨ (n.val = 1 ∧ p = cslotAddr sl))) := by
  refine ⟨?_, ?_⟩
  · unfold cdt.cap_removable
    by_cases h0 : n = 0#u64
    · subst h0; simp
    · have h0' : n.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
      by_cases h1 : n = 1#u64
      · subst h1
        simp only [↓reduceIte, show ¬ (1#u64 : U64) = 0#u64 by decide]
        congr 1
        simp only [show (1#u64 : U64).val = 1 from rfl, Nat.one_ne_zero, false_or, true_and, decide_eq_decide]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      · have h1' : n.val ≠ 1 := fun e => h1 (UScalar.eq_of_val_eq e)
        simp [h0, h1, h0', h1']
  · show (n.val = 0 ∨ (n.val = 1 ∧ homeSl p zt = sl)) ↔ _
    rw [homeSl_eq_iff hP hz hA]

theorem cyclic_zombie (hP : Placed th) {p zt n : U64} (hz : ZOK th p zt n) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot th sl) :
    cdt.cap_cyclic_zombie (.Zombie p zt n) (cslotAddr sl) = ok (decide (p = cslotAddr sl)) ∧
      (Fl4Spec.capCyclicZombie (absCap (.Zombie p zt n)) sl ↔ p = cslotAddr sl) := by
  refine ⟨rfl, ?_⟩
  show homeSl p zt = sl ↔ _
  exact homeSl_eq_iff hP hz hA

theorem DelInv.of_same {mem mem' : U64 → U64} (hD : DelInv th mem) (hS : SlotsSame th mem mem') :
    DelInv th mem' := by
  refine ⟨fun y hy p zt n h => ?_, fun y y' hy hy' hyy p zt n p' zt' n' h h' => ?_, fun y hy h => ?_⟩
  · rw [hS.capV hy] at h; exact hD.zwf y hy p zt n h
  · rw [hS.capV hy] at h; rw [hS.capV hy'] at h'; exact hD.zu y y' hy hy' hyy p zt n p' zt' n' h h'
  · rw [hS.capV hy] at h; rw [hS.prevOf hy, hS.nextOf hy]; exact hD.nc y hy h

theorem psiD_same {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G)
    (hS : SlotsSame th mem mem') : psiD mem' G = psiD mem G := by
  apply le_antisymm
  · exact psiD_le hM hM' (fun y hy h => by rw [← hS.capV hy]; exact h)
      (fun y hy _ h => by unfold HomeZ at h ⊢; rw [hS.capV hy] at h; exact h)
  · exact psiD_le hM' hM (fun y hy h => by rw [hS.capV hy]; exact h)
      (fun y hy _ h => by unfold HomeZ at h ⊢; rw [← hS.capV hy] at h; exact h)

/-- Two slots' caps swapped. -/
theorem FinInv.swap {mem mem' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {p x : U64}
    (hFI : FinInv th mem σ G) (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' (renG G (Equiv.swap p x)))
    (hK : KSub σ σ') (hpx : p ≠ x)
    (hcap : ∀ y, IsSlot th y → capV mem' y =
      if y = x then capV mem p else if y = p then capV mem x else capV mem y) :
    FinInv th mem' σ' (renG G (Equiv.swap p x)) := by
  refine ⟨hFI.kt.sub hK, hFI.fm.rename _ hM'.tree.nodup (fun a ha => ?_)⟩
  have has := ((hM.members a).1 ha).1
  have hea : Equiv.swap p x a ∈ (renG G (Equiv.swap p x)).chains.flatten := by
    rw [mem_renG]; simpa using ha
  have hes := ((hM'.members _).1 hea).1
  have e : capV mem' (Equiv.swap p x a) = capV mem a := by
    rw [hcap _ hes]
    by_cases h1 : a = x
    · subst h1; rw [Equiv.swap_apply_right, if_neg hpx, if_pos rfl]
    · by_cases h2 : a = p
      · subst h2; rw [Equiv.swap_apply_left, if_pos rfl]
      · rw [Equiv.swap_apply_of_ne_of_ne h2 h1, if_neg h1, if_neg h2]
  rw [e]; exact CapSim.refl _

theorem pp_ksub {σ σ' : Fl4Spec.State Unit} {P Q : Prop}
    (h : (P ∧ (.ok (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1) ∨
      (Q ∧ (.error (), σ') ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ).1)) : KSub σ σ' := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact preemptionPoint_nks σ _ h
  · exact preemptionPoint_nks σ _ h

theorem chgOK_of_fin {mem mem' : U64 → U64} {y : U64}
    (h : capV mem' y = capV mem y ∨ (capV mem' y = .Null ∧ isZb (capV mem y) = false)) : ChgOK mem mem' y := by
  rcases h with h | ⟨h, hz⟩
  · exact Or.inl h
  · refine Or.inr ⟨Or.inl h, fun ⟨zt, n, e⟩ => ?_⟩
    rw [e] at hz; cases hz

/-- The measure after a finalisation. -/
theorem psiD_fin {mem mem' : U64 → U64} {G G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    {x : U64} (hx : capV mem' x = capV mem x)
    (hch : ∀ y, IsSlot th y → y ≠ x → capV mem' y = capV mem y ∨ (capV mem' y = .Null ∧ isZb (capV mem y) = false)) :
    psiD mem' G' ≤ psiD mem G ∧ (nnS G').card ≤ (nnS G).card := by
  have hnn : ∀ y, IsSlot th y → capV mem' y ≠ .Null → capV mem y ≠ .Null := by
    intro y hy h
    by_cases hyx : y = x
    · rw [hyx, ← hx]; rw [hyx] at h; exact h
    · rcases hch y hy hyx with e | ⟨e, -⟩
      · rw [← e]; exact h
      · exact absurd e h
  have hmz : ∀ y, IsSlot th y → capV mem' y ≠ .Null → ¬ HomeZ mem' y → ¬ HomeZ mem y := by
    intro y hy h hh hz
    apply hh
    by_cases hyx : y = x
    · subst hyx; unfold HomeZ at hz ⊢; rw [hx]; exact hz
    · rcases hch y hy hyx with e | ⟨e, -⟩
      · unfold HomeZ at hz ⊢; rw [e]; exact hz
      · exact absurd e h
  refine ⟨psiD_le hM hM' hnn hmz, Finset.card_le_card fun y hy => ?_⟩
  rw [mem_nnS hM'] at hy; rw [mem_nnS hM]; exact ⟨hy.1, hnn y hy.1 hy.2⟩

end

/-! ## Changes come with a smaller measure -/

section
variable {th : TypedHeap}

/-- Every slot whose cap changed (other than `x`, or `x` too if it held a
zombie) comes with a strictly smaller measure. -/
def StrictChg (th : TypedHeap) (mem0 mem : U64 → U64) (G0 G : MdbGhost) (x : U64) : Prop :=
  ∀ y, IsSlot th y → capV mem y ≠ capV mem0 y → (y ≠ x ∨ isZb (capV mem0 x) = true) →
    psiD mem G < psiD mem0 G0

theorem StrictChg.refl (mem : U64 → U64) (G : MdbGhost) (x : U64) : StrictChg th mem mem G G x :=
  fun _ _ h => absurd rfl h

theorem StrictChg.trans {m0 m1 m2 : U64 → U64} {G0 G1 G2 : MdbGhost} {x : U64}
    (h1 : StrictChg th m0 m1 G0 G1 x) (h2 : StrictChg th m1 m2 G1 G2 x)
    (hl1 : psiD m1 G1 ≤ psiD m0 G0) (hl2 : psiD m2 G2 ≤ psiD m1 G1) : StrictChg th m0 m2 G0 G2 x := by
  intro y hy hne hc
  by_cases e : capV m1 y = capV m0 y
  · have hne' : capV m2 y ≠ capV m1 y := by rw [e]; exact hne
    have hc' : y ≠ x ∨ isZb (capV m1 x) = true := by
      rcases hc with h | h
      · exact Or.inl h
      · by_cases hyx : y = x
        · subst hyx; rw [e]; exact Or.inr h
        · exact Or.inl hyx
    have := h2 y hy hne' hc'
    omega
  · have := h1 y hy e hc
    omega

theorem StrictChg.of_lt {m0 m1 : U64 → U64} {G0 G1 : MdbGhost} {x : U64} (h : psiD m1 G1 < psiD m0 G0) :
    StrictChg th m0 m1 G0 G1 x := fun _ _ _ _ => h

/-- After a finalisation that only empties other slots. -/
theorem StrictChg.fin {m0 m1 : U64 → U64} {G0 G1 : MdbGhost} (hM : MdbLinks th m0 G0) (hM1 : MdbLinks th m1 G1)
    {x : U64} (hx : capV m1 x = capV m0 x)
    (hch : ∀ y, IsSlot th y → y ≠ x → capV m1 y = capV m0 y ∨ (capV m1 y = .Null ∧ isZb (capV m0 y) = false)) :
    StrictChg th m0 m1 G0 G1 x := by
  intro y hy hne _
  have hyx : y ≠ x := fun e => hne (by rw [e, hx])
  rcases hch y hy hyx with e | ⟨e, -⟩
  · exact absurd e hne
  · have hnn : ∀ z, IsSlot th z → capV m1 z ≠ .Null → capV m0 z ≠ .Null := by
      intro z hz h
      by_cases hzx : z = x
      · rw [hzx, ← hx]; rw [hzx] at h; exact h
      · rcases hch z hz hzx with e' | ⟨e', -⟩
        · rw [← e']; exact h
        · exact absurd e' h
    have hmz : ∀ z, IsSlot th z → capV m1 z ≠ .Null → ¬ HomeZ m1 z → ¬ HomeZ m0 z := by
      intro z hz h hh hz0
      apply hh
      by_cases hzx : z = x
      · subst hzx; unfold HomeZ at hz0 ⊢; rw [hx]; exact hz0
      · rcases hch z hz hzx with e' | ⟨e', -⟩
        · unfold HomeZ at hz0 ⊢; rw [e']; exact hz0
        · exact absurd e' h
    refine psiD_lt_nn hM hM1 hnn hmz (z := y) ((mem_nnS hM y).2 ⟨hy, fun h => hne (by rw [e, h])⟩) ?_
    rw [mem_nnS hM1]; rintro ⟨-, h⟩; exact h e

end

/-! ## The deferred loop -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The deferred loop's invariant, from `s0`/`σ0`/`G0`. -/
def DefInv (W : S → A → Fl4Spec.State Unit → MdbGhost → Prop) (th : TypedHeap) (sl : Fl4Spec.CslotPtr) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (x : S × A × U64) : Prop :=
  ∃ σ G, DState (L := L) th x.1 σ G ∧ psiD (L.mem x.1) G < x.2.2.val ∧ (nnS G).card ≤ (nnS G0).card ∧
    psiD (L.mem x.1) G ≤ psiD (L.mem s0) G0 ∧
    (∀ y, RD (.finaliseSlotCall sl false) σ y → RD (.finaliseSlotCall sl false) σ0 y) ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem x.1) y) ∧
    StrictChg th (L.mem s0) (L.mem x.1) G0 G (cslotAddr sl) ∧ MdbStep (L.mem s0) G0 (L.mem x.1) G ∧
    W x.1 x.2.1 σ G

/-- What `finalise_slot_deferred` ends with. -/
def DefPost (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (sl : Fl4Spec.CslotPtr) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (res : core.result.Result cdt.Finalised error.Exc × S × A) : Prop :=
  ∃ σ' G', DState (L := L) th res.2.1 σ' G' ∧ (nnS G').card ≤ (nnS G0).card ∧
    psiD (L.mem res.2.1) G' ≤ psiD (L.mem s0) G0 ∧
    (∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem res.2.1) y) ∧
    StrictChg th (L.mem s0) (L.mem res.2.1) G0 G' (cslotAddr sl) ∧ MdbStep (L.mem s0) G0 (L.mem res.2.1) G' ∧
    ((∃ f, res.1 = .Ok f ∧ CleanCap f.cleanup ∧ CapWf f.cleanup ∧
        (f.success = false → HomeZ (L.mem res.2.1) (cslotAddr sl)) ∧
        (f.success = true → capV (L.mem res.2.1) (cslotAddr sl) ≠ .Null →
          Rd res.2.1 res.2.2 σ' G' (cslotAddr sl)) ∧
        RD (.finaliseSlotCall sl false) σ0
          (.ok (f.success, if f.success then absCap f.cleanup else .nullCap), σ')) ∨
      (res.1 = .Err .Preempted ∧ RD (.finaliseSlotCall sl false) σ0 (.error (), σ'))) ∧
    WPost W Wp res.1 res.2.1 res.2.2 σ' G'

/-- **FL4's deferred finalisation loop refines `finalise_slot slot False`.** -/
theorem deferred_loop [Fl4Proofs.P1.PlainStore st] (W Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop)
    (Rd : S → A → Fl4Spec.State Unit → MdbGhost → U64 → Prop) (th : TypedHeap) (hP : Placed th)
    (hF : FinalHyp (L := L) th) (hH : DelHypsWR (L := L) arI W Wp Rd th)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s0 : S) (σ0 : Fl4Spec.State Unit) (G0 : MdbGhost)
    (s : S) (a : A) (fuel : U64) (hinv : DefInv (L := L) W th sl s0 σ0 G0 (s, a, fuel)) :
    cdt.finalise_slot_deferred_loop st arI s a (cslotAddr sl) fuel ⦃ res =>
      DefPost (L := L) W Wp Rd th sl s0 σ0 G0 res ⦄ := by
  unfold cdt.finalise_slot_deferred_loop
  refine loop.spec_decr_nat (fun x => x.2.2.val) (DefInv (L := L) W th sl s0 σ0 G0) _ _ _ ?_ hinv
  rintro ⟨s, a, fuel⟩ ⟨σ, G, hDS, hlt, hcd, hps, htr, hch, hsc, hmS, hW⟩
  simp only at hlt hcd hps htr hch hsc hmS hW ⊢
  unfold cdt.finalise_slot_deferred_loop.body
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
    refine ⟨σ, G, ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩, hcd, hps, hch, hsc, hmS, Or.inl ⟨_, rfl, trivial, trivial,
      fun h => by simp at h, fun _ h => absurd (capV_of_capAt hc) h, htr _ (rd_fin_null hg)⟩, hW⟩
  rw [cap_is_null_ne hcn]; simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf1, hbf2, -⟩ := hF s σ G sl c ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hA hc hcn
  rw [is_final_with_cap_eq _ _ _ hc, hbf1]; simp only [bind_ok]
  rw [hca.abs] at hg
  have hcan : absCap c ≠ .nullCap := fun h => hcn (absCap_eq_null.1 h)
  apply WP.spec_bind (fin_step arI W Rd th hH.fin hH.triv hF hP s a σ G ⟨⟨hR, hV, hM, hC, hI⟩, hD, hFI⟩ hW hA hc hcn
    bf hbf2)
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨σ1, G1, hmem, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, hx1, hch1, hcl, hclw, hzr, hrem,
    hfs1, hW1, hRd1⟩
  simp only [uncurry_apply_pair] at hmem hx1 hch1 hcl hclw hzr hrem hfs1 hW1 ⊢
  dsimp only at hR1 hV1 hM1 hC1 hI1 hD1 hmem hx1 hch1 hcl hclw hzr hrem hfs1 hW1 ⊢
  have hmS1 := hmS.trans hfs1
  obtain ⟨hps1, hcd1⟩ := psiD_fin hM hM1 (by rw [hx1, capV_of_capAt hc]) hch1
  have hsc1 : StrictChg th (L.mem s0) (L.mem s1) G0 G1 (cslotAddr sl) :=
    hsc.trans (StrictChg.fin hM hM1 (by rw [hx1, capV_of_capAt hc]) hch1) hps hps1
  have hch1' : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem s1) y :=
    fun y hy hyx => (hch y hy hyx).trans (chgOK_of_fin (hch1 y hy hyx))
  rcases hrem with rfl | ⟨p, zt, n, rfl, hz⟩
  · -- nothing remains: done
    simp only [cdt.cap_removable, bind_ok, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, by dsimp only at *; omega, by dsimp only at *; omega, hch1', hsc1, hmS1, Or.inl ⟨_, rfl, hcl, hclw,
      fun h => by simp at h, fun _ _ => hRd1, htr _ (rd_fin_removable hg hcan hmem trivial)⟩, hW1⟩
  -- a zombie remains
  obtain ⟨hrm, hrmS⟩ := removable_zombie hP hz.zok hA
  rw [hrm]; simp only [bind_ok]
  by_cases hrmv : n.val = 0 ∨ (n.val = 1 ∧ p = cslotAddr sl)
  · simp only [hrmv, decide_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ1, G1, ⟨⟨hR1, hV1, hM1, hC1, hI1⟩, hD1, hFI1⟩, by dsimp only at *; omega, by dsimp only at *; omega, hch1', hsc1, hmS1, Or.inl ⟨_, rfl, hcl, hclw,
      fun h => by simp at h, fun _ _ => hRd1, htr _ (rd_fin_removable hg hcan hmem (hrmS.2 hrmv))⟩, hW1⟩
  simp only [hrmv, decide_false, Bool.false_eq_true, ↓reduceIte]
  have hxn1 : capV (L.mem s1) (cslotAddr sl) ≠ .Null := by rw [hx1]; exact hcn
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
  have hsc2' : StrictChg th (L.mem s0) (L.mem s2) G0 G1 (cslotAddr sl) := by
    refine hsc1.trans (fun y hy hne hcnd => ?_) (le_trans hps1 hps) hps2
    by_cases hyx : y = cslotAddr sl
    · subst hyx
      rcases hcnd with h | h
      · exact absurd rfl h
      · rw [hx1] at h
        rw [hx2, hx1, hzr h] at hne; exact absurd rfl hne
    · exact absurd (hoth2 y hy hyx) hne
  have hch2 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem s2) y :=
    fun y hy hyx => (hch1' y hy hyx).trans (Or.inl (hoth2 y hy hyx))
  obtain ⟨hcy, hcyS⟩ := cyclic_zombie hP hz.zok hA
  rw [hcy]; simp only [bind_ok]
  have hnrm : ¬ Fl4Spec.capRemoveable (absCap (.Zombie p zt n)) sl := fun h => hrmv (hrmS.1 h)
  by_cases hpx : p = cslotAddr sl
  · -- cyclic: stop
    simp only [hpx, decide_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ2, G1, ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hD2, hFI2⟩, by dsimp only at *; omega, by dsimp only at *; omega, hch2, hsc2', hmS2, Or.inl ⟨_, rfl, hcl, hclw,
      fun _ => ⟨zt, n, by rw [hx2, hpx]⟩, fun h => by simp at h, htr _ (rd_fin_cyclic hg hcan hmem hnrm (hcyS.2 hpx) hsc2)⟩, hW2⟩
  simp only [hpx, decide_false, Bool.false_eq_true, ↓reduceIte]
  -- swap the zombie into its first slot
  have hx2a : capAt (L.mem s2) (cslotAddr sl) = ok (.Zombie p zt n) := by rw [capAt_capV, hx2]
  have hpsl : IsSlot th p := by have h := (home_abs hz.zok).isSlot; rwa [home_addr] at h
  apply WP.spec_bind (WP.spec_and (swap_home th s2 σ2 G1 hR2 hV2 hP hM2 hC2 hI2 hD2 hA hx2a hpx)
    (swap_for_delete_frame hP s2 hM2 hD2 hpsl hxs))
  rintro s3 ⟨⟨σ3, G3, hsw3, ⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hps3, hcd3, hch3, -, -, hG3, hcap3, hst3⟩, hF3⟩
  have hmS3 := hmS2.trans hst3
  have hFI3 : FinInv th (L.mem s3) σ3 G3 := by
    subst hG3; exact hFI2.swap hM2 hM3 (ksub_of_eq (capSwapForDelete_nks _ _) hsw3) hpx hcap3
  have hW3 : W s3 a1 σ3 G3 := hH.swap s2 s3 a1 σ2 σ3 G1 G3 sl p zt n hW2 ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hD2, hFI2⟩
    ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩ hF3 hsw3 hA hx2 hpx hG3 hcap3 hst3
  have hsc3 : StrictChg th (L.mem s0) (L.mem s3) G0 G3 (cslotAddr sl) :=
    hsc2'.trans (StrictChg.of_lt hps3) (le_trans hps2 (le_trans hps1 hps)) hps3.le
  have hch3' : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem s3) y :=
    fun y hy hyx => (hch2 y hy hyx).trans (hch3 y hy hyx)
  obtain ⟨v, hrz⟩ := rd_reduce_false (ptr := p.bv) (bits := zombieBits zt) (n := n.val - 1) (sl := sl)
    (σ := σ2) (σ' := σ3) (by
      rw [show n.val - 1 + 1 = n.val by dsimp only at *; omega]
      intro h; exact hpx ((homeSl_eq_iff hP hz.zok hA).1 h))
    (by rw [show n.val - 1 + 1 = n.val by dsimp only at *; omega]; exact mem_single hsw3)
  rw [show n.val - 1 + 1 = n.val by dsimp only at *; omega] at hrz
  have hcy' : ¬ (Fl4Spec.capCyclicZombie (absCap (.Zombie p zt n)) sl ∧ false = false) :=
    fun h => hpx (hcyS.1 h.1)
  apply WP.spec_bind (hH.pp s3 a1 σ3 G3 ⟨⟨hR3, hV3, hM3, hC3, hI3⟩, hD3, hFI3⟩ hW3)
  rintro ⟨r4, s4, a4⟩ ⟨hS4, σ4, hcase, hCR4, hW4⟩
  simp only at hS4 hcase hCR4 hW4 ⊢
  have hD4 := hD3.of_same hS4
  have hmS4 := hmS3.same_right hM3 hS4
  have hFI4 := hFI3.of_same hM3 hS4 (pp_ksub hcase)
  have hps4 := psiD_same hM3 hCR4.2.2.1 hS4
  have hch4 : ∀ y, IsSlot th y → y ≠ cslotAddr sl → ChgOK (L.mem s0) (L.mem s4) y :=
    fun y hy hyx => (hch3' y hy hyx).trans (Or.inl (hS4.capV hy))
  have hsc4 : StrictChg th (L.mem s0) (L.mem s4) G0 G3 (cslotAddr sl) :=
    hsc3.trans (fun y hy hne _ => absurd (hS4.capV hy) hne) (le_trans hps3.le (le_trans hps2 (le_trans hps1 hps)))
      (by rw [hps4])
  rcases hcase with ⟨rfl, hpm⟩ | ⟨rfl, hpm⟩
  · simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
    refine ⟨⟨σ4, G3, ⟨hCR4, hD4, hFI4⟩, by dsimp only at *; omega, by dsimp only at *; omega, by dsimp only at *; omega, fun y hy => ?_, hch4, hsc4, hmS4, hW4⟩, by dsimp only at *; omega⟩
    exact htr _ (rd_fin_reduce hg hcan hmem hnrm hcy' hsc2 hrz hpm hy)
  · simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σ4, G3, ⟨hCR4, hD4, hFI4⟩, by dsimp only at *; omega, by dsimp only at *; omega, hch4, hsc4, hmS4, Or.inr ⟨rfl,
      htr _ (rd_fin_pp_err hg hcan hmem hnrm hcy' hsc2 hrz hpm)⟩, hW4⟩

end

end

end Fl4Proofs.P3
