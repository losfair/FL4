/-
P3 (DESIGN.md §9), VSpace: **Frame `TestAndClearAccessed`** (l4h 0023/0029)
against the Fl4Spec/Ext/VSpace model.

* `frameMappingSlot` outcomes (`fms_*`) and FL4's `mapped_entry` against
  them (`mapped_entry_small`, `mapped_entry_large`);
* clearing the accessed bit (bit 5) keeps the entry relations
  (`PTERel_clr5`, `PDERel_clr5`);
* `tac_rel`, `frame_tac_rel`: the decode's errors are the model's, else FL4
  clears the bit and replies with whether it was set, one of the model's
  answers (`TacSpec`).
-/
import Fl4Proofs.P3.VsExt
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3
noncomputable section
open Fl4Spec

theorem fms_noVs {p : ObjRef} {sz : VMPageSize} {asid : Asid} {v : VSpaceRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.error e, σ)}, False)) :
    ExceptT.run (frameMappingSlot (Z := Unit) p sz asid v) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold frameMappingSlot
  exact runE_bind_err (by rw [runE_handle_err hf]; rfl)

theorem fms_s_noSlot {p vs : ObjRef} {asid : Asid} {v : VSpaceRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    ExceptT.run (frameMappingSlot (Z := Unit) p .x64SmallPage asid v) σ =
      ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold frameMappingSlot
  rw [runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_handle_err hl]; rfl)

theorem fms_s_entry {p vs slot : ObjRef} {asid : Asid} {v : VSpaceRef} {σ : State Unit} {x : PTE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPte (Z := Unit) slot σ = ({(x, σ)}, False)) :
    ExceptT.run (frameMappingSlot (Z := Unit) p .x64SmallPage asid v) σ =
      if checkMappingPptr p (.vmPTE x) = true then ({(.ok slot, σ)}, False)
      else ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold frameMappingSlot
  rw [runE_bind_ok (runE_handle_ok hf)]
  dsimp only
  rw [runE_bind_ok (runE_handle_ok hl), runE_bind_ok (runE_liftE hg)]
  split
  · rename_i h; rw [runE_bind_ok (runE_unlessE_true h _ σ)]; rfl
  · rename_i h; exact runE_bind_err (by rw [runE_unlessE_false h]; rfl)

theorem fms_l_noSlot {p vs : ObjRef} {asid : Asid} {v : VSpaceRef} {σ : State Unit} {e : LookupFailure}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    ExceptT.run (frameMappingSlot (Z := Unit) p .x64LargePage asid v) σ =
      ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold frameMappingSlot
  rw [runE_bind_ok (runE_handle_ok hf)]
  exact runE_bind_err (by rw [runE_handle_err hl]; rfl)

theorem fms_l_entry {p vs slot : ObjRef} {asid : Asid} {v : VSpaceRef} {σ : State Unit} {x : PDE}
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid) σ = ({(.ok vs, σ)}, False))
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) :
    ExceptT.run (frameMappingSlot (Z := Unit) p .x64LargePage asid v) σ =
      if checkMappingPptr p (.vmPDE x) = true then ({(.ok slot, σ)}, False)
      else ({(.error (.invalidCapability 0), σ)}, False) := by
  unfold frameMappingSlot
  rw [runE_bind_ok (runE_handle_ok hf)]
  dsimp only
  rw [runE_bind_ok (runE_handle_ok hl), runE_bind_ok (runE_liftE hg)]
  split
  · rename_i h; rw [runE_bind_ok (runE_unlessE_true h _ σ)]; rfl
  · rename_i h; exact runE_bind_err (by rw [runE_unlessE_false h]; rfl)

theorem bit5_off (k : Nat) (hk : k ≠ 5) : (~~~32#64 : BitVec 64).getLsbD k = decide (k < 64) := by
  rw [BitVec.getLsbD_not, show (32#64 : BitVec 64) = BitVec.twoPow 64 5 by decide, BitVec.getLsbD_twoPow]
  by_cases h : k < 64 <;> simp [h, Ne.symm hk]

theorem clr5 (w c : U64) (hc : c.bv.getLsbD 5 = false) : (w &&& ~~~32#u64) &&& c = w &&& c := by
  apply eq_of_bv
  show UScalar.bv ((w &&& ~~~32#u64) &&& c) = UScalar.bv (w &&& c)
  have h1 : ((w &&& ~~~32#u64) &&& c).bv = (w.bv &&& ~~~32#64) &&& c.bv := rfl
  have h2 : (w &&& c).bv = w.bv &&& c.bv := rfl
  rw [h1, h2]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_and]
  by_cases e : k = 5
  · subst e; rw [hc]; simp
  · rw [bit5_off k e]; simp [hk]

theorem bitL_clr5 (w : U64) {k : Nat} (hk : k ≠ 5) (hk' : k < 64) : bitL (w &&& ~~~32#u64) k = bitL w k := by
  unfold bitL
  show (w.bv &&& ~~~32#64).getLsbD k = _
  rw [BitVec.getLsbD_and, bit5_off k hk]; simp [hk']

theorem eP_clr5 (w : U64) : eP (w &&& ~~~32#u64) ↔ eP w := by
  unfold eP; rw [clr5 w 1#u64 (by decide)]
theorem eS_clr5 (w : U64) : eS (w &&& ~~~32#u64) ↔ eS w := by
  unfold eS; rw [clr5 w 128#u64 (by decide)]
theorem eA_clr5 (w : U64) : eA (w &&& ~~~32#u64) = eA w := by
  unfold eA; rw [clr5 w _ (by decide)]
theorem lA_clr5 (w : U64) : lA (w &&& ~~~32#u64) = lA w := by
  unfold lA; rw [clr5 w _ (by decide)]

theorem PTERel_clr5 {w : U64} {x : PTE} (h : PTERel w x) : PTERel (w &&& ~~~32#u64) x := by
  cases x with
  | invalidPTE => show ¬ eP _; rw [eP_clr5]; exact h
  | smallPagePTE f a r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨(eP_clr5 w).2 h1, by rw [eA_clr5]; exact h2, ?_, ?_⟩
    · unfold PteRights at *; rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]; exact h3
    · unfold PteAttrs at *
      rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]
      exact h4

theorem PDERel_clr5 {L1 : Set U64} {w : U64} {x : PDE} (h : PDERel L1 w x) : PDERel L1 (w &&& ~~~32#u64) x := by
  cases x with
  | invalidPDE => show ¬ eP _; rw [eP_clr5]; exact h
  | pageTablePDE t a r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨(eP_clr5 w).2 h1, by rw [eS_clr5]; exact h2, by rw [eA_clr5]; exact h3, ?_⟩
    unfold eT; rw [eA_clr5]; exact h4
  | largePagePDE f a r =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨(eP_clr5 w).2 h1, (eS_clr5 w).2 h2, by rw [lA_clr5]; exact h3, ?_, ?_⟩
    · unfold PteRights at *; rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]; exact h4
    · unfold PteAttrsL at *
      rw [bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide), bitL_clr5 w (by decide) (by decide)]
      exact h5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem mapped_entry_small [PlainStore st] {L4 L3 L2 L1 : Set U64} (s : S) (σ : State Unit)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPP : PtPlaced L4 L3 L2 L1) {r1 : U64} (hr1 : r1 ∈ L4)
    (ptr rt asid vaddr : U64) (dev mp : Bool)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok r1.bv, σ)}, False)) :
    vspace.mapped_entry st s ⟨ptr, .Small, rt, dev, mp, false, asid, vaddr⟩ r1 ⦃ o =>
      (o = none ∧ ExceptT.run (frameMappingSlot (Z := Unit) ptr.bv .x64SmallPage asid.bv vaddr.bv) σ =
        ({(.error (.invalidCapability 0), σ)}, False)) ∨
      (∃ q ∈ L1, o = some (peA q (vIdx vaddr 12)) ∧
        ExceptT.run (frameMappingSlot (Z := Unit) ptr.bv .x64SmallPage asid.bv vaddr.bv) σ =
          ({(.ok (peA q (vIdx vaddr 12)).bv, σ)}, False)) ⦄ := by
  have hAM : vspace.ADDR_MASK = 4503599627366400#u64 := by unfold vspace.ADDR_MASK; rfl
  unfold vspace.mapped_entry
  simp only [layout.paddr, bind_ok, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (lookup_pt_slot_rel s σ hPt hPP hr1 vaddr) ?_
  rintro r2 ⟨hsp, hsl, hse⟩
  cases r2 with
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 (Or.inl ⟨rfl, fms_s_noSlot hf hsp⟩)
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    obtain ⟨f, hk, hf2⟩ := hPt.l1 q hq
    have hqa := hPP q (Or.inr (Or.inr (Or.inr hq)))
    have hj := vIdx_lt vaddr 12
    have hfe2 := hf2 _ hj
    have hg : getPte (Z := Unit) (peA q (vIdx vaddr 12)).bv σ = ({(f (ucast 9 (vIdx vaddr 12).bv), σ)}, False) := by
      rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPte_at hqa hk hj
    have he := fms_s_entry (p := ptr.bv) hf hsp hg
    dsimp only
    rw [L.read_eq]
    apply ok_bind_spec
    simp only [vspace.frame_base, frame_gpa_plain, bind_ok, hAM]
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    by_cases hp0 : (L.mem s (peA q (vIdx vaddr 12)) &&& 1#u64) = 0#u64
    · rw [if_pos hp0]
      refine (WP.spec_ok _).2 (Or.inl ⟨rfl, he.trans (if_neg ?_)⟩)
      revert hfe2
      cases f (ucast 9 (vIdx vaddr 12).bv) with
      | invalidPTE => intro; simp [checkMappingPptr]
      | smallPagePTE _ _ _ => intro h; exact absurd hp0 h.1
    rw [if_neg hp0]
    obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (ucast 9 (vIdx vaddr 12).bv) = .smallPagePTE fb fa fr := by
      revert hfe2
      cases f (ucast 9 (vIdx vaddr 12).bv) with
      | invalidPTE => intro h; exact absurd hp0 h
      | smallPagePTE a b c => intro; exact ⟨a, b, c, rfl⟩
    rw [hfx] at hfe2 he
    have hfb : (eA (L.mem s (peA q (vIdx vaddr 12)))).bv = fb := hfe2.2.1
    by_cases hadr : ((L.mem s (peA q (vIdx vaddr 12)) &&& 4503599627366400#u64) !=
        core.num.U64.wrapping_sub ptr layout.PPTR_BASE) = true
    · simp only [hadr, ↓reduceIte, Bool.false_eq_true]
      refine (WP.spec_ok _).2 (Or.inl ⟨rfl, he.trans (if_neg ?_)⟩)
      show ¬ decide (fb = addrFromPPtr ptr.bv) = true
      rw [decide_eq_true_iff, ← hfb, ← paddr_bv]
      exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
    · simp only [hadr, ↓reduceIte, Bool.false_eq_true]
      have hadrE : eA (L.mem s (peA q (vIdx vaddr 12))) = core.num.U64.wrapping_sub ptr layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      refine (WP.spec_ok _).2 (Or.inr ⟨q, hq, rfl, he.trans (if_pos ?_)⟩)
      show decide (fb = addrFromPPtr ptr.bv) = true
      rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]

theorem mapped_entry_large [PlainStore st] {L4 L3 L2 L1 : Set U64} (s : S) (σ : State Unit)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hPP : PtPlaced L4 L3 L2 L1) {r1 : U64} (hr1 : r1 ∈ L4)
    (ptr rt asid vaddr : U64) (dev mp : Bool)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok r1.bv, σ)}, False)) :
    vspace.mapped_entry st s ⟨ptr, .Large, rt, dev, mp, false, asid, vaddr⟩ r1 ⦃ o =>
      (o = none ∧ ExceptT.run (frameMappingSlot (Z := Unit) ptr.bv .x64LargePage asid.bv vaddr.bv) σ =
        ({(.error (.invalidCapability 0), σ)}, False)) ∨
      (∃ q ∈ L2, o = some (peA q (vIdx vaddr 21)) ∧
        ExceptT.run (frameMappingSlot (Z := Unit) ptr.bv .x64LargePage asid.bv vaddr.bv) σ =
          ({(.ok (peA q (vIdx vaddr 21)).bv, σ)}, False)) ⦄ := by
  unfold vspace.mapped_entry
  simp only [layout.paddr, bind_ok, ↓reduceIte]
  refine WP.spec_bind (lookup_pd_slot_rel s σ hPt hPP hr1 vaddr) ?_
  rintro r2 ⟨hsp, hsl, hse⟩
  cases r2 with
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 (Or.inl ⟨rfl, fms_l_noSlot hf hsp⟩)
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    obtain ⟨f, hk, hf2⟩ := hPt.l2 q hq
    have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
    have hj := vIdx_lt vaddr 21
    have hfe2 := hf2 _ hj
    have hg : getPde (Z := Unit) (peA q (vIdx vaddr 21)).bv σ = ({(f (ucast 9 (vIdx vaddr 21).bv), σ)}, False) := by
      rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPde_at hqa hk hj
    have he := fms_l_entry (p := ptr.bv) hf hsp hg
    dsimp only
    rw [L.read_eq]
    apply ok_bind_spec
    simp only [vspace.frame_base, frame_gpa_plain, bind_ok]
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    by_cases hp0 : (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64
    · rw [if_pos hp0]
      refine (WP.spec_ok _).2 (Or.inl ⟨rfl, he.trans (if_neg ?_)⟩)
      revert hfe2
      cases f (ucast 9 (vIdx vaddr 21).bv) with
      | invalidPDE => intro; simp [checkMappingPptr]
      | pageTablePDE _ _ _ => intro h; exact absurd hp0 h.1
      | largePagePDE _ _ _ => intro h; exact absurd hp0 h.1
    rw [if_neg hp0]
    rw [P_PS_eq]
    apply ok_bind_spec
    apply ok_bind_spec
    by_cases hps : (L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) = 0#u64
    · rw [if_pos hps]
      refine (WP.spec_ok _).2 (Or.inl ⟨rfl, he.trans (if_neg ?_)⟩)
      revert hfe2
      cases f (ucast 9 (vIdx vaddr 21).bv) with
      | invalidPDE => intro; simp [checkMappingPptr]
      | pageTablePDE _ _ _ => intro; simp [checkMappingPptr]
      | largePagePDE _ _ _ => intro h; exact absurd hps h.2.1
    rw [if_neg hps]
    obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (ucast 9 (vIdx vaddr 21).bv) = .largePagePDE fb fa fr := by
      revert hfe2
      cases f (ucast 9 (vIdx vaddr 21).bv) with
      | invalidPDE => intro h; exact absurd hp0 h
      | pageTablePDE _ _ _ => intro h; exact absurd ((eS_iff _).1 (by simpa using hps)) h.2.1
      | largePagePDE a b c => intro; exact ⟨a, b, c, rfl⟩
    rw [hfx] at hfe2 he
    have hfb : (lA (L.mem s (peA q (vIdx vaddr 21)))).bv = fb := hfe2.2.2.1
    by_cases hadr : ((L.mem s (peA q (vIdx vaddr 21)) &&& 4503599625273344#u64) !=
        core.num.U64.wrapping_sub ptr layout.PPTR_BASE) = true
    · simp only [hadr, ↓reduceIte, Bool.false_eq_true]
      refine (WP.spec_ok _).2 (Or.inl ⟨rfl, he.trans (if_neg ?_)⟩)
      show ¬ decide (fb = addrFromPPtr ptr.bv) = true
      rw [decide_eq_true_iff, ← hfb, ← paddr_bv]
      exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
    · simp only [hadr, ↓reduceIte, Bool.false_eq_true]
      have hadrE : lA (L.mem s (peA q (vIdx vaddr 21))) = core.num.U64.wrapping_sub ptr layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      refine (WP.spec_ok _).2 (Or.inr ⟨q, hq, rfl, he.trans (if_pos ?_)⟩)
      show decide (fb = addrFromPPtr ptr.bv) = true
      rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]

end

theorem P_ACCESSED_eq : vspace.P_ACCESSED = ok 32#u64 := by
  unfold vspace.P_ACCESSED; rw [shl_eq _ _ (by decide) (by decide)]; rfl

theorem decodeTAC_huge (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) (ma : Option (Asid × VSpaceRef))
    (σ : State Unit) :
    ExceptT.run (decodeTestAndClearAccessed (Z := Unit) (.pageCap dev p R mt .x64HugePage ma)) σ =
      ({(.error .illegalOperation, σ)}, False) := by
  unfold decodeTestAndClearAccessed; dsimp only; rw [if_pos rfl]; rfl

theorem decodeTAC_unmapped (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) {sz : VMPageSize}
    (hsz : sz ≠ .x64HugePage) (σ : State Unit) :
    ExceptT.run (decodeTestAndClearAccessed (Z := Unit) (.pageCap dev p R mt sz none)) σ =
      ({(.error .illegalOperation, σ)}, False) := by
  unfold decodeTestAndClearAccessed; dsimp only; rw [if_neg hsz]; rfl

theorem decodeTAC_asid0 (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) {sz : VMPageSize}
    (hsz : sz ≠ .x64HugePage) (v : VSpaceRef) (σ : State Unit) :
    ExceptT.run (decodeTestAndClearAccessed (Z := Unit) (.pageCap dev p R mt sz (some (0, v)))) σ =
      ({(.error .illegalOperation, σ)}, False) := by
  unfold decodeTestAndClearAccessed; dsimp only; rw [if_neg hsz]
  exact runE_bind_err (by rw [runE_whenE_true rfl]; rfl)

theorem decodeTAC_mapped (dev : Bool) (p : ObjRef) (R : VMRights) (mt : VMMapType) {sz : VMPageSize}
    (hsz : sz ≠ .x64HugePage) {asid : Asid} (h0 : asid ≠ 0) (v : VSpaceRef) (σ : State Unit) :
    ExceptT.run (decodeTestAndClearAccessed (Z := Unit) (.pageCap dev p R mt sz (some (asid, v)))) σ =
      ExceptT.run (frameMappingSlot (Z := Unit) p sz asid v) σ := by
  unfold decodeTestAndClearAccessed; dsimp only; rw [if_neg hsz]
  exact runE_bind_ok (runE_whenE_false h0 _ σ)

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The hypotheses of `TestAndClearAccessed`: the replies, and `SR` stable
under the (abstractly invisible) accessed-bit writes of PT and PD entries. -/
structure VsTacHyps (A : Type) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  rep : VsReplyHyps st A th P L4 L3 L2 L1 SR
  stable1 : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PtW L1) → PtStep σ σ' → SR s' a σ'
  stable2 : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdW L2) → PdStep σ σ' → SR s' a σ'

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]


/-- The model's `TestAndClearAccessed` after the decode `D`: the slot, then
`Restart`, the answer and the reply, ending in a state with `Q`. -/
def TacSpec (D : Set (Except Fl4Spec.SyscallError Fl4Spec.ObjRef × Fl4Spec.State Unit) × Prop)
    (σ : Fl4Spec.State Unit) (call : Bool) (Q : Fl4Spec.State Unit → Prop) : Prop :=
  ∃ slot, D = ({(.ok slot, σ)}, False) ∧
    ∃ v σ1 σ', Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      ([v], σ1) ∈ (Fl4Spec.performTestAndClearAccessed (Z := Unit) slot σ1).1 ∧
      ¬ (replyRunning σ.curThread call [v] σ1).2 ∧
      ((), σ') ∈ (replyRunning σ.curThread call [v] σ1).1 ∧ Q σ'
/-- **Frame `TestAndClearAccessed` (l4h 0023/0029) refines the l4h model**:
FL4's decode against `decodeTestAndClearAccessed`; on success FL4 clears the
entry's accessed bit (invisible to the relation and to the model) and
replies with whether it was set, one of the model's answers. FL4 does not
set `Restart` first; `VsReplyHyps.replyR` matches its reply with l4v's
`Restart` and reply. -/
theorem tac_rel [Fl4Proofs.P1.PlainStore st] {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsTacHyps st A th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hU : UR st th P L4 L3 L2 L1 SR s a σ) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hVP : VsPlaced P (L.ksb s))
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (f : vspace.FrameCap) (call : Bool) :
    vspace.decode_test_and_clear_accessed st s f call ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ = ({(.error e', σ)}, False) ∧
        res.2 = s) ∨
      (res.1 = .Ok () ∧
        TacSpec (ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ) σ call
          (UR st th P L4 L3 L2 L1 SR res.2 a)) ⦄ := by
  obtain ⟨hS, hSt, hSV, hR, hPt⟩ := hU
  have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  generalize hD : ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit)
    (frameACapG ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩)) σ = D
  unfold vspace.decode_test_and_clear_accessed
  cases sz with
  | Huge =>
    refine WP.spec_bind (Pₘ := fun p => p = (.Huge, true)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if true = true then _ else _) ⦃ _ ⦄
    simp only [↓reduceIte, error.illegal, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, Or.inl (show SysErrRel (.Sys .IllegalOperation)
      .illegalOperation from trivial), hD ▸ decodeTAC_huge _ _ _ _ _ σ, rfl⟩)
  | Small => 
    refine WP.spec_bind (Pₘ := fun p => p = (.Small, false)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if false = true then _ else _) ⦃ _ ⦄
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    cases mp
    · simp only [Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial), hD ▸ decodeTAC_unmapped _ _ _ _ (by simp [frameSizeOf]) σ, rfl⟩)
    simp only [↓reduceIte]
    by_cases h0 : fa = 0#u64
    · subst h0
      simp only [↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial), hD ▸ decodeTAC_asid0 _ _ _ _ (by simp [frameSizeOf]) _ σ, rfl⟩)
    simp only [h0, ↓reduceIte]
    have h0' : fa.bv ≠ 0 := fun h => h0 (eq_of_bv h)
    have hdec := hD.symm.trans (decodeTAC_mapped dev ptr.bv (vmRightsOf rt) .vmVSpaceMap (sz := .x64SmallPage) (by decide) h0' fv.bv σ)
    refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR fa h0)
      (find_vspace_for_asid_L4 s σ hR hPI fa)) ?_
    rintro r ⟨hf, hL⟩
    cases r with
    | Err lf =>
      simp only [error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩,
        hdec.trans (fms_noVs hf), rfl⟩)
    | Ok r1 =>
      have hr1 := hL r1 rfl
      dsimp only
      refine WP.spec_bind (mapped_entry_small s σ hPt hPP hr1 ptr rt fa fv dev true hf) ?_
      rintro o hme
      rcases hme with ⟨rfl, hfms⟩ | ⟨q, hq, rfl, hfms⟩
      · simp only [error.invalid_cap, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩,
          hdec.trans hfms, rfl⟩)
      dsimp only
      rw [hct]
      apply ok_bind_spec
      rw [L.read_eq]
      apply ok_bind_spec
      rw [P_ACCESSED_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      apply ok_bind_spec
      rw [L.write_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      obtain ⟨f, hk, hf2⟩ := hPt.l1 q hq
      have hqa := hPP q (Or.inr (Or.inr (Or.inr hq)))
      have hj := vIdx_lt fv 12
      have hea : Aligned (peA q (vIdx fv 12)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx fv 12)) (L.mem s (peA q (vIdx fv 12)) &&& ~~~32#u64) with hs1
      have hPt1 : PtRel L4 L3 L2 L1 (L.mem s1) σ := by
        have := hPt.upd_l1 hPP hq hk hj _ _ (PTERel_clr5 (hf2 _ hj))
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
        rwa [Function.update_eq_self, updK_self hk] at this
      have hW : WritesIn st s s1 (PtW L1) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hS1 : SR s1 a σ := by
        have := hH.stable1 _ _ a σ _ hS hW ⟨q.bv, f, f, hk, rfl⟩
        rwa [updK_self hk] at this
      have hWA : ∀ b, PtW L1 b → PtWAll L4 L3 L2 L1 b := by
        rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
      have hU1 : UR st th P L4 L3 L2 L1 SR s1 a σ := by
        refine ⟨hS1, StateRel.of_caps hSt hcap, Vs.SlotsValid.of_caps hSV hcap, ?_, hPt1⟩
        rw [hW.1]
        exact hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun _ _ => rfl)
      have hst1 := Notif.setThreadState_eq (σ := σ) .restart hkt'
      have hfin : ∀ v : U64, v = 1#u64 ∨ v = 0#u64 → vspace.reply1 st s1 ct call v ⦃ s2 =>
          TacSpec D σ call (UR st th P L4 L3 L2 L1 SR s2 a) ⦄ := by
        intro v hv
        refine WP.spec_mono (hH.rep.replyR s1 a σ ct call v hU1 hcur) ?_
        rintro s2 ⟨hnf, σ', hm, hU2⟩
        rw [nd_bind_one hst1] at hnf hm
        rw [hcur] at hnf hm
        refine ⟨_, hdec.trans hfms, v.bv, _, σ', by rw [← hcur]; exact hst1, ?_, hnf, hm, hU2⟩
        simp only [Fl4Spec.performTestAndClearAccessed, Fl4Spec.NonDet.select, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, and_true]
        rcases hv with rfl | rfl
        · right; rfl
        · left; rfl
      split
      · refine WP.spec_bind (hfin 1#u64 (Or.inl rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 (Or.inr ⟨rfl, h⟩)
      · refine WP.spec_bind (hfin 0#u64 (Or.inr rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 (Or.inr ⟨rfl, h⟩)
  | Large => 
    refine WP.spec_bind (Pₘ := fun p => p = (.Large, false)) (by simp) ?_
    rintro ⟨fs, b⟩ hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    show (if false = true then _ else _) ⦃ _ ⦄
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    cases mp
    · simp only [Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial), hD ▸ decodeTAC_unmapped _ _ _ _ (by simp [frameSizeOf]) σ, rfl⟩)
    simp only [↓reduceIte]
    by_cases h0 : fa = 0#u64
    · subst h0
      simp only [↓reduceIte, error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .illegalOperation, rfl, Or.inl (show SysErrRel (.Sys .IllegalOperation)
        .illegalOperation from trivial), hD ▸ decodeTAC_asid0 _ _ _ _ (by simp [frameSizeOf]) _ σ, rfl⟩)
    simp only [h0, ↓reduceIte]
    have h0' : fa.bv ≠ 0 := fun h => h0 (eq_of_bv h)
    have hdec := hD.symm.trans (decodeTAC_mapped dev ptr.bv (vmRightsOf rt) .vmVSpaceMap (sz := .x64LargePage) (by decide) h0' fv.bv σ)
    refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR fa h0)
      (find_vspace_for_asid_L4 s σ hR hPI fa)) ?_
    rintro r ⟨hf, hL⟩
    cases r with
    | Err lf =>
      simp only [error.invalid_cap, bind_ok]
      exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩,
        hdec.trans (fms_noVs hf), rfl⟩)
    | Ok r1 =>
      have hr1 := hL r1 rfl
      dsimp only
      refine WP.spec_bind (mapped_entry_large s σ hPt hPP hr1 ptr rt fa fv dev true hf) ?_
      rintro o hme
      rcases hme with ⟨rfl, hfms⟩ | ⟨q, hq, rfl, hfms⟩
      · simp only [error.invalid_cap, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 0, rfl, Or.inr ⟨0#u64, rfl, rfl⟩,
          hdec.trans hfms, rfl⟩)
      dsimp only
      rw [hct]
      apply ok_bind_spec
      rw [L.read_eq]
      apply ok_bind_spec
      rw [P_ACCESSED_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      apply ok_bind_spec
      rw [L.write_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      obtain ⟨f, hk, hf2⟩ := hPt.l2 q hq
      have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
      have hj := vIdx_lt fv 21
      have hea : Aligned (peA q (vIdx fv 21)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx fv 21)) (L.mem s (peA q (vIdx fv 21)) &&& ~~~32#u64) with hs1
      have hPt1 : PtRel L4 L3 L2 L1 (L.mem s1) σ := by
        have := hPt.upd_l2 hPP hq hk hj _ _ (PDERel_clr5 (hf2 _ hj))
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
        rwa [Function.update_eq_self, updK_self hk] at this
      have hW : WritesIn st s s1 (PdW L2) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hS1 : SR s1 a σ := by
        have := hH.stable2 _ _ a σ _ hS hW ⟨q.bv, f, f, hk, rfl⟩
        rwa [updK_self hk] at this
      have hWA : ∀ b, PdW L2 b → PtWAll L4 L3 L2 L1 b := by
        rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
      have hU1 : UR st th P L4 L3 L2 L1 SR s1 a σ := by
        refine ⟨hS1, StateRel.of_caps hSt hcap, Vs.SlotsValid.of_caps hSV hcap, ?_, hPt1⟩
        rw [hW.1]
        exact hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun _ _ => rfl)
      have hst1 := Notif.setThreadState_eq (σ := σ) .restart hkt'
      have hfin : ∀ v : U64, v = 1#u64 ∨ v = 0#u64 → vspace.reply1 st s1 ct call v ⦃ s2 =>
          TacSpec D σ call (UR st th P L4 L3 L2 L1 SR s2 a) ⦄ := by
        intro v hv
        refine WP.spec_mono (hH.rep.replyR s1 a σ ct call v hU1 hcur) ?_
        rintro s2 ⟨hnf, σ', hm, hU2⟩
        rw [nd_bind_one hst1] at hnf hm
        rw [hcur] at hnf hm
        refine ⟨_, hdec.trans hfms, v.bv, _, σ', by rw [← hcur]; exact hst1, ?_, hnf, hm, hU2⟩
        simp only [Fl4Spec.performTestAndClearAccessed, Fl4Spec.NonDet.select, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff, and_true]
        rcases hv with rfl | rfl
        · right; rfl
        · left; rfl
      split
      · refine WP.spec_bind (hfin 1#u64 (Or.inl rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 (Or.inr ⟨rfl, h⟩)
      · refine WP.spec_bind (hfin 0#u64 (Or.inr rfl)) ?_
        rintro s2 h
        exact (WP.spec_ok _).2 (Or.inr ⟨rfl, h⟩)

/-- **Frame `TestAndClearAccessed` (l4h 0023/0029)**, from `decode_frame`
(see `tac_rel`). -/
theorem frame_tac_rel [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsTacHyps st A th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hU : UR st th P L4 L3 L2 L1 SR s a σ) (hPl : Placed th)
    (hPP : PtPlaced L4 L3 L2 L1) (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hVP : VsPlaced P (L.ksb s))
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (f : vspace.FrameCap) (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) :
    vspace.decode_frame st ar s a fl4_abi.label.X86PageTestAndClearAccessed length slot (frameCapOf f) call buf ex
      ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ = ({(.error e', σ)}, False) ∧
        res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ res.2.2 = a ∧
        TacSpec (ExceptT.run (Fl4Spec.decodeTestAndClearAccessed (Z := Unit) (frameACapG f)) σ) σ call
          (UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2)) ⦄ := by
  unfold vspace.decode_frame
  have hn1 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageMap; decide
  have hn2 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageUnmap := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageUnmap; decide
  have hn3 : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageGetAddress := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageGetAddress; decide
  have hfc : vspace.as_frame (frameCapOf f) = ok (some { f with is_ept := false }) := by
    obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f; rfl
  rw [hfc]
  have hnEpt : ¬ fl4_abi.label.X86PageTestAndClearAccessed = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageTestAndClearAccessed fl4_abi.label.X86PageMapEPT; decide
  simp only [bind_ok, hn1, hn2, hn3, hnEpt, ↓reduceIte]
  refine WP.spec_bind (tac_rel hH s a σ hU hPl hPP hPS hVP hPV hPI ct hct hcur hkt { f with is_ept := false } call) ?_
  rintro ⟨r, s1⟩ h
  rcases h with ⟨e, e', h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · exact (WP.spec_ok _).2 (Or.inl ⟨e, e', h1, h2, h3, h4, rfl⟩)
  · exact (WP.spec_ok _).2 (Or.inr ⟨h1, rfl, h2⟩)

end

end

end Fl4Proofs.P3.Vs
