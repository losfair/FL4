/-
P3 (DESIGN.md §9), VSpace: **`unmap_page_table` refines l4v
`unmap_page_table`**, and the zeroing of an unmapped page table.

* `find_vspace_for_asid_L4`: under `PoolsIn` (every non-null native pool entry
  is a PML4 of `L4`), the root `find_vspace_for_asid` finds is one of `L4`;
* `PtRel.zero_l1`, `writes_zero`: the relation after zeroing a PT of `L1`;
* `unmap_page_table_rel`: FL4's `unmap_page_table` either does nothing
  (the lookups fail, or the PD entry is not this table), as l4v's catches
  its lookup failures, or flushes the ASID, clears the PD entry and flushes
  the paging-structure cache. The flushes are arch effects
  (`VsPtUnmapHyps`): FL4's `invalidate_asid` is matched by an outcome of
  l4v's `flush_table`, `invalidate_page_structures` by an outcome of
  `invalidate_page_structure_cache_asid`;
* `pt_unmap_rel`: FL4's `vspace::decode_table` with label
  `X86PageTableUnmap` against l4v's decode (FL4's `is_final_capability`
  agreeing with l4v's `is_final_cap` is a hypothesis, as in CSpace),
  `Restart` and `perform_page_table_invocation`: for a mapped table,
  `unmap_page_table`, then the table zeroed (l4v: `InvalidPTE` in every
  slot), then the cap's mapping cleared.
-/
import Fl4Proofs.P3.VsPtUnmap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- Every non-null native pool entry is a PML4 of `L4`; guest tags remain occupied. -/
def PoolsIn (P L4 : Set U64) (m : U64 → U64) : Prop :=
  ∀ p ∈ P, ∀ lo : U64, lo.val < 512 → m (peA p lo) ≠ 0#u64 → m (peA p lo) &&& 1#u64 = 0#u64 → m (peA p lo) ∈ L4

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The hypotheses of the page-table unmap (see the module docstrings). -/
structure VsPtInnerHyps (A : Type) (ar : machine.Arch A) (L2 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  pdStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdW L2) → PdStep σ σ' → SR s' a σ'
  flushOK : ∀ (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (σ : Fl4Spec.State Unit),
    ¬ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid σ).2
  flushPS : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ → ar.invalidate_page_structures a asid ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄
  flushTblOK : ∀ (σ : Fl4Spec.State Unit) (vs : Fl4Spec.ObjRef) (v : Fl4Spec.VSpaceRef) (pt : Fl4Spec.ObjRef)
    (asid : Fl4Spec.Asid), v &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0 →
    (∃ f, σ.kheap pt = some (.archObj (.pageTable f))) → ¬ (Fl4Spec.flushTable (Z := Unit) vs v pt asid σ).2
  flushTbl : ∀ s a σ (vs : Fl4Spec.ObjRef) (v : Fl4Spec.VSpaceRef) (pt : Fl4Spec.ObjRef) (asid : U64), SR s a σ →
    v &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0 →
    (∃ f, σ.kheap pt = some (.archObj (.pageTable f))) →
    ar.invalidate_asid a asid ⦃ a' =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.flushTable (Z := Unit) vs v pt asid.bv σ).1 ∧ SR s a' σ' ⦄

/-- The hypotheses of the page-table unmap. -/
structure VsPtUnmapHyps (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop extends VsPtInnerHyps st A ar L2 SR where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → SR s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true → PoolsIn P L4 (L.mem s) →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ∧
      PoolsIn P L4 (L.mem s') ⦄
  capStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (SlotW th) → CapStep σ σ' → SR s' a σ'
  ptStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PtW L1) → PtStep σ σ' → SR s' a σ'

/-- `SR` with the CSpace, ASID and page-table relations. -/
def UR {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ StateRel th (L.mem s) σ ∧ SlotsValid th (L.mem s) ∧ VsRel P (L.mem s) (L.ksb s) σ ∧
    PtRel L4 L3 L2 L1 (L.mem s) σ

end Hyps

/-- **The relation after zeroing the PT at `p`.** -/
theorem PtRel.zero_l1 {L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ) {p : U64} (hp : p ∈ L1) {f : BitVec 9 → Fl4Spec.PTE}
    (hk : σ.kheap p.bv = some (.archObj (.pageTable f)))
    (hm : ∀ b, Aligned b → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) → m' b = m b)
    (hz : ∀ i : U64, i.val < 512 → m' (peA p i) = 0#u64) :
    PtRel L4 L3 L2 L1 m' (updK σ p.bv (.archObj (.pageTable fun _ => .invalidPTE))) := by
  have hpa := hP p (Or.inr (Or.inr (Or.inr hp)))
  have hal : ∀ q j : U64, q.val % 4096 = 0 → j.val < 512 → Aligned (peA q j) := fun q j hq hj => by
    show _ % 8 = 0; rw [peA_val (tbl_fit hq) hj]; omega
  have hoth : ∀ q j : U64, q.val % 4096 = 0 → q ≠ p → j.val < 512 → m' (peA q j) = m (peA q j) := by
    intro q j hq hqp hj
    refine hm _ (hal q j hq hj) ?_
    rw [peA_val (tbl_fit hq) hj]
    have : q.val ≠ p.val := fun h => hqp (UScalar.eq_of_val_eq h)
    omega
  have hkq : ∀ q : U64, ∀ o, σ.kheap q.bv = some o → (∀ g, o ≠ .archObj (.pageTable g)) →
      (updK σ p.bv (.archObj (.pageTable fun _ => .invalidPTE))).kheap q.bv = some o ∧ q ≠ p := by
    intro q o hq hno
    have hqp : q ≠ p := fun e => by subst e; rw [hk] at hq; injection hq with hq; exact hno f hq.symm
    exact ⟨by simp [updK, show q.bv ≠ p.bv from fun h => hqp (eq_of_bv h), hq], hqp⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l4 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inl hq)
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l3 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inl hq))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l2 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inr (Or.inl hq)))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l1 q hq
    have hqa := hP q (Or.inr (Or.inr (Or.inr hq)))
    by_cases e : q = p
    · subst e
      refine ⟨fun _ => .invalidPTE, by simp [updK], fun j hj => ?_⟩
      rw [hz j hj]
      show ¬ (0#u64 &&& 1#u64) ≠ 0#u64
      decide
    · exact ⟨g, by simp [updK, show q.bv ≠ p.bv from fun h => e (eq_of_bv h), hg],
        fun j hj => by rw [hoth q j hqa e hj]; exact hgf j hj⟩

/-- The spec's PageTable Unmap perform, for an unmapped table. -/
theorem performPtUnmap_none {q : Fl4Spec.ObjRef} {pc : Fl4Spec.ObjRef} {idx : List Bool} {r : Nat}
    {cs : Fl4Spec.CnodeContents} {ma : Option (Fl4Spec.Asid × Fl4Spec.VSpaceRef)} {σ1 : Fl4Spec.State Unit}
    (hkc : σ1.kheap pc = some (.cnode r cs)) (hwf : Fl4Spec.wellFormedCnodeN r cs) (hidx : idx.length = r)
    (hcs : cs idx = some (.archObjectCap (.pageTableCap q ma))) :
    Fl4Spec.performPageTableInvocation (Z := Unit) (.pageTableUnmap (.archObjectCap (.pageTableCap q none)) (pc, idx)) σ1 =
      ({((), setCnodeSlot σ1 pc r cs idx (.archObjectCap (.pageTableCap q none)))}, False) := by
  unfold Fl4Spec.performPageTableInvocation
  dsimp only
  rw [nd_bind_one (by unfold Fl4Spec.NonDet.liftM; rw [nd_bind_one' (getCap_cnode hkc hwf hcs)]; rfl)]
  exact setCap_cnode _ hkc hwf hidx

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- Zeroing a 4K table writes only its entry words. -/
theorem writes_zero {L1 : Set U64} {q : U64} (hq : q.val % 4096 = 0) (hq1 : q ∈ L1) (s : S) :
    WritesIn st s (L.zr s q 4096#u64) (PtW L1) := by
  have hf := tbl_fit hq
  refine ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hn => ?_⟩
  rw [L.mem_zr _ _ _ _ (show q.val % 8 = 0 by omega) (by decide) (by simpa using hf) hb]
  split_ifs with h
  · exfalso
    apply hn
    have hb8 : b.val % 8 = 0 := hb
    obtain ⟨h1, h2⟩ := h
    have h2' : b.val < q.val + 4096 := by simpa using h2
    set i : U64 := ⟨BitVec.ofNat 64 ((b.val - q.val) / 8)⟩
    have hi : i.val = (b.val - q.val) / 8 := by
      show (BitVec.ofNat 64 _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨q, hq1, i, by omega, ?_⟩
    apply UScalar.eq_of_val_eq
    rw [peA_val hf (by omega), hi]
    omega
  · rfl

/-- Under `PoolsIn`, the roots `find_vspace_for_asid` finds are PML4s of `L4`. -/
theorem find_asid_native_L4 {P L4 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPI : PoolsIn P L4 (L.mem s)) (asid : U64) :
    vspace.find_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → r1 &&& 1#u64 = 0#u64 → r1 ∈ L4 ⦄ := by
  unfold vspace.find_asid
  have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
  rw [hL]
  step as ⟨i, _hi⟩
  refine WP.spec_bind (asid_table_spec s i) ?_
  rintro pool rfl
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have hlo := and_lt asid 9 511#u64 rfl (by decide)
  split
  · exact (WP.spec_ok _).2 fun e he => by cases he
  · rename_i hp
    have hpP := hR.tmem _ hlt hp
    unfold lift
    simp only [bind_ok]
    rw [L.read_eq]
    simp only [bind_ok]
    split
    · exact (WP.spec_ok _).2 fun e he => by cases he
    · rename_i h0
      exact (WP.spec_ok _).2 fun r1 hr1 => by cases hr1; exact hPI _ hpP _ hlo h0

/-- Tagged guest entries are occupied, but native lookup never returns them. -/
theorem find_vspace_for_asid_L4 {P L4 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPI : PoolsIn P L4 (L.mem s)) (asid : U64) :
    vspace.find_vspace_for_asid st s asid ⦃ r => ∀ r1, r = .Ok r1 → r1 ∈ L4 ⦄ := by
  unfold vspace.find_vspace_for_asid
  refine WP.spec_bind (find_asid_native_L4 s σ hR hPI asid) ?_
  intro r hr
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, lift, bind_ok, bind_tc_ok, WP.spec_ok]
    intro r1 he
    cases he
  | Ok w =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
    by_cases ht : w &&& 1#u64 = 0#u64
    · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      intro r1 he
      cases he
      exact hr _ rfl ht
    · simp [ht, WP.spec_ok]

set_option maxRecDepth 8000 in
/-- **`unmap_page_table`** refines l4v `unmap_page_table` (see the module
docstring). -/
theorem unmap_page_table_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPtInnerHyps st A ar L2 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hVP : VsPlaced P (L.ksb s))
    (hPV : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hU : UR st th P L4 L3 L2 L1 SR s a σ) (asid vaddr pt : U64) (h0 : asid ≠ 0#u64)
    (hal : vaddr.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0) (hpt : pt ∈ L1) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r =>
      ¬ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).2 ∧
      (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).1 →
        ∀ p, (∀ g, σ.kheap p ≠ some (.archObj (.pageDirectory g))) → σ'.kheap p = σ.kheap p) ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).1 ∧
        UR st th P L4 L3 L2 L1 SR r.1 r.2 σ' ∧ L.ksb r.1 = L.ksb s ⦄ := by
  obtain ⟨hS, hSt, hSV, hR, hPt⟩ := hU
  have hskip : Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ = ({((), σ)}, False) →
      (ok (s, a) : Result (S × A)) ⦃ r =>
        ¬ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).2 ∧
        (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).1 →
          ∀ p, (∀ g, σ.kheap p ≠ some (.archObj (.pageDirectory g))) → σ'.kheap p = σ.kheap p) ∧
        ∃ σ', ((), σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid.bv vaddr.bv pt.bv σ).1 ∧
          UR st th P L4 L3 L2 L1 SR r.1 r.2 σ' ∧ L.ksb r.1 = L.ksb s ⦄ := by
    intro h
    refine (WP.spec_ok _).2 ⟨by rw [h]; exact id, fun x σ' hx p _ => ?_, σ, by rw [h]; simp,
      ⟨hS, hSt, hSV, hR, hPt⟩, rfl⟩
    rw [h] at hx; simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hx; rw [hx.2]
  unfold vspace.unmap_page_table
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0)
    (find_vspace_for_asid_L4 s σ hR hPI asid)) ?_
  rintro r ⟨hf, hL⟩
  cases r with
  | Err lf => exact hskip (unmapPT_noVs hf)
  | Ok r1 =>
    have hr1 := hL r1 rfl
    refine WP.spec_bind (lookup_pd_slot_rel s σ hPt hPP hr1 vaddr) ?_
    rintro r2 ⟨hsp, hsl, hse⟩
    cases r2 with
    | Err lf =>
      obtain ⟨n, rfl⟩ := hse _ rfl
      exact hskip (unmapPT_noSlot hf hsp)
    | Ok x =>
      obtain ⟨q, hq, rfl⟩ := hsl _ rfl
      obtain ⟨f, hk, hf2⟩ := hPt.l2 q hq
      have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
      have hj := vIdx_lt vaddr 21
      have hfe2 := hf2 _ hj
      have hg : Fl4Spec.getPde (Z := Unit) (peA q (vIdx vaddr 21)).bv σ =
          ({(f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv), σ)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPde_at hqa hk hj
      dsimp only
      rw [L.read_eq]
      apply ok_bind_spec
      rw [P_PRESENT_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      by_cases hp0 : (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64
      · rw [if_pos hp0]
        exact hskip (unmapPT_other hf hsp hg (fun a b c h => by rw [h] at hfe2; exact absurd hp0 hfe2.1))
      rw [if_neg hp0, P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hps : ((L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) != 0#u64) = true
      · rw [if_pos hps]
        exact hskip (unmapPT_other hf hsp hg (fun a b c h => by
          rw [h] at hfe2; exact absurd ((eS_iff _).1 hps) hfe2.2.1))
      rw [if_neg hps]
      apply ok_bind_spec
      have hAM : vspace.ADDR_MASK = 4503599627366400#u64 := by unfold vspace.ADDR_MASK; rfl
      simp only [layout.paddr, bind_ok]
      rw [hAM]
      have hadr' : ∀ a b c, f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) = .pageTablePDE a b c →
          (Fl4Spec.addrFromPPtr pt.bv = a ↔
            eA (L.mem s (peA q (vIdx vaddr 21))) = core.num.U64.wrapping_sub pt layout.PPTR_BASE) := by
        intro a b c h
        rw [h] at hfe2
        rw [← hfe2.2.2.1, ← paddr_bv]
        exact ⟨fun e => (eq_of_bv e).symm, fun e => by rw [e]⟩
      by_cases hadr : ((L.mem s (peA q (vIdx vaddr 21)) &&& 4503599627366400#u64) !=
          core.num.U64.wrapping_sub pt layout.PPTR_BASE) = true
      · rw [if_pos hadr]
        exact hskip (unmapPT_other hf hsp hg (fun a b c h e => (bne_iff_ne.1 hadr) ((hadr' a b c h).1 e)))
      rw [if_neg hadr]
      have hadrE : eA (L.mem s (peA q (vIdx vaddr 21))) = core.num.U64.wrapping_sub pt layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      obtain ⟨ta, tr, hpde⟩ : ∃ ta tr, f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) =
          .pageTablePDE (Fl4Spec.addrFromPPtr pt.bv) ta tr := by
        revert hadr'
        cases hfx : f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro; rw [hfx] at hfe2; exact absurd hp0 hfe2
        | largePagePDE _ _ _ => intro; rw [hfx] at hfe2; exact absurd ((eS_iff _).2 hfe2.2.1) hps
        | pageTablePDE a b c => intro h; exact ⟨b, c, by rw [(h a b c rfl).2 hadrE]⟩
      rw [hpde] at hg
      have hun := unmapPT_match hf hsp hg
      have hptk : ∃ g, σ.kheap pt.bv = some (.archObj (.pageTable g)) := by
        obtain ⟨g, hg', -⟩ := hPt.l1 pt hpt; exact ⟨g, hg'⟩
      have hstoreAt : ∀ ms, Fl4Spec.storePde (Z := Unit) (peA q (vIdx vaddr 21)).bv .invalidPDE
          { σ with machineState := ms } = ({((), updK { σ with machineState := ms } q.bv
            (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) .invalidPDE))))}, False) := by
        intro ms; rw [peA_bv _ _ hj (tbl_fit hqa)]
        exact storePde_at hqa (show ({ σ with machineState := ms } : Fl4Spec.State Unit).kheap q.bv = _ from hk) hj _
      refine WP.spec_bind (hH.flushTbl s a σ r1.bv vaddr.bv pt.bv asid hS hal hptk) ?_
      rintro a1 ⟨σf, hσf, hSf⟩
      have hσf' := hσf
      obtain ⟨ms, rfl⟩ := flushTable_mem hσf
      rw [L.write_eq]
      apply ok_bind_spec
      have hea : Aligned (peA q (vIdx vaddr 21)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx vaddr 21)) 0#u64 with hs1
      set σs := updK { σ with machineState := ms } q.bv
        (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) .invalidPDE))) with hσs
      have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
        (show PtRel L4 L3 L2 L1 (L.mem s) { σ with machineState := ms } from ⟨hPt.l4, hPt.l3, hPt.l2, hPt.l1⟩).upd_l2
          hPP hq hk hj 0#u64 .invalidPDE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
      have hW : WritesIn st s s1 (PdW L2) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hSs := hH.pdStable _ _ a1 _ σs hSf hW ⟨q.bv, f, _, hk, rfl⟩
      have hPS2 : ∀ b, PdW L2 b → ¬ SlotW th b := by
        rintro b ⟨p, hp, i, hi, hb⟩
        exact hPS b ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW hPS2
      have hSts : StateRel th (L.mem s1) σs :=
        Vs.StateRel.upd_other (StateRel.of_caps (Vs.StateRel.ms hSt ms) hcap) hk _
      have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
      have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
        rw [hW.1]
        refine (show VsRel P (L.mem s) (L.ksb s) { σ with machineState := ms } from ⟨hR.1, hR.2, hR.3⟩).frame
          (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b h hb)) rfl (fun p hp => ?_)
        obtain ⟨g, hg', -⟩ := hR.pool p hp
        have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
        simp [hσs, updK, this]
      refine WP.spec_bind (hH.flushPS s1 a1 σs (Fl4Spec.addrFromPPtr r1.bv) asid hSs) ?_
      rintro a2 ⟨σ', hσ', hS'⟩
      have hσ'' := hσ'
      obtain ⟨ms2, rfl⟩ := doMachineOp_mem hσ'
      refine (WP.spec_ok _).2 ⟨?_, ?_, _, ?_, ⟨hS', Vs.StateRel.ms hSts ms2, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
        ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _⟩
      · rw [hun]
        refine nd_nofail_bind (hH.flushTblOK σ r1.bv vaddr.bv pt.bv asid.bv hal hptk) (fun y hy => ?_)
        obtain ⟨u, σy⟩ := y
        cases u
        obtain ⟨msy, hmsy⟩ := flushTable_mem hy
        subst hmsy
        rw [nd_bind_one (hstoreAt msy)]
        exact hH.flushOK _ _ _
      · intro x σ'' hx p hp
        rw [hun, nd_bind_apply'] at hx
        obtain ⟨⟨u, σy⟩, hy, hx⟩ := hx
        cases u
        obtain ⟨msy, hmsy⟩ := flushTable_mem hy
        subst hmsy
        rw [nd_bind_one (hstoreAt msy)] at hx
        obtain ⟨ms3, rfl⟩ := doMachineOp_mem hx
        have : p ≠ q.bv := fun e => hp f (by rw [e]; exact hk)
        show Function.update σ.kheap q.bv _ p = σ.kheap p
        rw [Function.update_of_ne this]
      · rw [hun]
        exact nd_mem_bind hσf' (by rw [nd_bind_one (hstoreAt ms)]; exact hσ'')

section KF
open Fl4Spec

theorem kfoot_mapMx {α : Type} (g : α → SMonad Unit Unit)
    (hg : ∀ x (σ0 : State Unit), ∀ y ∈ (g x σ0).1, KFoot σ0 y.2) :
    ∀ (l : List α) (σ0 : State Unit), ∀ y ∈ (NonDet.mapMx g l σ0).1, KFoot σ0 y.2
  | [], σ0, y, hy => by
    simp only [NonDet.mapMx, NonDet.pure, Set.mem_singleton_iff] at hy; rw [hy]; exact KFoot.refl _
  | x :: l, σ0, y, hy => by
    simp only [NonDet.mapMx, NonDet.bind] at hy
    obtain ⟨z, hz, hw⟩ := hy
    exact (hg x σ0 z hz).trans (kfoot_mapMx g hg l z.2 y hw)

/-- `flush_table` changes the machine state only. -/
theorem kfoot_flushTable {σ : State Unit} {vs : ObjRef} {v : VSpaceRef} {pt : ObjRef} {asid : Asid}
    (hal : v &&& mask (ptTranslationBits + pageBits) = 0) {f : BitVec 9 → PTE}
    (hk : σ.kheap pt = some (.archObj (.pageTable f))) :
    ∀ y ∈ (flushTable (Z := Unit) vs v pt asid σ).1, KFoot σ y.2 := by
  have ha : NonDet.assert (σ := State Unit) (v &&& mask (ptTranslationBits + pageBits) = 0) σ = ({((), σ)}, False) := by
    simp [NonDet.assert, hal]
  have hg : getPt (Z := Unit) pt σ = ({(f, σ)}, False) := by
    unfold getPt; rw [nd_bind_one (getObject_eq hk)]; rfl
  unfold flushTable
  rw [nd_bind_one ha, nd_bind_one hg]
  refine kfoot_mapMx _ (fun index σ0 y hy => ?_) _ σ
  rw [nd_pure_bind'] at hy
  cases e : f index <;> rw [e] at hy
  all_goals first
    | (simp only [pure, NonDet.pure, Set.mem_singleton_iff] at hy; rw [hy]; exact KFoot.refl _)
    | (obtain ⟨u, σ1⟩ := y; obtain ⟨ms, rfl⟩ := doMachineOp_mem hy; exact KFoot.ms _ ms)

end KF

/-- **PageTable `Unmap` refines l4v**: the decode (`is_final_capability`
against l4v's `is_final_cap`, a hypothesis as in CSpace), `Restart`, and the
perform (`unmap_page_table`, clearing the table, and the cap's mapping). -/
theorem pt_unmap_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPtUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV2 : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b)
    (hPV1 : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL1 : ptr ∈ L1) (hfe : EncWf (.PageTable ptr mp asid0 va0))
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (length buf : U64) (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {fin : Bool} (hfin : cdt.is_final_capability st s (cslotAddr (pc.bv, idx)) = ok fin)
    (hfinR : fin = true ↔ Fl4Spec.isFinalCap'
      (.archObjectCap (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageTableUnmap length (cslotAddr (pc.bv, idx))
      (.PageTable ptr mp asid0 va0) buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx)
          (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs) σ =
            ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs
          (pc.bv, idx) (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs) σ =
            ({(.ok iv, σ)}, False) ∧
        PtMapSpec σ iv σ' ∧ UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.PageTable ptr mp asid0 va0) ∧ KFoot σ σ') ⦄ := by
  rw [show Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx)
      (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs =
    Fl4Spec.decodePageTableInvocation slbl args (pc.bv, idx)
      (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs from rfl]
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, ↓reduceIte]
  unfold vspace.decode_table_unmap
  rw [hfin]
  apply ok_bind_spec
  obtain ⟨cs, hkc, hwf, hsl⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .PageTable ptr mp asid0 va0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.PageTable ptr mp asid0 va0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnf : ¬ Fl4Spec.isFinalCap'
        (.archObjectCap (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ :=
      fun h => by simpa using hfinR.2 h
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .revokeFirst, rfl, Or.inl (show SysErrRel (.Sys .RevokeFirst) .revokeFirst from trivial),
      ptDecodeUnmap_notFinal hl _ _ _ _ _ σ hnf, rfl, rfl⟩)
  simp only [↓reduceIte]
  have hfn := hfinR.1 rfl
  have hdec := ptDecodeUnmap_final hl args (pc.bv, idx) ptr.bv _ vcs σ hfn
  rw [hdec]
  rw [hct]
  apply ok_bind_spec
  have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
  refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hPt hS hcur hkt' htcb hact hrun hPI)
    (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
  rintro s1 ⟨⟨hSt1, hSV1, hR1, hPt1, hS1, hk1, hPI1⟩, hSS1⟩
  set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
  have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
  have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by
    rw [hσ1, stsAct_kheap]; simp [updK, hpct, hkc]
  have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
  have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
  set nc : Fl4Spec.Cap := .archObjectCap (.pageTableCap ptr.bv none) with hnc
  have hca : CapRel (.PageTable ptr false 0#u64 0#u64) nc := ⟨trivial, rfl⟩
  have hew : EncWf (.PageTable ptr false 0#u64 0#u64) := ⟨hfe.1, by decide, by decide⟩
  have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
  -- the final `set_cap`, from a state `s4`/`σ4` with the CNode unchanged
  have fin_cap : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit), UR st th P L4 L3 L2 L1 SR s4 a4 σ4 →
      σ4.kheap pc.bv = some (.cnode r cs) → L.ksb s4 = L.ksb s →
      obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s4 (.PageTable ptr false 0#u64 0#u64) ⦃ s5 =>
        UR st th P L4 L3 L2 L1 SR s5 a4 (setCnodeSlot σ4 pc.bv r cs idx nc) ∧
        SlotFoot th (L.mem s4) (L.mem s5) (cslotAddr (pc.bv, idx)) ∧
        capV (L.mem s5) (cslotAddr (pc.bv, idx)) = .PageTable ptr false 0#u64 0#u64 ⦄ := by
    rintro s4 a4 σ4 ⟨hS4, hSt4, hSV4, hR4, hPt4⟩ hkc4 hks4
    refine WP.spec_mono (WP.spec_and (set_cap_refines th s4 σ4 hSt4 hSV4 hPl hpc hidx _ _ hca trivial hew)
      (WP.spec_and (set_cap_spec (L := L) _ s4 _) (set_cap_foot hPl hxsl s4 _ hew))) ?_
    rintro s5 ⟨⟨σ5, hsc, hSt5, hSV5, -, -, -, hfr5⟩, hs5, hF5, hcv5⟩
    have hσ5 : σ5 = setCnodeSlot σ4 pc.bv r cs idx nc := by
      rw [setCap_cnode nc hkc4 hwf hidx] at hsc
      have := congrArg Prod.fst hsc
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    subst hσ5
    have hks5 : L.ksb s5 = L.ksb s4 := by rw [hs5]; simp
    have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s5 b = L.mem s4 b := by
      intro b hb
      obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
      exact hfr5 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
    have hpools : ∀ q ∈ P, (setCnodeSlot σ4 pc.bv r cs idx nc).kheap q.bv = σ4.kheap q.bv := by
      intro q hq
      obtain ⟨g, hg, -⟩ := hR4.pool q hq
      have : q.bv ≠ pc.bv := kheap_ne hg hkc4 (fun _ h1 h2 => by subst h1; cases h2)
      simp [setCnodeSlot, this]
    have hWs : WritesIn st s4 s5 (SlotW th) := by
      refine ⟨by rw [hs5]; simp, by rw [hs5]; simp, fun b hb hn => ?_⟩
      obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
      exact hfr5 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
    refine ⟨⟨hH.capStable _ _ a4 _ _ hS4 hWs ⟨pc.bv, r, cs, idx, nc, hkc4, rfl⟩, hSt5, hSV5, ?_, ?_⟩, hF5, hcv5⟩
    · rw [hks5]; rw [hks4] at hR4 ⊢
      exact hR4.frame hfrV rfl hpools
    · refine hPt4.frame (fun b hb => ?_) (fun q hq => ?_)
      · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
        exact hfr5 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      · obtain ⟨ao, hao⟩ := hPt4.arch hq
        have : q.bv ≠ pc.bv := kheap_ne hao hkc4 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
  obtain ⟨f1, hkp1, -⟩ := hPt1.l1 ptr hpL1
  have hqa := hPP ptr (Or.inr (Or.inr (Or.inr hpL1)))
  have hpc' : ptr.bv ≠ pc.bv := kheap_ne hkp1 hkc1 (fun _ h1 h2 => by subst h1; cases h2)
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hcs ⊢
    rw [show vspace.with_mapping (.PageTable ptr false asid0 va0) false asid0 va0 =
      ok (.PageTable ptr false 0#u64 0#u64) by simp [vspace.with_mapping]]
    apply ok_bind_spec
    refine WP.spec_bind (fin_cap s1 a σ1 ⟨hS1, hSt1, hSV1, hR1, hPt1⟩ hkc1 hk1) ?_
    rintro s5 ⟨hU5, hF5, hcv5⟩
    refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans hF5,
      by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK] at h ⊢; first | exact ⟨h.1, h.2.1, fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2.1, trivial⟩⟩, (KFoot.sts hkt' _).trans (KFoot.cnode hkc1 hwf idx nc)⟩)
    unfold PtMapSpec
    dsimp only
    rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt'), performPtUnmap_none hkc1 hwf hidx hcs]
    exact ⟨rfl, id⟩
  · obtain ⟨hA0, hVA⟩ := hm0 rfl
    simp only [↓reduceIte] at hcs ⊢
    let SR' : S → A → Fl4Spec.State Unit → Prop := fun s' a' σ' =>
      SR s' a' σ' ∧ SlotFoot th (L.mem s1) (L.mem s') (cslotAddr (pc.bv, idx)) ∧ KFoot σ1 σ'
    have hH' : VsPtInnerHyps st A ar L2 SR' :=
      { pdStable := fun s' s'' a' σ' σ'' ⟨h1, h2, h3⟩ hw hst => ⟨hH.pdStable _ _ _ _ _ h1 hw hst,
          h2.trans (SlotFoot.of_writes hPl hw (fun b ⟨q, hq, i, hi, e⟩ =>
            hPO b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) _),
          h3.trans (by obtain ⟨p, f, f', hk, rfl⟩ := hst; exact KFoot.arch hk _)⟩
        flushOK := hH.flushOK
        flushPS := fun s' a' σ' vs asid ⟨h1, h2, h3⟩ => WP.spec_mono (hH.flushPS s' a' σ' vs asid h1)
          (fun a'' ⟨σ'', hm, hS''⟩ => ⟨σ'', hm, hS'', h2, h3.trans (by
            obtain ⟨ms, rfl⟩ := doMachineOp_mem hm; exact KFoot.ms _ ms)⟩)
        flushTblOK := hH.flushTblOK
        flushTbl := fun s' a' σ' vs v pt asid ⟨h1, h2, h3⟩ hal hf =>
          WP.spec_mono (hH.flushTbl s' a' σ' vs v pt asid h1 hal hf)
          (fun a'' ⟨σ'', hm, hS''⟩ => ⟨σ'', hm, hS'', h2, h3.trans (by
            obtain ⟨f, hk⟩ := hf; exact kfoot_flushTable hal hk _ hm)⟩) }
    have hU1 : UR st th P L4 L3 L2 L1 SR' s1 a σ1 := ⟨⟨hS1, SlotFoot.refl _ _, KFoot.refl _⟩, hSt1, hSV1, hR1, hPt1⟩
    refine WP.spec_bind (Pₘ := fun p => ∃ σu, ((), σu) ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 ∧
        ¬ (Fl4Spec.unmapPageTable (Z := Unit) asid0.bv va0.bv ptr.bv σ1).2 ∧
        (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 →
          σ'.kheap ptr.bv = σ1.kheap ptr.bv ∧ σ'.kheap pc.bv = σ1.kheap pc.bv) ∧
        UR st th P L4 L3 L2 L1 SR p.1 p.2 (updK σu ptr.bv (.archObj (.pageTable fun _ => .invalidPTE))) ∧
        (updK σu ptr.bv (.archObj (.pageTable fun _ => .invalidPTE))).kheap pc.bv = some (.cnode r cs) ∧
        L.ksb p.1 = L.ksb s ∧ SlotFoot th (L.mem s1) (L.mem p.1) (cslotAddr (pc.bv, idx)) ∧
        KFoot σ1 (updK σu ptr.bv (.archObj (.pageTable fun _ => .invalidPTE)))) ?_ ?_
    · refine WP.spec_bind (unmap_page_table_rel hH' s1 a σ1 hPl hPP hPS (hk1 ▸ hVP) (hk1 ▸ hPV2) hPI1 hU1
        asid0 va0 ptr hA0 hVA hpL1) ?_
      rintro ⟨s3, a3⟩ ⟨hnu, hall, σu, hu, ⟨⟨hS3, hF3, hK3⟩, hSt3, hSV3, hR3, hPt3⟩, hk3⟩
      show (st.zero s3 ptr 4096#u64 >>= fun s4 => ok (s4, a3)) ⦃ _ ⦄
      rw [L.zero_eq]
      apply ok_bind_spec
      have hall' : ∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPageTable (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 →
          σ'.kheap ptr.bv = σ1.kheap ptr.bv ∧ σ'.kheap pc.bv = σ1.kheap pc.bv := fun x σ' hx =>
        ⟨hall x σ' hx ptr.bv (fun g h => by rw [hkp1] at h; cases h),
          hall x σ' hx pc.bv (fun g h => by rw [hkc1] at h; cases h)⟩
      have hkpu : σu.kheap ptr.bv = some (.archObj (.pageTable f1)) := (hall' () σu hu).1.trans hkp1
      have hkcu : σu.kheap pc.bv = some (.cnode r cs) := (hall' () σu hu).2.trans hkc1
      have hW := writes_zero hqa hpL1 (L := L) s3
      have hf := tbl_fit hqa
      have hzr : ∀ b, Aligned b → L.mem (L.zr s3 ptr 4096#u64) b =
          if ptr.val ≤ b.val ∧ b.val < ptr.val + (4096#u64).val then 0#u64 else L.mem s3 b := fun b hb =>
        L.mem_zr _ _ _ _ (show ptr.val % 8 = 0 by omega) (by decide) (by simpa using hf) hb
      have hPt4 : PtRel L4 L3 L2 L1 (L.mem (L.zr s3 ptr 4096#u64))
          (updK σu ptr.bv (.archObj (.pageTable fun _ => .invalidPTE))) := by
        refine hPt3.zero_l1 hPP hpL1 hkpu (fun b hb hn => ?_) (fun i hi => ?_)
        · rw [hzr b hb, if_neg (by simpa using hn)]
        · have hal : Aligned (peA ptr i) := by show _ % 8 = 0; rw [peA_val hf hi]; omega
          rw [hzr _ hal, if_pos (by rw [peA_val hf hi]; simp; omega)]
      have hPS1 : ∀ b, PtW L1 b → ¬ SlotW th b := by
        rintro b ⟨p, hp, i, hi, hb⟩
        exact hPS b ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW hPS1
      have hks3 : L.ksb s3 = L.ksb s := hk3.trans hk1
      refine (WP.spec_ok _).2 ⟨σu, hu, hnu, hall', ⟨hH.ptStable _ _ a3 _ _ hS3 hW ⟨ptr.bv, f1, _, hkpu, rfl⟩,
        Vs.StateRel.upd_other (StateRel.of_caps hSt3 hcap) hkpu _, Vs.SlotsValid.of_caps hSV3 hcap, ?_, hPt4⟩,
        by simp [updK, hpc'.symm, hkcu], by rw [L.ksb_zr, hks3],
        hF3.trans (SlotFoot.of_writes hPl hW (fun b ⟨q, hq, i, hi, e⟩ =>
          hPO b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩) _), hK3.trans (KFoot.arch hkpu _)⟩
      rw [hW.1]
      refine hR3.frame (fun b hb => hW.2.2 b (hb.aligned (hks3 ▸ hVP)) (fun h => hPV1 b h (hks3 ▸ hb))) rfl
        (fun p hp => ?_)
      obtain ⟨g, hg, -⟩ := hR3.pool p hp
      have : p.bv ≠ ptr.bv := kheap_ne hg hkpu (fun _ h1 h2 => by subst h1; cases h2)
      simp [updK, this]
    · rintro ⟨s4, a4⟩ ⟨σu, hu, hnu, hall', hU4, hkc4, hks4, hF4, hK4⟩
      show (vspace.with_mapping (.PageTable ptr true asid0 va0) false asid0 va0 >>= fun c =>
        obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s4 c >>= fun s3 => ok (core.result.Result.Ok (), s3, a4)) ⦃ _ ⦄
      rw [show vspace.with_mapping (.PageTable ptr true asid0 va0) false asid0 va0 =
        ok (.PageTable ptr false 0#u64 0#u64) by simp [vspace.with_mapping]]
      apply ok_bind_spec
      refine WP.spec_bind (fin_cap s4 a4 _ hU4 hkc4 hks4) ?_
      rintro s5 ⟨hU5, hF5, hcv5⟩
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans (hF4.trans hF5),
        by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK] at h ⊢; first | exact ⟨h.1, h.2.1, fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2.1, trivial⟩⟩, (KFoot.sts hkt' _).trans (hK4.trans (KFoot.cnode hkc4 hwf idx nc))⟩)
      unfold PtMapSpec
      dsimp only
      rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
      exact performPtUnmap_mem hqa hnu hall' hu hkp1 hkc1 hwf hidx hcs

end

end

end Fl4Proofs.P3.Vs
