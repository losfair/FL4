/-
P3 (DESIGN.md §9), VSpace: **Frame `Unmap` refines l4v**, for every page
size.

* `unmap_page_rel`: FL4's `unmap_page` against l4v `unmap_page`: nothing
  when the lookups fail or the entry does not map the frame (FL4: not
  present, PS not as the size needs, or `frame_base` not the frame's address;
  l4v: `check_mapping_pptr` false, caught), else the entry is cleared and the
  page's translation flushed (FL4 `invalidate_page`, matched by an outcome of
  l4v's `invalidateTranslationSingleASID`, `VsFrameUnmapHyps.flushPg`).
* `frame_unmap_rel`: FL4's `vspace::decode_frame` with label `X86PageUnmap`
  against l4v's decode (which always succeeds), `Restart` and
  `perform_page_invocation`: for a mapped cap `unmap_page`, then the cap's
  mapping cleared.

Hypotheses (`VsFrameUnmapHyps`): `restart` (keeping `PoolsIn`), `capStable`,
`SR` stable under PT/PD/PDPT entry writes, and the flush.
-/
import Fl4Proofs.P3.VsFrameUnmap
import Fl4Proofs.P3.VsFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The hypotheses of `unmap_page`: `SR` stable under the entry writes, and
the flush. -/
structure VsUnmapPageHyps (A : Type) (ar : machine.Arch A) (L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  ptStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PtW L1) → PtStep σ σ' → SR s' a σ'
  pdStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdW L2) → PdStep σ σ' → SR s' a σ'
  pdptStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdptW L3) → PdptStep σ σ' → SR s' a σ'
  flushPgOK : ∀ (σ : Fl4Spec.State Unit) (v asid : Fl4Spec.Data),
    ¬ (Fl4Spec.doMachineOp (Z := Unit) (Fl4Spec.invalidateTranslationSingleASID v asid) σ).2
  flushPg : ∀ s a σ (asid vaddr : U64), SR s a σ → ar.invalidate_page a asid vaddr ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.doMachineOp (Z := Unit)
      (Fl4Spec.invalidateTranslationSingleASID vaddr.bv (Fl4Spec.ucast 64 asid.bv)) σ).1 ∧ SR s a' σ' ⦄

/-- The hypotheses of the frame unmap. -/
structure VsFrameUnmapHyps (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop extends VsUnmapPageHyps st A ar L3 L2 L1 SR where
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

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxRecDepth 8000 in
/-- **`unmap_page`** refines l4v `unmap_page` (see the module docstring). -/
theorem unmap_page_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hVP : VsPlaced P (L.ksb s))
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hU : UR st th P L4 L3 L2 L1 SR s a σ) (sz : capability.FrameSize) (asid vaddr pp : U64) (h0 : asid ≠ 0#u64) :
    vspace.unmap_page st ar s a sz asid vaddr pp ⦃ r =>
      ¬ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).2 ∧
      (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).1 →
        ∀ p, (∀ ao, σ.kheap p ≠ some (.archObj ao)) → σ'.kheap p = σ.kheap p) ∧
      ∃ σ', ((), σ') ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).1 ∧
        UR st th P L4 L3 L2 L1 SR r.1 r.2 σ' ∧ L.ksb r.1 = L.ksb s ⦄ := by
  obtain ⟨hS, hSt, hSV, hR, hPt⟩ := hU
  have hskip : Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ = ({((), σ)}, False) →
      (ok (s, a) : Result (S × A)) ⦃ r =>
        ¬ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).2 ∧
        (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).1 →
          ∀ p, (∀ ao, σ.kheap p ≠ some (.archObj ao)) → σ'.kheap p = σ.kheap p) ∧
        ∃ σ', ((), σ') ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) asid.bv vaddr.bv pp.bv σ).1 ∧
          UR st th P L4 L3 L2 L1 SR r.1 r.2 σ' ∧ L.ksb r.1 = L.ksb s ⦄ := by
    intro h
    refine (WP.spec_ok _).2 ⟨by rw [h]; exact id, fun x σ' hx p _ => ?_, σ, by rw [h]; simp,
      ⟨hS, hSt, hSV, hR, hPt⟩, rfl⟩
    rw [h] at hx; simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hx; rw [hx.2]
  have hAM : vspace.ADDR_MASK = 4503599627366400#u64 := by unfold vspace.ADDR_MASK; rfl
  unfold vspace.unmap_page
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0)
    (find_vspace_for_asid_L4 s σ hR hPI asid)) ?_
  rintro r ⟨hf, hL⟩
  cases r with
  | Err lf => exact hskip (unmapPage_noVs hf)
  | Ok r1 =>
    have hr1 := hL r1 rfl
    dsimp only
    simp only [layout.paddr, bind_ok]
    cases sz with
    | Small =>
      refine WP.spec_bind (lookup_pt_slot_rel s σ hPt hPP hr1 vaddr) ?_
      rintro r2 ⟨hsp, hsl, hse⟩
      cases r2 with
      | Err lf =>
        obtain ⟨n, rfl⟩ := hse _ rfl
        exact hskip (unmapPage_s_noSlot hf hsp)
      | Ok x =>
        obtain ⟨q, hq, rfl⟩ := hsl _ rfl
        obtain ⟨f, hk, hf2⟩ := hPt.l1 q hq
        have hqa := hPP q (Or.inr (Or.inr (Or.inr hq)))
        have hj := vIdx_lt vaddr 12
        have hfe2 := hf2 _ hj
        have hg : Fl4Spec.getPte (Z := Unit) (peA q (vIdx vaddr 12)).bv σ =
            ({(f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv), σ)}, False) := by
          rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPte_at hqa hk hj
        dsimp only
        rw [L.read_eq]
        apply ok_bind_spec
        rw [P_PRESENT_eq]
        apply ok_bind_spec
        unfold lift
        apply ok_bind_spec
        by_cases hp0 : (L.mem s (peA q (vIdx vaddr 12)) &&& 1#u64) = 0#u64
        · rw [if_pos hp0]
          refine hskip (unmapPage_s_other hf hsp hg ?_)
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) with
          | invalidPTE => intro; rfl
          | smallPagePTE _ _ _ => intro h; exact absurd hp0 h.1
        rw [if_neg hp0]
        simp only [not_true_eq_false, ↓reduceIte, vspace.frame_base, bind_ok]
        rw [hAM]
        obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) = .smallPagePTE fb fa fr := by
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) with
          | invalidPTE => intro h; exact absurd hp0 h
          | smallPagePTE a b c => intro; exact ⟨a, b, c, rfl⟩
        rw [hfx] at hfe2 hg
        have hfb : (eA (L.mem s (peA q (vIdx vaddr 12)))).bv = fb := hfe2.2.1
        by_cases hadr : ((L.mem s (peA q (vIdx vaddr 12)) &&& 4503599627366400#u64) !=
            core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
        · rw [if_pos hadr]
          refine hskip (unmapPage_s_other hf hsp hg ?_)
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
          rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
          exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
        rw [if_neg hadr]
        have hadrE : eA (L.mem s (peA q (vIdx vaddr 12))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
          Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
        have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPTE (.smallPagePTE fb fa fr)) = true := by
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
          rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
        set σs := updK σ q.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) .invalidPTE)))
          with hσs
        have hstore : Fl4Spec.storePte (Z := Unit) (peA q (vIdx vaddr 12)).bv .invalidPTE σ = ({((), σs)}, False) := by
          rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePte_at hqa hk hj _
        have hun := unmapPage_s_match hf hsp hg hc hstore
        rw [L.write_eq]
        apply ok_bind_spec
        have hea : Aligned (peA q (vIdx vaddr 12)) := by
          show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
        set s1 := L.wr s (peA q (vIdx vaddr 12)) 0#u64 with hs1
        have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
          hPt.upd_l1 hPP hq hk hj 0#u64 .invalidPTE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
            (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
        have hW : WritesIn st s s1 (PtW L1) :=
          ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
            (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
        have hSs := hH.ptStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
        have hWA : ∀ b, PtW L1 b → PtWAll L4 L3 L2 L1 b := by
          rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
        have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
        have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
        have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
        have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
          rw [hW.1]
          refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
          obtain ⟨g, hg', -⟩ := hR.pool p hp
          have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
          simp [hσs, updK, this]
        refine WP.spec_bind (hH.flushPg s1 a σs asid vaddr hSs) ?_
        rintro a1 ⟨σ', hσ', hS'⟩
        have hσ'' := hσ'
        obtain ⟨ms, rfl⟩ := doMachineOp_mem hσ'
        refine (WP.spec_ok _).2 ⟨?_, ?_, _, ?_, ⟨hS', Vs.StateRel.ms hSts ms, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
          ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _⟩
        · show ¬ (Fl4Spec.unmapPage (Z := Unit) .x64SmallPage asid.bv vaddr.bv pp.bv σ).2
          rw [hun]; exact hH.flushPgOK _ _ _
        · intro x σ'' hx p hp
          change (x, σ'') ∈ (Fl4Spec.unmapPage (Z := Unit) .x64SmallPage asid.bv vaddr.bv pp.bv σ).1 at hx
          rw [hun] at hx
          obtain ⟨ms3, rfl⟩ := doMachineOp_mem hx
          have : p ≠ q.bv := fun e => hp _ (by rw [e]; exact hk)
          show Function.update σ.kheap q.bv _ p = σ.kheap p
          rw [Function.update_of_ne this]
        · show ((), _) ∈ (Fl4Spec.unmapPage (Z := Unit) .x64SmallPage asid.bv vaddr.bv pp.bv σ).1
          rw [hun]; exact hσ''
    | Large =>
      refine WP.spec_bind (lookup_pd_slot_rel s σ hPt hPP hr1 vaddr) ?_
      rintro r2 ⟨hsp, hsl, hse⟩
      cases r2 with
      | Err lf =>
        obtain ⟨n, rfl⟩ := hse _ rfl
        exact hskip (unmapPage_l_noSlot hf hsp)
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
          refine hskip (unmapPage_l_other hf hsp hg ?_)
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
          | invalidPDE => intro; rfl
          | pageTablePDE _ _ _ => intro h; exact absurd hp0 h.1
          | largePagePDE _ _ _ => intro h; exact absurd hp0 h.1
        rw [if_neg hp0]
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        rw [P_PS_eq]
        apply ok_bind_spec
        apply ok_bind_spec
        by_cases hps : (L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) = 0#u64
        · rw [if_pos hps]
          refine hskip (unmapPage_l_other hf hsp hg ?_)
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
          | invalidPDE => intro; rfl
          | pageTablePDE _ _ _ => intro; rfl
          | largePagePDE _ _ _ => intro h; exact absurd hps h.2.1
        rw [if_neg hps]
        simp only [vspace.frame_base, bind_ok]
        obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) = .largePagePDE fb fa fr := by
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
          | invalidPDE => intro h; exact absurd hp0 h
          | pageTablePDE _ _ _ => intro h; exact absurd ((eS_iff _).1 (by simpa using hps)) h.2.1
          | largePagePDE a b c => intro; exact ⟨a, b, c, rfl⟩
        rw [hfx] at hfe2 hg
        have hfb : (lA (L.mem s (peA q (vIdx vaddr 21)))).bv = fb := hfe2.2.2.1
        by_cases hadr : ((L.mem s (peA q (vIdx vaddr 21)) &&& 4503599625273344#u64) !=
            core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
        · rw [if_pos hadr]
          refine hskip (unmapPage_l_other hf hsp hg ?_)
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
          rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
          exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
        rw [if_neg hadr]
        have hadrE : lA (L.mem s (peA q (vIdx vaddr 21))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
          Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
        have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPDE (.largePagePDE fb fa fr)) = true := by
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
          rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
        set σs := updK σ q.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) .invalidPDE)))
          with hσs
        have hstore : Fl4Spec.storePde (Z := Unit) (peA q (vIdx vaddr 21)).bv .invalidPDE σ = ({((), σs)}, False) := by
          rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePde_at hqa hk hj _
        have hun := unmapPage_l_match hf hsp hg hc hstore
        rw [L.write_eq]
        apply ok_bind_spec
        have hea : Aligned (peA q (vIdx vaddr 21)) := by
          show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
        set s1 := L.wr s (peA q (vIdx vaddr 21)) 0#u64 with hs1
        have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
          hPt.upd_l2 hPP hq hk hj 0#u64 .invalidPDE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
            (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
        have hW : WritesIn st s s1 (PdW L2) :=
          ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
            (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
        have hSs := hH.pdStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
        have hWA : ∀ b, PdW L2 b → PtWAll L4 L3 L2 L1 b := by
          rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩
        have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
        have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
        have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
        have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
          rw [hW.1]
          refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
          obtain ⟨g, hg', -⟩ := hR.pool p hp
          have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
          simp [hσs, updK, this]
        refine WP.spec_bind (hH.flushPg s1 a σs asid vaddr hSs) ?_
        rintro a1 ⟨σ', hσ', hS'⟩
        have hσ'' := hσ'
        obtain ⟨ms, rfl⟩ := doMachineOp_mem hσ'
        refine (WP.spec_ok _).2 ⟨?_, ?_, _, ?_, ⟨hS', Vs.StateRel.ms hSts ms, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
          ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _⟩
        · show ¬ (Fl4Spec.unmapPage (Z := Unit) .x64LargePage asid.bv vaddr.bv pp.bv σ).2
          rw [hun]; exact hH.flushPgOK _ _ _
        · intro x σ'' hx p hp
          change (x, σ'') ∈ (Fl4Spec.unmapPage (Z := Unit) .x64LargePage asid.bv vaddr.bv pp.bv σ).1 at hx
          rw [hun] at hx
          obtain ⟨ms3, rfl⟩ := doMachineOp_mem hx
          have : p ≠ q.bv := fun e => hp _ (by rw [e]; exact hk)
          show Function.update σ.kheap q.bv _ p = σ.kheap p
          rw [Function.update_of_ne this]
        · show ((), _) ∈ (Fl4Spec.unmapPage (Z := Unit) .x64LargePage asid.bv vaddr.bv pp.bv σ).1
          rw [hun]; exact hσ''
    | Huge =>
      refine WP.spec_bind (lookup_pdpt_slot_rel s σ hPt hPP hr1 vaddr) ?_
      rintro r2 ⟨hsp, hsl, hse⟩
      cases r2 with
      | Err lf =>
        obtain ⟨n, rfl⟩ := hse _ rfl
        exact hskip (unmapPage_h_noSlot hf hsp)
      | Ok x =>
        obtain ⟨q, hq, rfl⟩ := hsl _ rfl
        obtain ⟨f, hk, hf2⟩ := hPt.l3 q hq
        have hqa := hPP q (Or.inr (Or.inl hq))
        have hj := vIdx_lt vaddr 30
        have hfe2 := hf2 _ hj
        have hg : Fl4Spec.getPdpte (Z := Unit) (peA q (vIdx vaddr 30)).bv σ =
            ({(f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv), σ)}, False) := by
          rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPdpte_at hqa hk hj
        dsimp only
        rw [L.read_eq]
        apply ok_bind_spec
        rw [P_PRESENT_eq]
        apply ok_bind_spec
        unfold lift
        apply ok_bind_spec
        by_cases hp0 : (L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) = 0#u64
        · rw [if_pos hp0]
          refine hskip (unmapPage_h_other hf hsp hg ?_)
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
          | invalidPDPTE => intro; rfl
          | pageDirectoryPDPTE _ _ _ => intro h; exact absurd hp0 h.1
          | hugePagePDPTE _ _ _ => intro h; exact absurd hp0 h.1
        rw [if_neg hp0]
        simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
        rw [P_PS_eq]
        apply ok_bind_spec
        apply ok_bind_spec
        by_cases hps : (L.mem s (peA q (vIdx vaddr 30)) &&& 128#u64) = 0#u64
        · rw [if_pos hps]
          refine hskip (unmapPage_h_other hf hsp hg ?_)
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
          | invalidPDPTE => intro; rfl
          | pageDirectoryPDPTE _ _ _ => intro; rfl
          | hugePagePDPTE _ _ _ => intro h; exact absurd hps h.2.1
        rw [if_neg hps]
        simp only [vspace.frame_base, bind_ok]
        obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) = .hugePagePDPTE fb fa fr := by
          revert hfe2
          cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
          | invalidPDPTE => intro h; exact absurd hp0 h
          | pageDirectoryPDPTE _ _ _ => intro h; exact absurd ((eS_iff _).1 (by simpa using hps)) h.2.1
          | hugePagePDPTE a b c => intro; exact ⟨a, b, c, rfl⟩
        rw [hfx] at hfe2 hg
        have hfb : (hA (L.mem s (peA q (vIdx vaddr 30)))).bv = fb := hfe2.2.2.1
        by_cases hadr : ((L.mem s (peA q (vIdx vaddr 30)) &&& 4503598553628672#u64) !=
            core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
        · rw [if_pos hadr]
          refine hskip (unmapPage_h_other hf hsp hg ?_)
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
          rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
          exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
        rw [if_neg hadr]
        have hadrE : hA (L.mem s (peA q (vIdx vaddr 30))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
          Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
        have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPDPTE (.hugePagePDPTE fb fa fr)) = true := by
          show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
          rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
        set σs := updK σ q.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) .invalidPDPTE)))
          with hσs
        have hstore : Fl4Spec.storePdpte (Z := Unit) (peA q (vIdx vaddr 30)).bv .invalidPDPTE σ = ({((), σs)}, False) := by
          rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePdpte_at hqa hk hj _
        have hun := unmapPage_h_match hf hsp hg hc hstore
        rw [L.write_eq]
        apply ok_bind_spec
        have hea : Aligned (peA q (vIdx vaddr 30)) := by
          show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
        set s1 := L.wr s (peA q (vIdx vaddr 30)) 0#u64 with hs1
        have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
          hPt.upd_l3 hPP hq hk hj 0#u64 .invalidPDPTE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
            (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
        have hW : WritesIn st s s1 (PdptW L3) :=
          ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
            (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
        have hSs := hH.pdptStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
        have hWA : ∀ b, PdptW L3 b → PtWAll L4 L3 L2 L1 b := by
          rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inl hp), i, hi, hb⟩
        have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
        have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
        have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
        have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
          rw [hW.1]
          refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
          obtain ⟨g, hg', -⟩ := hR.pool p hp
          have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
          simp [hσs, updK, this]
        refine WP.spec_bind (hH.flushPg s1 a σs asid vaddr hSs) ?_
        rintro a1 ⟨σ', hσ', hS'⟩
        have hσ'' := hσ'
        obtain ⟨ms, rfl⟩ := doMachineOp_mem hσ'
        refine (WP.spec_ok _).2 ⟨?_, ?_, _, ?_, ⟨hS', Vs.StateRel.ms hSts ms, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
          ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _⟩
        · show ¬ (Fl4Spec.unmapPage (Z := Unit) .x64HugePage asid.bv vaddr.bv pp.bv σ).2
          rw [hun]; exact hH.flushPgOK _ _ _
        · intro x σ'' hx p hp
          change (x, σ'') ∈ (Fl4Spec.unmapPage (Z := Unit) .x64HugePage asid.bv vaddr.bv pp.bv σ).1 at hx
          rw [hun] at hx
          obtain ⟨ms3, rfl⟩ := doMachineOp_mem hx
          have : p ≠ q.bv := fun e => hp _ (by rw [e]; exact hk)
          show Function.update σ.kheap q.bv _ p = σ.kheap p
          rw [Function.update_of_ne this]
        · show ((), _) ∈ (Fl4Spec.unmapPage (Z := Unit) .x64HugePage asid.bv vaddr.bv pp.bv σ).1
          rw [hun]; exact hσ''

theorem decodeUnmap_eq {lbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType lbl = .archInvocationLabel .x64PageUnmap)
    (args : List Fl4Spec.Data) (cte : Fl4Spec.CslotPtr) (dev : Bool) (p : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights)
    (mt : Fl4Spec.VMMapType) (sz : Fl4Spec.VMPageSize) (ma : Option (Fl4Spec.Asid × Fl4Spec.VSpaceRef))
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (σ : Fl4Spec.State Unit) :
    ExceptT.run (Fl4Spec.decodePageInvocation (Z := Unit) lbl args cte (.pageCap dev p R mt sz ma) ex) σ =
      ({(.ok (.invokePage (.pageUnmap (.pageCap dev p R mt sz ma) cte)), σ)}, False) := by
  unfold Fl4Spec.decodePageInvocation
  dsimp only
  rw [if_neg (by rw [hl]; simp), if_pos hl]
  rfl

theorem setCnodeSlot_self {σ : Fl4Spec.State Unit} {pc : Fl4Spec.ObjRef} {r : Nat} {cs : Fl4Spec.CnodeContents}
    {idx : List Bool} {c : Fl4Spec.Cap} (hk : σ.kheap pc = some (.cnode r cs)) (hc : cs idx = some c) :
    setCnodeSlot σ pc r cs idx c = σ := by
  have h1 : Function.update cs idx (some c) = cs := by rw [Function.update_eq_self_iff]; exact hc.symm
  rw [setCnodeSlot, h1]
  exact updK_self hk

/-- The spec's cap of a decoded frame (any size). -/
def frameACapG (f : vspace.FrameCap) : Fl4Spec.ArchCap :=
  .pageCap f.is_device f.ptr.bv (vmRightsOf f.rights) (if f.mapped then .vmVSpaceMap else .vmNoMap) (frameSizeOf f.size)
    (if f.mapped then some (f.asid.bv, f.vaddr.bv) else none)

/-- **Frame `Unmap` refines l4v** (decode, `Restart`, `perform_page_invocation`). -/
theorem frame_unmap_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPI : PoolsIn P L4 (L.mem s)) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (frameCapOf f))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageUnmap)
    (length buf : U64) (call : Bool) (ex : Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (xs : Fl4Spec.CapRef) (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.decode_frame st ar s a fl4_abi.label.X86PageUnmap length (cslotAddr (pc.bv, idx)) (frameCapOf f) call buf ex
      ⦃ res => res.1 = .Ok () ∧ ∃ iv σ',
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx) (frameACapG f) vcs) σ =
          ({(.ok iv, σ)}, False) ∧
        MapSpec σ iv σ' ∧ UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf f) ∧ KFoot σ σ' ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  rw [show Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx)
      (frameACapG ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) vcs =
    Fl4Spec.decodePageInvocation slbl args (pc.bv, idx) (frameACapG ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) vcs from rfl]
  unfold frameACapG
  dsimp only
  rw [decodeUnmap_eq hl]
  unfold vspace.decode_frame
  have hne : ¬ fl4_abi.label.X86PageUnmap = fl4_abi.label.X86PageMap := by
    unfold fl4_abi.label.X86PageUnmap fl4_abi.label.X86PageMap; decide
  have hneEpt : ¬ fl4_abi.label.X86PageUnmap = fl4_abi.label.X86PageMapEPT := by
    unfold fl4_abi.label.X86PageUnmap fl4_abi.label.X86PageMapEPT; decide
  simp only [frameCapOf, vspace.as_frame, bind_ok, hne, hneEpt, ↓reduceIte]
  have hfcv : CapValid th (frameCapOf ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩) :=
    hSV.cnode pc r hpc (blVal 0 idx) (hidx ▸ blVal_lt idx) _ (by rw [show slotAddr pc.bv (BitVec.ofNat 64 (blVal 0 idx)) = cslotAddr (pc.bv, idx) from (slotAddr_ofBl pc idx).symm]; exact hcx)
  obtain ⟨cs, hkc, hwf, hsl⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap)
      (frameSizeOf sz) (if mp then some (fa.bv, fv.bv) else none))) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .Frame ptr sz rt dev mp false fa fv := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa [frameCapOf] using h2 : capability.Cap.Frame ptr sz rt dev mp false fa fv = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
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
  set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmNoMap (frameSizeOf sz) none) with hnc
  have hca : CapRel (.Frame ptr sz rt dev false false 0#u64 0#u64) nc := ⟨hfw, rfl⟩
  have hew : EncWf (.Frame ptr sz rt dev false false 0#u64 0#u64) := ⟨hfe.1, hfe.2.1, by decide, by decide⟩
  have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
  -- the final `set_cap`, from a state `s4`/`σ4` with the CNode unchanged
  have fin_cap : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit), UR st th P L4 L3 L2 L1 SR s4 a4 σ4 →
      σ4.kheap pc.bv = some (.cnode r cs) → L.ksb s4 = L.ksb s →
      obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s4 (.Frame ptr sz rt dev false false 0#u64 0#u64) ⦃ s5 =>
        UR st th P L4 L3 L2 L1 SR s5 a4 (setCnodeSlot σ4 pc.bv r cs idx nc) ∧
        SlotFoot th (L.mem s4) (L.mem s5) (cslotAddr (pc.bv, idx)) ∧
        capV (L.mem s5) (cslotAddr (pc.bv, idx)) = .Frame ptr sz rt dev false false 0#u64 0#u64 ⦄ := by
    rintro s4 a4 σ4 ⟨hS4, hSt4, hSV4, hR4, hPt4⟩ hkc4 hks4
    refine WP.spec_mono (WP.spec_and (set_cap_refines th s4 σ4 hSt4 hSV4 hPl hpc hidx _ _ hca (by exact hfcv) hew)
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
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hcs ⊢
    refine WP.spec_bind (fin_cap s1 a σ1 ⟨hS1, hSt1, hSV1, hR1, hPt1⟩ hkc1 hk1) ?_
    rintro s5 ⟨hU5, hF5, hcv5⟩
    rw [setCnodeSlot_self hkc1 hcs] at hU5
    refine (WP.spec_ok _).2 ⟨rfl, _, σ1, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans hF5,
      by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; first | exact h | exact h.2 | exact ⟨fun e => absurd e (by decide), h.2⟩⟩, KFoot.sts hkt' _⟩
    unfold MapSpec
    dsimp only
    rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt'), performUnmap_none]
    exact ⟨rfl, id⟩
  · have hfa := hfm rfl
    have hfa' : (fa != 0#u64) = true := by simp [hfa]
    simp only [↓reduceIte, hfa'] at hcs ⊢
    -- `unmap_page`, with the footprint carried in `SR`
    let SR' : S → A → Fl4Spec.State Unit → Prop := fun s' a' σ' =>
      SR s' a' σ' ∧ SlotFoot th (L.mem s1) (L.mem s') (cslotAddr (pc.bv, idx)) ∧ KFoot σ1 σ'
    have hPOw : ∀ (W : U64 → Prop), (∀ b, W b → PtWAll L4 L3 L2 L1 b) → ∀ b, W b → OutsideObjects th b :=
      fun W hW b hb => hPO b (hW b hb)
    have hH' : VsUnmapPageHyps st A ar L3 L2 L1 SR' :=
      { ptStable := fun s' s'' a' σ' σ'' ⟨h1, h2, h3⟩ hw hst => ⟨hH.ptStable _ _ _ _ _ h1 hw hst,
          h2.trans (SlotFoot.of_writes hPl hw (hPOw _ (fun b ⟨q, hq, i, hi, e⟩ =>
            ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩)) _),
          h3.trans (by obtain ⟨p, f, f', hk, rfl⟩ := hst; exact KFoot.arch hk _)⟩
        pdStable := fun s' s'' a' σ' σ'' ⟨h1, h2, h3⟩ hw hst => ⟨hH.pdStable _ _ _ _ _ h1 hw hst,
          h2.trans (SlotFoot.of_writes hPl hw (hPOw _ (fun b ⟨q, hq, i, hi, e⟩ =>
            ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)) _),
          h3.trans (by obtain ⟨p, f, f', hk, rfl⟩ := hst; exact KFoot.arch hk _)⟩
        pdptStable := fun s' s'' a' σ' σ'' ⟨h1, h2, h3⟩ hw hst => ⟨hH.pdptStable _ _ _ _ _ h1 hw hst,
          h2.trans (SlotFoot.of_writes hPl hw (hPOw _ (fun b ⟨q, hq, i, hi, e⟩ =>
            ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)) _),
          h3.trans (by obtain ⟨p, f, f', hk, rfl⟩ := hst; exact KFoot.arch hk _)⟩
        flushPgOK := hH.flushPgOK
        flushPg := fun s' a' σ' asid vaddr ⟨h1, h2, h3⟩ => WP.spec_mono (hH.flushPg s' a' σ' asid vaddr h1)
          (fun a'' ⟨σ'', hm, hS''⟩ => ⟨σ'', hm, hS'', h2, h3.trans (by
            obtain ⟨ms, rfl⟩ := doMachineOp_mem hm; exact KFoot.ms _ ms)⟩) }
    refine WP.spec_bind (unmap_page_rel hH' s1 a σ1 hPl hPP hPS (hk1 ▸ hVP) (hk1 ▸ hPV) hPI1
      ⟨⟨hS1, SlotFoot.refl _ _, KFoot.refl _⟩, hSt1, hSV1, hR1, hPt1⟩ sz fa fv ptr hfa) ?_
    rintro ⟨s3, a3⟩ ⟨hnu, hall, σu, hu, ⟨⟨hS3, hF3, hK3⟩, hU3⟩, hk3⟩
    replace hU3 : UR st th P L4 L3 L2 L1 SR s3 a3 σu := ⟨hS3, hU3⟩
    have hall' : ∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPage (Z := Unit) (frameSizeOf sz) fa.bv fv.bv ptr.bv σ1).1 →
        σ'.kheap pc.bv = σ1.kheap pc.bv := fun x σ' hx =>
      hall x σ' hx pc.bv (fun ao h => by rw [hkc1] at h; cases h)
    show (obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s3 (.Frame ptr sz rt dev false false 0#u64 0#u64) >>= fun s5 =>
      ok (core.result.Result.Ok (), s5, a3)) ⦃ _ ⦄
    refine WP.spec_bind (fin_cap s3 a3 σu hU3 ((hall' _ _ hu).trans hkc1) (hk3.trans hk1)) ?_
    rintro s5 ⟨hU5, hF5, hcv5⟩
    refine (WP.spec_ok _).2 ⟨rfl, _, _, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans (hF3.trans hF5),
      by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; first | exact h | exact h.2 | exact ⟨fun e => absurd e (by decide), h.2⟩⟩,
      (KFoot.sts hkt' _).trans (hK3.trans (KFoot.cnode ((hall' _ _ hu).trans hkc1) hwf idx nc))⟩
    unfold MapSpec
    dsimp only
    rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
    exact performUnmap_mem hnu hall' hu hkc1 hwf hidx hcs

end

end

end Fl4Proofs.P3.Vs
