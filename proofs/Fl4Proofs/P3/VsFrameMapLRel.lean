/-
P3 (DESIGN.md §9), VSpace: **Frame `Map` for large (2M) and huge (1G)
pages refines l4v**: `frame_map_large_rel`, `frame_map_huge_rel`, as
`frame_map_rel` for 4K pages. FL4's `page_entry_slot` fails with
`DeleteFirst` on a present table entry (PS clear), as l4v's
`ensure_safe_mapping` (`page_entry_slot_large`/`_huge`); the entry is built
by `make_user_page` with `large` and written at the PD / PDPT level
(`write_mapping_rel_pd`/`_pdpt`). Invariant hypotheses as for 4K pages,
with the frame's physical address 2M- / 1G-aligned.
-/
import Fl4Proofs.P3.VsFrameWriteL
import Fl4Proofs.P3.VsPdptMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

section Spec
open Fl4Spec

theorem decodeMapL_badVs {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (ma : Option (Asid × VSpaceRef)) (vc : Cap) (xsl : CslotPtr) (ex : List (Cap × CslotPtr))
    (hvc : ∀ pm asid, vc ≠ .archObjectCap (.pml4Cap pm (some asid))) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64LargePage ma) ((vc, xsl) :: ex)) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  split
  · rename_i pm asid h
    exact absurd h (hvc pm asid)
  · exact runE_bind_err (runE_throw _ σ)

end Spec

theorem al21 (v : U64) : (v &&& 2097151#u64) = 0#u64 ↔ Fl4Spec.isAligned v.bv 21 := by
  unfold Fl4Spec.isAligned
  have : (v &&& 2097151#u64).val = v.val % 2097152 := by
    rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod v.val 21
  constructor
  · intro h; rw [h] at this; exact Nat.dvd_of_mod_eq_zero (by simpa using this.symm)
  · intro h; apply UScalar.eq_of_val_eq; rw [this, Nat.mod_eq_zero_of_dvd (show 2097152 ∣ v.val from h)]; rfl

theorem addL (v : U64) : (core.num.U64.wrapping_add v 2097152#u64).bv = v.bv + 2097152 := by
  rw [core.num.U64.wrapping_add_bv_eq]; rfl

theorem check_vspace_pml4L {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (p asid : U64) (h0 : asid ≠ 0#u64) (dev : Bool) (pp : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights)
    (va rm at' : Fl4Spec.Data) (cte : Fl4Spec.CslotPtr) :
    vspace.check_vspace st s (.Pml4 p true asid) ⦃ r =>
      (r = .Ok (p, asid) ∧
        ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) ∨
      (∃ e e', r = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (mapTailL p.bv asid.bv dev pp R va rm at' cte) σ = ({(.error e', σ)}, False)) ⦄ := by
  unfold vspace.check_vspace
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0) (find_vspace_for_asid_err s asid)) ?_
  rintro r ⟨hf, he⟩
  cases r with
  | Ok r1 =>
    by_cases hr : r1 = p
    · subst hr
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 (Or.inl ⟨rfl, hf⟩)
    · have : (r1 != p) = true := by simp [hr]
      simp only [this, ↓reduceIte, error.invalid_cap]
      exact (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inr ⟨1#u64, rfl, rfl⟩, mapTailL_wrongVs hf (fun h => hr (eq_of_bv h))⟩)
  | Err lf =>
    obtain rfl := he lf rfl
    refine (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inl (show SysErrRel (.Sys (.FailedLookup false .InvalidRoot))
      (.failedLookup false .invalidRoot) by simp [SysErrRel, LookupFaultRel]), mapTailL_noVs hf⟩)

theorem page_entry_slot_large {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.page_entry_slot st s pm vaddr .Large ⦃ r =>
      (∀ x, r = .Ok x → ExceptT.run (Fl4Spec.lookupPdSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok x.bv, σ)}, False) ∧
        ∃ q ∈ L2, x = peA q (vIdx vaddr 21) ∧ ∃ d : Fl4Spec.PDE, Fl4Spec.getPde (Z := Unit) x.bv σ = ({(d, σ)}, False) ∧
          (d = .invalidPDE ∨ ∃ a b c, d = .largePagePDE a b c)) ∧
      (∀ e, r = .Err e → (∃ n, e = .Sys (.FailedLookup false (.MissingCapability n)) ∧
        ExceptT.run (Fl4Spec.lookupPdSlot (Z := Unit) pm.bv vaddr.bv) σ =
          ({(.error (.missingCapability n.val), σ)}, False)) ∨
        (e = .Sys .DeleteFirst ∧ ∃ y, ExceptT.run (Fl4Spec.lookupPdSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok y, σ)}, False) ∧
          ∃ a b c, Fl4Spec.getPde (Z := Unit) y σ = ({(.pageTablePDE a b c, σ)}, False))) ⦄ := by
  unfold vspace.page_entry_slot
  refine WP.spec_bind (lookup_pd_slot_rel s σ hR hP hpm vaddr) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => by cases he; exact Or.inl ⟨n, rfl, hsp⟩⟩
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    obtain ⟨f, hk, hf2⟩ := hR.l2 q hq
    have hqa := hP q (Or.inr (Or.inr (Or.inl hq)))
    have hj := vIdx_lt vaddr 21
    have hfe2 := hf2 _ hj
    have hg : Fl4Spec.getPde (Z := Unit) (peA q (vIdx vaddr 21)).bv σ =
        ({(f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv), σ)}, False) := by
      rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPde_at hqa hk hj
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    rw [L.read_eq]
    apply ok_bind_spec
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    by_cases hp0 : (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64
    · have : ((L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) != 0#u64) = false := by simp [hp0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨fun y hy => ?_, fun e he => by cases he⟩
      cases hy
      refine ⟨hsp, q, hq, rfl, _, hg, Or.inl ?_⟩
      revert hfe2
      cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
      | invalidPDE => intro; rfl
      | pageTablePDE _ _ _ => intro h; exact absurd hp0 h.1
      | largePagePDE _ _ _ => intro h; exact absurd hp0 h.1
    · have : ((L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) != 0#u64) = true := by simp [hp0]
      simp only [this, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hps : (L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) = 0#u64
      · simp only [hps, ↓reduceIte]
        refine (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => ?_⟩
        cases he
        refine Or.inr ⟨rfl, _, hsp, ?_⟩
        revert hfe2 hg
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro h; exact absurd hp0 h
        | pageTablePDE a b c => intro _ hg; exact ⟨a, b, c, hg⟩
        | largePagePDE _ _ _ => intro h; exact absurd hps h.2.1
      · simp only [hps, ↓reduceIte]
        refine (WP.spec_ok _).2 ⟨fun y hy => ?_, fun e he => by cases he⟩
        cases hy
        refine ⟨hsp, q, hq, rfl, _, hg, Or.inr ?_⟩
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro h; exact absurd hp0 h
        | pageTablePDE _ _ _ => intro h; exact absurd hps (by simpa [eS] using h.2.1)
        | largePagePDE a b c => intro; exact ⟨a, b, c, rfl⟩

/-- The spec's footprint of a PD store and its flush. -/
theorem kfoot_store_flush_pd {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L2) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePde (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : KFoot σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l2 q hq
  have hpa := hP q (Or.inr (Or.inr (Or.inl hq)))
  have hst : Fl4Spec.storePde (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePde_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (KFoot.arch hk _).trans (KFoot.ms _ ms)

/-- The spec's footprint of a PDPT store and its flush. -/
theorem kfoot_store_flush_pdpt {L4 L3 L2 L1 : Set U64} {m : U64 → U64} {σ2 σ' : Fl4Spec.State Unit}
    (hP : PtPlaced L4 L3 L2 L1) (hR : PtRel L4 L3 L2 L1 m σ2) {q : U64} (hq : q ∈ L3) {i : U64} (hi : i.val < 512)
    (pte : Fl4Spec.PDPTE) (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid)
    (hm : ((), σ') ∈ ((Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid) σ2).1) : KFoot σ2 σ' := by
  obtain ⟨f, hk, -⟩ := hR.l3 q hq
  have hpa := hP q (Or.inr (Or.inl hq))
  have hst : Fl4Spec.storePdpte (Z := Unit) (peA q i).bv pte σ2 =
      ({((), updK σ2 q.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte))))}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePdpte_at hpa hk hi pte
  rw [nd_bind_one hst] at hm
  obtain ⟨ms, rfl⟩ := doMachineOp_mem hm
  exact (KFoot.arch hk _).trans (KFoot.ms _ ms)

set_option hygiene false in
/-- The common part of both cases: from `check_vspace` on. -/
macro "map_tail_L" : tactic => `(tactic| (
  refine WP.spec_bind (check_vspace_pml4L s σ hR p1 as1 has1 dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) ?_
  rintro r1 (⟨rfl, hf⟩ | ⟨e, e', rfl, he, hte⟩)
  rotate_left
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp only [Bind.bind, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, Or.inl he, hdec.trans hte, rfl, rfl⟩)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 2097152#u64 1#u64 = 2097151#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 2097151#u64) = 0#u64
  · have : ((a0 &&& 2097151#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (page_entry_slot_large s σ hPt hPP hp1 a0) ?_
    rintro r3 ⟨hsl, hse⟩
    cases r3 with
    | Err lf =>
      rcases hse _ rfl with ⟨n, rfl, hsp⟩ | ⟨rfl, y, hsp, a', b', c', hg⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
          Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
          hdec.trans (mapTailL_noSlot hf ((al21 a0).1 hal) hsp), rfl, rfl⟩)
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys .DeleteFirst) .deleteFirst from trivial)),
          hdec.trans (mapTailL_used hf ((al21 a0).1 hal) hsp hg), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl, d, hgd, hd⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      refine WP.spec_bind (make_user_page_large s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pde_of_make_large (L1 := L1) (vmOk_of hm1 hm3) hpa he
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
      refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hPt hS hcur hkt' htcb hact hrun)
        (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
      rintro s1 ⟨⟨hSt1, hSV1, hR1, hPt1, hS1, hk1⟩, hSS1⟩
      set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
      have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by
        rw [hσ1, stsAct_kheap]; simp [updK, hpct, hkc]
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64LargePage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Large rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Large rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
        (WP.spec_and (set_cap_spec (L := L) _ s1 _) (set_cap_foot hPl hxsl s1 _ hew))) ?_
      rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
      have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx nc := by
        rw [setCap_cnode nc hkc1 hwf hidx] at hsc
        have := congrArg Prod.fst hsc
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      subst hσ2
      have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
      have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
      have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
      have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s1 b := by
        intro b hb
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
        exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hpools : ∀ q ∈ P, (setCnodeSlot σ1 pc.bv r cs idx nc).kheap q.bv = σ1.kheap q.bv := by
        intro q hq
        obtain ⟨g, hg, -⟩ := hR1.pool q hq
        have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
      have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
        rw [hks2]; rw [hk1] at hR1
        exact hR1.frame hfrV rfl hpools
      have hWs : WritesIn st s1 s2 (SlotW th) := by
        refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
        exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
      have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
        refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
        · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
          exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        · obtain ⟨ao, hao⟩ := hPt1.arch hq
          have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [setCnodeSlot, this]
      have hMR : MapRelA st th P L4 L3 L2 L1 SR s2 a (setCnodeSlot σ1 pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel_pd (hH.map.ext hPl hPS) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 21) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 21)) := hPO _ ⟨q, Or.inr (Or.inr (Or.inl hq)), _, vIdx_lt a0 21, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTailL_ok hf ((al21 a0).1 hal) hsp hgd hd), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_⟩)
      · unfold MapSpec mapInvL
        dsimp only
        rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
        exact performLMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2⟩⟩
      · exact (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush_pd hPP hPt2 hq (vIdx_lt a0 21) _ _ _ hm'))
  · have : ((a0 &&& 2097151#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTailL_unaligned hf (fun h => hal ((al21 a0).2 h))), rfl, rfl⟩)))

/-- **Large Frame `Map` refines l4v** (as `frame_map_rel`). -/
theorem frame_map_large_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Large) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs (pc.bv, idx)
          (frameACapG f) ((vc', xsl) :: rest)) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs
          (pc.bv, idx) (frameACapG f) ((vc', xsl) :: rest)) σ = ({(.ok iv, σ)}, False) ∧
        MapSpec σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf f) ∧ KFoot σ σ') ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  simp only at hsz hfm hpa ⊢
  subst hsz
  rw [show ∀ args' ex', Fl4Spec.archDecodeInvocation (Z := Unit) slbl args' xs (pc.bv, idx)
      (frameACapG ⟨ptr, .Large, rt, dev, mp, ep, fa, fv⟩) ex' =
    Fl4Spec.decodePageInvocation slbl args' (pc.bv, idx) (.pageCap dev ptr.bv (vmRightsOf rt)
      (if mp then .vmVSpaceMap else .vmNoMap) .x64LargePage (if mp then some (fa.bv, fv.bv) else none)) ex' from
    fun _ _ => rfl]
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64LargePage
      (if mp then some (fa.bv, fv.bv) else none)) ((vc', xsl) :: rest)) σ = D
  unfold vspace.decode_page_map
  rw [hct]
  apply ok_bind_spec
  rw [hex]
  apply ok_bind_spec
  dsimp only
  by_cases h3 : length >= 3#u64
  · rw [if_pos h3]
    have h3' : 3 ≤ args.length := by
      have : 3 ≤ length.val := by scalar_tac
      omega
    obtain ⟨a0, a1, a2, ar', rfl⟩ : ∃ a0 a1 a2 r', args = a0 :: a1 :: a2 :: r' := by
      match args, h3' with
      | a0 :: a1 :: a2 :: r', _ => exact ⟨_, _, _, _, rfl⟩
    rw [hargs 0#u64 a0 (by simp)]; apply ok_bind_spec
    rw [hargs 1#u64 a1 (by simp)]; apply ok_bind_spec
    rw [hargs 2#u64 a2 (by simp)]; apply ok_bind_spec
    unfold lift; apply ok_bind_spec; apply ok_bind_spec; apply ok_bind_spec
    rw [slot_cap_eq, hcx]; apply ok_bind_spec
    by_cases hvp : ∃ p asid, vc = .Pml4 p true asid
    · obtain ⟨p1, as1, rfl⟩ := hvp
      obtain ⟨hp1, has1, has2⟩ := hvc p1 as1 rfl
      have hvc' : vc' = .archObjectCap (.pml4Cap p1.bv (some as1.bv)) := by rw [← hvr.2]; rfl
      subst hvc'
      simp only [vspace.mapped_root, ↓reduceIte, bind_ok]
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte, capability.FrameSize.bits, bind_ok, shl21]
        simp only [List.map_cons, Bool.false_eq_true, ↓reduceIte] at hDec
        have hdec0 := decodeMapL_unmapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmNoMap p1.bv as1.bv xsl rest σ
        by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
        · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
            Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
        · by_cases hv2 : core.num.U64.wrapping_add a0 2097152#u64 > fl4_abi.consts.USER_TOP
          · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0]
            exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← addL]; exact (gt_top _).2 hv2))]; rfl)
          · simp only [hv1, hv2, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTailL p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
              rintro (h | h)
              · exact hv1 ((gt_top a0).1 h)
              · rw [← addL] at h; exact hv2 ((gt_top _).1 h)
            have hva : a0.val < 2 ^ 48 := by
              have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
              rw [gt_iff_val] at this
              have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
              omega
            map_tail_L
      · have hfa := hfm rfl
        have hfa' : (fa != 0#u64) = true := by simp [hfa]
        simp only [↓reduceIte, hfa', capability.FrameSize.bits, bind_ok, shl21]
        simp only [List.map_cons, ↓reduceIte] at hDec
        have hdec0 := decodeMapL_mapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv xsl rest σ
        by_cases hfa1 : fa = as1
        · have : (fa != as1) = false := by simp [hfa1]
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          by_cases hfv : fv = a0
          · have : (fv != a0) = false := by simp [hfv]
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTailL p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
                runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
            have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
            map_tail_L
          · have : (fv != a0) = true := by simp [hfv]
            simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
              runE_bind_ok (runE_whenE_false (by simp) _ σ)]
            exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
        · have : (fa != as1) = true := by simp [hfa1]
          simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)
    · have hmr : vspace.mapped_root vc = ok none := by
        cases vc <;> simp_all [vspace.mapped_root]
      rw [hmr]
      simp only [bind_ok, error.invalid_cap]
      have hbad : ∀ pm asid, vc' ≠ .archObjectCap (.pml4Cap pm (some asid)) := by
        intro pm asid h
        rw [← hvr.2] at h
        cases vc <;> simp_all [absCap]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, List.map_cons, List.map_cons, List.map_cons]
      exact decodeMapL_badVs hl _ _ _ _ _ _ _ _ _ _ _ _ _ hbad σ
  · rw [if_neg h3]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, Or.inl (Or.inl (show SysErrRel (.Sys .TruncatedMessage) .truncatedMessage from trivial)),
      hDec ▸ decodeMap_trunc hl _ _ _ _ _ _ _ _ _ ?_ σ, rfl, rfl⟩)
    have : length.val < 3 := by scalar_tac
    simp only [List.length_map]; omega


section Spec
open Fl4Spec

theorem decodeMapH_badVs {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64PageMap)
    (a0 a1 a2 : Data) (rest : List Data) (cte : CslotPtr) (dev : Bool) (p : ObjRef) (R : VMRights)
    (mt : VMMapType) (ma : Option (Asid × VSpaceRef)) (vc : Cap) (xsl : CslotPtr) (ex : List (Cap × CslotPtr))
    (hvc : ∀ pm asid, vc ≠ .archObjectCap (.pml4Cap pm (some asid))) (σ : State Unit) :
    ExceptT.run (decodePageInvocation (Z := Unit) lbl (a0 :: a1 :: a2 :: rest) cte
      (.pageCap dev p R mt .x64HugePage ma) ((vc, xsl) :: ex)) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
  unfold decodePageInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  split
  · rename_i pm asid h
    exact absurd h (hvc pm asid)
  · exact runE_bind_err (runE_throw _ σ)

end Spec

theorem al30 (v : U64) : (v &&& 1073741823#u64) = 0#u64 ↔ Fl4Spec.isAligned v.bv 30 := by
  unfold Fl4Spec.isAligned
  have : (v &&& 1073741823#u64).val = v.val % 1073741824 := by
    rw [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod v.val 30
  constructor
  · intro h; rw [h] at this; exact Nat.dvd_of_mod_eq_zero (by simpa using this.symm)
  · intro h; apply UScalar.eq_of_val_eq; rw [this, Nat.mod_eq_zero_of_dvd (show 1073741824 ∣ v.val from h)]; rfl

theorem addH (v : U64) : (core.num.U64.wrapping_add v 1073741824#u64).bv = v.bv + 1073741824 := by
  rw [core.num.U64.wrapping_add_bv_eq]; rfl

theorem check_vspace_pml4H {P : Set U64} (s : S) (σ : Fl4Spec.State Unit) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (p asid : U64) (h0 : asid ≠ 0#u64) (dev : Bool) (pp : Fl4Spec.ObjRef) (R : Fl4Spec.VMRights)
    (va rm at' : Fl4Spec.Data) (cte : Fl4Spec.CslotPtr) :
    vspace.check_vspace st s (.Pml4 p true asid) ⦃ r =>
      (r = .Ok (p, asid) ∧
        ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False)) ∨
      (∃ e e', r = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (mapTailH p.bv asid.bv dev pp R va rm at' cte) σ = ({(.error e', σ)}, False)) ⦄ := by
  unfold vspace.check_vspace
  simp only [↓reduceIte]
  refine WP.spec_bind (WP.spec_and (find_vspace_for_asid_rel s σ hR asid h0) (find_vspace_for_asid_err s asid)) ?_
  rintro r ⟨hf, he⟩
  cases r with
  | Ok r1 =>
    by_cases hr : r1 = p
    · subst hr
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 (Or.inl ⟨rfl, hf⟩)
    · have : (r1 != p) = true := by simp [hr]
      simp only [this, ↓reduceIte, error.invalid_cap]
      exact (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inr ⟨1#u64, rfl, rfl⟩, mapTailH_wrongVs hf (fun h => hr (eq_of_bv h))⟩)
  | Err lf =>
    obtain rfl := he lf rfl
    refine (WP.spec_ok _).2 (Or.inr ⟨_, _, rfl, Or.inl (show SysErrRel (.Sys (.FailedLookup false .InvalidRoot))
      (.failedLookup false .invalidRoot) by simp [SysErrRel, LookupFaultRel]), mapTailH_noVs hf⟩)

theorem page_entry_slot_huge {L4 L3 L2 L1 : Set U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) {pm : U64} (hpm : pm ∈ L4) (vaddr : U64) :
    vspace.page_entry_slot st s pm vaddr .Huge ⦃ r =>
      (∀ x, r = .Ok x → ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok x.bv, σ)}, False) ∧
        ∃ q ∈ L3, x = peA q (vIdx vaddr 30) ∧ ∃ d : Fl4Spec.PDPTE, Fl4Spec.getPdpte (Z := Unit) x.bv σ = ({(d, σ)}, False) ∧
          (d = .invalidPDPTE ∨ ∃ a b c, d = .hugePagePDPTE a b c)) ∧
      (∀ e, r = .Err e → (∃ n, e = .Sys (.FailedLookup false (.MissingCapability n)) ∧
        ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ =
          ({(.error (.missingCapability n.val), σ)}, False)) ∨
        (e = .Sys .DeleteFirst ∧ ∃ y, ExceptT.run (Fl4Spec.lookupPdptSlot (Z := Unit) pm.bv vaddr.bv) σ = ({(.ok y, σ)}, False) ∧
          ∃ a b c, Fl4Spec.getPdpte (Z := Unit) y σ = ({(.pageDirectoryPDPTE a b c, σ)}, False))) ⦄ := by
  unfold vspace.page_entry_slot
  refine WP.spec_bind (lookup_pdpt_slot_rel s σ hR hP hpm vaddr) ?_
  rintro r ⟨hsp, hsl, hse⟩
  cases r with
  | Err lf =>
    obtain ⟨n, rfl⟩ := hse _ rfl
    exact (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => by cases he; exact Or.inl ⟨n, rfl, hsp⟩⟩
  | Ok x =>
    obtain ⟨q, hq, rfl⟩ := hsl _ rfl
    obtain ⟨f, hk, hf2⟩ := hR.l3 q hq
    have hqa := hP q (Or.inr (Or.inl hq))
    have hj := vIdx_lt vaddr 30
    have hfe2 := hf2 _ hj
    have hg : Fl4Spec.getPdpte (Z := Unit) (peA q (vIdx vaddr 30)).bv σ =
        ({(f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv), σ)}, False) := by
      rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPdpte_at hqa hk hj
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    rw [L.read_eq]
    apply ok_bind_spec
    rw [P_PRESENT_eq]
    apply ok_bind_spec
    unfold lift
    apply ok_bind_spec
    by_cases hp0 : (L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) = 0#u64
    · have : ((L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) != 0#u64) = false := by simp [hp0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      refine (WP.spec_ok _).2 ⟨fun y hy => ?_, fun e he => by cases he⟩
      cases hy
      refine ⟨hsp, q, hq, rfl, _, hg, Or.inl ?_⟩
      revert hfe2
      cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
      | invalidPDPTE => intro; rfl
      | pageDirectoryPDPTE _ _ _ => intro h; exact absurd hp0 h.1
      | hugePagePDPTE _ _ _ => intro h; exact absurd hp0 h.1
    · have : ((L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) != 0#u64) = true := by simp [hp0]
      simp only [this, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hps : (L.mem s (peA q (vIdx vaddr 30)) &&& 128#u64) = 0#u64
      · simp only [hps, ↓reduceIte]
        refine (WP.spec_ok _).2 ⟨(fun y hy => by cases hy), fun e he => ?_⟩
        cases he
        refine Or.inr ⟨rfl, _, hsp, ?_⟩
        revert hfe2 hg
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
        | invalidPDPTE => intro h; exact absurd hp0 h
        | pageDirectoryPDPTE a b c => intro _ hg; exact ⟨a, b, c, hg⟩
        | hugePagePDPTE _ _ _ => intro h; exact absurd hps h.2.1
      · simp only [hps, ↓reduceIte]
        refine (WP.spec_ok _).2 ⟨fun y hy => ?_, fun e he => by cases he⟩
        cases hy
        refine ⟨hsp, q, hq, rfl, _, hg, Or.inr ?_⟩
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
        | invalidPDPTE => intro h; exact absurd hp0 h
        | pageDirectoryPDPTE _ _ _ => intro h; exact absurd hps (by simpa [eS] using h.2.1)
        | hugePagePDPTE a b c => intro; exact ⟨a, b, c, rfl⟩

set_option hygiene false in
/-- The common part of both cases: from `check_vspace` on. -/
macro "map_tail_H" : tactic => `(tactic| (
  refine WP.spec_bind (check_vspace_pml4H s σ hR p1 as1 has1 dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) ?_
  rintro r1 (⟨rfl, hf⟩ | ⟨e, e', rfl, he, hte⟩)
  rotate_left
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from]
    simp only [Bind.bind, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨e, e', rfl, Or.inl he, hdec.trans hte, rfl, rfl⟩)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, from_word_eq]
  obtain ⟨m, hm, hm1, hm3, hmv⟩ := vm_mask rt hfw (rightsW a1)
  rw [hm]
  apply ok_bind_spec
  rw [show core.num.U64.wrapping_sub 1073741824#u64 1#u64 = 1073741823#u64 from eq_of_bv (by rw [core.num.U64.wrapping_sub_bv_eq]; decide)]
  by_cases hal : (a0 &&& 1073741823#u64) = 0#u64
  · have : ((a0 &&& 1073741823#u64) != 0#u64) = false := by simp [hal]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (page_entry_slot_huge s σ hPt hPP hp1 a0) ?_
    rintro r3 ⟨hsl, hse⟩
    cases r3 with
    | Err lf =>
      rcases hse _ rfl with ⟨n, rfl, hsp⟩ | ⟨rfl, y, hsp, a', b', c', hg⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .failedLookup false (.missingCapability n.val), rfl,
          Or.inl (Or.inl (by simp [SysErrRel, LookupFaultRel])),
          hdec.trans (mapTailH_noSlot hf ((al30 a0).1 hal) hsp), rfl, rfl⟩)
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        simp only [Bind.bind, bind_ok]
        exact (WP.spec_ok _).2 (Or.inl ⟨_, .deleteFirst, rfl,
          Or.inl (Or.inl (show SysErrRel (.Sys .DeleteFirst) .deleteFirst from trivial)),
          hdec.trans (mapTailH_used hf ((al30 a0).1 hal) hsp hg), rfl, rfl⟩)
    | Ok sl =>
      obtain ⟨hsp, q, hq, rfl, d, hgd, hd⟩ := hsl _ rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, layout.paddr]
      refine WP.spec_bind (make_user_page_large s _ _ m) ?_
      rintro e ⟨xd, he⟩
      have hpte := pdpte_of_make_huge (L2 := L2) (vmOk_of hm1 hm3) hpa he
      simp only [paddr_bv, attr_defer, vm_eq (rightsW a1) a1 rfl hmv] at hpte
      have hkt' : σ.kheap ct.bv = some (.tcb xct) := by rw [hcur]; exact hkt
      refine WP.spec_bind (WP.spec_and (hH.restart s a σ ct xct hSt hSV hR hPt hS hcur hkt' htcb hact hrun)
        (set_thread_state_slots th hPl s ct sched.TS_RESTART htcb hact)) ?_
      rintro s1 ⟨⟨hSt1, hSV1, hR1, hPt1, hS1, hk1⟩, hSS1⟩
      set σ1 := stsAct (updK σ ct.bv (.tcb { xct with tcbState := .restart })) ct.bv with hσ1
      obtain ⟨cs, hkc, hwf, -⟩ := hSt.cnode pc r hpc
      have hpct : pc.bv ≠ ct.bv := kheap_ne hkc hkt' (fun _ h1 h2 => by subst h1; cases h2)
      have hkc1 : σ1.kheap pc.bv = some (.cnode r cs) := by
        rw [hσ1, stsAct_kheap]; simp [updK, hpct, hkc]
      set nc : Fl4Spec.Cap := .archObjectCap (.pageCap dev ptr.bv (vmRightsOf rt) .vmVSpaceMap .x64HugePage
        (some (as1.bv, a0.bv))) with hnc
      have hca : CapRel (.Frame ptr .Huge rt dev true false as1 a0) nc := ⟨hfw, rfl⟩
      have hew : EncWf (.Frame ptr .Huge rt dev true false as1 a0) := ⟨hfe.1, hfe.2.1, has2, hva⟩
      have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
        (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
      refine WP.spec_bind (WP.spec_and (set_cap_refines th s1 σ1 hSt1 hSV1 hPl hpc hidx _ _ hca (by exact hfcv) hew)
        (WP.spec_and (set_cap_spec (L := L) _ s1 _) (set_cap_foot hPl hxsl s1 _ hew))) ?_
      rintro s2 ⟨⟨σ2, hsc, hSt2, hSV2, -, -, -, hfr2⟩, hs2, hF2, hcv2⟩
      have hσ2 : σ2 = setCnodeSlot σ1 pc.bv r cs idx nc := by
        rw [setCap_cnode nc hkc1 hwf hidx] at hsc
        have := congrArg Prod.fst hsc
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      subst hσ2
      have hks2 : L.ksb s2 = L.ksb s := by rw [hs2]; simp [hk1]
      have hxs : IsSlotAt th pc (blVal 0 idx) := Or.inl ⟨r, hpc, hidx ▸ blVal_lt idx⟩
      have hx0 : cslotAddr (pc.bv, idx) = slotOf pc (blVal 0 idx) := slotAddr_ofBl pc idx
      have hfrV : ∀ b, VsWrite P (L.ksb s) b → L.mem s2 b = L.mem s1 b := by
        intro b hb
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hD b hb)
        exact hfr2 b (hb.aligned hVP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hpools : ∀ q ∈ P, (setCnodeSlot σ1 pc.bv r cs idx nc).kheap q.bv = σ1.kheap q.bv := by
        intro q hq
        obtain ⟨g, hg, -⟩ := hR1.pool q hq
        have : q.bv ≠ pc.bv := kheap_ne hg hkc1 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
      have hR2 : VsRel P (L.mem s2) (L.ksb s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
        rw [hks2]; rw [hk1] at hR1
        exact hR1.frame hfrV rfl hpools
      have hWs : WritesIn st s1 s2 (SlotW th) := by
        refine ⟨by rw [hs2]; simp, by rw [hs2]; simp, fun b hb hn => ?_⟩
        obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs hn
        exact hfr2 b hb (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      have hS2 := hH.capStable _ _ a _ _ hS1 hWs ⟨pc.bv, r, cs, idx, nc, hkc1, rfl⟩
      have hPt2 : PtRel L4 L3 L2 L1 (L.mem s2) (setCnodeSlot σ1 pc.bv r cs idx nc) := by
        refine hPt1.frame (fun b hb => ?_) (fun q hq => ?_)
        · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
          exact hfr2 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
        · obtain ⟨ao, hao⟩ := hPt1.arch hq
          have : q.bv ≠ pc.bv := kheap_ne hao hkc1 (fun _ h1 h2 => by subst h1; cases h2)
          simp [setCnodeSlot, this]
      have hMR : MapRelA st th P L4 L3 L2 L1 SR s2 a (setCnodeSlot σ1 pc.bv r cs idx nc) :=
        ⟨hS2, hSt2, hSV2, hR2, by rw [hks2]; exact hVP, by rw [hks2]; exact hPV⟩
      refine WP.spec_bind (write_mapping_rel_pdpt (hH.map.ext hPl hPS) s2 a _ hPt2 hPP hMR hq (vIdx_lt a0 30) e _ hpte
        as1 a0 _ (Fl4Spec.addrFromPPtr p1.bv)) ?_
      rintro ⟨s3, a3⟩ ⟨hr3, hnf, σ', hm', hPt3, hS3, hSt3, hSV3, hR3, -, -⟩
      have hbo : OutsideObjects th (peA q (vIdx a0 30)) := hPO _ ⟨q, Or.inr (Or.inl hq), _, vIdx_lt a0 30, rfl⟩
      simp only at hr3
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, σ', hdec.trans (mapTailH_ok hf ((al30 a0).1 hal) hsp hgd hd), ?_,
        hSt3, hSV3, hR3, hPt3, hS3, ?_, ?_, ?_⟩)
      · unfold MapSpec mapInvH
        dsimp only
        rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
        exact performHMap_mem (setCap_cnode nc hkc1 hwf hidx) hm' hnf
      · rw [hr3]
        exact (SlotFoot.of_same hSS1 _).trans (hF2.trans (SlotFoot.wr_out hPl s2 hbo _))
      · rw [hr3, capV_wr_out hPl hxsl s2 hbo, hcv2]; exact ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK, frameCapOf] at h ⊢; exact ⟨fun _ => has1, h.2⟩⟩
      · exact (KFoot.sts hkt' _).trans ((KFoot.cnode hkc1 hwf idx nc).trans
          (kfoot_store_flush_pdpt hPP hPt2 hq (vIdx_lt a0 30) _ _ _ hm'))
  · have : ((a0 &&& 1073741823#u64) != 0#u64) = true := by simp [hal]
    simp only [this, ↓reduceIte]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, _, rfl, Or.inr ⟨rfl, rfl⟩,
      hdec.trans (mapTailH_unaligned hf (fun h => hal ((al30 a0).2 h))), rfl, rfl⟩)))

/-- **Huge Frame `Map` refines l4v** (as `frame_map_rel`). -/
theorem frame_map_huge_rel {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Huge) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ MapErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs (pc.bv, idx)
          (frameACapG f) ((vc', xsl) :: rest)) σ = ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) xs
          (pc.bv, idx) (frameACapG f) ((vc', xsl) :: rest)) σ = ({(.ok iv, σ)}, False) ∧
        MapSpec σ iv σ' ∧ StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        VsRel P (L.mem res.2.1) (L.ksb res.2.1) σ' ∧ PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (frameCapOf f) ∧ KFoot σ σ') ⦄ := by
  obtain ⟨ptr, sz, rt, dev, mp, ep, fa, fv⟩ := f
  simp only at hsz hfm hpa ⊢
  subst hsz
  rw [show ∀ args' ex', Fl4Spec.archDecodeInvocation (Z := Unit) slbl args' xs (pc.bv, idx)
      (frameACapG ⟨ptr, .Huge, rt, dev, mp, ep, fa, fv⟩) ex' =
    Fl4Spec.decodePageInvocation slbl args' (pc.bv, idx) (.pageCap dev ptr.bv (vmRightsOf rt)
      (if mp then .vmVSpaceMap else .vmNoMap) .x64HugePage (if mp then some (fa.bv, fv.bv) else none)) ex' from
    fun _ _ => rfl]
  generalize hDec : ExceptT.run (Fl4Spec.decodePageInvocation slbl (args.map UScalar.bv) (pc.bv, idx)
    (.pageCap dev ptr.bv (vmRightsOf rt) (if mp then .vmVSpaceMap else .vmNoMap) .x64HugePage
      (if mp then some (fa.bv, fv.bv) else none)) ((vc', xsl) :: rest)) σ = D
  unfold vspace.decode_page_map
  rw [hct]
  apply ok_bind_spec
  rw [hex]
  apply ok_bind_spec
  dsimp only
  by_cases h3 : length >= 3#u64
  · rw [if_pos h3]
    have h3' : 3 ≤ args.length := by
      have : 3 ≤ length.val := by scalar_tac
      omega
    obtain ⟨a0, a1, a2, ar', rfl⟩ : ∃ a0 a1 a2 r', args = a0 :: a1 :: a2 :: r' := by
      match args, h3' with
      | a0 :: a1 :: a2 :: r', _ => exact ⟨_, _, _, _, rfl⟩
    rw [hargs 0#u64 a0 (by simp)]; apply ok_bind_spec
    rw [hargs 1#u64 a1 (by simp)]; apply ok_bind_spec
    rw [hargs 2#u64 a2 (by simp)]; apply ok_bind_spec
    unfold lift; apply ok_bind_spec; apply ok_bind_spec; apply ok_bind_spec
    rw [slot_cap_eq, hcx]; apply ok_bind_spec
    by_cases hvp : ∃ p asid, vc = .Pml4 p true asid
    · obtain ⟨p1, as1, rfl⟩ := hvp
      obtain ⟨hp1, has1, has2⟩ := hvc p1 as1 rfl
      have hvc' : vc' = .archObjectCap (.pml4Cap p1.bv (some as1.bv)) := by rw [← hvr.2]; rfl
      subst hvc'
      simp only [vspace.mapped_root, ↓reduceIte, bind_ok]
      cases mp
      · simp only [Bool.false_eq_true, ↓reduceIte, capability.FrameSize.bits, bind_ok, shl30]
        simp only [List.map_cons, Bool.false_eq_true, ↓reduceIte] at hDec
        have hdec0 := decodeMapH_unmapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmNoMap p1.bv as1.bv xsl rest σ
        by_cases hv1 : a0 > fl4_abi.consts.USER_TOP
        · simp only [hv1, ↓reduceIte, error.invalid_arg, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
            Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (Or.inl ((gt_top a0).2 hv1))]; rfl)
        · by_cases hv2 : core.num.U64.wrapping_add a0 1073741824#u64 > fl4_abi.consts.USER_TOP
          · simp only [hv1, hv2, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0]
            exact runE_bind_err (by rw [runE_whenE_true (Or.inr (by rw [← addH]; exact (gt_top _).2 hv2))]; rfl)
          · simp only [hv1, hv2, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTailH p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false ?_ _ σ)]
              rintro (h | h)
              · exact hv1 ((gt_top a0).1 h)
              · rw [← addH] at h; exact hv2 ((gt_top _).1 h)
            have hva : a0.val < 2 ^ 48 := by
              have := (show ¬ a0 > fl4_abi.consts.USER_TOP from hv1)
              rw [gt_iff_val] at this
              have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
              omega
            map_tail_H
      · have hfa := hfm rfl
        have hfa' : (fa != 0#u64) = true := by simp [hfa]
        simp only [↓reduceIte, hfa', capability.FrameSize.bits, bind_ok, shl30]
        simp only [List.map_cons, ↓reduceIte] at hDec
        have hdec0 := decodeMapH_mapped hl a0.bv a1.bv a2.bv (ar'.map UScalar.bv) (pc.bv, idx) dev ptr.bv
          (vmRightsOf rt) .vmVSpaceMap fa.bv fv.bv p1.bv as1.bv xsl rest σ
        by_cases hfa1 : fa = as1
        · have : (fa != as1) = false := by simp [hfa1]
          simp only [this, Bool.false_eq_true, ↓reduceIte]
          by_cases hfv : fv = a0
          · have : (fv != a0) = false := by simp [hfv]
            simp only [this, Bool.false_eq_true, ↓reduceIte]
            have hdec : D = ExceptT.run (mapTailH p1.bv as1.bv dev ptr.bv (vmRightsOf rt) a0.bv a1.bv a2.bv (pc.bv, idx)) σ := by
              rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
                runE_bind_ok (runE_whenE_false (by simp) _ σ), runE_bind_ok (runE_whenE_false (by simp [hfv]) _ σ)]
            have hva : a0.val < 2 ^ 48 := hfv ▸ hfe.2.2.2
            map_tail_H
          · have : (fv != a0) = true := by simp [hfv]
            simp only [this, ↓reduceIte, error.invalid_arg, bind_ok]
            refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidArgument 0, rfl,
              Or.inl (Or.inl (show SysErrRel (.Sys (.InvalidArgument 0#u64)) (.invalidArgument 0) from rfl)), ?_, rfl, rfl⟩)
            rw [← hDec, hdec0, runE_bind_ok (runE_whenE_false (by simp [hfa1]) _ σ),
              runE_bind_ok (runE_whenE_false (by simp) _ σ)]
            exact runE_bind_err (by rw [runE_whenE_true (show fv.bv ≠ a0.bv from fun h => hfv (eq_of_bv h))]; rfl)
        · have : (fa != as1) = true := by simp [hfa1]
          simp only [this, ↓reduceIte, error.invalid_cap, bind_ok]
          refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
          rw [← hDec, hdec0]
          exact runE_bind_err (by rw [runE_whenE_true (show fa.bv ≠ as1.bv from fun h => hfa1 (eq_of_bv h))]; rfl)
    · have hmr : vspace.mapped_root vc = ok none := by
        cases vc <;> simp_all [vspace.mapped_root]
      rw [hmr]
      simp only [bind_ok, error.invalid_cap]
      have hbad : ∀ pm asid, vc' ≠ .archObjectCap (.pml4Cap pm (some asid)) := by
        intro pm asid h
        rw [← hvr.2] at h
        cases vc <;> simp_all [absCap]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, .invalidCapability 1, rfl, Or.inl (Or.inr ⟨1#u64, rfl, rfl⟩), ?_, rfl, rfl⟩)
      rw [← hDec, List.map_cons, List.map_cons, List.map_cons]
      exact decodeMapH_badVs hl _ _ _ _ _ _ _ _ _ _ _ _ _ hbad σ
  · rw [if_neg h3]
    simp only [error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, .truncatedMessage, rfl, Or.inl (Or.inl (show SysErrRel (.Sys .TruncatedMessage) .truncatedMessage from trivial)),
      hDec ▸ decodeMap_trunc hl _ _ _ _ _ _ _ _ _ ?_ σ, rfl, rfl⟩)
    have : length.val < 3 := by scalar_tac
    simp only [List.length_map]; omega


end

end

end Fl4Proofs.P3.Vs
