/-
P3 (DESIGN.md §9), VSpace: **the page-directory `Unmap` of a table outside the
sets** (`pd_unmap_rel_off`): VsPdUnmapRel's `pd_unmap_rel` for a mapped cap
whose table `ptr` is in no set, as VsPtUnmapOff's `pt_unmap_rel_off`.
-/
import Fl4Proofs.P3.VsPdUnmapRel
import Fl4Proofs.P3.VsPtUnmapOff
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The page-directory `Unmap` of a table outside the sets** (`pd_unmap_rel` for
a table `ptr` in no set; as VsPtUnmapOff's `pt_unmap_rel_off`). -/
theorem pd_unmap_rel_off {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV3 : ∀ b, PdptW L3 b → ¬ VsWrite P (L.ksb s) b)
    (hPV2 : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool)
    (hTy : ∃ f, σ.kheap ptr.bv = some (.archObj (.pageDirectory f))) (hqa : ptr.val % 4096 = 0)
    (hoff : ∀ i : U64, i.val < 512 → ¬ PtWAll L4 L3 L2 L1 (peA ptr i) ∧ ¬ SlotW th (peA ptr i) ∧
      ¬ VsWrite P (L.ksb s) (peA ptr i) ∧ OutsideObjects th (peA ptr i))
    (hnS : ¬ (ptr ∈ L4 ∨ ptr ∈ L3 ∨ ptr ∈ L2 ∨ ptr ∈ L1))
    (hoffSt : ∀ s1 s2 a1 σ1 σ2, SR s1 a1 σ1 → L.ksb s1 = L.ksb s → KFoot σ σ1 → WritesIn st s1 s2 (PtW {ptr}) →
      (∃ f f', σ1.kheap ptr.bv = some (.archObj (.pageDirectory f)) ∧ σ2 = updK σ1 ptr.bv (.archObj (.pageDirectory f'))) →
      SR s2 a1 σ2)
    (hfe : EncWf (.PageDirectory ptr mp asid0 va0))
    (hm0 : mp = true → asid0 ≠ 0#u64) (hmu : mp = true → Vs.UserV va0)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf : U64) (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {fin : Bool} (hfin : cdt.is_final_capability st s (cslotAddr (pc.bv, idx)) = ok fin)
    (hfinR : fin = true ↔ Fl4Spec.isFinalCap'
      (.archObjectCap (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageDirectoryUnmap length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) buf ex ⦃ res =>
      (∃ e e', res.1 = .Err e ∧ VsErrRel e e' ∧
        ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx)
          (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs) σ =
            ({(.error e', σ)}, False) ∧ res.2.1 = s ∧ res.2.2 = a) ∨
      (res.1 = .Ok () ∧ ∃ iv σ', ExceptT.run (Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs
          (pc.bv, idx) (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs) σ =
            ({(.ok iv, σ)}, False) ∧
        PdMapSpec σ iv σ' ∧ UR st th P L4 L3 L2 L1 SR res.2.1 res.2.2 σ' ∧
        SlotFoot th (L.mem s) (L.mem res.2.1) (cslotAddr (pc.bv, idx)) ∧
        VsLike (capV (L.mem res.2.1) (cslotAddr (pc.bv, idx))) (.PageDirectory ptr mp asid0 va0) ∧ KFoot σ σ' ∧
        (mp = true → (∀ i : U64, i.val < 512 → L.mem res.2.1 (peA ptr i) = 0#u64) ∧
          σ'.kheap ptr.bv = some (.archObj (.pageDirectory fun _ => .invalidPDE)))) ⦄ := by
  rw [show Fl4Spec.archDecodeInvocation (Z := Unit) slbl args xs (pc.bv, idx)
      (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs =
    Fl4Spec.decodePageDirectoryInvocation slbl args (pc.bv, idx)
      (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none)) vcs from rfl]
  unfold vspace.decode_table
  simp only [vspace.as_table, bind_ok, ↓reduceIte]
  unfold vspace.decode_table_unmap
  rw [hfin]
  apply ok_bind_spec
  obtain ⟨cs, hkc, hwf, hsl⟩ := hSt.cnode pc r hpc
  have hcs : cs idx = some (.archObjectCap (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) := by
    obtain ⟨c, ac, hc, hac, hca⟩ := hsl idx hidx
    have : c = .PageDirectory ptr mp asid0 va0 := by
      have h2 : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok c := hc
      rw [hcx] at h2; exact (by simpa using h2 : capability.Cap.PageDirectory ptr mp asid0 va0 = c).symm
    subst this
    rw [hac, ← hca.2]; rfl
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnf : ¬ Fl4Spec.isFinalCap'
        (.archObjectCap (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ :=
      fun h => by simpa using hfinR.2 h
    exact (WP.spec_ok _).2 (Or.inl ⟨_, .revokeFirst, rfl, Or.inl (show SysErrRel (.Sys .RevokeFirst) .revokeFirst from trivial),
      pdDecodeUnmap_notFinal hl _ _ _ _ _ σ hnf, rfl, rfl⟩)
  simp only [↓reduceIte]
  have hfn := hfinR.1 rfl
  have hdec := pdDecodeUnmap_final hl args (pc.bv, idx) ptr.bv _ vcs σ hfn
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
  set nc : Fl4Spec.Cap := .archObjectCap (.pageDirectoryCap ptr.bv none) with hnc
  have hca : CapRel (.PageDirectory ptr false 0#u64 0#u64) nc := ⟨trivial, rfl⟩
  have hew : EncWf (.PageDirectory ptr false 0#u64 0#u64) := ⟨hfe.1, by decide, by decide⟩
  have hxsl : IsSlot th (cslotAddr (pc.bv, idx)) :=
    (show AbsSlot th (pc.bv, idx) from ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩).isSlot
  -- the final `set_cap`, from a state `s4`/`σ4` with the CNode unchanged
  have fin_cap : ∀ (s4 : S) (a4 : A) (σ4 : Fl4Spec.State Unit), UR st th P L4 L3 L2 L1 SR s4 a4 σ4 →
      σ4.kheap pc.bv = some (.cnode r cs) → L.ksb s4 = L.ksb s →
      obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s4 (.PageDirectory ptr false 0#u64 0#u64) ⦃ s5 =>
        UR st th P L4 L3 L2 L1 SR s5 a4 (setCnodeSlot σ4 pc.bv r cs idx nc) ∧
        SlotFoot th (L.mem s4) (L.mem s5) (cslotAddr (pc.bv, idx)) ∧
        capV (L.mem s5) (cslotAddr (pc.bv, idx)) = .PageDirectory ptr false 0#u64 0#u64 ∧ WritesIn st s4 s5 (SlotW th) ⦄ := by
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
    refine ⟨⟨hH.capStable _ _ a4 _ _ hS4 hWs ⟨pc.bv, r, cs, idx, nc, hkc4, rfl⟩, hSt5, hSV5, ?_, ?_⟩, hF5, hcv5, hWs⟩
    · rw [hks5]; rw [hks4] at hR4 ⊢
      exact hR4.frame hfrV rfl hpools
    · refine hPt4.frame (fun b hb => ?_) (fun q hq => ?_)
      · obtain ⟨h1, h2⟩ := ne_slot_words hPl hxs (hPS b hb)
        exact hfr5 b (hb.aligned hPP) (by rw [hx0]; exact h1) (by rw [hx0]; exact h2)
      · obtain ⟨ao, hao⟩ := hPt4.arch hq
        have : q.bv ≠ pc.bv := kheap_ne hao hkc4 (fun _ h1 h2 => by subst h1; cases h2)
        simp [setCnodeSlot, this]
  obtain ⟨f1, hkp0⟩ := hTy
  have hpct' : ptr.bv ≠ ct.bv := kheap_ne hkp0 hkt' (fun _ h1 h2 => by subst h1; cases h2)
  have hkp1 : σ1.kheap ptr.bv = some (.archObj (.pageDirectory f1)) := by
    rw [hσ1, stsAct_kheap]; simp [updK, hpct', hkp0]
  have hpc' : ptr.bv ≠ pc.bv := kheap_ne hkp1 hkc1 (fun _ h1 h2 => by subst h1; cases h2)
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hcs ⊢
    rw [show vspace.with_mapping (.PageDirectory ptr false asid0 va0) false asid0 va0 =
      ok (.PageDirectory ptr false 0#u64 0#u64) by simp [vspace.with_mapping]]
    apply ok_bind_spec
    refine WP.spec_bind (fin_cap s1 a σ1 ⟨hS1, hSt1, hSV1, hR1, hPt1⟩ hkc1 hk1) ?_
    rintro s5 ⟨hU5, hF5, hcv5, -⟩
    refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans hF5,
      by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK] at h ⊢; first | exact ⟨h.1, h.2.1, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1, trivial, trivial⟩ | exact ⟨h.1, h.2.1, fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2.1, trivial⟩⟩, (KFoot.sts hkt' _).trans (KFoot.cnode hkc1 hwf idx nc), fun h => absurd h (by decide)⟩)
    unfold PdMapSpec
    dsimp only
    rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt'), performPdUnmap_none hkc1 hwf hidx hcs]
    exact ⟨rfl, id⟩
  · have hA0 := hm0 rfl
    simp only [↓reduceIte] at hcs ⊢
    let SR' : S → A → Fl4Spec.State Unit → Prop := fun s' a' σ' =>
      SR s' a' σ' ∧ SlotFoot th (L.mem s1) (L.mem s') (cslotAddr (pc.bv, idx)) ∧ KFoot σ1 σ'
    have hH' : VsPdInnerHyps st A ar L3 SR' :=
      { pdptStable := fun s' s'' a' σ' σ'' ⟨h1, h2, h3⟩ hw hst => ⟨hH.pdptStable _ _ _ _ _ h1 hw hst,
          h2.trans (SlotFoot.of_writes hPl hw (fun b ⟨q, hq, i, hi, e⟩ =>
            hPO b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) _),
          h3.trans (by obtain ⟨p, f, f', hk, rfl⟩ := hst; exact KFoot.arch hk _)⟩
        flushOK := hH.flushOK
        flushPS := fun s' a' σ' vs asid ⟨h1, h2, h3⟩ => WP.spec_mono (hH.flushPS s' a' σ' vs asid h1)
          (fun a'' ⟨σ'', hm, hS''⟩ => ⟨σ'', hm, hS'', h2, h3.trans (by
            obtain ⟨ms, rfl⟩ := doMachineOp_mem hm; exact KFoot.ms _ ms)⟩)
        flushAllOK := hH.flushAllOK
        flushAllH := fun s' a' σ' vs asid ⟨h1, h2, h3⟩ => WP.spec_mono (hH.flushAllH s' a' σ' vs asid h1)
          (fun a'' ⟨σ'', hm, hS''⟩ => ⟨σ'', hm, hS'', h2, h3.trans (by
            obtain ⟨ms, rfl⟩ := doMachineOp_mem hm; exact KFoot.ms _ ms)⟩) }
    have hU1 : UR st th P L4 L3 L2 L1 SR' s1 a σ1 := ⟨⟨hS1, SlotFoot.refl _ _, KFoot.refl _⟩, hSt1, hSV1, hR1, hPt1⟩
    refine WP.spec_bind (Pₘ := fun p => ∃ σu, ((), σu) ∈ (Fl4Spec.unmapPd (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 ∧
        ¬ (Fl4Spec.unmapPd (Z := Unit) asid0.bv va0.bv ptr.bv σ1).2 ∧
        (∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPd (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 →
          σ'.kheap ptr.bv = σ1.kheap ptr.bv ∧ σ'.kheap pc.bv = σ1.kheap pc.bv) ∧
        UR st th P L4 L3 L2 L1 SR p.1 p.2 (updK σu ptr.bv (.archObj (.pageDirectory fun _ => .invalidPDE))) ∧
        (updK σu ptr.bv (.archObj (.pageDirectory fun _ => .invalidPDE))).kheap pc.bv = some (.cnode r cs) ∧
        L.ksb p.1 = L.ksb s ∧ SlotFoot th (L.mem s1) (L.mem p.1) (cslotAddr (pc.bv, idx)) ∧
        KFoot σ1 (updK σu ptr.bv (.archObj (.pageDirectory fun _ => .invalidPDE))) ∧
        ∀ i : U64, i.val < 512 → L.mem p.1 (peA ptr i) = 0#u64) ?_ ?_
    · refine WP.spec_bind (unmap_page_directory_rel hH' s1 a σ1 hPl hPP hPS (hk1 ▸ hVP) (hk1 ▸ hPV3) hPI1 hU1
        asid0 va0 ptr hA0 (hmu rfl)) ?_
      rintro ⟨s3, a3⟩ ⟨hnu, hall, σu, hu, ⟨⟨hS3, hF3, hK3⟩, hSt3, hSV3, hR3, hPt3⟩, hk3⟩
      show (st.zero s3 ptr 4096#u64 >>= fun s4 => ok (s4, a3)) ⦃ _ ⦄
      rw [L.zero_eq]
      apply ok_bind_spec
      have hall' : ∀ x σ', (x, σ') ∈ (Fl4Spec.unmapPd (Z := Unit) asid0.bv va0.bv ptr.bv σ1).1 →
          σ'.kheap ptr.bv = σ1.kheap ptr.bv ∧ σ'.kheap pc.bv = σ1.kheap pc.bv := fun x σ' hx =>
        ⟨hall x σ' hx ptr.bv (fun g h => by rw [hkp1] at h; cases h),
          hall x σ' hx pc.bv (fun g h => by rw [hkc1] at h; cases h)⟩
      have hkpu : σu.kheap ptr.bv = some (.archObj (.pageDirectory f1)) := (hall' () σu hu).1.trans hkp1
      have hkcu : σu.kheap pc.bv = some (.cnode r cs) := (hall' () σu hu).2.trans hkc1
      have hW := writes_zero hqa (Set.mem_singleton ptr) (L := L) s3
      have hf := tbl_fit hqa
      have hzr : ∀ b, Aligned b → L.mem (L.zr s3 ptr 4096#u64) b =
          if ptr.val ≤ b.val ∧ b.val < ptr.val + (4096#u64).val then 0#u64 else L.mem s3 b := fun b hb =>
        L.mem_zr _ _ _ _ (show ptr.val % 8 = 0 by omega) (by decide) (by simpa using hf) hb
      have hPt4 : PtRel L4 L3 L2 L1 (L.mem (L.zr s3 ptr 4096#u64))
          (updK σu ptr.bv (.archObj (.pageDirectory fun _ => .invalidPDE))) := by
        refine hPt3.frame (fun b hb => ?_) (fun q hq => ?_)
        · exact hW.2.2 b (hb.aligned hPP) (fun ⟨q, hq, i, hi, e⟩ => by
            rw [Set.mem_singleton_iff.1 hq] at e; exact (hoff i hi).1 (e ▸ hb))
        · have : q.bv ≠ ptr.bv := fun e => hnS (by rw [← P1.eq_of_bv e]; exact hq)
          simp [updK, this]
      have hPS1 : ∀ b, PtW {ptr} b → ¬ SlotW th b := by
        rintro b ⟨p, hp, i, hi, rfl⟩
        rw [Set.mem_singleton_iff.1 hp]; exact (hoff i hi).2.1
      have hcap := capAt_of_writes hPl hW hPS1
      have hks3 : L.ksb s3 = L.ksb s := hk3.trans hk1
      refine (WP.spec_ok _).2 ⟨σu, hu, hnu, hall', ⟨hoffSt _ _ a3 _ _ hS3 hks3 ((KFoot.sts hkt' _).trans hK3) hW ⟨f1, _, hkpu, rfl⟩,
        Vs.StateRel.upd_other (StateRel.of_caps hSt3 hcap) hkpu _, Vs.SlotsValid.of_caps hSV3 hcap, ?_, hPt4⟩,
        by simp [updK, hpc'.symm, hkcu], by rw [L.ksb_zr, hks3],
        hF3.trans (SlotFoot.of_writes hPl hW (fun b ⟨q, hq, i, hi, e⟩ => by
          rw [Set.mem_singleton_iff.1 hq] at e; rw [e]; exact (hoff i hi).2.2.2) _), hK3.trans (KFoot.arch hkpu _), fun i hi => ?_⟩
      rw [hW.1]
      refine hR3.frame (fun b hb => hW.2.2 b (hb.aligned (hks3 ▸ hVP)) (fun ⟨q, hq, i, hi, e⟩ => by
          rw [Set.mem_singleton_iff.1 hq] at e; exact (hoff i hi).2.2.1 (e ▸ hks3 ▸ hb))) rfl
        (fun p hp => ?_)
      obtain ⟨g, hg, -⟩ := hR3.pool p hp
      have : p.bv ≠ ptr.bv := kheap_ne hg hkpu (fun _ h1 h2 => by subst h1; cases h2)
      simp [updK, this]
      · have hv := peA_val hf hi
        have h4 : (4096#u64 : U64).val = 4096 := by simp
        rw [hzr _ (show (peA ptr i).val % 8 = 0 by rw [hv]; omega), if_pos ⟨by rw [hv]; omega, by rw [hv, h4]; omega⟩]
    · rintro ⟨s4, a4⟩ ⟨σu, hu, hnu, hall', hU4, hkc4, hks4, hF4, hK4, hz4⟩
      show (vspace.with_mapping (.PageDirectory ptr true asid0 va0) false asid0 va0 >>= fun c =>
        obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s4 c >>= fun s3 => ok (core.result.Result.Ok (), s3, a4)) ⦃ _ ⦄
      rw [show vspace.with_mapping (.PageDirectory ptr true asid0 va0) false asid0 va0 =
        ok (.PageDirectory ptr false 0#u64 0#u64) by simp [vspace.with_mapping]]
      apply ok_bind_spec
      refine WP.spec_bind (fin_cap s4 a4 _ hU4 hkc4 hks4) ?_
      rintro s5 ⟨hU5, hF5, hcv5, hWs5⟩
      refine (WP.spec_ok _).2 (Or.inr ⟨rfl, _, _, rfl, ?_, hU5, (SlotFoot.of_same hSS1 _).trans (hF4.trans hF5),
        by rw [hcv5]; exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun _ _ _ _ _ h => by simp only [VCapOK] at h ⊢; first | exact ⟨h.1, h.2.1, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1, trivial, trivial⟩ | exact ⟨h.1, h.2.1, fun e => absurd e (by decide)⟩ | exact ⟨h.1, h.2.1⟩ | exact ⟨h.1, h.2.1, trivial⟩⟩, (KFoot.sts hkt' _).trans (hK4.trans (KFoot.cnode hkc4 hwf idx nc)),
        fun _ => ⟨fun i hi => ?_, by simp [setCnodeSlot, updK, hpc']⟩⟩)
      swap
      · have hv := peA_val (tbl_fit hqa) hi
        rw [hWs5.mem_eq (show (peA ptr i).val % 8 = 0 by rw [hv]; omega) (fun h => (hoff i hi).2.1 h)]
        exact hz4 i hi
      unfold PdMapSpec
      dsimp only
      rw [← hcur, nd_bind_one (Notif.setThreadState_eq .restart hkt')]
      exact performPdUnmap_mem hqa hnu hall' hu hkp1 hkc1 hwf hidx hcs

end

end

end Fl4Proofs.P3.Vs
