/-
P3 (DESIGN.md §9), CSpace: **the CNode Rotate invocation** (FL4
`cnode::decode_rotate`, `rotate_slots`) against l4v
`decode_cnode_invocation` (the `CNodeRotate` branch) followed by
`set_thread_state Restart` and `invoke_cnode` (`cap_swap`, or two
`cap_move`s).

Extra caps: `extra[0]` (the pivot root) and `extra[1]` (the source root)
related to the spec's first two extra caps, or null when there are fewer
(`ExtraRel2`).
-/
import Fl4Proofs.P3.CnodeOther
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's Rotate branch -/

section
open Fl4Spec

theorem copyTail_rotate {label : Data} (hg : genInvocationType label = .cnodeRotate)
    (a0 a1 a2 a3 a4 a5 : Data) (rest : List Data) (e0 e1 : Cap) (erest : List Cap) (d : CslotPtr) :
    copyTail label (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest) (e0 :: e1 :: erest) d = (do
      let srcSlot ← lookupSourceSlot e1 (dataToCptr a4) (dataToNat a5)
      let pivotSlot ← lookupPivotSlot e0 (dataToCptr a1) (dataToNat a2)
      NonDetE.whenE (pivotSlot = srcSlot ∨ pivotSlot = d) <| NonDetE.throwError .illegalOperation
      NonDetE.unlessE (srcSlot = d) <| ensureEmpty d
      let srcCap ← NonDetE.liftE <| getCap srcSlot
      NonDetE.whenE (srcCap = .nullCap) <|
        NonDetE.throwError <| .failedLookup true <| .missingCapability (dataToNat a5)
      let pivotCap ← NonDetE.liftE <| getCap pivotSlot
      NonDetE.whenE (pivotCap = .nullCap) <|
        NonDetE.throwError <| .failedLookup false <| .missingCapability (dataToNat a2)
      let newSrcCap ← NonDetE.returnOk <| updateCapData true a3 srcCap
      let newPivotCap ← NonDetE.returnOk <| updateCapData true a0 pivotCap
      NonDetE.whenE (newSrcCap = .nullCap) <| NonDetE.throwError .illegalOperation
      NonDetE.whenE (newPivotCap = .nullCap) <| NonDetE.throwError .illegalOperation
      NonDetE.returnOk <| .rotateCall newSrcCap newPivotCap srcSlot pivotSlot d) := by
  have hnc : GenInvocationLabels.cnodeRotate ∉ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate := by decide
  unfold copyTail
  simp [hg, hnc, NonDetE.returnOk, the]

theorem copyTail_rotate_short {label : Data} (hg : genInvocationType label = .cnodeRotate)
    (args : List Data) (excaps : List Cap) (d : CslotPtr) (h : ¬ (args.length > 5 ∧ excaps.length > 1)) :
    copyTail label args excaps d = NonDetE.throwError .truncatedMessage := by
  have hnc : GenInvocationLabels.cnodeRotate ∉ GenInvocationLabels.uptoEnum .cnodeCopy .cnodeMutate := by decide
  unfold copyTail
  simp only [hg, hnc, and_false, ↓reduceIte, reduceCtorEq, true_and, if_neg h]

end

/-- `extra[0]` and `extra[1]` against the spec's extra caps: null when there
is none, else the slot of the cap. -/
def ExtraRel2 (th : TypedHeap) (mem : U64 → U64) (x0 x1 : U64) (excaps : List Fl4Spec.Cap) : Prop :=
  (x0 = 0#u64 ∧ excaps = []) ∨
  (x0 ≠ 0#u64 ∧ IsSlot th x0 ∧ ∃ c a, capAt mem x0 = ok c ∧ CapRel c a ∧ CapValid th c ∧
    ((x1 = 0#u64 ∧ excaps = [a]) ∨
     (x1 ≠ 0#u64 ∧ IsSlot th x1 ∧ ∃ c' a' rest, capAt mem x1 = ok c' ∧ CapRel c' a' ∧ CapValid th c' ∧
       excaps = a :: a' :: rest)))


theorem slot_ne_eq (a b : obj.Slot) :
    core.cmp.PartialEq.ne.trait_default obj.Slot.Insts.CoreCmpPartialEqSlot a b = ok (decide (a ≠ b)) := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Slot.Insts.CoreCmpPartialEqSlot.eq]
  exact ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

theorem slot_eq_eq (a b : obj.Slot) : obj.Slot.Insts.CoreCmpPartialEqSlot.eq a b = ok (decide (a = b)) := rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]


/-- The slots after `move_cap` (from a linked slot to a free one). -/
theorem move_caps {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrcm : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdestm : dest ∉ G.chains.flatten)
    (c : capability.Cap) (he : EncWf c) :
    cdt.move_cap st s c src dest ⦃ s' => ∀ a, IsSlot th a →
      capAt (L.mem s') a = if a = dest then ok c else if a = src then ok .Null else capAt (L.mem s) a ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrcm
  have hne : src ≠ dest := fun e => hdestm (e ▸ hsrcm)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrcm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrcm h0
      refine Or.inr ⟨hslot _ h1, fun e => hdestm (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrcm with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  exact WP.spec_mono (move_mem hP s c _ _ hs hd hne hpv hnx) (fun s' hW a ha => hW.capAt' ha he hne)

theorem run_whenE_false {σ ε : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : Fl4Spec.NonDetE σ ε Unit) (s : σ) :
    (Fl4Spec.NonDetE.whenE P m).run s = ({(.ok (), s)}, False) := by
  simp only [Fl4Spec.NonDetE.whenE, h, ↓reduceIte]; rfl

theorem run_unlessE_true {σ ε : Type} {P : Prop} [Decidable P] (h : P) (m : Fl4Spec.NonDetE σ ε Unit) (s : σ) :
    (Fl4Spec.NonDetE.unlessE P m).run s = ({(.ok (), s)}, False) := by
  simp only [Fl4Spec.NonDetE.unlessE, h, ↓reduceIte]; rfl

/-- **`decode_rotate` refines the spec's Rotate branch** (after the target
slot lookup), then `set_thread_state Restart` and `invoke_cnode`
(`swap_full`, or `move_full` twice). -/
theorem decode_rotate_rel (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hg : Fl4Spec.genInvocationType slbl = .cnodeRotate)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length) (h2 : 2 ≤ args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0) (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel2 th (L.mem s) x0 x1 excaps)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (dsl : Fl4Spec.CslotPtr) (pd : U64) (hpd1 : dsl.1 = pd.bv) (hpd : th pd = some (.cnode dsl.2.length))
    (root : capability.Cap)
    (hpdL : (∃ y, IsSlot th y ∧ capV (L.mem s) y = root) → DestLive th (L.mem s) (L.ksb s) pd) :
    cnode.decode_rotate st s length buf extra (cslotAddr dsl) ⦃ res =>
      InvPost (L := L) th σ G (copyTail slbl ((args.map UScalar.bv).drop 2) excaps dsl) s res
        (CnTrace (L := L) th ct σ root s) ⦄ := by
  have hts := set_thread_state_slots th hP s ct sched.TS_RESTART htcb hact
  have hAd : AbsSlot th dsl := ⟨pd, hpd1, Or.inl hpd⟩
  unfold cnode.decode_rotate
  by_cases h8 : length < 8#u64
  · rw [if_pos h8]
    simp only [error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, .truncatedMessage, ?_, trivial⟩
    rw [copyTail_rotate_short hg _ _ _ (fun ⟨h, _⟩ => by simp at h; scalar_tac)]; rfl
  rw [if_neg h8]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rest, rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5 a6 a7 rest, args = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest := by
    match args with
    | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rest, rfl⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
      exfalso; simp at hlen; scalar_tac
  simp only [List.map_cons, List.drop_succ_cons, List.drop_zero]
  rw [hx0]; simp only [bind_ok, obj.Slot.is_null]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, hx0s, c0, e0, hc0, hca0, hcv0, hx1r⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, .truncatedMessage, ?_, trivial⟩
    rw [copyTail_rotate_short hg _ _ _ (fun ⟨_, h⟩ => by simp at h)]; rfl
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [hx1]; simp only [bind_ok]
  rcases hx1r with ⟨rfl, rfl⟩ | ⟨hx1n, hx1s, c1, e1, erest, hc1, hca1, hcv1, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    refine ⟨rfl, .truncatedMessage, ?_, trivial⟩
    rw [copyTail_rotate_short hg _ _ _ (fun ⟨_, h⟩ => by simp at h)]; rfl
  simp only [hx1n, decide_false, Bool.false_eq_true, ↓reduceIte]
  simp only [hct, hargs 2#u64 a2 (by simp), hargs 5#u64 a5 (by simp), bind_ok]
  unfold cnode.rotate_slots
  simp only [hct, hargs 3#u64 a3 (by simp), hargs 4#u64 a4 (by simp), hargs 6#u64 a6 (by simp),
    hargs 7#u64 a7 (by simp), hx0, hx1, slot_cap_eq, hc0, hc1, bind_ok]
  rw [copyTail_rotate hg]
  -- the source slot
  rw [lookup_source_eq]
  obtain ⟨r1, hr1, ee1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV true c1 e1 hca1 hcv1 a6 a7)
  rw [hr1]; simp only [bind_ok]
  have hls : (Fl4Spec.lookupSourceSlot (Z := Unit) e1 (Fl4Spec.dataToCptr a6.bv) (Fl4Spec.dataToNat a7.bv)).run σ =
      ({(ee1, σ)}, False) := he1
  cases r1 with
  | Err e =>
    cases ee1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        core.convert.FromSame.from, bind_ok, bind_tc_ok]
      rw [WP.spec_ok]
      exact ⟨rfl, e', run_bind_error hls _, hrel1⟩
  | Ok src =>
    cases ee1 with
    | error _ => exact hrel1.elim
    | ok sl =>
      obtain ⟨rfl, ps, hps1, hps, hcr1⟩ := hrel1
      have hpsL : DestLive th (L.mem s) (L.ksb s) ps := DestLive.of_cnRef hcr1 ⟨x1, hx1s, capV_of_capAt hc1⟩
      refine InvPost.congr (run_bind_ok hls _) ?_
      have hAs : AbsSlot th sl := ⟨ps, hps1, Or.inl hps⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      -- the pivot slot
      unfold cspace.lookup_pivot_slot
      obtain ⟨r2, hr2, ee2, he2, hrel2⟩ := spec_exists
        (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV true c0 e0 hca0 hcv0 a3 a4)
      rw [hr2]; simp only [bind_ok]
      have hlp : (Fl4Spec.lookupPivotSlot (Z := Unit) e0 (Fl4Spec.dataToCptr a3.bv) (Fl4Spec.dataToNat a4.bv)).run σ =
          ({(ee2, σ)}, False) := he2
      cases r2 with
      | Err e =>
        cases ee2 with
        | ok _ => exact hrel2.elim
        | error e' =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            core.convert.FromSame.from, bind_ok, bind_tc_ok]
          rw [WP.spec_ok]
          exact ⟨rfl, e', run_bind_error hlp _, hrel2⟩
      | Ok piv =>
        cases ee2 with
        | error _ => exact hrel2.elim
        | ok pl =>
          obtain ⟨rfl, ppv, hpl1, hpl, hcr2⟩ := hrel2
          have hplL : DestLive th (L.mem s) (L.ksb s) ppv :=
            DestLive.of_cnRef hcr2 ⟨x0, hx0s, capV_of_capAt hc0⟩
          refine InvPost.congr (run_bind_ok hlp _) ?_
          have hAp : AbsSlot th pl := ⟨ppv, hpl1, Or.inl hpl⟩
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, slot_eq_eq]
          obtain ⟨sa, sb⟩ := sl
          obtain ⟨pa, pb⟩ := pl
          simp only at hps1 hpl1; subst hps1 hpl1
          obtain ⟨da, db⟩ := dsl
          simp only at hpd1; subst hpd1
          obtain ⟨srcC, srcA, hsc, hsca, hgs⟩ := hR.slot_cap (Z := Unit) rfl hps
          obtain ⟨pivC, pivA, hpc, hpca, hgp⟩ := hR.slot_cap (Z := Unit) rfl hpl
          obtain ⟨cd, ad, hcd, hcad, hgd⟩ := hR.slot_cap (Z := Unit) rfl hpd
          by_cases e1 : cslotAddr (ppv.bv, pb) = cslotAddr (ps.bv, sb)
          · simp only [show decide (cslotAddr (ppv.bv, pb) = cslotAddr (ps.bv, sb)) = true from decide_eq_true e1, ↓reduceIte, error.illegal, bind_ok,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
              bind_tc_ok]
            rw [WP.spec_ok]
            refine ⟨rfl, .illegalOperation, ?_, trivial⟩
            have := cslotAddr_inj hP hAp hAs e1
            simp only [this, true_or, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
          have e1' : (ppv.bv, pb) ≠ (ps.bv, sb) := fun h => e1 (by rw [h])
          by_cases e2 : cslotAddr (ppv.bv, pb) = cslotAddr (pd.bv, db)
          · simp only [show decide (cslotAddr (ppv.bv, pb) = cslotAddr (ps.bv, sb)) = false from decide_eq_false e1,
              show decide (cslotAddr (ppv.bv, pb) = cslotAddr (pd.bv, db)) = true from decide_eq_true e2, Bool.false_eq_true, ↓reduceIte, error.illegal, bind_ok,
              core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
              bind_tc_ok]
            rw [WP.spec_ok]
            refine ⟨rfl, .illegalOperation, ?_, trivial⟩
            have := cslotAddr_inj hP hAp hAd e2
            simp only [this, or_true, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
          have e2' : (ppv.bv, pb) ≠ (pd.bv, db) := fun h => e2 (by rw [h])
          simp only [show decide (cslotAddr (ppv.bv, pb) = cslotAddr (ps.bv, sb)) = false from decide_eq_false e1,
            show decide (cslotAddr (ppv.bv, pb) = cslotAddr (pd.bv, db)) = false from decide_eq_false e2, Bool.false_eq_true, ↓reduceIte, slot_ne_eq, bind_ok]
          refine InvPost.congr (run_bind_ok (run_whenE_false (not_or.2 ⟨e1', e2'⟩) _ σ) _) ?_
          have hsw : CapWf srcC := hsca.1
          have hse : EncWf srcC := by rw [capAt_words] at hsc; exact decode_encWf hsc
          have hscv := hV.abs hAs hsc
          have hpw : CapWf pivC := hpca.1
          have hpe : EncWf pivC := by rw [capAt_words] at hpc; exact decode_encWf hpc
          have hpcv := hV.abs hAp hpc
          by_cases e3 : cslotAddr (ps.bv, sb) = cslotAddr (pd.bv, db)
          · have e3' : (ps.bv, sb) = (pd.bv, db) := cslotAddr_inj hP hAs hAd e3
            simp only [show decide (cslotAddr (ps.bv, sb) ≠ cslotAddr (pd.bv, db)) = false from decide_eq_false (fun h => h e3), Bool.false_eq_true,
              ↓reduceIte]
            refine InvPost.congr (run_bind_ok (run_unlessE_true e3' _ σ) _) ?_
            rw [hsc]; simp only [bind_ok]
            refine InvPost.congr (run_bind_ok (run_liftE hgs) _) ?_
            by_cases hsn : srcC = .Null
            · subst hsn
              have : srcA = .nullCap := (hsca.null_iff).2 rfl
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, cnode.missing_source, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
                bind_tc_ok]
              rw [WP.spec_ok]
              refine ⟨rfl, .failedLookup true (.missingCapability a7.val), ?_, show true = true ∧ a7.val = a7.val from ⟨rfl, rfl⟩⟩
              simp only [this, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hsan : srcA ≠ .nullCap := fun h => hsn ((hsca.null_iff).1 h)
            rw [cap_is_null_ne hsn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, hpc]
            refine InvPost.congr (run_bind_ok (run_whenE_false hsan _ σ) _) (InvPost.congr (run_bind_ok (run_liftE hgp) _) ?_)
            by_cases hpn : pivC = .Null
            · subst hpn
              have : pivA = .nullCap := (hpca.null_iff).2 rfl
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, cnode.missing_source, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
                bind_tc_ok]
              rw [WP.spec_ok]
              refine ⟨rfl, .failedLookup false (.missingCapability a4.val), ?_, show false = false ∧ a4.val = a4.val from ⟨rfl, rfl⟩⟩
              simp only [this, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hpan : pivA ≠ .nullCap := fun h => hpn ((hpca.null_iff).1 h)
            rw [cap_is_null_ne hpn]
            obtain ⟨ns, hns, hnsw, hnsa, hnse, hnscv, -⟩ := update_rel true a5 srcC hsw hse
            obtain ⟨np, hnp, hnpw, hnpa, hnpe, hnpcv, -⟩ := update_rel true a2 pivC hpw hpe
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
            simp only [uncurry_apply_pair, hsc, hpc, hns, hnp, bind_ok]
            rw [← hsca.abs, ← hpca.abs] at *
            refine InvPost.congr (run_bind_ok (run_whenE_false hpan _ σ) _) (InvPost.congr (run_bind_ok (run_returnOk _ σ) _)
              (InvPost.congr (run_bind_ok (run_returnOk _ σ) _) ?_))
            rw [← hnsa, ← hnpa]
            by_cases hnsn : ns = .Null
            · subst hnsn
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, error.illegal]
              rw [WP.spec_ok]
              refine ⟨rfl, .illegalOperation, ?_, trivial⟩
              simp only [show absCap capability.Cap.Null = .nullCap from rfl, Fl4Spec.NonDetE.whenE, ↓reduceIte,
                Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hnsan : absCap ns ≠ .nullCap := fun h => hnsn ((show CapRel ns (absCap ns) from ⟨hnsw, rfl⟩).null_iff.1 h)
            rw [cap_is_null_ne hnsn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
            by_cases hnpn : np = .Null
            · subst hnpn
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, error.illegal]
              rw [WP.spec_ok]
              refine ⟨rfl, .illegalOperation, ?_, trivial⟩
              simp only [hnsan, show absCap capability.Cap.Null = .nullCap from rfl, Fl4Spec.NonDetE.whenE, ↓reduceIte,
                Fl4Spec.NonDetE.throwError, ndE_throw_bind, ndE_pure_bind]; rfl
            have hnpan : absCap np ≠ .nullCap := fun h => hnpn ((show CapRel np (absCap np) from ⟨hnpw, rfl⟩).null_iff.1 h)
            rw [cap_is_null_ne hnpn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨hshs, hbds⟩ := update_shape hns hnsn
            obtain ⟨hshp, hbdp⟩ := update_shape hnp hnpn
            have hbds' : badgeF ns = badgeF srcC := by rcases hbds with h | ⟨-, h⟩; exact h; cases h
            have hbdp' : badgeF np = badgeF pivC := by rcases hbdp with h | ⟨-, h⟩; exact h; cases h
            -- set_thread_state
            obtain ⟨s2, hs2, hS⟩ := spec_exists hts
            rw [hs2]; simp only [bind_ok, slot_eq_eq]
            obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
            rw [← hcur] at hk
            obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
            have hI1 := MdbInv.of_same hM hI hS
            have hFI1 := hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)
            have hsc2 : capAt (L.mem s2) (cslotAddr (ps.bv, sb)) = ok srcC := by rw [hS.capAt hAs.isSlot, hsc]
            have hpc2 : capAt (L.mem s2) (cslotAddr (ppv.bv, pb)) = ok pivC := by rw [hS.capAt hAp.isSlot, hpc]
            simp only [show decide (cslotAddr (ps.bv, sb) = cslotAddr (pd.bv, db)) = true from decide_eq_true e3, ↓reduceIte]
            obtain ⟨s3, hs3, σ', G', hsw', hR', hV', hM', hC', hI', hFI', hSt, hG'⟩ := spec_exists
              (swap_full_finG th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hFI1 hps hpl rfl rfl (fun h => e1' h.symm) hsc2 hsn hpc2 hpn
                ns (absCap ns) ⟨hnsw, rfl⟩ (hnscv th hscv) hnse hnsn hshs hbds' (update_okey hns hnsn)
                np (absCap np) ⟨hnpw, rfl⟩ (hnpcv th hpcv) hnpe hnpn hshp hbdp' (update_okey hnp hnpn)
                (update_vcap hns) (update_vcap hnp))
            have htr := swap_trace hP s2 G hM1 ((hM1.members _).2 ⟨hAs.isSlot, srcC, hsc2, hsn⟩)
              ((hM1.members _).2 ⟨hAp.isSlot, pivC, hpc2, hpn⟩) (fun h => e1 h.symm) ns np hnse hnpe
            rw [hs3, WP.spec_ok] at htr
            have hdi := swap_delinv_imp hP s2 G hM1 ((hM1.members _).2 ⟨hAs.isSlot, srcC, hsc2, hsn⟩)
              ((hM1.members _).2 ⟨hAp.isSlot, pivC, hpc2, hpn⟩) (fun h => e1 h.symm) ns np hnse hnpe hnsn hnpn
              (by rw [capV_of_capAt hsc2]; exact hshs) (by rw [capV_of_capAt hpc2]; exact hshp)
            rw [hs3, WP.spec_ok] at hdi
            rw [hs3]; simp only [bind_ok]
            rw [WP.spec_ok]
            have hrunI : (Fl4Spec.invokeCnode (Z := Unit)
                (.rotateCall (absCap ns) (absCap np) (ps.bv, sb) (ppv.bv, pb) (pd.bv, db))).run σ1 =
                ({(.ok (), σ')}, False) := by
              unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
              simp only [e3', ↓reduceIte]
              simp only [e3'] at hsw'
              exact run_liftE' hsw'
            refine ⟨.rotateCall (absCap ns) (absCap np) (ps.bv, sb) (ppv.bv, pb) (pd.bv, db), ?_, σ1, hst, σ', G', hrunI,
              hR', hV', hM', hC', hI', hFI', MdbStep.same_left hM hS (hSt (update_ut hns) (update_ut hnp)),
              s2, by simp [invSlots], hs2, htr.1, fun sl hsl => by
                simp only [invSlots, List.mem_cons, List.not_mem_nil, or_false] at hsl
                rcases hsl with rfl | rfl | rfl
                exacts [⟨ps, _, rfl, hps, rfl⟩, ⟨ppv, _, rfl, hpl, rfl⟩, ⟨pd, _, rfl, hpd, rfl⟩],
              fun y hy hne => htr.2.1 y hy (hne _ (by simp [invSlots])) (hne _ (by simp [invSlots])), hdi,
              typedKept_swap hAs.isSlot hAp.isSlot htr.2.1 htr.2.2.1 htr.2.2.2
                (by rw [capV_of_capAt hsc2]; exact hshs) (by rw [capV_of_capAt hpc2]; exact hshp),
              fun hr sl hsl => by
                simp only [invSlots, List.mem_cons, List.not_mem_nil, or_false] at hsl
                rcases hsl with rfl | rfl | rfl
                exacts [⟨ps, rfl, hpsL.same hS rfl⟩, ⟨ppv, rfl, hplL.same hS rfl⟩, ⟨pd, rfl, (hpdL hr).same hS rfl⟩],
              fun σ1' σ'' h1 h2 => by
                have e1 : σ1 = σ1' := nd_single_inj (hst.symm.trans h1)
                subst e1
                have e2 : σ' = σ'' := nd_single_inj (hrunI.symm.trans h2)
                subst e2
                exact utSrc_swap hP hC1 hC' hAs hAp hG'
                  (fun _ _ _ _ h => by
                    rw [htr.2.2.2] at h
                    have hu : isUt pivC = true := by rw [← isUt_of_shape hshp, h]; rfl
                    rw [capV_of_capAt hpc2, ← update_ut hnp hu, h])
                  (fun _ _ _ _ h => by
                    rw [htr.2.2.1] at h
                    have hu : isUt srcC = true := by rw [← isUt_of_shape hshs, h]; rfl
                    rw [capV_of_capAt hsc2, ← update_ut hns hu, h]) htr.2.1,
              vsSlotsT_swap hAs.isSlot hAp.isSlot htr.2.1 htr.2.2.1 htr.2.2.2
                (by rw [capV_of_capAt hsc2]; exact update_vcap hns) (by rw [capV_of_capAt hsc2]; exact update_tabun hns)
                (by rw [capV_of_capAt hpc2]; exact update_vcap hnp) (by rw [capV_of_capAt hpc2]; exact update_tabun hnp)
                (by rw [capV_of_capAt hsc2]; exact update_okey hns hnsn)
                (by rw [capV_of_capAt hpc2]; exact update_okey hnp hnpn)
                (by rw [capV_of_capAt hsc2]; exact update_nat hns) (by rw [capV_of_capAt hpc2]; exact update_nat hnp),
              coverUt_swap hAs.isSlot hAp.isSlot (fun h => e1 h.symm) (capV_of_capAt hsc2) (capV_of_capAt hpc2)
                htr.2.2.1 htr.2.2.2 htr.2.1 hshs hshp (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt srcC = true := by rw [hs]; rfl
                rw [update_ut hns hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩)
                (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt pivC = true := by rw [hs]; rfl
                rw [update_ut hnp hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩),
              cnLive_swap e3.symm (capV_of_capAt hsc2) hsn (capV_of_capAt hpc2) hpn htr.2.2.2 htr.2.2.1 hnsn hnpn hshs hshp,
              nullSrc_swap e3.symm htr.2.2.2 htr.2.2.1 hnsn hnpn⟩
            simp only [hnsan, hnpan, Fl4Spec.NonDetE.whenE, ↓reduceIte, ndE_pure_bind]; rfl

          · have e3' : (ps.bv, sb) ≠ (pd.bv, db) := fun h => e3 (by rw [h])
            simp only [show decide (cslotAddr (ps.bv, sb) ≠ cslotAddr (pd.bv, db)) = true from decide_eq_true e3, ↓reduceIte]
            unfold cdt.ensure_empty_slot
            simp only [slot_cap_eq, hcd, bind_ok]
            have hee := ensureEmpty_run (pd.bv, db) σ hgd
            have hun : (Fl4Spec.NonDetE.unlessE ((ps.bv, sb) = (pd.bv, db)) (Fl4Spec.ensureEmpty (pd.bv, db)) :
                Fl4Spec.SEMonad Unit Unit).run σ = (Fl4Spec.ensureEmpty (Z := Unit) (pd.bv, db)).run σ := by
              simp only [Fl4Spec.NonDetE.unlessE, e3', ↓reduceIte]
            by_cases hdn : cd = .Null
            swap
            · rw [cap_is_null_ne hdn]
              simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
                core.convert.FromSame.from, bind_tc_ok]
              rw [WP.spec_ok]
              have : ad ≠ .nullCap := fun h => hdn ((hcad.null_iff).1 h)
              simp only [this, ↓reduceIte] at hee
              exact ⟨rfl, .deleteFirst, run_bind_error (hun.trans hee) _, trivial⟩
            subst hdn
            have hadn : ad = .nullCap := (hcad.null_iff).2 rfl
            simp only [hadn, ↓reduceIte] at hee
            rw [cap_is_null_null]
            simp only [bind_ok, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
            refine InvPost.congr (run_bind_ok (hun.trans hee) _) ?_
            rw [hsc]; simp only [bind_ok]
            refine InvPost.congr (run_bind_ok (run_liftE hgs) _) ?_
            by_cases hsn : srcC = .Null
            · subst hsn
              have : srcA = .nullCap := (hsca.null_iff).2 rfl
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, cnode.missing_source, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
                bind_tc_ok]
              rw [WP.spec_ok]
              refine ⟨rfl, .failedLookup true (.missingCapability a7.val), ?_, show true = true ∧ a7.val = a7.val from ⟨rfl, rfl⟩⟩
              simp only [this, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hsan : srcA ≠ .nullCap := fun h => hsn ((hsca.null_iff).1 h)
            rw [cap_is_null_ne hsn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, hpc]
            refine InvPost.congr (run_bind_ok (run_whenE_false hsan _ σ) _) (InvPost.congr (run_bind_ok (run_liftE hgp) _) ?_)
            by_cases hpn : pivC = .Null
            · subst hpn
              have : pivA = .nullCap := (hpca.null_iff).2 rfl
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, cnode.missing_source, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
                bind_tc_ok]
              rw [WP.spec_ok]
              refine ⟨rfl, .failedLookup false (.missingCapability a4.val), ?_, show false = false ∧ a4.val = a4.val from ⟨rfl, rfl⟩⟩
              simp only [this, Fl4Spec.NonDetE.whenE, ↓reduceIte, Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hpan : pivA ≠ .nullCap := fun h => hpn ((hpca.null_iff).1 h)
            rw [cap_is_null_ne hpn]
            obtain ⟨ns, hns, hnsw, hnsa, hnse, hnscv, -⟩ := update_rel true a5 srcC hsw hse
            obtain ⟨np, hnp, hnpw, hnpa, hnpe, hnpcv, -⟩ := update_rel true a2 pivC hpw hpe
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch]
            simp only [uncurry_apply_pair, hsc, hpc, hns, hnp, bind_ok]
            rw [← hsca.abs, ← hpca.abs] at *
            refine InvPost.congr (run_bind_ok (run_whenE_false hpan _ σ) _) (InvPost.congr (run_bind_ok (run_returnOk _ σ) _)
              (InvPost.congr (run_bind_ok (run_returnOk _ σ) _) ?_))
            rw [← hnsa, ← hnpa]
            by_cases hnsn : ns = .Null
            · subst hnsn
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, error.illegal]
              rw [WP.spec_ok]
              refine ⟨rfl, .illegalOperation, ?_, trivial⟩
              simp only [show absCap capability.Cap.Null = .nullCap from rfl, Fl4Spec.NonDetE.whenE, ↓reduceIte,
                Fl4Spec.NonDetE.throwError, ndE_throw_bind]; rfl
            have hnsan : absCap ns ≠ .nullCap := fun h => hnsn ((show CapRel ns (absCap ns) from ⟨hnsw, rfl⟩).null_iff.1 h)
            rw [cap_is_null_ne hnsn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
            by_cases hnpn : np = .Null
            · subst hnpn
              rw [cap_is_null_null]
              simp only [bind_ok, ↓reduceIte, error.illegal]
              rw [WP.spec_ok]
              refine ⟨rfl, .illegalOperation, ?_, trivial⟩
              simp only [hnsan, show absCap capability.Cap.Null = .nullCap from rfl, Fl4Spec.NonDetE.whenE, ↓reduceIte,
                Fl4Spec.NonDetE.throwError, ndE_throw_bind, ndE_pure_bind]; rfl
            have hnpan : absCap np ≠ .nullCap := fun h => hnpn ((show CapRel np (absCap np) from ⟨hnpw, rfl⟩).null_iff.1 h)
            rw [cap_is_null_ne hnpn]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨hshs, hbds⟩ := update_shape hns hnsn
            obtain ⟨hshp, hbdp⟩ := update_shape hnp hnpn
            have hbds' : badgeF ns = badgeF srcC := by rcases hbds with h | ⟨-, h⟩; exact h; cases h
            have hbdp' : badgeF np = badgeF pivC := by rcases hbdp with h | ⟨-, h⟩; exact h; cases h
            -- set_thread_state
            obtain ⟨s2, hs2, hS⟩ := spec_exists hts
            rw [hs2]; simp only [bind_ok, slot_eq_eq]
            obtain ⟨tcb, hk, -⟩ := hR.tcb ct htcb
            rw [← hcur] at hk
            obtain ⟨σ1, hst, hR1, hV1, hM1, hC1, -, hio1⟩ := restart_rel hR hV hM hC hS hk .restart
            have hI1 := MdbInv.of_same hM hI hS
            have hFI1 := hFI.of_same hM hS (ksub_of_eq (setThreadState_nks _ _) hst)
            have hsc2 : capAt (L.mem s2) (cslotAddr (ps.bv, sb)) = ok srcC := by rw [hS.capAt hAs.isSlot, hsc]
            have hpc2 : capAt (L.mem s2) (cslotAddr (ppv.bv, pb)) = ok pivC := by rw [hS.capAt hAp.isSlot, hpc]
            simp only [show decide (cslotAddr (ps.bv, sb) = cslotAddr (pd.bv, db)) = false from decide_eq_false e3, Bool.false_eq_true, ↓reduceIte]
            have hdc2 : capAt (L.mem s2) (cslotAddr (pd.bv, db)) = ok .Null := by rw [hS.capAt hAd.isSlot, hcd]
            have hpm : cslotAddr (ppv.bv, pb) ∈ G.chains.flatten := (hM1.members _).2 ⟨hAp.isSlot, pivC, hpc2, hpn⟩
            have hdm : cslotAddr (pd.bv, db) ∉ G.chains.flatten := by
              intro h; obtain ⟨-, c0, h0, hn⟩ := (hM1.members _).1 h; rw [hdc2] at h0; exact hn (eq_of_ok_eq h0).symm
            obtain ⟨s3, hs3, σ2, G2, hmv1, hR2, hV2, hM2, hC2, hI2, hFI2, hSt2, hG2⟩ := spec_exists
              (move_full_finG th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hFI1 hpl hpd rfl rfl hpc2 hpn hdc2 np (absCap np) ⟨hnpw, rfl⟩
                (hnpcv th hpcv) hnpe hnpn hshp hbdp' (update_okey hnp hnpn) (update_vcap hnp))
            obtain ⟨s3', hs3', hcaps⟩ := spec_exists (move_caps (L := L) hP s2 G hM1 hpm hAd.isSlot hdm np hnpe)
            rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
            rw [hs3]; simp only [bind_ok]
            have hsc3 : capAt (L.mem s3) (cslotAddr (ps.bv, sb)) = ok srcC := by
              rw [hcaps _ hAs.isSlot, if_neg e3, if_neg (fun h => e1 h.symm), hsc2]
            have hpc3 : capAt (L.mem s3) (cslotAddr (ppv.bv, pb)) = ok .Null := by
              rw [hcaps _ hAp.isSlot, if_neg e2, if_pos rfl]
            obtain ⟨s4, hs4, σ', G', hmv2, hR', hV', hM', hC', hI', hFI', hSt, hG'⟩ := spec_exists
              (move_full_finG th s3 σ2 G2 hR2 hV2 hP hM2 hC2 hI2 hFI2 hps hpl rfl rfl hsc3 hsn hpc3 ns (absCap ns) ⟨hnsw, rfl⟩
                (hnscv th hscv) hnse hnsn hshs hbds' (update_okey hns hnsn) (update_vcap hns))
            have htr1 := Vs.move_trace hP s2 G hM1 hpm hAd.isSlot hdm np hnpe
            rw [hs3, WP.spec_ok] at htr1
            have htr2 := Vs.move_trace hP s3 G2 hM2 ((hM2.members _).2 ⟨hAs.isSlot, srcC, hsc3, hsn⟩) hAp.isSlot
              (fun h => by obtain ⟨-, c0, h0, hn⟩ := (hM2.members _).1 h; rw [hpc3] at h0
                           exact hn (eq_of_ok_eq h0).symm) ns hnse
            rw [hs4, WP.spec_ok] at htr2
            have hdi1 := move_delinv_imp hP s2 G hM1 hpm hAd.isSlot hdm np hnpe hnpn
              (by rw [capV_of_capAt hpc2]; exact hshp)
            rw [hs3, WP.spec_ok] at hdi1
            have hdi2 := move_delinv_imp hP s3 G2 hM2 ((hM2.members _).2 ⟨hAs.isSlot, srcC, hsc3, hsn⟩) hAp.isSlot
              (fun h => by obtain ⟨-, c0, h0, hn⟩ := (hM2.members _).1 h; rw [hpc3] at h0
                           exact hn (eq_of_ok_eq h0).symm) ns hnse hnsn (by rw [capV_of_capAt hsc3]; exact hshs)
            rw [hs4, WP.spec_ok] at hdi2
            rw [hs4]; simp only [bind_ok]
            rw [WP.spec_ok]
            have hrunI : (Fl4Spec.invokeCnode (Z := Unit)
                (.rotateCall (absCap ns) (absCap np) (ps.bv, sb) (ppv.bv, pb) (pd.bv, db))).run σ1 =
                ({(.ok (), σ')}, False) := by
              unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
              simp only [e3', ↓reduceIte]
              apply run_liftE'
              show (Fl4Spec.capMove _ _ _ >>= fun _ => Fl4Spec.capMove _ _ _) σ1 = _
              rw [nd_bind_one hmv1]; exact hmv2
            refine ⟨.rotateCall (absCap ns) (absCap np) (ps.bv, sb) (ppv.bv, pb) (pd.bv, db), ?_, σ1, hst, σ', G', hrunI,
              hR', hV', hM', hC', hI', hFI',
              (MdbStep.same_left hM hS (hSt2 (update_ut hnp))).trans (hSt (update_ut hns)),
              s2, by simp [invSlots], hs2, ⟨htr2.1.1.trans htr1.1.1, htr2.1.2.1.trans htr1.1.2.1,
                fun b hb hn => (htr2.1.2.2 b hb hn).trans (htr1.1.2.2 b hb hn)⟩, fun sl hsl => by
                simp only [invSlots, List.mem_cons, List.not_mem_nil, or_false] at hsl
                rcases hsl with rfl | rfl | rfl
                exacts [⟨ps, _, rfl, hps, rfl⟩, ⟨ppv, _, rfl, hpl, rfl⟩, ⟨pd, _, rfl, hpd, rfl⟩],
              fun y hy hne => (htr2.2.1 y hy (hne _ (by simp [invSlots])) (hne _ (by simp [invSlots]))).trans
                (htr1.2.1 y hy (hne _ (by simp [invSlots])) (hne _ (by simp [invSlots]))),
              fun hD => hdi2 (hdi1 hD),
              (typedKept_mov hAp.isSlot htr1.2.1 htr1.2.2.1 htr1.2.2.2 (by rw [capV_of_capAt hpc2]; exact hshp)).trans
                (typedKept_mov hAs.isSlot htr2.2.1 htr2.2.2.1 htr2.2.2.2 (by rw [capV_of_capAt hsc3]; exact hshs)),
              fun hr sl hsl => by
                simp only [invSlots, List.mem_cons, List.not_mem_nil, or_false] at hsl
                rcases hsl with rfl | rfl | rfl
                exacts [⟨ps, rfl, hpsL.same hS rfl⟩, ⟨ppv, rfl, hplL.same hS rfl⟩, ⟨pd, rfl, (hpdL hr).same hS rfl⟩],
              fun σ1' σ'' h1 h2 => by
                have e1 : σ1 = σ1' := nd_single_inj (hst.symm.trans h1)
                subst e1
                have e2 : σ' = σ'' := nd_single_inj (hrunI.symm.trans h2)
                subst e2
                exact (utSrc_swap hP hC1 hC2 hAp hAd hG2 (fun _ _ _ _ h => by rw [htr1.2.2.2] at h; cases h)
                  (fun _ _ _ _ h => by
                    rw [htr1.2.2.1] at h
                    have hu : isUt pivC = true := by rw [← isUt_of_shape hshp, h]; rfl
                    rw [capV_of_capAt hpc2, ← update_ut hnp hu, h]) htr1.2.1).trans
                  (utSrc_swap hP hC2 hC' hAs hAp hG' (fun _ _ _ _ h => by rw [htr2.2.2.2] at h; cases h)
                  (fun _ _ _ _ h => by
                    rw [htr2.2.2.1] at h
                    have hu : isUt srcC = true := by rw [← isUt_of_shape hshs, h]; rfl
                    rw [capV_of_capAt hsc3, ← update_ut hns hu, h]) htr2.2.1),
              (vsSlotsT_move hAp.isSlot htr1.2.1 htr1.2.2.1 htr1.2.2.2 (by rw [capV_of_capAt hpc2]; exact update_vcap hnp)
                (by rw [capV_of_capAt hpc2]; exact update_tabun hnp)
                (by rw [capV_of_capAt hpc2]; exact update_okey hnp hnpn)
                (by rw [capV_of_capAt hpc2]; exact update_nat hnp)).trans
                (vsSlotsT_move hAs.isSlot htr2.2.1 htr2.2.2.1 htr2.2.2.2 (by rw [capV_of_capAt hsc3]; exact update_vcap hns)
                (by rw [capV_of_capAt hsc3]; exact update_tabun hns)
                (by rw [capV_of_capAt hsc3]; exact update_okey hns hnsn)
                (by rw [capV_of_capAt hsc3]; exact update_nat hns)),
              ⟨(coverUt_mov hAd.isSlot (fun e => hdm (e ▸ hpm)) (capV_of_capAt hpc2) (capV_of_capAt hdc2)
                htr1.2.2.1 htr1.2.2.2 htr1.2.1 hshp hAp.isSlot (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt pivC = true := by rw [hs]; rfl
                rw [update_ut hnp hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩)).1.trans
                (coverUt_mov hAp.isSlot (fun h => e1 h.symm) (capV_of_capAt hsc3) (capV_of_capAt hpc3)
                htr2.2.2.1 htr2.2.2.2 htr2.2.1 hshs hAs.isSlot (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt srcC = true := by rw [hs]; rfl
                rw [update_ut hns hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩)).1,
              (coverUt_mov hAd.isSlot (fun e => hdm (e ▸ hpm)) (capV_of_capAt hpc2) (capV_of_capAt hdc2)
                htr1.2.2.1 htr1.2.2.2 htr1.2.1 hshp hAp.isSlot (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt pivC = true := by rw [hs]; rfl
                rw [update_ut hnp hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩)).2.trans
                (coverUt_mov hAp.isSlot (fun h => e1 h.symm) (capV_of_capAt hsc3) (capV_of_capAt hpc3)
                htr2.2.2.1 htr2.2.2.2 htr2.2.1 hshs hAs.isSlot (fun _ _ _ _ hc _ _ hs => by
                have hu : isUt srcC = true := by rw [hs]; rfl
                rw [update_ut hns hu, hs] at hc; cases hc; exact ⟨rfl, Or.inl le_rfl⟩)).2⟩,
              cnLive_rot (capV_of_capAt hsc2) hsn (capV_of_capAt hpc2) hpn (capV_of_capAt hdc2) htr2.2.2.2 htr2.2.2.1
                ((htr2.2.1 _ hAd.isSlot (fun h => e3 h.symm) (fun h => e2 h.symm)).trans htr1.2.2.1) hnsn hnpn hshs hshp,
              nullSrc_rot e3' htr2.2.2.1
                ((htr2.2.1 _ hAd.isSlot (fun h => e3 h.symm) (fun h => e2 h.symm)).trans htr1.2.2.1) hnsn hnpn⟩
            simp only [hnsan, hnpan, Fl4Spec.NonDetE.whenE, ↓reduceIte, ndE_pure_bind]; rfl


/-- **CNode Rotate**, decode and invoke: FL4's `cnode::decode` at label
`CNodeRotate` against l4v's `decode_cnode_invocation` (whose target
lookup and tail are the Rotate branch), then `set_thread_state Restart`
and `invoke_cnode` (`cap_swap` when the source is the destination,
otherwise the two `cap_move`s). -/
theorem cnode_rotate_refines {A : Type} (arI : machine.Arch A) (th : TypedHeap) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeRotate)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (cap : capability.Cap) (a : Fl4Spec.Cap) (hca : CapRel cap a) (hcv : CapValid th cap)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 x1 : U64)
    (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (hx1 : Aeneas.Std.Array.index_usize extra 1#usize = ok x1)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel2 th (L.mem s) x0 x1 excaps)
    (hI : MdbInv (L.mem s) G) (hFI : FinInv th (L.mem s) σ G)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb) :
    cnode.decode st arI s ar fl4_abi.label.CNodeRotate length cap buf extra ⦃ res =>
      InvPost (L := L) th σ G (Fl4Spec.decodeCnodeInvocation slbl (args.map UScalar.bv) a excaps) s
        (res.1, res.2.1) (CnTrace (L := L) th ct σ cap s) ∧ res.2.2 = ar ⦄ := by
  have hin : Fl4Spec.genInvocationType slbl ∈
      Fl4Spec.GenInvocationLabels.uptoEnum .cnodeRevoke .cnodeRotate := by rw [hlbl]; decide
  unfold cnode.decode
  have n1 : ¬ fl4_abi.label.CNodeRotate < fl4_abi.label.CNodeRevoke := by
    have := lbl_revoke_val; have := lbl_rotate_val; scalar_tac
  have n2 : ¬ fl4_abi.label.CNodeRotate > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
  rw [if_neg n1, if_neg n2]
  by_cases h2 : length < 2#u64
  · rw [if_pos h2]
    simp only [error.truncated, bind_ok]
    rw [WP.spec_ok]
    exact ⟨⟨rfl, .truncatedMessage, decode_short _ _ _ σ hin _ (by simp; scalar_tac), trivial⟩, rfl⟩
  rw [if_neg h2]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | [_] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: rest => exact ⟨y0, y1, rest, rfl⟩
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), bind_ok]
  unfold cspace.lookup_target_slot
  obtain ⟨r1, hr1, e1, he1, hrel1⟩ := spec_exists
    (lookup_slot_for_cnode_op_refines (Z := Unit) th s σ hR hV false cap a hca hcv y0 y1)
  rw [hr1]; simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have hlt : (Fl4Spec.lookupTargetSlot (Z := Unit) a (Fl4Spec.dataToCptr y0.bv) (Fl4Spec.dataToNat y1.bv)).run σ =
      ({(e1, σ)}, False) := he1
  have hdec := decode_lookup slbl a excaps hin y0.bv y1.bv (rest.map UScalar.bv)
  simp only [List.map_cons]
  rw [hdec]
  cases r1 with
  | Err e =>
    cases e1 with
    | ok _ => exact hrel1.elim
    | error e' =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      rw [WP.spec_ok]
      exact ⟨⟨rfl, e', run_bind_error hlt _, hrel1⟩, rfl⟩
  | Ok dest =>
    cases e1 with
    | error _ => exact hrel1.elim
    | ok dsl =>
      obtain ⟨rfl, pd, hpd1, hpd, hcrd⟩ := hrel1
      have g1 : fl4_abi.label.CNodeRotate ≥ fl4_abi.label.CNodeCopy := by
        have := lbl_copy_val; have := lbl_rotate_val; scalar_tac
      have g2 : ¬ fl4_abi.label.CNodeRotate ≤ fl4_abi.label.CNodeMutate := by
        have := lbl_mutate_val; have := lbl_rotate_val; scalar_tac
      have k1 : ¬ fl4_abi.label.CNodeRotate = fl4_abi.label.CNodeRevoke := by rw [u64_eq_iff]; simp
      have k2 : ¬ fl4_abi.label.CNodeRotate = fl4_abi.label.CNodeDelete := by rw [u64_eq_iff]; simp
      have k3 : ¬ fl4_abi.label.CNodeRotate = fl4_abi.label.CNodeCancelBadgedSends := by rw [u64_eq_iff]; simp
      simp only [g1, g2, k1, k2, k3, ↓reduceIte, bind_ok]
      obtain ⟨⟨r2, s2⟩, hdc, hpost⟩ := spec_exists
        (decode_rotate_rel th s σ G hR hV hP hM hC slbl hlbl length buf ct hct (y0 :: y1 :: rest) hlen
          (by simp) hargs extra x0 x1 hx0 hx1 excaps hex hI hFI hact hcur htcb dsl pd hpd1 hpd cap
          (fun hr => DestLive.of_cnRef hcrd hr))
      rw [hdc]; simp only [bind_ok, uncurry_apply_pair]
      rw [WP.spec_ok]
      simp only [List.map_cons, List.drop_succ_cons, List.drop_zero] at hpost
      exact ⟨InvPost.of_run (run_bind_ok hlt _) hpost, rfl⟩


end

end

end Fl4Proofs.P3
