/-
P3 (DESIGN.md §9), untyped: **`Retype` end to end for every non-arch type,
TCBs included, against FL4's spec** (`fl4DecodeUntypedInvocation`,
`set_thread_state Restart`, `fl4InvokeUntyped`: 4 KiB TCBs,
Fl4Spec/Ext/TcbSize.lean).
-/
import Fl4Proofs.P3.UntypedTcbLoop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] tcb_state_spec' sc_is_null_spec' action_spec' set_action_spec' cur_thread_spec'
  is_schedulable_spec'

theorem set_thread_state_ksb (s : S) (t v : U64) :
    sched.set_thread_state st s t v ⦃ s' => L.ksb s' = L.ksb s ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals subst_vars; simp

theorem retype_cont_all {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64)
    (hn : nt.val ≤ 13 ∧ nt.val ≠ 8) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val + fi.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hctx : RetCtx (L := L) th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      RetPost (L := L) th (L.mem s) G σ ar bitsApi (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  obtain ⟨ht, ⟨hus, hz47, hsB, hsC, hsD⟩, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, hempty, hreset, hfiv, -, hmem, hdevc⟩ := hctx
  -- set_thread_state
  have htf := hP.fits ct _ htcb
  have hta := hP.align ct _ htcb
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
  obtain ⟨s2', hs2', hF⟩ := spec_exists (set_thread_state_frame (L := L) s ct sched.TS_RESTART
    (by unfold P1.Aligned; rw [hstv]; omega) hact.1)
  rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
  rw [hs2]; simp only [bind_ok]
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hSS (t := ct.bv) hkt .restart
  have hI1 := MdbInv.of_same hM hI hSS
  have hU1 := UtInv.of_same hM hU hSS
  have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
    rw [hSS.capAt (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩)]; exact hcap
  have hempty1 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    rw [hSS.capAt ⟨dest, i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩]; exact hempty i h1 h2
  have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hF w hw (by
      rw [hstv]; intro e
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hfree ct _ htcb with h | h <;> omega) (by
      intro e; exact hactZ (by rw [← e]; exact ⟨h1, h2⟩))]
    exact hzero w hw h1 h2
  have horig1 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
  have hct0 : nt.val = 4 → us.val ≠ 0 := fun h e => hsB ⟨h, e⟩
  obtain ⟨s2', hs2', hk2⟩ := spec_exists (set_thread_state_ksb (L := L) s ct sched.TS_RESTART)
  rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
  have hDW2 : L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hk2 _ _
  have hDWm2 : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hF _ hDWal hDWne.1 hDWne.2
  have hfiv' : fiv = fi := by
    rw [hfiv]
    cases hrs : reset
    · rfl
    · rw [hrs] at hreset
      have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
      exact (UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl))
  subst hfiv'
  have hfull : untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧ (dev = false → ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val)) ∧
        (FinInv th (L.mem s2) σ1 G → FinInv th' (L.mem res.2.1) σ' G') ⦄ := by
    by_cases h1 : nt.val = 1
    · refine WP.spec_mono (retype_full_tcb (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 horig1 hpp hidx hcap1
        hpal hpfit hfi hhigh nt us t ht h1 hus hdest (by omega) off win hwin hw1 hmem hempty1 hfree hzero1
        (by rw [hDW2]; exact hDWal) (by rw [hDW2]; exact hDWobj) (by rw [hDW2]; exact hDWreg)
        (by rw [hDW2, hDWm2]; exact hhead) bitsApi hb) ?_
      rintro res ⟨h1, h2, σ', G', th', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      exact ⟨h1, h2, σ', G', th', h3, h4, h5, h6, h7, h8, h9, h10, fun _ => h11, h12⟩
    · exact retype_full (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 horig1 hpp hidx hcap1 hpal hpfit
        hfi hhigh nt us t ht (by omega) hus hz47 hsc hct0 hdest (by omega) off win hwin hw1 hmem hempty1 hfree (fun _ => hzero1)
        (fun hd => (dev_nt ht (hdevc hd)).2.1) bitsApi hb
  have hpost : ∀ res, (res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧ (dev = false → ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val)) ∧
        (FinInv th (L.mem s2) σ1 G → FinInv th' (L.mem res.2.1) σ' G')) →
      (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) reset p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 =
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 →
      RetPost (L := L) th (L.mem s) G σ ar bitsApi (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res := by
    rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin⟩ he
    exact ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', th', he.trans hrun, hP', hR', hV', hM', hC', hI', hU',
      MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1))⟩
  rcases Bool.eq_false_or_eq_true reset with hrs | hrs <;> subst hrs
  · have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
    have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
    have hcap0 := hcap1; rw [hf0] at hcap0
    rw [retype_reset_unused (L := L) arI s2 ar _ _ nt us dest off win dev hcap0]
    have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 = ({(.untypedCap dev p.bv sb.val 0, σ1)}, False) := by
      obtain ⟨c, a, hc, hca, hg⟩ := hR1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
      rw [hcap0] at hc; have := eq_of_ok_eq hc; subst this
      rw [hg, hca.abs]; rfl
    exact WP.spec_mono hfull (fun res h => hpost res h (invokeUntyped_reset_unused bitsApi _ _ _ t us.val _ dev σ1 hg))
  · exact WP.spec_mono hfull (fun res h => hpost res h rfl)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's untyped `Retype` refines FL4's spec** (l4v's with 4 KiB TCBs:
`fl4DecodeUntypedInvocation`, `set_thread_state Restart`, `fl4InvokeUntyped`;
`Z = Unit`), for every non-arch type (Untyped, TCB, endpoint, notification,
CNode, scheduling context, reply), with, for TCBs, hypotheses on the core-0
debug list (its head word aligned, outside the old slots, the free region,
the state and scheduler words, holding 0 or an old TCB):
`decode` ends with the error the spec's decode throws (state unchanged), or
the spec decodes an invocation and `RetPost` holds: single spec outcomes,
related to FL4's result for a grown typed heap, with the MDB invariant kept.

Hypotheses beyond the CSpace relation (all on the state, explicit): the
untyped invariant `UtInv`; the untyped cap aligned to its size, not
wrapping, in the kernel half, its free index at most its size; its free
region free (`RegionFree`) and zero (`ZeroRegion`); the current core's
scheduler-action word outside it; only existing slots original (`horig`);
and an untyped cap without children unused (`hunused`, as the reset of a
used region is not covered). -/
theorem untyped_retype_refines_fl4 {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (ar : A')
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val ≤ 13 ∧ x.val ≠ 8)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hactZ : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val + fi.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))) :
    untyped.decode st arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocation slbl (args.map UScalar.bv) (pp.bv, idx)
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPost (L := L) th (L.mem s) G σ ar Fl4Spec.fl4ObjBitsApi) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refines_fl4 arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    (fun x hx => Or.inl (by have := hnt x hx; omega))
    _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  have hn := hnt nt hnt0
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hctx.ty us.val).2.1
  exact retype_cont_all arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur htcb hact hpp hidx hcap hpal hpfit hfi
    hhigh hactZ hfree hzero hunused Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv hn hb hDWal hDWobj hDWreg
    hDWne hhead hctx

end

end
end Fl4Proofs.P3
