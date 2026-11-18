/-
P3 (DESIGN.md §9), untyped: **`untyped::decode` with the retype it runs
refines l4v `decode_untyped_invocation`, `set_thread_state Restart` and
`invoke_untyped`**, for the non-arch types but the TCB (`untyped_retype_refines`),
under the untyped invariant (`UtInv`), the free region being free and zero,
and, when the untyped cap has no children (so `decode` asks for a reset), it
being unused (free index 0; the reset of a used untyped region, l4v
`reset_untyped_cap`, is not covered).
-/
import Fl4Proofs.P3.UntypedSuccess
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

attribute [local step] tcb_state_spec' sc_is_null_spec' action_spec' set_action_spec' cur_thread_spec'
  is_schedulable_spec'

/-- `s'` differs from `s` at most in the words `a` and `b`. -/
def Frame2 (s s' : S) (a b : U64) : Prop :=
  ∀ w : U64, P1.Aligned w → w.val ≠ a.val → w.val ≠ b.val → L.mem s' w = L.mem s w

/-- **`set_thread_state` writes only the TCB's state word and the current
core's scheduler-action word.** -/
theorem set_thread_state_frame (s : S) (t v : U64) (hst : P1.Aligned (stA t))
    (hact : P1.Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    sched.set_thread_state st s t v ⦃ s' => Frame2 (L := L) s s' (stA t)
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals
    unfold Frame2
    intro w hw h1 h2
    subst_vars
  all_goals first
    | exact L.mem_wr_ne hst hw (Ne.symm h1)
    | skip
  all_goals
    have e : L.nodeAt (L.wr s (stA t) v) (L.cpu (L.wr s (stA t) v)) layout.node.SCHED_ACTION =
        L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION := by simp
    rw [e, L.mem_wr_ne hact hw (Ne.symm h2), L.mem_wr_ne hst hw (Ne.symm h1)]

theorem sts_ksb_ret (s : S) (t v : U64) :
    sched.set_thread_state st s t v ⦃ s' => L.ksb s' = L.ksb s ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals subst_vars; simp

end

theorem UtInv.of_same {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th m G)
    (hU : UtInv m G) (hS : SlotsSame th m m') : UtInv m' G := by
  have hsl : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hc : ∀ x, x ∈ G.chains.flatten → capV m' x = capV m x := fun x hx => hS.capV (hsl x hx)
  refine ⟨fun x hx => ?_, fun x hx p sb fi d hcx y hy => ?_, fun x hx p sb fi d hcx y hy => ?_,
    fun x hx y hy hne p sb fi fi' d d' h1 h2 => ?_, fun x hx p sb fi d hcx => ?_,
    fun x hx p sb fi d hcx y hy hyx hp hd => ?_⟩
  · rw [hc x hx]; exact hU.reg x hx
  · rw [hc x hx] at hcx; rw [hc y (desc_mem hM hy).1]; exact hU.inc x hx p sb fi d hcx y hy
  · rw [hc x hx] at hcx ⊢; rw [hc y hy]; exact hU.noov x hx p sb fi d hcx y hy
  · rw [hc x hx] at h1; rw [hc y hy] at h2; exact hU.excl x hx y hy hne p sb fi fi' d d' h1 h2
  · rw [hc x hx] at hcx; exact hU.fib x hx p sb fi d hcx
  · rw [hc x hx] at hcx hd; rw [hc y hy] at hp hd; exact hU.drange x hx p sb fi d hcx y hy hyx hp hd

/-- The source slot of an untyped invocation. -/
def invSrc : Fl4Spec.UntypedInvocation → U64
  | .retype sl _ _ _ _ _ _ _ => cslotAddr sl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The result of an untyped invocation that `decode` hands to `retype`:
the spec's `set_thread_state Restart` and `invoke_untyped` (object sizes
`bitsApi`) have single outcomes related to FL4's, with `ksb` kept (`ks` before) and what the retype did
exposed (`RetExp`) with its write frame from the state `s0` before the
restart (`RetFrameI`). -/
def RetPost {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ar : A')
    (arI : machine.Arch A') (s0 : S) (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ks : U64)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ σ' G' th', (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 = ({(.ok (), σ')}, False) ∧
      Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
      MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = ks ∧
      ∃ A k w dslot cj, RetExp th th' m (L.mem res.2.1) G G' A k w dslot cj (invSrc inv) ∧
        RetFrameI (L := L) arI ar th G s0 bitsApi inv A k w dslot cj th' res

/-- **The success continuation of `decode`** (`set_thread_state Restart`,
then `retype`) satisfies `RetPost`, for the types 0, 2..7 and 9..13. -/
theorem retype_cont {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (ct : U64) (hcur : σ.curThread = ct.bv) (hct : sched.cur_thread st s = ok ct) (htcb : th ct = some .tcb)
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
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hctx : RetCtx (L := L) th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      RetPost (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
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
  obtain ⟨s2k, hs2k, hk2⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
  rw [hs2] at hs2k; cases eq_of_ok_eq hs2k
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
  have hfiv' : fiv = fi := by
    rw [hfiv]
    cases hrs : reset
    · rfl
    · rw [hrs] at hreset
      have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
      exact (UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl))
  subst hfiv'
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hA1, hWA2, hA3, -⟩ := retype_region p fiv sb.val (zOf nt.val us.val) win.val hsb (by omega) hpal hpfit hfi hw1 hmem
  have hsl : ∀ a, IsSlot th a → a.val + 32 ≤ (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ∨
      (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hfull := retype_full (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 horig1 hpp hidx hcap1 hpal hpfit
    hfi hhigh nt us t ht hn hus hz47 hsc hct0 hdest (by omega) off win hwin hw1 hmem hempty1 hfree (fun _ => hzero1) (fun hd => (dev_nt ht (hdevc hd)).2.1) bitsApi hb
  have hRB0 : reset = true → (∃ p sb d, capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 d)) ∧
      untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), s2, ar) := by
    intro hrs
    have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by rw [hrs] at hreset; simpa using hreset.symm
    have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
    rw [hf0] at hcap1
    exact ⟨⟨_, _, _, hcap1⟩, reset_untyped_unused arI s2 ar _ hcap1⟩
  have hpost : ∀ res, (res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧ (dev = false → ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val)) ∧
        (FinInv th (L.mem s2) σ1 G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s2 ∧
        WFrame (L := L) s2 res.2.1 (SlotSpan th) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s2) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
          A = (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX th th' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC th dslot w) →
      (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) reset p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 =
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 →
      RetPost (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res := by
    rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w, dslot,
      cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩ he
    exact ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', th', he.trans hrun, hP', hR', hV', hM', hC', hI', hU',
      MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)),
      by rw [hks, hk2], _, _, _, dslot, cj, hE.same_left hM hSS,
      ⟨⟨ct, s2, hct, hs2, Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s2, th, _, _, Or.inl ⟨rfl, rfl, rfl, rfl, hRB0⟩, le_rfl, le_rfl, hthx.2, fun a h => h, ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC, hWf.mono fun v hv => Or.inl (Or.inr hv),
        fun _ => winZero_of_slots hWf (fun w hw h1' h2' => hzero1 w hw (by omega) (by omega)) hsl _,
        fun hT => absurd (objTypeOf_tcb (hT ▸ ht)) (by omega)⟩⟩, fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
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

/-- **FL4's untyped `Retype` refines l4v's** (`decode_untyped_invocation`,
`set_thread_state Restart`, `invoke_untyped`; `Z = Unit`), for the object
types Untyped, endpoint, notification, CNode, scheduling context and reply:
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
theorem untyped_retype_refines [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (ar : A')
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hnt : ∀ x, args.head? = some x → x.val = 0 ∨ (2 ≤ x.val ∧ x.val ≤ 13 ∧ x.val ≠ 8))
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
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64) :
    untyped.decode st arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.decodeUntypedInvocation slbl (args.map UScalar.bv) (pp.bv, idx) (absCap (.Untyped p sb fi dev))
        excaps) s ar (RetPost (L := L) th (L.mem s) G σ ar arI s Fl4Spec.objBitsApi (L.ksb s)) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refines arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    (fun x hx => Or.inl (by have := hnt x hx; omega))
    (fun x hx => by have := hnt x hx; omega) _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  have hn := hnt nt hnt0
  have hb : Fl4Spec.objBitsApi t us.val = zOf nt.val us.val := (objTypeOf_some hctx.ty (by omega) us.val).2.1
  exact retype_cont arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx hcap hpal hpfit hfi hhigh
    hactZ hfree hzero hunused Fl4Spec.objBitsApi nt us dest off win t r reset fiv hn hb hctx

end

end
end Fl4Proofs.P3
