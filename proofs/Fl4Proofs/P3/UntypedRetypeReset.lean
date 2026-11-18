/-
P3 (DESIGN.md §9), untyped: **`Retype` end to end with the reset of a used
untyped region**, against FL4's spec: the spec is nondeterministic when it
resets (its preemption points), so the result is no failure and an outcome
of FL4's kind (`RetPostN`), for every non-arch type, TCBs included. It
drops `hunused` of `untyped_retype_refines_fl4` for hypotheses on the
region being reset.
-/
import Fl4Proofs.P3.UntypedResetRetype
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The result of an untyped invocation (nondeterministic): the spec's
`set_thread_state Restart` and then `invoke_untyped` do not fail, and have
an outcome of FL4's kind (done, or preempted in the reset) whose CSpace
parts are related to FL4's result for some typed heap and ghost tree, with
`MdbInv` and `UtInv`. -/
def RetPostN {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit)
    (arI : machine.Arch A') (ar : A') (s0 : S)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ks : U64)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun _ => True) ∧
    ∃ e σ' G' th', ((res.1 = .Ok () ∧ e = .ok ()) ∨ (res.1 = .Err .Preempted ∧ e = .error ())) ∧
      NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun y => y.1 = e ∧ KSame σ' y.2) ∧
      Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
      MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = ks ∧
      ∃ A k w dslot cj, RetExp th th' m (L.mem res.2.1) G G' A k w dslot cj (invSrc inv) ∧
        RetFrameI (L := L) arI ar th G s0 bitsApi inv A k w dslot cj th' res

theorem RetPost.toN {A' : Type} {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit} {ar : A'}
    {arI : machine.Arch A'} {s0 : S} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {ks : U64}
    {inv : Fl4Spec.UntypedInvocation} {res : core.result.Result Unit error.Exc × S × A'}
    (h : RetPost (L := L) th m G σ ar arI s0 bitsApi ks inv res) : RetPostN (L := L) th m G σ arI ar s0 bitsApi ks inv res := by
  obtain ⟨h1, -, σ1, hst, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, hE⟩ := h
  exact ⟨σ1, hst, nsat_det hrun trivial, .ok (), σ', G', th', Or.inl ⟨h1, rfl⟩, nhas_det hrun ⟨rfl, KSame.refl _⟩,
    hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, hE⟩

/-- **The success continuation of `decode`, resets included** (for the
types 0..6): `RetPostN`. With no reset, or a reset of an unused region, as
`retype_cont_all`; with the reset of a used region, `retype_reset_full` /
`retype_reset_tcb` after `set_thread_state`. -/
theorem retype_cont_allN {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
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
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    -- the reset of a used region
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64)
    (hn : nt.val ≤ 13 ∧ nt.val ≠ 8) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
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
      RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  by_cases hcase : reset = true ∧ fi.val ≠ 0
  case neg =>
    have hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0 := by
      intro hnc
      by_contra hf
      exact hcase ⟨by rw [hctx.resetEq]; simpa using hnc, hf⟩
    refine WP.spec_mono (retype_cont_all (L := L) arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx
      hcap hpal hpfit hfi hhigh (fun h => hactZ ⟨by omega, h.2⟩) hfree hzero hunused bitsApi nt us dest off win t r
      reset fiv hn hb hDWal hDWobj (fun h => hDWreg ⟨by omega, h.2⟩) hDWne hhead hctx) (fun res h => h.toN)
  obtain ⟨hrs, hfi0⟩ := hcase
  have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by
    have := hctx.resetEq; rw [hrs] at this; simpa using this.symm
  obtain ⟨horigR, hcnR, hheadR⟩ := hRst hnc hfi0
  subst hrs
  have hfv : fiv = 0#u64 := by rw [hctx.fidx]; rfl
  subst hfv
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
      intro e; exact hactZ (by rw [← e]; exact ⟨by omega, h2⟩))]
    exact hzero w hw h1 h2
  have horig1 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by omega
  have hct0 : nt.val = 4 → us.val ≠ 0 := fun h e => hsB ⟨h, e⟩
  obtain ⟨s2', hs2', hk2⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
  rw [hs2] at hs2'; cases eq_of_ok_eq hs2'
  have hDW2 : L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    nodeAt_ksb hk2 _ _
  have hDWm2 : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hF _ hDWal hDWne.1 hDWne.2
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hnd := nodesc_of_cdt hP hC1 hAs (by rw [hcdt1]; exact hnc)
  have horig2 : ∀ sl, σ1.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl := by
    rw [hio1]; exact horigR
  have hdout := hcnR dest r hdest
  have hPP2 : PPHyp (L := L) arI th p sb (fun t => L.ksb t = L.ksb s2 ∧
      L.mem t (L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS) = L.mem s2 (L.nodeAt s2 0#u64 layout.node.DEBUG_TCBS)) := by
    rw [hDW2]; exact hPP _ _
  have hsbW : sb.val < 64 := capAt_untyped_inv hcap
  have hWR := retype_region p 0#u64 sb.val (zOf nt.val us.val) win.val hsbW (by omega) hpal hpfit (by simp) hw1 hmem
  have hWA2 : (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 := hWR.2.1
  have hWLO : p.val ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat := by have := hWR.1; rwa [show (0#u64 : U64).val = 0 from rfl, Nat.add_zero] at this
  have hWHI : (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val := hWR.2.2.1
  have hp8W : p.val % 8 = 0 := by
    have h8 : 8 ∣ 2 ^ sb.val := by
      have := Nat.pow_dvd_pow 2 (show 3 ≤ sb.val by omega); simpa using this
    have := Nat.mod_mod_of_dvd p.val h8; rw [hpal, Nat.zero_mod] at this; exact this.symm
  have hpost : ∀ res : core.result.Result Unit error.Exc × S × A', (NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
          (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ1 (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s2) σ1 G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s2 ∧ untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s2)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ1 (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s2) σ1 G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s2 ∧
          (∃ t1 a1, untyped.reset_untyped st arI s2 ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧
            WFrame (L := L) t1 res.2.1 (fun v => (t = .tcbObject ∧ TcbLoopW (restrictTh th p.val (p.val + 2 ^ sb.val)) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat win.val
              (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS)) v) ∨
              SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val)) v) ∧
            (dev = false → WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat (2 ^ zOf nt.val us.val) win.val (t = .tcbObject)) ∧
            (t = .tcbObject → (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨ th (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS)) = some .tcb))) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s2) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w))) →
      RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype (pp.bv, idx) true p.bv
        (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
        dev) res := by
    rintro res ⟨hNS, ⟨h1, σ', f, hhas, hRR, hSt, hFr, hks, hrs, hE⟩ | ⟨h1, σ', G', th'', hhas, hP'', hR'', hV'', hM'', hC'',
      hI'', ⟨hU'', hSt⟩, hFin, hks, ⟨t1, a1, hr, hWf, hWZ, hHd⟩, A, k, w, dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩⟩
    · exact ⟨σ1, by rw [hcur]; exact hst1, hNS, .error (), σ', G, _, Or.inr ⟨h1, rfl⟩, hhas, hP.restrict,
        hRR.R, hRR.V, hRR.M, hRR.C, hRR.I, hRR.U, MdbStep.same_left hM hSS hSt,
        fun hFI => hFr (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)), by rw [hks, hk2],
        p.val, 1, 0, fun _ => 0#u64, fun _ => .Null, (hE _ _).same_left hM hSS, ⟨⟨ct, s2, hct, hs2, Or.inl ⟨h1, hrs⟩⟩, fun e => by rw [h1] at e; cases e⟩⟩
    · exact ⟨σ1, by rw [hcur]; exact hst1, hNS, .ok (), σ', G', th'', Or.inl ⟨h1, rfl⟩, hhas, hP'', hR'', hV'', hM'',
        hC'', hI'', hU'', MdbStep.same_left hM hSS hSt,
        fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)), by rw [hks, hk2],
        _, _, _, dslot, cj, hE.same_left hM hSS, ⟨⟨ct, s2, hct, hs2, Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, t1, (restrictTh th p.val (p.val + 2 ^ sb.val)), _, _, Or.inr ⟨a1, p, sb, _, _, hr, hcap1, hcap, hp8W, hsb4,
          (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩, hnd, rfl, rfl, rfl, rfl⟩, hWLO, hWHI,
          by simpa using RegionFree.restrict hN,
          fun a h => h.of_restrict, ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, (fun j hj => let ⟨q, r, hq, i, hi, e⟩ := hdsC j hj; ⟨q, r, (restrictTh_some hq).1, i, hi, e⟩), hWf.mono fun v hv => Or.inl hv, fun ⟨hd, _⟩ => hWZ hd, hHd⟩⟩, fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩
  have hxs : IsSlot th (cslotAddr (pp.bv, idx)) := hAs.isSlot
  by_cases h1 : nt.val = 1
  · have hdf : dev = false := by
      cases hd : dev
      · rfl
      · exact absurd h1 (dev_nt ht (hdevc hd)).1
    subst hdf
    refine WP.spec_mono (retype_reset_tcb (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 hpp hidx hcap1 hfi0 hnd
      hpal hsb4 hhigh hN (hns hnc) hzero1 hrcb hppS hPP2 (by rw [hDW2]; exact hDWal) (by rw [hDW2]; exact hDWobj)
      (by rw [hDW2]; exact hDWreg) (by rw [hDW2, hDWm2]; exact hhead) (by rw [hDW2, hDWm2]; exact hheadR) horig2
      nt us t ht h1 hus hdest hdout (by omega) off win hwin hw1 hmem hempty1 bitsApi hb) fun res h => hpost res ?_
    rcases h with ⟨hNS, hE | ⟨h1', σ', G', th'', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ⟨t1, a1, hr, hw⟩, e11⟩⟩
    · exact ⟨hNS, Or.inl hE⟩
    obtain ⟨hw, hz, hhd⟩ := hw
    have htT : t = .tcbObject := by rw [h1] at ht; simpa [objTypeOf] using ht.symm
    exact ⟨hNS, Or.inr ⟨h1', σ', G', th'', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ⟨t1, a1, hr, hw.mono fun v hv => Or.inl ⟨htT, hv⟩, fun _ => hz, fun _ => hhd⟩, e11⟩⟩
  · refine WP.spec_mono (retype_reset_full (L := L) arI ar th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 hpp hidx hcap1 hfi0 hnd
      hpal hsb4 hhigh hN (hns hnc) hzero1 hrcb hppS hPP2
      (ekept_dw hP hxs _ (by rw [hDW2]; exact hDWal) (by rw [hDW2]; exact hDWreg) (by rw [hDW2]; exact hDWobj _ hxs)
        hpfit _ _) ⟨rfl, rfl⟩ (fun _ h => h.1) horig2
      nt us t ht (by omega) hus hz47 hsc hct0 hdest hdout (by omega) off win hwin hw1 hmem hempty1 (fun hd => (dev_nt ht (hdevc hd)).2.1) bitsApi hb)
      fun res h => hpost res ?_
    rcases h with ⟨hNS, hE | ⟨h1', σ', G', th'', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ⟨t1, a1, hr, hw⟩, e11⟩⟩
    · exact ⟨hNS, Or.inl hE⟩
    obtain ⟨hw, hz⟩ := hw
    exact ⟨hNS, Or.inr ⟨h1', σ', G', th'', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
      ⟨t1, a1, hr, hw.mono fun w hw => Or.inr hw, hz,
        fun hT => absurd (objTypeOf_tcb (hT ▸ ht)) h1⟩, e11⟩⟩


/-- **FL4's untyped `Retype` refines FL4's spec, resets included**
(`fl4DecodeUntypedInvocation`, `set_thread_state Restart`,
`fl4InvokeUntyped`; `Z = Unit`), for every non-arch type: `decode` ends with
the error the spec's decode throws, or the spec decodes an invocation and
`RetPostN` holds (no failure; an outcome of FL4's kind, done or preempted in
the reset, related to FL4's result).

Beyond the hypotheses of `untyped_retype_refines_fl4` (with `hunused`
dropped, and the scheduler-action and debug-list words outside the whole
region): for the reset of a used region (`hRst`, when the cap has no
children and `fi ≠ 0`; device caps included) the spec's original
slots, the CNodes of the typed heap and the debug-list head TCB are outside
the region (l4v: nothing reachable is there); no linked slot is in it and no
object straddles it; the region is at least 16 bytes; the chunk size is FL4's;
and the preemption points are opaque (`hppS`, `hPP`). -/
theorem untyped_retype_refines_fl4N [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (th : TypedHeap) (s : S) (ar : A')
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
    (hactZ : ¬ (p.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hsb4 : 4 ≤ sb.val) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : ∀ k0 v0 : U64, PPHyp (L := L) arI th p sb (fun t => L.ksb t = k0 ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = v0))
    (hRst : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val ≠ 0 →
      (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl) ∧
      (∀ q r, th q = some (.cnode r) → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val)) ∧
      ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
        (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hDWne : (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (stA ct).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ≠ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val)
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))) :
    untyped.decode st arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocation slbl (args.map UScalar.bv) (pp.bv, idx)
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostN (L := L) th (L.mem s) G σ arI ar s Fl4Spec.fl4ObjBitsApi (L.ksb s)) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refines_fl4 arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen hargs
    (fun x hx => Or.inl (by have := hnt x hx; omega))
    _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  have hn := hnt nt hnt0
  have hb : Fl4Spec.fl4ObjBitsApi t us.val = zOf nt.val us.val := (objTypeOf_fl4 hctx.ty us.val).2.1
  exact retype_cont_allN arI ar th s σ G hR hV hP hM hC hI hU horig ct hcur hct htcb hact hpp hidx hcap hpal hpfit hfi
    hhigh hactZ hfree hzero hsb4 hN hns hrcb hppS hPP hRst Fl4Spec.fl4ObjBitsApi nt us dest off win t r reset fiv hn hb
    hDWal hDWobj hDWreg hDWne hhead hctx

end

end
end Fl4Proofs.P3
