
/-! ## The Untyped invocation and decode under `MachPlat` -/

section Dec
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The retype after the decode under `MachPlat`** (XTopJointUt's
`JUtRetHypD` with `UtRetPostJM`). -/
def JUtRetHypDM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (th : TypedHeap) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p sb fi : U64) (dev : Bool) (ct : U64)
    (blk call don : Bool) (argsU : List U64) : Prop :=
  ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
    argsU.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr sl) reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us
        dest off win dev) ⦃ res =>
      UtRetPostJM (L := L) arI AR MR σ blk call don (.retype sl reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev)
        res ⦄

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The retype of a RAM untyped cap under `MachPlat`** (module docstring):
a native object type (`hNat`), with a reset by `JAtZ.utResetJM`, without one
by `JAtZ.jUtRetHyp` (its residual `JUtRetHypR` is asked only with a reset or
of a non-native type: vacuous here, the decode fixes `reset` by the cap's
children, `RetCtx.resetEq`) and `UtRetPostJ.toM`. -/
theorem JAtZ.jUtRetHypM {s : S} {ar : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hMP : MachPlat arI MR)
    (hPA : PPPlatA arI AR) (hrcb : Fl4Spec.resetChunkBits = 16)
    (hRd0 : σ.consumedTime = 0 → ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.scActive y = true →
      Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd y) = true)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    (hUZ : UtZero (L.mem s) Z.G σ) (hUN : UtNodesJ (L.mem s) Z.G (L.ksb s))
    (hMR : MR ar σ.machineState) (hVT : ValidMachineTime σ) (hVIM : ValidIrqMasks σ)
    {blk call don : Bool} {argsU : List U64} (hNat : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val) :
    JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi false ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  have hnt14 : nt.val < 14 := by
    have h19 := (objTypeOf_fl4 hctx.ty us.val).1
    rcases hNat nt hh with h | h <;> omega
  cases reset
  · have hR' : JUtRetHypR (L := L) arI AR Z.th s ar σ sl p sb fi ct blk call don argsU := by
      intro nt' us' dest' off' win' t' r' reset' fiv' hh' hctx' hcase'
      exfalso
      have e : nt' = nt := Option.some.inj (hh'.symm.trans hh)
      subst e
      have hrs : reset' = false := hctx'.resetEq.trans hctx.resetEq.symm
      subst hrs
      rcases hcase' with h | h
      · cases h
      · omega
    exact WP.spec_mono (J.jUtRetHyp hni hct hsl hcap hBO hAF hRU hc0 hUZ hUN hR' nt us dest off win t r false fiv hh hctx)
      fun res h => h.toM fun σ1 _ => (NoPre.noErr_retypeNoReset blk call don _ _ _ _ _ _ _).at σ1
  · obtain ⟨sl1, idx⟩ := sl
    obtain ⟨pp, hp1, hpp⟩ := hsl
    dsimp only at hp1 hpp
    subst hp1
    have hB : UtBodyHyp (L := L) arI AR pp idx p sb nt us dest off win t r fiv := by
      rcases (show (nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ nt.val = 7 ∨ nt.val = 12 ∨ nt.val = 13 ∨
          nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11) ∨
          nt.val = 0 ∨ nt.val = 5 ∨ nt.val = 8 ∨ nt.val = 4 ∨ nt.val = 1 by omega) with
        h | h | h | h | h | h
      · exact utEp_bodyHyp (by omega)
      · exact utUt_bodyHyp h
      · exact utSc_bodyHyp h
      · exact utPm_bodyHyp h
      · exact utCn_bodyHyp h
      · exact utTcb_bodyHyp h
    exact J.utResetJM hni hct hpp rfl hcap hc0 hctx hBO hAF hRU hAK hA hnd hMP hPA hrcb hRd0 hnq hVM hUZ hUN hB
      hMR hVT hVIM blk call don

set_option maxHeartbeats 4000000 in
/-- **The retype of a device untyped cap under `MachPlat`**: UtDevReset's
`JAtZ.jUtRetHypDev` and `UtRetPostJ.toM` (without a reset, or with one: the
spec's reset of the device cap read at the restart's state has no error
outcome, `NoPre.noErrAt_retypeDev`). -/
theorem JAtZ.jUtRetHypDevM {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) {ct : U64} (hct : sched.cur_thread st s = ok ct) {sl : Fl4Spec.CslotPtr}
    (hsl : ∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi true))
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ) (hRU : RegionUnrefAt (L := L) H Cs D s) (hc0 : Z.c = 0#u64)
    (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ) (hGP : DevGpm (L.mem s) Z.G σ)
    (hrcb : Fl4Spec.resetChunkBits = 16)
    (hVM : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s1) (L.ksb s1)
        (Vs.NeedR Z.th (L.mem s1) 5) (Vs.NeedR Z.th (L.mem s1) 4) (Vs.NeedR Z.th (L.mem s1) 3)
        (Vs.NeedR Z.th (L.mem s1) 2) (Vs.NeedR Z.th (L.mem s1) 1))
    {blk call don : Bool} {argsU : List U64} :
    JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi true ct blk call don argsU := by
  intro nt us dest off win t r reset fiv hh hctx
  refine WP.spec_mono (J.jUtRetHypDev hni hct hsl hcap hBO hAF hRU hc0 hDA hDF hGP hrcb hVM nt us dest off win t r
    reset fiv hh hctx) fun res h => h.toM fun σ1 hst1 => ?_
  cases reset
  · exact (NoPre.noErr_retypeNoReset blk call don _ _ _ _ _ _ _).at σ1
  obtain ⟨sl1, idx⟩ := sl
  obtain ⟨pp, hp1, hpp⟩ := hsl
  dsimp only at hp1 hpp
  subst hp1
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  subst hctE
  obtain ⟨hP, -, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl hpp⟩
  obtain ⟨s1, σ1', x1, -, hst1', -, -, -, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  have e1 : σ1 = σ1' :=
    congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj (hst1.symm.trans hst1')).1)
  subst e1
  obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, -, -⟩ :=
    restart_dstate Z.th hP s σ Z.G J.dstate (L.curW s) hct J.kern.cur J.kern.curT J.kern.act
  rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
  have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true) :=
    (hSS1.capAt hAs.isSlot).trans hcap
  have hg1 : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap true p.bv sb.val fi.val, σ1)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := J1.xtop.rel.2.1.1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl hpp
    rw [hcap1] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  exact NoPre.noErrAt_retypeDev blk call don hg1 _ _ _ _ _ _

/-- **An untyped cap's decode at `J` under `MachPlat`** (XTopJointUt's
`decode_invocation_untypedJ` with `JUtRetHypDM`): `XCapP` at `JAt`/`JAtPreMV`. -/
theorem decode_invocation_untypedJM [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (argsU : List U64)
    (hlen : length.val = argsU.length)
    (hargs : ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hNative : ∀ x, argsU.head? = some x → x.val < 14 ∨ 19 ≤ x.val)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (p sb fi : U64) {dev : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hR : JUtRetHypDM (L := L) arI AR MR Z.th s ar σ sl p sb fi dev ct blk call don argsU) :
    XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl)
      (.Untyped p sb fi dev) blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct := by
  have hX0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  obtain ⟨hP, ⟨hSR, hV, hM, hC, hI⟩, -⟩ := J.xtop.rel
  left
  unfold DecOKDMXP syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_mono (untyped_decode_refines_fl4 arI Z.th s ar σ Z.G hSR hV hP hM hC hI lbl slbl hlbl length buf ct
    hct argsU hlen hargs hNative _ sl rfl hAs p sb fi dev hc extra x0 hx0 _ hex hfan
    (fun inv res => UtRetPostJM (L := L) arI AR MR σ blk call don inv res) hR) ?_
  rintro res (⟨e, e', rfl, h1, h2⟩ | ⟨inv, hrun, σ1, hst, y, hy, hrel, hx⟩)
  · exact TopPostDMX.errP ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, hX0⟩
  · exact Or.inr ⟨.invokeUntyped inv, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, y, hy, hrel, hx⟩

end Dec

end

end Fl4Proofs.P3
