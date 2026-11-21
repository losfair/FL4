/-
P3 (DESIGN.md §9), CSpace: **the finalisations at `WJL`**, toward
`FinObjHypWRcZ` at `WJL` (`RdLO`, `RzJ`; XTopJointWJL, XTopJointWJLRd).

* `JFinAtL Kd`: a final cap's finalisation of a kind `Kd` at `WJL`, the
  loop's post (`FinObjHypWRcZ`'s) at `WJL`, `RdLO`, `RzJ` (the latter when
  the remainder is a zombie: DelW's `FinObjHypWRcZ` asks it only then, so a
  non-final thread cap, its remainder null, needs none).
* `wjl_keep`: a finalisation keeping every slot, the MDB ghost, the debug
  words, and landing at a `JAtZ` whose dead set holds the TCB zombies' TCBs
  before, keeps `LiveJ` (`LiveJ.of_sameZ`), `DbgWF` (`JAtZ.dbgWF_keep`) and
  `NullOrig` (`orig_eq_of_slots`, `NullOrig.of_same`).
* `rdLO_noRef`: `RdLO` at a slot whose cap names no container, from `RdJ`
  and `LiveJ` (`JAtZ.readyLive_noRef`, `LiveJ.liveOther_noRef`).
* `jFinAtL_ep`: XTopJointDelR's `jFinAt_ep` at `WJL` (`JAtZ.finEpJ` from the
  dead set grown by the TCB zombies' TCBs, P1's `fin_endpoint.dbgKeep`).
-/
import Fl4Proofs.P3.XTopJointWJLPP
import Fl4Proofs.P3.XTopJointFinVtJD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

/-- **A final cap's finalisation of a kind `Kd` at `WJL`** (module docstring). -/
def JFinAtL (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (Kd : capability.Cap → Prop) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64), Z.th = th →
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    DState (L := L) th s σ G → WJL (L := L) arI AR Z H Cs kb s a σ G → AbsSlot th sl →
    capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c → Kd c → Fl4Spec.isFinalCap' (absCap c) σ →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJL (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → RdLO (L := L) (A := A) th H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
        (∀ p zt n, r.1.1 = .Zombie p zt n → RzJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄

/-- **A slot-keeping finalisation keeps `LiveJ`, `DbgWF` and `NullOrig`**
(module docstring). -/
theorem wjl_keep {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hDS : DState (L := L) Z.th s σ G)
    (hL : LiveJ (L := L) Z.th H G s σ) (hDW : DbgWF (P1.Heap.tcbs H) Cs (L.mem s) (dbgHd (L := L) s))
    (hN : NullOrig Z.th (L.mem s) σ)
    {V1 : XVs} {Ac1 : Set U64} {Lst1 : U64 → List U64} {D1 : Set U64} {s1 : S} {a1 : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR (Z.mv G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1) (hE : ZTcb (L := L) Z.th s ⊆ D1)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s1)) (hDS1 : DState (L := L) Z.th s1 σ1 G)
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1) (hid : σ1.idleThread = σ.idleThread) :
    LiveJ (L := L) Z.th H G s1 σ1 ∧ DbgWF (P1.Heap.tcbs H) Cs (L.mem s1) (dbgHd (L := L) s1) ∧
      NullOrig Z.th (L.mem s1) σ1 := by
  have horig : σ1.isOriginalCap = σ.isOriginalCap :=
    orig_eq_of_slots hDS.1.2.2.2.1 hDS1.1.2.2.2.1 J.kern.orig J1.kern.orig hSS
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
    ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  obtain ⟨lst, hDW⟩ := hDW
  exact ⟨hL.of_sameZ hSS hmem horig hid hK J.kern.cs0 hTz fun p hp => J1.jcov.dead p (hE hp),
    ⟨lst, J.dbgWF_keep J1 rfl rfl hDW hK⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩

/-- **`RdLO` at a slot whose cap names no container** (module docstring). -/
theorem rdLO_noRef {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost} {V : XVs}
    (J : JAtZ (L := L) arI AR (Z.mv G V) H Cs Ac Lst D s a σ) (hL : LiveJ (L := L) Z.th H G s σ) {x : U64}
    (hRd : EmptyReady (L := L) H G s x) (hn : ∀ q, ¬ RefsObj q (capV (L.mem s) x)) :
    RdLO (L := L) (A := A) Z.th H s a σ G x :=
  ⟨⟨hRd, J.readyLive_noRef hL hn⟩, hL.liveOther_noRef hn⟩

set_option maxHeartbeats 4000000 in
/-- **A final endpoint cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_ep : JFinAtL (L := L) arI AR th EpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨e, b, x1, x2, x3, x4, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHe : H e = some .ep := (hJ.typed _ hA.isSlot).1 e b x1 x2 x3 x4 hcv
  have heE : e ∈ (Z.mv G V).E := J.hset.1 e hHe
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (J0.finEpJ heE)
    (P1.fin_cap_ep.dead (ar := arI) s a e b x1 x2 x3 x4 false J.blk hHe))
    (P1.fin_endpoint.dbgKeep (ar := arI) s a e b x1 x2 x3 x4 true false J.blk hHe)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, hmem1, J1, -, hSS1, hks1⟩, d1⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 e :=
    ⟨fun h => (by rw [hHe] at h; cases h), fun _ => d1, fun h => (by rw [hHe] at h; cases h),
      fun h => (by rw [hHe] at h; cases h), fun z h => (by rw [hHe] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Endpoint e b x1 x2 x3 x4 := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hmem1)
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac, Lst, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.ep_ready arI J1 hA.isSlot hcv1 hdp) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- **A final notification cap's finalisation at `WJL`** (XTopJointDelR's
`jFinNtfnK`, final case: `JAtZ.finNtfnJ` from the grown dead set, P1's
`fin_cap_ntfn.dbgKeep`). -/
theorem jFinAtL_ntfn : JFinAtL (L := L) arI AR th NtfnK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, b, w, r, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .ntfn := ((hJ.typed _ hA.isSlot).2.1 p b w r hcv).2
  have hpN : p ∈ (Z.mv G V).N := J.hset.2.1 p hHp
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (J0.finNtfnJ hpN)
    (P1.fin_cap_ntfn.dead (ar := arI) s a p b w r false J.blk hHp hHp))
    (P1.fin_cap_ntfn.dbgKeep (ar := arI) s a p b w r true false J.blk hHp hHp)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, hmem1, J1, -, -, hSS1, hks1⟩, d1, d2, d3⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 d2 d3 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ => ⟨d1, d2, d3⟩,
      fun h => (by rw [hHp] at h; cases h), fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Notification p b w r := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hmem1)
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac, Lst, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (J1.ntfn_ready hA.isSlot hcv1 (Or.inl hdp)) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- **A final SC cap's finalisation at `WJL`** (XTopJointDelR's `jFinAt_sc`
with XTopJointFinSc's `jScFin_of`: `JAtZ.finScJD` from the grown dead set,
`jYieldToHypD_of`; P1's `fin_cap_sc.slots`, `fin_cap_sc.dead`,
`fin_sc.dbgKeep`). -/
theorem jFinAtL_sc (hT : P0.ArchTotal arI)
    (hticks : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      ∀ (a : A) (v : U64), arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    JFinAtL (L := L) arI AR th ScK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, sb, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hC' := J.scCap arI hA hc
  obtain ⟨hHp, hpC, hpz, hna, hidle, -, hpi⟩ :=
    JAtZ.scCapFacts arI J hA hc ⟨hC'.1, hC'.2, fun _ _ _ _ _ u hu => (hns u hu).elim⟩
  have hpS : p ∈ P1.Heap.scs H := ⟨_, hHp⟩
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (JAtZ.finScJD arI hT (jYieldToHypD_of arI hT hticks) J0 hpC hpz hpi hpS hna hidle)
    (P1.fin_cap_sc.slots (ar := arI) hT s a p sb true false J.blk hpS hpz hna hidle))
    (P1.fin_cap_sc.dead (ar := arI) hT s a p sb false J.blk hpS hpz hna hidle))
    (P1.fin_sc.dbgKeep (ar := arI) hT s a p sb true false J.blk hpS hpz hna hidle)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨⟨σ1, hm1, ⟨V1, Ac1, Lst1, J1⟩, y1⟩, e, -, f, hW1⟩, d1, d2, d3⟩, hK⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only at hm1 J1 y1 d1 d2 d3 hK hW1 f
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  have hks1 : L.ksb s1 = L.ksb s := f.1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h), fun _ _ => ⟨d1, d2, d3, y1⟩⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .SchedContext p sb := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hm1)
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hm1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hm1 hns, SpecGlob.fin hm1 hsg, hpp _ _ hm1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.sc_ready arI J1 hcv1 hHp hdp) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- **A final native VSpace cap's finalisation at `WJL`** (XTopJointDelR's
`jFinAt_vs`: `JAtZ.finVsJ` from the grown dead set, `JAtZ.finVsDbg`). -/
theorem jFinAtL_vs [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFinAtL (L := L) arI AR th VsK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hv hfin
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hxm : cslotAddr sl ∈ G.chains.flatten := (hDS.1.2.2.1.members _).2 ⟨hA.isSlot, _, hc, fun h => by
    subst h
    rcases hv with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> cases e⟩
  have hvf : IsVsFin c := by
    rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial
  have hw : FinWork c true := by
    refine Or.inl ⟨Or.inl rfl, ?_, ?_⟩
    · rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
    · intro f l e
      rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
        cases e
  have hn0 : ∀ q, ¬ RefsObj q c := fun q h => by
    rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact h
  have hnt : ∀ q, c ≠ .Thread q := fun q e => by
    subst e; rcases hv with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ <;> cases e
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (J0.finVsJ hAR Ap hDS hA hc hv) (J.finVsDbg hAR Ap hDS hA hc hvf true hw)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩, hK⟩
  simp only at h1 h2 h3 hm J1 hSS hks hK ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hm)
  exact ⟨h1, h2, h3, σ1, G, hm, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨⟨V, Ac, Lst, _, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg, hpp _ _ hm hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (J.vs_ready hxm hcv hv hcv1) (by rw [hcv1]; exact hn0),
    fun _ _ _ _ q h => absurd (hcv1.symm.trans h) (hnt q)⟩

set_option maxHeartbeats 4000000 in
/-- **A final mapped EPT root cap's finalisation at `WJL`** (XTopJointDelR's
`jFinAt_eptRoot`: `JAtZ.finVsJb` from the grown dead set, `JAtZ.finVsDbg`). -/
theorem jFinAtL_eptRoot [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) : JFinAtL (L := L) arI AR th EptRootK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hk' hfin
  obtain ⟨p, asid, va, hce⟩ := hk'
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hpr⟩, hL, hDW, hN⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hap0 := J.ept_obj hA.isSlot hcv
  have hp0 := J.ept_ne0 hA.isSlot hcv
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (J0.finVsJb hAR Ap hDS hA hc ⟨rfl, rfl, hp0⟩ ⟨_, rfl⟩ true
    (Or.inl ⟨Or.inl rfl, rfl, fun f l e => by cases e⟩))
    (J.finVsDbg hAR Ap hDS hA hc ⟨rfl, rfl, hp0⟩ true (Or.inl ⟨Or.inl rfl, rfl, fun f l e => by cases e⟩))) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩, hK⟩
  simp only at h1 h2 h3 hm J1 hSS hks hK ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Ept p 0#u64 true asid va := by rw [hSS.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hm)
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨h1, h2, h3, σ1, G, hm, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨⟨V, Ac, Lst, _, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg, hpp _ _ hm hpr⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (EmptyReady.of_apartO (by rw [hcv1]; exact hap0)) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- **A final VT-x object cap's finalisation at `WJL`** (XTopJointDelR's
`jFinAt_vt`: `JAtZ.finEptJD`/`JAtZ.finVcpuJD` from the grown dead set,
`JAtZ.finEptDbg`/`JAtZ.finVcpuDbg`; the spec state kept). -/
theorem jFinAtL_vt (hAR : ArchRefines arI AR) (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR th) :
    JFinAtL (L := L) arI AR th (fun c => EptK c ∨ VcpuK c) := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk hk' hfin
  subst hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hn0 : ∀ q, ¬ RefsObj q c := fun q h => by
    rcases hk' with ⟨_, _, _, _, _, rfl, -⟩ | ⟨_, rfl⟩ <;> exact h
  have hnt : ∀ q, c ≠ .Thread q := fun q e => by
    subst e; rcases hk' with ⟨_, _, _, _, _, e, -⟩ | ⟨_, e⟩ <;> cases e
  rw [decide_eq_true hfin]
  have hsp : objects.finalise_cap st arI s a c true false ⦃ r =>
      (VtPostD (L := L) arI AR (Z.mv G V) H Cs (D ∪ ZTcb (L := L) Z.th s) s σ c true r ∧
        EmptyReady (L := L) H G r.2.1 (cslotAddr sl)) ∧ P1.DbgKeep st (P1.Heap.tcbs H) Cs s r.2.1 ⦄ := by
    rcases hk' with he | hv
    · exact WP.spec_and (J0.finEptJD (G := G) hAR hV hA hc he) (J.finEptDbg hAR hV hA.isSlot (capV_of_capAt hc) he)
    · exact WP.spec_and (J0.finVcpuJD (G := G) hK hV hA hc hv) (J.finVcpuDbg hK hV hA hc hv)
  refine WP.spec_mono hsp ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨h1, h2, h3, hm, ⟨Ac1, Lst1, J1⟩, hSS, hks⟩, hRd⟩, hK'⟩
  simp only at h1 h2 h3 hm J1 hSS hks hRd hK' ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS hDS1 hK' rfl
  exact ⟨h1, h2, h3, σ, G, hm, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨⟨V, Ac1, Lst1, _, J1, hks.trans hkb, hns, hsg, hp0⟩, hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 hRd (by rw [hcv1]; exact hn0),
    fun _ _ _ _ q h => absurd (hcv1.symm.trans h) (hnt q)⟩

set_option maxHeartbeats 4000000 in
/-- **A non-final object cap's finalisation at `WJL`**, but a frame's or an
IO port's (XTopJointDelR's `jFin_nonfinalL`, its `LiveJHyp` replaced by
`WJL`'s `LiveJ`): nothing done, the state kept; `RdLO` from another cap of
the same key (`JAtZ.readyLive_key`, `LiveJ.liveOther_key`); the remainder
null, so no `RzJ`. -/
theorem jFin_nonfinalLO [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap)
    (hDS : DState (L := L) th s σ G) (hW : WJL (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hk : FinObjKind c) (hfi : ¬ FrIoK c)
    (hfin : ¬ Fl4Spec.isFinalCap' (absCap c) σ) :
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ WJL (L := L) arI AR Z H Cs kb r.2.1 r.2.2 σ' G' ∧
        (RmOK r.1.1 (cslotAddr sl) → RdLO (L := L) (A := A) th H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ∧
        (∀ p zt n, r.1.1 = .Zombie p zt n → RzJ (L := L) (A := A) H r.2.1 r.2.2 σ' G' (cslotAddr sl)) ⦄ := by
  subst hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := id hW
  have hP : Placed Z.th := J.xtop.rel.1
  have hcv := capV_of_capAt hc
  have hf : isFrame c = false := by
    cases h : isFrame c
    · rfl
    · exact absurd (Or.inl h) hfi
  have hio : ∀ f l o, c ≠ .IoPort f l o := fun f l o e => hfi (Or.inr ⟨f, l, o, e⟩)
  rw [decide_eq_false hfin]
  obtain ⟨cl, he, hmem, -, hrem, hnio⟩ := fin_idle (st := st) (L := L) arI s a σ c hk false (by
    rintro (⟨h | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩)
    · cases h
    · exact hio _ _ _ e
    · subst e; simp [isFrame] at hf)
  have hcl0 : cl = .Null := hnio (fun f l e => hio f l 0#u64 e)
  subst hcl0
  obtain ⟨y, hy, hne, hky⟩ := other_key hP hDS hA hcv hk hf hfin
  have hn : okey c ≠ none := okey_of_finObj hk
  have hsh : shape (capV (L.mem s) y) = shape c := shape_of_key hky (by rw [hky]; exact hn)
  obtain ⟨eb, et, ep⟩ := range_of_shape hsh
  have hut : isUt (capV (L.mem s) y) = false := by
    rw [isUt_of_shape hsh]; exact isUt_of_finObj hk
  rw [he, WP.spec_ok]
  exact ⟨hrem.symm, trivial, trivial, σ, G, hmem, hDS, hcv, fun y _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1,
    hW, fun _ => ⟨⟨EmptyReady.of_cover (x := cslotAddr sl) hy hne (fun h => by rw [ep]; rw [hcv] at h; exact h) hut
      (by rw [eb, hcv]) (by rw [et, hcv]),
      J.readyLive_key hL hy hne (by rw [hky, hcv]) (by rw [hcv]; exact hn)⟩,
      hL.liveOther_key hy hne (by rw [hky, hcv]) (by rw [hcv]; exact hn)⟩,
    fun _ _ _ e => by cases e⟩

set_option maxHeartbeats 4000000 in
/-- **A VSpace-mapped frame cap's finalisation at `WJL`** (XTopJointDelR's
`jFrMap_of`: `JAtZ.finVsJb` from the grown dead set, `JAtZ.finVsDbg`). -/
theorem jFrMapL [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hAp : JVsApartHyp (L := L) arI AR th)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    FinObjHypWRK (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrMapK := by
  intro s a σ G sl c hDS hW hA hc hk ⟨p, sz, r, d, asid, va, hce⟩
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have Ap := hAp (Z.mv G V) H Cs Ac Lst D s a σ hth J
  subst hth hce
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  refine WP.spec_mono (WP.spec_and (J0.finVsJb hAR Ap hDS hA hc rfl ⟨_, rfl⟩ _
    (Or.inr ⟨p, sz, r, d, false, asid, va, rfl⟩))
    (J.finVsDbg hAR Ap hDS hA hc rfl _ (Or.inr ⟨p, sz, r, d, false, asid, va, rfl⟩))) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, σ1, hm, J1, hSS, hks⟩, hK⟩
  simp only at h1 h2 h3 hm J1 hSS hks hK ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Frame p sz r d true false asid va := by
    rw [hSS.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hm)
  exact ⟨h1, h2, h3, σ1, G, hm, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨⟨V, Ac, Lst, _, J1, hks.trans hkb, ak_finaliseCap_ns hm hns, SpecGlob.fin hm hsg, hpp _ _ hm hp0⟩,
      hL1, hDW1, hN1⟩, trivial⟩

set_option maxHeartbeats 4000000 in
/-- **The VT-x work of a finalisation at `WJL`** (XTopJointDelR's
`jFrVt_of`: `JAtZ.frVtJD` from the grown dead set, `JAtZ.frVtDbg`; the spec
state kept). -/
theorem jFrVtL [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hK : ARKeep arI AR)
    (hV : JVtHyps (L := L) arI AR th) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    FinObjHypWRK (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (fun _ _ _ _ _ => True) th FrVtK := by
  intro s a σ G sl c hDS hW hA hc _ hk
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  subst hth
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  refine WP.spec_mono (WP.spec_and (J0.frVtJD hAR hK hV hDS hA hc hk _) (J.frVtDbg hAR hK hV hA.isSlot (capV_of_capAt hc) hk _)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, hm, ⟨Ac1, Lst1, J1⟩, hSS, hks⟩, hK'⟩
  simp only at h1 h2 h3 hm J1 hSS hks hK' ⊢
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = c := by rw [hSS.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS hDS1 hK' rfl
  exact ⟨h1, h2, h3, σ, G, hm, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS,
    ⟨⟨V, Ac1, Lst1, _, J1, hks.trans hkb, hns, hsg, hp0⟩, hL1, hDW1, hN1⟩, trivial⟩

/-- **The frame and IO port caps' finalisation at `WJL`**, final or not
(XTopJointFinFrIo's `finFrIo_of` at `WJL` with `RdLO`: a frame or IO port cap
names no container, `rdLO_noRef`; the slot ready as in XTopJointDelR's
`jFinAt_frio`). -/
theorem jFinAtL_frio [Fl4Proofs.P1.PlainStore st] (hAR : ArchRefines arI AR) (hK : ARKeep arI AR)
    (hAp : JVsApartHyp (L := L) arI AR th) (hV : JVtHyps (L := L) arI AR th)
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    FinObjHypWRK (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (RdLO (L := L) (A := A) th H) th FrIoK := by
  refine finFrIo_of arI (jFrMapL arI hAR hAp Z H Cs kb hth) (jFrVtL arI hAR hK hV Z H Cs kb hth) ?_
  intro s a σ G sl c hW hA hcv hk
  obtain ⟨⟨V, Ac, Lst, D, J, -⟩, hL, -⟩ := hW
  subst hth
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s) (cslotAddr sl)) := fun q h => by
    rw [hcv] at h
    rcases hk with hf | ⟨f, l, o, rfl⟩
    · cases c <;> first | exact h | simp [isFrame] at hf
    · exact h
  refine rdLO_noRef arI J hL ?_ hn
  rcases hk with hf | ⟨f, l, o, rfl⟩
  · cases c with
    | Frame p sz r d m ep a' va =>
      have hC := J.cobj hA.isSlot
      rw [hcv] at hC
      exact EmptyReady.of_apartO (by rw [hcv]; exact hC)
    | _ => cases hf
  · exact EmptyReady.of_nonphys (by rw [hcv]; exact physF_ioPort f l o)

end

end

end Fl4Proofs.P3
