/-
P3 (DESIGN.md §9), CSpace: **the reply's, the thread's and the IRQ
handler's finalisations at `WJL`** (XTopJointWJLFin's `JFinAtL`, the kinds
left there).

* `jFinAtL_reply`: XTopJointDelR's `jFinAt_reply` at `WJL`
  (`JAtZ.finReplyJD` from the dead set grown by the TCB zombies' TCBs, its
  `reply_remove` case by `JAtZ.replyRemoveJD` at that set; P1's
  `fin_reply.dbgKeep`, its caller-core premise by `JAtZ.rmCore`).
* `jFinAtL_thread`: XTopJointDelR's `jFinAt_thread` at `WJL`
  (`JAtZ.finThreadJL` from the grown dead set): the debug lists lose exactly
  the thread (`JAtZ.dbgWF_thread`), so `LiveJ` after by `LiveJ.of_sameDbg`
  (every debug-list member after one before: `dbgNth_mem_wf`,
  `dbgNth_getElem_wf`) and `RzJ` at the zombie remainder (the thread dead,
  off the list).
* `jFinNtfnKL`, `delete_oneJL`, `jFinAtL_irq`: XTopJointDelR's `jFinNtfnK`,
  `delete_oneJ` and `jFinAt_irq` at `WJL` (the notification's finalisation
  by `jFinAtL_ntfn`/`jFin_nonfinalLO`, every slot kept by `jFinNtfnK`; the
  slot emptied by `emptyHypJL` with `RdLO`; the handler's slot `RdLO` by
  `rdLO_noRef`: an IRQ handler cap is not physical and names nothing).
-/
import Fl4Proofs.P3.XTopJointWJLFin
import Fl4Proofs.P3.XTopJointFinThreadU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **A final reply cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_reply [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) : JFinAtL (L := L) arI AR th RpK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, g, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHp : H p = some .reply := (hJ.typed _ hA.isSlot).2.2 p g hcv
  have hpR : p ∈ (Z.mv G V).R := J.hset.2.2 p hHp
  have hrH : p ∈ P1.Heap.replies H := J.zH.2.2.1 p hpR
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  have hdc : ∀ t ∈ P1.Heap.tcbs H, headBit (L.mem s (rNextA p)) = true →
      L.mem s (P1.affA t) = L.mem s (P1.scCoreA (L.mem s (rNextA p) &&& ~~~1#u64)) := fun t ht =>
    J.rmCore hpR (by rw [J.tcbs_eq.1]; exact ht)
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and
    (J0.finReplyJD hT (fun r t x hr ht hk hst => WP.spec_mono (J0.replyRemoveJD hT hr ht hk hst)
      fun res ⟨h1, σ', V', Ac', Lst', D', e, J', hSS, hks, hD, _⟩ => by
        subst hD; exact ⟨h1, σ', V', Ac', Lst', e, J', hSS, hks⟩) hpR)
    (P1.fin_cap_reply.dead (ar := arI) hT s a p g false J.blk hHp))
    (P1.fin_reply.dbgKeep (ar := arI) hT s a p g true false J.blk hrH hdc)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨e1, e2, σ1, V1, Ac1, Lst1, hmem1, J1, hSS1, hks1⟩, d1⟩, hK⟩
  simp only at e1 e2 hmem1 J1 hSS1 hks1 d1 hK
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  subst e2
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun h => (by rw [hHp] at h; cases h), fun h => (by rw [hHp] at h; cases h),
      fun h => (by rw [hHp] at h; cases h), fun _ => d1, fun z h => (by rw [hHp] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Reply p g := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI J hDS hL hDW hN J1 (fun p hp => Or.inr hp) hSS1 hDS1 hK (gk_idle (Vs.gk_finaliseCap _ _) hmem1)
  have hn : ∀ q, ¬ RefsObj q (capV (L.mem s1) (cslotAddr sl)) := fun q h => by rw [hcv1] at h; exact h
  exact ⟨rfl, trivial, trivial, σ1, G, hmem1, hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hmem1 hns, SpecGlob.fin hmem1 hsg, hpp _ _ hmem1 hp0⟩,
      hL1, hDW1, hN1⟩,
    fun _ => rdLO_noRef arI J1 hL1 (JAtZ.reply_ready arI J1 hA.isSlot hcv1 hdp) hn,
    fun _ _ _ _ q h => by rw [hcv1] at h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- **A final thread cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_thread (hT : P0.ArchTotal arI) (hK : ARKeep arI AR)
    (hF : JThreadFinHypsU (L := L) arI AR th) : JFinAtL (L := L) arI AR th TcbK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc hk ⟨p, hce⟩ hfin
  subst hce hth
  obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hcv := capV_of_capAt hc
  have hthp : Z.th p = some .tcb := hDS.1.2.1.abs hA hc
  have hpT : p ∈ Z.T := J.thT p hthp
  have hpH : H p = some .tcb := J.zH.1 p hpT
  have hv0 := hF.obj (Z.mv G V) H Cs Ac Lst D s a σ rfl J _ p hA.isSlot hcv
  have hidle : L.idleW s ≠ p := by
    intro e
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA
    rw [hc] at hc0; cases eq_of_ok_eq hc0
    rw [hca0.abs] at hg0
    have ha0 := (getCap_set_iff σ sl.1 sl.2 _).1 (congrArg Prod.fst hg0)
    apply hsg.idle sl.1 sl.2 _ ha0 (by simp [IsPageCap, absCap])
    rw [JAtZ.idleThread_eq arI J, e]; simp [absCap, Fl4Spec.objRefs]
  have hna : L.actionW s ≠ p := J.action_ne_of_noSwitch hpT hns
  have hp00 : p ≠ 0#u64 := fun e => by rw [e, J.kern.h0] at hpH; cases hpH
  have c0 : 0#u64 ∈ Cs := J.kern.cs0
  have hnd := hDW.nodup 0#u64 c0
  have hpp := jFinPPHyp arI (Z.mv G V) H Cs Ac Lst D s a σ rfl J sl _ hA hc hk
  rw [decide_eq_true hfin] at hpp ⊢
  refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and
    (J0.finThreadJL hT hK hF.ticks hL hpT hv0 hna hidle)
    (P1.fin_cap_thread.dead (ar := arI) hT s a p false J.blk hpH hna hidle hv0))
    (P1.fin_cap_thread.slots (ar := arI) hT s a p true false J.blk hpH hna hidle hv0))
    (J.finThreadDbgPre hT hpH hna hidle hv0)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨⟨⟨σ1, hm1, V1, Ac1, Lst1, J1⟩, d1, d2, d3, d4, d5, d6⟩, e, -, f, hW1⟩, s5, hpre⟩
  simp only [ite_true, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hSS1 : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_capw J.xtop.rel.1 (J.slotCapW (tLowSlots_all _)) hW1
  have hks1 : L.ksb s1 = L.ksb s := f.1
  have hdp : DeadP (L := L) H s1 p :=
    ⟨fun _ => ⟨d1, d2, d3, Ne.symm d4, Ne.symm d5, d6⟩, fun h => (by rw [hpH] at h; cases h),
      fun h => (by rw [hpH] at h; cases h), fun h => (by rw [hpH] at h; cases h),
      fun z h => (by rw [hpH] at h; cases h)⟩
  have hcv1 : capV (L.mem s1) (cslotAddr sl) = .Thread p := by
    rw [hSS1.capV hA.isSlot, hcv]
  have hm1' : ((absCap (capability.Cap.Zombie p capability.ZOMBIE_TCB 6#u64), absCap capability.Cap.Null), σ1) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Thread p)) true σ).1 := by
    rw [absCap_zombieTcb]; exact hm1
  have hDS1 : DState (L := L) Z.th s1 σ1 G := ⟨J1.xtop.rel.2.1, J1.del, J1.xtop.rel.2.2.1⟩
  have horig : σ1.isOriginalCap = σ.isOriginalCap :=
    orig_eq_of_slots hDS.1.2.2.2.1 hDS1.1.2.2.2.1 J.kern.orig J1.kern.orig hSS1
  have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
  have hDW1 := J.dbgWF_thread J1 rfl rfl hDW hpH hpre
  have hW1m : ∀ n, dbgNth (L.mem s1) n (dbgHead (L := L) s1) = 0#u64 ∨
      dbgNth (L.mem s1) n (dbgHead (L := L) s1) ∈ (lst 0#u64).erase p := fun n =>
    dbgNth_mem_wf hDW1 c0 n
  have hdbg : ∀ n, dbgNth (L.mem s1) n (dbgHead (L := L) s1) ≠ 0#u64 → ∃ k,
      dbgNth (L.mem s1) n (dbgHead (L := L) s1) = dbgNth (L.mem s) k (dbgHead (L := L) s) ∧
      dbgNth (L.mem s) k (dbgHead (L := L) s) ≠ 0#u64 := by
    intro n hn
    have hy := ((List.Nodup.mem_erase_iff hnd).1 ((hW1m n).resolve_left hn)).2
    obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.1 hy
    have e2 : dbgNth (L.mem s) k (dbgHead (L := L) s) = (lst 0#u64)[k] := dbgNth_getElem_wf hDW c0 k hk
    exact ⟨k, by rw [e2, ek], by rw [e2, ek]; exact hn⟩
  have hL1 : LiveJ (L := L) Z.th H G s1 σ1 :=
    hL.of_sameDbg hSS1 hmem horig (gk_idle (Vs.gk_finaliseCap _ _) hm1') hks1 hdbg (fun q hq => J1.jcov.dead q (Or.inr hq))
  have hN1 : NullOrig Z.th (L.mem s1) σ1 := hN.of_same (fun y hy => hSS1.capV hy) horig
  refine ⟨rfl, trivial, trivial, σ1, G, hm1', hDS1, hcv1,
    fun y hy _ => Or.inl (hSS1.capV hy), (MdbStep.refl hDS.1.2.2.1).same_right hDS.1.2.2.1 hSS1,
    ⟨⟨V1, Ac1, Lst1, _, J1, hks1.trans hkb, ak_finaliseCap_ns hm1' hns, SpecGlob.fin hm1' hsg, hpp _ _ hm1' hp0⟩,
      hL1, ⟨_, hDW1⟩, hN1⟩, fun hrm => ?_, fun _ _ _ _ q hq => ?_⟩
  · exfalso
    rcases hrm with e | ⟨p', zt, n, e, hn⟩
    · cases e
    · cases e
      rcases hn with hn | ⟨hn, -⟩ <;> exact absurd hn (by decide)
  · have e : p = q := by rw [hcv1] at hq; cases hq; rfl
    subst e
    refine ⟨hdp, fun n hn => ?_⟩
    rcases hW1m n with h | h
    · exact hp00 (hn.symm.trans h)
    · rw [hn] at h
      exact ((List.Nodup.mem_erase_iff hnd).1 h).1 rfl

set_option maxHeartbeats 4000000 in
/-- **A notification cap's finalisation at `WJL`, every slot kept** (module
docstring). -/
theorem jFinNtfnKL [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr)
    (p b : U64) (w r : Bool)
    (hDS : DState (L := L) th s σ G) (hW : WJL (L := L) arI AR Z H Cs kb s a σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Notification p b w r)) :
    objects.finalise_cap st arI s a (.Notification p b w r)
        (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) false ⦃ res =>
      res.1.1 = finRem (.Notification p b w r) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) ∧
      res.1.2 = .Null ∧ ∃ σ' G', ((absCap res.1.1, absCap res.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit)
          (absCap (.Notification p b w r)) (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ)) σ).1 ∧
        DState (L := L) th res.2.1 σ' G' ∧ (∀ y, IsSlot th y → capV (L.mem res.2.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem res.2.1) G' ∧ WJL (L := L) arI AR Z H Cs kb res.2.1 res.2.2 σ' G' ∧
        RdLO (L := L) (A := A) th H res.2.1 res.2.2 σ' G' (cslotAddr sl) ⦄ := by
  have hK := jFinNtfnK arI Z H Cs kb hth s a σ G sl p b w r hDS (hW.1.wj arI) hA hc
  have hfi : ¬ FrIoK (.Notification p b w r) := by
    rintro (h | ⟨f, l, o, e⟩)
    · simp [isFrame] at h
    · cases e
  by_cases hfin : Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ
  · refine WP.spec_mono (WP.spec_and hK
      (jFinAtL_ntfn arI Z H Cs kb hth s a σ G sl _ hDS hW hA hc trivial ⟨p, b, w, r, rfl⟩ hfin)) ?_
    rintro res ⟨⟨h1, h2, σ0, G0, -, -, hkeep, -⟩, ⟨-, -, -, σ', G', h4, h5, -, -, h7, h8, h9, -⟩⟩
    exact ⟨h1, h2, σ', G', h4, h5, hkeep, h7, h8, h9 (Or.inl h1)⟩
  · refine WP.spec_mono (WP.spec_and hK
      (jFin_nonfinalLO arI Z H Cs kb hth s a σ G sl _ hDS hW hA hc trivial hfi hfin)) ?_
    rintro res ⟨⟨h1, h2, σ0, G0, -, -, hkeep, -⟩, ⟨-, -, -, σ', G', h4, h5, -, -, h7, h8, h9, -⟩⟩
    exact ⟨h1, h2, σ', G', h4, h5, hkeep, h7, h8, h9 (Or.inl h1)⟩

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of a notification cap at `WJL`** (module docstring). -/
theorem delete_oneJL [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64)
    (hth : Z.th = th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hW : WJL (L := L) arI AR Z H Cs kb s a σ G) {sl : Fl4Spec.CslotPtr} (hA : AbsSlot th sl) {p b : U64}
    {w r : Bool} (hk : capV (L.mem s) (cslotAddr sl) = .Notification p b w r) :
    cdt.delete_one st arI s a (cslotAddr sl) ⦃ res =>
      ∃ σ' G', ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 ∧ DState (L := L) th res.1 σ' G' ∧
        capV (L.mem res.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem res.1) y = capV (L.mem s) y) ∧
        MdbStep (L.mem s) G (L.mem res.1) G' ∧ WJL (L := L) arI AR Z H Cs kb res.1 res.2 σ' G' ⦄ := by
  have hP : Placed th := by obtain ⟨⟨V, Ac, Lst, D, J, -⟩, -⟩ := hW; exact hth ▸ J.xtop.rel.1
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS.1.1.abs_cap hA
  rw [hca.abs] at hg
  have hcv := capV_of_capAt hc
  unfold cdt.delete_one
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  rw [hcv] at hk; subst hk
  have hcn : capability.Cap.Notification p b w r ≠ .Null := by simp
  simp only [isNullB_false hcn, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bf, hbf, hbf2, -⟩ := finalHyp_full th hP s σ G sl _ hDS hA hc hcn
  have hNF : NeedsFin (.Notification p b w r) := Or.inl ⟨trivial, rfl⟩
  rw [hbf2 hNF] at hbf
  rw [is_final_with_cap_eq _ _ _ hc, hbf]; simp only [bind_ok]
  rw [← finalise_cap_ntfn arI s a p b w r _ false]
  apply WP.spec_bind (jFinNtfnKL arI Z H Cs kb hth s a σ G sl p b w r hDS hW hA hc)
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨hrem, hcl, σ1, G1, hmem, hDS1, hkeep, hm1, hW1, hRd1⟩
  simp only at hrem hcl hmem hDS1 hkeep hm1 hW1 hRd1
  subst hcl
  simp only [uncurry_apply_pair]
  refine WP.spec_mono (empty_stepWR' arI (WJL (L := L) arI AR Z H Cs kb) (RdLO (L := L) (A := A) th H) th hP
    (cl := .Null) (fun h => absurd rfl h) (emptyHypJL arI Z H Cs kb hth) s1 a1 σ1 G1 hDS1 hW1 hA
    (fun _ => hRd1) trivial trivial) ?_
  rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth, -, -, -, hm2, hW2⟩
  refine ⟨σ2, G2, ?_, hDS2, hx2, fun y hy hyx => by rw [hoth y hy hyx, hkeep y hy], hm1.trans hm2, hW2⟩
  unfold Fl4Spec.capDeleteOne
  refine mem_bind_nd (x := (absCap (.Notification p b w r), σ)) (by rw [hg]; rfl) ?_
  simp only [absCap, Fl4Spec.NonDet.unless, reduceCtorEq, ↓reduceIte]
  refine mem_bind_nd (x := (decide (Fl4Spec.isFinalCap' (absCap (.Notification p b w r)) σ), σ)) rfl ?_
  refine mem_bind_nd (x := ((), σ1)) (fastFinalise_of_finaliseCap hmem) ?_
  exact hes

set_option maxHeartbeats 8000000 in
/-- **A final IRQ handler cap's finalisation at `WJL`** (module docstring). -/
theorem jFinAtL_irq [Fl4Proofs.P1.PlainStore st] : JFinAtL (L := L) arI AR th IrqK := by
  intro Z H Cs kb hth s a σ G sl c hDS hW hA hc _ ⟨i, hci⟩ hfin
  subst hci hth
  obtain ⟨V, hX, hL⟩ : ∃ V, XTopAt (L := L) AR (Z.mv G V) s a σ ∧ IntLayout Z.th (L.ksb s) := by
    obtain ⟨⟨V, Ac, Lst, D, J, -⟩, -⟩ := hW; exact ⟨V, J.xtop, J.intL⟩
  obtain ⟨c', ac, hc', hca, -⟩ := hDS.1.1.abs_cap hA
  rw [hc] at hc'; cases eq_of_ok_eq hc'
  have hcw : CapWf (.IrqHandler i) := hca.1
  have hi : i.val < 128 := hcw
  rw [decide_eq_true hfin]
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  rw [irq_slot_eq]; simp only [bind_ok]
  have hA' : AbsSlot Z.th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
  set sl' : Fl4Spec.CslotPtr := ((nodeA (L.ksb s) i).bv, []) with hsl'
  have hcs : cslotAddr sl' = nodeA (L.ksb s) i := cslotAddr_nil _
  have hcv := capV_of_capAt hc
  have hnode : σ.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA (L.ksb s) i).bv :=
    hX.fin.1.1.2.2.2.1.node i hi
  have hfo : ∀ (s1 : S) (a1 : A), objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true =
      ok ((.Null, .IrqHandler i), s1, a1) := fun _ _ => rfl
  have hspec : ∀ σ1 : Fl4Spec.State Unit, ((), σ1) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl' σ).1 →
      ((absCap .Null, absCap (.IrqHandler i)), σ1) ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.IrqHandler i)) true σ).1 := by
    intro σ1 h1
    show _ ∈ ((if true = true then do
        Fl4Spec.deletingIrqHandler (BitVec.ofNat 8 i.val)
        return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.irqHandlerCap (BitVec.ofNat 8 i.val))
      else return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) σ).1
    simp only [↓reduceIte]
    refine mem_bind_nd (x := ((), σ1)) ?_ (Set.mem_singleton _)
    unfold Fl4Spec.deletingIrqHandler Fl4Spec.getIrqSlot
    refine mem_bind_nd (x := (sl', σ)) (by
      show (((nodeA (L.ksb s) i).bv, []), σ) = ((σ.interruptIrqNode (BitVec.ofNat 8 i.val), []), σ)
      rw [hnode]) h1
  have hok := jIrqSlotHyp arI (AR := AR) Z H Cs kb rfl s a σ G (hW.1.wj arI) i hi
  have hne : cslotAddr sl ≠ nodeA (L.ksb s) i := by
    intro e
    rcases hok with h | ⟨p, b, w, r, h⟩
    · rw [← e, hcv] at h; cases h
    · rw [← e, hcv] at h; cases h
  have hphys : physF (.IrqHandler i) = false := ok_inj (phys_eq _).symm
  have hrd : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) (G' : MdbGhost),
      WJL (L := L) arI AR Z H Cs kb s' a' σ' G' →
      capV (L.mem s') (cslotAddr sl) = .IrqHandler i → RdLO (L := L) (A := A) Z.th H s' a' σ' G' (cslotAddr sl) := by
    intro s' a' σ' G' hW' h
    obtain ⟨⟨V', Ac', Lst', D', J', -⟩, hL', -⟩ := hW'
    exact rdLO_noRef arI J' hL' (fun hp => by rw [h, hphys] at hp; cases hp)
      (fun q hr => by rw [h] at hr; exact hr)
  rcases hok with hnull | ⟨p, b, w, r, hn⟩
  · -- a null node slot: nothing to delete
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA'
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s a (nodeA (L.ksb s) i) = ok (s, a) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) sl' σ = ({((), σ)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg0]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e1]; simp only [bind_ok]
    show objects.finalise_cap_object st arI s a (.IrqHandler i) true ⦃ _ ⦄
    rw [hfo, WP.spec_ok]
    exact ⟨rfl, trivial, hcw, σ, G, hspec σ (by rw [e2]; exact Set.mem_singleton _), hDS, hcv,
      fun _ _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1, hW, fun _ => hrd s a σ G hW hcv,
      fun _ _ _ e => by cases e⟩
  · -- a notification cap: `delete_oneJL`
    have hd := delete_oneJL arI Z H Cs kb rfl s a σ G hDS hW hA' (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_bind hd ?_
    rintro ⟨s1, a1⟩ ⟨σ1, G1, hm1, hDS1, hx1, hoth1, hmS1, hW1⟩
    show objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true ⦃ _ ⦄
    rw [hfo, WP.spec_ok]
    have hcv1 : capV (L.mem s1) (cslotAddr sl) = .IrqHandler i := by
      rw [hoth1 _ hA.isSlot hne]; exact hcv
    refine ⟨rfl, trivial, hcw, σ1, G1, hspec σ1 hm1, hDS1, hcv1, fun y hy hyx => ?_, hmS1, hW1,
      fun _ => hrd _ _ _ _ hW1 hcv1, fun _ _ _ e => by cases e⟩
    by_cases e : y = nodeA (L.ksb s) i
    · subst e; refine Or.inr ⟨hx1, ?_⟩; rw [hn]; rfl
    · exact Or.inl (hoth1 y hy e)

end

end

end Fl4Proofs.P3
