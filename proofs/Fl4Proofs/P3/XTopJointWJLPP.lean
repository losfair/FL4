/-
P3 (DESIGN.md §9), CSpace: **the preemption point and `post_cap_deletion`
keep `WJL`** (XTopJointWJL).

* `jPreemptHypL`: `PPHypDW` at `WJL` (`WJP` after a preemption), as
  XTopJointPP's `jPreemptHyp_of` at a dead set holding the TCB zombies' TCBs
  (`JAtZ.addDeadSet`, `ppJD` keeping it).
* `jPostDelHypL`: `PostDelHypW` at `WJL`, as XTopJointPost's
  `jPostDelHyp_of` (`jowes_ksD` keeping the dead set).
* Both keep the slots (`SlotsSame`) and the original bits
  (`orig_eq_of_slots`), so `LiveJ` by `LiveJ.of_sameZ`, `NullOrig` by
  `NullOrig.of_same`, `DbgWF` by `JAtZ.ppDbg` / `JAtZ.postDbg` and
  `JAtZ.dbgWF_keep`.
-/
import Fl4Proofs.P3.XTopJointWJLRd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The preemption point keeps `WJL`** (module docstring). -/
theorem jPreemptHypL (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hP : PPPlat arI AR) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    PPHypDW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) (WJP (L := L) arI AR Z H Cs kb) th := by
  intro s a σ G hDS ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩
  subst hth
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  obtain ⟨⟨r1, s', a'⟩, hr, ⟨⟨σ', hcase, hX', hJ'⟩, -, hw⟩, hK⟩ :=
    spec_exists (WP.spec_and (WP.spec_and (J0.ppJD arI hAK hA hnd hP hp0)
      (P1.sched.preemption_point.pp hA s a J.blk)) (J.ppDbg hA))
  rw [hr, WP.spec_ok]
  simp only at hcase hX' hJ' hw hK ⊢
  have hX := J.xtop
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  have hN' : P1.NodePlaced st (Z.mv G V).T s (L.cpu s) := by
    rw [hc.cur, J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ (hc.cur ▸ J.kern.cpuCs)
  have hSS : SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') := hX.slotsSame_of hw fun b hb => by
    have hf := J.kern.ksbFit
    rcases hb with rfl | rfl | rfl
    · have := workUnits_val hf; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e := P1.nodeAt_val hN' (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
      have e48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CUR_TIME).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
    · have e := P1.nodeAt_val hN' (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
      have e40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
      refine Or.inl ?_
      show L.nodeBase s _ ≤ (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val ∧
        (L.nodeAt s (L.cpu s) layout.node.CONSUMED).val < L.nodeBase s _ + 4288
      rw [e, hc.cur]; omega
  have hks : L.ksb s' = L.ksb s := hw.1
  refine ⟨hSS, σ', hcase, hX'.rel.2.1, ?_⟩
  rcases hcase with ⟨rfl, hm0⟩ | ⟨rfl, hm⟩
  · obtain ⟨⟨Ac', Lst', J'⟩, hp'⟩ := hJ' rfl
    have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
    have horig : σ'.isOriginalCap = σ.isOriginalCap :=
      orig_eq_of_slots hDS.1.2.2.2.1 hX'.rel.2.1.2.2.2.1 J.kern.orig J'.kern.orig hSS
    have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
      ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
    have hL' : LiveJ (L := L) Z.th H G s' σ' :=
      hL.of_sameZ hSS hmem horig (congrArg Prod.snd (Vs.gke_preemptionPoint' σ _ hm0)) hK J.kern.cs0 hTz
        fun p hp => J'.jcov.dead p (Or.inr hp)
    exact ⟨⟨V, Ac', Lst', _, J', by rw [hks]; exact hkb, Vs.ake_preemptionPoint'.noSwitch hm0 hns,
      SpecGlob.pp hm0 hsg, hp'⟩, hL', ⟨lst, J.dbgWF_keep J' rfl rfl hDW hK⟩,
      hN.of_same (fun y hy => hSS.capV hy) horig⟩
  · exact ⟨s, a, σ, ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hr, hm, hX'.rel.2.2.2.1, hX'.rel.2.2.2.2.1⟩

set_option maxHeartbeats 4000000 in
/-- **A cleanup cap's `post_cap_deletion` keeps `WJL`** (module docstring). -/
theorem jPostDelHypL (hAM : ARMask arI AR)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hfree : ∀ (a : A) (irq : U64), ∃ a', arI.irq_free a irq = ok a')
    (Z : XSets) (H : P1.Heap) (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    PostDelHypW (L := L) arI (WJL (L := L) arI AR Z H Cs kb) th := by
  intro s a σ G cl hDS ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ hcl hcln hclw
  subst hth
  have hX := J.xtop
  have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
  have hLy : IntLayout Z.th (L.ksb s) ∧ IoLayout Z.th (L.ksb s) := ⟨J.intL, J.ioLay⟩
  have hfin : ∀ (s' : S) (a' : A) (σ' : Fl4Spec.State Unit), SlotsSame (Z.mv G V).th (L.mem s) (L.mem s') →
      P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' → XTopAt (L := L) AR (Z.mv G V) s' a' σ' →
      CRel Z.th (L.mem s') σ' G → P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' →
      WJL (L := L) arI AR Z H Cs kb s' a' σ' G := fun s' a' σ' hSS hw hO hX' hCR hK => by
    obtain ⟨Ac', Lst', R⟩ := jowes_ksD arI s s' a a' σ σ' hw hO _ H Cs Ac Lst _ rfl J0 hX'
    have J' := J0.cs_frameK hw.1 hX' (KBack.of_kheap hO.kh) (IpcFrKeep.of_kheap hO.kh)
      (JCs.same J0 hSS (KSz.of_kheap hO.kh)) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (J0.vkeep_of hw fun _ hb => J0.ksW_nv hb)
      hSS hK hO.idle
    have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
    have horig : σ'.isOriginalCap = σ.isOriginalCap :=
      orig_eq_of_slots hDS.1.2.2.2.1 hCR.2.2.2.1 J.kern.orig J'.kern.orig hSS
    have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
      ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
    have hL' : LiveJ (L := L) Z.th H G s' σ' :=
      hL.of_sameZ hSS hmem horig hO.idle hK J.kern.cs0 hTz fun p hp => J'.jcov.dead p (Or.inr hp)
    exact ⟨⟨V, Ac', Lst', _, J', by rw [hw.1]; exact hkb, fun u e => hns u (by rw [← hO.act]; exact e),
      hsg.of_eq hO.kh hO.inode hO.idle, hp0.of_ppk (PPK.of_ksStep hO)⟩, hL',
      ⟨lst, J.dbgWF_keep J' rfl rfl hDW hK⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · refine WP.spec_mono (WP.spec_and (post_irqX arI hAM hX J.ks (hLy.1) hmask hfree _ hclw)
      (J.postDbg hAM hmask hfree hcl hcln hclw)) ?_
    rintro r ⟨⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩, hK⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX' hCR hK⟩
  · have ⟨_, hl, hfl⟩ := hclw
    refine WP.spec_mono (WP.spec_and (post_ioX arI hX J.ks (hLy.2) _ _ _ hfl hl)
      (J.postDbg hAM hmask hfree hcl hcln hclw)) ?_
    rintro r ⟨⟨hSS, -, σ', hm, hCR, hw, hO, hX'⟩, hK⟩
    exact ⟨hSS, σ', hm, hCR, hfin _ _ _ hSS hw hO hX' hCR hK⟩

end

end

end Fl4Proofs.P3
