/-
P3 (DESIGN.md §9), TCB: **the TCB cap installs at `WJL`** (XTopJointWJL's
deletion-loop invariant with liveness), so that the Thread cap's
SetTimeoutEndpoint, SetSpace, SetIPCBuffer, Configure and SetSchedParams
labels delete at `WJL` (`delHypsJL`) instead of at `WJR` (which needed
`JDelParts.live`).

* `bufHypW_JL`: TcbCaps' `BufHypW` at `WJL` (as XTopJointTcbInstall's
  `bufHypW_J`): the IPC-buffer word by `JAtZ.bufWrJ` at a dead set grown by
  the TCB zombies' TCBs, `wjl_keep` (the debug words kept: a TCB word of
  `KW`, `P1.dbgW_not_kw`); the tail's `reschedule_required` keeps the slots,
  the original bits (`orig_eq_of_slots`), the debug words (P1's
  `reschedule_required.blk` footprint) and the TCB zombies' TCBs dead
  (`JAtZ.deadP_hstep`, as XTopJointRest's `jowes_sched`), so `LiveJ`
  (`LiveJ.of_sameZ`), `DbgWF` and `NullOrig` after.
* `insWJ_wjl`: XTopJointTcbInstall's `InsWJ` at `WJL` (the insert by
  XTopJointWJLIns' `LiveDN.insT`); `tcbInsW_wjl`: `TcbInsW` at `WJL` with
  XTopJointWJLDel's `delHypsJL`.
-/
import Fl4Proofs.P3.XTopJointWJLIns
import Fl4Proofs.P3.XTopJointTcbSsp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64}

set_option maxHeartbeats 8000000 in
/-- **TcbCaps' `BufHypW` at `WJL`** (module docstring). -/
theorem bufHypW_JL {t : U64} (ht : Z.th t = some .tcb) (kb addr : U64) :
    BufHypW (L := L) (WJL (L := L) arI AR Z H Cs kb) Z.th t addr addr.bv := by
  refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G hDS hW => ?_⟩
  · obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, hDW, hN⟩ := hW
    have hX := J.xtop
    have htT : t ∈ Z.T := J.thT t ht
    obtain ⟨Q, R0, hc, hs⟩ := hX.fin.1.1.1.lists
    obtain ⟨x, hk, -⟩ := hs.tcb t htT
    have hta := hc.tcbs t htT
    have hwa : P1.Aligned (tIpcBufA t) := tIpcBufA_aligned hta
    refine WP.spec_mono (set_ipc_buffer_wr s t addr) ?_
    rintro s' rfl
    have hstep := tcbBufStep_upd hk addr.bv
    have J0 := J.addDeadSet (E := ZTcb (L := L) Z.th s) hL.ztcb
    obtain ⟨V', J'⟩ := J0.bufWrJ htT hk addr (ipcframe_null_of hX.rel.2.1.1 ht hk hnull)
    have hSS : SlotsSame Z.th (L.mem s) (L.mem (L.wr s (tIpcBufA t) addr)) :=
      hX.slotsSame_of (P1.writesIn_wr hwa) (fun b hb => by subst hb; exact tcb_oobj htT hta (by decide) (by decide))
    have hCR' := J'.xtop.rel.2.1
    have hDS1 := hDS.of_same hSS hCR' hstep.ksub
    have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s (L.wr s (tIpcBufA t) addr) :=
      dbgKeep_of_writes J.blk (P1.writesIn_wr hwa) fun b hb => by
        subst hb
        exact P1.dbgW_not_kw J.blk (Or.inl ⟨t, J.zH.1 t htT, 3512#u64, by decide, by decide, by decide, by decide, rfl⟩)
    obtain ⟨hL1, hDW1, hN1⟩ := wjl_keep arI (V1 := V') J hDS hL hDW hN J' (fun p hp => Or.inr hp) hSS hDS1 hdk rfl
    refine ⟨hSS, _, ?_, hCR', hstep.ksub, ⟨V', Ac, Lst, _, J', by rw [L.ksb_wr]; exact hkb, fun u e => hns u e,
      hsg.of_slotK (SlotK.ipcBuf hk addr.bv) rfl rfl, hp0.of_ppk (PPK.updTcbSc hk rfl)⟩, hL1, hDW1, hN1⟩
    rw [Notif.threadSet_eq _ hk]; rfl
  · obtain ⟨⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩ := hW
    have hX := J.xtop
    have hS := hX.fin.1.1.1
    obtain ⟨Q, R0, hc, hs⟩ := hS.lists
    have hcur : σ.curThread = (L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)).bv := by
      rw [hs.curThread, hc.cur]; rfl
    rw [cur_thread_eq]
    simp only [bind_ok, tcb_eq_ct]
    by_cases e : t = L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)
    · simp only [e, decide_true, ↓reduceIte]
      have hA1 : Notif.ActReady σ := J.inv.actReady
      obtain ⟨σ', hres, hK', hdl', hds'⟩ := rescheduleRequired_k hA1
      have hN0 := hX.fin.1.1.2.2.1
      refine WP.spec_bind (WP.spec_and (WP.spec_and (WP.spec_and (Sched.reschedule_required_refines s _ hN0 hS hA1)
        (Sched.reschedule_required_sfootI hS)) (spec_self (Sched.reschedule_required_sfootI hS)))
        (P1.sched.reschedule_required.blk s J.blk)) ?_
      rintro s5 ⟨⟨⟨⟨σ3, he3, -, -, -, -⟩, hw⟩, hrun5⟩, -, hft⟩
      rw [hres] at he3
      have e3 : σ3 = σ' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he3))).2.symm
      subst σ3
      have hSt := schedStep_resched (th := Z.th) hA1 hrun5 hres hK' hdl' hds'
      obtain ⟨Ac5, Lst5, D5, J5⟩ := J.schedJ hSt
      have hact5 := Sched.rescheduleRequired_action hA1 hres
      have hgk := gk_rescheduleRequired' σ ((), σ') (by rw [hres]; rfl)
      have hSS : SlotsSame Z.th (L.mem s) (L.mem s5) := hX.slotsSame_of hw (fun b hb => sfootI_oobj hc.tcbs hb)
      -- the TCB zombies' TCBs stay dead (as `jowes_sched`)
      have hwS := (hSt.2.1 _ _ _ _ J.thT hX.fin.1.1.1 hX.fin.1.1.2.2.1).2.1
      obtain ⟨-, -, -, k3, -⟩ := schW_keeps arI J hwS
      have hC : HStep σ σ' := ⟨fun p => Or.inl (by rw [hK'.kh]), hK'.rel, hK'.ct, hK'.csc, hK'.ctime, hK'.cons,
        hK'.idle, hK'.isc⟩
      have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := hC.tcbF hp; ⟨y, hy, hc.yld⟩,
        fun p x n hp => ⟨x, hC.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, hC.sc.1 hp, rfl⟩⟩
      have hdead : ∀ p ∈ ZTcb (L := L) Z.th s, DeadP (L := L) H s5 p := fun p hp =>
        J.deadP_hstep (G' := G) J5.xtop hC k3 (fun q z hq K h8 hK => J.schW_scKeep hwS hq h8 hK) J5.act.1 J5.yld yk
          (hL.ztcb p hp)
      have hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s5 := P1.Foot.dbgKeep J.blk (Set.empty_subset _) hft
      have horig : σ'.isOriginalCap = σ.isOriginalCap :=
        orig_eq_of_slots hDS.1.2.2.2.1 J5.xtop.rel.2.1.2.2.2.1 J.kern.orig J5.kern.orig hSS
      have hmem : ∀ y ∈ G.chains.flatten, IsSlot Z.th y := fun y hy => ((hDS.1.2.2.1.members y).1 hy).1
      have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s :=
        ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
      have hL1 := hL.of_sameZ hSS hmem horig (congrArg Prod.snd hgk) hdk J.kern.cs0 hTz hdead
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, hSS, σ', ?_, J5.xtop.rel.2.1, KSub.of_kheap hK'.kh, ⟨V, Ac5, Lst5, D5, J5,
        by rw [hw.1]; exact hkb, (fun u e' => by rw [hact5] at e'; cases e'),
        hsg.of_eq hK'.kh (congrArg Prod.fst hgk) (congrArg Prod.snd hgk), hp0.of_ppk (PPK.of_schedK hK' (fun u e' => by rw [hact5] at e'; cases e') (rq_of_resched hns hres))⟩,
        hL1, ⟨lst, J.dbgWF_keep J5 rfl rfl hDW hdk⟩, hN.of_same (fun y hy => hSS.capV hy) horig⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : t.bv = σ.curThread := by rw [hcur, e]
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ')) (by rw [hres]; rfl)
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨trivial, trivial, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, σ, ?_, hX.rel.2.1, KSub.refl σ,
        ⟨V, Ac, Lst, D, J, hkb, hns, hsg, hp0⟩, hL, ⟨lst, hDW⟩, hN⟩
      refine mem_bindE_ok (a := σ.curThread) (s' := σ) (mem_liftE_ok (x := (σ.curThread, σ)) rfl) ?_
      have hb : ¬ t.bv = σ.curThread := fun h => e (P1.eq_of_bv (h.trans hcur))
      simp only [Fl4Spec.NonDet.when, hb, ↓reduceIte]
      exact mem_liftE_ok (x := ((), σ)) rfl

/-- **XTopJointTcbInstall's `InsWJ` at `WJL`** (module docstring). -/
theorem insWJ_wjl (kb : U64) : InsWJ (L := L) arI AR Z H Cs kb (WJL (L := L) arI AR Z H Cs kb) := by
  refine ⟨fun _ _ _ _ h => h.1, ?_, fun _ ht addr => bufHypW_JL arI ht kb addr⟩
  intro s s' a σ σ' G G' t n c src hDS hW hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive
  obtain ⟨V, Ac, Lst, D, J, -⟩ := hW.1
  obtain ⟨V', Ac', Lst', D', J', -⟩ := id hW'
  exact ⟨hW', LiveDN.insT J hDS hW.2 J' hDS' ht hn hci hwS hnull hcap hnn hsh hlive⟩

/-- **`TcbInsW` at `WJL`** (module docstring). -/
theorem tcbInsW_wjl [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR Z.th) (hF : JThreadFinHypsU (L := L) arI AR Z.th)
    (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR) (hAM : ARMask arI AR) :
    TcbInsW (L := L) arI AR Z H Cs (fun kb => WJL (L := L) arI AR Z H Cs kb) (RdLO (L := L) (A := A) Z.th H)
      (RzJ (L := L) (A := A) H) :=
  ⟨insWJ_wjl arI, fun kb => delHypsJL arI hT hAR hK hV hF hnd hPP hAM Z H Cs kb rfl⟩

end

end

end Fl4Proofs.P3
