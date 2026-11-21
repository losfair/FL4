/-
P3 (DESIGN.md §9), scheduler: **`possible_switch_to` at `J`**
(`JAtZ.switchJ`; toward `JReplyRestHyp`'s tail and `JSendRestHyp`'s switch
to a woken receiver).

* `sched.possible_switch_to.blk` (P1): `possible_switch_to` of a runnable
  thread with an active SC keeps `BlkOK`, with its footprint (`.sch`, `.kw`).
* `JAtZ.switchJ`: for a schedulable thread `t`, neither current nor idle, an
  SC step with an unchanged heap: FL4's side `possible_switch_to_refines`
  with `ActReady` from `Inv` (`Inv.actReady`) and the footprint `SFoot`
  (`possible_switch_to_sfoot`); the spec's frame (`nkt_possibleSwitchTo`:
  `ScTKw` with nothing changed, `lkm_`, `pres_`, `bkm_of`), `Inv` by
  `possibleSwitchTo_qchange`, `ActIdle` by `ActIdle.possibleSwitchTo`,
  `CurInv` by `MidKn.mid3` (`mkn_possibleSwitchTo`) unless a reschedule is
  pending (it stays pending, `possibleSwitchTo_cn`), `CurOwnW` and `OffOK` by
  `Calm` (`possibleSwitchTo_calm`), `CurRunM` (no resumption made,
  `possibleSwitchTo_nr`), the dead kept (`deadP_sc_stepQ`).
-/
import Fl4Proofs.P3.XTopJointRunI
import Fl4Proofs.P3.XTopJointRestart
import Fl4Proofs.P3.ScAwaken
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt Ac Es : Set U64} {Z : U64 → Nat}

/-- **`possible_switch_to` keeps `BlkOK`**, with its footprint (module
docstring). -/
theorem sched.possible_switch_to.blk (s : S) (t : obj.Tcb) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hrun : Runnable (L.mem s (stA t)))
    (hmx : L.mem s (scA t) ≠ 0#u64 → L.rmax s (L.mem s (scA t)) ≠ 0#u64) :
    sched.possible_switch_to st s t ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch (Sg := Sg) s t Q R h0 hB hSg ht hrun
    (fun h1 => (hS.act _ (hX.2.2.bound t ht h1).1).2 (hmx h1)))
    (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s t h0 ht)) ?_
  rintro s' ⟨⟨p, -, -⟩, fw⟩
  exact ⟨⟨p.inv, p.bnd, hX.fr p.fr, hS.fr p.fr, hSg.fr p.fr⟩, fw⟩

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **`possible_switch_to` at `J`** (module docstring). -/
theorem JAtZ.switchJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    (hti : t.bv ≠ σ.idleThread) (htc : t.bv ≠ σ.curThread) (hs : Fl4Spec.schedulable t.bv σ = true) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ Lst' : U64 → List U64, JAtZ (L := L) arI AR Z H Cs Ac Lst' D s' a σ' ⦄ := by
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hwd := (schedulable_eq hR hS ht).trans hs
  obtain ⟨hrw, -, hmx, -⟩ := of_decide_eq_true hwd
  have hrun : P1.Runnable (L.mem s (P1.stA t)) := by rw [stA_tStA]; exact hrw
  refine WP.spec_mono (WP.spec_and (WP.spec_and (possible_switch_to_refines s σ hR hS J.inv.actReady t ht)
    (possible_switch_to_sfoot hR hS J.inv.actReady ht))
    (P1.sched.possible_switch_to.blk (Es := P1.EH H) s t J.blk htH hrun (fun _ e => by
      rw [e] at hmx; simp at hmx))) ?_
  rintro s' ⟨⟨⟨σ', he, hke, hfe, hS'⟩, hw⟩, hblk, hfoot⟩
  have mem : ((), σ') ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  have hR' : NtfnStateRel Z.N Z.T (L.mem s') σ' := hR.frame hS.placed hfe (KView.of_kheap hke)
  have hwK : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) := WritesIn.kfoot_of_sfoot hw
  have hwT := WritesIn.tfoot_of_kfoot hwK
  have hK : ScTKw (fun _ => False) σ σ' := nkt_possibleSwitchTo t.bv σ _ mem
  have hX' : XTopAt (L := L) AR Z s' a σ' := xtop_sc_step hX J.ip J.nk hwT (hK.ofFalse (P := fun p => p = t.bv)) hS' hR' id
  have hq := possibleSwitchTo_qchange J.inv hs he
  have hc := possibleSwitchTo_calm J.inv hs he
  have hI' : Inv σ' := J.inv.qchange hq
  have hL : LK (fun _ => False) σ σ' := lkm_possibleSwitchTo t.bv σ _ mem
  have hN' : NSC Z.N Z.C σ' := nsc_of_lk J.nsc hK hL
  have hsok : SOK (true, true) σ σ' := pres_possibleSwitchTo (f := (true, true)) t.bv σ _ mem
  obtain ⟨-, hY', hM', ⟨Lst', hCR', hRF'⟩, hRP', -⟩ :=
    ScAll.of_k hS J.rp J.yld J.mcp J.call J.rfree ⟨⟨hS', hR', hN', hI'⟩, hwK, hsok⟩
  have hF : FK σ σ' := ⟨hc.2.2.1, hc.2.2.2.2.2.1, hK.isc⟩
  have hMK := mkn_possibleSwitchTo ⟨hti, htc⟩ _ mem
  have hAI : ActIdle σ' := J.act.possibleSwitchTo J.inv hs he
  have hBK : BK σ σ' := bkm_of (nkt_possibleSwitchTo t.bv) (MaxK.mk_possibleSwitchTo' t.bv) σ _ mem
  have hbsa : BlockedScActive σ' := J.bsa.bk hBK hsok
  have hcur : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases J.cur with e | hC
    · exact Or.inl (possibleSwitchTo_cn J.inv hs he e)
    · exact (hMK.mid3 hC J.off J.inv ⟨L.curW s, J.thT _ J.kern.curT, J.kern.cur.symm⟩).1
  have hown : CurOwnW Z.T Z.C σ' := J.own.sub hc (fun u hu => by rw [hq.2.1] at hu; exact hu)
  have hoff : OffOK σ' := by
    intro h0 y n hy ha
    rw [hc.2.2.2.2.1] at h0 ⊢
    rw [hc.2.2.2.1]
    rw [hc.1, hc.2.2.1] at hy
    rw [hc.2.2.1, hc.2.2.2.2.2.2.2.2] at ha
    exact J.off h0 y n hy ha
  have hcr : CurRunM σ' := by
    by_cases hr : σ'.schedulerAction = .resumeCurThread
    · have h0 : σ.schedulerAction = .resumeCurThread := by
        by_contra h
        exact possibleSwitchTo_nr J.inv hs he h hr
      right
      rcases J.curRun.resolve_left (fun h => h h0) with h | h
      · left
        intro y hy
        rw [hc.2.1, hc.1] at hy
        exact h y hy
      · right; rw [hc.2.1, hc.2.2.2.2.2.1]; exact h
    · exact Or.inl hr
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_sc_stepQ hX' hwT hK (fun _ hp => hp.elim) hL hF hAI.1 hY' ((hsok.ykeep rfl).dk q.bv) (fun h => h) (J.jcov.dead q hq)
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  exact ⟨σ', he, Lst', J.sc_frame hwT hK hX' hCR' hRF' hY' hM' (J.sc_buf hwT hK) hRP' (J.sc_apart hwT hK)
    (J.sc_jpl hwT hK (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).2) (J.sc_jcov hwT hdead (fun q hq hn => absurd hq hn) (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2))
    (J.sc_kern hwT hK hF hX' hDbg fun _ h => h) (J.sc_utc hwT hK hDbg) hN' hI' hcur hown hoff hAI hbsa hcr hblk hKd (J.idleW_keep hX'.fin.1.1.1 hF.2.1 hF.2.2).1 J.zD⟩

end

end

end Fl4Proofs.P3
