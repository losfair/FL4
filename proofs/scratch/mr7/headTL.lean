/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **the Thread cap's decode
at `MachPlat`**: XTopJointTcb's `decode_invocation_threadJ_step` with the
five installing labels (SetTimeoutEndpoint, SetSpace, SetIPCBuffer,
Configure, SetSchedParams) by XTopJointMRTcb's copies at `WMR MR WJL` /
`WJPM`, so the Thread cap's decode ends in `XCapP JAt (JAtPreMV MR)` from
`MRV MR ar σ` at the decode's state and `MachPlat` [P] + `MRKeepD` [P] +
`PPPlatA` [P]: no `PPPlat`.

* `BufHypW.mrv`: TcbCaps' `BufHypW` at `W` gives it at `WMR MR W` (the IPC
  buffer's `threadSet` and the tail's `rescheduleRequired` keep `msFT`).
* `insWJ_wjlM`: XTopJointTcbInstall's `InsWJ` at `WMR MR WJL` (the insert's
  `capInsert` keeps `msFT`: `mtk_capInsert`); `tcbInsWM_wjl`: `TcbInsWM` at
  `WMR MR WJL` with XTopJointMRDel's `delHypsJLM`.
* `decode_invocation_threadJ_stepM` (generated: scratch/mr7/gentcbl.py +
  headTL.lean): the copy, with the caller's restart keeping `MRV`
  (`mtk_setThreadState'`) and `PPPlatA.minBudget` for `PPPlat.minBudget`.
-/
import Fl4Proofs.P3.XTopJointTcb
import Fl4Proofs.P3.XTopJointMRTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`BufHypW` with `MRV` beside the invariant** (module docstring). -/
theorem BufHypW.mrv {W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} {th : TypedHeap} {t addr : U64}
    {ptr : Fl4Spec.VSpaceRef} (hM : MachPlat arI MR) (h : BufHypW (L := L) W th t addr ptr) :
    BufHypW (L := L) (WMR MR W) th t addr ptr := by
  refine ⟨fun s a σ G hDS hW hnull => ?_, fun s a σ G hDS hW => ?_⟩
  · refine WP.spec_mono (h.ipc s a σ G hDS hW.1 hnull) ?_
    rintro s' ⟨hSS, σ', hm, hCR, hK, hW'⟩
    exact ⟨hSS, σ', hm, hCR, hK, ⟨hW', mrv_keep hM hW.2 (MachT.mtk_threadSet' _ _ σ ((), σ') hm)⟩⟩
  · refine WP.spec_mono (h.tail s a σ G hDS hW.1) ?_
    rintro res ⟨h1, h2, hSS, σ', hm, hCR, hK, hW'⟩
    refine ⟨h1, h2, hSS, σ', hm, hCR, hK, ⟨hW', ?_⟩⟩
    rw [h2]
    exact mrv_keep hM hW.2 (dke_bind (dke_liftE (dk_gets _))
      (fun _ => dke_liftE (dk_when _ MachT.mtk_rescheduleRequired')) σ _ hm)

/-- **`InsWJ` at `WMR MR WJL`** (module docstring). -/
theorem insWJ_wjlM (hM : MachPlat arI MR) (kb : U64) :
    InsWJ (L := L) arI AR Z H Cs kb (WMR MR (WJL (L := L) arI AR Z H Cs kb)) := by
  have h0 := insWJ_wjl (L := L) arI (AR := AR) (Z := Z) (H := H) (Cs := Cs) kb
  refine ⟨fun s a σ G h => h0.wjr s a σ G h.1, ?_, fun t ht addr => (h0.buf t ht addr).mrv hM⟩
  intro s s' a σ σ' G G' t n c src hDS hW hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive
  exact ⟨h0.ins s s' a σ σ' G G' t n c src hDS hW.1 hDS' hW' ht hn hci hwS hnull hcap hnn hsh hlive,
    mrv_keep hM hW.2 (MachT.mtk_capInsert c src _ σ ((), σ') (mem_of_single hci))⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`TcbInsWM` at `WMR MR WJL`** (module docstring). -/
theorem tcbInsWM_wjl [Fl4Proofs.P1.PlainStore st] (hT : P0.ArchTotal arI) (hAR : ArchRefines arI AR)
    (hK : ARKeep arI AR) (hV : JVtHyps (L := L) arI AR Z.th) (hF : JThreadFinHypsU (L := L) arI AR Z.th)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR)
    (hAM : ARMask arI AR) :
    TcbInsWM (L := L) arI AR MR Z H Cs (fun kb => WMR MR (WJL (L := L) arI AR Z H Cs kb))
      (RdLO (L := L) (A := A) Z.th H) (RzJ (L := L) (A := A) H) :=
  ⟨fun kb => insWJ_wjlM hM kb, fun kb => delHypsJLM arI hT hAR hK hV hF hnd hM hKD hPA hAM Z H Cs kb rfl⟩

