/-
P3 (DESIGN.md §9), VSpace: **the native VSpace caps' finalisation at `XTop`**
(`XFinHyps.rest`, `xFinRest_of`).

`Vs.vs_fin` at `FootSR TopSR s VsFootW` (the VSpace hypothesis structures
carried to the footprint: `VsHyps.foot`, `VsFinHyps.foot`) gives the
finalisation with `FinX` after and FL4's writes in `VsFootW`. `XTopAt` after
at the same sets (the ghost tree `G'` of the step): the kernel base and the
domain-schedule words kept (`dom_of_foot`), the spec's domain schedule kept
(`Vs.dk_finaliseCap`), the SC objects kept (`MaxK.mk_archFinaliseCapS`:
`archFinaliseCap` keeps every SC), the MDB invariant by the step
(`MdbStep.okv`), `IpcRel` and `ScApart` from `TopSR`/`TopPlaced` after.

The premise left (`hpre`, at the `XTopAt` states) is the VSpace cap
invariant at the sets (`VsCapsIn`, [J]: l4v `valid_cap` for the arch caps),
with the platform's arch interface (`ArchRefines`, [P]).
-/
import Fl4Proofs.P3.VsThX
import Fl4Proofs.P3.DelObjVs
import Fl4Proofs.P3.XTopDel
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.ScSchedBsa
open Aeneas Aeneas.Std Result

/-! ## The spec's arch finalisation keeps the SCs -/

namespace Fl4Proofs.P3.MaxK
open Fl4Spec Classical

noncomputable section

/-- The VSpace operations unfolded down to `MK`'s leaves. -/
macro "vs_unf" : tactic => `(tactic| first
  | unfold deleteAsidPool | unfold deleteAsid | unfold hwAsidInvalidate | unfold flushAll | unfold flushTable
  | unfold flushPd | unfold flushPdpt | unfold unmapPdpt | unfold unmapPd | unfold unmapPageTable
  | unfold unmapPage | unfold invalidatePageStructureCacheAsid | unfold setAsidPool
  | unfold lookupPdptSlot | unfold lookupPdSlot | unfold lookupPtSlot
  | unfold getPt | unfold getPte | unfold getPd | unfold getPde | unfold getPdpt | unfold getPdpte
  | unfold getPml4 | unfold getPml4e | unfold setPt | unfold setPd | unfold setPdpt | unfold setPml4
  | unfold storePte | unfold storePde | unfold storePdpte | unfold storePml4e)

set_option maxHeartbeats 4000000 in
/-- **The spec's arch finalisation keeps every SC's `REFILL_MAX` and bound
thread.** -/
theorem mk_archFinaliseCapS (c : ArchCap) (x : Bool) : MK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap
  repeat' (first | mk_leaf | mk_step0 | fk_unf | sched_unf | vs_unf)

end

end Fl4Proofs.P3.MaxK

/-! ## The VSpace hypotheses carried to the footprint -/

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s0 : S} {W : U64 → Prop}
variable {A : Type} {ar : machine.Arch A} {SR : S → A → Fl4Spec.State Unit → Prop}

theorem VsRootHyps.foot (hH : VsRootHyps st A ar SR) : VsRootHyps st A ar (FootSR st SR s0 W) where
  setVs := fun s a σ ptr asid h => WP.spec_mono (hH.setVs s a σ ptr asid h.1) fun _ h2 => ⟨h2, h.2⟩
  setKernel := fun s a σ h => WP.spec_mono (hH.setKernel s a σ h.1) fun r ⟨h1, h2⟩ => ⟨h1, h2, h.2⟩

theorem VsHyps.foot (hsubV : ∀ b, VsWrite P (L.ksb s0) b → W b) (hH : VsHyps st A ar P th SR) :
    VsHyps st A ar P th (FootSR st SR s0 W) where
  stable := fun s s' a σ σ' h hw hst =>
    ⟨hH.stable s s' a σ σ' h.1 hw hst, (h.2.trans hw).mono fun b hb =>
      hb.elim id fun hv => hsubV b (by rw [← h.2.1]; exact hv)⟩
  invalOK := hH.invalOK
  inval := fun s a σ asid vs hR h =>
    WP.spec_mono (hH.inval s a σ asid vs hR h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  invEpt := fun s a σ root mask h => WP.spec_mono (hH.invEpt s a σ root mask h.1) fun _ h2 => ⟨h2, h.2⟩
  curT := fun s a σ h => hH.curT s a σ h.1
  root := hH.root.foot

theorem VsFinHyps.foot (hsub : ∀ b, VsFootW0 st th L4 L3 L2 L1 s0 b → W b)
    (hsubV : ∀ b, VsWrite P (L.ksb s0) b → W b) (hH : VsFinHyps st A ar th P L4 L3 L2 L1 SR) :
    VsFinHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  pt := hH.pt.foot hsub
  pd := hH.pd.foot hsub
  pdpt := hH.pdpt.foot hsub
  pg := hH.pg.foot hsub
  del := hH.del.foot hsubV

end

end

end Fl4Proofs.P3.Vs

/-! ## `XFinHyps.rest` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The VSpace caps' spec finalisation keeps the SC objects. -/
theorem szKeep_finVs {c : capability.Cap} (hv : IsVsFin c) {b : Bool} {σ σ' : Fl4Spec.State Unit}
    {x : Fl4Spec.Cap × Fl4Spec.Cap} (hm : (x, σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) :
    Sched.SzKeep σ σ' := by
  have hac : ∃ ac, absCap c = .archObjectCap ac := by
    cases c <;> simp only [IsVsFin] at hv <;> exact ⟨_, rfl⟩
  obtain ⟨ac, e⟩ := hac
  rw [e] at hm
  have hk := MaxK.mk_archFinaliseCapS ac b σ _ hm
  intro p y n hp
  obtain ⟨y0, h0, -, -⟩ := hk p y n hp
  exact ⟨y0, h0⟩

set_option maxHeartbeats 8000000 in
/-- **`XFinHyps.rest` holds** (module docstring). -/
theorem xFinRest_of [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} (hA : ArchRefines arI AR)
    (hpre : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
      VsCapsIn Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s) Z.G) :
    XFinAt (L := L) arI FinRestK AR th := by
  intro Z s a σ sl c hth hX hK hTh hk hDS hAs hc hfk hw
  have hVC := hpre Z s a σ hth hX
  subst hth
  have hS := hX.fin.1
  have hv := isVsFin_of_rest hk hfk
  have hH : VsFinHyps st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s
        (VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s)) :=
    VsFinHyps.foot (fun _ h => h.toW) (fun b h => Or.inr (Or.inr (Or.inr (Or.inl h)))) (vsFinHyps_top hA)
  refine WP.spec_mono (vs_fin hH s a σ Z.G sl hDS hAs
    ⟨hS.2.pl, hS.2.pt, hS.2.ps, hS.2.pv, hS.2.po, hS.2.vo, hS.2.sd, hS.2.vs,
      ⟨⟨hS, P1.WritesIn.refl _ _⟩, hX.fin.2⟩, hVC⟩ c hc hv _ hw) ?_
  rintro r ⟨⟨h1, h2, h3, σ', G', hm, hDS', hcv, hoth, hmS, ⟨hS', hW⟩, hx'⟩, -⟩
  have hkb : L.ksb r.2.1 = L.ksb s := hW.1
  have hdom := dom_of_foot hS (Or.inr hW)
  have hdk := Vs.DK.dom (Vs.dk_finaliseCap _ _) hm
  have hsk := szKeep_finVs hv hm
  obtain ⟨hPl, -, -, hD, hMO, hIA, -⟩ := hX.rel
  refine ⟨h1, h2, h3, σ', G', hm, hDS', hcv, hoth, hmS, ⟨Z.vs, ⟨hS', hx'⟩,
    ⟨hPl, hDS'.1, hDS'.2.2, ?_, ?_, ?_, ScApart.of_top hS'.2⟩, ?_, hX.esa.mono hkb hsk⟩, hkb⟩
  · rw [hkb]; exact hD.frame hdom.2 hdk.1 hdk.2
  · rw [hkb]; exact hmS.okv hMO
  · rw [hkb]; exact hIA
  · obtain ⟨⟨hSch, hEp, hNt, -⟩, -⟩ := hS'
    exact IpcRel.of hNt hEp (sched_sc hSch)

end

end

end Fl4Proofs.P3
