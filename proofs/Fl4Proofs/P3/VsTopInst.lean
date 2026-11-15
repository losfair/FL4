/-
P3 (DESIGN.md §9), VSpace: **the hypothesis structures of the VSpace
invocations for the composite relation** (`SR := TopSR`): every stability
and flush field from VsTop/VsArch (`capStable_top` … `flushTbl_top`, with
the arch interface `ArchRefines`); the `restart` fields (and ASID pool's
`curT`) stay arguments.
-/
import Fl4Proofs.P3.VsArch
import Fl4Proofs.P3.VsSubTop
import Fl4Proofs.P3.VsExtTac
import Fl4Proofs.P3.VsDecFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`set_thread_state Restart` of the current thread** for the CSpace,
ASID and page-table relations and the composite relation (`restart_top`,
`set_thread_state_slots`); the pool table references kept. -/
theorem restart_full {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (ct : U64) (x : Fl4Spec.Tcb) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hcur : ct.bv = σ.curThread) (hk : σ.kheap ct.bv = some (.tcb x)) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : Fl4Spec.runnable x.tcbState = true) :
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      (PtRel L4 L3 L2 L1 (L.mem s) σ →
        PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)) ∧
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      L.ksb s' = L.ksb s ∧ (PoolsIn P L4 (L.mem s) → PoolsIn P L4 (L.mem s')) ⦄ := by
  refine WP.spec_mono (WP.spec_and (restart_top s a σ ct x hS hR hcur hk hrun)
    (set_thread_state_slots th hS.2.pl s ct sched.TS_RESTART htcb hact)) ?_
  rintro s' ⟨⟨hVs, hPt', hS', hk', hmV⟩, hSS⟩
  refine ⟨(hSt.tcb_state hk (by rw [stsAct_kheap, updK_kheap])).of_caps (fun y hy => hSS.capAt hy),
    hSV.of_caps (fun y hy => hSS.capAt hy), hVs, hPt', hS', hk', fun hPI q hq lo hl => ?_⟩
  have hw : VsWrite P (L.ksb s) (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  rw [hmV _ (hw.aligned hS.2.vs) (vsWrite_vobj hS.2.vs hw)]
  exact hPI q hq lo hl

/-- `VsMapHyps` for the composite relation. -/
theorem vsMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsMapHyps st A arI L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  noFlush := fun s a σ vs asid hS => noFlush_top s a σ vs asid hS
  flushPage := fun s a σ vs asid vaddr hS => flushPage_top hA s a σ vs asid vaddr hS
  flushAsid := fun s a σ vs asid hS => flushAsid_top hA s a σ vs asid hS

/-- `VsMapHypsAll` for the composite relation. -/
theorem vsMapHypsAll_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsMapHypsAll st A arI L1 L2 L3 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable1 := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  stable2 := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  stable3 := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  noFlush := fun s a σ vs asid hS => noFlush_top s a σ vs asid hS
  flushPage := fun s a σ vs asid vaddr hS => flushPage_top hA s a σ vs asid vaddr hS
  flushAsid := fun s a σ vs asid hS => flushAsid_top hA s a σ vs asid hS

/-- `VsFrameHyps` for the composite relation (the restart field given). -/
theorem vsFrameHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsFrameHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  map := vsMapHyps_top hA
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `VsFrameHypsL` for the composite relation (the restart field given). -/
theorem vsFrameHypsL_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsFrameHypsL st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  map := vsMapHypsAll_top hA
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `VsUnmapPageHyps` for the composite relation. -/
theorem vsUnmapPageHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsUnmapPageHyps st A arI L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  ptStable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushPgOK := fun σ v asid => flushPgOK_top σ v asid
  flushPg := fun s a σ asid vaddr hS => flushPg_top hA s a σ asid vaddr hS

/-- `VsPtMapHyps` for the composite relation (the restart field given). -/
theorem vsPtMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPtMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `VsPdMapHyps` for the composite relation (the restart field given). -/
theorem vsPdMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `VsPdptMapHyps` for the composite relation (the restart field given). -/
theorem vsPdptMapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdptMapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pml4Stable := fun s s' a σ σ' hS hw hc => pml4Stable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- `VsPtInnerHyps` for the composite relation. -/
theorem vsPtInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPtInnerHyps st A arI L2 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  flushTblOK := fun σ vs v pt asid hal hk => flushTblOK_top σ vs v pt asid hal hk
  flushTbl := fun s a σ vs v pt asid hS hal hk => flushTbl_top hA s a σ vs v pt asid hS hal hk

/-- `VsPdInnerHyps` for the composite relation. -/
theorem vsPdInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdInnerHyps st A arI L3 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  flushOK := fun vs asid σ => flushOK_top vs asid σ
  flushPS := fun s a σ vs asid hS => flushPS_top hA s a σ vs asid hS
  flushAllOK := fun σ vs asid => flushAllOK_top σ vs asid
  flushAllH := fun s a σ vs asid hS => flushAllH_top hA s a σ vs asid hS

/-- `VsPdptInnerHyps` for the composite relation. -/
theorem vsPdptInnerHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdptInnerHyps st A arI L4 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pml4Stable := fun s s' a σ σ' hS hw hc => pml4Stable_top s s' a σ σ' hS hw hc
  flushAllOK := fun σ vs asid => flushAllOK_top σ vs asid
  flushAllH := fun s a σ vs asid hS => flushAllH_top hA s a σ vs asid hS

/-- `VsFrameUnmapHyps` for the composite relation (the restart field given). -/
theorem vsFrameUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsFrameUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsUnmapPageHyps := vsUnmapPageHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2 hPI⟩

/-- `VsPtUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPtUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPtUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPtInnerHyps := vsPtInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  ptStable := fun s s' a σ σ' hS hw hc => ptStable_top s s' a σ σ' hS hw hc
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2 hPI⟩

/-- `VsPdUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPdUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPdInnerHyps := vsPdInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdStable := fun s s' a σ σ' hS hw hc => pdStable_top s s' a σ σ' hS hw hc
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2 hPI⟩

/-- `VsPdptUnmapHyps` for the composite relation (the restart field given). -/
theorem vsPdptUnmapHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsPdptUnmapHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  toVsPdptInnerHyps := vsPdptInnerHyps_top hA
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  pdptStable := fun s s' a σ σ' hS hw hc => pdptStable_top s s' a σ σ' hS hw hc
  restart := fun s a σ ct x hSt hSV hR hPt hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (restart_full s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun) fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1 hPt, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2 hPI⟩

/-- `VsMpHyps` for the composite relation (`RegOK := RegOKTop`). -/
theorem vsMpHyps_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} :
    VsMpHyps st A th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) (RegOKTop (L := L) N T C E R B c) where
  restart := fun s a σ ct x hS hR hPt hcur hk _ _ hrun => by
    refine WP.spec_mono (WP.spec_and (restart_top s a σ ct x hS hR hcur hk hrun) (set_thread_state_cpu s ct _)) ?_
    rintro s' ⟨⟨hVs, hPt', hS', hk', -⟩, -, hcpu⟩
    refine ⟨hVs, hPt' hPt, hS', hk', hcpu, fun p h => ⟨h.1, h.2.1, fun a' h1 h2 ho => h.2.2.1 a' h1 h2
      (OObj.of_kh hk' (fun q y n hq => ?_) ho), h.2.2.2⟩⟩
    rw [stsAct_kheap, updK_kheap] at hq
    by_cases e : q = ct.bv
    · subst e; rw [Function.update_self] at hq; cases hq
    · rwa [Function.update_of_ne e] at hq
  mpSR := fun s s' a σ σ' p hi hhi hS hRO hksb hcpu hW hMp => mpSR_top s s' a σ σ' p hi hhi hS hRO hksb hcpu hW hMp

/-- **The current thread at `TopSR`**: FL4's `cur_thread` word is the spec's
`cur_thread` (`SchedSpec.curThread`; the core is `c`, `SchedCore.cur`). -/
theorem curT_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ) :
    sched.cur_thread st s ⦃ ct => ct.bv = σ.curThread ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.1.1.lists
  refine WP.spec_mono (cur_thread_spec' s) ?_
  rintro v rfl
  rw [hs.curThread, hc.cur]; rfl

/-- `VsInvHyps` for the composite relation (`curT` given). -/
theorem vsInvHyps_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop}
    (hcurT : ∀ s a σ, TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ →
      sched.cur_thread st s ⦃ ct => ct.bv = σ.curThread ⦄) :
    VsInvHyps st A th P (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  curT := hcurT
  restart := fun s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) s a σ ct x hSt hSV hR hS hcur hk htcb hact hrun)
      fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  capStable := fun s s' a σ σ' hS hw hc => capStable_top s s' a σ σ' hS hw hc
  vsStable := fun s s' a σ σ' hS hw hc => vsStable_top s s' a σ σ' hS hw hc

/-- `VsFlushHyps` for the composite relation. -/
theorem vsFlushHyps_top {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (hA : ArchRefines arI AR) :
    VsFlushHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  restart := fun s a σ ct x hU hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.1 hcur hk htcb hact hrun)
      fun _ h => ⟨h.2.2.2.2.1, h.1, h.2.1, h.2.2.1, h.2.2.2.1 hU.2.2.2.2⟩
  flushAllOK := fun σ vs asid => flushAllOK_top σ vs asid
  flushAllH := fun s a σ vs asid hS => flushAllH_top hA s a σ vs asid hS

/-- `VsReplyHyps` for the composite relation (the Ep side's `reply`,
`replyR` given). -/
theorem vsReplyHyps_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop}
    (hreply : ∀ s a σ (ct : U64) (call : Bool) (v : U64),
      UR st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
      vspace.reply1 st s ct call v ⦃ s' => ¬ (replyRunning ct.bv call [v.bv] σ).2 ∧
        ∃ σ', ((), σ') ∈ (replyRunning ct.bv call [v.bv] σ).1 ∧
          UR st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a σ' ⦄)
    (hreplyR : ∀ s a σ (ct : U64) (call : Bool) (v : U64),
      UR st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ → ct.bv = σ.curThread →
      vspace.reply1 st s ct call v ⦃ s' =>
        ¬ ((Fl4Spec.setThreadState (Z := Unit) ct.bv .restart >>= fun _ => replyRunning ct.bv call [v.bv]) σ).2 ∧
        ∃ σ', ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) ct.bv .restart >>= fun _ =>
          replyRunning ct.bv call [v.bv]) σ).1 ∧
          UR st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s' a σ' ⦄) :
    VsReplyHyps st A th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  restart := fun s a σ ct x hU hcur hk htcb hact hrun =>
    WP.spec_mono (restart_full s a σ ct x hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.1 hcur hk htcb hact hrun)
      fun _ h => ⟨h.2.2.2.2.1, h.1, h.2.1, h.2.2.1, h.2.2.2.1 hU.2.2.2.2⟩
  reply := hreply
  replyR := hreplyR

variable {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **A frame cap with the composite relation** (`decode_invocation_frame`; the placement from `TopPlaced`). -/
theorem decode_invocation_frame_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : FrameLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {p : U64} {sz : capability.FrameSize} {rt asid va : U64} {d m : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Frame p sz rt d m false asid va))
    (hfm : m = true → asid ≠ 0#u64)
    (hpaS : sz = .Small → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaL : sz = .Large → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hpaH : sz = .Huge → (core.num.U64.wrapping_sub p layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub p layout.PPTR_BASE)
    (hAl : ErrRel (.Sys .AlignmentError) .alignmentError)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef)
    (hGA : lbl = fl4_abi.label.X86PageGetAddress →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hTAC : lbl = fl4_abi.label.X86PageTestAndClearAccessed →
      DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct)
    (hDS : lbl = fl4_abi.label.X86PageDeriveSubframe →
      DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
        buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ∨
    DecOKRM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Frame p sz rt d m false asid va) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer ct := (decode_invocation_frame arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vsFrameHyps_top hA) (vsFrameHypsL_top hA)
    (vsFrameUnmapHyps_top hA) hS hS.2.vs hS.2.sd hS.2.pt hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlbl length buf ct hct hcur htcb
    hact hrun args hlen hargs hpc hidx hcap hfm hpaS hpaL hpaH hAl extra excaps hext blk call don fp ci buffer hGA hTAC (fun h => DecOKM.toMQ arI (hDS h))).imp (fun h => DecOKMQ.toM arI h.2.2) (fun h => h.2)


set_option maxHeartbeats 8000000 in
/-- **A page-table cap with the composite relation** (`decode_invocation_page_table`; the placement from `TopPlaced`). -/
theorem decode_invocation_page_table_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageTableMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (hlU : lbl = fl4_abi.label.X86PageTableUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageTableMap → lbl ≠ fl4_abi.label.X86PageTableUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageTableUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0)) (hpL : ptr ∈ L1)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageTable ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQ.toM arI <| decode_invocation_page_table arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vsPtMapHyps_top hA) (vsPtUnmapHyps_top hA) hS hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer

set_option maxHeartbeats 8000000 in
/-- **A page-directory cap with the composite relation** (`decode_invocation_page_directory`; the placement from `TopPlaced`). -/
theorem decode_invocation_page_directory_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PageDirectoryMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (hlU : lbl = fl4_abi.label.X86PageDirectoryUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PageDirectoryMap → lbl ≠ fl4_abi.label.X86PageDirectoryUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0)) (hpL : ptr ∈ L2)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.PageDirectory ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQ.toM arI <| decode_invocation_page_directory arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vsPdMapHyps_top hA) (vsPdUnmapHyps_top hA) hS hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer

set_option maxHeartbeats 8000000 in
/-- **A PDPT cap with the composite relation** (`decode_invocation_pdpt`; the placement from `TopPlaced`). -/
theorem decode_invocation_pdpt_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hA : ArchRefines arI AR) (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hPI : PoolsIn P L4 (L.mem s))
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86PDPTMap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (hlU : lbl = fl4_abi.label.X86PDPTUnmap → Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (hlO : lbl ≠ fl4_abi.label.X86PDPTMap → lbl ≠ fl4_abi.label.X86PDPTUnmap →
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTMap ∧ Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64PDPTUnmap)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {ptr asid0 va0 : U64} {mp : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0)) (hpL : ptr ∈ L3)
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    (hm0 : mp = true → asid0 ≠ 0#u64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ x vc vc' xsl rest, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok vc ∧
        CapRel vc vc' ∧ excaps = (vc', xsl) :: rest ∧
        ∀ p' asid', vc = .Pml4 p' true asid' → p' ∈ L4 ∧ asid' ≠ 0#u64 ∧ asid'.val < 2 ^ 20)
    (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length (cslotAddr (pc.bv, idx)) (.Pdpt ptr mp asid0 va0) blk call don fp
      buf extra slbl (args.map UScalar.bv) ci (pc.bv, idx) excaps buffer :=
  DecOKMQ.toM arI <| decode_invocation_pdpt arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vsPdptMapHyps_top hA) (vsPdptUnmapHyps_top hA) hS hS.2.vs hS.2.sd hS.2.pt
    hS.2.ps hS.2.pv hS.2.po hPI hR hPt lbl slbl hlM hlU hlO length buf ct hct hcur htcb hact hrun args hlen hargs
    hpc hidx hcap hpL hpa hm0 extra excaps hext blk call don fp ci buffer

set_option maxHeartbeats 8000000 in
/-- **An ASID pool cap with the composite relation** (`decode_invocation_asid_pool`; `curT` from `curT_top`). -/
theorem decode_invocation_asid_pool_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlA : lbl = fl4_abi.label.X86ASIDPoolAssign ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hNative : ∀ x, vspace.extra extra 0#usize = ok (some x) →
      ∀ p level mapped asid va, capAt (L.mem s) x ≠ ok (.Ept p level mapped asid va))
    (hext : (vspace.extra extra 0#usize = ok none ∧ excaps = []) ∨
      ∃ (pc : U64) (r : Nat) (idx : List Bool) (vc : capability.Cap) (vc' : Fl4Spec.Cap)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), th pc = some (.cnode r) ∧ idx.length = r ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pc.bv, idx))) ∧
        capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok vc ∧ CapRel vc vc' ∧ excaps = (vc', (pc.bv, idx)) :: rest ∧
        ∀ p1 a1, vc = .Pml4 p1 false a1 → p1 ≠ 0#u64)
    (slot : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot (.AsidPool ptr base) blk call don fp buf extra slbl args ci sl excaps
      buffer :=
  DecOKMQ.toM arI <| decode_invocation_asid_pool arI th hS.2.pl s ar σ G hCR hFI hMO (fun _ _ _ _ => trivial) (vsInvHyps_top curT_top) hS hS.2.vs hS.2.sd hR hS.2.vo
    lbl slbl hlA length buf ct hct hcur htcb hact hrun ptr base hb hb20 extra excaps hNative hext slot blk call don fp args ci sl
    buffer

set_option maxHeartbeats 8000000 in
/-- **The ASID control cap with the composite relation** (`decode_invocation_asid_control`; `RegOK := RegOKTop`). -/
theorem decode_invocation_asid_control_top (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hU : UtInv (L.mem s) G)
    (hMO : MdbOKV (L.ksb s) (L.mem s) G)
    {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {AR : A → Fl4Spec.Cr3 → Prop}
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s ar σ)
    (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hrun : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
          MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOKTop (L := L) N T C E R B c s σ p)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKM (L := L) arI s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excaps buffer :=
  DecOKMQ.toM arI <| decode_invocation_asid_control arI th hS.2.pl s ar σ G hCR hFI hU hMO (fun _ _ _ _ => trivial) vsMpHyps_top hS hR hPt hS.2.vs hS.2.pt
    hS.2.vo hS.2.po hS.2.pv lbl slbl hlM length buf ct hct hcur htcb hact hrun args hlen hargs extra excaps hext slot
    blk call don fp ci sl buffer

end

end

end Fl4Proofs.P3.Vs
