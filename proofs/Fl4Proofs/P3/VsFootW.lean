/-
P3 (DESIGN.md §9), VSpace: **the memory footprint of the VSpace
invocations** (for the other agents' frame arguments: `DomRel`, `ScPlaced`,
`CallRel`, … through `WritesIn`).

* `VsFootW st th P L4 L3 L2 L1 s0`: the words a VSpace invocation from `s0` may
  write: the slot words (`SlotW`, `SlotWord`), the page-table words
  (`PtWAll`), the ASID table and pool words (`VsWrite P (ksb s0)`), the
  TCB state words, and the current core's scheduler-action word (the
  `Restart` of `set_thread_state`). `MakePool` also writes its frame
  (`MpFootW`).
* `FootSR st SR s0 W`: `SR` with `WritesIn s0 s W`; every hypothesis structure
  of the VSpace invocations carries over to it (`VsFrameHyps.foot`, …, one
  per structure), so the invocation theorems instantiated at `FootSR` give
  the footprint.
* The footprint theorems (`frame_map_foot`, …, `pml4_flush_foot`,
  `derive_subframe_foot`; the last through `FootSRc`): from the
  hypotheses of the invocation theorem, FL4's result state differs from
  the initial state only in `VsFootW` (`MpFootW` for `MakePool`).
-/
import Fl4Proofs.P3.VsTopInst
import Fl4Proofs.P3.UntypedInvoke
import Fl4Proofs.P3.IoPortDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The VSpace footprint** from `s0` (see the module docstring). -/
def VsFootW (st : machine.Store S) [L : LawfulStore st] (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (s0 : S) (b : U64) : Prop :=
  SlotW th b ∨ SlotWord th b ∨ PtWAll L4 L3 L2 L1 b ∨ VsWrite P (L.ksb s0) b ∨
    (∃ t, th t = some .tcb ∧ b = stA t) ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

/-- `VsFootW` without the ASID-table and pool words: the footprint of every
VSpace invocation but `Assign` and `MakePool`. -/
def VsFootW0 (st : machine.Store S) [L : LawfulStore st] (th : TypedHeap) (L4 L3 L2 L1 : Set U64) (s0 : S) (b : U64) : Prop :=
  SlotW th b ∨ SlotWord th b ∨ PtWAll L4 L3 L2 L1 b ∨
    (∃ t, th t = some .tcb ∧ b = stA t) ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem VsFootW0.toW {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s0 : S} {b : U64}
    (h : VsFootW0 st th L4 L3 L2 L1 s0 b) : VsFootW st th P L4 L3 L2 L1 s0 b := by
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- `MakePool`'s footprint: `VsFootW` and the new pool's frame (the
untyped cap `uc`'s first page). -/
def MpFootW (st : machine.Store S) [L : LawfulStore st] (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (s0 : S) (uc : capability.Cap) (b : U64) : Prop :=
  VsFootW st th P L4 L3 L2 L1 s0 b ∨
    ∃ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧ p.val ≤ b.val ∧ b.val < p.val + 4096

/-- `SR` with the writes since `s0` in `W`. -/
def FootSR (st : machine.Store S) [L : LawfulStore st] {A : Type} (SR : S → A → Fl4Spec.State Unit → Prop) (s0 : S) (W : U64 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ WritesIn st s0 s W

/-- `MakePool`'s `RegOK` with the frame in the footprint. -/
def RegOKF (RegOK : S → Fl4Spec.State Unit → U64 → Prop) (W : U64 → Prop) (s : S) (σ : Fl4Spec.State Unit)
    (p : U64) : Prop :=
  RegOK s σ p ∧ ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → W b

/-- `FootSR` with the current thread a TCB of `th` and the scheduler-action
word outside the objects (for `VsSubHyps`, whose `restart` does not carry
them). -/
def FootSRc (st : machine.Store S) [L : LawfulStore st] {A : Type} (th : TypedHeap)
    (SR : S → A → Fl4Spec.State Unit → Prop) (s0 : S) (W : U64 → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ WritesIn st s0 s W ∧ (∀ t : U64, t.bv = σ.curThread → th t = some .tcb) ∧
    OutsideObjects th (L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION)

theorem stsAct_updK_cur (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (o : Fl4Spec.KernelObject)
    (t : Fl4Spec.ObjRef) : (stsAct (updK σ p o) t).curThread = σ.curThread := by
  unfold stsAct updK; split_ifs <;> rfl

theorem insStep_cur {σ σ' : Fl4Spec.State Unit} (h : InsStep σ σ') : σ'.curThread = σ.curThread := by
  obtain ⟨p, r, cs, idx, a, cdt, io, -, rfl⟩ := h; rfl

theorem stA_al {th : TypedHeap} (hPl : Placed th) {t : U64} (ht : th t = some .tcb) : Aligned (stA t) := by
  have h1 := hPl.align t _ ht
  have h2 := hPl.fits t _ ht
  have hv : (stA t).val = t.val + 3328 := by
    rw [stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    simp [objSize] at h2; omega
  unfold Aligned; rw [hv]; omega

variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s0 : S} {W : U64 → Prop}

/-- **`set_thread_state`'s writes** are in the footprint. -/
theorem sts_foot (hPl : Placed th) (hsub : ∀ b, VsFootW0 st th L4 L3 L2 L1 s0 b → W b) {s : S} {ct v : U64}
    (hw : WritesIn st s0 s W) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    sched.set_thread_state st s ct v ⦃ s' => WritesIn st s0 s' W ⦄ := by
  refine WP.spec_mono (WP.spec_and (set_thread_state_frame s ct v (stA_al hPl htcb) hact.1)
    (set_thread_state_cpu s ct v)) ?_
  rintro s' ⟨hF, hk, hc⟩
  have hsa : L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION := by
    unfold LawfulStore.nodeAt; rw [hw.1, hw.2.1]
  refine ⟨hk.trans hw.1, hc.trans hw.2.1, fun b hb hn => ?_⟩
  rw [hF b hb (fun e => hn (hsub b (Or.inr (Or.inr (Or.inr (Or.inl ⟨ct, htcb, UScalar.eq_of_val_eq e⟩))))))
    (fun e => hn (hsub b (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← hsa]; exact UScalar.eq_of_val_eq e)))))))]
  exact hw.2.2 b hb hn

/-- A stability field carried to `FootSR`. -/
theorem foot_stab {A : Type} {SR : S → A → Fl4Spec.State Unit → Prop} {X : U64 → Prop}
    {Step : Fl4Spec.State Unit → Fl4Spec.State Unit → Prop} (hX : ∀ b, X b → W b)
    (h : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' X → Step σ σ' → SR s' a σ') :
    ∀ s s' a σ σ', FootSR st SR s0 W s a σ → WritesIn st s s' X → Step σ σ' → FootSR st SR s0 W s' a σ' :=
  fun s s' a σ σ' h1 hw hst => ⟨h s s' a σ σ' h1.1 hw hst, (h1.2.trans hw).mono fun b hb => hb.elim id (hX b)⟩

theorem slotW_foot {b : U64} (h : SlotW th b) : VsFootW0 st th L4 L3 L2 L1 s0 b := Or.inl h
theorem ptW_foot {b : U64} (h : PtW L1 b) : VsFootW0 st th L4 L3 L2 L1 s0 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, e⟩))
theorem pdW_foot {b : U64} (h : PdW L2 b) : VsFootW0 st th L4 L3 L2 L1 s0 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, e⟩))
theorem pdptW_foot {b : U64} (h : PdptW L3 b) : VsFootW0 st th L4 L3 L2 L1 s0 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨p, Or.inr (Or.inl hp), i, hi, e⟩))
theorem pml4W_foot {b : U64} (h : Pml4W L4 b) : VsFootW0 st th L4 L3 L2 L1 s0 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨p, Or.inl hp, i, hi, e⟩))

variable {A : Type} {ar : machine.Arch A} {SR : S → A → Fl4Spec.State Unit → Prop}
  (hsub : ∀ b, VsFootW0 st th L4 L3 L2 L1 s0 b → W b)
include hsub

theorem VsMapHyps.foot (hH : VsMapHyps st A ar L1 SR) : VsMapHyps st A ar L1 (FootSR st SR s0 W) where
  stable := foot_stab (fun b h => hsub b (ptW_foot h)) hH.stable
  flushOK := hH.flushOK
  noFlush := fun s a σ vs asid h => by
    obtain ⟨σ', h1, h2⟩ := hH.noFlush s a σ vs asid h.1; exact ⟨σ', h1, h2, h.2⟩
  flushPage := fun s a σ vs asid va h =>
    WP.spec_mono (hH.flushPage s a σ vs asid va h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushAsid := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAsid s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsMapHypsAll.foot (hH : VsMapHypsAll st A ar L1 L2 L3 SR) : VsMapHypsAll st A ar L1 L2 L3 (FootSR st SR s0 W) where
  stable1 := foot_stab (fun b h => hsub b (ptW_foot h)) hH.stable1
  stable2 := foot_stab (fun b h => hsub b (pdW_foot h)) hH.stable2
  stable3 := foot_stab (fun b h => hsub b (pdptW_foot h)) hH.stable3
  flushOK := hH.flushOK
  noFlush := fun s a σ vs asid h => by
    obtain ⟨σ', h1, h2⟩ := hH.noFlush s a σ vs asid h.1; exact ⟨σ', h1, h2, h.2⟩
  flushPage := fun s a σ vs asid va h =>
    WP.spec_mono (hH.flushPage s a σ vs asid va h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushAsid := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAsid s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsFrameHyps.foot (hPl : Placed th) (hH : VsFrameHyps st A ar th P L4 L3 L2 L1 SR) :
    VsFrameHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  map := hH.map.foot hsub

theorem VsFrameHypsL.foot (hPl : Placed th) (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR) :
    VsFrameHypsL st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  map := hH.map.foot hsub

theorem VsUnmapPageHyps.foot (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) :
    VsUnmapPageHyps st A ar L3 L2 L1 (FootSR st SR s0 W) where
  ptStable := foot_stab (fun b h => hsub b (ptW_foot h)) hH.ptStable
  pdStable := foot_stab (fun b h => hsub b (pdW_foot h)) hH.pdStable
  pdptStable := foot_stab (fun b h => hsub b (pdptW_foot h)) hH.pdptStable
  flushPgOK := hH.flushPgOK
  flushPg := fun s a σ asid va h =>
    WP.spec_mono (hH.flushPg s a σ asid va h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsFrameUnmapHyps.foot (hPl : Placed th) (hH : VsFrameUnmapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsFrameUnmapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  toVsUnmapPageHyps := hH.toVsUnmapPageHyps.foot hsub
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun hPI)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, hw⟩ =>
        ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6, a7⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable

theorem VsPtMapHyps.foot (hPl : Placed th) (hH : VsPtMapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPtMapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  pdStable := foot_stab (fun b h => hsub b (pdW_foot h)) hH.pdStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdMapHyps.foot (hPl : Placed th) (hH : VsPdMapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPdMapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  pdptStable := foot_stab (fun b h => hsub b (pdptW_foot h)) hH.pdptStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdptMapHyps.foot (hPl : Placed th) (hH : VsPdptMapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPdptMapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  pml4Stable := foot_stab (fun b h => hsub b (pml4W_foot h)) hH.pml4Stable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPtInnerHyps.foot (hH : VsPtInnerHyps st A ar L2 SR) : VsPtInnerHyps st A ar L2 (FootSR st SR s0 W) where
  pdStable := foot_stab (fun b h => hsub b (pdW_foot h)) hH.pdStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushTblOK := hH.flushTblOK
  flushTbl := fun s a σ vs v pt asid h hv hpt =>
    WP.spec_mono (hH.flushTbl s a σ vs v pt asid h.1 hv hpt) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPtUnmapHyps.foot (hPl : Placed th) (hH : VsPtUnmapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPtUnmapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  toVsPtInnerHyps := hH.toVsPtInnerHyps.foot hsub
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun hPI)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, hw⟩ =>
        ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6, a7⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  ptStable := foot_stab (fun b h => hsub b (ptW_foot h)) hH.ptStable

theorem VsPdInnerHyps.foot (hH : VsPdInnerHyps st A ar L3 SR) : VsPdInnerHyps st A ar L3 (FootSR st SR s0 W) where
  pdptStable := foot_stab (fun b h => hsub b (pdptW_foot h)) hH.pdptStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAllH s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdUnmapHyps.foot (hPl : Placed th) (hH : VsPdUnmapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPdUnmapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  toVsPdInnerHyps := hH.toVsPdInnerHyps.foot hsub
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun hPI)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, hw⟩ =>
        ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6, a7⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  pdStable := foot_stab (fun b h => hsub b (pdW_foot h)) hH.pdStable

theorem VsPdptInnerHyps.foot (hH : VsPdptInnerHyps st A ar L4 SR) :
    VsPdptInnerHyps st A ar L4 (FootSR st SR s0 W) where
  flushPSKeep := fun s a σ asid h => WP.spec_mono (hH.flushPSKeep s a σ asid h.1) fun _ hS => ⟨hS, h.2⟩
  pml4Stable := foot_stab (fun b h => hsub b (pml4W_foot h)) hH.pml4Stable
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAllH s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdptUnmapHyps.foot (hPl : Placed th) (hH : VsPdptUnmapHyps st A ar th P L4 L3 L2 L1 SR) :
    VsPdptUnmapHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  toVsPdptInnerHyps := hH.toVsPdptInnerHyps.foot hsub
  restart := fun s a σ ct x h1 h2 h3 h4 hS hcur hk htcb hact hrun hPI =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 h4 hS.1 hcur hk htcb hact hrun hPI)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, hw⟩ =>
        ⟨a1, a2, a3, a4, ⟨a5, hw⟩, a6, a7⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  pdptStable := foot_stab (fun b h => hsub b (pdptW_foot h)) hH.pdptStable

theorem VsInvHyps.foot (hPl : Placed th) (hsubV : ∀ b, VsWrite P (L.ksb s0) b → W b) (hH : VsInvHyps st A th P SR) :
    VsInvHyps st A th P (FootSR st SR s0 W) where
  curT := fun s a σ h => hH.curT s a σ h.1
  restart := fun s a σ ct x h1 h2 h3 hS hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x h1 h2 h3 hS.1 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a5, a6⟩, hw⟩ => ⟨a1, a2, a3, ⟨a5, hw⟩, a6⟩
  capStable := foot_stab (fun b h => hsub b (slotW_foot h)) hH.capStable
  vsStable := fun s s' a σ σ' h hw hst =>
    ⟨hH.vsStable s s' a σ σ' h.1 hw hst, (h.2.trans hw).mono fun b hb =>
      hb.elim id fun hv => hsubV b (by rw [← h.2.1]; exact hv)⟩

theorem VsFlushHyps.foot (hPl : Placed th) (hH : VsFlushHyps st A ar th P L4 L3 L2 L1 SR) :
    VsFlushHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  restart := fun s a σ ct x hU hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x ⟨hU.1.1, hU.2⟩ hcur hk htcb hact hrun)
      (sts_foot hPl hsub hU.1.2 htcb hact)) fun _ ⟨h, hw⟩ => ⟨⟨h.1, hw⟩, h.2⟩
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAllH s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsSubHyps.foot (hPl : Placed th) (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) :
    VsSubHyps st A P L4 L3 L2 L1 th (FootSRc st th SR s0 W) where
  restart := fun s a σ ct x hS hR hPt hcur hk hrun => by
    have hsa : L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION =
        L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION := by
      unfold LawfulStore.nodeAt; rw [hS.2.1.1, hS.2.1.2.1]
    refine WP.spec_mono (WP.spec_and (hH.restart s a σ ct x hS.1 hR hPt hcur hk hrun)
      (sts_foot hPl hsub hS.2.1 (hS.2.2.1 ct hcur) (by rw [hsa]; exact hS.2.2.2))) ?_
    rintro _ ⟨⟨a1, a2, a3, a4⟩, hw⟩
    exact ⟨a1, a2, ⟨a3, hw, fun t ht => hS.2.2.1 t (ht.trans (stsAct_updK_cur _ _ _ _)), hS.2.2.2⟩, a4⟩
  insStable := fun s s' a σ σ' hS hw hI =>
    ⟨hH.insStable s s' a σ σ' hS.1 hw hI, (hS.2.1.trans hw).mono fun b hb => hb.elim id fun h => hsub b (Or.inr (Or.inl h)),
      fun t ht => hS.2.2.1 t (ht.trans (insStep_cur hI)), hS.2.2.2⟩

theorem VsMpHyps.foot (hPl : Placed th) (hsubV : ∀ b, VsWrite P (L.ksb s0) b → W b)
    {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK) :
    VsMpHyps st A th P L4 L3 L2 L1 (FootSR st SR s0 W) (RegOKF RegOK W) where
  restart := fun s a σ ct x hS h1 h2 hcur hk htcb hact hrun =>
    WP.spec_mono (WP.spec_and (hH.restart s a σ ct x hS.1 h1 h2 hcur hk htcb hact hrun)
      (sts_foot hPl hsub hS.2 htcb hact)) fun _ ⟨⟨a1, a2, a3, a4, a5, a6⟩, hw⟩ =>
        ⟨a1, a2, ⟨a3, hw⟩, a4, a5, fun p hp => ⟨a6 p hp.1, hp.2⟩⟩
  mpSR := fun s s' a σ σ' p hi hhi hS hRO hksb hcpu hW hMp =>
    ⟨hH.mpSR s s' a σ σ' p hi hhi hS.1 hRO.1 hksb hcpu hW hMp,
      ⟨hksb.trans hS.2.1, hcpu.trans hS.2.2.1, fun b hb hn => by
        rw [hW b hb (by
          rintro (h | h | h)
          · exact hn (hsub b (Or.inr (Or.inl h)))
          · exact hn (hRO.2 b h.1 h.2)
          · exact hn (hsubV b (Or.inl ⟨hi, hhi, by rw [← hS.2.1]; exact h⟩)))]
        exact hS.2.2.2 b hb hn⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **The footprint of `frame_map_rel`** (`VsFootW`). -/
theorem frame_map_foot [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Small) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (frame_map_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsFrameHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hPO := hPO) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (f := f) (hsz := hsz) (hfw := hfw) (hfe := hfe) (hfcv := hfcv) (hfm := hfm) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `frame_map_large_rel`** (`VsFootW`). -/
theorem frame_map_large_foot [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Large) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503599625273344#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (frame_map_large_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsFrameHypsL.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hPO := hPO) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (f := f) (hsz := hsz) (hfw := hfw) (hfe := hfe) (hfcv := hfcv) (hfm := hfm) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `frame_map_huge_rel`** (`VsFootW`). -/
theorem frame_map_huge_foot [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameHypsL st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hsz : f.size = .Huge) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f)) (hfcv : CapValid th (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    (hpa : (core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE &&& 4503598553628672#u64) =
      core.num.U64.wrapping_sub f.ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_page_map st ar s a length (cslotAddr (pc.bv, idx)) f buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (frame_map_huge_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsFrameHypsL.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hPO := hPO) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (f := f) (hsz := hsz) (hfw := hfw) (hfe := hfe) (hfcv := hfcv) (hfm := hfm) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `frame_unmap_rel`** (`VsFootW`). -/
theorem frame_unmap_foot [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFrameUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hPI : PoolsIn P L4 (L.mem s)) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (f : vspace.FrameCap) (hfw : CapWf (frameCapOf f)) (hfe : EncWf (frameCapOf f))
    (hfm : f.mapped = true → f.asid ≠ 0#u64)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (frameCapOf f))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageUnmap)
    (length buf : U64) (call : Bool) (ex : Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (xs : Fl4Spec.CapRef) (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.decode_frame st ar s a fl4_abi.label.X86PageUnmap length (cslotAddr (pc.bv, idx)) (frameCapOf f) call buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (frame_unmap_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsFrameUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hPI := hPI) (hPO := hPO) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (f := f) (hfw := hfw) (hfe := hfe) (hfm := hfm) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (hcx := hcx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (call := call) (ex := ex) (args := args) (xs := xs) (vcs := vcs)) ?_
  intro res h
  obtain ⟨-, iv, σ', -, -, hU, -⟩ := h
  exact hU.1.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pt_map_rel`** (`VsFootW`). -/
theorem pt_map_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPtMapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL1 : ptr ∈ L1) (hfe : EncWf (.PageTable ptr mp asid0 va0))
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageTableMap length (cslotAddr (pc.bv, idx))
      (.PageTable ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pt_map_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPtMapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL1 := hpL1) (hfe := hfe) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pd_map_rel`** (`VsFootW`). -/
theorem pd_map_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdMapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, PdptW L3 b → ¬ VsWrite P (L.ksb s) b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL2 : ptr ∈ L2) (hfe : EncWf (.PageDirectory ptr mp asid0 va0))
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageDirectoryMap length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pd_map_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPdMapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL2 := hpL2) (hfe := hfe) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pdpt_map_rel`** (`VsFootW`). -/
theorem pdpt_map_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdptMapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV : ∀ b, Pml4W L4 b → ¬ VsWrite P (L.ksb s) b)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL3 : ptr ∈ L3) (hfe : EncWf (.Pdpt ptr mp asid0 va0))
    (hpa : (core.num.U64.wrapping_sub ptr layout.PPTR_BASE &&& 4503599627366400#u64) =
      core.num.U64.wrapping_sub ptr layout.PPTR_BASE)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTMap)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize) {x : obj.Slot} (hex : vspace.extra ex 0#usize = ok (some x))
    {vc : capability.Cap} (hcx : capAt (L.mem s) x = ok vc) {vc' : Fl4Spec.Cap} (hvr : CapRel vc vc')
    (xsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hvc : ∀ p asid, vc = .Pml4 p true asid → p ∈ L4 ∧ asid ≠ 0#u64 ∧ asid.val < 2 ^ 20) :
    vspace.decode_table st ar s a fl4_abi.label.X86PDPTMap length (cslotAddr (pc.bv, idx))
      (.Pdpt ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pdpt_map_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPdptMapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV := hPV) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL3 := hpL3) (hfe := hfe) (hpa := hpa) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (ex := ex) (x := x) (hex := hex) (vc := vc) (hcx := hcx) (vc' := vc') (hvr := hvr) (xsl := xsl) (rest := rest) (hvc := hvc)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pt_unmap_rel`** (`VsFootW`). -/
theorem pt_unmap_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPtUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV2 : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b)
    (hPV1 : ∀ b, PtW L1 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL1 : ptr ∈ L1) (hfe : EncWf (.PageTable ptr mp asid0 va0))
    (hm0 : mp = true → asid0 ≠ 0#u64 ∧ va0.bv &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageTable ptr mp asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageTableUnmap)
    (length buf : U64) (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {fin : Bool} (hfin : cdt.is_final_capability st s (cslotAddr (pc.bv, idx)) = ok fin)
    (hfinR : fin = true ↔ Fl4Spec.isFinalCap'
      (.archObjectCap (.pageTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageTableUnmap length (cslotAddr (pc.bv, idx))
      (.PageTable ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pt_unmap_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPtUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV2 := hPV2) (hPV1 := hPV1) (hPI := hPI) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL1 := hpL1) (hfe := hfe) (hm0 := hm0) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (hcx := hcx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (xs := xs) (ex := ex) (vcs := vcs) (fin := fin) (hfin := hfin) (hfinR := hfinR)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, hU, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hU.1.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pd_unmap_rel`** (`VsFootW`). -/
theorem pd_unmap_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV3 : ∀ b, PdptW L3 b → ¬ VsWrite P (L.ksb s) b)
    (hPV2 : ∀ b, PdW L2 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL2 : ptr ∈ L2) (hfe : EncWf (.PageDirectory ptr mp asid0 va0))
    (hm0 : mp = true → asid0 ≠ 0#u64)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.PageDirectory ptr mp asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PageDirectoryUnmap)
    (length buf : U64) (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {fin : Bool} (hfin : cdt.is_final_capability st s (cslotAddr (pc.bv, idx)) = ok fin)
    (hfinR : fin = true ↔ Fl4Spec.isFinalCap'
      (.archObjectCap (.pageDirectoryCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ) :
    vspace.decode_table st ar s a fl4_abi.label.X86PageDirectoryUnmap length (cslotAddr (pc.bv, idx))
      (.PageDirectory ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pd_unmap_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPdUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV3 := hPV3) (hPV2 := hPV2) (hPI := hPI) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL2 := hpL2) (hfe := hfe) (hm0 := hm0) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (hcx := hcx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (xs := xs) (ex := ex) (vcs := vcs) (fin := fin) (hfin := hfin) (hfinR := hfinR)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, hU, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hU.1.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pdpt_unmap_rel`** (`VsFootW`). -/
theorem pdpt_unmap_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsPdptUnmapHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hPV4 : ∀ b, Pml4W L4 b → ¬ VsWrite P (L.ksb s) b)
    (hPV3 : ∀ b, PdptW L3 b → ¬ VsWrite P (L.ksb s) b) (hPI : PoolsIn P L4 (L.mem s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ) (hS : SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (ptr asid0 va0 : U64) (mp : Bool) (hpL3 : ptr ∈ L3) (hfe : EncWf (.Pdpt ptr mp asid0 va0))
    (hm0 : mp = true → asid0 ≠ 0#u64)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pdpt ptr mp asid0 va0))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64PDPTUnmap)
    (length buf : U64) (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (ex : Array obj.Slot 3#usize)
    (vcs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    {fin : Bool} (hfin : cdt.is_final_capability st s (cslotAddr (pc.bv, idx)) = ok fin)
    (hfinR : fin = true ↔ Fl4Spec.isFinalCap'
      (.archObjectCap (.pdPointerTableCap ptr.bv (if mp then some (asid0.bv, va0.bv) else none))) σ) :
    vspace.decode_table st ar s a fl4_abi.label.X86PDPTUnmap length (cslotAddr (pc.bv, idx))
      (.Pdpt ptr mp asid0 va0) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pdpt_unmap_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsPdptUnmapHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hPP := hPP) (hPS := hPS) (hPV4 := hPV4) (hPV3 := hPV3) (hPI := hPI) (hSt := hSt) (hSV := hSV) (hR := hR) (hPt := hPt) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (hPO := hPO) (ptr := ptr) (asid0 := asid0) (va0 := va0) (mp := mp) (hpL3 := hpL3) (hfe := hfe) (hm0 := hm0) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (hcx := hcx) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (xs := xs) (ex := ex) (vcs := vcs) (fin := fin) (hfin := hfin) (hfinR := hfinR)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, hU, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hU.1.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `assign_rel`** (`VsFootW`). -/
theorem assign_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsInvHyps st A th P SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hVP : VsPlaced P (L.ksb s))
    (hD : VsSlotsDisj th P (L.ksb s))
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s)) (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hS : SR s a σ) {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (ptr base : U64) (hb : base.val % 512 = 0) (hb20 : base.val < 2 ^ 20)
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Fl4Spec.Data) (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr)
    (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize)
    {pc : U64} {r : Nat} (hpc : th pc = some (.cnode r)) {idx : List Bool} (hidx : idx.length = r)
    (hex : vspace.extra ex 0#usize = ok (some (cslotAddr (pc.bv, idx))))
    {ptr1 asid0 : U64} (hcx : capAt (L.mem s) (cslotAddr (pc.bv, idx)) = ok (.Pml4 ptr1 false asid0))
    (hcan : Canonical ptr1) (hp10 : ptr1 ≠ 0#u64)
    (htcb : ∀ ct : U64, ct.bv = σ.curThread → th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDPoolAssign length slot (.AsidPool ptr base) call buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (assign_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsInvHyps.foot (s0 := s) (fun _ h => h.toW) hPl (fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (A := A) (ar := ar) (th := th) (P := P) (s := s) (a := a) (σ := σ) (hPl := hPl) (hVP := hVP) (hD := hD) (hSt := hSt) (hSV := hSV) (hR := hR) (xct := xct) (hkt := hkt) (hrun := hrun) (ptr := ptr) (base := base) (hb := hb) (hb20 := hb20) (slbl := slbl) (hl := hl) (args := args) (xs := xs) (cte := cte) (rest := rest) (length := length) (slot := slot) (call := call) (buf := buf) (ex := ex) (pc := pc) (r := r) (hpc := hpc) (idx := idx) (hidx := hidx) (hex := hex) (ptr1 := ptr1) (asid0 := asid0) (hcx := hcx) (hcan := hcan) (hp10 := hp10) (htcb := htcb) (hact := hact) (hVO := hVO)) ?_
  intro res h
  rcases h with h | ⟨-, -, asid, σ', -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `makepool_rel`** (`VsFootW`; with the new pool frame, `MpFootW`). -/
theorem makepool_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {slbl : Fl4Spec.Data} (hl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (xs : Fl4Spec.CapRef) (cte : Fl4Spec.CslotPtr) (slot : obj.Slot) (call : Bool)
    (ex : Array obj.Slot 3#usize)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    (hex0 : vspace.extra ex 0#usize = ok (some (cslotAddr (pp.bv, idx))))
    {y : obj.Slot} (hex1 : vspace.extra ex 1#usize = ok (some y))
    {uc : capability.Cap} (hcx : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc) {uc' : Fl4Spec.Cap}
    (hur : CapRel uc uc')
    {rc : capability.Cap} (hcy : capAt (L.mem s) y = ok rc) {rc' : Fl4Spec.Cap} (hrr : CapRel rc rc')
    (hrv : CapValid th rc)
    (ysl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hRg : ∀ p fi, uc = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      MpRegion th G P L4 L3 L2 L1 (L.ksb s) p ∧ RegOK s σ p) (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) :
    vspace.decode st ar s a fl4_abi.label.X86ASIDControlMakePool length slot .AsidControl call buf ex ⦃ res =>
      WritesIn st s res.2.1 (MpFootW st th P L4 L3 L2 L1 s uc) ⦄ := by
  refine WP.spec_mono (makepool_rel (SR := FootSR st SR s (MpFootW st th P L4 L3 L2 L1 s uc)) (hH := VsMpHyps.foot (s0 := s) (fun _ h => Or.inl h.toW) hPl (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) hH) (hS := ⟨hS, WritesIn.refl _ _⟩) (RegOK := RegOKF RegOK (MpFootW st th P L4 L3 L2 L1 s uc)) (hRg := fun p fi h hc => ⟨(hRg p fi h hc).1, (hRg p fi h hc).2, fun b h1 h2 => Or.inr ⟨p, fi, h, h1, h2⟩⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (G := G) (hPl := hPl) (hSt := hSt) (hSV := hSV) (hM := hM) (hC := hC) (hI := hI) (hU := hU) (hR := hR) (hPt := hPt) (hVP := hVP) (hPP := hPP) (hVO := hVO) (hPO := hPO) (hPV := hPV) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (slbl := slbl) (hl := hl) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (xs := xs) (cte := cte) (slot := slot) (call := call) (ex := ex) (pp := pp) (rs := rs) (hpp := hpp) (idx := idx) (hidx := hidx) (hex0 := hex0) (y := y) (hex1 := hex1) (uc := uc) (hcx := hcx) (uc' := uc') (hur := hur) (rc := rc) (hcy := hcy) (rc' := rc') (hrr := hrr) (hrv := hrv) (ysl := ysl) (rest := rest) (hFI := hFI) (hFR := hFR)) ?_
  intro res h
  rcases h with h | ⟨-, p, dest, ps, base, -, -, σ', th', G', -, -, -, -, -, -, -, -, -, -, -, hSR, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSR.2

set_option maxHeartbeats 4000000 in
/-- **The footprint of `pml4_flush_rel`** (`VsFootW`). -/
theorem pml4_flush_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsFlushHyps st A ar th P L4 L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hU : UR st th P L4 L3 L2 L1 SR s a σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (p asid : U64) (mp : Bool) (length : U64) (slot : obj.Slot) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (hPl : Placed th) :
    vspace.decode st ar s a fl4_abi.label.X86PML4Flush length slot (.Pml4 p mp asid) call buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (pml4_flush_rel (SR := FootSR st SR s (VsFootW st th P L4 L3 L2 L1 s)) (hH := VsFlushHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH) (hU := ⟨⟨hU.1, WritesIn.refl _ _⟩, hU.2⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (s := s) (a := a) (σ := σ) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (p := p) (asid := asid) (mp := mp) (length := length) (slot := slot) (call := call) (buf := buf) (ex := ex)) ?_
  intro res h
  rcases h with h | ⟨-, iv, σ', -, -, -, hU⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hU.1.2


set_option maxHeartbeats 4000000 in
/-- **The footprint of `derive_subframe_rel`** (`VsFootW`). -/
theorem derive_subframe_foot {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop}
    (hH : VsSubHyps st A P L4 L3 L2 L1 th SR) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {ptr rt fa fv : U64} {sz : capability.FrameSize} {dev mm : Bool}
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s))
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b) (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Frame ptr sz rt dev mm false fa fv))
    (hno : sz = .Large → dev = false → ∀ x ∈ G.chains.flatten,
      Disj (capV (L.mem s) x) (.Frame ptr sz rt dev mm false fa fv) ∨
      (isFrame (capV (L.mem s) x) = true ∧ revOf (L.mem s) x = false) ∨
      Within (.Frame ptr sz rt dev mm false fa fv) (capV (L.mem s) x))
    (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) (hVC : VsCapsIn P L4 L3 L2 L1 (L.mem s) G)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : ct.bv = σ.curThread)
    {xct : Fl4Spec.Tcb} (hkt : σ.kheap σ.curThread = some (.tcb xct))
    (hrun : Fl4Spec.runnable xct.tcbState = true)
    (htcb : th ct = some .tcb) (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (ex : Array obj.Slot 3#usize) {y : obj.Slot} (hex0 : vspace.extra ex 0#usize = ok (some y))
    {nc : capability.Cap} (hcy : capAt (L.mem s) y = ok nc) {nc' : Fl4Spec.Cap} (hnr : CapRel nc nc')
    (hnv : CapValid th nc) (nsl : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    vspace.derive_subframe st ar s a length (cslotAddr (pp.bv, idx)) (.Frame ptr sz rt dev mm false fa fv) buf ex ⦃ res =>
      WritesIn st s res.2.1 (VsFootW st th P L4 L3 L2 L1 s) ⦄ := by
  refine WP.spec_mono (derive_subframe_rel (SR := FootSRc st th SR s (VsFootW st th P L4 L3 L2 L1 s))
    (hH := VsSubHyps.foot (s0 := s) (fun _ h => h.toW) hPl hH)
    (hS := ⟨hS, WritesIn.refl _ _, fun t ht => by
      have e := P1.eq_of_bv (ht.trans hcur.symm); subst e; exact htcb, hact⟩) (A := A) (ar := ar) (th := th) (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) (hPl := hPl) (hPP := hPP) (pp := pp) (rs := rs) (hpp := hpp) (idx := idx) (hidx := hidx) (ptr := ptr) (rt := rt) (fa := fa) (fv := fv) (sz := sz) (dev := dev) (mm := mm) (s := s) (a := a) (σ := σ) (G := G) (hSt := hSt) (hSV := hSV) (hM := hM) (hC := hC) (hI := hI) (hU := hU) (hR := hR) (hPt := hPt) (hVP := hVP) (hVO := hVO) (hPO := hPO) (hcap := hcap) (hno := hno) (hFI := hFI) (hFR := hFR) (hVC := hVC) (ct := ct) (hct := hct) (hcur := hcur) (xct := xct) (hkt := hkt) (hrun := hrun) (htcb := htcb) (hact := hact) (length := length) (buf := buf) (args := args) (hlen := hlen) (hargs := hargs) (ex := ex) (y := y) (hex0 := hex0) (nc := nc) (hcy := hcy) (nc' := nc') (hnr := hnr) (hnv := hnv) (nsl := nsl) (rest := rest)) ?_
  intro res h
  rcases h with h | ⟨-, -, iv, -, σ', G', -, -, hSub, -⟩
  · obtain ⟨-, -, -, -, -, hs, -⟩ := h; rw [hs]; exact WritesIn.refl _ _
  · exact hSub.sr.2.1

end

end

end Fl4Proofs.P3.Vs
