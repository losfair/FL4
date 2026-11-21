/-
P3 (DESIGN.md §9), VSpace: **the VSpace half of `FinWorkHyp`** (DelObj):
`finalise_cap` of a final page-table, page-directory, PDPT, PML4 or ASID
pool cap (`unmap_page_table`, `unmap_page_directory`, `unmap_pdpt`,
`delete_asid`, `delete_asid_pool`) and of a mapped frame cap (`unmap_page`),
against l4v `arch_finalise_cap`.

Each post (`FinOKX`) is `FinObjHyp`'s, with the ghost tree unchanged
(`MdbStep.of_same`), plus `SlotsSame`: **none of these writes a cap slot**
(their words are page-table entries, `PtWAll`, or ASID-table and pool words,
`VsWrite`, all outside the objects), so the slot facts are the
slot-preserving ones (every cap kept). The extra relation `FinX` is kept:
`SR`, `VsRel`, `PtRel`, `PoolsIn` and `CurOK`, so the VSpace invariants
compose across finalisations.

The unmaps' and ASID deletions' relational theorems (VsPtUnmapRel, …,
VsDelRoot) are used at an instrumented relation `FinSR` (`SR`, the writes
since the start in `W`, the spec's `KFoot` and current thread), whose
hypothesis structures come from `SR`'s (`VsPtInnerHyps.fin`, …); for the ASID
deletions `FinSRP` adds `PtRel` (`VsHyps.fin`: their writes miss the page
tables, their spec steps miss the tables' objects). `PoolsIn` after an
unmap: its writes miss the pool words (`PoolsIn.of_writes`); after an ASID
deletion: its writes are zeroes (`VsZeroW`, `PoolsIn.of_zero`). `CurOK`
after an unmap: the slots and the current thread kept (`CurOK.of_same`).

The cap's side conditions (table in its ghost set, ASID non-zero, the PT's
alignment, the PML4 and the pool non-null, the pool base aligned) come
from the cap invariant `VsCapsIn` (`VsFinCtx` bundles it with the
placement and `FinX`). `vs_fin_top` gives the lot at `SR := TopSR`.
-/
import Fl4Proofs.P3.VsTopCap
import Fl4Proofs.P3.VsDelRoot
import Fl4Proofs.P3.DelObj
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`FinObjHyp`'s post**, with an extra relation `X` on the outcome. -/
def FinOKX {A : Type} (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr)
    (c : capability.Cap) (b : Bool) (X : S → A → Fl4Spec.State Unit → Prop)
    (r : (capability.Cap × capability.Cap) × S × A) : Prop :=
  r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
    ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
      DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
        (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
      MdbStep (L.mem s) G (L.mem r.2.1) G' ∧ X r.2.1 r.2.2 σ'

/-- Writes outside the objects keep every slot. -/
theorem SlotsSame.of_writes {th : TypedHeap} (hP : Placed th) {s s' : S} {W : U64 → Prop}
    (hW : WritesIn st s s' W) (hWo : ∀ b, W b → OutsideObjects th b) : SlotsSame th (L.mem s) (L.mem s') := by
  intro y hy
  have h0 := SlotFoot.of_writes hP hW hWo 0#u64 y hy
  have h1 := SlotFoot.of_writes hP hW hWo 1#u64 y hy
  by_cases e : y = 0#u64
  · subst e
    exact ⟨(h1.2.2 (by decide)).1, (h1.2.2 (by decide)).2, h1.1, h1.2.1⟩
  · exact ⟨(h0.2.2 e).1, (h0.2.2 e).2, h0.1, h0.2.1⟩

/-- **The finalisation's post from a slot-preserving step** with the spec's
`KFoot`. -/
theorem fin_after {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hSS : SlotsSame th (L.mem s) (L.mem s'))
    (hSt' : StateRel th (L.mem s') σ') (hK : KFoot σ σ') :
    DState (L := L) th s' σ' G ∧ capV (L.mem s') (cslotAddr sl) = c ∧
      (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem s') y = capV (L.mem s) y ∨
        (capV (L.mem s') y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
      MdbStep (L.mem s) G (L.mem s') G := by
  obtain ⟨hCR, hD, hFI⟩ := hDS
  have hx := hA.isSlot
  have hcv : capV (L.mem s') (cslotAddr sl) = c := by rw [hSS.capV hx]; exact capV_of_capAt hc
  obtain ⟨hCR', hFI'⟩ := crel_after hCR hFI hc hSt' (P3.SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy))
    (SlotFoot.of_same hSS _) (by rw [hcv]; exact ⟨rfl, rfl, rfl, rfl⟩) hK
  exact ⟨⟨hCR', hD.of_same hSS, hFI'⟩, hcv, fun y hy _ => Or.inl (hSS.capV hy),
    MdbStep.of_same hCR.2.2.1 hSS⟩

/-- The finalisations without work keep everything. -/
theorem fin_none {A : Type} {th : TypedHeap} {s : S} {a : A} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {b : Bool} {X : S → A → Fl4Spec.State Unit → Prop}
    (hDS : DState (L := L) th s σ G) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hX : X s a σ)
    (hrem : finRem c b = .Null)
    (hspec : ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ) ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) :
    FinOKX (L := L) th s σ G sl c b X ((.Null, .Null), s, a) ∧ SlotsSame th (L.mem s) (L.mem s) :=
  ⟨⟨hrem.symm, trivial, trivial, σ, G, hspec, hDS, capV_of_capAt hc, fun _ _ _ => Or.inl rfl,
    MdbStep.refl hDS.1.2.2.1, hX⟩, SlotsSame.refl _ _⟩

/-! ## The instrumented relation -/

/-- `SR` with the writes since `s0` in `W`, the spec's `KFoot` and the
current thread since `σ0`. -/
def FinSR (st : machine.Store S) [L : LawfulStore st] {A : Type} (SR : S → A → Fl4Spec.State Unit → Prop)
    (W : U64 → Prop) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ WritesIn st s0 s W ∧ KFoot σ0 σ ∧ σ.curThread = σ0.curThread

/-- `FinSR` with `PtRel` (the ASID deletions). -/
def FinSRP (st : machine.Store S) [L : LawfulStore st] {A : Type} (L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) (W : U64 → Prop) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  FinSR st SR W s0 σ0 s a σ ∧ PtRel L4 L3 L2 L1 (L.mem s) σ

variable {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
  {SR : S → A → Fl4Spec.State Unit → Prop} {W : U64 → Prop} {s0 : S} {σ0 : Fl4Spec.State Unit}

theorem FinSR.init {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : SR s a σ) : FinSR st SR W s σ s a σ :=
  ⟨h, WritesIn.refl _ _, KFoot.refl _, rfl⟩

/-- The spec steps of the VSpace code: `KFoot`, the current thread kept. -/
def KStep (σ σ' : Fl4Spec.State Unit) : Prop := KFoot σ σ' ∧ σ'.curThread = σ.curThread

theorem KStep.mop {α : Type} {mop : Fl4Spec.NonDet Fl4Spec.MachineState α} {σ σ' : Fl4Spec.State Unit} {r : α}
    (h : (r, σ') ∈ (Fl4Spec.doMachineOp (Z := Unit) mop σ).1) : KStep σ σ' := by
  obtain ⟨ms, rfl⟩ := doMachineOp_mem h; exact ⟨KFoot.ms _ ms, rfl⟩

theorem KStep.arch {σ σ' : Fl4Spec.State Unit}
    (h : ∃ p f f', σ.kheap p = some (.archObj f) ∧ σ' = updK σ p (.archObj f')) : KStep σ σ' := by
  obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩

theorem KStep.cr3 (σ : Fl4Spec.State Unit) (c : Fl4Spec.Cr3) : KStep σ (cr3Upd σ c) :=
  ⟨⟨rfl, rfl, fun _ h => absurd rfl h, rfl⟩, rfl⟩

theorem KStep.table (σ : Fl4Spec.State Unit) (t : Fl4Spec.AsidHighIndex → Option Fl4Spec.ObjRef) :
    KStep σ { σ with archState := { σ.archState with x64AsidTable := t } } :=
  ⟨⟨rfl, rfl, fun _ h => absurd rfl h, rfl⟩, rfl⟩

theorem KStep.flushTable {σ σ' : Fl4Spec.State Unit} {vs : Fl4Spec.ObjRef} {v : Fl4Spec.VSpaceRef}
    {pt : Fl4Spec.ObjRef} {asid : Fl4Spec.Asid}
    (hal : v &&& Fl4Spec.mask (Fl4Spec.ptTranslationBits + Fl4Spec.pageBits) = 0)
    (hf : ∃ f, σ.kheap pt = some (.archObj (.pageTable f)))
    (h : ((), σ') ∈ (Fl4Spec.flushTable (Z := Unit) vs v pt asid σ).1) : KStep σ σ' := by
  obtain ⟨f, hk⟩ := hf
  obtain ⟨ms, e, -⟩ := (flushTable_ok (vs := vs) (asid := asid) hal hk).2.2 _ h
  simp only at e; subst e; exact ⟨KFoot.ms _ ms, rfl⟩

/-- A stability field carried to `FinSR`. -/
theorem fin_stab {X : U64 → Prop} {Step : Fl4Spec.State Unit → Fl4Spec.State Unit → Prop}
    (hX : ∀ b, X b → W b) (hK : ∀ σ σ', Step σ σ' → KStep σ σ')
    (h : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' X → Step σ σ' → SR s' a σ') :
    ∀ s s' a σ σ', FinSR st SR W s0 σ0 s a σ → WritesIn st s s' X → Step σ σ' → FinSR st SR W s0 σ0 s' a σ' :=
  fun s s' a σ σ' ⟨h1, h2, h3, h4⟩ hw hst =>
    ⟨h s s' a σ σ' h1 hw hst, (h2.trans hw).mono fun b hb => hb.elim id (hX b), h3.trans (hK σ σ' hst).1,
      (hK σ σ' hst).2.trans h4⟩

/-- A spec step of `KStep` kind with the FL4 state unchanged. -/
theorem FinSR.kstep {s : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} (h : FinSR st SR W s0 σ0 s a σ)
    (hS : SR s a' σ') (hk : KStep σ σ') : FinSR st SR W s0 σ0 s a' σ' :=
  ⟨hS, h.2.1, h.2.2.1.trans hk.1, hk.2.trans h.2.2.2⟩

section Fin
variable (hW : ∀ b, PtWAll L4 L3 L2 L1 b → W b)
include hW

theorem VsPtInnerHyps.fin (hH : VsPtInnerHyps st A ar L2 SR) : VsPtInnerHyps st A ar L2 (FinSR st SR W s0 σ0) where
  pdStable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.pdStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h => WP.spec_mono (hH.flushPS s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm)⟩
  flushTblOK := hH.flushTblOK
  flushTbl := fun s a σ vs v pt asid h hal hf => WP.spec_mono (hH.flushTbl s a σ vs v pt asid h.1 hal hf)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.flushTable hal hf hm)⟩

theorem VsPdInnerHyps.fin (hH : VsPdInnerHyps st A ar L3 SR) : VsPdInnerHyps st A ar L3 (FinSR st SR W s0 σ0) where
  pdptStable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.pdptStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h => WP.spec_mono (hH.flushPS s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm)⟩
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h => WP.spec_mono (hH.flushAllH s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm)⟩

theorem VsPdptInnerHyps.fin (hH : VsPdptInnerHyps st A ar L4 SR) :
    VsPdptInnerHyps st A ar L4 (FinSR st SR W s0 σ0) where
  flushPSKeep := fun s a σ asid h => WP.spec_mono (hH.flushPSKeep s a σ asid h.1) fun _ hS => ⟨hS, h.2⟩
  pml4Stable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inl hq, i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.pml4Stable
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h => WP.spec_mono (hH.flushAllH s a σ vs asid h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm)⟩

theorem VsUnmapPageHyps.fin (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) :
    VsUnmapPageHyps st A ar L3 L2 L1 (FinSR st SR W s0 σ0) where
  ptStable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.ptStable
  pdStable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.pdStable
  pdptStable := fin_stab (fun b ⟨q, hq, i, hi, e⟩ => hW b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩)
    (fun _ _ h => by obtain ⟨p, f, f', hk, rfl⟩ := h; exact ⟨KFoot.arch hk _, rfl⟩) hH.pdptStable
  flushPgOK := hH.flushPgOK
  flushPg := fun s a σ asid va h => WP.spec_mono (hH.flushPg s a σ asid va h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm)⟩

end Fin

/-- No ASID pool is a table of the page-table relation. -/
theorem PtRel.not_pool {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : PtRel L4 L3 L2 L1 m σ) {p : Fl4Spec.ObjRef}
    {f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef} (hk : σ.kheap p = some (.archObj (.asidPool f))) {q : U64}
    (hq : q ∈ L4 ∨ q ∈ L3 ∨ q ∈ L2 ∨ q ∈ L1) : q.bv ≠ p := by
  rintro rfl
  rcases hq with hq | hq | hq | hq
  · obtain ⟨g, hg, -⟩ := hR.l4 q hq; rw [hk] at hg; cases hg
  · obtain ⟨g, hg, -⟩ := hR.l3 q hq; rw [hk] at hg; cases hg
  · obtain ⟨g, hg, -⟩ := hR.l2 q hq; rw [hk] at hg; cases hg
  · obtain ⟨g, hg, -⟩ := hR.l1 q hq; rw [hk] at hg; cases hg

/-- `PtRel` across a spec step keeping the heap. -/
theorem PtRel.same_heap {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (hR : PtRel L4 L3 L2 L1 m σ)
    (hk : σ'.kheap = σ.kheap) : PtRel L4 L3 L2 L1 m σ' :=
  hR.frame (fun _ _ => rfl) (fun q _ => by rw [hk])

/-- `VsHyps` carried to `FinSRP` (the ASID-table and pool words in `W`, apart
from the page-table words). -/
theorem VsHyps.fin (hPP : PtPlaced L4 L3 L2 L1) (hWV : ∀ b, VsWrite P (L.ksb s0) b → W b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s0) b)
    (hH : VsHyps st A ar P th SR) : VsHyps st A ar P th (FinSRP st L4 L3 L2 L1 SR W s0 σ0) where
  stable := fun s s' a σ σ' ⟨h, hPt⟩ hw hst => by
    have hks : L.ksb s = L.ksb s0 := h.2.1.1
    have kst : KStep σ σ' := by
      rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨t, rfl⟩
      · exact KStep.arch ⟨p, _, _, hk, rfl⟩
      · exact KStep.table _ t
    refine ⟨⟨hH.stable s s' a σ σ' h.1 hw hst, (h.2.1.trans hw).mono fun b hb => hb.elim id (fun hv => hWV b (hks ▸ hv)),
      h.2.2.1.trans kst.1, kst.2.trans h.2.2.2⟩, ?_⟩
    refine hPt.frame (fun b hb => hw.2.2 b (PtWAll.aligned hPP hb) (fun hv => hPV b hb (hks ▸ hv))) ?_
    rcases hst with ⟨p, f, f', hk, rfl⟩ | ⟨t, rfl⟩
    · intro q hq
      rw [updK_kheap, Function.update_of_ne (hPt.not_pool hk hq)]
    · intro q _; rfl
  invalOK := hH.invalOK
  inval := fun s a σ asid vs hR ⟨h, hPt⟩ => WP.spec_mono (hH.inval s a σ asid vs hR h.1)
    fun _ ⟨σ', hm, hS⟩ => ⟨σ', hm, h.kstep hS (KStep.mop hm), by
      obtain ⟨ms, rfl⟩ := doMachineOp_mem hm; exact hPt.same_heap rfl⟩
  invEpt := fun s a σ root mask ⟨h, hPt⟩ =>
    WP.spec_mono (hH.invEpt s a σ root mask h.1)
      (fun _ hS => ⟨⟨hS, h.2⟩, hPt⟩)
  curT := fun s a σ h => hH.curT s a σ h.1.1
  root :=
    { setVs := fun s a σ ptr asid ⟨h, hPt⟩ => WP.spec_mono (hH.root.setVs s a σ ptr asid h.1)
        fun _ hS => ⟨h.kstep hS (KStep.cr3 _ _), hPt.same_heap rfl⟩
      setKernel := fun s a σ ⟨h, hPt⟩ => WP.spec_mono (hH.root.setKernel s a σ h.1)
        fun _ ⟨e, hS⟩ => ⟨e, h.kstep hS (KStep.cr3 _ _), hPt.same_heap rfl⟩ }

/-! ## The VSpace invariants across -/

/-- `PoolsIn` across writes apart from the pool words. -/
theorem PoolsIn.of_writes {s s' : S} {W : U64 → Prop} (hPI : PoolsIn P L4 (L.mem s)) (hW : WritesIn st s s' W)
    (hVP : VsPlaced P (L.ksb s)) (hWV : ∀ b, W b → ¬ VsWrite P (L.ksb s) b) : PoolsIn P L4 (L.mem s') := by
  intro p hp lo hl hne
  have hw : VsWrite P (L.ksb s) (peA p lo) := Or.inr ⟨p, hp, lo, hl, rfl⟩
  have e := hW.2.2 _ (VsWrite.aligned hVP hw) (fun h => hWV _ h hw)
  rw [e] at hne ⊢; exact hPI p hp lo hl hne

/-- `PoolsIn` across zero writes (the ASID deletions). -/
theorem PoolsIn.of_zero {s s' : S} (hPI : PoolsIn P L4 (L.mem s)) (hZ : VsZeroW st P s s')
    (hVP : VsPlaced P (L.ksb s)) : PoolsIn P L4 (L.mem s') := by
  intro p hp lo hl hne
  have hw : VsWrite P (L.ksb s) (peA p lo) := Or.inr ⟨p, hp, lo, hl, rfl⟩
  by_cases e : L.mem s' (peA p lo) = L.mem s (peA p lo)
  · rw [e] at hne ⊢; exact hPI p hp lo hl hne
  · exact absurd (hZ.2.2 _ (VsWrite.aligned hVP hw) e).2 hne

/-- `CurOK` across a step keeping the slots and the current thread. -/
theorem CurOK.of_same {s s' : S} {σ σ' : Fl4Spec.State Unit} (hC : CurOK st th s σ)
    (hSS : SlotsSame th (L.mem s) (L.mem s')) (hc : σ'.curThread = σ.curThread) : CurOK st th s' σ' := by
  obtain ⟨t, h1, h2, h3⟩ := hC
  refine ⟨t, h1.trans hc.symm, h2, fun p asid h => h3 p asid ?_⟩
  rwa [hSS.capAt ⟨t, 1, Or.inr ⟨h2, by decide⟩, rfl⟩] at h

/-! ## The finalisations -/

/-- **The VSpace invariants of the posts**: `SR`, the ASID and page-table
relations, the pools' entries in `L4`, the current thread. -/
def FinX (st : machine.Store S) [L : LawfulStore st] {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ VsRel P (L.mem s) (L.ksb s) σ ∧ PtRel L4 L3 L2 L1 (L.mem s) σ ∧ PoolsIn P L4 (L.mem s) ∧
    CurOK st th s σ

/-- **The ghost form gives the slot form** (`VCapOK.toW`; a slot outside
the tree holds the null cap). -/
theorem VsCapsIn.slotsW {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {m : U64 → U64} {G : MdbGhost}
    (h : VsCapsIn P L4 L3 L2 L1 m G) (hM : MdbLinks th m G) : VsSlotsW th P L4 L3 L2 L1 m := by
  intro y hy
  by_cases hn : capV m y = .Null
  · rw [hn]; trivial
  · exact (h y ((hM.members y).2 ⟨hy, _, capAt_capV m y, hn⟩)).toW

/-- The context of the VSpace finalisations: the placement, `FinX` and the
cap invariant. -/
structure VsFinCtx (st : machine.Store S) [L : LawfulStore st] {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) : Prop where
  pl : Placed th
  pp : PtPlaced L4 L3 L2 L1
  ps : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b
  pv : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b
  po : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b
  vo : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b
  sd : VsSlotsDisj th P (L.ksb s)
  vp : VsPlaced P (L.ksb s)
  x : FinX st th P L4 L3 L2 L1 SR s a σ
  /-- The slots' VSpace caps placed (`JAtZ.vsc`, VsCapWBase's weakened form:
  a mapped table cap's table need not be in its set). -/
  vc : VsSlotsW th P L4 L3 L2 L1 (L.mem s)

section Ops
variable {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
  {SR : S → A → Fl4Spec.State Unit → Prop}

/-- An unmap's outcome (writes in the page-table words): the post. -/
theorem fin_unmap_after {s s1 : S} {a a1 : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {sl : Fl4Spec.CslotPtr}
    {c : capability.Cap} {b : Bool} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G) (hc : capAt (L.mem s) (cslotAddr sl) = ok c)
    (hF : FinSR st SR (PtWAll L4 L3 L2 L1) s σ s1 a1 σ') (hSt1 : StateRel th (L.mem s1) σ')
    (hR1 : VsRel P (L.mem s1) (L.ksb s1) σ') (hPt1 : PtRel L4 L3 L2 L1 (L.mem s1) σ')
    (hrem : finRem c b = .Null)
    (hspec : ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) :
    FinOKX (L := L) th s σ G sl c b (FinX st th P L4 L3 L2 L1 SR) ((.Null, .Null), s1, a1) ∧
      SlotsSame th (L.mem s) (L.mem s1) := by
  obtain ⟨hS1, hW, hK, hcur⟩ := hF
  have hSS := SlotsSame.of_writes hX.pl hW hX.po
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  exact ⟨⟨hrem.symm, trivial, trivial, σ', G, hspec, hD', hcv, hsl, hMS, hS1, hR1, hPt1,
    hX.x.2.2.2.1.of_writes hW hX.vp hX.pv, hX.x.2.2.2.2.of_same hSS hcur⟩, hSS⟩

/-- An ASID deletion's outcome (zero writes to the ASID-table and pool
words): the post. -/
theorem fin_del_after {s s1 : S} {a a1 : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {sl : Fl4Spec.CslotPtr}
    {c : capability.Cap} {b : Bool} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G) (hc : capAt (L.mem s) (cslotAddr sl) = ok c)
    (hF : FinSRP st L4 L3 L2 L1 SR (VsWrite P (L.ksb s)) s σ s1 a1 σ') (hSt1 : StateRel th (L.mem s1) σ')
    (hR1 : VsRel P (L.mem s1) (L.ksb s1) σ') (hC1 : CurOK st th s1 σ') (hZ : VsZeroW st P s s1)
    (hrem : finRem c b = .Null)
    (hspec : ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) :
    FinOKX (L := L) th s σ G sl c b (FinX st th P L4 L3 L2 L1 SR) ((.Null, .Null), s1, a1) ∧
      SlotsSame th (L.mem s) (L.mem s1) := by
  obtain ⟨⟨hS1, hW, hK, -⟩, hPt1⟩ := hF
  have hSS := SlotsSame.of_writes hX.pl hW hX.vo
  obtain ⟨hD', hcv, hsl, hMS⟩ := fin_after hDS hA hc hSS hSt1 hK
  exact ⟨⟨hrem.symm, trivial, trivial, σ', G, hspec, hD', hcv, hsl, hMS, hS1, hR1, hPt1,
    hX.x.2.2.2.1.of_zero hZ hX.vp, hC1⟩, hSS⟩

set_option maxHeartbeats 1000000 in
/-- **A final page-table cap**: `unmap_page_table` if mapped (l4v
`unmap_page_table`); no cap slot written. -/
theorem fin_page_table (hH : VsPtInnerHyps st A ar L2 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.PageTable p mp asid va)) :
    objects.finalise_cap st ar s a (.PageTable p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.PageTable p mp asid va) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  obtain ⟨-, -, hm, hmu⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none hDS hc hX.x rfl (Set.mem_singleton _))
  obtain ⟨h0, hal⟩ := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_page_table_rel (hH.fin (W := PtWAll L4 L3 L2 L1) (s0 := s) (σ0 := σ) (fun _ h => h)) s a σ hX.pl hX.pp hX.ps
    hX.vp (fun b ⟨q, hq, i, hi, e⟩ => hX.pv b ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, e⟩) hX.x.2.2.2.1
    ⟨FinSR.init hX.x.1, hDS.1.1, hDS.1.2.1, hX.x.2.1, hX.x.2.2.1⟩ asid va p h0 hal (hmu rfl)) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨hF, hSt1, -, hR1, hPt1⟩, -⟩
  exact (WP.spec_ok _).2 (fin_unmap_after hDS hA hX hc hF hSt1 hR1 hPt1 rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A final page-directory cap**: `unmap_page_directory` if mapped (l4v
`unmap_pd`); no cap slot written. -/
theorem fin_page_directory (hH : VsPdInnerHyps st A ar L3 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.PageDirectory p mp asid va)) :
    objects.finalise_cap st ar s a (.PageDirectory p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.PageDirectory p mp asid va) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  obtain ⟨-, -, hm, hmu⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none hDS hc hX.x rfl (Set.mem_singleton _))
  have h0 := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_page_directory_rel (hH.fin (W := PtWAll L4 L3 L2 L1) (s0 := s) (σ0 := σ) (fun _ h => h)) s a σ hX.pl hX.pp hX.ps
    hX.vp (fun b ⟨q, hq, i, hi, e⟩ => hX.pv b ⟨q, Or.inr (Or.inl hq), i, hi, e⟩) hX.x.2.2.2.1
    ⟨FinSR.init hX.x.1, hDS.1.1, hDS.1.2.1, hX.x.2.1, hX.x.2.2.1⟩ asid va p h0 (hmu rfl)) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨hF, hSt1, -, hR1, hPt1⟩, -⟩
  exact (WP.spec_ok _).2 (fin_unmap_after hDS hA hX hc hF hSt1 hR1 hPt1 rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A final PDPT cap**: `unmap_pdpt` if mapped (l4v `unmap_pdpt`); no cap
slot written. -/
theorem fin_pdpt (hH : VsPdptInnerHyps st A ar L4 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p asid va : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pdpt p mp asid va)) :
    objects.finalise_cap st ar s a (.Pdpt p mp asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Pdpt p mp asid va) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  obtain ⟨-, -, hm, hmu⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none hDS hc hX.x rfl (Set.mem_singleton _))
  have h0 := hm rfl
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (unmap_pdpt_rel (hH.fin (W := PtWAll L4 L3 L2 L1) (s0 := s) (σ0 := σ) (fun _ h => h)) s a σ hX.pl hX.pp hX.ps
    hX.vp (fun b ⟨q, hq, i, hi, e⟩ => hX.pv b ⟨q, Or.inl hq, i, hi, e⟩) hX.x.2.2.2.1
    ⟨FinSR.init hX.x.1, hDS.1.1, hDS.1.2.1, hX.x.2.1, hX.x.2.2.1⟩ asid va p h0 (hmu rfl)) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨hF, hSt1, -, hR1, hPt1⟩, -⟩
  exact (WP.spec_ok _).2 (fin_unmap_after hDS hA hX hc hF hSt1 hR1 hPt1 rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A mapped frame cap** (final or not): `unmap_page` (l4v `unmap_page`); no
cap slot written. -/
theorem fin_frame [Fl4Proofs.P1.PlainStore st] (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p : U64) (sz : capability.FrameSize) (rt : U64) (d : Bool) (asid va : U64) (b : Bool)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz rt d true false asid va)) :
    objects.finalise_cap st ar s a (.Frame p sz rt d true false asid va) b false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Frame p sz rt d true false asid va) b (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  have h0 : asid ≠ 0#u64 := by simpa using hok.1
  have hvU : UserV va := by simpa using hok.2.2
  simp only [objects.finalise_cap, objects.finalise_cap_object, plain_retire, bind_ok, ↓reduceIte,
    bne_iff_ne, ne_eq, h0, not_false_eq_true, not_true_eq_false, Bool.false_eq_true, ite_self]
  refine WP.spec_bind (unmap_page_rel (hH.fin (W := PtWAll L4 L3 L2 L1) (s0 := s) (σ0 := σ) (fun _ h => h)) s a σ hX.pl hX.pp hX.ps hX.vp
    hX.pv hX.x.2.2.2.1 ⟨FinSR.init hX.x.1, hDS.1.1, hDS.1.2.1, hX.x.2.1, hX.x.2.2.1⟩ sz asid va p h0 hvU) ?_
  rintro ⟨s1, a1⟩ ⟨-, -, σ', hm, ⟨hF, hSt1, -, hR1, hPt1⟩, -⟩
  exact (WP.spec_ok _).2 (fin_unmap_after hDS hA hX hc hF hSt1 hR1 hPt1 rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A final PML4 cap**: `delete_asid` if mapped (l4v `delete_asid`); no
cap slot written. -/
theorem fin_pml4 (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p asid : U64) (mp : Bool) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid)) :
    objects.finalise_cap st ar s a (.Pml4 p mp asid) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Pml4 p mp asid) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  obtain ⟨-, hp0, -⟩ := hok
  cases mp
  · simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (fin_none hDS hc hX.x rfl (Set.mem_singleton _))
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (delete_asid_rel (hH.fin (W := VsWrite P (L.ksb s)) (s0 := s) (σ0 := σ) hX.pp (fun _ h => h) hX.pv) s a σ hX.vp hX.x.2.1
    ⟨⟨FinSR.init hX.x.1, hX.x.2.2.1⟩, hDS.1.1, hX.pl, hX.sd, hX.x.2.2.2.2⟩ asid p hp0) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ', hm, hR1, ⟨hF, hSt1, -, -, hC1⟩, hZ⟩
  exact (WP.spec_ok _).2 (fin_del_after hDS hA hX hc hF hSt1 hR1 hC1 hZ rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A final ASID pool cap**: `delete_asid_pool` (l4v `delete_asid_pool`);
no cap slot written. -/
theorem fin_asid_pool (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p base : U64) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.AsidPool p base)) :
    objects.finalise_cap st ar s a (.AsidPool p base) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.AsidPool p base) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hok := hX.vc.at hA.isSlot hc
  simp only [VCapW, VCapOK] at hok
  obtain ⟨⟨-, hp0⟩, hb, -⟩ := hok
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, ↓reduceIte]
  refine WP.spec_bind (delete_asid_pool_rel (hH.fin (W := VsWrite P (L.ksb s)) (s0 := s) (σ0 := σ) hX.pp (fun _ h => h) hX.pv) s a σ hX.vp
    hX.x.2.1 ⟨⟨FinSR.init hX.x.1, hX.x.2.2.1⟩, hDS.1.1, hX.pl, hX.sd, hX.x.2.2.2.2⟩ base p hb hp0) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ', hm, hR1, ⟨hF, hSt1, -, -, hC1⟩, hZ⟩
  exact (WP.spec_ok _).2 (fin_del_after hDS hA hX hc hF hSt1 hR1 hC1 hZ rfl (mem_bind_nd hm (Set.mem_singleton _)))

set_option maxHeartbeats 1000000 in
/-- **A final mapped EPT root cap**: `delete_asid` of the root (FL4's
`ept::finalise`; the spec's `arch_finalise_cap` of a mapped level-0
`EPTCap`, whose pool entry is the root tagged guest, cleared by
`deleteAsid`'s nested branch); no cap slot written. -/
theorem fin_ept_root (hH : VsHyps st A ar P th SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (p asid va : U64) (hp0 : p ≠ 0#u64) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p 0#u64 true asid va)) :
    objects.finalise_cap st ar s a (.Ept p 0#u64 true asid va) true false ⦃ r =>
      FinOKX (L := L) th s σ G sl (.Ept p 0#u64 true asid va) true (FinX st th P L4 L3 L2 L1 SR) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  simp only [objects.finalise_cap, objects.finalise_cap_object, ept.finalise, bind_ok, ↓reduceIte]
  refine WP.spec_bind (delete_asid_rel (hH.fin (W := VsWrite P (L.ksb s)) (s0 := s) (σ0 := σ) hX.pp (fun _ h => h) hX.pv) s a σ hX.vp hX.x.2.1
    ⟨⟨FinSR.init hX.x.1, hX.x.2.2.1⟩, hDS.1.1, hX.pl, hX.sd, hX.x.2.2.2.2⟩ asid p hp0) ?_
  rintro ⟨s1, a1⟩ ⟨-, σ', hm, hR1, ⟨hF, hSt1, -, -, hC1⟩, hZ⟩
  have hw : Fl4Spec.NonDet.when ((0#u64 : U64).val = 0) (Fl4Spec.deleteAsid (Z := Unit) asid.bv p.bv) =
      Fl4Spec.deleteAsid (Z := Unit) asid.bv p.bv := by
    have h0 : (0#u64 : U64).val = 0 := rfl
    unfold Fl4Spec.NonDet.when; rw [if_pos h0]
  exact (WP.spec_ok _).2 (fin_del_after hDS hA hX hc hF hSt1 hR1 hC1 hZ rfl
    (mem_bind_nd (show ((), σ') ∈ (Fl4Spec.NonDet.when ((0#u64 : U64).val = 0)
      (Fl4Spec.deleteAsid (Z := Unit) asid.bv p.bv) σ).1 by rw [hw]; exact hm) (Set.mem_singleton _)))

/-! ## All VSpace finalisations -/

/-- The VSpace caps whose finalisation may work (a mapped EPT root cap's
releases its ASID, `fin_ept_root`). -/
def IsVsFin : capability.Cap → Prop
  | .Frame _ _ _ _ _ ep _ _ => ep = false
  | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .AsidPool .. => True
  | .Ept p lv m _ _ => lv = 0#u64 ∧ m = true ∧ p ≠ 0#u64
  | _ => False

/-- The hypotheses of the VSpace finalisations. -/
structure VsFinHyps (st : machine.Store S) [L : LawfulStore st] (A : Type) (ar : machine.Arch A) (th : TypedHeap)
    (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  pt : VsPtInnerHyps st A ar L2 SR
  pd : VsPdInnerHyps st A ar L3 SR
  pdpt : VsPdptInnerHyps st A ar L4 SR
  pg : VsUnmapPageHyps st A ar L3 L2 L1 SR
  del : VsHyps st A ar P th SR

/-- **The VSpace half of `FinWorkHyp`**: a final table, PML4, ASID pool or
mapped EPT root cap, or a mapped frame cap; no cap slot written (`SlotsSame`); `FinX`
kept. -/
theorem vs_fin [Fl4Proofs.P1.PlainStore st] (hH : VsFinHyps st A ar th P L4 L3 L2 L1 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hX : VsFinCtx st th P L4 L3 L2 L1 SR s a σ G)
    (c : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hv : IsVsFin c) (b : Bool)
    (hw : FinWork c b) :
    objects.finalise_cap st ar s a c b false ⦃ r =>
      FinOKX (L := L) th s σ G sl c b (FinX st th P L4 L3 L2 L1 SR) r ∧ SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ := by
  have hb : isFrame c = false → b = true := by
    rintro hf; rcases hw with ⟨h, -⟩ | ⟨p, sz, r, d, ep, asid, va, rfl⟩
    · rcases h with h | ⟨f, l, owner, rfl, -⟩
      · exact h
      · simp [IsVsFin] at hv
    · simp [isFrame] at hf
  cases c <;> simp only [IsVsFin] at hv
  case Frame p sz rt d m ept asid va =>
    subst ept
    rcases hw with ⟨-, hf, -⟩ | ⟨p', sz', r', d', ep', asid', va', e⟩
    · simp [isFrame] at hf
    · cases e
      exact fin_frame hH.pg s a σ G sl hDS hA hX p sz rt d asid va b hc
  case PageTable p mp asid va => rw [hb rfl]; exact fin_page_table hH.pt s a σ G sl hDS hA hX p asid va mp hc
  case PageDirectory p mp asid va =>
    rw [hb rfl]; exact fin_page_directory hH.pd s a σ G sl hDS hA hX p asid va mp hc
  case Pdpt p mp asid va => rw [hb rfl]; exact fin_pdpt hH.pdpt s a σ G sl hDS hA hX p asid va mp hc
  case Pml4 p mp asid => rw [hb rfl]; exact fin_pml4 hH.del s a σ G sl hDS hA hX p asid mp hc
  case AsidPool p base => rw [hb rfl]; exact fin_asid_pool hH.del s a σ G sl hDS hA hX p base hc
  case Ept p lv m asid va =>
    obtain ⟨rfl, rfl, hp0⟩ := hv
    rw [hb rfl]; exact fin_ept_root hH.del s a σ G sl hDS hA hX p asid va hp0 hc

end Ops

/-- `FinOKX` gives `FinObjHyp`'s post. -/
theorem FinOKX.base {A : Type} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {b : Bool} {X : S → A → Fl4Spec.State Unit → Prop}
    {r : (capability.Cap × capability.Cap) × S × A} (h : FinOKX (L := L) th s σ G sl c b X r) :
    r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' := by
  obtain ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8, -⟩ := h
  exact ⟨h1, h2, h3, σ', G', h4, h5, h6, h7, h8⟩

/-! ## At the composite relation -/

section Top
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}

/-- `VsHyps` for the composite relation. -/
theorem vsHyps_top (hA : ArchRefines arI AR) : VsHyps st A arI P th (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  stable := fun s s' a σ σ' hS hw hc => vsStable_top s s' a σ σ' hS hw hc
  invalOK := fun asid vs σ => invalOK_top asid vs σ
  inval := fun s a σ asid vs _ hS => inval_top hA s a σ asid vs hS
  invEpt := fun s a σ root mask hS => invEpt_top hA s a σ root mask hS
  curT := fun s a σ hS => curT_top s a σ hS
  root := vsRootHyps_top hA

/-- `VsFinHyps` for the composite relation. -/
theorem vsFinHyps_top (hA : ArchRefines arI AR) :
    VsFinHyps st A arI th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) where
  pt := vsPtInnerHyps_top hA
  pd := vsPdInnerHyps_top hA
  pdpt := vsPdptInnerHyps_top hA
  pg := vsUnmapPageHyps_top hA
  del := vsHyps_top hA

/-- **The VSpace half of `FinWorkHyp` at `TopSR`**: the placement from
`TopPlaced`; `FinX` (`TopSR`, `VsRel`, `PtRel`, `PoolsIn`, `CurOK`) kept; no
cap slot written. -/
theorem vs_fin_top [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (sl : Fl4Spec.CslotPtr) (hDS : DState (L := L) th s σ G) (hAs : AbsSlot th sl)
    (hX : FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s a σ)
    (hVC : VsSlotsW th P L4 L3 L2 L1 (L.mem s))
    (cp : capability.Cap) (hc : capAt (L.mem s) (cslotAddr sl) = ok cp) (hv : IsVsFin cp) (b : Bool)
    (hw : FinWork cp b) :
    objects.finalise_cap st arI s a cp b false ⦃ r =>
      FinOKX (L := L) th s σ G sl cp b (FinX st th P L4 L3 L2 L1 (TopSR st th P L4 L3 L2 L1 N T C E R B c AR)) r ∧
        SlotsSame th (L.mem s) (L.mem r.2.1) ⦄ :=
  vs_fin (vsFinHyps_top hA) s a σ G sl hDS hAs
    ⟨hX.1.2.pl, hX.1.2.pt, hX.1.2.ps, hX.1.2.pv, hX.1.2.po, hX.1.2.vo, hX.1.2.sd, hX.1.2.vs, hX, hVC⟩ cp hc hv b hw

end Top

end

end

end Fl4Proofs.P3.Vs
