/-
P3 (DESIGN.md §9), VSpace: **`JAtZ` across a final native VSpace cap's
finalisation** (a page table, page directory, PDPT, PML4 or ASID pool cap;
toward `JDelParts`' `jFinAt_vs`, as XTopJointFinEp for endpoints).

* FL4's side: VsFin's `vs_fin` at `FootSR TopSR s VsW` (the hypothesis
  structures carried to the narrow footprint `VsW`: the page-table words
  and the ASID-table and pool words, `VsFinHyps.footN`), `XTopAt` after at
  the same sets and ghost (as XTopFinVs's `xFinRest_of`; the ghost kept by
  `SlotsSame`, as IpcSlotsSame's `irel_same`).
* The spec's side: XTopJointFinVsSpec's `ArFr` (only arch objects, of the
  same arch type, the ASID table, the CR3 and the machine state change).
* `VsApart` (`JVsApartHyp`, proved by `jVsApartHyp`: `JAtZ.hscC` puts
  every SC of `H` in `Z.C`): the ASID table lies apart from `H`'s SCs
  outside `Z.C` (l4v `pspace_distinct` of the kernel's global data against
  the objects; FL4's ASID table, `[ksb+288000, +16384)`, follows the 64 cores'
  nodes and is not in `JKern.hks`' `[ksb, ksb+13568)`). The untyped caps' free
  parts need no placement against the table: a table word there is zero
  (`UtCapP3.zero`), so its entry is empty, and the spec's arch finalisation
  only clears entries (`tn_archFinaliseCap`), so it stays zero (`vs_utc`).
  `H`'s other objects are derived apart (`JAtZ.vobj_apart`: the endpoints,
  notifications, replies and `Z.C`'s SCs by `TopPlaced.disj`; the TCBs by
  `TopPlaced.po`/`vo`; every SC from the VSpace frames by `JAtZ.vsFr_sc`,
  the cores' nodes by `JAtZ.vsFr_node`: a frame is a spec arch object, so
  an `other` object of `H`, `SpecCover.arch`, `HeapOK.disj`, `JKern.hnd`).
* `JAtZ.finVsJ`: `JAtZ` after at the same sets: every `H` object word, node
  word and kernel-state word but the VSpace ones kept (`VsW`, `objW`,
  `nodeW`), so the call stacks, yield, MCP, buffer words, `JPlaced`, the
  dead set, `JKern`, the untyped caps' facts (a table or pool word is in a
  spec object, `SpecFree`) and P1's `BlkOK` (`blk_of_untracked`); the
  scheduler's invariants by `ArFr`.
* `JAtZ.vs_ready`: the slot of a VSpace cap is ready: no object of `H` but
  the `other` ones starts in its frame.
-/
import Fl4Proofs.P3.XTopJointFinVsSpec
import Fl4Proofs.P3.XTopJointFinW
import Fl4Proofs.P3.XTopJointFin
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

/-! ## The hypotheses carried to the narrow footprint -/

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s0 : S} {W : U64 → Prop}

theorem ptWA {b : U64} (h : PtW L1 b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, e⟩
theorem pdWA {b : U64} (h : PdW L2 b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, e⟩
theorem pdptWA {b : U64} (h : PdptW L3 b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact ⟨p, Or.inr (Or.inl hp), i, hi, e⟩
theorem pml4WA {b : U64} (h : Pml4W L4 b) : PtWAll L4 L3 L2 L1 b := by
  obtain ⟨p, hp, i, hi, e⟩ := h; exact ⟨p, Or.inl hp, i, hi, e⟩

variable {A : Type} {ar : machine.Arch A} {SR : S → A → Fl4Spec.State Unit → Prop}
  (hsub : ∀ b, PtWAll L4 L3 L2 L1 b → W b)
include hsub

theorem VsUnmapPageHyps.footN (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR) :
    VsUnmapPageHyps st A ar L3 L2 L1 (FootSR st SR s0 W) where
  ptStable := foot_stab (fun b h => hsub b (ptWA h)) hH.ptStable
  pdStable := foot_stab (fun b h => hsub b (pdWA h)) hH.pdStable
  pdptStable := foot_stab (fun b h => hsub b (pdptWA h)) hH.pdptStable
  flushPgOK := hH.flushPgOK
  flushPg := fun s a σ asid va h =>
    WP.spec_mono (hH.flushPg s a σ asid va h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPtInnerHyps.footN (hH : VsPtInnerHyps st A ar L2 SR) : VsPtInnerHyps st A ar L2 (FootSR st SR s0 W) where
  pdStable := foot_stab (fun b h => hsub b (pdWA h)) hH.pdStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushTblOK := hH.flushTblOK
  flushTbl := fun s a σ vs v pt asid h hv hpt =>
    WP.spec_mono (hH.flushTbl s a σ vs v pt asid h.1 hv hpt) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdInnerHyps.footN (hH : VsPdInnerHyps st A ar L3 SR) : VsPdInnerHyps st A ar L3 (FootSR st SR s0 W) where
  pdptStable := foot_stab (fun b h => hsub b (pdptWA h)) hH.pdptStable
  flushOK := hH.flushOK
  flushPS := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushPS s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAllH s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

theorem VsPdptInnerHyps.footN (hH : VsPdptInnerHyps st A ar L4 SR) :
    VsPdptInnerHyps st A ar L4 (FootSR st SR s0 W) where
  flushPSKeep := fun s a σ asid h => WP.spec_mono (hH.flushPSKeep s a σ asid h.1) fun _ hS => ⟨hS, h.2⟩
  pml4Stable := foot_stab (fun b h => hsub b (pml4WA h)) hH.pml4Stable
  flushAllOK := hH.flushAllOK
  flushAllH := fun s a σ vs asid h =>
    WP.spec_mono (hH.flushAllH s a σ vs asid h.1) fun _ ⟨σ', h1, h2⟩ => ⟨σ', h1, h2, h.2⟩

/-- **`VsFinHyps` at the narrow footprint**: the page-table words and the
ASID-table and pool words (no slot, TCB-state or scheduler-action word: the
finalisations restart no thread). -/
theorem VsFinHyps.footN (hsubV : ∀ b, VsWrite P (L.ksb s0) b → W b) (hH : VsFinHyps st A ar th P L4 L3 L2 L1 SR) :
    VsFinHyps st A ar th P L4 L3 L2 L1 (FootSR st SR s0 W) where
  pt := hH.pt.footN hsub
  pd := hH.pd.footN hsub
  pdpt := hH.pdpt.footN hsub
  pg := hH.pg.footN hsub
  del := hH.del.foot hsubV

end

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The VSpace frames of the sets: the ASID pools and the tables. -/
def VsFr (Z : XSets) (q : U64) : Prop := q ∈ Z.P ∨ q ∈ Z.L4 ∨ q ∈ Z.L3 ∨ q ∈ Z.L2 ∨ q ∈ Z.L1

/-- The words a VSpace finalisation writes: the page-table words, the
ASID-table and pool words. -/
def VsW (Z : XSets) (kb b : U64) : Prop := PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b ∨ VsWrite Z.P kb b

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The VSpace frames apart** (module docstring). -/
structure VsApart (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) : Prop where
  /-- The ASID table overlaps no SC of `H` outside `Z.C` (the other objects
  of `H` but the `other` ones: `TopPlaced.disj`, `JAtZ.vobj_apart`, and the
  TCBs outside the VSpace words, `TopPlaced.po`; the VSpace frames apart
  from every SC of `H`: `JAtZ.vsFr_sc`). -/
  scOut : ∀ p z, H p = some (.sc z) → p ∉ Z.C →
    (L.ksb s).val + 288000 + 16384 ≤ p.val ∨ p.val + 2 ^ z ≤ (L.ksb s).val + 288000

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The VSpace frames apart at `J`** (`VsApart` at every `JAtZ` state;
proved by `jVsApartHyp`). -/
def JVsApartHyp (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit), Z.th = th → JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VsApart (L := L) Z H Cs s

/-- **`JVsApartHyp` holds** (no longer a premise): `JAtZ.hscC` puts every SC
of `H` in `Z.C`, so `scOut` is vacuous (`JAtZ.scOut`). -/
theorem jVsApartHyp {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} : JVsApartHyp (L := L) arI AR th :=
  fun _ _ _ _ _ _ _ _ _ _ J => ⟨J.scOut⟩


end

/-! ## The VSpace words -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {Z : XSets}

/-- **A VSpace word by value**: in a frame of the sets, or in the ASID table. -/
theorem vsW_val {kb b : U64} (hPP : PtPlaced Z.L4 Z.L3 Z.L2 Z.L1) (hVP : VsPlaced Z.P kb) (h : VsW Z kb b) :
    (∃ q, VsFr Z q ∧ q.val % 4096 = 0 ∧ q.val + 4096 ≤ 2 ^ 64 ∧ q.val ≤ b.val ∧ b.val + 8 ≤ q.val + 4096 ∧
      b.val % 8 = 0) ∨
    (kb.val + 288000 ≤ b.val ∧ b.val + 8 ≤ kb.val + 288000 + 16384 ∧ b.val % 8 = 0) := by
  rcases h with ⟨q, hq, i, hi, rfl⟩ | ⟨⟨hi, hh, rfl⟩ | ⟨q, hq, lo, hl, rfl⟩⟩
  · have ha := hPP q hq
    have hf := tbl_fit ha
    have hv := peA_val hf hi
    exact Or.inl ⟨q, Or.inr hq, ha, hf, by omega, by omega, by omega⟩
  · have hv := atA_val hVP.ksb_fit hh
    have := hVP.ksb_al
    exact Or.inr ⟨by omega, by omega, by omega⟩
  · obtain ⟨ha, hf⟩ := hVP.pal q hq
    have hv := peA_val hf hl
    exact Or.inl ⟨q, Or.inl hq, ha, hf, by omega, by omega, by omega⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

theorem vsFr_al {kb q : U64}
    (hPP : PtPlaced Z.L4 Z.L3 Z.L2 Z.L1) (hVP : VsPlaced Z.P kb) (hq : VsFr Z q) :
    q.val % 4096 = 0 ∧ q.val + 4096 ≤ 2 ^ 64 := by
  rcases hq with hq | hq
  · exact hVP.pal q hq
  · exact ⟨hPP q hq, tbl_fit (hPP q hq)⟩

/-- **A VSpace frame is an `other` object of `H` of at least a page**: a
spec arch object (`VsRel.pool`, `PtRel`), so `H`'s (`SpecCover.arch`). -/
theorem JAtZ.vsFr_other {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {q : U64} (hq : VsFr Z q) : ∃ n, 12 ≤ n ∧ H q = some (.other n) := by
  have hF := J.xtop.fin
  have hk : ∃ ao, σ.kheap q.bv = some (.archObj ao) := by
    rcases hq with hq | hq | hq | hq | hq
    · obtain ⟨f, hf, -⟩ := hF.2.1.pool q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q hq; exact ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q hq; exact ⟨_, hf⟩
  obtain ⟨ao, hao⟩ := hk
  obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hao
  exact ⟨n, hn, hH⟩

/-- **A VSpace frame lies apart from every SC of `H`** (`JAtZ.vsFr_other`,
`HeapOK.disj`). -/
theorem JAtZ.vsFr_sc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {q : U64} (hq : VsFr Z q) {p : U64} {z : Nat} (hp : H p = some (.sc z)) :
    q.val + 4096 ≤ p.val ∨ p.val + 2 ^ z ≤ q.val := by
  obtain ⟨n, hn, hH⟩ := J.vsFr_other hq
  have hne : p ≠ q := fun e => by subst e; rw [hp] at hH; cases hH
  have h4 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rcases J.kern.heap.disj p _ q _ hp hH hne with h | h
  · simp only [P1.HKind.bits] at h
    exact Or.inr h
  · simp only [P1.HKind.bits] at h
    exact Or.inl (by omega)

/-- **A VSpace frame overlaps no core's node** (`JAtZ.vsFr_other`,
`JKern.hnd`). -/
theorem JAtZ.vsFr_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {q : U64} (hq : VsFr Z q) {c : U64} (hc : c ∈ Cs) :
    q.val + 4096 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ q.val := by
  obtain ⟨n, hn, hH⟩ := J.vsFr_other hq
  have h4 : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  rcases J.kern.hnd q _ hH c hc with h | h
  · simp only [P1.HKind.bits] at h
    exact Or.inl (by omega)
  · exact Or.inr h

/-- **An address of the VSpace objects lies in no endpoint, notification,
reply or SC of `Z.C`** (`TopPlaced.disj`: those are the other subsystems'
objects). -/
theorem JAtZ.vobj_apart {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {w : U64} (hv : VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) w) {p : U64} {k : P1.HKind} (hp : H p = some k)
    (hk : k = .ep ∨ k = .ntfn ∨ k = .reply ∨ ∃ z, k = .sc z ∧ p ∈ Z.C) :
    w.val < p.val ∨ p.val + 2 ^ k.bits ≤ w.val := by
  have hP := J.xtop.fin.1.2
  by_contra hn
  have g1 : p.val ≤ w.val := by omega
  have g2 : w.val < p.val + 2 ^ k.bits := by omega
  apply hP.disj w _ hv
  rcases hk with rfl | rfl | rfl | ⟨z, rfl, hpC⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, J.hset.1 p hp, g1, by simpa [P1.HKind.bits] using g2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, J.hset.2.1 p hp, g1,
      by simpa [P1.HKind.bits] using g2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, J.hset.2.2 p hp, g1, by simpa [P1.HKind.bits] using g2⟩))))
  · obtain ⟨Q, R0, -, hs⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨x, n, hkx, -⟩ := hs.scs p hpC
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc p x n (J.c0 p hpC) hkx).2
    rw [hH] at hp
    cases hp
    have hso : Sched.ScObj p n w := by
      unfold Sched.ScObj; exact ⟨g1, by simpa [P1.HKind.bits] using g2⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hpC, x, n, hkx, hso⟩))))))

/-- A VSpace word lies in no object of `H` but the `other` ones. -/
theorem JAtZ.vsObjW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s) {b : U64} (hb : VsW Z (L.ksb s) b) {p : U64} {k : P1.HKind}
    (hp : H p = some k) (hk : ∀ z, k ≠ .other z) : b.val < p.val ∨ p.val + 2 ^ k.bits ≤ b.val := by
  have hP := J.xtop.fin.1.2
  have hv : VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b := by
    rcases hb with ⟨q, hq, i, hi, rfl⟩ | h
    · exact table_vobj hP.pt hq hi _
    · exact vsWrite_vobj hP.vs h
  cases k with
  | tcb =>
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hO : OutsideObjects Z.th b := by
      rcases hb with h | h
      · exact hP.po b h
      · exact hP.vo b h
    have := hO.2 p .tcb ((hJ.tcb p).2 hp)
    simp only [objSize] at this
    simp only [P1.HKind.bits]
    omega
  | ep => exact J.vobj_apart hv hp (Or.inl rfl)
  | ntfn => exact J.vobj_apart hv hp (Or.inr (Or.inl rfl))
  | reply => exact J.vobj_apart hv hp (Or.inr (Or.inr (Or.inl rfl)))
  | sc z =>
    by_cases hpC : p ∈ Z.C
    · exact J.vobj_apart hv hp (Or.inr (Or.inr (Or.inr ⟨z, rfl, hpC⟩)))
    · have e2 := Ap.scOut p z hp hpC
      simp only [P1.HKind.bits]
      rcases vsW_val hP.pt hP.vs hb with ⟨q, hq, -, -, h1, h2, -⟩ | ⟨h1, h2, -⟩
      · rcases J.vsFr_sc hq hp with e | e <;> omega
      · rcases e2 with e | e <;> omega
  | other z => exact absurd rfl (hk z)

/-- A VSpace word lies in no core's node. -/
theorem JAtZ.vsNodeW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : VsW Z (L.ksb s) b) {c : U64} (hc : c ∈ Cs) :
    b.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ b.val := by
  have hS := J.xtop.fin.1
  rcases vsW_val hS.2.pt hS.2.vs hb with ⟨q, hq, -, -, h1, h2, -⟩ | ⟨h1, h2, -⟩
  · rcases J.vsFr_node hq hc with e | e <;> omega
  · have h64 := J.kern.csLt c hc
    have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    have : c.val * 4288 + 4288 ≤ 64 * 4288 := by omega
    right; omega

/-- A VSpace word misses the IRQ node: it lies outside the typed heap's
objects (`TopPlaced.po`/`.vo`), and the IRQ node's CTEs are objects of it
(`IntLayout.node`). -/
theorem JAtZ.vsKsW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : VsW Z (L.ksb s) b) : b.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ b.val := by
  have hP := J.xtop.fin.1.2
  have ho : OutsideObjects Z.th b := by
    rcases hb with h | h
    · exact hP.po b h
    · exact hP.vo b h
  exact J.intL.out_node ho.2

theorem JAtZ.vsW_al {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : VsW Z (L.ksb s) b) : P1.Aligned b := by
  have hS := J.xtop.fin.1
  unfold P1.Aligned
  rcases vsW_val hS.2.pt hS.2.vs hb with ⟨q, -, -, -, -, -, h⟩ | ⟨-, -, h⟩ <;> exact h

/-- **The untyped caps' facts after a VSpace finalisation**: the free parts
zero (a table or pool word lies in a spec object, `SpecFree`; an ASID-table
word in a free part is zero, so its entry is empty and stays empty, `hTN`,
and the word stays zero, `VsRel.table` after), the rest as `finW_utc`. -/
theorem JAtZ.vs_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (VsW Z (L.ksb s)))
    (hVR1 : VsRel Z.P (L.mem s') (L.ksb s) σ')
    (hTN : ∀ i, σ.archState.x64AsidTable i = none → σ'.archState.x64AsidTable i = none)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  have hfi := U.fiLe
  have hVR := J.xtop.fin.2.1
  have hPt := J.xtop.fin.2.2.1
  -- a spec object of `2 ^ 12` bytes at a frame
  have spec4k : ∀ (q : U64) (ko : Fl4Spec.KernelObject), σ.kheap q.bv = some ko → Fl4Spec.objBits ko = 12 →
      ∀ w : U64, q.val ≤ w.val → w.val < q.val + 4096 → w.val < p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val := by
    intro q ko hk hb w h1 h2
    have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) q.bv ko hk
    simp only [hb, UScalar.bv_toNat] at this
    omega
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [hgp]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    by_cases hb : VsW Z (L.ksb s) w
    swap
    · rw [hw.mem_eq hal hb]; exact U.zero (B g) w hal h1 h2
    rcases hb with ⟨q, hq, i, hi, rfl⟩ | ⟨⟨hi, hh, rfl⟩ | ⟨q, hq, lo, hl, rfl⟩⟩
    · exfalso
      have hf := tbl_fit (J.xtop.fin.1.2.pt q hq)
      have hv := peA_val hf hi
      have key : ∃ ko, σ.kheap q.bv = some ko ∧ Fl4Spec.objBits ko = 12 := by
        rcases hq with hq | hq | hq | hq
        · obtain ⟨f, hk, -⟩ := hPt.l4 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l3 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l2 q hq; exact ⟨_, hk, rfl⟩
        · obtain ⟨f, hk, -⟩ := hPt.l1 q hq; exact ⟨_, hk, rfl⟩
      obtain ⟨ko, hk, hb⟩ := key
      rcases spec4k q ko hk hb (peA q i) (by omega) (by omega) with e | e <;> omega
    · have h0 : L.mem s (atA (L.ksb s) hi) = 0#u64 := U.zero (B g) _ hal h1 h2
      have t0 := hVR.table hi hh
      rw [h0] at t0
      have t0' : σ.archState.x64AsidTable (Fl4Spec.ucast 11 hi.bv) = none := by rw [t0]; simp [optRef]
      have t1 := hVR1.table hi hh
      rw [hTN _ t0'] at t1
      by_contra hne
      simp [optRef, hne] at t1
    · exfalso
      obtain ⟨-, hf⟩ := J.xtop.fin.1.2.vs.pal q hq
      have hv := peA_val hf hl
      obtain ⟨f, hk, -⟩ := hVR.pool q hq
      rcases spec4k q _ hk rfl (peA q lo) (by omega) (by omega) with e | e <;> omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

/-- **`JKern` across an arch step** (`kern_keep` with the global PML4 kept a
PML4 rather than every arch object kept). -/
theorem JAtZ.kern_keepA {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ') (F : ArFr σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    JKern (L := L) H Cs D Z.th s' σ' := by
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, F.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, F.csc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  refine ⟨fun sl h => K.orig sl (by rw [← F.orig]; exact h), by rw [ecw, F.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    by rw [F.gpml4]; exact F.hasPm K.gpm, by rw [F.gpml4]; exact K.ga, by rw [F.gpml4]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0⟩
  rw [hna, hDbg]; exact K.head

set_option maxHeartbeats 16000000 in
/-- **`JAtZ` across a native VSpace finalisation doing work** (module
docstring; `vs_fin`'s caps: a VSpace-mapped frame, final or not, or a final
table or pool cap): at the same sets, the dead set and P1's sets kept. From
the slots' caps placed (`JAtZ.vsc`), `VsApart` at the state (`jVsApartHyp`)
and `ArchRefines` [P]. -/
theorem JAtZ.finVsJb [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Ap : VsApart (L := L) Z H Cs s)
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) Z.th s σ Z.G) (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hvf : IsVsFin c)
    (hac : ∃ ac, absCap c = .archObjectCap ac) (b : Bool) (hw : FinWork c b) :
    objects.finalise_cap st arI s a c b false ⦃ r =>
      r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧ ∃ σ',
        ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D r.2.1 r.2.2 σ' ∧ SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧
        L.ksb r.2.1 = L.ksb s ⦄ := by
  have hS := J.xtop.fin.1
  have hH : VsFinHyps st A arI Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1
      (FootSR st (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR) s (VsW Z (L.ksb s))) :=
    VsFinHyps.footN (fun _ h => Or.inl h) (fun _ h => Or.inr h) (vsFinHyps_top hA)
  refine WP.spec_mono (vs_fin hH s a σ Z.G sl hDS hAs
    ⟨hS.2.pl, hS.2.pt, hS.2.ps, hS.2.pv, hS.2.po, hS.2.vo, hS.2.sd, hS.2.vs,
      ⟨⟨hS, P1.WritesIn.refl _ _⟩, J.xtop.fin.2⟩, J.vsc⟩ c hc hvf b hw) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨⟨h1, h2, h3, σ1, G1, hm, hDS1, -, -, -, ⟨hS1, hW⟩, hx1⟩, hSS⟩
  simp only at h1 h2 h3 hm hDS1 hS1 hW hx1 hSS ⊢
  obtain ⟨ac, hacE⟩ := hac
  have F : ArFr σ σ1 := by rw [hacE] at hm; exact ArFr.of_fin hm
  have hTN : ∀ i, σ.archState.x64AsidTable i = none → σ1.archState.x64AsidTable i = none := by
    rw [hacE] at hm; exact tn_archFinaliseCap ac b σ _ hm
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  -- `XTopAt` after, at the same sets and ghost
  have hWF : P1.WritesIn st s s1 (VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s) :=
    hW.mono fun b hb => Or.elim hb (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hdom := dom_of_foot hS (Or.inr hWF)
  have hdk := Vs.DK.dom (Vs.dk_finaliseCap _ _) hm
  obtain ⟨hPl, hCR, hFI, hD, hMO, hIA, -⟩ := J.xtop.rel
  obtain ⟨-, -, hM, hC, hMI⟩ := hCR
  have hCR1 : CRel Z.th (L.mem s1) σ1 Z.G :=
    ⟨hDS1.1.1, hDS1.1.2.1, hM.of_same hSS, hC.of_same hSS F.cdt F.orig, MdbInv.of_same hM hMI hSS⟩
  have hFI1 : FinInv Z.th (L.mem s1) σ1 Z.G := hFI.of_same hM hSS F.ksub
  have hX1 : XTopAt (L := L) AR Z s1 a1 σ1 := by
    have hSch := hS1.1.1
    have hEp := hS1.1.2.1
    have hNt := hS1.1.2.2.1
    exact ⟨⟨hS1, hx1⟩, ⟨hPl, hCR1, hFI1, by rw [hkb]; exact hD.frame hdom.2 hdk.1 hdk.2,
      by rw [hkb]; exact MdbOKV.of_same hM hSS hMO, by rw [hkb]; exact hIA, ScApart.of_top hS1.2⟩,
      IpcRel.of hNt hEp (sched_sc hSch), J.xtop.esa.mono hkb F.szKeep⟩
  have hVR1 : VsRel Z.P (L.mem s1) (L.ksb s) σ1 := by have := hX1.fin.2.1; rwa [hkb] at this
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w : U64, P1.Aligned w → p.val ≤ w.val →
      w.val < p.val + 2 ^ k.bits → L.mem s1 w = L.mem s w := fun p k hp hk w hal g1 g2 =>
    hW.mem_eq hal fun hb => by rcases J.vsObjW Ap hb hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w : U64, P1.Aligned w → t.val ≤ w.val → w.val < t.val + 4096 →
      L.mem s1 w = L.mem s w := fun t ht w hal g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w hal g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s1 w = L.mem s w := fun q z hq w hal g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w hal g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s1 (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s1 (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s1 (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s1 a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s1 (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by rcases J.vsNodeW hb J.kern.cs0 with e | e <;> omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => J.vsKsW hb
  -- the dead stay dead
  have hAI : ActIdle σ1 := J.act.ar F
  have yk : YKeep σ σ1 := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_keep hX1.fin.1.1.1 hX1.ipc
      (fun x hx _ => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl, rfl, Or.inl rfl⟩)
      (fun x hx => (F.look (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, F.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, F.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- P1's `BlkOK`
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 := by
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨J.vsW_al hb, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · rcases J.vsObjW Ap hb (p := t) (k := .tcb) ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · rcases J.vsNodeW hb hc with e | e <;> omega
    · rcases he with he | he
      · have hb8 : b.val % 8 = 0 := J.vsW_al hb
        have ha := hHk.align e _ he
        simp only [P1.HKind.bits] at ha
        rcases J.vsObjW Ap hb he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · have hb8 : b.val % 8 = 0 := J.vsW_al hb
        have ha := hHk.align e _ he
        simp only [P1.HKind.bits] at ha
        rcases J.vsObjW Ap hb he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases J.vsObjW Ap hb hp hko with e | e <;> omega
  -- the spec's frames
  have ck : Sched.CKeep σ σ1 := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s1 σ1 :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hkb hirq (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc).2⟩
  have hkern := J.kern_keepA hkb hcpu hX1.fin.1.1.1 F hDbg
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ1 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, J.jcov_keep hkb hSS hdead (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc), hkern,
      J.vs_utc hW hVR1 hTN hSS F.cdt F.orig F.gpml4 hDbg, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F, J.own.ar F,
      J.off.ar F, hAI, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, hblk⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsObjW Ap hb hp (fun z h => by cases h)) (fun c hc => J.vsNodeW hb hc)
  exact ⟨h1, h2, h3, σ1, hm, J.cs_frameK hkb hX1 F.kback F.ipcFr (JCs.same J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy) (fun t ht => tcbK t (J.thT t ht) _ (Sched.tVcpuA_aligned J.ip.e.tcb (J.thT t ht)) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega) (by rw [Sched.tVcpuA_val J.ip.e.tcb (J.thT t ht)]; omega))
    hSS hKd F.idle, hSS, hkb⟩

/-- **`JAtZ` across a final native VSpace cap's finalisation** (`finVsJb`
at a table or pool cap). -/
theorem JAtZ.finVsJ [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Ap : VsApart (L := L) Z H Cs s)
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} (hDS : DState (L := L) Z.th s σ Z.G) (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c)
    (hv : (∃ p m a v, c = .PageTable p m a v) ∨ (∃ p m a v, c = .PageDirectory p m a v) ∨
      (∃ p m a v, c = .Pdpt p m a v) ∨ (∃ p m a, c = .Pml4 p m a) ∨ ∃ p b, c = .AsidPool p b) :
    objects.finalise_cap st arI s a c true false ⦃ r =>
      r.1.1 = finRem c true ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧ ∃ σ',
        ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) true σ).1 ∧
        JAtZ (L := L) arI AR Z H Cs Ac Lst D r.2.1 r.2.2 σ' ∧ SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧
        L.ksb r.2.1 = L.ksb s ⦄ := by
  have hvf : IsVsFin c := by
    rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> trivial
  have hac : ∃ ac, absCap c = .archObjectCap ac := by
    rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      exact ⟨_, rfl⟩
  have hw : FinWork c true := by
    refine Or.inl ⟨Or.inl rfl, ?_, ?_⟩
    · rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
    · intro f l e
      rcases hv with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
        cases e
  exact J.finVsJb hA Ap hDS hAs hc hvf hac true hw


/-- **A VSpace cap's slot is ready** (module docstring): a table cap's range
meets no object of `H` but `other` ones (`JPlaced.cobj`, mapped or not, in
the sets or not); a PML4 or pool cap's frame `p`, a VSpace frame of the sets
(`JAtZ.vsc`), holds none either; so every object in its range is dead, and
the current SC is not in it. -/
theorem JAtZ.vs_ready {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {c : capability.Cap} (hcv : capV (L.mem s) x = c)
    (hv : (∃ p m a v, c = .PageTable p m a v) ∨ (∃ p m a v, c = .PageDirectory p m a v) ∨
      (∃ p m a v, c = .Pdpt p m a v) ∨ (∃ p m a, c = .Pml4 p m a) ∨ ∃ p b, c = .AsidPool p b) {s' : S}
    (hcv' : capV (L.mem s') x = c) : EmptyReady (L := L) H Z.G s' x := by
  have hS := J.xtop.fin.1
  have hxs : IsSlot Z.th x := ((J.mdbL.members x).1 hx).1
  -- a cap whose range misses `H`'s live objects
  have apartR : (∀ q k, H q = some k → (∀ z, k ≠ .other z) → q.val + 2 ^ k.bits ≤ baseF c ∨ topF c < q.val) →
      EmptyReady (L := L) H Z.G s' x := by
    intro hap
    unfold EmptyReady
    rw [hcv']
    intro _ _
    refine fun lo hi hlh h1 h2 => Or.inr fun q hq => ?_
    cases hk : H q with
    | none => exact deadP_none hk
    | some k =>
      by_cases ho : ∃ z, k = .other z
      · obtain ⟨z, rfl⟩ := ho
        exact ⟨fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun z' e => (by rw [hk] at e; cases e)⟩
      · have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
        rcases hap q k hk (fun z e => ho ⟨z, e⟩) with e | e <;> omega
  have hcobj : Sched.CapObjH H (Sched.idleScW (L := L) s) c := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have h := hJ.cobj x hxs
    rw [hcv] at h; exact h
  rcases hv with ⟨p, m, a0, v, rfl⟩ | ⟨p, m, a0, v, rfl⟩ | ⟨p, m, a0, v, rfl⟩ | hv
  · exact apartR hcobj
  · exact apartR hcobj
  · exact apartR hcobj
  have hok : VCapOK Z.P Z.L4 Z.L3 Z.L2 Z.L1 c := by
    have h := J.vsc x hxs
    rw [hcv] at h
    rcases hv with ⟨p, m, a0, rfl⟩ | ⟨p, b, rfl⟩ <;> exact h
  -- the cap's frame and range
  have key : ∃ p : U64, VsFr Z p ∧ baseF c = p.val ∧ topF c ≤ p.val + 4095 := by
    have rng : ∀ p : U64, p.val % 4096 = 0 → ptrF c = p → sizeF c = 12#u64 →
        baseF c = p.val ∧ topF c ≤ p.val + 4095 := fun p ha hp hs => by
      have hf := tbl_fit ha
      have := capRange (c := c) (b := 12#u64) hp hs (by decide) hf
      have e2 : topF c = p.val + 2 ^ 12 - 1 := this.2
      exact ⟨this.1, by omega⟩
    rcases hv with ⟨p, m, a0, rfl⟩ | ⟨p, b, rfl⟩
    · simp only [VCapOK] at hok
      exact ⟨p, Or.inr (Or.inl hok.1), rng p (hS.2.pt p (Or.inl hok.1))
        (ok_inj (ptr_eq _).symm) (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits]))⟩
    · simp only [VCapOK] at hok
      exact ⟨p, Or.inl hok.1.1, rng p (hS.2.vs.pal p hok.1.1).1 (ok_inj (ptr_eq _).symm)
        (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.ASID_POOL]))⟩
  obtain ⟨p, hp, eb, et⟩ := key
  -- no object of `H` but `other` ones starts in the frame
  have hpal := vsFr_al hS.2.pt hS.2.vs hp
  have hVq : ∀ w : U64, p.val ≤ w.val → w.val < p.val + 4096 → VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) w :=
    fun w g1 g2 => Or.inr (Or.inr (Or.inl ⟨p, hp, g1, g2⟩))
  have noH : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → p.val ≤ q.val → q.val < p.val + 4096 → False :=
    fun q k hq hk g1 g2 => by
      have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
      cases k with
      | tcb =>
        obtain ⟨Tr, Cq, hJ⟩ := J.jpl
        have hqT : q ∈ Z.T := J.thT q ((hJ.tcb q).2 hq)
        have hal := J.kern.heap.align q _ hq
        have hfit := J.kern.heap.fits q _ hq
        simp only [P1.HKind.bits] at hal hfit
        have hqp : q.val = p.val := by omega
        have hv : (core.num.U64.wrapping_add q 256#u64).val = q.val + 256 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        exact hS.2.disj (core.num.U64.wrapping_add q 256#u64)
          (Or.inr (Or.inr (Or.inl ⟨q, hqT, by omega, by omega⟩))) (hVq _ (by omega) (by omega))
      | ep => rcases J.vobj_apart (hVq q g1 g2) hq (Or.inl rfl) with e | e <;> omega
      | ntfn => rcases J.vobj_apart (hVq q g1 g2) hq (Or.inr (Or.inl rfl)) with e | e <;> omega
      | reply => rcases J.vobj_apart (hVq q g1 g2) hq (Or.inr (Or.inr (Or.inl rfl))) with e | e <;> omega
      | sc z =>
        by_cases hqC : q ∈ Z.C
        · rcases J.vobj_apart (hVq q g1 g2) hq (Or.inr (Or.inr (Or.inr ⟨z, rfl, hqC⟩))) with e | e <;> omega
        · simp only [P1.HKind.bits] at this
          rcases J.vsFr_sc hp hq with e | e <;> omega
      | other z => exact hk z rfl
  unfold EmptyReady
  rw [hcv']
  intro _ _
  refine fun lo hi hlh h1 h2 => Or.inr fun q hq => ?_
  · cases hk : H q with
    | none => exact deadP_none hk
    | some k =>
      by_cases ho : ∃ z, k = .other z
      · obtain ⟨z, rfl⟩ := ho
        exact ⟨fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun e => (by rw [hk] at e; cases e), fun e => (by rw [hk] at e; cases e),
          fun z' e => (by rw [hk] at e; cases e)⟩
      · exact (noH q k hk (fun z e => ho ⟨z, e⟩) (by omega) (by omega)).elim

end

end

end Fl4Proofs.P3
