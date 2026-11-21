/-
P3 (DESIGN.md §9), VSpace: **the frame invariant** `FrameInv`, next to
`MdbInv`: every cap of the MDB naming a page of a large (2 MiB, RAM) frame
cap's window is a frame cap in that cap's chain (l4h 0029's aliases, and
copies of the large frame). `DeriveSubframe` needs it (`hov` of
`insert_frame_fin`).

Preservation, per primitive (for the CSpace paths too):
* `FrameInv.of_caps`: the MDB's caps kept (`set_thread_state`, writes
  outside the slots);
* `FrameInv.recap`: one slot's cap replaced by one alike for the MDB
  (`MdbLike`: a remapped frame or table cap, an untyped cap's free index);
* `FrameInv.remove`: a slot removed from its chain (delete);
* `FrameInv.rename`: the slots renamed (move, swap);
* `FrameInv.insert_copy`: a cap derived from `src` inserted after it (copy,
  mint, mutate: its objects among `src`'s, a frame iff `src`'s cap is, large
  only as `src`'s);
* `FrameInv.insert_fresh`: a non-frame cap naming no page of a large frame
  (retype, `MakePool`'s pool cap);
* `FrameInv.insert_alias`: a 4 KiB alias of a page of `src`'s large frame
  (`DeriveSubframe`), the large frames 2 MiB-aligned (`CapValid`).
* `FrameInv.insert_fresh_large`: a large frame cap over a fresh region
  (retype).
At boot: `FrameInv.of_no_large` (stated; there are no boot proofs).
-/
import Fl4Proofs.P3.VsMdb
import Fl4Proofs.P3.VsSubMdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- **The frame invariant** (see the module docstring). -/
def FrameInv (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va →
    ∀ w ∈ G.chains.flatten, ∀ q : U64, p.val ≤ q.val → q.val < p.val + 2 ^ 21 →
      q.bv ∈ Fl4Spec.objRefs (absCap (capV mem w)) →
      isFrame (capV mem w) = true ∧ ∃ ch ∈ G.chains, x ∈ ch ∧ w ∈ ch

theorem objRefs_iff (c : Fl4Spec.Cap) (q : Fl4Spec.ObjRef) :
    q ∈ Fl4Spec.objRefs c ↔ Fl4Spec.GenObjRef.objRef q ∈ Fl4Spec.genObjRefs c := by
  simp only [Fl4Spec.genObjRefs, Set.mem_union, Set.mem_image]
  constructor
  · intro h; exact Or.inl (Or.inl ⟨q, h, rfl⟩)
  · rintro ((⟨x, hx, e⟩ | ⟨x, -, e⟩) | ⟨x, -, e⟩)
    · cases e; exact hx
    · cases e
    · cases e

theorem MdbLike.objRefs {c' c : capability.Cap} (h : MdbLike c' c) :
    Fl4Spec.objRefs (absCap c') = Fl4Spec.objRefs (absCap c) := by
  ext q; rw [objRefs_iff, objRefs_iff, refs_of_shape h.1]

theorem MdbLike.large {c' c : capability.Cap} (h : MdbLike c' c) {p r a va : U64} {mb ep : Bool}
    (hc : c' = .Frame p .Large r false mb ep a va) : ∃ r0 m0 ep0 a0 v0, c = .Frame p .Large r0 false m0 ep0 a0 v0 := by
  obtain ⟨h1, h2, -⟩ := h
  subst hc
  cases c <;> simp_all [shape, okey]

theorem MdbLike.symm {c' c : capability.Cap} (h : MdbLike c' c) : MdbLike c c' := ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

section
variable {mem mem' : U64 → U64} {G : MdbGhost}

/-- **At boot** (no boot proofs exist; stated): an MDB without a large RAM
frame cap satisfies the invariant (the boot MDB, if boot hands out no large
frame cap; not checked here). Retype then grows it with `insert_fresh` /
`insert_fresh_large`. -/
theorem FrameInv.of_no_large {mem : U64 → U64} {G : MdbGhost}
    (h : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x ≠ .Frame p .Large r false m ep a va) : FrameInv mem G :=
  fun x hx p r m ep a va hc => absurd hc (h x hx p r m ep a va)

/-- The MDB's caps kept. -/
theorem FrameInv.of_caps (h : FrameInv mem G) (hc : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) :
    FrameInv mem' G := by
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  rw [hc x hx] at hcx; rw [hc w hw] at hq ⊢
  exact h x hx p r m ep a va hcx w hw q h1 h2 hq

/-- One slot's cap replaced by one alike for the MDB. -/
theorem FrameInv.recap (h : FrameInv mem G) (x0 : U64) (hl : MdbLike (capV mem' x0) (capV mem x0))
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : FrameInv mem' G := by
  have hlk : ∀ z ∈ G.chains.flatten, MdbLike (capV mem' z) (capV mem z) := fun z hz => by
    by_cases e : z = x0
    · subst e; exact hl
    · rw [hc z hz e]; exact MdbLike.refl _
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hlk x hx).large hcx
  rw [(hlk w hw).objRefs] at hq
  obtain ⟨hf, hch⟩ := h x hx p r0 m0 ep0 a0 v0 hcx0 w hw q h1 h2 hq
  exact ⟨by rw [(shape_kind (hlk w hw).1).2.2.2.1]; exact hf, hch⟩

end

/-- A slot removed from its chain (delete). -/
theorem FrameInv.remove {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (h : FrameInv mem G) (x0 : U64)
    (hc : ∀ z ∈ G.chains.flatten, z ≠ x0 → capV mem' z = capV mem z) : FrameInv mem' (remG G x0) := by
  have hn := hM.tree.nodup
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  obtain ⟨hx0, hxn⟩ := (Mdb.mem_removeChains hn).1 hx
  obtain ⟨hw0, hwn⟩ := (Mdb.mem_removeChains hn).1 hw
  rw [hc x hx0 hxn] at hcx; rw [hc w hw0 hwn] at hq ⊢
  obtain ⟨hf, ch, hch, hxc, hwc⟩ := h x hx0 p r m ep a va hcx w hw0 q h1 h2 hq
  refine ⟨hf, @List.erase U64 instBEqOfDecidableEq ch x0, ?_, ?_, ?_⟩
  · unfold remG Mdb.removeChains
    refine List.mem_filter.2 ⟨List.mem_map.2 ⟨ch, hch, rfl⟩, ?_⟩
    have : x ∈ @List.erase U64 instBEqOfDecidableEq ch x0 := (@List.mem_erase_of_ne U64 instBEqOfDecidableEq _ _ _ _ hxn).2 hxc
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
    exact List.ne_nil_of_mem this
  · exact (@List.mem_erase_of_ne U64 instBEqOfDecidableEq _ _ _ _ hxn).2 hxc
  · exact (@List.mem_erase_of_ne U64 instBEqOfDecidableEq _ _ _ _ hwn).2 hwc

/-- The slots renamed along `e` (move, swap). -/
theorem FrameInv.rename {mem mem' : U64 → U64} {G : MdbGhost} (h : FrameInv mem G) (e : U64 ≃ U64)
    (hc : ∀ z ∈ G.chains.flatten, MdbLike (capV mem' (e z)) (capV mem z)) : FrameInv mem' (renG G e) := by
  have hmem : ∀ z, z ∈ (renG G e).chains.flatten ↔ e.symm z ∈ G.chains.flatten := fun z => mem_renG e z
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  have hx0 := (hmem x).1 hx
  have hw0 := (hmem w).1 hw
  have lx := hc _ hx0; rw [Equiv.apply_symm_apply] at lx
  have lw := hc _ hw0; rw [Equiv.apply_symm_apply] at lw
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := lx.large hcx
  rw [lw.objRefs] at hq
  obtain ⟨hf, ch, hch, hxc, hwc⟩ := h _ hx0 p r0 m0 ep0 a0 v0 hcx0 _ hw0 q h1 h2 hq
  refine ⟨by rw [(shape_kind lw.1).2.2.2.1]; exact hf, ch.map e, List.mem_map.2 ⟨ch, hch, rfl⟩, ?_, ?_⟩
  · exact List.mem_map.2 ⟨_, hxc, by simp⟩
  · exact List.mem_map.2 ⟨_, hwc, by simp⟩

section Ins
variable {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64}

theorem chain_ins {ch : List U64} (hch : ch ∈ G.chains) (hs : src ∈ ch) (b : Bool) :
    Mdb.insAfter src dest ch ∈ (insG G src dest b).chains ∧ src ∈ Mdb.insAfter src dest ch ∧
      dest ∈ Mdb.insAfter src dest ch ∧ ∀ z ∈ ch, z ∈ Mdb.insAfter src dest ch :=
  ⟨List.mem_map.2 ⟨ch, hch, rfl⟩, (mem_insAfter hs).2 (Or.inr hs), (mem_insAfter hs).2 (Or.inl rfl),
    fun z hz => (mem_insAfter hs).2 (Or.inr hz)⟩

theorem chain_ins' {ch : List U64} (hch : ch ∈ G.chains) (b : Bool) :
    Mdb.insAfter src dest ch ∈ (insG G src dest b).chains ∧ ∀ z ∈ ch, z ∈ Mdb.insAfter src dest ch := by
  refine ⟨List.mem_map.2 ⟨ch, hch, rfl⟩, fun z hz => ?_⟩
  by_cases hs : src ∈ ch
  · exact (mem_insAfter hs).2 (Or.inr hz)
  · rw [Mdb.insAfter_of_not_mem hs]; exact hz

/-- A cap derived from `src` inserted after it (copy, mint, mutate). -/
theorem FrameInv.insert_copy (h : FrameInv mem G) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
    (b : Bool) {c : capability.Cap} (hcd : capV mem' dest = c) (hcs : MdbLike (capV mem' src) (capV mem src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z)
    (hrefs : ∀ q, q ∈ Fl4Spec.objRefs (absCap c) → q ∈ Fl4Spec.objRefs (absCap (capV mem src)))
    (hfrm : isFrame c = isFrame (capV mem src))
    (hlg : ∀ p r mm ep a va, c = .Frame p .Large r false mm ep a va →
      ∃ r' mm' ep' a' va', capV mem src = .Frame p .Large r' false mm' ep' a' va') :
    FrameInv mem' (insG G src dest b) := by
  have hne : ∀ z ∈ G.chains.flatten, z ≠ dest := fun z hz e => hdest (e ▸ hz)
  have hlk : ∀ z ∈ G.chains.flatten, MdbLike (capV mem' z) (capV mem z) := fun z hz => by
    by_cases e : z = src
    · subst e; exact hcs
    · rw [hcap z hz e]; exact MdbLike.refl _
  obtain ⟨chs, hchs, hss⟩ := List.mem_flatten.1 hsrc
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0 <;> rcases (mem_flatten_ins hsrc).1 hw with rfl | hw0
  · -- both the new cap
    rw [hcd] at hcx; subst hcx
    obtain ⟨c1, c2, c3, c4⟩ := chain_ins hchs hss b
    exact ⟨by rw [hcd]; rfl, _, c1, c3, c3⟩
  · -- the new large frame cap, an old cap naming its page
    rw [hcd] at hcx
    obtain ⟨r', mm', ep', a', va', hsC⟩ := hlg p r m ep a va hcx
    rw [(hlk w hw0).objRefs] at hq
    obtain ⟨hf, ch, hch, hsc, hwc⟩ := h src hsrc p r' mm' ep' a' va' hsC w hw0 q h1 h2 hq
    obtain ⟨c1, c2, c3, c4⟩ := chain_ins hch hsc b
    exact ⟨by rw [(shape_kind (hlk w hw0).1).2.2.2.1]; exact hf, _, c1, c3, c4 w hwc⟩
  · -- an old large frame cap, the new cap naming its page
    obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hlk x hx0).large hcx
    rw [hcd] at hq
    obtain ⟨hf, ch, hch, hxc, hsc⟩ := h x hx0 p r0 m0 ep0 a0 v0 hcx0 src hsrc q h1 h2 (hrefs _ hq)
    obtain ⟨c1, c2, c3, c4⟩ := chain_ins hch hsc b
    exact ⟨by rw [hcd, hfrm]; exact hf, _, c1, c4 x hxc, c3⟩
  · obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hlk x hx0).large hcx
    rw [(hlk w hw0).objRefs] at hq
    obtain ⟨hf, ch, hch, hxc, hwc⟩ := h x hx0 p r0 m0 ep0 a0 v0 hcx0 w hw0 q h1 h2 hq
    obtain ⟨c1, c4⟩ := chain_ins' (src := src) (dest := dest) hch b
    exact ⟨by rw [(shape_kind (hlk w hw0).1).2.2.2.1]; exact hf, _, c1, c4 x hxc, c4 w hwc⟩

/-- A non-frame cap naming no page of a large frame, inserted (retype,
`MakePool`). -/
theorem FrameInv.insert_fresh (h : FrameInv mem G) (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten)
    (b : Bool) {c : capability.Cap} (hcd : capV mem' dest = c) (hcs : MdbLike (capV mem' src) (capV mem src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z)
    (hnl : ∀ p r mm ep a va, c ≠ .Frame p .Large r false mm ep a va)
    (hout : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va →
      ∀ q : U64, p.val ≤ q.val → q.val < p.val + 2 ^ 21 → q.bv ∉ Fl4Spec.objRefs (absCap c)) :
    FrameInv mem' (insG G src dest b) := by
  have hlk : ∀ z ∈ G.chains.flatten, MdbLike (capV mem' z) (capV mem z) := fun z hz => by
    by_cases e : z = src
    · subst e; exact hcs
    · rw [hcap z hz e]; exact MdbLike.refl _
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · rw [hcd] at hcx; exact absurd hcx (hnl p r m ep a va)
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hlk x hx0).large hcx
  rcases (mem_flatten_ins hsrc).1 hw with rfl | hw0
  · rw [hcd] at hq; exact absurd hq (hout x hx0 p r0 m0 ep0 a0 v0 hcx0 q h1 h2)
  rw [(hlk w hw0).objRefs] at hq
  obtain ⟨hf, ch, hch, hxc, hwc⟩ := h x hx0 p r0 m0 ep0 a0 v0 hcx0 w hw0 q h1 h2 hq
  obtain ⟨c1, c4⟩ := chain_ins' (src := src) (dest := dest) hch b
  exact ⟨by rw [(shape_kind (hlk w hw0).1).2.2.2.1]; exact hf, _, c1, c4 x hxc, c4 w hwc⟩

/-- A large RAM frame cap over a fresh region inserted (retype): no cap of the
MDB names a page of its window, and it names no page of another large
frame's window. -/
theorem FrameInv.insert_fresh_large (h : FrameInv mem G) (hsrc : src ∈ G.chains.flatten)
    (hdest : dest ∉ G.chains.flatten) (b : Bool) {c : capability.Cap} (hcd : capV mem' dest = c)
    (hcs : MdbLike (capV mem' src) (capV mem src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z)
    (hown : ∀ p r mm ep a va, c = .Frame p .Large r false mm ep a va → ∀ w ∈ G.chains.flatten, ∀ q : U64,
      p.val ≤ q.val → q.val < p.val + 2 ^ 21 → q.bv ∉ Fl4Spec.objRefs (absCap (capV mem w)))
    (hout : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va →
      ∀ q : U64, p.val ≤ q.val → q.val < p.val + 2 ^ 21 → q.bv ∉ Fl4Spec.objRefs (absCap c)) :
    FrameInv mem' (insG G src dest b) := by
  have hlk : ∀ z ∈ G.chains.flatten, MdbLike (capV mem' z) (capV mem z) := fun z hz => by
    by_cases e : z = src
    · subst e; exact hcs
    · rw [hcap z hz e]; exact MdbLike.refl _
  obtain ⟨chs, hchs, hss⟩ := List.mem_flatten.1 hsrc
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · rw [hcd] at hcx
    rcases (mem_flatten_ins hsrc).1 hw with rfl | hw0
    · obtain ⟨c1, -, c3, -⟩ := chain_ins hchs hss b
      exact ⟨by rw [hcd, hcx]; rfl, _, c1, c3, c3⟩
    · rw [(hlk w hw0).objRefs] at hq; exact absurd hq (hown p r m ep a va hcx w hw0 q h1 h2)
  obtain ⟨r0, m0, ep0, a0, v0, hcx0⟩ := (hlk x hx0).large hcx
  rcases (mem_flatten_ins hsrc).1 hw with rfl | hw0
  · rw [hcd] at hq; exact absurd hq (hout x hx0 p r0 m0 ep0 a0 v0 hcx0 q h1 h2)
  rw [(hlk w hw0).objRefs] at hq
  obtain ⟨hf, ch, hch, hxc, hwc⟩ := h x hx0 p r0 m0 ep0 a0 v0 hcx0 w hw0 q h1 h2 hq
  obtain ⟨c1, c4⟩ := chain_ins' (src := src) (dest := dest) hch b
  exact ⟨by rw [(shape_kind (hlk w hw0).1).2.2.2.1]; exact hf, _, c1, c4 x hxc, c4 w hwc⟩

/-- **A 4 KiB alias of a page of `src`'s large frame inserted after it**
(`DeriveSubframe`), the large frames of the MDB 2 MiB-aligned. -/
theorem FrameInv.insert_alias (h : FrameInv mem G) (hsrc : src ∈ G.chains.flatten)
    (hdest : dest ∉ G.chains.flatten) (b : Bool) {ptr rt fa fv q0 vm : U64} {mm epSrc : Bool}
    (hsC : capV mem src = .Frame ptr .Large rt false mm epSrc fa fv)
    (hcd : capV mem' dest = .Frame q0 .Small vm false false false 0#u64 0#u64)
    (hcs : capV mem' src = capV mem src)
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z)
    (hq1 : ptr.val ≤ q0.val) (hq2 : q0.val < ptr.val + 2 ^ 21)
    (halg : ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va → p.val % 2 ^ 21 = 0) :
    FrameInv mem' (insG G src dest b) := by
  have hlk : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z := fun z hz => by
    by_cases e : z = src
    · subst e; exact hcs
    · exact hcap z hz e
  obtain ⟨chs, hchs, hss⟩ := List.mem_flatten.1 hsrc
  have hpal := halg src hsrc _ _ _ _ _ _ hsC
  intro x hx p r m ep a va hcx w hw q h1 h2 hq
  rcases (mem_flatten_ins hsrc).1 hx with rfl | hx0
  · rw [hcd] at hcx; cases hcx
  rw [hlk x hx0] at hcx
  rcases (mem_flatten_ins hsrc).1 hw with rfl | hw0
  · -- the alias names `q0`, in `x`'s window: `x`'s window is `src`'s
    rw [hcd] at hq
    have hq0 : q = q0 := by
      simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef] at hq; exact P1.eq_of_bv hq
    subst hq0
    have hxal := halg x hx0 _ _ _ _ _ _ hcx
    have hpp : ptr = p := UScalar.eq_of_val_eq (by omega)
    subst hpp
    have hsr : ptr.bv ∈ Fl4Spec.objRefs (absCap (capV mem src)) := by
      rw [hsC]; simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef]
    obtain ⟨-, ch, hch, hxc, hsc⟩ := h x hx0 ptr r m ep a va hcx src hsrc ptr le_rfl (by omega) hsr
    obtain ⟨c1, c2, c3, c4⟩ := chain_ins hch hsc b
    exact ⟨by rw [hcd]; rfl, _, c1, c4 x hxc, c3⟩
  · rw [hlk w hw0] at hq ⊢
    obtain ⟨hf, ch, hch, hxc, hwc⟩ := h x hx0 p r m ep a va hcx w hw0 q h1 h2 hq
    obtain ⟨c1, c4⟩ := chain_ins' (src := src) (dest := dest) hch b
    exact ⟨hf, _, c1, c4 x hxc, c4 w hwc⟩

end Ins

/-- An alias overlapping a cap names its page. -/
theorem ovl_page_ref {q vm : U64} {c : capability.Cap}
    (h : Ovl (absCap (.Frame q .Small vm false false false 0#u64 0#u64)) (absCap c)) :
    q.bv ∈ Fl4Spec.objRefs (absCap c) := by
  unfold Ovl at h
  obtain ⟨g, hg1, hg2⟩ := Set.nonempty_iff_ne_empty.2 h
  simp [Fl4Spec.genObjRefs, absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef, Fl4Spec.capIrqs, Fl4Spec.archCapSetMap,
    Fl4Spec.archGenObjRefs, Fl4Spec.capIrqOpt] at hg1
  subst hg1
  exact (objRefs_iff _ _).2 hg2

/-- **`DeriveSubframe`'s `hov`** from the invariant. -/
theorem FrameInv.alias_ov {mem : U64 → U64} {G : MdbGhost} (h : FrameInv mem G) {src : U64}
    (hsrc : src ∈ G.chains.flatten) {ptr rt fa fv : U64} {mm epSrc : Bool}
    (hsC : capV mem src = .Frame ptr .Large rt false mm epSrc fa fv) :
    ∀ w ∈ G.chains.flatten, ∀ q vm : U64, ptr.val ≤ q.val → q.val < ptr.val + 2 ^ 21 →
      Ovl (absCap (.Frame q .Small vm false false false 0#u64 0#u64)) (absCap (capV mem w)) →
      isFrame (capV mem w) = true ∧ ∃ ch ∈ G.chains, src ∈ ch ∧ w ∈ ch :=
  fun w hw q vm h1 h2 hov => h src hsrc ptr rt mm epSrc fa fv hsC w hw q h1 h2 (ovl_page_ref hov)

/-- A large frame's range is its 2 MiB window, when it does not wrap. -/
theorem large_top {p0 r a va : U64} {m ep : Bool} (hreg : baseF (.Frame p0 .Large r false m ep a va) ≤
    topF (.Frame p0 .Large r false m ep a va)) : topF (.Frame p0 .Large r false m ep a va) = p0.val + 2 ^ 21 - 1 := by
  obtain ⟨bs, ts⟩ := frame_range p0 .Large r false m a va ep
  have hmL : (maskF (fbitsF .Large)).val = 2 ^ 21 - 1 := by
    rw [maskF_val (by rw [fbitsF_val]; decide), fbitsF_val]; rfl
  rw [bs, ts] at hreg; rw [ts]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmL] at hreg ⊢
  have : p0.val < 2 ^ 64 := p0.hBounds
  omega

/-- **An ASID pool cap disjoint from a large frame names none of its pages**
(`insert_fresh`'s `hout` for `MakePool`, from `InsACtx`'s `hreg`/`hno`). -/
theorem pool_out {c : capability.Cap} {p0 r a va : U64} {m ep : Bool} (hc : c = .Frame p0 .Large r false m ep a va)
    {p b : U64} (hreg : physF c = true → baseF c ≤ topF c)
    (hno : physF c = true → Disj c (.AsidPool p b) ∨ isUt c = true)
    (hpr : baseF (.AsidPool p b) ≤ topF (.AsidPool p b))
    (q : U64) (h1 : p0.val ≤ q.val) (h2 : q.val < p0.val + 2 ^ 21) :
    q.bv ∉ Fl4Spec.objRefs (absCap (.AsidPool p b)) := by
  subst hc
  intro hq
  have hqp : q = p := by
    simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef] at hq; exact P1.eq_of_bv hq
  subst hqp
  have hph := physF_frame p0 .Large r false m a va ep
  have ht := large_top (hreg hph)
  have hb2 : baseF (.AsidPool q b) = q.val := by unfold baseF; rw [ptrF_of rfl]
  have hbs := (frame_range p0 .Large r false m a va ep).1
  rcases hno hph with h | h
  · unfold Disj at h; omega
  · simp [isUt] at h

/-- The cap of a slot is valid. -/
theorem capValid_slot {th : TypedHeap} {mem : U64 → U64} (hV : SlotsValid th mem) {z : U64} (h : IsSlot th z) :
    CapValid th (capV mem z) := by
  obtain ⟨p, i, hi, rfl⟩ := h
  rcases hi with ⟨r, hp, hi⟩ | ⟨hp, hi⟩
  · exact hV.cnode p r hp i hi _ (capAt_capV _ _)
  · exact hV.tcb p hp i hi _ (capAt_capV _ _)

/-- The large frames of the MDB are 2 MiB aligned (`insert_alias`'s `halg`). -/
theorem large_aligned {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hV : SlotsValid th mem)
    (hM : MdbLinks th mem G) :
    ∀ x ∈ G.chains.flatten, ∀ p r m ep a va, capV mem x = .Frame p .Large r false m ep a va → p.val % 2 ^ 21 = 0 := by
  intro x hx p r m ep a va hc
  have h := capValid_slot hV ((hM.members x).1 hx).1
  rw [hc] at h; exact h

/-- **After a VSpace invocation** with the footprint of VsFoot. -/
theorem FrameInv.after {th : TypedHeap} {m m' : U64 → U64} {G : MdbGhost} {x : U64} (hM : MdbLinks th m G)
    (h : FrameInv m G) (hF : SlotFoot th m m' x) (hx : MdbLike (capV m' x) (capV m x)) : FrameInv m' G := by
  refine h.recap x hx (fun z hz hne => ?_)
  have hzs := ((hM.members z).1 hz).1
  unfold capV; rw [((hF z hzs).2.2 hne).1, ((hF z hzs).2.2 hne).2]

end

end Fl4Proofs.P3.Vs
