/-
P3 (DESIGN.md §9), CSpace: **the facts a slot step's caller gives about the
slots written** (StepSem's `slot` and `cslot`): their CNodes live
(`DestLive`, from the lookups' `CnRef`), and where the untyped caps after
come from (`UtSrc`).
-/
import Fl4Proofs.P3.Lookup
import Fl4Proofs.P3.Restart
import Fl4Proofs.P3.MdbInsert
import Fl4Proofs.P3.MdbOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The destination of a slot step lies in a live CNode (named by a CNode
cap held in a slot) or in the kernel-state block (the IRQ node). -/
def DestLive (th : TypedHeap) (mem : U64 → U64) (kb pd : U64) : Prop :=
  (∃ y r gs g, IsSlot th y ∧ capV mem y = .CNode pd r gs g) ∨
    (∀ k, th pd = some k → kb.val ≤ pd.val ∧ pd.val + objSize k ≤ kb.val + 13568)

theorem DestLive.same {th : TypedHeap} {m m' : U64 → U64} {kb kb' pd : U64} (h : DestLive th m kb pd)
    (hS : SlotsSame th m m') (hk : kb' = kb) : DestLive th m' kb' pd := by
  subst hk
  rcases h with ⟨y, r, gs, g, hy, hc⟩ | h
  · exact Or.inl ⟨y, r, gs, g, hy, by rw [hS.capV hy]; exact hc⟩
  · exact Or.inr h

/-- A CNode reached by a lookup from a root held in a slot is live. -/
theorem DestLive.of_cnRef {th : TypedHeap} {mem : U64 → U64} {c0 : capability.Cap} {kb pd : U64}
    (h : CnRef th mem c0 pd) (hroot : ∃ y, IsSlot th y ∧ capV mem y = c0) : DestLive th mem kb pd := by
  obtain ⟨r, gs, g, hr⟩ := h
  rcases hr with ⟨p, r', idx, hp, hl, hc⟩ | e
  · exact Or.inl ⟨cslotAddr (p.bv, idx), r, gs, g, AbsSlot.isSlot ⟨p, rfl, Or.inl (by rw [hl]; exact hp)⟩,
      capV_of_capAt hc⟩
  · obtain ⟨y, hy, hyc⟩ := hroot
    exact Or.inl ⟨y, r, gs, g, hy, by rw [hyc, e]⟩

/-- **The CNode `pd` named by a CNode cap of a slot** (`DestLive`'s left
disjunct). -/
def DestCap (th : TypedHeap) (mem : U64 → U64) (pd : U64) : Prop :=
  ∃ y r gs g, IsSlot th y ∧ capV mem y = .CNode pd r gs g

theorem DestCap.live {th : TypedHeap} {mem : U64 → U64} {pd : U64} (h : DestCap th mem pd) (kb : U64) :
    DestLive th mem kb pd := Or.inl h

theorem DestCap.same {th : TypedHeap} {m m' : U64 → U64} {pd : U64} (h : DestCap th m pd)
    (hS : SlotsSame th m m') : DestCap th m' pd := by
  obtain ⟨y, r, gs, g, hy, hc⟩ := h
  exact ⟨y, r, gs, g, hy, by rw [hS.capV hy]; exact hc⟩

/-- A CNode reached by a lookup from a root held in a slot is named by a
CNode cap of a slot (`DestLive.of_cnRef`'s left disjunct). -/
theorem DestCap.of_cnRef {th : TypedHeap} {mem : U64 → U64} {c0 : capability.Cap} {pd : U64}
    (h : CnRef th mem c0 pd) (hroot : ∃ y, IsSlot th y ∧ capV mem y = c0) : DestCap th mem pd := by
  obtain ⟨r, gs, g, hr⟩ := h
  rcases hr with ⟨p, r', idx, hp, hl, hc⟩ | e
  · exact ⟨cslotAddr (p.bv, idx), r, gs, g, AbsSlot.isSlot ⟨p, rfl, Or.inl (by rw [hl]; exact hp)⟩,
      capV_of_capAt hc⟩
  · obtain ⟨y, hy, hyc⟩ := hroot
    exact ⟨y, r, gs, g, hy, by rw [hyc, e]⟩

/-- **Where a CNode-only step's untyped caps come from**: each untyped cap of
a slot after was one of a slot before over the same region, with the same
free index and device flag and a child then if it has none now, or is now full and has a
child (a copy's source, `cap_insert`'s `set_untyped_cap_as_full`). -/
def UtSrc (th : TypedHeap) (m m' : U64 → U64) (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ sl p sb fi d, AbsSlot th sl → capV m' (cslotAddr sl) = .Untyped p sb fi d →
    ∃ sl0 fi0, AbsSlot th sl0 ∧ capV m (cslotAddr sl0) = .Untyped p sb fi0 d ∧
      ((fi0 = fi ∧ ((¬ ∃ x, σ'.cdt x = some sl) → ¬ ∃ x, σ.cdt x = some sl0)) ∨
        (fi.val = 2 ^ sb.val ∧ ∃ x, σ'.cdt x = some sl))

theorem UtSrc.trans {th : TypedHeap} {m1 m2 m3 : U64 → U64} {σ1 σ2 σ3 : Fl4Spec.State Unit}
    (h1 : UtSrc th m1 m2 σ1 σ2) (h2 : UtSrc th m2 m3 σ2 σ3) : UtSrc th m1 m3 σ1 σ3 := by
  intro sl p sb fi d hs hc
  obtain ⟨sl1, fi1, hs1, hc1, h⟩ := h2 sl p sb fi d hs hc
  obtain ⟨sl0, fi0, hs0, hc0, h'⟩ := h1 sl1 p sb fi1 d hs1 hc1
  refine ⟨sl0, fi0, hs0, hc0, ?_⟩
  rcases h with ⟨rfl, hn⟩ | hB
  · rcases h' with ⟨rfl, hn'⟩ | ⟨hf, hx⟩
    · exact Or.inl ⟨rfl, fun h => hn' (hn h)⟩
    · by_cases hc3 : ∃ x, σ3.cdt x = some sl
      · exact Or.inr ⟨hf, hc3⟩
      · exact absurd hx (hn hc3)
  · exact Or.inr hB

end

end Fl4Proofs.P3
