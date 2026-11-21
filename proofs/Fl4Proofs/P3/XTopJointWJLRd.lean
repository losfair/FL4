/-
P3 (DESIGN.md §9), CSpace: **the loop's readiness `RdLO` at `WJL`**
(XTopJointWJLEmpty): `LiveOther` from `LiveJ` as XTopJointLive's
`JAtZ.readyLive` gives `ReadyLive` (a cap at `x` naming a container, or
being a thread cap, has another such cap elsewhere), in the same three cases
(`x`'s cap naming nothing, another cap of its key, a removable zombie), and
`rdTrivJLO`: `RdTrivHyp` at `WJL` with `RdLO` (XTopJointDelR's `rdTrivJ` and
`rdTrivJL` with `LiveJ` from `WJL` in place of `LiveJHyp`; a zombie's TCB
dead by `LiveJ.zdead`).
-/
import Fl4Proofs.P3.XTopJointWJLEmpty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`LiveOther` from `LiveJ`** (module docstring). -/
theorem LiveJ.liveOther {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hL : LiveJ (L := L) th H G s σ) {x : U64}
    (hc1 : ∀ q i, IsSlotAt th q i → slotOf q i ≠ x → InUse (L.mem s) σ (slotOf q i) →
      RefsObj q (capV (L.mem s) x) → ∃ y ∈ G.chains.flatten, y ≠ x ∧ RefsObj q (capV (L.mem s) y))
    (hc2 : ∀ w, capV (L.mem s) x = .Thread w → ∃ y ∈ G.chains.flatten, y ≠ x ∧ capV (L.mem s) y = .Thread w) :
    LiveOther (L := L) th s σ G x := by
  refine ⟨fun q i hqi hne hu => ?_, fun k hk hki => ?_⟩
  · rcases hL.slots q i hqi hu with ⟨y', hy', hr⟩ | hb
    rotate_left
    · exact Or.inr hb
    refine Or.inl ?_
    by_cases e : y' = x
    · subst e; exact hc1 q i hqi hne hu hr
    · exact ⟨y', hy', e, hr⟩
  · obtain ⟨y', hy', hT⟩ := hL.dbg k hk hki
    by_cases e : y' = x
    · subst e; exact hc2 _ hT
    · exact ⟨y', hy', e, hT⟩

/-- `LiveOther` when `x`'s cap names no container and is no thread cap. -/
theorem LiveJ.liveOther_noRef {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hL : LiveJ (L := L) th H G s σ) {x : U64} (hn : ∀ q, ¬ RefsObj q (capV (L.mem s) x)) :
    LiveOther (L := L) th s σ G x :=
  hL.liveOther (fun q _ _ _ _ h => absurd h (hn q)) (fun w h => absurd (by rw [h]; rfl) (hn w))

/-- `LiveOther` when another cap of the MDB has `x`'s cap's key. -/
theorem LiveJ.liveOther_key {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hL : LiveJ (L := L) th H G s σ) {x y : U64} (hy : y ∈ G.chains.flatten) (hne : y ≠ x)
    (hk : okey (capV (L.mem s) y) = okey (capV (L.mem s) x)) (hkn : okey (capV (L.mem s) x) ≠ none) :
    LiveOther (L := L) th s σ G x := by
  refine hL.liveOther (fun q _ _ _ _ hr => ⟨y, hy, hne, ?_⟩) (fun w hw => ⟨y, hy, hne, ?_⟩)
  · generalize capV (L.mem s) x = c at hr hk hkn
    generalize capV (L.mem s) y = d at hk ⊢
    cases c <;> simp only [RefsObj] at hr <;> subst hr <;> cases d <;> simp_all [okey, RefsObj]
  · rw [hw] at hk
    generalize capV (L.mem s) y = d at hk ⊢
    cases d <;> simp_all [okey]

/-- `LiveOther` at a removable zombie: its object's slots unused but its own. -/
theorem LiveJ.liveOther_zombie {th : TypedHeap} {H : P1.Heap} {G : MdbGhost} {s : S} {σ : Fl4Spec.State Unit}
    (hP : Placed th) (hL : LiveJ (L := L) th H G s σ) {x : U64} (hx : IsSlot th x) {p zt n : U64}
    (hz : capV (L.mem s) x = .Zombie p zt n) (hrm : n.val = 0 ∨ (n.val = 1 ∧ p = x)) :
    LiveOther (L := L) th s σ G x := by
  refine hL.liveOther (fun q i hqi hne hu hr => ?_) (fun w h => by rw [hz] at h; cases h)
  rw [hz] at hr
  simp only [RefsObj] at hr
  subst hr
  exfalso
  have hlt : ¬ n.val ≤ i := fun h => hL.zslots x hx p zt n hz i hqi h hu
  rcases hrm with h0 | ⟨h1, hpx⟩
  · omega
  · have hi : i = 0 := by omega
    subst hi
    apply hne
    have hv := hqi.val hP
    apply UScalar.eq_of_val_eq
    rw [hv, ← hpx]; simp

variable (arI : machine.Arch A) {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **The readiness at `WJL` of a cap finalised without effect** (module
docstring). -/
theorem rdTrivJLO [Fl4Proofs.P1.PlainStore st] (Z : XSets) (H : P1.Heap)
    (Cs : Set U64) (kb : U64) (hth : Z.th = th) :
    RdTrivHyp (L := L) (WJL (L := L) arI AR Z H Cs kb) (RdLO (L := L) (A := A) th H) th := by
  intro s a σ G sl c hDS hW hA hc hcn hnk hCN hZ
  subst hth
  obtain ⟨⟨V, Ac, Lst, D, J, -, -, -, -⟩, hL, -, -⟩ := hW
  have hcv := capV_of_capAt hc
  rcases cap_cases c hcn with ht | ⟨q, r, gs, g, rfl⟩ | ⟨p, zt, n, rfl⟩ | ho
  · have hn : ∀ q, ¬ RefsObj q (capV (L.mem s) (cslotAddr sl)) := fun q h => by
      rw [hcv] at h; cases c <;> simp [TrivFin] at ht <;> simp [RefsObj] at h
    refine ⟨⟨?_, J.readyLive_noRef hL hn⟩, hL.liveOther_noRef hn⟩
    intro hp hu
    rw [hcv] at hp hu
    rw [physF_triv c ht hu] at hp
    cases hp
  · have hcvd : CapValid Z.th (.CNode q r gs g) := hDS.1.2.1.abs hA hc
    have hfin : ¬ Fl4Spec.isFinalCap' (absCap (.CNode q r gs g)) σ := fun hf =>
      (show Z.th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).2 (hCN q r gs g rfl hf).1
    obtain ⟨y, hy, hne, hky⟩ := other_keyN J.xtop.rel.1 hDS hA hcv (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)) rfl hfin
    refine ⟨⟨JAtZ.cnode_ready arI J hcv (show Z.th q = some (.cnode r.val) ∧ r.val ≠ 0 from hcvd).1,
      J.readyLive_key hL hy hne (by rw [hky, hcv]) (by rw [hcv]; simp [okey])⟩,
      hL.liveOther_key hy hne (by rw [hky, hcv]) (by rw [hcv]; simp [okey])⟩
  · exact ⟨⟨J.zombie_ready hA.isSlot hcv (hL.zdead _ hA.isSlot p zt n hcv),
      J.readyLive_zombie hL hA.isSlot hcv (hZ p zt n rfl)⟩,
      hL.liveOther_zombie J.xtop.rel.1 hA.isSlot hcv (hZ p zt n rfl)⟩
  · exact absurd ho hnk

end

end

end Fl4Proofs.P3
