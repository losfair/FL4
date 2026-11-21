/-
P3 (DESIGN.md §9), invariant line G1 (sb1): **the refill writers that keep the
binding frame only as a whole** (spec side only; imports SpecInvSbK).

`refill_pop_head` can empty an SC's refill list (`List.tail` of a one-element
list) and `refill_new` raises `sc_refill_max` before writing the refills, so the
single steps break `BR`'s refill clauses; the functions around them restore
them: every path ends in a write of a non-empty refill list (`update_refill_hd`,
`update_refill_tl`, `refill_add_tail`, `[the head]`, `[refill]`). The proofs
track `RO p k` (only the SC at `p` changed, its TCB kept) and `NE` (its refills
non-empty), and close with `br_of_ro_ne`.

* `sb_mergeOverlappingRefills`, `sb_mergeNonoverlappingHeadRefill`,
  `sb_chargeEntireHeadRefill`, `sb_refillNew`, `sb_refillUpdate`: `SBK h0`.
-/
import Fl4Proofs.P3.SpecInvSbK
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-- Only the SC at `p` changed, with the same TCB and size. -/
def RO (p : ObjRef) (k k' : KHeap) : Prop :=
  (∀ q, q ≠ p → k' q = k q) ∧
    (k' p = k p ∨ ∃ y n y', k p = some (.schedContext y n) ∧ k' p = some (.schedContext y' n) ∧ y'.scTcb = y.scTcb)

theorem RO.refl (p : ObjRef) (k : KHeap) : RO p k k := ⟨fun _ _ => rfl, Or.inl rfl⟩

theorem RO.trans {p : ObjRef} {k1 k2 k3 : KHeap} (a : RO p k1 k2) (b : RO p k2 k3) : RO p k1 k3 := by
  refine ⟨fun q hq => (b.1 q hq).trans (a.1 q hq), ?_⟩
  rcases b.2 with e | ⟨y, n, y', h2, h3, e3⟩
  · rw [e]; exact a.2
  · rcases a.2 with e' | ⟨y0, n0, y1, h1, h2', e2⟩
    · exact Or.inr ⟨y, n, y', by rw [← e']; exact h2, h3, e3⟩
    · rw [h2'] at h2
      simp only [Option.some.injEq, KernelObject.schedContext.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr ⟨y0, n0, y', h1, h3, e3.trans e2⟩

/-- The SC at `p`, if any, has refills. -/
def NE (p : ObjRef) (k : KHeap) : Prop := ∀ y n, k p = some (.schedContext y n) → y.scRefills ≠ []

theorem br_of_ro_ne {p : ObjRef} {k k' : KHeap} (h : RO p k k') (hne : NE p k') : BR k k' := by
  refine ⟨fun q x hx => ?_, fun q x hx => ?_, fun q y n hy => ?_, fun q y n hy => ?_⟩
  · by_cases e : q = p
    · subst e
      rcases h.2 with e | ⟨y, n, y', h1, -, -⟩
      · exact ⟨x, by rw [e]; exact hx, rfl⟩
      · rw [h1] at hx; cases hx
    · exact ⟨x, by rw [h.1 q e]; exact hx, rfl⟩
  · by_cases e : q = p
    · subst e
      rcases h.2 with e | ⟨y, n, y', -, h2, -⟩
      · exact ⟨x, by rw [← e]; exact hx⟩
      · rw [h2] at hx; cases hx
    · rw [h.1 q e] at hx; exact ⟨x, hx⟩
  · by_cases e : q = p
    · subst e
      rcases h.2 with e | ⟨y0, n0, y', h1, h2, e3⟩
      · exact ⟨y, n, by rw [e]; exact hy, scKeep_refl y⟩
      · rw [h1] at hy
        simp only [Option.some.injEq, KernelObject.schedContext.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨y', _, h2, scKeep_ne e3 (hne _ _ h2)⟩
    · exact ⟨y, n, by rw [h.1 q e]; exact hy, scKeep_refl y⟩
  · by_cases e : q = p
    · subst e
      rcases h.2 with e | ⟨y0, n0, y', h1, h2, -⟩
      · exact ⟨y, n, by rw [← e]; exact hy⟩
      · exact ⟨y0, n0, h1⟩
    · rw [h.1 q e] at hy; exact ⟨y, n, hy⟩

/-- State forms. -/
def ROs (p : ObjRef) (k : KHeap) (s : State Unit) : Prop := RO p k s.kheap
def RN (p : ObjRef) (k : KHeap) (s : State Unit) : Prop := RO p k s.kheap ∧ NE p s.kheap

/-- Pre/post triples. -/
def HK (P Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → Q x.2

theorem hk_bind {P Q R : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : HK P Q m) (hg : ∀ a, HK Q R (g a)) : HK P R (m >>= g) :=
  fun σ h x ⟨y, hy, hx⟩ => hg y.1 y.2 (hm σ h y hy) x hx

theorem hk_of_ik {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : IK P m) : HK P P m := h

theorem hk_pure_of {P Q : State Unit → Prop} {α : Type} (a : α) (h : ∀ s, P s → Q s) :
    HK P Q (pure a : NonDet (State Unit) α) := by
  intro σ hσ x hx
  rw [Set.mem_singleton_iff.1 hx]; exact h σ hσ

theorem hk_mono {P Q R : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} (h : HK P Q m)
    (hq : ∀ s, Q s → R s) : HK P R m :=
  fun σ hσ x hx => hq _ (h σ hσ x hx)

theorem rn_ro {p : ObjRef} {k : KHeap} {s : State Unit} (h : RN p k s) : ROs p k s := h.1

/-! ## The SC writes -/

theorem ro_upd_step {p : ObjRef} {f : SchedContext → SchedContext} (hf : ∀ y, (f y).scTcb = y.scTcb)
    {σ : State Unit} {x : Unit × State Unit} (hx : x ∈ (updateSchedContext (Z := Unit) p f σ).1) :
    RO p σ.kheap x.2.kheap ∧ ∃ y n, σ.kheap p = some (.schedContext y n) ∧
      x.2.kheap p = some (.schedContext (f y) n) := by
  obtain ⟨y, n, hk, e⟩ := mem_updateSchedContext hx
  rw [e]
  exact ⟨⟨fun q hq => Function.update_of_ne hq _ _, Or.inr ⟨y, n, f y, hk, by simp, hf y⟩⟩, y, n, hk, by simp⟩

theorem ik_ro_upd {p : ObjRef} {k : KHeap} {f : SchedContext → SchedContext} (hf : ∀ y, (f y).scTcb = y.scTcb) :
    IK (ROs p k) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  exact RO.trans hσ (ro_upd_step hf hx).1

theorem hk_ne_upd {p : ObjRef} {k : KHeap} {f : SchedContext → SchedContext} (hf : ∀ y, (f y).scTcb = y.scTcb)
    (hne : ∀ y, (f y).scRefills ≠ []) : HK (ROs p k) (RN p k) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨h1, y, n, -, h2⟩ := ro_upd_step hf hx
  refine ⟨RO.trans hσ h1, fun y' n' h => ?_⟩
  rw [h2] at h
  simp only [Option.some.injEq, KernelObject.schedContext.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hne y

theorem ik_rn_upd {p : ObjRef} {k : KHeap} {f : SchedContext → SchedContext} (hf : ∀ y, (f y).scTcb = y.scTcb)
    (hm : ∀ y, y.scRefills ≠ [] → (f y).scRefills ≠ []) : IK (RN p k) (updateSchedContext (Z := Unit) p f) := by
  intro σ hσ x hx
  obtain ⟨h1, y, n, h0, h2⟩ := ro_upd_step hf hx
  refine ⟨RO.trans hσ.1 h1, fun y' n' h => ?_⟩
  rw [h2] at h
  simp only [Option.some.injEq, KernelObject.schedContext.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hm y (hσ.2 y n h0)

/-- Reads keep any predicate. -/
macro "rd_auto" : tactic => `(tactic| repeat' (first | ik_step0 | ik_unfold))

theorem ik_ro_pop (p : ObjRef) (k : KHeap) : IK (ROs p k) (refillPopHead (Z := Unit) p) := by
  unfold refillPopHead
  refine ik_bind (by unfold getRefillHead; rd_auto) fun _ => ik_bind (ik_ro_upd fun _ => rfl) fun _ => ik_pure _

theorem sbk_of_hk {h0 : KHeap} {α : Type} {p : ObjRef} {m : NonDet (State Unit) α}
    (h : ∀ k, HK (ROs p k) (RN p k) m) : SBK h0 m :=
  sbk_of_step fun σ x hx => by
    have := h σ.kheap σ (RO.refl _ _) x hx
    exact br_of_ro_ne this.1 this.2

/-! ## The functions -/

section
variable {h0 : KHeap}

theorem sb_mergeOverlappingRefills (p : ObjRef) : SBK h0 (mergeOverlappingRefills (Z := Unit) p) := by
  refine sbk_of_hk (p := p) fun k => ?_
  unfold mergeOverlappingRefills
  refine hk_bind (hk_of_ik (ik_ro_pop p k)) fun hd => ?_
  unfold updateRefillHd
  exact hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)

theorem sb_mergeNonoverlappingHeadRefill (p : ObjRef) : SBK h0 (mergeNonoverlappingHeadRefill (Z := Unit) p) := by
  refine sbk_of_hk (p := p) fun k => ?_
  unfold mergeNonoverlappingHeadRefill
  refine hk_bind (hk_of_ik (ik_ro_pop p k)) fun hd => ?_
  unfold updateRefillHd
  exact hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ =>
    hk_of_ik (ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _))

theorem hk_scheduleUsed (p : ObjRef) (k : KHeap) (new : Refill) :
    HK (ROs p k) (RN p k) (scheduleUsed (Z := Unit) p new) := by
  unfold scheduleUsed
  refine hk_bind (hk_of_ik (by unfold getRefills; rd_auto)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_assert _)) fun _ => ?_
  refine hk_bind (hk_of_ik (by unfold getRefillTail; rd_auto)) fun tail => ?_
  split
  · unfold updateRefillTl; exact hk_ne_upd (fun _ => rfl) (fun _ => by simp [scRefillsUpdate])
  · refine hk_bind (hk_of_ik (by unfold refillFull; rd_auto)) fun _ => ?_
    split
    · unfold refillAddTail; exact hk_ne_upd (fun _ => rfl) (fun _ => by simp [scRefillsUpdate])
    · unfold updateRefillTl
      exact hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => by simp [scRefillsUpdate])) fun _ =>
        hk_of_ik (ik_rn_upd (fun _ => rfl) (fun _ _ => by simp [scRefillsUpdate]))

theorem sb_chargeEntireHeadRefill (p : ObjRef) (usage : Ticks) :
    SBK h0 (chargeEntireHeadRefill (Z := Unit) p usage) := by
  refine sbk_of_hk (p := p) fun k => ?_
  unfold chargeEntireHeadRefill
  refine hk_bind (hk_of_ik (by unfold getRefillHead; rd_auto)) fun head => ?_
  refine hk_bind (hk_of_ik (by unfold getSchedContext; rd_auto)) fun sc => ?_
  refine hk_bind (hk_of_ik (by unfold refillSingle refillSize getRefills; rd_auto)) fun single => ?_
  dsimp only
  split
  · unfold updateRefillHd
    exact hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ => hk_pure_of _ fun _ h => h
  · exact hk_bind (hk_of_ik (ik_ro_pop p k)) fun _ => hk_bind (hk_scheduleUsed p k _) fun _ =>
      hk_pure_of _ fun _ h => h

theorem ik_rn_maybeAddEmptyTail (p : ObjRef) (k : KHeap) : IK (RN p k) (maybeAddEmptyTail (Z := Unit) p) := by
  unfold maybeAddEmptyTail
  refine ik_bind (by unfold isRoundRobin; rd_auto) fun _ => ?_
  unfold NonDet.when
  split
  · refine ik_bind (by unfold getRefillHead; rd_auto) fun _ => ik_pure_bind ?_
    unfold refillAddTail
    exact ik_rn_upd (fun _ => rfl) (fun _ _ => by simp [scRefillsUpdate])
  · exact ik_pure _

theorem sb_refillNew (p : ObjRef) (mr : Nat) (budget period : Ticks) :
    SBK h0 (refillNew (Z := Unit) p mr budget period) := by
  refine sbk_of_hk (p := p) fun k => ?_
  unfold refillNew
  refine hk_bind (hk_of_ik (ik_gets _)) fun ct => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine hk_bind (hk_of_ik (ik_pure _)) fun _ => ?_
  exact hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ =>
    hk_of_ik (ik_rn_maybeAddEmptyTail p k)

theorem sb_refillUpdate (p : ObjRef) (np nb : Ticks) (nm : Nat) :
    SBK h0 (refillUpdate (Z := Unit) p np nb nm) := by
  refine sbk_of_hk (p := p) fun k => ?_
  unfold refillUpdate
  refine hk_bind (hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ => hk_of_ik ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (by unfold getScRefillReady; rd_auto) fun _ => ?_
  refine ik_bind ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · refine ik_bind (ik_gets _) fun _ => ?_
      unfold updateRefillHd
      exact ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)
    · exact ik_pure _
  refine ik_bind (by unfold getRefillHead; rd_auto) fun _ => ?_
  split
  · unfold updateRefillHd
    exact ik_bind (ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)) fun _ =>
      ik_rn_maybeAddEmptyTail p k
  · refine ik_pure_bind (ik_pure_bind ?_)
    unfold refillAddTail
    exact ik_rn_upd (fun _ => rfl) (fun _ _ => by simp [scRefillsUpdate])

end

macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_mergeOverlappingRefills _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_mergeNonoverlappingHeadRefill _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_chargeEntireHeadRefill _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillNew _ _ _ _)
macro_rules | `(tactic| sb_leaf) => `(tactic| with_reducible exact sb_refillUpdate _ _ _ _)

end

end Fl4Proofs.P3.SInvB
