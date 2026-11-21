/-
P3 (DESIGN.md §9), untyped: **the IPC-buffer ghost `B` across the frame
retype** (handoff/glob.md gl13-gl15): the retype of RAM frames (types 9, 10,
11) creates spec data pages, so `JAtZ.fcov` (every word of every non-device
data page a pair `(a, a)` of `B`) asks `B` grown by the new pages' words.

* `XTopAt.chgB`: `XTopAt` at a new `B'` whose pairs are old ones or new words
  `(a, a)` (`Wn a`): 8-aligned, FL4's word equal to the spec's (both zero at
  a retype: FL4 zeroes the window, `UtCapP3.zero`; the spec's free part is
  zero by `JEntryAt.urz`), apart from the TCBs, endpoints and replies, off the
  kernel-state block, and none of their bytes an `OObj` or `VObj` word; `B'`
  injective (`EPlaced.binj`).
* `EPlaced.chgB`, `IPlaced.chgB`, `KsApart.chgB`: the placements at `B'`.
-/
import Fl4Proofs.P3.UtEpXTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section ChgB
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {N T C E R : Set U64} {B B' : Set (U64 × Fl4Spec.Word)} {c : U64}
variable {σ : Fl4Spec.State Unit} {Wn : U64 → Prop}

/-- `B'`'s pairs: old ones or new words `(a, a)`. -/
def BNew (B B' : Set (U64 × Fl4Spec.Word)) (Wn : U64 → Prop) : Prop :=
  ∀ wp ∈ B', wp ∈ B ∨ (Wn wp.1 ∧ wp.2 = wp.1.bv)

theorem oobj_chgB (hB : BNew B B' Wn) {s : S} {b : U64} (h : OObj st N T C E R B' c s σ b) :
    OObj st N T C E R B c s σ b ∨ ∃ a, Wn a ∧ a.val ≤ b.val ∧ b.val < a.val + 8 := by
  unfold OObj at h
  rcases h with h | h | h | h | h | h | h | ⟨wp, hw, h1, h2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, h1, h2⟩)))))))
    · exact Or.inr ⟨wp.1, hn, h1, h2⟩

theorem efoot_chgB (hB : BNew B B' Wn) {b : U64} (h : EFoot T E R B' b) :
    EFoot T E R B b ∨ Wn b := by
  rcases h with h | h | h | ⟨wp, hw, rfl⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)))
    · exact Or.inr hn

theorem ewrite_chgB (hB : BNew B B' Wn) {b : U64} (h : EWrite T E R B' b) :
    EWrite T E R B b ∨ Wn b := by
  rcases h with h | h | h | ⟨wp, hw, rfl⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)))
    · exact Or.inr hn

theorem iwords_chgB (hB : BNew B B' Wn) {b : U64} (h : IWords N T E R B' b) :
    IWords N T E R B b ∨ ∃ a, Wn a ∧ a.val ≤ b.val ∧ b.val < a.val + 8 := by
  rcases h with h | h | h | h | ⟨wp, hw, h1, h2⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, h1, h2⟩))))
    · exact Or.inr ⟨wp.1, hn, h1, h2⟩

/-- **`EPlaced` at `B'`.** -/
theorem Endp.EPlaced.chgB (h : EPlaced T E R B) (hB : BNew B B' Wn)
    (hinj : ∀ wp ∈ B', ∀ wq ∈ B', (wp.1 = wq.1 ↔ wp.2 = wq.2))
    (hal : ∀ a, Wn a → a.val % 8 = 0)
    (hT : ∀ a, Wn a → ∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val)
    (hE : ∀ a, Wn a → ∀ e ∈ E, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val)
    (hR : ∀ a, Wn a → ∀ r ∈ R, a.val + 8 ≤ r.val ∨ r.val + 32 ≤ a.val) : EPlaced T E R B' := by
  refine ⟨h.tcb, h.ep, h.rep, h.et, h.rt, h.er, fun wp hw => ?_, fun wp hw t ht => ?_, fun wp hw e he => ?_,
    fun wp hw r hr => ?_, hinj⟩
  · rcases hB wp hw with hw | ⟨hn, e2⟩
    · exact h.balign wp hw
    · refine ⟨hal _ hn, ?_⟩
      rw [e2]; simp only [UScalar.bv_toNat]; exact hal _ hn
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact h.bt wp hw t ht
    · exact hT _ hn t ht
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact h.be wp hw e he
    · have := hE _ hn e he; omega
  · rcases hB wp hw with hw | ⟨hn, -⟩
    · exact h.br wp hw r hr
    · have := hR _ hn r hr; omega

/-- **`IPlaced` at `B'`.** -/
theorem Ipc.IPlaced.chgB (h : IPlaced N T E R B) (hB : BNew B B' Wn) (hEP : EPlaced T E R B')
    (hN : ∀ a, Wn a → ∀ n ∈ N, a.val + 8 ≤ n.val ∨ n.val + 64 ≤ a.val) : IPlaced N T E R B' :=
  ⟨h.n, hEP, h.ne, h.nr, fun n hn wp hw => by
    rcases hB wp hw with hw | ⟨ha, -⟩
    · exact h.nb n hn wp hw
    · have := hN _ ha n hn; omega⟩

/-- **`KsApart` at `B'`.** -/
theorem KsApart.chgB {kb : U64} (h : KsApart N T E R B kb) (hB : BNew B B' Wn)
    (hks : ∀ a, Wn a → a.val + 8 ≤ kb.val ∨ kb.val + 13568 ≤ a.val) : KsApart N T E R B' kb :=
  ⟨h.ep, h.rep, h.ntfn, fun wp hw => by
    rcases hB wp hw with hw | ⟨ha, -⟩
    · exact h.buf wp hw
    · exact hks _ ha⟩

set_option maxHeartbeats 1000000 in
/-- **`XTopAt` at a `B'` of old pairs and new words** (module docstring). -/
theorem XTopAt.chgB {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    (hX : XTopAt (L := L) AR Z s a σ) (hB : BNew Z.B B' Wn)
    (hinj : ∀ wp ∈ B', ∀ wq ∈ B', (wp.1 = wq.1 ↔ wp.2 = wq.2))
    (hal : ∀ a, Wn a → a.val % 8 = 0)
    (hmem : ∀ a, Wn a → (L.mem s a).bv = Endp.loadWordAt σ.machineState.underlyingMemory a.bv)
    (hT : ∀ a, Wn a → ∀ t ∈ Z.T, a.val < t.val ∨ t.val + 4096 ≤ a.val)
    (hE : ∀ a, Wn a → ∀ e ∈ Z.E, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val)
    (hR : ∀ a, Wn a → ∀ r ∈ Z.R, a.val + 8 ≤ r.val ∨ r.val + 32 ≤ a.val)
    (hks : ∀ a, Wn a → a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val)
    (hfr : ∀ a, Wn a → ∀ b : U64, a.val ≤ b.val → b.val < a.val + 8 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b) :
    XTopAt (L := L) AR { Z with B := B' } s a σ := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩, hV, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, hD, hMO, hIA, hSA⟩,
    -, hEs⟩ := hX
  have hEp' : Endp.EpStateRel Z.T Z.E Z.R B' (L.mem s) σ := by
    refine ⟨hEp.ep, hEp.reply, hEp.tcb, fun wp hw => ?_⟩
    rcases hB wp hw with hw | ⟨hn, e2⟩
    · exact hEp.buf wp hw
    · rw [e2]; exact hmem _ hn
  have hEP' : EPlaced Z.T Z.E Z.R B' := hP.ep.chgB hB hinj hal hT hE hR
  -- a new word's bytes are no node word
  have hnodeE : ∀ b : U64, L.nodeBase s Z.c ≤ b.val → b.val < L.nodeBase s Z.c + 4288 →
      ¬ Endp.EFoot Z.T Z.E Z.R B' b := by
    intro b h1 h2 hf
    rcases efoot_chgB hB hf with hf | hn
    · exact hP.nodeE b h1 h2 hf
    · exact (hfr b hn b le_rfl (by omega)).1 (Or.inl ⟨h1, h2⟩)
  have hP' : TopPlaced st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R B' Z.c s σ := by
    refine { hP with ep := hEP', disj := fun b hb => ?_, nodeE := hnodeE }
    rcases oobj_chgB hB hb with hb | ⟨a0, hn, g1, g2⟩
    · exact hP.disj b hb
    · exact (hfr a0 hn b g1 g2).2
  have hIA' : IpcApart Z.th Z.N Z.T Z.E Z.R B' (L.ksb s) Z.c := by
    refine { hIA with slot := fun b hb x hx hin => ?_, dom := fun b hb => ?_ }
    · rcases iwords_chgB hB hb with hb | ⟨a0, hn, g1, g2⟩
      · exact hIA.slot b hb x hx hin
      · exact (hfr a0 hn b g1 g2).2 (Vs.vobj_of_slot hPl _ _ _ _ _ _ hx hin.1 hin.2)
    · rcases iwords_chgB hB hb with hb | ⟨a0, hn, g1, g2⟩
      · exact hIA.dom b hb
      · have := hks a0 hn; omega
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hE' : EpSchedApart st Z.T Z.C Z.E Z.R B' Z.c s σ := by
    refine ⟨hnodeE, fun hw => ?_, fun hw => ?_, fun sc hsc x n hx b hb hw => ?_⟩
    · rcases ewrite_chgB hB hw with hw | hn
      · exact hEs.dom hw
      · have := hks _ hn; rw [Sched.curDomA_val hc.node] at this; omega
    · rcases ewrite_chgB hB hw with hw | hn
      · exact hEs.dt hw
      · have := hks _ hn; rw [Sched.dtA_val hc.node] at this; omega
    · rcases ewrite_chgB hB hw with hw | hn
      · exact hEs.sc sc hsc x n hx b hb hw
      · exact (hfr b hn b le_rfl (by omega)).1
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hx, hb⟩)))))))
  exact ⟨⟨⟨⟨hSch, hEp', hNt, hIrq, hIo, hKr, hAr⟩, hP'⟩, hV, hPt, hPI, hCO⟩,
    ⟨hPl, hCR, hFI, hD, hMO, hIA', hSA⟩, IpcRel.of hNt hEp' (sched_sc hSch), hE'⟩

end ChgB

end

end Fl4Proofs.P3
