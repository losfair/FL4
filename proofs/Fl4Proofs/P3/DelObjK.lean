/-
P3 (DESIGN.md §9), CSpace: **`FinWorkHyp` by the kind of cap**
(`finWorkHyp_split`): the notification and reply caps (proved here, from
P1's `fin_cap_ntfn.slots` / `fin_cap_reply.slots` and the spec frames
`finNtfn_nkc` / `finReply_nkc`), the IRQ handler caps (`IrqFinHyp`, left
until the IRQ invariants are in `DState`), and the rest (`FinWorkAt
FinRestK`: endpoints, threads, scheduling contexts, the VSpace caps).

A notification or reply cap's finalisation writes no cap-slot word (P1),
so FL4's slots are unchanged (`SlotsSame`, through `SlotCapW`), and the
spec's keeps every cap (`NKC`), so the CSpace relation carries over and the
step is `MdbStep.of_same`. What is left of the two cases is the coupling of
P3's state to P1's invariant at the cap (`NtfnP1Hyp`, `ReplyP1Hyp`: `BlkOK`
with the cap's object in its set, the slots among P1's `CapW` words) and
that the spec's finalisation has an outcome (`SpecFinOut`).
-/
import Fl4Proofs.P3.DelObj
import Fl4Proofs.P3.SpecCaps
import Fl4Proofs.P3.ScInstFoot
import Fl4Proofs.P3.DomDecode
import Fl4Proofs.P3.TcbCaps
import Fl4Proofs.P1.QueueFinCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical
open Fl4Proofs.P3.Sched (SlotCapW)

noncomputable section

/-- Notification caps. -/
def FinNtfnK (c : capability.Cap) : Prop := ∃ n b0 b1 b2, c = .Notification n b0 b1 b2
/-- Reply caps. -/
def FinReplyK (c : capability.Cap) : Prop := ∃ p x, c = .Reply p x
/-- IRQ handler caps. -/
def FinIrqK (c : capability.Cap) : Prop := ∃ i, c = .IrqHandler i
/-- The other caps. -/
def FinRestK (c : capability.Cap) : Prop := ¬ FinNtfnK c ∧ ¬ FinReplyK c ∧ ¬ FinIrqK c

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`FinWorkHyp` for the caps of kind `K`.** -/
def FinWorkAt (K : capability.Cap → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    K c → DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c → FinObjKind c →
    FinWork c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) →
    objects.finalise_cap st arI s a c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) false ⦃ r =>
      r.1.1 = finRem c (decide (Fl4Spec.isFinalCap' (absCap c) σ)) ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap c) (decide (Fl4Spec.isFinalCap' (absCap c) σ)) σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄

/-- **The IRQ handler case**, a hypothesis until the IRQ invariants
(`IrqSlotOK`, `IntLayout`, `IrqRel`) are in `DState`. -/
abbrev IrqFinHyp (th : TypedHeap) : Prop := FinWorkAt (L := L) arI FinIrqK th

/-- **`FinWorkHyp` from its kinds.** -/
theorem finWorkHyp_split (th : TypedHeap) (hN : FinWorkAt (L := L) arI FinNtfnK th)
    (hR : FinWorkAt (L := L) arI FinReplyK th) (hI : IrqFinHyp (L := L) arI th)
    (hX : FinWorkAt (L := L) arI FinRestK th) : FinWorkHyp (L := L) arI th := by
  intro s a σ G sl c
  by_cases h1 : FinNtfnK c
  · exact hN s a σ G sl c h1
  by_cases h2 : FinReplyK c
  · exact hR s a σ G sl c h2
  by_cases h3 : FinIrqK c
  · exact hI s a σ G sl c h3
  exact hX s a σ G sl c ⟨h1, h2, h3⟩

/-- **The spec's finalisation of a final cap of kind `K` has an outcome**
(with the remainder and no cleanup cap). -/
def SpecFinOut (K : capability.Cap → Prop) (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (c : capability.Cap),
    K c → DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok c →
    Fl4Spec.isFinalCap' (absCap c) σ →
    ∃ σ', ((absCap (finRem c true), absCap .Null), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) true σ).1

/-- **P1's invariant at a notification cap**: `BlkOK`, the notification in
P1's set, the cap slots among P1's `CapW` words. -/
def NtfnP1Hyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (n : U64) (b0 : U64) (b1 b2 : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Notification n b0 b1 b2) →
    ∃ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
      P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotCapW th T Ω Sg ∧ n ∈ Nt ∧ H n = some .ntfn

/-- **P1's invariant at a reply cap**: `BlkOK`, the reply in P1's set, the
cap slots among P1's `CapW` words. -/
def ReplyP1Hyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (p : U64) (x : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Reply p x) →
    ∃ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
      P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ SlotCapW th T Ω Sg ∧ p ∈ Rp

/-- FL4's slots unchanged when no `CapW` word is. -/
theorem slotsSame_of_capw {th : TypedHeap} (hP : Placed th) {T Ω Sg : Set U64} (hSC : SlotCapW th T Ω Sg)
    {s s' : S} (h : ∀ b, P1.Aligned b → P1.CapW T Ω Sg b → L.mem s' b = L.mem s b) :
    SlotsSame th (L.mem s) (L.mem s') := fun a ha => by
  have w : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
    h _ (slot_word_aligned hP ha hk) (hSC _ ⟨a, ha, k, hk, rfl⟩)
  exact ⟨by have := w _ off0; rwa [wordOf_zero] at this, w _ off8, w _ off16, w _ off24⟩

/-- **A finalisation with no slot change on FL4's side and no cap change on
the spec's** gives `FinWorkAt`'s post, with the remainder and cleanup
`.Null` and the ghost tree unchanged. -/
theorem finWork_post_same {th : TypedHeap} {s s' : S} {a' : A} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {sl : Fl4Spec.CslotPtr} {c : capability.Cap} {b : Bool} (hDS : DState (L := L) th s σ G) (hA : AbsSlot th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (hrem : finRem c b = .Null)
    (hS : SlotsSame th (L.mem s) (L.mem s')) (hmem : ((absCap .Null, absCap .Null), σ') ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1) (hK : CKeep σ σ') :
    let r : (capability.Cap × capability.Cap) × S × A := ((.Null, .Null), s', a')
    r.1.1 = finRem c b ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧
      ∃ σ' G', ((absCap r.1.1, absCap r.1.2), σ') ∈ (Fl4Spec.finaliseCap (Z := Unit) (absCap c) b σ).1 ∧
        DState (L := L) th r.2.1 σ' G' ∧ capV (L.mem r.2.1) (cslotAddr sl) = c ∧
        (∀ y, IsSlot th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y ∨
          (capV (L.mem r.2.1) y = .Null ∧ isZb (capV (L.mem s) y) = false)) ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' := by
  intro r
  have hR' : StateRel th (L.mem s') σ' := (hDS.1.1.of_caps (fun x hx => hS.capAt hx)).of_ckeep hK
  obtain ⟨hCR', -⟩ := crel_step hDS.1 hDS.2.2 hS hK.ks hR' hK.cdt hK.orig
  refine ⟨hrem.symm, trivial, trivial, σ', G, hmem, DState.of_same hDS hS hCR' hK.ks, ?_,
    fun y hy _ => Or.inl (hS.capV hy), MdbStep.of_same hDS.1.2.2.1 hS⟩
  show capV (L.mem s') (cslotAddr sl) = c
  rw [hS.capV hA.isSlot]; exact capV_of_capAt hc

/-- **The notification case.** -/
theorem finWorkAt_ntfn (th : TypedHeap) (hP : Placed th) (hP1 : NtfnP1Hyp (L := L) th)
    (hEx : SpecFinOut (L := L) FinNtfnK th) : FinWorkAt (L := L) arI FinNtfnK th := by
  intro s a σ G sl c hk hDS hA hc _ hw
  obtain ⟨n, b0, b1, b2, rfl⟩ := hk
  obtain ⟨T, Cs, Ω, H, Sg, Rp, Scs, Nt, Z, Ac, hB, hSC, hn, hH⟩ := hP1 s σ G sl n b0 b1 b2 hDS hA hc
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Notification n b0 b1 b2)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨n, b0, b1, b2, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_ntfn.slots (ar := arI) s a n b0 b1 b2 true false hB hn hH) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finNtfn_nkc _ _ _ true σ _ hmem)

/-- **The reply case.** -/
theorem finWorkAt_reply (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI) (hP1 : ReplyP1Hyp (L := L) th)
    (hEx : SpecFinOut (L := L) FinReplyK th) : FinWorkAt (L := L) arI FinReplyK th := by
  intro s a σ G sl c hk hDS hA hc _ hw
  obtain ⟨p, x, rfl⟩ := hk
  obtain ⟨T, Cs, Ω, H, Sg, Rp, Scs, Nt, Z, Ac, hB, hSC, hp⟩ := hP1 s σ G sl p x hDS hA hc
  have hfin : decide (Fl4Spec.isFinalCap' (absCap (.Reply p x)) σ) = true := by
    simpa [FinWork, isFrame] using hw
  rw [hfin]
  obtain ⟨σ', hmem⟩ := hEx s σ G sl _ ⟨p, x, rfl⟩ hDS hA hc (of_decide_eq_true hfin)
  refine WP.spec_mono (P1.fin_cap_reply.slots hAT s a p x true false hB hp) ?_
  rintro ⟨⟨r1, r2⟩, s', a'⟩ ⟨e, -, -, hW⟩
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact finWork_post_same (L := L) hDS hA hc rfl (slotsSame_of_capw hP hSC hW) hmem
    (finReply_nkc _ _ true σ _ hmem)

end

end

end Fl4Proofs.P3
