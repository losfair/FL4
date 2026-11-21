/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, ut5): **every slot a CNode
lookup returns is a `DestRefV` destination** (spec side only; imports
SpecInvUtN5). KENTRY-PLAN ut4 handoff step 1, lookup half.

`resolve_address_bits` returns `(oref, offset)` only after reading the CNode
cap `cnodeCap oref radix guard` (the root, or a cap read from a slot on the
way) with `offset` of length `radix`: that cap is the non-Zombie slot-holding
reference `DestRefV` asks for, provided the root itself sits in a slot (the
invoked cap, an extra cap, or a thread's CSpace root). `okv_resolveN`,
`okv_lookupErrorOnFailure`, **`okv_lookupSlotForCnodeOpN`** (so
`lookup_target_slot` / `lookup_source_slot` / `lookup_pivot_slot`).
-/
import Fl4Proofs.P3.SpecInvUtN5
open Classical

namespace Fl4Proofs.P3.SInvU
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

theorem okv_resolveN {w : UView} (p : Cap × CapRef)
    (hp : ∀ r bits g, p.1 = .cnodeCap r bits g → ∃ s, w.2.1 s = some p.1) :
    OkV w (fun x : CslotPtr × CapRef => DestRefV w x.1) (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · rename_i oref radixBits guard heq
    obtain ⟨s0, hs0⟩ := hp oref radixBits guard heq
    rw [heq] at hs0
    split
    · exact okv_liftE_fail
    · refine okv_whenE_bind fun _ => okv_whenE_bind fun hlen => ?_
      refine okv_returnOk_bind ?_
      dsimp only
      have hD : DestRefV w (oref, (p.2.drop guard.length).take radixBits) := by
        refine ⟨s0, _, hs0, by simp [sRefs], fun _ _ _ e => (by cases e), ?_⟩
        show ((p.2.drop guard.length).take radixBits).length = radixBits
        simp only [List.length_take, List.length_drop]
        omega
      split
      · exact okv_returnOk hD
      · refine okv_liftE_getCap_bind fun nc hnc => ?_
        split
        · exact okv_resolveN _ fun _ _ _ _ => ⟨_, hnc⟩
        · exact okv_returnOk hD
  · exact okv_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega

theorem okv_lookupErrorOnFailure {w : UView} {α : Type} {P : α → Prop} (sr : Bool)
    {m : LFMonad Unit α} (h : OkV w P m) : OkV w P (lookupErrorOnFailure (Z := Unit) sr m) := by
  intro σ hσ a s hs
  unfold lookupErrorOnFailure NonDetE.handleE at hs
  rw [ExceptT.run_mk] at hs
  obtain ⟨z, hz, hs⟩ := hs
  obtain ⟨r, s'⟩ := z
  cases r with
  | ok b =>
    have e := Set.mem_singleton_iff.1 hs
    simp only [Prod.mk.injEq, Except.ok.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact h σ hσ _ _ hz
  | error e =>
    have e' := Set.mem_singleton_iff.1 hs; simp at e'

/-- **A CNode lookup's slot is a `DestRefV` destination** when the root sits in a slot. -/
theorem okv_lookupSlotForCnodeOpN {w : UView} (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat)
    (hroot : ∃ s, w.2.1 s = some croot) :
    OkV w (DestRefV w) (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp
  split
  · refine okv_whenE_bind fun _ => okv_lookupErrorOnFailure _ ?_
    refine okv_returnOk_bind ?_
    refine okv_bind (fun _ => uk_resolveAddressBits _) (okv_resolveN _ fun _ _ _ _ => hroot) fun x hx => ?_
    obtain ⟨slot, rem⟩ := x
    dsimp only
    split
    · exact okv_returnOk hx
    · exact okv_throw _
  · exact okv_throw _

end

end Fl4Proofs.P3.SInvU
