/-
P3 (DESIGN.md §9), CSpace: **an IRQ handler cap's finalisation at `XTop`**
(`XFinHyps.irq`, `xFinIrq_of`): when final, FL4's `deleting_irq_handler`
deletes the cap in the IRQ's node slot (a null or notification cap,
`IrqSlotOK`) with `delete_one` (`delete_one_xtopK`), the spec's
`deleting_irq_handler` the cap at `get_irq_slot` (`IrqRel.node`); the cleanup
is the handler cap.

`XFinHyps.io` (an IO port cap with a VCPU owner: `vcpu::revoke_ports`) is
VT-x work (DESIGN §5), not done here.
-/
import Fl4Proofs.P3.XTopDelOne
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem finWork_irq {i : U64} {b : Bool} (h : FinWork (.IrqHandler i) b) : b = true := by
  unfold FinWork at h
  rcases h with ⟨hb | ⟨f, l, o, e, -⟩, -⟩ | ⟨p, sz, r, d, ep, asid, va, e⟩
  · exact hb
  · cases e
  · cases e

set_option maxHeartbeats 8000000 in
/-- **`XFinHyps.irq` holds**, from the notification's finalisation at `XTop`
(`XFinAt FinNtfnK`, as for `xDelNtfnHyp_of`), the cleanup at `XTop`
(`XPostDelHyp`), the notification's finalisation keeping the slots
(`NtfnKeepHyp` [W]) and, at the `XTopAt` states, the interrupt layout
(`IntLayout` [P]) and the IRQ node's slots holding null or notification caps
(`IrqSlotOK` [J], l4v `valid_irq_node`). -/
theorem xFinIrq_of [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap}
    (hN : ∀ Z : XSets, Z.th = th → XFinAt (L := L) arI FinNtfnK AR Z.th)
    (hXD : XPostDelHyp (L := L) arI AR th) (hKeep : NtfnKeepHyp (L := L) arI th)
    (hLay : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ → IntLayout th (L.ksb s))
    (hOKs : ∀ (Z : XSets) s a σ, Z.th = th → XTopAt (L := L) AR Z s a σ →
      ∀ i : U64, i.val < 128 → IrqSlotOK (L.mem s) (nodeA (L.ksb s) i)) :
    XFinAt (L := L) arI FinIrqK AR th := by
  intro Z s a σ sl c hth hX hK hTh ⟨i, hci⟩ hDS hA hc hk hw
  subst hth hci
  have hL := hLay Z s a σ rfl hX
  obtain ⟨c', ac, hc', hca, -⟩ := hDS.1.1.abs_cap hA
  rw [hc] at hc'; cases eq_of_ok_eq hc'
  have hcw : CapWf (.IrqHandler i) := hca.1
  have hi : i.val < 128 := hcw
  have hfin := finWork_irq hw
  set fin := decide (Fl4Spec.isFinalCap' (absCap (.IrqHandler i)) σ) with hfd
  unfold objects.finalise_cap
  simp only [hfin, ↓reduceIte]
  unfold interrupt.deleting_irq_handler
  rw [irq_slot_eq]; simp only [bind_ok]
  have hA' : AbsSlot Z.th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hL.node i hi)⟩
  set sl' : Fl4Spec.CslotPtr := ((nodeA (L.ksb s) i).bv, []) with hsl'
  have hcs : cslotAddr sl' = nodeA (L.ksb s) i := cslotAddr_nil _
  have hcv := capV_of_capAt hc
  have hnode : σ.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA (L.ksb s) i).bv :=
    hX.fin.1.1.2.2.2.1.node i hi
  have hfo : ∀ (s1 : S) (a1 : A), objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true =
      ok ((.Null, .IrqHandler i), s1, a1) := fun _ _ => rfl
  -- the spec's finalisation from the node slot's deletion
  have hspec : ∀ σ1 : Fl4Spec.State Unit, ((), σ1) ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl' σ).1 →
      ((absCap .Null, absCap (.IrqHandler i)), σ1) ∈
        (Fl4Spec.finaliseCap (Z := Unit) (absCap (.IrqHandler i)) true σ).1 := by
    intro σ1 h1
    show _ ∈ ((if true = true then do
        Fl4Spec.deletingIrqHandler (BitVec.ofNat 8 i.val)
        return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.irqHandlerCap (BitVec.ofNat 8 i.val))
      else return (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) σ).1
    simp only [↓reduceIte]
    refine mem_bind_nd (x := ((), σ1)) ?_ (Set.mem_singleton _)
    unfold Fl4Spec.deletingIrqHandler Fl4Spec.getIrqSlot
    refine mem_bind_nd (x := (sl', σ)) (by
      show (((nodeA (L.ksb s) i).bv, []), σ) = ((σ.interruptIrqNode (BitVec.ofNat 8 i.val), []), σ)
      rw [hnode]) h1
  have hne : cslotAddr sl ≠ nodeA (L.ksb s) i := by
    intro e
    rcases hOKs Z s a σ rfl hX i hi with h | ⟨p, b, w, r, h⟩
    · rw [← e, hcv] at h; cases h
    · rw [← e, hcv] at h; cases h
  rcases hOKs Z s a σ rfl hX i hi with hnull | ⟨p, b, w, r, hn⟩
  · -- a null node slot: nothing to delete
    obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS.1.1.abs_cap hA'
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s a (nodeA (L.ksb s) i) = ok (s, a) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) sl' σ = ({((), σ)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg0]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e1]; simp only [bind_ok]
    show objects.finalise_cap_object st arI s a (.IrqHandler i) true ⦃ r => FinXPost (L := L) AR Z s σ sl (.IrqHandler i) r ⦄
    rw [hfo, WP.spec_ok]; unfold FinXPost
    refine ⟨rfl, trivial, hcw, σ, Z.G, (by rw [← hfd, hfin]; exact hspec σ (by rw [e2]; exact Set.mem_singleton _)), hDS, hcv,
      fun _ _ _ => Or.inl rfl, MdbStep.refl hDS.1.2.2.1, ⟨Z.vs, hX⟩, rfl⟩
  · -- a notification cap: `delete_one`
    have hW : WXZ (L := L) AR Z (L.ksb s) s a σ Z.G := ⟨⟨Z.vs, hX⟩, hK, hTh, rfl⟩
    have hd := delete_one_xtopK arI (hN Z rfl) hXD hKeep s a σ hDS hW hA' (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_bind hd ?_
    rintro ⟨s1, a1⟩ ⟨σ1, G1, hm1, hDS1, hx1, hoth1, hmS1, hX1, -, -, hkb1⟩
    show objects.finalise_cap_object st arI s1 a1 (.IrqHandler i) true ⦃ r => FinXPost (L := L) AR Z s σ sl (.IrqHandler i) r ⦄
    rw [hfo, WP.spec_ok]; unfold FinXPost
    refine ⟨rfl, trivial, hcw, σ1, G1, (by rw [← hfd, hfin]; exact hspec σ1 hm1), hDS1, ?_, fun y hy hyx => ?_, hmS1, hX1, hkb1⟩
    · rw [hoth1 _ hA.isSlot hne]; exact hcv
    · by_cases e : y = nodeA (L.ksb s) i
      · subst e; refine Or.inr ⟨hx1, ?_⟩; rw [hn]; rfl
      · exact Or.inl (hoth1 y hy e)

end

end

end Fl4Proofs.P3
