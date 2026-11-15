/-
P3 (DESIGN.md §9), CSpace: **`post_cap_deletion` of an IRQ handler cap**
(`empty_slot`'s cleanup, l4v `deleted_irq_handler`): FL4 writes the IRQ's
state word (in the kernel-state block, outside every object) and masks the
IRQ (an arch operation, assumed total); the spec sets the IRQ's state and
masks it. Neither touches a cap slot, so the CSpace relations are kept.
IO port cleanup caps stay a hypothesis (`PostIoHyp`); with it,
`PostDelHyp` holds.
-/
import Fl4Proofs.P3.DelCnode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

theorem setIrqState_mem {Z : Type} (sti : IrqState) (irq : Irq) (σ : State Z) :
    ∃ σ', ((), σ') ∈ (setIrqState (Z := Z) sti irq σ).1 ∧ σ'.kheap = σ.kheap ∧ σ'.cdt = σ.cdt ∧
      σ'.isOriginalCap = σ.isOriginalCap := by
  let σ1 : State Z := { σ with interruptStates := Function.update σ.interruptStates irq sti }
  let ms' : MachineState := { σ1.machineState with
    irqMasks := Function.update σ1.machineState.irqMasks irq (decide (sti = .irqInactive)) }
  refine ⟨{ σ1 with machineState := ms' }, ?_, rfl, rfl, rfl⟩
  unfold setIrqState doMachineOp maskInterrupt
  refine mem_bind_nd (x := ((), σ1)) rfl ?_
  refine mem_bind_nd (x := (σ1.machineState, σ1)) rfl ?_
  refine mem_bind_nd (x := (((), ms'), σ1)) ⟨rfl, rfl⟩ ?_
  refine mem_bind_nd (x := ((), { σ1 with machineState := ms' })) (Set.mem_singleton _) ?_
  rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The IO port cleanup (a hypothesis): as `PostDelHyp`, for IO port caps. -/
def PostIoHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (f l owner : U64),
    DState (L := L) th s σ G → CapWf (.IoPort f l owner) →
    objects.post_cap_deletion st arI s a (.IoPort f l owner) ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.1) ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap (.IoPort f l owner)) σ).1 ∧ CRel th (L.mem r.1) σ' G ⦄

theorem crel_same {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (h : CRel th m σ G) (hS : SlotsSame th m m') (hk : σ'.kheap = σ.kheap) (hc : σ'.cdt = σ.cdt)
    (hio : σ'.isOriginalCap = σ.isOriginalCap) : CRel th m' σ' G := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := h
  have hcap : ∀ x, IsSlot th x → capAt m' x = capAt m x := fun x hx => hS.capAt hx
  exact ⟨(StateRel.of_kheap hR hk).of_caps hcap, hV.of_caps hcap, hM.of_same hS, hC.of_same hS hc hio,
    MdbInv.of_same hM hI hS⟩

/-- **`post_cap_deletion` of an IRQ handler cap.** -/
theorem post_irq (th : TypedHeap) (hP : Placed th)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hout : ∀ (s : S) (irq : U64), interrupt.state_off irq ⦃ off =>
      OutsideObjects th (core.num.U64.wrapping_add (L.ksb s) off) ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hCR : CRel th (L.mem s) σ G) (irq : U64) :
    objects.post_cap_deletion st arI s a (.IrqHandler irq) ⦃ r =>
      SlotsSame th (L.mem s) (L.mem r.1) ∧ ∃ σ',
        ((), σ') ∈ (Fl4Spec.postCapDeletion (Z := Unit) (absCap (.IrqHandler irq)) σ).1 ∧
        CRel th (L.mem r.1) σ' G ⦄ := by
  unfold objects.post_cap_deletion interrupt.deleted_irq_handler interrupt.set_irq_state
  simp only
  apply WP.spec_bind (hout s irq)
  intro off ho
  unfold obj.ks_set
  rw [L.ks_base_eq]
  simp only [bind_ok, lift, L.write_eq]
  obtain ⟨a', ha'⟩ := hmask a irq (decide True)
  rw [ha']
  simp only [bind_ok, WP.spec_ok]
  have hS : SlotsSame th (L.mem s) (L.mem (L.wr s (core.num.U64.wrapping_add (L.ksb s) off) interrupt.IRQ_INACTIVE)) := by
    refine slotsSame_wr hP s _ ho.1 (fun x hx => ?_)
    obtain ⟨p, k, hk, h1, h2, -⟩ := slot_in_object hP hx
    have := ho.2 p k hk
    omega
  obtain ⟨σ', hσ', hk, hc, hio⟩ := setIrqState_mem (Z := Unit) .irqInactive (BitVec.ofNat 8 irq.val) σ
  exact ⟨hS, σ', hσ', crel_same hCR hS hk hc hio⟩

/-- **`PostDelHyp` holds**, from the IRQ handler case and `PostIoHyp`. -/
theorem postDelHyp_of (th : TypedHeap) (hP : Placed th)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hout : ∀ (s : S) (irq : U64), interrupt.state_off irq ⦃ off =>
      OutsideObjects th (core.num.U64.wrapping_add (L.ksb s) off) ⦄)
    (hio : PostIoHyp (L := L) arI th) : PostDelHyp (L := L) arI th := by
  intro s a σ G cl hDS hcl hcln hclw
  cases cl <;> simp only [CleanCap] at hcl
  · exact absurd rfl hcln
  · exact post_irq arI th hP hmask hout s a σ G hDS.1 _
  · exact hio s a σ G _ _ _ hDS hclw

end

end

end Fl4Proofs.P3
