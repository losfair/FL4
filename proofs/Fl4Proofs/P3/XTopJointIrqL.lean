/-
P3 (DESIGN.md §9), interrupts: **the IRQ handler cap at `J` with the
deletion at `WJL`** (`ClearIRQHandler`, `SetIRQHandler`: FL4's `delete_one`
of the IRQ's node slot after the caller's restart), from `LiveJ`, `DbgWF`
and `NullOrig` at the invocation's start (`LiveDN`, the entry fact
`JEntryAt.live`) in place of the ∀-state `LiveJHyp`: a notification cap's
deletion is no primitive step (StepSem), IrqHandler's `IrqSteps` records it.

* `irqDelOKJL`: IrqHandler's `IrqDelOK` at `J`: the caller's restart keeps
  `WJL` (XTopJointWJLRestart's `WJL.restart`), the node slot null or a
  notification cap there (`jIrqSlotHyp`), a null slot's deletion doing
  nothing, a notification cap's by XTopJointWJLFinT's `delete_oneJL`.
* `IrqSteps.jat`: `JAt` after an IRQ handler invocation's run: primitive
  steps by `Steps.jat` (`jStepHyps`); the restart, the deletion of a
  notification cap and the steps after it by `WJL.restart`, `delete_oneJL`
  (its outcome the run's by the spec's determinism,
  `Det.detAt_capDeleteOne_ntfn`) and `Steps.jat` from the `JAtZ` in `WJL`
  after.
* `decode_invocation_irq_handlerJL`: the IRQ handler cap, `JAt` after
  (XTopIrqH's `decode_invocation_irq_handlerXSD` with `IrqSteps.jat`,
  `irqDelOKJL`, XTopJointIrqDel's `irqDelDKJ`).
-/
import Fl4Proofs.P3.XTopJointWJLRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`IrqDelOK` at `J`, the deletion at `WJL`** (module docstring). -/
theorem irqDelOKJL [Fl4Proofs.P1.PlainStore st] {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (irq : U64) (hirq : irq.val < 128) :
    IrqDelOK (L := L) arI Z.th s ar σ Z.G ct irq := by
  intro s2 σ1 hs2 hst hDS1
  have hW := WJL.restart arI J hni hsg hP0 hLv hct s2 σ1 hs2 hst
  have hkb2 : L.ksb s2 = L.ksb s := by obtain ⟨⟨_, _, _, _, _, hk, _⟩, _⟩ := hW; exact hk
  have hok := jIrqSlotHyp (L := L) arI (AR := AR) (th := Z.th) Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G (hW.1.wj arI) irq hirq
  rw [hkb2] at hok
  have hA : AbsSlot Z.th ((nodeA (L.ksb s) irq).bv, []) := ⟨_, rfl, Or.inl (by simpa using J.intL.node irq hirq)⟩
  have hcs : cslotAddr ((nodeA (L.ksb s) irq).bv, []) = nodeA (L.ksb s) irq := cslotAddr_nil _
  rcases hok with hnull | ⟨p, b, w, r, hn⟩
  · obtain ⟨c0, ac0, hc0, hca0, hg0⟩ := hDS1.1.1.abs_cap hA
    rw [hca0.abs] at hg0
    have hcv0 := capV_of_capAt hc0
    rw [hcs] at hcv0
    rw [hcv0] at hnull; subst hnull
    have e1 : cdt.delete_one st arI s2 ar (nodeA (L.ksb s) irq) = ok (s2, ar) := by
      unfold cdt.delete_one
      rw [slot_cap_eq, ← hcs, hc0]
      simp only [bind_ok, cap_is_null_eq, isNullB, ↓reduceIte]
    have e2 : Fl4Spec.capDeleteOne (Z := Unit) ((nodeA (L.ksb s) irq).bv, []) σ1 = ({((), σ1)}, False) := by
      unfold Fl4Spec.capDeleteOne
      rw [nd_bind_one hg0]
      simp [absCap, Fl4Spec.NonDet.unless, Fl4Spec.NonDet.pure]
    rw [e1, WP.spec_ok]
    refine ⟨⟨σ1, Z.G, by rw [e2]; exact Set.mem_singleton _, hDS1, MdbStep.refl hDS1.1.2.2.1⟩, ?_,
      fun _ _ _ => rfl⟩
    rw [← hcs]; exact capV_of_capAt hc0
  · have hd := delete_oneJL arI Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hDS1 hW hA (by rw [hcs]; exact hn)
    rw [hcs] at hd
    refine WP.spec_mono hd ?_
    rintro r ⟨σ', G', h1, h2, h3, h4, h5, -⟩
    exact ⟨⟨σ', G', h1, h2, h5⟩, h3, h4⟩

set_option maxHeartbeats 4000000 in
/-- **`JAt` after an IRQ handler invocation's run** (module docstring). -/
theorem IrqSteps.jat [Fl4Proofs.P1.PlainStore st] (hAM : ARMask arI AR) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hsg : SpecGlob σ) (hP0 : PPR0 σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} (h : IrqSteps (L := L) arI Z.th s ar σ s' a' σ') : JAt (L := L) arI AR s' a' σ' := by
  rcases h with h | ⟨ct, s2, σ1, sl, p, b, w, r, s3, a3, σ3, hct, hs2, hst, -, hA, -, hk, hd, hm, h2⟩
  · exact Steps.jat arI hAM (jStepHyps arI) h rfl J (J.zNoBlk hsg)
  have hW := WJL.restart arI J hni hsg hP0 hLv hct s2 σ1 hs2 hst
  have hDS2 : DState (L := L) Z.th s2 σ1 Z.G := by
    obtain ⟨⟨V, Ac2, Lst2, D2, J2, -⟩, -⟩ := hW
    exact ⟨J2.xtop.rel.2.1, J2.del, J2.xtop.rel.2.2.1⟩
  have hd' := delete_oneJL arI Z H Cs (L.ksb s) rfl s2 ar σ1 Z.G hDS2 hW hA hk
  rw [hd, WP.spec_ok] at hd'
  obtain ⟨σ4, G4, hm4, -, -, -, -, hW4⟩ := hd'
  obtain ⟨c, ac, hc, hca, hg⟩ := hDS2.1.1.abs_cap hA
  rw [hca.abs] at hg
  rw [capV_of_capAt hc] at hk; subst hk
  have e := (Det.detAt_capDeleteOne_ntfn hg).eq hm4 hm
  have e2 : σ4 = σ3 := congrArg Prod.snd e
  subst e2
  obtain ⟨⟨V4, Ac4, Lst4, D4, J4, -, -, hsg4, -⟩, -⟩ := hW4
  exact Steps.jat arI hAM (jStepHyps arI) h2 (Z := Z.mv G4 V4) rfl J4 (J4.zNoBlk hsg4)

set_option maxHeartbeats 4000000 in
/-- **An IRQ handler cap, `JAt` after** (module docstring). -/
theorem decode_invocation_irq_handlerJL [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hsg : SpecGlob σ) (hP0 : PPR0 σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    (hARI : ARIface arI AR) (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (irq : U64) (hsc : capV (L.mem s) (cslotAddr sl) = .IrqHandler irq)
    (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel Z.th (L.mem s) x0 excaps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq)
    (hD : DomPlaced (L := L) Z.th s) (hP1 : IrqDelP1 (L := L) s ct irq)
    (length buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.IrqHandler irq) blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hirq : irq.val < 128 := (slot_cap_wf hX hAs hsc).1
  exact decode_invocation_irq_handlerXSD arI Z.th hX.rel.1 s ar σ Z.G J.dstate J.intL
    hX.fin.1.1.2.2.2.1 lbl slbl hlbl ct hct hcur (hX.curTcb hcur).1 J.kern.act (maskIrq_total arI hT) irq hirq hok
    (irqDelOKJL arI J hni hsg hP0 hLv hct irq hirq) (irqDelDKJ arI (jStepHyps arI) J hni hsg hct irq hirq)
    extra x0 hx0 excaps hex hxn hX.rel.2.2.2.2.1 hD hP1 rfl hX (J.curRun.run hni) _ ⟨Z, H, Cs, Ac, Lst, D, J⟩
    (fun _ _ _ h => IrqSteps.jat arI hARI.toMask J hni hsg hP0 hLv h) (fun _ _ _ h => JAt.xtop arI h)
    length (cslotAddr sl) buf blk call don fp args ci sl buffer

end

end

end Fl4Proofs.P3
