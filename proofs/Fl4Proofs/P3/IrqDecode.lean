/-
P3 (DESIGN.md §9), interrupts: **the whole of `decode_irq_handler` and of
`decode_irq_control`**, every label, against l4v's
`decode_irq_handler_invocation` and FL4's `decode_irq_control_invocation`,
then `set_thread_state Restart` and the invocation
(`irq_handler_decode_refines`, `irq_control_decode_refines`). Each label is
its own theorem (Ack, Set, Clear, the other labels; Issue, IOAPIC, MSI,
IOAPIC remapped, the other labels); here they are put together, the
hypotheses of each label taken for that label only. The results are `HPost`
and `CPost`: the CSpace relation, `MdbInv` and `FinInv` after the spec's
outcome, or the spec's error with the state unchanged.
-/
import Fl4Proofs.P3.IrqArch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The spec's IRQ handler label of an FL4 label. -/
def irqHLabelOf (lbl : U64) : Fl4Spec.GenInvocationLabels :=
  if lbl.val = 34 then .irqAckIRQ else if lbl.val = 35 then .irqSetIRQHandler
  else if lbl.val = 36 then .irqClearIRQHandler else .invalidInvocation

/-- The spec's label `slbl` of the IRQ control invocation at FL4 label `lbl`. -/
def IrqCLabel (lbl : U64) (slbl : Fl4Spec.Data) : Prop :=
  (lbl.val = 33 → Fl4Spec.genInvocationType slbl = .irqIssueIRQHandler) ∧
  (lbl.val = 70 → Fl4Spec.invocationType slbl = .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC) ∧
  (lbl.val = 71 → Fl4Spec.invocationType slbl = .archInvocationLabel .x64IRQIssueIRQHandlerMSI) ∧
  (lbl.val ≠ 33 → lbl.val ≠ 70 → lbl.val ≠ 71 → lbl.val ≠ 72 →
    Fl4Spec.genInvocationType slbl ≠ .irqIssueIRQHandler ∧
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC ∧
    Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64IRQIssueIRQHandlerMSI)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`decode_irq_handler`, every label.** -/
theorem irq_handler_decode_refines (th : TypedHeap) (hP : Placed th)
    (hO : FinObjHyp (L := L) arI th) (hPD : PostDelHyp (L := L) arI th) (hK : NtfnKeepHyp (L := L) arI th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = irqHLabelOf lbl)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hok : IrqSlotOK (L.mem s) (nodeA (L.ksb s) irq))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (cps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hex : lbl.val = 35 → ExtraSRel th (L.mem s) x0 cps) (hxn : lbl.val = 35 → x0 ≠ nodeA (L.ksb s) irq) :
    interrupt.decode_irq_handler st arI s ar lbl irq extra ⦃ res =>
      HPost (L := L) th σ G (Fl4Spec.decodeIrqHandlerInvocation slbl (BitVec.ofNat 8 irq.val) cps) s res ⦄ := by
  by_cases h34 : lbl.val = 34
  · have e : lbl = fl4_abi.label.IRQAckIRQ := UScalar.eq_of_val_eq (by rw [h34]; simp [fl4_abi.label.IRQAckIRQ])
    subst e
    exact irq_ack_refines arI th s ar σ G hDS.1 hDS.2.2 hP slbl (by rw [hlbl]; simp [irqHLabelOf, h34]) ct hct hcur
      htcb hact hmask irq extra cps
  by_cases h35 : lbl.val = 35
  · have e : lbl = fl4_abi.label.IRQSetIRQHandler :=
      UScalar.eq_of_val_eq (by rw [h35]; simp [fl4_abi.label.IRQSetIRQHandler])
    subst e
    exact irq_set_refines arI th hP hO hPD hK s ar σ G hDS hL hIR slbl (by rw [hlbl]; simp [irqHLabelOf, h35]) ct hct
      hcur htcb hact irq hirq hok extra x0 hx0 cps (hex h35) (hxn h35)
  by_cases h36 : lbl.val = 36
  · have e : lbl = fl4_abi.label.IRQClearIRQHandler :=
      UScalar.eq_of_val_eq (by rw [h36]; simp [fl4_abi.label.IRQClearIRQHandler])
    subst e
    exact irq_clear_refines arI th hP hO hPD s ar σ G hDS hL hIR slbl (by rw [hlbl]; simp [irqHLabelOf, h36]) ct hct
      hcur htcb hact irq hirq hok extra cps
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; simp [irqHLabelOf, h34, h35, h36]
  exact irq_other_refines arI th s ar σ lbl h34 h35 h36 slbl (by rw [hg]; decide) ct hct irq extra cps

/-- **`decode_irq_control`, every label.** -/
theorem irq_control_decode_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) :
    interrupt.decode_irq_control st arI s ar lbl length (cslotAddr (ps.bv, idxs)) buf extra ⦃ res =>
      CPost (L := L) Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs) excaps)
        s res ⦄ := by
  obtain ⟨l33, l67, l68, lo⟩ := hlbl
  by_cases h33 : lbl.val = 33
  · have e : lbl = fl4_abi.label.IRQIssueIRQHandler :=
      UScalar.eq_of_val_eq (by rw [h33]; simp [fl4_abi.label.IRQIssueIRQHandler])
    subst e
    simp only [h33]
    exact irq_issue_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR slbl (l33 h33) length buf ct hct args hlen hargs
      hcur htcb hact hact2 extra x0 hx0 excaps hex hps hls hsrcC nA hnum hnA hmask
  by_cases h70 : lbl.val = 70
  · have e : lbl = fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC :=
      UScalar.eq_of_val_eq (by rw [h70]; simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC])
    subst e
    simp only [h70]
    exact irq_ioapic_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR slbl (l67 h70) length buf ct hct args hlen hargs
      hcur htcb hact hact2 extra x0 hx0 excaps hex hps hls hsrcC hAR
  by_cases h71 : lbl.val = 71
  · have e : lbl = fl4_abi.label.X86IRQIssueIRQHandlerMSI :=
      UScalar.eq_of_val_eq (by rw [h71]; simp [fl4_abi.label.X86IRQIssueIRQHandlerMSI])
    subst e
    simp only [h71]
    exact irq_msi_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR slbl (l68 h71) length buf ct hct args hlen hargs
      hcur htcb hact hact2 extra x0 hx0 excaps hex hps hls hsrcC hmask
  by_cases h72 : lbl.val = 72
  · have e : lbl = fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped :=
      UScalar.eq_of_val_eq (by rw [h72]; simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped])
    subst e
    simp only [h72]
    exact irq_remap_refines arI th hP s ar σ G hCR hL hIR hHA hFI hFR slbl length buf ct hct args hlen hargs
      hcur htcb hact hact2 extra x0 hx0 excaps hex hps hls hsrcC hAR
  simp only [h72]
  exact irq_ctl_other_refines arI th s ar σ lbl h33 h70 h71 h72 slbl (lo h33 h70 h71 h72) length _ buf extra _ _ _

end

end

end Fl4Proofs.P3
