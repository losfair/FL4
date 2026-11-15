/-
P3 (DESIGN.md §9), interrupts: **IRQControl, the x86 labels**
(`X86IRQIssueIRQHandlerMSI`, `X86IRQIssueIRQHandlerIOAPIC`, and l4h's
`X86IRQIssueIRQHandlerIOAPICRemapped`): decode and invoke, against l4v's
`arch_decode_irq_control_invocation` and `arch_invoke_irq_control` (and
FL4's remapped copy, Fl4Spec/Ext/IrqControl.lean).

The arch state FL4 does not keep (l4v `x64_irq_state`, the MSI/IOAPIC
routing of each IRQ) is only on the spec side; the IOAPIC programming is the
spec's machine operation and FL4's arch operation (`ioapic_map`, assumed
total). FL4's `num_ioapics` and `ioapic_pins` are the spec's
`x64_num_ioapics` and `x64_ioapic_nirqs` (each IOAPIC has a pin).
-/
import Fl4Proofs.P3.IrqIssue
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- A machine operation through `machine_op_lift` has an outcome, changing
only the machine state. -/
theorem doMachineOp_lift_ex (f : MachineRestMonad Unit) (σ : State Unit) :
    ∃ ms', ((), { σ with machineState := ms' }) ∈ (doMachineOp (Z := Unit) (machineOpLift f) σ).1 := by
  unfold doMachineOp machineOpLift machineRestLift ignoreFailure
  by_cases h : (f σ.machineState.machineStateRest).1 = ∅
  · let ms' : MachineState := { σ.machineState with machineStateRest := σ.machineState.machineStateRest }
    refine ⟨ms', ?_⟩
    refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
    refine mem_bind_nd (x := (((), ms'), σ)) ⟨?_, rfl⟩ ?_
    · show ((), ms') ∈ ((NonDet.bind (NonDet.gets MachineState.machineStateRest) _) σ.machineState).1
      refine mem_bind_nd (x := (σ.machineState.machineStateRest, σ.machineState)) rfl ?_
      refine mem_bind_nd (x := (((), σ.machineState.machineStateRest), σ.machineState)) ⟨?_, rfl⟩ ?_
      · simp only [h, ↓reduceIte]; rfl
      · refine mem_bind_nd (x := ((), ms')) rfl ?_; rfl
    · refine mem_bind_nd (x := ((), { σ with machineState := ms' })) (Set.mem_singleton _) ?_; rfl
  · obtain ⟨⟨u, mr'⟩, hx⟩ := Set.nonempty_iff_ne_empty.2 h
    let ms' : MachineState := { σ.machineState with machineStateRest := mr' }
    refine ⟨ms', ?_⟩
    refine mem_bind_nd (x := (σ.machineState, σ)) rfl ?_
    refine mem_bind_nd (x := (((), ms'), σ)) ⟨?_, rfl⟩ ?_
    · show ((), ms') ∈ ((NonDet.bind (NonDet.gets MachineState.machineStateRest) _) σ.machineState).1
      refine mem_bind_nd (x := (σ.machineState.machineStateRest, σ.machineState)) rfl ?_
      refine mem_bind_nd (x := (((), mr'), σ.machineState)) ⟨?_, rfl⟩ ?_
      · simp only [h, ↓reduceIte]; exact hx
      · refine mem_bind_nd (x := ((), ms')) rfl ?_; rfl
    · refine mem_bind_nd (x := ((), { σ with machineState := ms' })) (Set.mem_singleton _) ?_; rfl

theorem updateIrqState_mem (irq : Irq) (x : X64IRQState) (σ : State Unit) :
    ((), { σ with archState := { σ.archState with x64IrqState := Function.update σ.archState.x64IrqState irq x } })
      ∈ (updateIrqState (Z := Unit) irq x σ).1 := by
  unfold updateIrqState
  exact mem_bind_nd (x := (σ.archState.x64IrqState, σ)) rfl rfl

theorem invocationType_gen {slbl : Data} {l : ArchInvocationLabel}
    (h : invocationType slbl = .archInvocationLabel l) : genInvocationType slbl = .invalidInvocation := by
  unfold genInvocationType; rw [h]

end

theorem the_some {α : Type} [Nonempty α] (x : α) : Fl4Spec.the (some x) = x := rfl

theorem user_max_eq : layout.irq.USER_MAX = ok 123#u64 := by
  obtain ⟨v, hv, rfl⟩ := spec_exists P0.Consts.layout.irq.USER_MAX.spec; exact hv

theorem user_min_eq : layout.irq.USER_MIN = 16#u64 := by unfold layout.irq.USER_MIN; rfl

theorem irqv_eq (y : U64) (hy : y.val ≤ 107) :
    (Fl4Spec.ucast 8 y.bv + Fl4Spec.minUserIRQ : BitVec 8) = BitVec.ofNat 8 (y.val + 16) := by
  apply BitVec.eq_of_toNat_eq
  simp [Fl4Spec.ucast, Fl4Spec.minUserIRQ, BitVec.toNat_add]
  try omega

theorem maxmin_eq : (Fl4Spec.ucast 64 (Fl4Spec.maxUserIRQ - Fl4Spec.minUserIRQ) : BitVec 64) = BitVec.ofNat 64 107 := by
  decide

@[simp] theorem lbl_msi_val : fl4_abi.label.X86IRQIssueIRQHandlerMSI.val = 71 := by
  simp [fl4_abi.label.X86IRQIssueIRQHandlerMSI]
@[simp] theorem lbl_ioapic_val : fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC.val = 70 := by
  simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC]
@[simp] theorem lbl_remap_val : fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped.val = 72 := by
  simp [fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- After `set_thread_state Restart` (`restart_irq`) and spec steps outside
the CSpace and the interrupt state: `invoke_irq_control`. -/
theorem ctl_finish (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hHA : HandlersActive (L.mem s) (L.ksb s) G)
    (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (irq : U64) (hirq : irq.val < 128) (hin : L.mem s (irqStA (L.ksb s) irq) = 0#u64)
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (dsl : Fl4Spec.CslotPtr) (pd : U64) (hpd1 : dsl.1 = pd.bv) (hpd : th pd = some (.cnode dsl.2.length))
    (hdst : capAt (L.mem s) (cslotAddr dsl) = ok .Null)
    (s1 : S) (σ1 : Fl4Spec.State Unit) (hkb : L.ksb s1 = L.ksb s) (hS : SlotsSame th (L.mem s) (L.mem s1))
    (hCR1 : CRel th (L.mem s1) σ1 G) (hIR1 : IrqRel (L.mem s1) (L.ksb s) σ1)
    (hw : ∀ i : U64, i.val < 128 → L.mem s1 (irqStA (L.ksb s) i) = L.mem s (irqStA (L.ksb s) i))
    (hK1 : KSub σ σ1) (a1 : A) (σ1' : Fl4Spec.State Unit) (hk : σ1'.kheap = σ1.kheap) (hc : σ1'.cdt = σ1.cdt)
    (ho : σ1'.isOriginalCap = σ1.isOriginalCap) (hs : σ1'.interruptStates = σ1.interruptStates)
    (hn : σ1'.interruptIrqNode = σ1.interruptIrqNode) :
    interrupt.invoke_irq_control st arI s1 a1 irq (cslotAddr dsl) (cslotAddr (ps.bv, idxs)) ⦃ r =>
      ∃ σ' G', ((), σ') ∈ ((Fl4Spec.setIrqState (Z := Unit) .irqSignal (BitVec.ofNat 8 irq.val) >>= fun _ =>
          Fl4Spec.capInsert (Z := Unit) (.irqHandlerCap (BitVec.ofNat 8 irq.val)) (ps.bv, idxs) dsl) σ1').1 ∧
        CRel th (L.mem r.1) σ' G' ∧ IrqRel (L.mem r.1) (L.ksb s) σ' ∧
        FinInv th (L.mem r.1) σ' G' ∧ HandlersActive (L.mem r.1) (L.ksb s) G' ∧ MdbOKV (L.ksb s) (L.mem r.1) G' ⦄ := by
  obtain ⟨da, db⟩ := dsl
  simp only at hpd1 hpd; subst hpd1
  obtain ⟨hCR1', hIR1'⟩ := crel_irq_of hCR1 hIR1 hk hc ho hs hn
  have hL1 : IntLayout th (L.ksb s1) := by rw [hkb]; exact hL
  have hIR2 : IrqRel (L.mem s1) (L.ksb s1) σ1' := by rw [hkb]; exact hIR1'
  have hHA1 : HandlersActive (L.mem s1) (L.ksb s1) G := by
    intro y hy i hi
    rw [hS.capV ((hCR.2.2.1.members y).1 hy).1] at hi
    obtain ⟨h1, h2⟩ := hHA y hy i hi
    rw [hkb, hw i h1]; exact ⟨h1, h2⟩
  have hin1 : L.mem s1 (irqStA (L.ksb s1) irq) = 0#u64 := by rw [hkb, hw irq hirq, hin]
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot th (pd.bv, db) := ⟨pd, rfl, Or.inl hpd⟩
  have hsrc1 : capAt (L.mem s1) (cslotAddr (ps.bv, idxs)) = ok .IrqControl := by rw [hS.capAt hAs.isSlot, hsrcC]
  have hdst1 : capAt (L.mem s1) (cslotAddr (pd.bv, db)) = ok .Null := by rw [hS.capAt hAd.isSlot, hdst]
  have hFI1 : FinInv th (L.mem s1) σ1' G := hFI.of_same hCR.2.2.1 hS (hK1.trans (KSub.of_kheap hk))
  have hFR1 : MdbOKV (L.ksb s1) (L.mem s1) G := by rw [hkb]; exact MdbOKV.of_same hCR.2.2.1 hS hFR
  refine WP.spec_mono (invoke_ctl_rel arI th hP s1 a1 σ1' G hCR1' hL1 hIR2 hHA1 hFI1 hFR1 hmask irq hirq hin1 hps hpd
    hls rfl hsrc1 hdst1) ?_
  rintro ⟨s2, a2⟩ ⟨σ', G', hmem, hCR', hIR', -, hFI', hHA', hFR'⟩
  exact ⟨σ', G', hmem, hCR', by rw [← hkb]; exact hIR', hFI', by rw [← hkb]; exact hHA', by rw [← hkb]; exact hFR'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem sub_107 : (123#u64 - 16#u64 : Result U64) = ok 107#u64 := by
  obtain ⟨v, hv, hvv⟩ := spec_exists (U64.sub_spec (x := 123#u64) (y := 16#u64) (by decide))
  rw [hv]; congr 1; apply UScalar.eq_of_val_eq; rw [hvv.1]; rfl

/-- **`X86IRQIssueIRQHandlerMSI`** (label 71). -/
theorem irq_msi_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64IRQIssueIRQHandlerMSI)
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
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a') :
    interrupt.decode_irq_control st arI s ar fl4_abi.label.X86IRQIssueIRQHandlerMSI length
      (cslotAddr (ps.bv, idxs)) buf extra ⦃ res =>
      CPost (L := L) Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl false slbl (args.map UScalar.bv) (ps.bv, idxs) excaps) s res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold interrupt.decode_irq_control
  have n1 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerMSI = fl4_abi.label.IRQIssueIRQHandler := by
    rw [u64_eq_iff]; simp
  have n2 : (fl4_abi.label.X86IRQIssueIRQHandlerMSI != fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC) = true := by
    rw [bne_iff_ne, ne_eq, u64_eq_iff]; simp
  have n3 : ¬ ((fl4_abi.label.X86IRQIssueIRQHandlerMSI != fl4_abi.label.X86IRQIssueIRQHandlerMSI) = true) := by
    simp
  have n4 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerMSI = fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped := by
    rw [u64_eq_iff]; simp
  rw [if_neg n1, if_pos n2, if_neg n3]
  simp only [n4, ↓reduceIte, bind_ok]
  unfold interrupt.extra0; rw [hx0]; simp only [bind_ok, is_null_eq]
  -- the spec's decode
  unfold Fl4Spec.decodeFl4IrqControl
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine CPost.liftME' ?_
  unfold Fl4Spec.decodeIrqControlInvocationWith
  rw [if_neg (show ¬ Fl4Spec.genInvocationType slbl = .irqIssueIRQHandler by rw [invocationType_gen hlbl]; decide)]
  refine CPost.liftME' ?_
  unfold Fl4Spec.archDecodeIrqControlInvocation
  rw [if_neg (show ¬ Fl4Spec.invocationType slbl = .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC by
    rw [hlbl]; decide), if_pos hlbl]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 7 ∧ ([] : List Fl4Spec.Cap).length ≥ 1) by simp)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  by_cases h7 : length >= 7#u64
  swap
  · rw [if_neg h7]; simp only [error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 7 ∧ (ac0 :: erest).length ≥ 1) by simp; scalar_tac)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  rw [if_pos h7]
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, rest, rfl⟩ :
      ∃ y0 y1 y2 y3 y4 y5 y6 rest, args = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest := by
    match args with
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] =>
      exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest => exact ⟨y0, y1, y2, y3, y4, y5, y6, rest, rfl⟩
  rw [if_pos (show ((y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest).map UScalar.bv).length ≥ 7 ∧
    (ac0 :: erest).length ≥ 1 by simp)]
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 6#u64 y6 (by simp), bind_ok,
    user_max_eq, user_min_eq, sub_107]
  have hmap : List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest) =
      y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv := rfl
  rw [hmap]
  have g2 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[2]? = some y2.bv := rfl
  have g3 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[3]? = some y3.bv := rfl
  have g4 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[4]? = some y4.bv := rfl
  have g6 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[6]? = some y6.bv := rfl
  have g0 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  have g1 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[1]? = some y1.bv := rfl
  have g5 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[5]? = some y5.bv := rfl
  have ge : (ac0 :: erest)[0]? = some ac0 := rfl
  rw [g0, g1, g2, g3, g4, g5, g6, ge]
  repeat rw [the_some]
  rw [maxmin_eq]
  by_cases hr : y6 > 107#u64
  · rw [if_pos hr]; simp only [error.range, bind_ok]
    rw [whenE_pos ((bv_gt_iff y6 107 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 (BitVec.ofNat 64 107))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 (BitVec.ofNat 64 107)) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hr]
  have hy6 : y6.val ≤ 107 := by scalar_tac
  rw [whenE_neg (fun h => by have := (bv_gt_iff y6 107 (by norm_num)).1 h; omega)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IRQ
  obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := y6) (y := 16#u64) (by scalar_tac))
  rw [hz]; simp only [bind_ok]
  rw [irqv_eq y6 hy6, show y6.val + 16 = z.val by rw [hzv]; rfl]
  have hz128 : z.val < 128 := by rw [hzv]; simp; omega
  rw [is_irq_active_eq]; simp only [bind_ok]
  refine CPost.congr (run_bind_ok (run_liftE (isIrqActive_run hIR hz128)) _) ?_
  by_cases hact0 : L.mem s (irqStA (L.ksb s) z) = 0#u64
  swap
  · simp only [hact0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    rw [whenE_pos (by simpa using hact0)]
    exact CPost.err (e' := .revokeFirst)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.revokeFirst :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  simp only [hact0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [whenE_neg (by simp [hact0])]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  refine target_tail _ th (L.ksb s) s ar σ hR hV c0 ac0 hca0 hcv0 y0 y1 _ _ ?_
  intro dsl pd hpd1 hpd hdst
  try rw [if_pos rfl]
  unfold interrupt.check_msi
  simp only [hct, hargs 2#u64 y2 (by simp), hargs 3#u64 y3 (by simp), hargs 4#u64 y4 (by simp), bind_ok]
  have hB : interrupt.PCI_BUS_MAX = 255#u64 := by unfold interrupt.PCI_BUS_MAX; rfl
  have hD : interrupt.PCI_DEV_MAX = 31#u64 := by unfold interrupt.PCI_DEV_MAX; rfl
  have hF : interrupt.PCI_FUNC_MAX = 7#u64 := by unfold interrupt.PCI_FUNC_MAX; rfl
  have mB : Fl4Spec.maxPCIBus = BitVec.ofNat 64 255 := rfl
  have mD : Fl4Spec.maxPCIDev = BitVec.ofNat 64 31 := rfl
  have mF : Fl4Spec.maxPCIFunc = BitVec.ofNat 64 7 := rfl
  rw [hB, hD, hF]
  by_cases e2 : y2 > 255#u64
  · rw [if_pos e2]
    simp only [error.range, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok, uncurry_apply_pair]
    rw [whenE_pos (by rw [mB]; exact (bv_gt_iff y2 255 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 Fl4Spec.maxPCIBus)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 Fl4Spec.maxPCIBus) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg e2, whenE_neg (by rw [mB]; exact fun h => by have := (bv_gt_iff y2 255 (by norm_num)).1 h; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  by_cases e3 : y3 > 31#u64
  · rw [if_pos e3]
    simp only [error.range, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok, uncurry_apply_pair]
    rw [whenE_pos (by rw [mD]; exact (bv_gt_iff y3 31 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 Fl4Spec.maxPCIDev)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 Fl4Spec.maxPCIDev) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg e3, whenE_neg (by rw [mD]; exact fun h => by have := (bv_gt_iff y3 31 (by norm_num)).1 h; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  by_cases e4 : y4 > 7#u64
  · rw [if_pos e4]
    simp only [error.range, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok, uncurry_apply_pair]
    rw [whenE_pos (by rw [mF]; exact (bv_gt_iff y4 7 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 Fl4Spec.maxPCIFunc)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 Fl4Spec.maxPCIFunc) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg e4, whenE_neg (by rw [mF]; exact fun h => by have := (bv_gt_iff y4 7 (by norm_num)).1 h; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- `set_thread_state Restart`, then `invoke_irq_control`
  simp only [Std.bind_assoc, bind_ok]
  refine WP.spec_bind (restart_irq th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hIR ct hcur htcb hact hact2) ?_
  rintro s1 ⟨hkb, hS, σ1, hst, hCR1, hIR1, -, -, hw⟩
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  let irqSt : Fl4Spec.X64IRQState := .irqMSI (y2.bv &&& Fl4Spec.mask 8) (y3.bv &&& Fl4Spec.mask 5)
    (y4.bv &&& Fl4Spec.mask 3) (y5.bv &&& Fl4Spec.mask 32)
  let σb : Fl4Spec.State Unit := { σ1 with archState := { σ1.archState with
    x64IrqState := Function.update σ1.archState.x64IrqState (BitVec.ofNat 8 z.val) irqSt } }
  refine WP.spec_bind (ctl_finish arI th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hHA hFI hFR hmask z hz128 hact0 hps hls hsrcC
    dsl pd hpd1 hpd hdst s1 σ1 hkb hS hCR1 hIR1 hw (ksub_of_eq (setThreadState_nks _ _) hst) ar σb rfl rfl rfl rfl rfl) ?_
  rintro ⟨s2, a2⟩ ⟨σ', G', hmem, hCR', hIR', hFI', hHA', hFR'⟩
  apply (WP.spec_ok (core.result.Result.Ok (), s2, a2)).mpr
  refine ⟨.issueIRQHandlerMSI (BitVec.ofNat 8 z.val) dsl (ps.bv, idxs) y2.bv y3.bv y4.bv y5.bv, rfl, σ1, hst,
    σ', G', ?_, hCR', hIR', hFI', hHA', hFR'⟩
  refine mem_liftE (x := ((), σ')) ?_
  refine mem_bind_nd (x := (irqSt, σ1)) rfl ?_
  refine mem_bind_nd (x := ((), σb)) (updateIrqState_mem _ _ _) ?_
  exact hmem

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem bv_gt_iff' (y : U64) (B : BitVec 64) : y.bv > B ↔ B.toNat < y.val := by
  rw [GT.gt, BitVec.lt_def]; rfl

theorem bv_sub1_toNat (n : U64) (h : n.val ≠ 0) : (n.bv - 1 : BitVec 64).toNat = n.val - 1 := by
  rw [BitVec.toNat_sub]
  have e : n.bv.toNat = n.val := rfl
  have hl : n.val < 2 ^ 64 := by scalar_tac
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [h1, e]
  omega

theorem nirq_toNat (x : BitVec 8) (h : 0 < x.toNat) : (Fl4Spec.ucast 64 (x - 1) : BitVec 64).toNat = x.toNat - 1 := by
  simp only [Fl4Spec.ucast, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hl : x.toNat < 2 ^ 8 := x.isLt
  simp
  omega

/-- The arch operations of the IOAPIC labels against the spec's arch state:
the IOAPIC count and each IOAPIC's pin count (at least one), and total
`ioapic_map`, `ioapic_map_remapped`, `mask_irq`. -/
structure ArchIrqRel (a : A) (σ : Fl4Spec.State Unit) : Prop where
  num : ∃ n, arI.num_ioapics a = ok n ∧ n.bv = σ.archState.x64NumIoapics
  pins : ∀ n, arI.num_ioapics a = ok n → ∀ i : U64, i.val < n.val →
    ∃ p, arI.ioapic_pins a i = ok p ∧ p.val = (σ.archState.x64IoapicNirqs i.bv).toNat ∧ 0 < p.val
  map : ∀ (a : A) i p l po v, ∃ b a', arI.ioapic_map a i p l po v = ok (b, a')
  mapr : ∀ (a : A) i p l po v h, ∃ b a', arI.ioapic_map_remapped a i p l po v h = ok (b, a')
  mask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a'

theorem shl16 : (1#u64 <<< 16#i32 : Result U64) = ok 65536#u64 := by
  rw [shl_eq _ _ (by decide) (by decide)]; rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`X86IRQIssueIRQHandlerIOAPIC`** (label 70). -/
theorem irq_ioapic_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.invocationType slbl = .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC)
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
    (hAR : ArchIrqRel arI ar σ) :
    interrupt.decode_irq_control st arI s ar fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC length
      (cslotAddr (ps.bv, idxs)) buf extra ⦃ res =>
      CPost (L := L) Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl false slbl (args.map UScalar.bv) (ps.bv, idxs) excaps) s res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold interrupt.decode_irq_control
  have n1 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC = fl4_abi.label.IRQIssueIRQHandler := by
    rw [u64_eq_iff]; simp
  have n2 : ¬ ((fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC != fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC) = true) := by
    simp
  have n4 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC = fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped := by
    rw [u64_eq_iff]; simp
  have n5 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC = fl4_abi.label.X86IRQIssueIRQHandlerMSI := by
    rw [u64_eq_iff]; simp
  rw [if_neg n1, if_neg n2]
  simp only [n4, n5, ↓reduceIte, bind_ok]
  obtain ⟨nA, hnum, hnA⟩ := hAR.num
  unfold interrupt.extra0; rw [hx0]; simp only [bind_ok, is_null_eq]
  -- the spec's decode
  unfold Fl4Spec.decodeFl4IrqControl
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine CPost.liftME' ?_
  unfold Fl4Spec.decodeIrqControlInvocationWith
  rw [if_neg (show ¬ Fl4Spec.genInvocationType slbl = .irqIssueIRQHandler by rw [invocationType_gen hlbl]; decide)]
  refine CPost.liftME' ?_
  unfold Fl4Spec.archDecodeIrqControlInvocation
  rw [if_pos hlbl]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 7 ∧ ([] : List Fl4Spec.Cap).length ≥ 1) by simp)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  by_cases h7 : length >= 7#u64
  swap
  · rw [if_neg h7]; simp only [error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 7 ∧ (ac0 :: erest).length ≥ 1) by simp; scalar_tac)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  rw [if_pos h7]
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, rest, rfl⟩ :
      ∃ y0 y1 y2 y3 y4 y5 y6 rest, args = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest := by
    match args with
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _] =>
      exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest => exact ⟨y0, y1, y2, y3, y4, y5, y6, rest, rfl⟩
  rw [if_pos (show ((y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest).map UScalar.bv).length ≥ 7 ∧
    (ac0 :: erest).length ≥ 1 by simp)]
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 6#u64 y6 (by simp), bind_ok,
    user_max_eq, user_min_eq, sub_107]
  have hmap : List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: rest) =
      y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv := rfl
  rw [hmap]
  have g2 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[2]? = some y2.bv := rfl
  have g3 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[3]? = some y3.bv := rfl
  have g4 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[4]? = some y4.bv := rfl
  have g6 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[6]? = some y6.bv := rfl
  have g0 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  have g1 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[1]? = some y1.bv := rfl
  have g5 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: rest.map UScalar.bv)[5]? = some y5.bv := rfl
  have ge : (ac0 :: erest)[0]? = some ac0 := rfl
  rw [g0, g1, g2, g3, g4, g5, g6, ge]
  repeat rw [the_some]
  rw [maxmin_eq]
  by_cases hr : y6 > 107#u64
  · rw [if_pos hr]; simp only [error.range, bind_ok]
    rw [whenE_pos ((bv_gt_iff y6 107 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 (BitVec.ofNat 64 107))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 (BitVec.ofNat 64 107)) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hr]
  have hy6 : y6.val ≤ 107 := by scalar_tac
  rw [whenE_neg (fun h => by have := (bv_gt_iff y6 107 (by norm_num)).1 h; omega)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IRQ
  obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := y6) (y := 16#u64) (by scalar_tac))
  rw [hz]; simp only [bind_ok]
  rw [irqv_eq y6 hy6, show y6.val + 16 = z.val by rw [hzv]; rfl]
  have hz128 : z.val < 128 := by rw [hzv]; simp; omega
  rw [is_irq_active_eq]; simp only [bind_ok]
  refine CPost.congr (run_bind_ok (run_liftE (isIrqActive_run hIR hz128)) _) ?_
  by_cases hact0 : L.mem s (irqStA (L.ksb s) z) = 0#u64
  swap
  · simp only [hact0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    rw [whenE_pos (by simpa using hact0)]
    exact CPost.err (e' := .revokeFirst)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.revokeFirst :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  simp only [hact0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [whenE_neg (by simp [hact0])]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  refine target_tail _ th (L.ksb s) s ar σ hR hV c0 ac0 hca0 hcv0 y0 y1 _ _ ?_
  intro dsl pd hpd1 hpd hdst
  -- the vector
  have hio : layout.irq.INT_OFFSET = 32#u64 := by unfold layout.irq.INT_OFFSET; rfl
  rw [hio]
  obtain ⟨z2, hz2, hz2v⟩ := spec_exists (U64.add_spec (x := z) (y := 32#u64) (by scalar_tac))
  rw [hz2]; simp only [bind_ok]
  unfold interrupt.map_ioapic
  simp only [hct, hargs 2#u64 y2 (by simp), hargs 3#u64 y3 (by simp), hargs 4#u64 y4 (by simp),
    hargs 5#u64 y5 (by simp), hnum, bind_ok, decide_false, Bool.false_eq_true, ↓reduceIte, shl16]
  -- the spec reads the IOAPIC count and pins
  refine CPost.congr (run_bind_ok (run_liftE
    (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64NumIoapics) rfl) _) ?_
  refine CPost.congr (run_bind_ok (run_liftE
    (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64IoapicNirqs) rfl) _) ?_
  beta_reduce
  rw [← hnA]
  -- no IOAPIC
  by_cases hn0 : nA = 0#u64
  · rw [if_pos hn0]
    simp only [error.illegal, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (show nA.bv = 0 by rw [hn0]; rfl)]
    exact CPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  have hn0' : nA.val ≠ 0 := fun h => hn0 (UScalar.eq_of_val_eq h)
  rw [if_neg hn0, whenE_neg (fun h => hn0 (by rw [UScalar.eq_equiv_bv_eq]; exact h))]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IOAPIC
  by_cases hia : y2 >= nA
  · rw [if_pos hia]
    obtain ⟨m1, hm1, hm1v⟩ := spec_exists (U64.sub_spec (x := nA) (y := 1#u64) (by scalar_tac))
    rw [hm1]; simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (by rw [bv_gt_iff', bv_sub1_toNat nA hn0']; scalar_tac)]
    refine CPost.err (e := .Sys (.RangeError 0#u64 m1)) (e' := .rangeError 0 (nA.bv - 1))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 (nA.bv - 1)) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, ?_⟩)
    apply BitVec.eq_of_toNat_eq
    have : m1.val = nA.val - 1 := by rw [hm1v.1]; simp
    rw [bv_sub1_toNat nA hn0']; exact this.symm
  rw [if_neg hia, whenE_neg (by rw [bv_gt_iff', bv_sub1_toNat nA hn0']; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the pin
  obtain ⟨p, hp, hpv, hp0⟩ := hAR.pins nA hnum y2 (by scalar_tac)
  rw [hp]; simp only [bind_ok]
  by_cases hpin : y3 >= p
  · rw [if_pos hpin]
    simp only [lift, bind_ok, error.range, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (by rw [bv_gt_iff', nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]; scalar_tac)]
    refine CPost.err (e := .Sys (.RangeError 0#u64 (core.num.U64.wrapping_sub p 1#u64)))
      (e' := .rangeError 0 (Fl4Spec.ucast 64 (σ.archState.x64IoapicNirqs y2.bv - 1)))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0
        (Fl4Spec.ucast 64 (σ.archState.x64IoapicNirqs y2.bv - 1))) : Fl4Spec.SEMonad Unit Unit)) rfl _)
      (Or.inl ⟨rfl, ?_⟩)
    apply BitVec.eq_of_toNat_eq
    rw [nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]
    rw [show (core.num.U64.wrapping_sub p 1#u64).bv.toNat = (core.num.U64.wrapping_sub p 1#u64).val from rfl,
      core.num.U64.wrapping_sub_val_eq]
    simp [U64.size, U64.numBits]; omega
  rw [if_neg hpin, whenE_neg (by rw [bv_gt_iff', nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- level and polarity
  by_cases hlv : y4 > 1#u64
  · rw [if_pos hlv]
    simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos ((bv_gt_iff' y4 1).2 (by simp; scalar_tac))]
    exact CPost.err (e := .Sys (.RangeError 0#u64 1#u64)) (e' := .rangeError 0 1)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 1) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hlv, whenE_neg (fun h => by have := (bv_gt_iff' y4 1).1 h; simp at this; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  by_cases hpo : y5 > 1#u64
  · rw [if_pos hpo]
    simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos ((bv_gt_iff' y5 1).2 (by simp; scalar_tac))]
    exact CPost.err (e := .Sys (.RangeError 0#u64 1#u64)) (e' := .rangeError 0 1)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 1) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hpo, whenE_neg (fun h => by have := (bv_gt_iff' y5 1).1 h; simp at this; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the handle is 0
  rw [if_neg (by scalar_tac)]
  -- `set_thread_state Restart`, the IOAPIC, then `invoke_irq_control`
  simp only [Std.bind_assoc, bind_ok]
  refine WP.spec_bind (restart_irq th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hIR ct hcur htcb hact hact2) ?_
  rintro s1 ⟨hkb, hS, σ1, hst, hCR1, hIR1, ha1, -, hw⟩
  obtain ⟨b, a1, hmap⟩ := hAR.map ar y2 y3 y4 y5 z2
  rw [hmap]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  obtain ⟨ms', hms'⟩ := doMachineOp_lift_ex
    (Fl4Spec.ioapicMapPinToVectorImpl y2.bv y3.bv y4.bv y5.bv (Fl4Spec.ucast 64 (BitVec.ofNat 8 z.val) + Fl4Spec.irqIntOffset)) σ1
  let σa : Fl4Spec.State Unit := { σ1 with machineState := ms' }
  let irqSt : Fl4Spec.X64IRQState := .irqIOAPIC (y2.bv &&& Fl4Spec.mask 5) (y3.bv &&& Fl4Spec.mask 5)
    (y4.bv &&& 1) (y5.bv &&& 1) true
  let σb : Fl4Spec.State Unit := { σa with archState := { σa.archState with
    x64IrqState := Function.update σa.archState.x64IrqState (BitVec.ofNat 8 z.val) irqSt } }
  refine WP.spec_bind (ctl_finish arI th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hHA hFI hFR hAR.mask z hz128 hact0 hps hls hsrcC
    dsl pd hpd1 hpd hdst s1 σ1 hkb hS hCR1 hIR1 hw (ksub_of_eq (setThreadState_nks _ _) hst) a1 σb rfl rfl rfl rfl rfl) ?_
  rintro ⟨s2, a2⟩ ⟨σ', G', hmem, hCR', hIR', hFI', hHA', hFR'⟩
  apply (WP.spec_ok (core.result.Result.Ok (), s2, a2)).mpr
  refine ⟨.issueIRQHandlerIOAPIC (BitVec.ofNat 8 z.val) dsl (ps.bv, idxs) y2.bv y3.bv y4.bv y5.bv
      (Fl4Spec.ucast 64 (BitVec.ofNat 8 z.val) + Fl4Spec.irqIntOffset), rfl, σ1, hst, σ', G', ?_, hCR', hIR', hFI', hHA', hFR'⟩
  refine mem_liftE (x := ((), σ')) ?_
  refine mem_bind_nd (x := ((), σa)) hms' ?_
  refine mem_bind_nd (x := (irqSt, σa)) rfl ?_
  refine mem_bind_nd (x := ((), σb)) (updateIrqState_mem _ _ _) ?_
  exact hmem


/-- **l4h `X86IRQIssueIRQHandlerIOAPICRemapped`** (label 72), against FL4's copy of the IOAPIC decode with
the remapping-table handle. -/
theorem irq_remap_refines (th : TypedHeap) (hP : Placed th) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hL : IntLayout th (L.ksb s)) (hIR : IrqRel (L.mem s) (L.ksb s) σ)
    (hHA : HandlersActive (L.mem s) (L.ksb s) G) (hFI : FinInv th (L.mem s) σ G) (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (slbl : Fl4Spec.Data)
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
    (hAR : ArchIrqRel arI ar σ) :
    interrupt.decode_irq_control st arI s ar fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped length
      (cslotAddr (ps.bv, idxs)) buf extra ⦃ res =>
      CPost (L := L) Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl true slbl (args.map UScalar.bv) (ps.bv, idxs) excaps) s res ⦄ := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  unfold interrupt.decode_irq_control
  have n1 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped = fl4_abi.label.IRQIssueIRQHandler := by
    rw [u64_eq_iff]; simp
  have n2 : (fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped != fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC) = true := by
    rw [bne_iff_ne, ne_eq, u64_eq_iff]; simp
  have n3 : (fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped != fl4_abi.label.X86IRQIssueIRQHandlerMSI) = true := by
    rw [bne_iff_ne, ne_eq, u64_eq_iff]; simp
  have n5 : ¬ fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped = fl4_abi.label.X86IRQIssueIRQHandlerMSI := by
    rw [u64_eq_iff]; simp
  rw [if_neg n1, if_pos n2, if_pos n3, if_pos rfl]
  simp only [n5, eq_self_iff_true, ↓reduceIte, bind_ok]
  obtain ⟨nA, hnum, hnA⟩ := hAR.num
  unfold interrupt.extra0; rw [hx0]; simp only [bind_ok, is_null_eq]
  -- the spec's decode
  unfold Fl4Spec.decodeFl4IrqControl
  simp only [↓reduceIte]
  unfold Fl4Spec.decodeIrqControlRemapped
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, c0, ac0, erest, hc0, hca0, hcv0, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 8 ∧ ([] : List Fl4Spec.Cap).length ≥ 1) by simp)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, hc0, bind_ok]
  by_cases h7 : length >= 8#u64
  swap
  · rw [if_neg h7]; simp only [error.truncated, bind_ok]
    rw [if_neg (show ¬ ((args.map UScalar.bv).length ≥ 8 ∧ (ac0 :: erest).length ≥ 1) by simp; scalar_tac)]
    exact CPost.err (e' := .truncatedMessage) rfl (Or.inl trivial)
  rw [if_pos h7]
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, rest, rfl⟩ :
      ∃ y0 y1 y2 y3 y4 y5 y6 y7 rest, args = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest := by
    match args with
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
    | [_, _, _, _, _, _, _] =>
      exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest => exact ⟨y0, y1, y2, y3, y4, y5, y6, y7, rest, rfl⟩
  rw [if_pos (show ((y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest).map UScalar.bv).length ≥ 8 ∧
    (ac0 :: erest).length ≥ 1 by simp)]
  simp only [hct, hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 6#u64 y6 (by simp), bind_ok,
    user_max_eq, user_min_eq, sub_107]
  have hmap : List.map UScalar.bv (y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest) =
      y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv := rfl
  rw [hmap]
  have g2 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[2]? = some y2.bv := rfl
  have g3 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[3]? = some y3.bv := rfl
  have g4 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[4]? = some y4.bv := rfl
  have g6 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[6]? = some y6.bv := rfl
  have g0 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[0]? = some y0.bv := rfl
  have g1 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[1]? = some y1.bv := rfl
  have g5 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[5]? = some y5.bv := rfl
  have ge : (ac0 :: erest)[0]? = some ac0 := rfl
  have g7 : (y0.bv :: y1.bv :: y2.bv :: y3.bv :: y4.bv :: y5.bv :: y6.bv :: y7.bv :: rest.map UScalar.bv)[7]? =
    some y7.bv := rfl
  rw [g0, g1, g2, g3, g4, g5, g6, g7, ge]
  repeat rw [the_some]
  rw [maxmin_eq]
  by_cases hr : y6 > 107#u64
  · rw [if_pos hr]; simp only [error.range, bind_ok]
    rw [whenE_pos ((bv_gt_iff y6 107 (by norm_num)).2 (by scalar_tac))]
    exact CPost.err (e' := .rangeError 0 (BitVec.ofNat 64 107))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 (BitVec.ofNat 64 107)) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hr]
  have hy6 : y6.val ≤ 107 := by scalar_tac
  rw [whenE_neg (fun h => by have := (bv_gt_iff y6 107 (by norm_num)).1 h; omega)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IRQ
  obtain ⟨z, hz, hzv⟩ := spec_exists (U64.add_spec (x := y6) (y := 16#u64) (by scalar_tac))
  rw [hz]; simp only [bind_ok]
  rw [irqv_eq y6 hy6, show y6.val + 16 = z.val by rw [hzv]; rfl]
  have hz128 : z.val < 128 := by rw [hzv]; simp; omega
  rw [is_irq_active_eq]; simp only [bind_ok]
  refine CPost.congr (run_bind_ok (run_liftE (isIrqActive_run hIR hz128)) _) ?_
  by_cases hact0 : L.mem s (irqStA (L.ksb s) z) = 0#u64
  swap
  · simp only [hact0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    rw [whenE_pos (by simpa using hact0)]
    exact CPost.err (e' := .revokeFirst)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.revokeFirst :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  simp only [hact0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [whenE_neg (by simp [hact0])]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  refine target_tail _ th (L.ksb s) s ar σ hR hV c0 ac0 hca0 hcv0 y0 y1 _ _ ?_
  intro dsl pd hpd1 hpd hdst
  -- the vector
  have hio : layout.irq.INT_OFFSET = 32#u64 := by unfold layout.irq.INT_OFFSET; rfl
  rw [hio]
  obtain ⟨z2, hz2, hz2v⟩ := spec_exists (U64.add_spec (x := z) (y := 32#u64) (by scalar_tac))
  rw [hz2]; simp only [bind_ok]
  unfold interrupt.map_ioapic
  simp only [hct, hargs 2#u64 y2 (by simp), hargs 3#u64 y3 (by simp), hargs 4#u64 y4 (by simp),
    hargs 5#u64 y5 (by simp), hargs 7#u64 y7 (by simp), hnum, bind_ok, decide_true, ↓reduceIte, shl16]
  -- the spec reads the IOAPIC count and pins
  refine CPost.congr (run_bind_ok (run_liftE
    (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64NumIoapics) rfl) _) ?_
  refine CPost.congr (run_bind_ok (run_liftE
    (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.archState.x64IoapicNirqs) rfl) _) ?_
  beta_reduce
  rw [← hnA]
  -- no IOAPIC
  by_cases hn0 : nA = 0#u64
  · rw [if_pos hn0]
    simp only [error.illegal, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (show nA.bv = 0 by rw [hn0]; rfl)]
    exact CPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl trivial)
  have hn0' : nA.val ≠ 0 := fun h => hn0 (UScalar.eq_of_val_eq h)
  rw [if_neg hn0, whenE_neg (fun h => hn0 (by rw [UScalar.eq_equiv_bv_eq]; exact h))]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the IOAPIC
  by_cases hia : y2 >= nA
  · rw [if_pos hia]
    obtain ⟨m1, hm1, hm1v⟩ := spec_exists (U64.sub_spec (x := nA) (y := 1#u64) (by scalar_tac))
    rw [hm1]; simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (by rw [bv_gt_iff', bv_sub1_toNat nA hn0']; scalar_tac)]
    refine CPost.err (e := .Sys (.RangeError 0#u64 m1)) (e' := .rangeError 0 (nA.bv - 1))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 (nA.bv - 1)) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, ?_⟩)
    apply BitVec.eq_of_toNat_eq
    have : m1.val = nA.val - 1 := by rw [hm1v.1]; simp
    rw [bv_sub1_toNat nA hn0']; exact this.symm
  rw [if_neg hia, whenE_neg (by rw [bv_gt_iff', bv_sub1_toNat nA hn0']; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the pin
  obtain ⟨p, hp, hpv, hp0⟩ := hAR.pins nA hnum y2 (by scalar_tac)
  rw [hp]; simp only [bind_ok]
  by_cases hpin : y3 >= p
  · rw [if_pos hpin]
    simp only [lift, bind_ok, error.range, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (by rw [bv_gt_iff', nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]; scalar_tac)]
    refine CPost.err (e := .Sys (.RangeError 0#u64 (core.num.U64.wrapping_sub p 1#u64)))
      (e' := .rangeError 0 (Fl4Spec.ucast 64 (σ.archState.x64IoapicNirqs y2.bv - 1)))
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0
        (Fl4Spec.ucast 64 (σ.archState.x64IoapicNirqs y2.bv - 1))) : Fl4Spec.SEMonad Unit Unit)) rfl _)
      (Or.inl ⟨rfl, ?_⟩)
    apply BitVec.eq_of_toNat_eq
    rw [nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]
    rw [show (core.num.U64.wrapping_sub p 1#u64).bv.toNat = (core.num.U64.wrapping_sub p 1#u64).val from rfl,
      core.num.U64.wrapping_sub_val_eq]
    simp [U64.size, U64.numBits]; omega
  rw [if_neg hpin, whenE_neg (by rw [bv_gt_iff', nirq_toNat _ (by rw [← hpv]; exact hp0), ← hpv]; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- level and polarity
  by_cases hlv : y4 > 1#u64
  · rw [if_pos hlv]
    simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos ((bv_gt_iff' y4 1).2 (by simp; scalar_tac))]
    exact CPost.err (e := .Sys (.RangeError 0#u64 1#u64)) (e' := .rangeError 0 1)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 1) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hlv, whenE_neg (fun h => by have := (bv_gt_iff' y4 1).1 h; simp at this; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  by_cases hpo : y5 > 1#u64
  · rw [if_pos hpo]
    simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos ((bv_gt_iff' y5 1).2 (by simp; scalar_tac))]
    exact CPost.err (e := .Sys (.RangeError 0#u64 1#u64)) (e' := .rangeError 0 1)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 1) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hpo, whenE_neg (fun h => by have := (bv_gt_iff' y5 1).1 h; simp at this; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- the handle
  by_cases hh : y7 >= 65536#u64
  · rw [if_pos hh]
    simp only [error.range, bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, bind_tc_ok]
    rw [whenE_pos (by rw [GE.ge, BitVec.le_def]; show (65536 : BitVec 64).toNat ≤ y7.val; simp; scalar_tac)]
    exact CPost.err (e := .Sys (.RangeError 0#u64 65535#u64)) (e' := .rangeError 0 0xffff)
      (run_bind_error (m := (Fl4Spec.NonDetE.throwError (Fl4Spec.SyscallError.rangeError 0 0xffff) :
        Fl4Spec.SEMonad Unit Unit)) rfl _) (Or.inl ⟨rfl, rfl⟩)
  rw [if_neg hh, whenE_neg (by rw [GE.ge, BitVec.le_def]; show ¬ (65536 : BitVec 64).toNat ≤ y7.val; simp; scalar_tac)]
  refine CPost.congr (run_bind_ok (m := (Fl4Spec.NonDetE.returnOk () : Fl4Spec.SEMonad Unit Unit)) rfl _) ?_
  -- `set_thread_state Restart`, the IOAPIC, then `invoke_irq_control`
  simp only [Std.bind_assoc, bind_ok]
  refine WP.spec_bind (restart_irq th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hIR ct hcur htcb hact hact2) ?_
  rintro s1 ⟨hkb, hS, σ1, hst, hCR1, hIR1, ha1, -, hw⟩
  obtain ⟨b, a1, hmap⟩ := hAR.mapr ar y2 y3 y4 y5 z2 y7
  rw [hmap]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  obtain ⟨ms', hms'⟩ := doMachineOp_lift_ex
    (Fl4Spec.ioapicMapPinToVectorRemappedImpl y2.bv y3.bv y4.bv y5.bv
      (Fl4Spec.ucast 64 (BitVec.ofNat 8 z.val) + Fl4Spec.irqIntOffset) y7.bv) σ1
  let σa : Fl4Spec.State Unit := { σ1 with machineState := ms' }
  let irqSt : Fl4Spec.X64IRQState := .irqIOAPIC (y2.bv &&& Fl4Spec.mask 5) (y3.bv &&& Fl4Spec.mask 5)
    (y4.bv &&& 1) (y5.bv &&& 1) true
  let σb : Fl4Spec.State Unit := { σa with archState := { σa.archState with
    x64IrqState := Function.update σa.archState.x64IrqState (BitVec.ofNat 8 z.val) irqSt } }
  refine WP.spec_bind (ctl_finish arI th hP s σ G ⟨hR, hV, hM, hC, hI⟩ hL hHA hFI hFR hAR.mask z hz128 hact0 hps hls hsrcC
    dsl pd hpd1 hpd hdst s1 σ1 hkb hS hCR1 hIR1 hw (ksub_of_eq (setThreadState_nks _ _) hst) a1 σb rfl rfl rfl rfl rfl) ?_
  rintro ⟨s2, a2⟩ ⟨σ', G', hmem, hCR', hIR', hFI', hHA', hFR'⟩
  apply (WP.spec_ok (core.result.Result.Ok (), s2, a2)).mpr
  refine ⟨.ioapicRemapped (BitVec.ofNat 8 z.val) dsl (ps.bv, idxs) y2.bv y3.bv y4.bv y5.bv
      (Fl4Spec.ucast 64 (BitVec.ofNat 8 z.val) + Fl4Spec.irqIntOffset) y7.bv, rfl, σ1, hst, σ', G', ?_, hCR', hIR', hFI', hHA', hFR'⟩
  refine mem_liftE (x := ((), σ')) ?_
  refine mem_bind_nd (x := ((), σa)) hms' ?_
  refine mem_bind_nd (x := (irqSt, σa)) rfl ?_
  refine mem_bind_nd (x := ((), σb)) (updateIrqState_mem _ _ _) ?_
  exact hmem

end

section
open Fl4Spec

theorem run_bind_congr {σ ε α β : Type} {m m' : NonDetE σ ε α} {s : σ} (h : m.run s = m'.run s)
    (k : α → NonDetE σ ε β) : (m >>= k).run s = (m' >>= k).run s := by
  simp only [ExceptT.run_bind]
  show (ExceptT.run m >>= _) s = (ExceptT.run m' >>= _) s
  simp only [nd_bind_apply, h]

/-- **With an IOAPIC, FL4's IRQControl decode is l4v's.** -/
theorem decodeWith_fl4_eq {σ : State Unit} (h : σ.archState.x64NumIoapics ≠ 0) (label : Data) (args : List Data)
    (src : CslotPtr) (cps : List Cap) :
    (decodeIrqControlInvocationWith (Z := Unit) fl4ArchCheckIrq label args src cps).run σ =
      (decodeIrqControlInvocation (Z := Unit) label args src cps).run σ := by
  rw [← decodeIrqControlInvocationWith_archCheckIrq]
  unfold decodeIrqControlInvocationWith
  split_ifs
  · apply run_bind_congr
    unfold fl4ArchCheckIrq archCheckIrq
    rw [run_bind_ok (run_liftE (m := NonDet.gets fun s : State Unit => s.archState.x64NumIoapics) rfl)]
    rw [if_neg h]
  · rfl
  · rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **Any other IRQControl label**: `IllegalOperation`. -/
theorem irq_ctl_other_refines (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (lbl : U64) (h1 : lbl.val ≠ 33) (h2 : lbl.val ≠ 70) (h3 : lbl.val ≠ 71) (h4 : lbl.val ≠ 72)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl ≠ .irqIssueIRQHandler ∧
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64IRQIssueIRQHandlerIOAPIC ∧
      Fl4Spec.invocationType slbl ≠ .archInvocationLabel .x64IRQIssueIRQHandlerMSI)
    (length src buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (args : List Fl4Spec.Data)
    (ssl : Fl4Spec.CslotPtr) (excaps : List Fl4Spec.Cap) :
    interrupt.decode_irq_control st arI s ar lbl length src buf extra ⦃ res =>
      CPost (L := L) Fl4Spec.invokeFl4IrqControl th (L.ksb s) σ
        (Fl4Spec.decodeFl4IrqControl false slbl args ssl excaps) s res ⦄ := by
  unfold interrupt.decode_irq_control
  have n1 : ¬ lbl = fl4_abi.label.IRQIssueIRQHandler := by rw [u64_eq_iff]; simpa using h1
  have n2 : (lbl != fl4_abi.label.X86IRQIssueIRQHandlerIOAPIC) = true := by
    rw [bne_iff_ne, ne_eq, u64_eq_iff]; simpa using h2
  have n3 : (lbl != fl4_abi.label.X86IRQIssueIRQHandlerMSI) = true := by
    rw [bne_iff_ne, ne_eq, u64_eq_iff]; simpa using h3
  have n4 : ¬ lbl = fl4_abi.label.X86IRQIssueIRQHandlerIOAPICRemapped := by rw [u64_eq_iff]; simpa using h4
  rw [if_neg n1, if_pos n2, if_pos n3, if_neg n4]
  simp only [error.illegal, bind_ok]
  unfold Fl4Spec.decodeFl4IrqControl
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine CPost.liftME' ?_
  unfold Fl4Spec.decodeIrqControlInvocationWith
  rw [if_neg hlbl.1]
  refine CPost.liftME' ?_
  unfold Fl4Spec.archDecodeIrqControlInvocation
  rw [if_neg hlbl.2.1, if_neg hlbl.2.2]
  exact CPost.err (e := .Sys .IllegalOperation) (e' := .illegalOperation) rfl (Or.inl trivial)

end

end

end Fl4Proofs.P3
