/-
P3 (DESIGN.md §9), invariant line G4 (g4h, KENTRY-PLAN g4h; g4d's handoff):
**`JDecMRL` narrowed: the IO port, IRQ handler and IRQ control caps' decodes
with `MR` at the chosen outcome proved.**

* `XCapP.mrG` (`TopPostDMXP.mrG`, `TopPostRMX.mrG`): `XCapP.mr` for a decode
  that moves the machine fields `MR` reads by a fixed `f`: FL4's decode ends
  at `MR` of `f ms` when it succeeds (of `ms` when it fails), every perform
  outcome of every decoded invocation has the four fields of `f` at the
  restart's machine state (`MachF.mF`).
* IO port (`z = 0`): FL4 by `MKD.decode_ioport` (MachKeepG4h, under the new
  arch-only [P] `MRKeepIo`: `port_in` / `port_out` keep `MR`), spec by
  `MachT.dec_quiet` (an IO port cap is an arch cap, its invocation `QInv`).
* IRQ handler: FL4 by `MKD.decode_irq_handler_mr` (Ack: the one
  `mask_irq irq false` moves `MR` by `MachPlat.mask`; Set / Clear: arch
  kept); spec: at the Ack label the decode yields `aCKIrq irq`
  (`dec_irqH_ack`), whose perform is `maskInterrupt false irq`
  (`perf_ack_ms`); at the other labels Set / Clear (`dec_irqH_nack`), which
  keep `msFT` (`perf_irqH_nack`).
* IRQ control: `decode_invocation_irq_controlXSM` (XTopCaps' `XS` with
  IrqCtlMR's `irq_control_decode_refinesM`: `MR` at the outcome, FL4's
  `mask_irq` against the spec's `setIrqState Signal`; the IOAPIC labels under
  the new arch-only [P] `MRKeepIoapic`).
* `LoudR` (Thread, Untyped) and **`JDecMRL2`** [W]: `JDecMRL`
  asked only for `LoudR` caps. `jDecMRL_of`: at a dispatch state with the
  invocation's `JEntryGlobM` / `JEntryAt` / `JPreDecHypM` (what
  `KDispHyps13PU` gives), `JDecMRL2 → JDecMRL`.
* Copies with `hDL : JDecMRL2` (and `hIo`, `hIoa`): `dispatch_all13PUNM2`,
  `kernel_entryJ13PUGMD2`, NEW TOPS **`kernel_entryJ39`** (= `kernel_entryJ38`
  with `JDecMRL2` for `JDecMRL`, plus `hIo` / `hIoa` [P]) and
  **`kernel_entry_reachMD2`**.
-/
import Fl4Proofs.P3.XTopJointKEntry38
import Fl4Proofs.P3.MachKeepG4h
import Fl4Proofs.P3.IrqCtlMR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec side of the IRQ handler cap -/

/-- The machine state with line `w` unmasked (`MachPlat.mask`'s update). -/
def unmaskMs (ms : Fl4Spec.MachineState) (w : U64) : Fl4Spec.MachineState :=
  { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) false }


section
open Fl4Spec

theorem dec_irqH_ack (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (i : Irq)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (h : genInvocationType lbl = .irqAckIRQ) :
    NoPre.OkP (fun inv => inv = .invokeIRQHandler (.aCKIrq i))
      (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.irqHandlerCap i) ex buf) := by
  simp only [fl4DecodeInvocation]
  refine NoPre.okP_liftME' (Q := fun j => j = .aCKIrq i) ?_ fun x hx => by rw [hx]
  simp only [decodeIrqHandlerInvocation, if_pos h, NonDetE.returnOk]
  exact NoPre.okP_pure rfl

theorem dec_irqH_nack (fp : Bool) (lbl : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (i : Irq)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (h : genInvocationType lbl ≠ .irqAckIRQ) :
    NoPre.OkP (fun inv => ∃ j, inv = .invokeIRQHandler j ∧ ∀ k, j ≠ .aCKIrq k)
      (fl4DecodeInvocation (Z := Unit) fp lbl args ci sl (.irqHandlerCap i) ex buf) := by
  simp only [fl4DecodeInvocation]
  refine NoPre.okP_liftME' (Q := fun j => ∀ k, j ≠ .aCKIrq k) ?_ fun x hx => ⟨x, rfl, hx⟩
  unfold decodeIrqHandlerInvocation
  simp only [if_neg h, NonDetE.returnOk, NonDetE.throwError]
  repeat' (first
    | exact NoPre.okP_throw
    | exact NoPre.okP_pure (fun k e => by cases e)
    | split)

/-- The Ack invocation's perform unmasks the line. -/
theorem perf_ack_ms (b c d : Bool) (i : Irq) (σ1 : State Unit) {y : Except Unit (List Data) × State Unit}
    (hy : y ∈ ((fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i))).run σ1).1) :
    y.2.machineState = { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } := by
  have h1 : invokeIrqHandler (Z := Unit) (.aCKIrq i) σ1 = ({((), { σ1 with machineState :=
      { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } })}, False) := by
    show doMachineOp (maskInterrupt false i) σ1 = _
    exact doMachineOp_single rfl
  have h2 := run_liftE' (ε := Unit) h1
  have h3 : (fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i))).run σ1 =
      ({(.ok [], { σ1 with machineState :=
        { σ1.machineState with irqMasks := Function.update σ1.machineState.irqMasks i false } })}, False) := by
    rw [show fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler (.aCKIrq i)) =
      (NonDetE.liftE (invokeIrqHandler (.aCKIrq i)) >>= fun _ => NonDetE.returnOk []) from rfl]
    rw [dec_run_bind h2]; rfl
  rw [h3] at hy
  rw [Set.mem_singleton_iff.1 hy]

/-- The Set / Clear invocations keep `msFT`. -/
theorem perf_irqH_nack (b c d : Bool) (j : IrqHandlerInvocation) (hj : ∀ k, j ≠ .aCKIrq k) :
    MachT.MTKE (fl4PerformInvocation (Z := Unit) b c d (.invokeIRQHandler j)) := by
  cases j with
  | aCKIrq k => exact absurd rfl (hj k)
  | _ => unfold fl4PerformInvocation invokeIrqHandler; mtk_auto

end

/-! ## `XCapP.mr` for a decode that moves `MR`'s fields by `f` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

theorem mF_mr (hM : MachPlat arI MR) {a : A} {ms ms' : Fl4Spec.MachineState} (hR : MR a ms)
    (h : MachF.mF ms' = MachF.mF ms) : MR a ms' := by
  simp only [MachF.mF, Prod.mk.injEq] at h
  exact hM.frame a _ _ hR h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The perform outcomes' four fields are `f`'s at the decode state. -/
def PerfF (f : Fl4Spec.MachineState → Fl4Spec.MachineState) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) : Prop :=
  ∀ inv, DecOut m σ inv → ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    ∀ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, (∃ l, y.1 = .ok l) →
      MachF.mF y.2.machineState = MachF.mF (f σ.machineState)

theorem TopPostDMXP.mrG (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    rw [h1] at hR
    rw [if_neg (by simp)] at hR
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      obtain ⟨th', G', hc, -⟩ := h3
      have hc' : res.1 = .Ok () ∧ y.1 = .ok [] := hc.resolve_right fun ⟨e, _⟩ => hp e
      rw [if_pos hc'.1] at hR
      exact ⟨h4, mF_mr hM hR (hq inv h1 σ1 h2 y hy ⟨_, hc'.2⟩)⟩

theorem TopPostRMX.mrG (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res)
    (hR : MR res.2.2 (if res.1 = .Ok () then f σ.machineState else σ.machineState))
    (hq : PerfF f σ blk call don m) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · rw [h1, if_neg (by simp)] at hR
    exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · rw [if_pos h1] at hR
    refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, mF_mr hM hR ?_⟩
    have e1 := congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)
    simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
    have e2 := hq inv h3 σ1 h4 _ h5 ⟨rr, rfl⟩
    rw [← e2]
    simp only [MachF.mF, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

/-- **`XCapP` with `MR`, the fields moved by `f`** (module docstring). -/
theorem XCapP.mrG (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64} {f : Fl4Spec.MachineState → Fl4Spec.MachineState}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 (if r.1 = .Ok () then f σ.machineState else σ.machineState) ⦄)
    (hq : PerfF f σ blk call don (specDec fp slbl args ci sl c excaps buffer)) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrG hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrG hM h2 hq)

theorem irqAck_val : fl4_abi.label.IRQAckIRQ.val = 34 := by simp [fl4_abi.label.IRQAckIRQ]

/-- **`PerfF` of the IRQ handler cap** (module docstring). -/
theorem perfF_irqH (irq : U64) (hirq : irq.val < 128) (lbl : U64) (σ : Fl4Spec.State Unit) (blk call don fp : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) :
    PerfF (fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) σ blk call don
      (specDec fp lbl.bv args ci sl (.IrqHandler irq) excaps buffer) := by
  intro inv hd σ1 hst y hy _
  have e1 := congrArg Prod.fst (MachT.mtk_setThreadState' _ _ σ ((), σ1) (mem_of_single hst))
  simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e1
  by_cases hl : lbl = fl4_abi.label.IRQAckIRQ
  · have hg : Fl4Spec.genInvocationType lbl.bv = .irqAckIRQ := by
      have h34 : lbl.val = 34 := by rw [hl, irqAck_val]
      rw [irqH_in lbl (by omega) (by omega)]; unfold irqHLabelOf; rw [if_pos h34]
    have hinv := dec_irqH_ack fp lbl.bv args ci sl (BitVec.ofNat 8 irq.val) excaps buffer hg σ _ hd.1 inv rfl
    subst hinv
    rw [perf_ack_ms blk call don _ σ1 hy]
    simp only [if_pos hl]
    have hw : (irq.bv.setWidth 8 : BitVec 8) = BitVec.ofNat 8 irq.val := by
      apply BitVec.eq_of_toNat_eq; simp
    simp only [MachF.mF, unmaskMs, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1, hw]
  · have hg : Fl4Spec.genInvocationType lbl.bv ≠ .irqAckIRQ := by
      have h34 : lbl.val ≠ 34 := fun e => hl (UScalar.eq_of_val_eq (by rw [e, irqAck_val]))
      by_cases hr : 34 ≤ lbl.val ∧ lbl.val ≤ 36
      · rw [irqH_in lbl hr.1 hr.2]; unfold irqHLabelOf; rw [if_neg h34]; split_ifs <;> decide
      · intro e; exact (irqH_out lbl hr).1 (by rw [e]; decide)
    obtain ⟨j, rfl, hj⟩ := dec_irqH_nack fp lbl.bv args ci sl (BitVec.ofNat 8 irq.val) excaps buffer hg σ _ hd.1 inv rfl
    have e2 := congrArg Prod.fst (perf_irqH_nack blk call don j hj σ1 y hy)
    simp only [MachT.msFT, MachF.msF, Prod.mk.injEq] at e2
    simp only [if_neg hl]
    simp only [MachF.mF, e2.1, e2.2.1, e2.2.2.1, e2.2.2.2.1, e1.1, e1.2.1, e1.2.2.1, e1.2.2.2.1]

end

/-! ## The IRQ control cap with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`decode_invocation_irq_controlXS` with `MR`** (IrqCtlMR's
`irq_control_decode_refinesM`). -/
theorem decode_invocation_irq_controlXSM {AR : A → Fl4Spec.Cr3 → Prop}
    (th : TypedHeap) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hL : IntLayout th (L.ksb s))
    (hHA : HandlersActive (L.mem s) (L.ksb s) G)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : IrqCLabel lbl slbl)
    (hrm : decide (lbl.val = 72) = Fl4Spec.isFl4RemappedLabel slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hact2 : ∀ i : U64, i.val < 128 → L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ irqStA (L.ksb s) i)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    {ps : U64} {rs : Nat} (hps : th ps = some (.cnode rs)) {idxs : List Bool} (hls : idxs.length = rs)
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok .IrqControl)
    (nA : U64) (hnum : arI.num_ioapics ar = ok nA) (hnA : nA.bv = σ.archState.x64NumIoapics)
    (hmask : ∀ (a : A) (irq : U64) (b : Bool), ∃ a', arI.mask_irq a irq b = ok a')
    (hAR : ArchIrqRel arI ar σ) {Z : XSets} (hth : Z.th = th) (hG : Z.G = G) (hX0 : XTopAt (L := L) AR Z s ar σ)
    (hC : CurRun σ) (X : S → A → Fl4Spec.State Unit → Prop) (hXa : X s ar σ)
    (hXS : ∀ s' a' σ', Steps (L := L) arI th s ar σ s' a' σ' → X s' a' σ')
    (hXX : ∀ s a σ, X s a σ → XTop (L := L) AR s a σ) (blk call don fp : Bool) (ci : Fl4Spec.CapRef)
    (buffer : Option Fl4Spec.ObjRef) (hMk : MaskMR arI MR) (hfr : FrameMR MR) (hR0 : MR ar σ.machineState)
    (hIoa : MRKeepIoapic arI MR) :
    XCap (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) s ar σ lbl length (cslotAddr (ps.bv, idxs)) .IrqControl blk call don fp buf
      extra slbl (args.map UScalar.bv) ci (ps.bv, idxs) excaps buffer ct := by
  subst hth hG
  have hP := hX0.rel.1
  have hCR := hX0.rel.2.1
  have hFI := hX0.rel.2.2.1
  have hFR := hX0.rel.2.2.2.2.1
  have hIR := hX0.fin.1.1.2.2.2.1
  have htcb : Z.th ct = some .tcb := by
    obtain ⟨t, htb, hth, -⟩ := hX0.fin.2.2.2.2
    rwa [← P1.eq_of_bv (htb.trans hcur)]
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  have e : specDec fp slbl (args.map UScalar.bv) ci (ps.bv, idxs) .IrqControl excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeIRQControl
        (Fl4Spec.decodeFl4IrqControl (decide (lbl.val = 72)) slbl (args.map UScalar.bv) (ps.bv, idxs)
          (excaps.map Prod.fst)) := by
    rw [hrm]; rfl
  rw [e]
  refine WP.spec_mono (irq_control_decode_refinesM arI Z.th hP s ar σ Z.G hCR hL hIR hHA hFI hFR lbl slbl hlbl length buf ct
    hct args hlen hargs hcur htcb hact hact2 extra x0 hx0 _ hex hps hls hsrcC nA hnum hnA hmask hAR hMk hfr hR0 hIoa) ?_
  rintro ⟨r0, s', a'⟩ hq
  cases r0 with
  | Err e =>
    obtain ⟨rfl, ⟨e', h1, h2⟩, rfl⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, h2⟩, hXa, hR0⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, σ', G', hx, hmr, -, -, -, -, -, -, hstp⟩ := hq
    have hXp := hXS _ _ _ (hstp hC)
    obtain ⟨Z', hZ'⟩ := hXX _ _ _ hXp
    exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ'),
      mem_bindE_ok hx (Set.mem_singleton _), ⟨Z'.th, Z'.G, Or.inl ⟨rfl, rfl⟩, hZ'.rel.1, hZ'.rel.2.1,
        hZ'.rel.2.2.1, hZ'.rel.2.2.2.1, hZ'.rel.2.2.2.2.1⟩, hXp, hmr⟩

end

/-! ## `JDecMRL` narrowed -/

/-- **The cap kinds whose decode with `MR` is still asked** (module docstring). -/
def LoudR : capability.Cap → Prop
  | .Thread _ => True
  | .Untyped .. => True
  | _ => False

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] `JDecMRL` for the `LoudR` caps** (Thread, Untyped; module docstring):
the IO port, IRQ handler and IRQ control caps are proved (`jDecMRL_of`).
l4v: `invoke_tcb_corres`, `invoke_untyped_corres` with the machine state
shared (`preemption_point` in the installs' and the reset's loops). -/
def JDecMRL2 (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  MR ar σ.machineState → ValidMachineTime σ → ValidIrqMasks σ →
  ∀ (lbl length : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64), length.val = argsU.length →
    (∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x) →
    msg.lookup_ipc_buffer st s false ct = ok buf → argsU.length ≤ 120 →
    ∀ (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    ∀ (c : capability.Cap), capAt (L.mem s) (cslotAddr sl) = ok c → (LoudR c ∧ Vs.NativeCap c) →
    ∀ (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef),
    ExtraOK Z.th (L.mem s) extra excaps → ExtraNamed Z.th (L.mem s) extra → lbl.bv = slbl →
    ArgRel (st := st) s σ ct buf buffer 5 →
    JPathM (L := L) arI AR Z H Cs D s ar σ lbl length blk call don fp buf extra slbl argsU ci sl excaps buffer ct c →
    XCapP (L := L) arI (JAtM (L := L) arI AR MR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c
      blk call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

/-- **[J] The IRQ ack's unmask at an entry state** (module docstring): unmasking the line of an IRQ
handler cap held in a CNode slot keeps `MR` (moved from IrqFixC in collapse A, Q). Under the un-narrowed `MachPlat`
before collapse A (unmasking any line `< 256`) it held; under `MachPlatF` it is l4v `valid_cap`'s `irq ≤ maxIRQ` for the handler caps (`IrqAckU.of_bound`). -/
def IrqAckU (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val < 128 → MR ar σ.machineState →
    arI.mask_irq ar irq false ⦃ a' =>
      MR a' { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks (irq.bv.setWidth 8) false } ⦄

/-- `JDecMRL2` with the IRQ ack's `IrqAckU`. -/
def JDecMRL2Q (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable {arI} in
/-- **`IrqAckU` under `MachPlatF` from l4v `valid_cap`'s bound** (every handler cap's line `≤ maxIRQ`). -/
theorem IrqAckU.of_bound (hM : MachPlatF arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hB : ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val ≤ 125) :
    IrqAckU (L := L) arI MR Z s ar σ :=
  fun sl irq hsl hc _ hR => hM.mask0 ar irq _ hR (hB sl irq hsl hc)

set_option maxHeartbeats 4000000 in
/-- **`JDecMRL` from `JDecMRL2`** at a dispatch state (module docstring): the
IO port cap by `XCapP.mr` (FL4 `MKD.decode_ioport` under `MRKeepIo`, spec
`dec_quiet`), the IRQ handler cap by `XCapP.mrG` (`MKD.decode_irq_handler_mr`,
`perfF_irqH`), the IRQ control cap by `decode_invocation_irq_controlXSM`,
the rest by `JDecMRL2`. -/
theorem jDecMRL_of [Fl4Proofs.P1.PlainStore st] (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hG : JEntryGlobM (L := L) arI AR MR Z.th) (hE : JEntryAt (L := L) arI AR Z H Cs s ar σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hPD : JPreDecHypM (L := L) arI AR MR Z H Cs D s ar σ ct) (hNs : NativeScope σ) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hIoa : MRKeepIoapic arI MR) (hDL : JDecMRL2Q (L := L) arI AR MR Z H Cs D s ar σ ct) :
    JDecMRL (L := L) arI AR MR Z H Cs D s ar σ ct := by
  intro hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl c hc hcl
    excaps buffer hXO hXN hLb hA5 hN
  obtain ⟨hlo, hNat⟩ := hcl
  have hA := hG.tot
  have hX0 := decOK_JMU arI s ar σ J hG hE ct hct lbl length blk call don fp buf extra slbl argsU hlen hargs
    hbuf hl ci sl hsl c hc excaps buffer hXO hXN hLb hA5 hN hPD hR hVT hVI hNs
  have hAs : AbsSlot Z.th sl := by
    obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
  cases c <;> simp only [LoudF] at hlo
  case IoPort first last z =>
    exact XCapP.mr hM hX0 (MKD.decode_ioport L.total hA hKD hIo hR)
      (fun inv hd => MachT.dec_quiet fp slbl _ ci sl _ excaps buffer (by simp [absCap, MachT.QuietS]) σ _ hd.1 inv rfl)
  case IrqHandler irq =>
    have hirq : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    subst hLb
    exact XCapP.mrG (f := fun ms => if lbl = fl4_abi.label.IRQAckIRQ then unmaskMs ms irq else ms) hM hX0 (MKD.decode_irq_handler_mr L.total hA hKD (hDL.2 sl irq hsl hc hirq hR) hR)
      (perfF_irqH irq hirq lbl σ blk call don fp _ ci sl excaps buffer)
  case IrqControl =>
    subst hLb
    have hPl : Placed Z.th := J.xtop.rel.1
    have hex := ExtraOK.rel1 hPl hXO
    obtain ⟨nA, hnum, hnA⟩ := hE.ioapics
    obtain ⟨sl1, idxs⟩ := sl
    obtain ⟨p0, hp0, hth0⟩ := hsl
    try simp only at hp0 hth0
    subst hp0
    obtain ⟨hcur, -⟩ := J.curEq hct
    exact (decode_invocation_irq_controlXSM arI Z.th s ar σ Z.G J.intL hE.handlers lbl lbl.bv (irqControl_label lbl)
      (irqControl_remap lbl) length buf ct hct argsU hlen hargs hcur J.kern.act J.act2 extra _ (exAt_idx0 extra) excaps
      hex hth0 rfl hc nA hnum hnA (maskIrq_total arI hA) hE.archIrq rfl rfl J.xtop (J.curRun.run hE.ni) _
      ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩
      (fun _ _ _ h => Steps.jat arI hG.ari.toMask (jStepHyps arI) h rfl J (J.zNoBlk hE.sg)) (fun _ _ _ h => JAt.xtop arI h)
      blk call don fp ci buffer hM.mask (fun a ms ms' h e => mF_mr hM h e) hR hIoa).toPN arI (specDec_noPreK (by trivial))
  all_goals
    exact hDL.1 hR hVT hVI lbl length blk call don fp buf extra slbl argsU hlen hargs hbuf hl ci sl hsl _ hc
      ⟨trivial, hNat⟩ excaps buffer hXO hXN hLb hA5 hN

end


/-! ## Every native dispatch with `MR` at the chosen outcome -/

/-! ## The tops -/

end

end Fl4Proofs.P3
