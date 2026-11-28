/-
P3 (line irqfix, gen 3): **`kernel_entry_reachU36I`**: U34's statement with a start condition that FL4's real
boot state can meet.

* U34's `JReachU34 := JReachU17 ∧ IrqStB` is false at FL4's boot (lines 126 / 127 `IRQ_IPI` ↦ `irqReserved`;
  jboot gen 6 `irqStB_false_of_ipiWord`). **`JReachU36I s a σ := JReachU17 s a σ ∧ IrqCarry σ`** with
  `IrqCarry σ := IrqStB σ ∨ (IrqStS σ ∧ ValidIrqHandlersL σ)` (SpecInvIrqStS): `IrqStS` asks only that no line
  above `maxIRQ` is `IRQSignal`, and `ValidIrqHandlersL` is l4v's own `valid_irq_handlers` (handler caps on
  `IRQSignal` lines, SpecInvVihL..S, kept by every spec entry). Either disjunct with the port's
  `ValidIrqHandlers` gives `IrqCapBound` (`IrqCarry.capBound`), hence U34's `IrqAckU` discharge.
* Start-condition evidence: `JReachU36I.of_noHandler` (`JReachU17` at a state with no handler cap and `IrqStS`),
  `JReachU36I.of_U34` (every U34 start state), SpecInvIrqStS's `fInitIpi_irqCarry` (lines 125 timer, 126 / 127
  reserved) and `irqStS_of_irqRel` (FL4's boot IRQ words).
* **`kernel_entry_reachU34_of36I`**: U34's statement re-derived from `kernel_entry_reachU36I` alone (plus gen 2's
  spec-only `IrqStB` preservation for the exits), not from U34 / U33.

**Premise diff U34 → U36I**: `hJ : JReachU34` ↦ `hJ : JReachU36I` (weaker: `JReachU36I.of_U34`); conclusion
U34's with every exit's `JReachU34` ↦ `JReachU36I`. Every other premise verbatim ([P] `MachPlatF`, `IpiF`,
`IrqPlatK`, … as U34; [J] the syscall clause's `KDispHypsKVU32` / `JDecMRLK` / `KFinAtR13`, the events' `KFinEv13`
as U34). New premises: none ([J] 0, [P] 0, [W] 0). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU34
import Fl4Proofs.P3.SpecInvIrqStS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- The carried fact at the dispatch state. -/
theorem BudgetAt.irqCarry {σ σb : Fl4Spec.State Unit} (hm : SInvV.ValidIrqMasks σ) (h : SInvIB.IrqCarry σ)
    (hb : BudgetAt σ σb true) : SInvIB.IrqCarry σb := by
  obtain ⟨σ0, h0, hb⟩ := hb
  exact SInvIB.budget_irqCarry _ hm h h0 _ hb

/-- The carried fact at every `EvOut` outcome. -/
theorem EvOut.irqCarry {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (hm : SInvV.ValidIrqMasks σ)
    (h : SInvIB.IrqCarry σ) (hO : EvOut fip ev σ σ') : SInvIB.IrqCarry σ' := by
  cases fip with
  | false => exact SInvIB.kcall_irqCarry true ev hm h _ hO
  | true =>
    obtain ⟨w, hw, hO⟩ := hO
    exact SInvIB.fipcall_irqCarry true ev _ hm h hw _ hO

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with irqfix gen 3's carried IRQ fact** (module docstring). -/
abbrev JReachU36I (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInvIB.IrqCarry σ

/-- **`IrqCapBound` at every `JReachU36I` state with `SInvX`** (so at every exit of U36I). -/
theorem JReachU36I.irqCapBound {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hJ : JReachU36I (L := L) arI AR MR s a σ) (hX : SInvX σ) : SInvIB.IrqCapBound σ :=
  SInvIB.IrqCarry.capBound hX.sb.1.1.vih hJ.2

/-- Every U34 start state is a U36I start state. -/
theorem JReachU36I.of_U34 {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ) :
    JReachU36I (L := L) arI AR MR s a σ := ⟨hJ.1, Or.inl hJ.2⟩

/-- **`JReachU17` at a state with no IRQ handler cap and no `IRQSignal` line above `maxIRQ` is a U36I start
state** (FL4's boot: lines 125 timer, 126 / 127 reserved, no handler cap). -/
theorem JReachU36I.of_noHandler {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ)
    (hn : ∀ p cref irq, capOpt (σ.kheap p) cref ≠ some (Fl4Spec.Cap.irqHandlerCap irq)) (hs : SInvIB.IrqStS σ) :
    JReachU36I (L := L) arI AR MR s a σ := ⟨hJ, SInvIB.irqCarry_of_noHandler hn hs⟩

/-- At jboot's state with FL4's boot IRQ states (`fInitIpiASt`). -/
theorem JReachU36I.of_fInitIpi {s : S} {a : A} (hJ : JReachU17 (L := L) arI AR MR s a SInvIB.fInitIpiASt) :
    JReachU36I (L := L) arI AR MR s a SInvIB.fInitIpiASt := ⟨hJ, SInvIB.fInitIpi_irqCarry⟩

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU36I`** (module docstring): U34 from `JReachU36I`. -/
theorem kernel_entry_reachU36I [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU32 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ' ⦄)
  := by
  obtain ⟨hJ17, hB⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU33 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ17
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  have hh := hX.sb.1.1.vih
  have hm := hX.sb.1.1.vim
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, SInvIB.IrqCarry.capBound hh hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK (fun σb hb V' Ac' Lst' D' s' a' hF J' ct' hct' =>
      ⟨hDL σb hb V' Ac' Lst' D' s' a' hF J' ct' hct',
        irqAckU_of_capBound hM J' (SInvIB.IrqCarry.capBound (vih_disp hnd hk hb hh) (BudgetAt.irqCarry hm hB hb))⟩)
      hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ', SInvIB.kentry_irqCarry true c hm hB _ hσ'⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqCarry hm hB hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqCarry hm hB hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqCarry hm hB hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqCarry hm hB hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqCarry hm hB hO⟩


end

end

end Fl4Proofs.P3.SInvR.G5
