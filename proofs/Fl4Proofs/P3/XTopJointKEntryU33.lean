/-
P3 (line irqfix): **`kernel_entry_reachU33`**: `kernel_entry_reachU32` with the platform record split into
`MachPlatF` + `IpiF` and the syscall clause's decode premise written as `JDecMRLK ∧ IrqAckU` (JBootIpi's finding:
the old, un-narrowed `MachPlat` and `IrqPlatA` with one `MR` pair forced the opaque `irqOracle` off the IPI
vectors).

Collapse A, Q wrote irqfix's `MachPlatT` / `IrqPlatK` back into `MachPlat` / `IrqPlatA`, and U32's cone now
carries `JDecMRLKQ` (= `JDecMRLK ∧ IrqAckU`) where irqfix's transport (IrqFixGen) put it. So U33 is U32 itself
with `hM : MachPlat` given as `MachPlatF.toT hM hIp`:
* `hM : MachPlatF arI MR` [P]: masking any line `< 256`, unmasking only lines `≤ maxIRQ = 125`;
* `hIp : IpiF arI MR` [P]: `take_pending_irq` gives no IPI vector from an `MR`-related state;
* `hIA : IrqPlatA arI AR` [P] (`IrqPlatA` without `noIpi` since collapse A, Q);
* the syscall clause's per-entry decode premise `JDecMRLK … VtxK … ∧ IrqAckU …` [J] (XTopJointKEntry39): at the
  dispatch state, unmasking the line of an IRQ handler cap in a CNode slot keeps `MR`. Needed by the IRQ ack
  (`IRQAckIRQ`, FL4 `mask_irq irq false`): FL4's handler cap only bounds `irq < 128`, and nothing U32 carries
  bounds it by `maxIRQ` (l4v `valid_cap`; SpecInvG5's `SpecIrqH` is not preserved anywhere).
  `IrqAckU.of_bound`: under `MachPlatF`, l4v's bound `irq ≤ 125` gives it (U34 discharges it so).
Every other premise and the conclusion are U32's verbatim. [W] 0.

**The model meets U33's platform premises with no oracle assumption** (`modelArch_u33Plat`, at `ipiMR` =
`modelMR` with 126, 127 masked: `MachPlatF`, `IpiF`, `MRKeepD`, `MRKeepIo`, `MRKeepIoapic`; `modelArch_irqAckU`
from the handler-cap bound). (Collapse A, Q removed `kernel_entry_reachU32_of33`, the Rule-3 implication from the
un-narrowed U32, with the old records.)

**Proof**: `kernel_entry_reachU32` at `MachPlatF.toT hM hIp` (before collapse A, Q: IrqFixGen's transported copy
`Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32`).
-/
import Fl4Proofs.P3.XTopJointKEntryU32
import Fl4Proofs.P3.JBootIpi
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **The model arch meets U33's new platform premises at `ipiMR`, whatever the oracle**
(`MachPlatF`, `IpiF`: JBootIpi; the three keep records: the model's ops leave the state). -/
theorem modelArch_u33Plat :
    MachPlatF modelArch ipiMR ∧ IpiF modelArch ipiMR ∧ MRKeepD modelArch ipiMR ∧
      MRKeepIo modelArch ipiMR ∧ MRKeepIoapic modelArch ipiMR :=
  ⟨modelArch_machPlatF, modelArch_ipiF, modelArch_mrKeepD ipiMR,
    ⟨fun _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h,
     fun _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h⟩,
    ⟨fun _ _ _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h,
     fun _ _ _ _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h⟩⟩

/-- **`IrqAckU` for the model at `ipiMR`** from l4v `valid_cap`'s handler bound (`irq ≤ maxIRQ`). -/
theorem modelArch_irqAckU {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {Z : XSets} {s : S}
    {a : Fl4Spec.MachineState} {σ : Fl4Spec.State Unit}
    (hB : ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val ≤ 125) :
    IrqAckU (L := L) modelArch ipiMR Z s a σ :=
  IrqAckU.of_bound modelArch_machPlatF hB

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`kernel_entry_reachU33`** (module docstring): `kernel_entry_reachU32` with `MachPlatF` + `IpiF` for
`MachPlat` and the syscall clause's decode premise as `JDecMRLK ∧ IrqAckU` (= `JDecMRLKQ`). -/
theorem kernel_entry_reachU33 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
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
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct' ∧
                IrqAckU (L := L) arI MR (Z.mv Z.G V') s' a' σb) →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.1 r.2 σ' ⦄)  := by
  exact Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU32 arI AR MR hARI hA hnd (MachPlatF.toT hM hIp) hKD hIo hIoa
    hPAi hIA hT hmax htu hRef hPI hSX hDR hJ


end

end

end Fl4Proofs.P3.SInvR.G5
