/-
P3 (line p3J, gen 6): **`kernel_entry_reachU40`** = `kernel_entry_reachU39` with irqfix gen 3's start condition:
one top with irqfix3's boot-state fix and p3J's narrowings (U35 … U39).

* **`JReachU40 s a σ := JReachU36I s a σ ∧ IoaRel arI σ`** (`JReachU36I := JReachU17 ∧ IrqCarry`,
  XTopJointKEntryU36I; `IoaRel` [P] start condition, XTopJointKEntryU38).
* **Proof**: as irqfix3's `kernel_entry_reachU36I` (from U33, start `JReachU17`; `IrqCapBound` and the decode
  premise's `IrqAckU` from `IrqCarry`), but from the p3J transport's copy
  `Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU33` (P3JGen: U33 on the narrowed path premises `JPathAtMU35`), the
  syscall clause's `KDispHypsKVU39` brought to the copy's `KDispHypsKVU32` by U39 → U38 (`IoaMap`) → U36
  (`IoaRel` at the dispatch state) → the copy's U35 (`toJ`) → the copy's U32 (`hA`). Exits: `IrqCarry` and
  `IoaRel` kept by every spec step (`SInvIB.kentry_irqCarry`, `EvOut.irqCarry`; `SInvIox.kentry_ioxV`,
  `EvOut.ioaRel`).

**Premise diff U39 → U40**: `hJ : JReachU38` ↦ `hJ : JReachU40` (`JReachU34 ∧ IoaRel` ↦ `JReachU36I ∧ IoaRel`;
weaker: `JReachU36I.of_U34`); conclusion U39's with every exit's `JReachU38` ↦ `JReachU40`. Every other premise
verbatim. New premises: none. [W] 0.

* **`kernel_entry_reachU39_of40`**: U39's statement, verbatim, from U40 (start by `IrqStB ⇒ IrqCarry`; exits'
  `IrqStB` by the spec-only preservation `SInvIB.kentry_irqStB` / `EvOut.irqStB`, as irqfix3's
  `kernel_entry_reachU34_of36I`).
* **`kernel_entry_reachU36I_of40`**: U36I's statement with two more hypotheses, `hMap : IoaMap arI` and
  `hIR : IoaRel arI σ` (U36I asks both only per entry, inside its syscall clause; as gen 4's
  `kernel_entry_reachU36_of38`). The syscall clause by `KDispHypsKVU32.toU35.toU36.toU38.toU39`.
* **`JReachU40.of_fInitIpi`**, **`fInitIpi_ioaStart`**: at irqfix3's `fInitIpiASt` (jboot's boot state with line
  125 `irqTimer`, 126 / 127 `irqReserved`, where `IrqStB` fails) the start's spec half `IrqCarry ∧ IoaRel` holds
  (`fInitIpi_irqCarry`; `IoaRel` framed from `fInitASt`, same `ioxV`); a `JReachU17` there gives `JReachU40`.

Named premises: U39's (XTopJointKEntryU39: U34's global platform [P]s, `IoaMap` [P], the start `JReachU40`
with `IoaRel` [P], the per-entry syscall [J]s `KDispHypsKVU39` / `JDecMRLK` / `KFinAtR13`, the events'
`KFinEv13`). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU39
import Fl4Proofs.P3.XTopJointKEntryU36I
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with irqfix3's carried IRQ fact and the backend's IOAPIC counts** (module
docstring). -/
abbrev JReachU40 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU36I (L := L) arI AR MR s a σ ∧ IoaRel arI σ

variable {arI AR MR} in
/-- Every U39 start state is a U40 start state. -/
theorem JReachU40.of_U38 {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU38 (L := L) arI AR MR s a σ) :
    JReachU40 (L := L) arI AR MR s a σ := ⟨⟨hJ.1.1, Or.inl hJ.1.2⟩, hJ.2⟩

variable {arI} in
/-- **The start's spec half at irqfix3's boot-like state** (126 / 127 reserved): `IrqCarry` and `IoaRel`
(this one from `fInitASt`'s: `fInitIpiASt` changes only the interrupt states). -/
theorem fInitIpi_ioaStart (h : IoaRel arI JBoot.fInitASt) :
    SInvIB.IrqCarry SInvIB.fInitIpiASt ∧ IoaRel arI SInvIB.fInitIpiASt :=
  ⟨SInvIB.fInitIpi_irqCarry, h.frame rfl⟩

variable {arI AR MR} in
/-- **`JReachU17` at `fInitIpiASt` gives the U40 start** under the backend's `IoaRel` at `fInitASt`. -/
theorem JReachU40.of_fInitIpi {s : S} {a : A} (hJ : JReachU17 (L := L) arI AR MR s a SInvIB.fInitIpiASt)
    (h : IoaRel arI JBoot.fInitASt) : JReachU40 (L := L) arI AR MR s a SInvIB.fInitIpiASt :=
  ⟨⟨hJ, SInvIB.fInitIpi_irqCarry⟩, h.frame rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU40`** (module docstring). -/
theorem kernel_entry_reachU40 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU40 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU39 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
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
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨⟨hJ17, hB⟩, hR0⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU33 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu
      hRef hPI hSX hDR hJ17
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  have hh := hX.sb.1.1.vih
  have hm := hX.sb.1.1.vim
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, SInvIB.IrqCarry.capBound hh hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl
      (fun σb hb V' Ac' Lst' D' s' a' hF J' =>
        (((hK σb hb V' Ac' Lst' D' s' a' hF J').toU38 hMap).toU36 (BudgetAt.ioaRel hR0 hb)).toJ.toU32 hA)
      (fun σb hb V' Ac' Lst' D' s' a' hF J' ct' hct' =>
        ⟨hDL σb hb V' Ac' Lst' D' s' a' hF J' ct' hct',
          irqAckU_of_capBound hM J' (SInvIB.IrqCarry.capBound (vih_disp hnd hk hb hh) (BudgetAt.irqCarry hm hB hb))⟩)
      hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', ⟨hJ', SInvIB.kentry_irqCarry true c hm hB _ hσ'⟩,
      hR0.frame (SInvIox.kentry_ioxV true c σ _ hσ')⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', ⟨hJ', EvOut.irqCarry hm hB hO⟩, EvOut.ioaRel hR0 hO⟩



end

end

end Fl4Proofs.P3.SInvR.G5
