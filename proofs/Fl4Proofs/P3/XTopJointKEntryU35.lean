/-
P3 (line p3J, gen 1): **`kernel_entry_reachU35`** = `kernel_entry_reachU34` with two fields of the
syscall clause's per-entry `KDispHypsKVU32` discharged (inventory: `WS/handoff/p3J.md`).

* **`ArchIrqRelN.num`** (E2) is `JEntryAtR7T.ioapics` (E1) restated: the same proposition.
* **`ArchIrqRelN.mask`** (E6, `∀ a irq b, ∃ a', mask_irq a irq b = ok a'`) is
  `P0.ArchTotal.mask_irq`, U34's own premise `hA`.

`JEntryAtR7V` = `JEntryAtR7T` without those two; `KDispHypsKVU35` = `KDispHypsKVU32` with
`JEntryAtR7V` in both `inv` and `mid`. `KDispHypsKVU35.toU32` (from `hA`) and `KDispHypsKVU32.toU35`
(dropping fields).

**Premise diff U34 → U35**: in the syscall clause, `KDispHypsKVU32 …` ↦ `KDispHypsKVU35 …`, i.e.
`JEntryAtR7T.archIrq.num` and `JEntryAtR7T.archIrq.mask` removed (in `inv` and `mid`). Every other
premise, every other clause and the conclusion verbatim. No new premise. [W] 0.
**`kernel_entry_reachU34_of35`** proves U34's statement, verbatim, from U35.

Named premises still open in U35 (all inherited, statement-level, unchanged):
* [P] `JEntryAtR7V.ioapics` (IOAPIC count = spec `x64NumIoapics`), `.pins` (pin counts = spec
  `x64IoapicNirqs`), `.map` / `.mapr` (in-range routing succeeds with `true`);
* `JPathAtMU30` ([P]/[S] SchedControl `cpu = Z.c`; untyped `fan`, `core0`, `rcb` [P]; `vtx` [scope];
  Thread SetEPTRoot and EPT-frame `JVtxScope` [scope]);
* [J]/[scope] `JDecMRLK … VtxK …`; [P] `KFinAtR13` (`ArchSwF`, `ArchNdF`); the global [P] premises of U34.
The p3J inventory records which of these are false at reachable entries (the ∀-slot form of
`JPathAtMU30`): they are kept, not weakened.
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU34
import Fl4Proofs.P3.CnodeCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JEntryAtR7T` without `archIrq.num` (= `ioapics`) and `archIrq.mask` (from `ArchTotal`).** -/
structure JEntryAtR7V (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) :
    Prop where
  /-- [P] `JEntryAt.ioapics`: the backend's IOAPIC count is the spec's `x64NumIoapics`. -/
  ioapics : ∃ nA, arI.num_ioapics ar = ok nA ∧ nA.bv = σ.archState.x64NumIoapics
  /-- [P] `ArchIrqRelN.pins`: each IOAPIC's pin count is the spec's `x64IoapicNirqs`, at least one. -/
  pins : ∀ n, arI.num_ioapics ar = ok n → ∀ i : U64, i.val < n.val →
    ∃ p, arI.ioapic_pins ar i = ok p ∧ p.val = (σ.archState.x64IoapicNirqs i.bv).toNat ∧ 0 < p.val
  /-- [P] `ArchIrqRelN.map`: in-range IOAPIC routing succeeds and routes (`true`). -/
  map : ∀ (a : A) (n i p l po v np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ∃ a', arI.ioapic_map a i p l po v = ok (true, a')
  /-- [P] `ArchIrqRelN.mapr`: the remapped form. -/
  mapr : ∀ (a : A) (n i p l po v h np : U64), arI.num_ioapics a = ok n → ¬ i >= n → arI.ioapic_pins a i = ok np →
    ¬ p >= np → ¬ l > 1#u64 → ¬ po > 1#u64 → ¬ h >= 65536#u64 →
    ∃ a', arI.ioapic_map_remapped a i p l po v h = ok (true, a')

/-- **`KDispHypsKVU32` with `JEntryAtR7V`.** -/
structure KDispHypsKVU35 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  /-- [P]/[J] as `KDispHypsKVU32.inv` without the two discharged fields. -/
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  /-- [P]/[J] as `KDispHypsKVU32.mid` without the two discharged fields. -/
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR7V arI AR Z s a σ ∧
    JPathAtMU30 (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `JEntryAtR7T` from `JEntryAtR7V` and `ArchTotal` (`num` is `ioapics`, `mask` is total). -/
theorem JEntryAtR7V.toT (hA : P0.ArchTotal arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (h : JEntryAtR7V arI AR Z s ar σ) : JEntryAtR7T arI AR Z s ar σ :=
  ⟨h.ioapics, ⟨h.ioapics, h.pins, h.map, h.mapr, fun a irq b => by
    obtain ⟨v, hv, -⟩ := spec_exists (hA.mask_irq a irq b)
    exact ⟨v, hv⟩⟩⟩

/-- `JEntryAtR7V` from `JEntryAtR7T` (fields dropped). -/
theorem JEntryAtR7T.toV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (h : JEntryAtR7T arI AR Z s ar σ) : JEntryAtR7V arI AR Z s ar σ :=
  ⟨h.ioapics, h.archIrq.pins, h.archIrq.map, h.archIrq.mapr⟩

/-- **`KDispHypsKVU35` gives `KDispHypsKVU32`** under `ArchTotal`. -/
theorem KDispHypsKVU35.toU32 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c) (hA : P0.ArchTotal arI) :
    KDispHypsKVU32 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toT hA, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toT hA, (h.mid ct rg sr cr hct hm).2⟩⟩

/-- **`KDispHypsKVU32` gives `KDispHypsKVU35`.** -/
theorem KDispHypsKVU32.toU35 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S}
    {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHypsKVU32 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKVU35 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => ⟨(h.inv ct call bl don hct hi).1.toV, (h.inv ct call bl don hct hi).2⟩,
   fun ct rg sr cr hct hm => ⟨(h.mid ct rg sr cr hct hm).1.toV, (h.mid ct rg sr cr hct hm).2⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU35`** (module docstring): U34 with the syscall clause's per-entry
`KDispHypsKVU32` narrowed to `KDispHypsKVU35` (no `ArchIrqRelN.num`, no `ArchIrqRelN.mask`). -/
theorem kernel_entry_reachU35 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU35 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
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
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU34 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, hSys, hRest⟩ :=
    kernel_entry_reachU34 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hB, hW, hI, hN, hR, hFl, hPg, ?_, hRest⟩
  intro n c hct hn hfl hK hDL hFin
  exact hSys n c hct hn hfl
    (fun σb hb V' Ac' Lst' D' s' a' hF J' => (hK σb hb V' Ac' Lst' D' s' a' hF J').toU32 hA) hDL hFin


end

end

end Fl4Proofs.P3.SInvR.G5
