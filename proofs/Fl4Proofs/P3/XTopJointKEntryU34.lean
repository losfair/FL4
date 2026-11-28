/-
P3 (line irqfix, gen 2): **`kernel_entry_reachU34`**: `kernel_entry_reachU33` without its per-entry [J]
`IrqAckU`, by l4v `valid_cap`'s IRQ handler bound carried with the reachable states.

* **`JReachU34 s a σ := JReachU17 s a σ ∧ IrqStB σ`** (a new top-level wrapper; `JReachU17` unchanged):
  every IRQ line above `maxIRQ` is inactive (SpecInvIrqBoundKit). With `SInvX`'s `ValidIrqHandlers` it gives
  **`IrqCapBound σ`** (l4v `valid_cap` for `IRQHandlerCap`, Invariants_AI `valid_cap_def`: `irq ≤ maxIRQ`),
  stated in U34's entry conjunct. `IrqStB` is kept by every spec entry (SpecInvIrqBound: `kentry_irqStB`,
  `kcall_irqStB`, the FaultIP write and the budget front: `EvOut.irqStB`, `BudgetAt.irqStB`) and holds at
  boot (`initASt` / jboot's `fInitASt`: every line inactive; `fInit_irqCapBound`: no handler cap at all).
* **`irqAckU_of_capBound`**: at a `JAtZ` state, `IrqCapBound` bounds FL4's handler cap in a CNode slot
  (`StateRel.abs_cap`: the slot's spec cap is `absCap (.IrqHandler irq) = irqHandlerCap (ofNat 8 irq)`,
  `CapWf`: `irq < 128`), so `IrqAckU.of_bound` gives `IrqAckU` under `MachPlatF`.

**Premise diff U33 → U34**: the syscall clause's `JDecMRLK … ∧ IrqAckU …` [J] ↦ `JDecMRLK …` (U32's form);
`hJ : JReachU17` ↦ `hJ : JReachU34` (start condition `IrqStB`, true at boot). Conclusion: U33's with
`IrqCapBound σ` added after `SInvX σ` and every exit's `JReachU17` ↦ `JReachU34`. Every other premise verbatim
([P] `MachPlatF`, `IpiF`, `IrqPlatK` as U33). [W] 0.
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU33
import Fl4Proofs.P3.SpecInvIrqBound
import Fl4Proofs.P3.JBootSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **`IrqCapBound` at jboot's witness `fInitASt`**: it holds no IRQ handler cap (its objects are `initASt`'s
and empty IRQ CNodes). -/
theorem fInit_irqCapBound : SInvIB.IrqCapBound JBoot.fInitASt := by
  intro p cref irq hc
  exfalso
  have hb : ∀ q, capOpt (Fl4Spec.initKheap q) cref ≠ some (.irqHandlerCap irq) :=
    fun q h => SInvV.boot_vih q cref irq h rfl
  change capOpt (JBoot.fInitKheap p) cref = some (.irqHandlerCap irq) at hc
  simp only [JBoot.fInitKheap, Function.update_apply] at hc
  split_ifs at hc
  all_goals first
    | exact hb _ hc
    | (simp only [capOpt, Fl4Spec.emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp [capOpt] at hc; done)

/-- `IrqStB` at jboot's witness (every line inactive, as `initASt`). -/
theorem fInit_irqStB : SInvIB.IrqStB JBoot.fInitASt := fun _ _ => rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`IrqAckU` from l4v's handler bound** at a `JAtZ` state (module docstring). -/
theorem irqAckU_of_capBound (hM : MachPlatF arI MR) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hB : SInvIB.IrqCapBound σ) :
    IrqAckU (L := L) arI MR Z s a σ :=
  IrqAckU.of_bound hM fun sl irq hsl hc => by
    have hAs : AbsSlot Z.th sl := by
      obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
    have hwf : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    obtain ⟨c', ac, hc', hcr, hg⟩ := J.xtop.rel.2.1.1.abs_cap hAs
    rw [hc] at hc'; cases eq_of_ok_eq hc'
    have hco : capOpt (σ.kheap sl.1) sl.2 = some ac :=
      (getCap_set_iff σ sl.1 sl.2 ac).1 (congrArg Prod.fst hg)
    have hco' : capOpt (σ.kheap sl.1) sl.2 = some (.irqHandlerCap (BitVec.ofNat 8 irq.val)) :=
      hco.trans (by rw [← hcr.2]; try rfl)
    have h1 := hB _ _ _ hco'
    have h2 : irq.val % 256 ≤ 125 := by
      have := h1; rw [BitVec.le_def, BitVec.toNat_ofNat] at this; exact this
    omega

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- `IrqStB` at the dispatch state (the FaultIP write and the budget front keep it). -/
theorem BudgetAt.irqStB {σ σb : Fl4Spec.State Unit} (h : SInvIB.IrqStB σ) (hb : BudgetAt σ σb true) :
    SInvIB.IrqStB σb := by
  obtain ⟨σ0, h0, hb⟩ := hb
  exact SInvIB.budget_irqStB (SInvIB.fip_irqStB _ h _ h0) _ hb

/-- `IrqStB` at every `EvOut` outcome. -/
theorem EvOut.irqStB {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (h : SInvIB.IrqStB σ)
    (hO : EvOut fip ev σ σ') : SInvIB.IrqStB σ' := by
  cases fip with
  | false => exact SInvIB.kcall_irqStB true ev h _ hO
  | true =>
    obtain ⟨w, hw, hO⟩ := hO
    exact SInvIB.kcall_irqStB true ev (SInvIB.fip_irqStB _ h w hw) _ hO

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with the IRQ line bound** (module docstring). -/
abbrev JReachU34 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInvIB.IrqStB σ

/-- `IrqCapBound` at every `JReachU34` state with `SInvX` (`ValidIrqHandlers` ∧ `IrqStB`). -/
theorem JReachU34.irqCapBound {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ)
    (hX : SInvX σ) : SInvIB.IrqCapBound σ :=
  SInvIB.irqCapBound_of hX.sb.1.1.vih hJ.2

/-- **JReachU34's extra start fact at the boot states** (`initASt`, jboot's `fInitASt`): `JReachU17` at a
boot state gives `JReachU34`. -/
theorem JReachU34.of_boot {s : S} {a : A} (hJ : JReachU17 (L := L) arI AR MR s a JBoot.fInitASt) :
    JReachU34 (L := L) arI AR MR s a JBoot.fInitASt := ⟨hJ, fInit_irqStB⟩

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU34`** (module docstring): U33 without the syscall clause's `IrqAckU` [J]. -/
theorem kernel_entry_reachU34 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
  obtain ⟨hJ17, hB⟩ := hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU33 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ17
  obtain ⟨x, hk, -⟩ := hX.sb.1.2
  have hh := hX.sb.1.1.vih
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, SInvIB.irqCapBound_of hh hB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK (fun σb hb V' Ac' Lst' D' s' a' hF J' ct' hct' =>
      ⟨hDL σb hb V' Ac' Lst' D' s' a' hF J' ct' hct',
        irqAckU_of_capBound hM J' (SInvIB.irqCapBound_of (vih_disp hnd hk hb hh) (BudgetAt.irqStB hB hb))⟩) hFin) ?_
    rintro r ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ'⟩
    exact ⟨σ', hσ', hRJ, hX', hM', hIo', hNo', hZ', hPg', hJ', SInvIB.kentry_irqStB true c hB _ hσ'⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqStB hB hO⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqStB hB hO⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨σ', hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqStB hB hO⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqStB hB hO⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ'⟩
    exact ⟨ev, σ', hK, hO, hRJ, hX', hM', hIo', hNo', hZ', hJ', EvOut.irqStB hB hO⟩

end

end

end Fl4Proofs.P3.SInvR.G5
