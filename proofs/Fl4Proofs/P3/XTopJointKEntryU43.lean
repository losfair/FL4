/-
P3 (line p3J, gen 11): **`kernel_entry_reachU43`** = `kernel_entry_reachU42` without the per-entry
`ArchSwFT` [P] (the thread half of `ArchSwF`), which is now a theorem from opaque-operation facts.

* ArchSwThr: **`archSwFT_of : FpuImplDet → FpuWriteDet → P0.ArchTotal ar → ArchSwFT st ar N T C c`** at
  every ghost set. `ArchSwFT`'s post says nothing about CR3, so no `StateRel` / `VsRel` at the scheduler's
  intermediate states is needed: FL4's `set_vm_root` keeps the store and is total; the spec's `setVmRoot`
  has one outcome by `VsRootOK` (already `ArchSwFT`'s guard) and the TCB from `SchedRel`; the spec's
  `lazyFpuRestore` has one outcome given that the three opaque FPU machine operations it can run
  (`enableFpuImpl`, `disableFpuImpl`, `writeFpuStateImpl`) have at most one outcome each.
* `KFinAtR42` has the single field `arch : ArchSwFT`, so `kFinAtR42_of` / `kFinEv42_of` supply every
  per-entry `KFinAtR42` / `KFinEv42` premise of U42.
* **Premise diff U42 → U43**: the syscall clause's `(∀ x ∈ (specFront c σ).1, … → KFinAtR42 …) →` and the
  five event clauses' `KFinEv42 …` premises are **removed**; one global premise is **added**:
  `hFW : FpuWriteDet` [P] (Fl4Spec `opaque writeFpuStateImpl`, l4v `MachineOps.X64.writeFpuState_impl`,
  `consts'`: at most one outcome; the same shape as U41's `hFpu : FpuImplDet`, which does not cover this
  operation). `hFpu : FpuImplDet` is reused unchanged. Start (`JReachU40`) and conclusion verbatim. [W] 0.
  Why `FpuWriteDet` cannot be avoided: in `lazyFpuRestore`'s owner-switch branch the spec runs
  `writeFpuStateImpl` on the new owner's image; if it had two outcomes `archSwitchToThread` would have two,
  and `ArchSwFT` asks for exactly one (it is not derivable from U42's premises; it is a fact about an
  opaque constant, not about FL4).
* **`kernel_entry_reachU42_of43`**: U42's statement verbatim plus `hFW : FpuWriteDet`, from U43 (the
  dropped premises are ignored). As gen 8's `kernel_entry_reachU40_of41` (+ `hFpu`).

Named premises: U42's (XTopJointKEntryU42) minus `KFinAtR42.arch : ArchSwFT` [P] (per entry), plus
`FpuWriteDet` [P] (global, opaque constant). Remaining per-entry premises unchanged from
U42: `KDispHypsKVU39` [J], `JDecMRLK` [J]. No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU42
import Fl4Proofs.P3.ArchSwThr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- Every `KFinAtR42` from the opaque FPU premises and `ArchTotal` (`archSwFT_of`). -/
theorem kFinAtR42_of (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hA : P0.ArchTotal arI)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} : KFinAtR42 (L := L) arI AR Z H Cs s a σ :=
  ⟨archSwFT_of hFpu hFW hA⟩

/-- Every `KFinEv42` from the opaque FPU premises and `ArchTotal`. -/
theorem kFinEv42_of (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hA : P0.ArchTotal arI)
    {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop} {σ : Fl4Spec.State Unit} :
    KFinEv42 (L := L) arI AR ev Kf σ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => kFinAtR42_of hFpu hFW hA

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU43`** (module docstring). -/
theorem kernel_entry_reachU43 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
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
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU42 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL
    exact hSys n c hct hn hfl hK hDL (fun _ _ _ _ _ _ _ _ _ _ _ _ => kFinAtR42_of hFpu hFW hA)
  · intro w a1 hIh; exact hIrq w a1 hIh (kFinEv42_of hFpu hFW hA)
  · intro n c hct hU; exact hUs n c hct hU (kFinEv42_of hFpu hFW hA)
  · intro ad c ft hct hVm'; exact hVm ad c ft hct hVm' (kFinEv42_of hFpu hFW hA)
  · intro v hct hv; exact hTr v hct hv (fun _ _ _ _ => (kFinEv42_of hFpu hFW hA))
  · intro n hct hU hD; exact hSU n hct hU hD (fun _ _ _ _ => (kFinEv42_of hFpu hFW hA))


end

end

end Fl4Proofs.P3.SInvR.G5
