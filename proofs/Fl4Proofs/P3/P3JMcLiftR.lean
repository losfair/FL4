/-
P3 (p3J gen 25): **the other five clause tops on `RunMcWKR`** (`RunMcWK ∧ NoSig ∧ RR`, P3JMcIrqRQ).

Gen 23's `kernel_entry_runMcWK_userWC` / `_vmfWC` / `_sysUWC` / `_trapWC` (outcomes `EvOut`) lift by
`runMcWKR_of`; `_sysWC` (outcome in `fl4KernelEntrySyscall`) by **`runMcWKR_sys`** (P3JNsSys's `kentry_noSig`,
P3JRrSys's `kentry_rr`). With `kernel_entry_runMcWKR_irqJ` all six clauses map `RunMcWKR` to `RunMcWKR`, and
`runMcWKR_w2` starts the run at the 2-core boot witness. Premises: exactly gen 23's per clause (`UserFootWC`,
`VmfFootWC`, `SysUFootWC`, `TrapFootWC`, `SysStabC`, `SysFootWC` [J]) and its globals; nothing new.

No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcIrqRQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- A syscall-entry outcome of a `RunMcWKR` state that is `RunMcWK` is `RunMcWKR`. -/
theorem runMcWKR_sys {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit} {c : Fl4Spec.Syscall}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) (hy : ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1)
    (hR' : RunMcWK (L := L) arI AR MR s' a' σ') : RunMcWKR (L := L) arI AR MR s' a' σ' :=
  ⟨⟨hR', SInvNs.kentry_noSig true c hR.1.1.1.1.2 hR.1.2 _ hy⟩, SInvRr.kentry_rr true c hR.1.1.1.1.2 hR.2 _ hy⟩

/-- **The user-exception entry, `RunMcWKR` to `RunMcWKR`** (`hFt` [J], gen 23). -/
theorem kernel_entry_runMcWKR_userWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hFt : UserFootWC (L := L) arI AR MR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c h1 h2
  refine WP.spec_mono (kernel_entry_runMcWK_userWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu
    hFW hR.1.1 hFt n c h1 h2) ?_
  rintro r ⟨σ', hO, hR'⟩
  exact ⟨σ', hO, runMcWKR_of hR hO hR'⟩

/-- **The VM-fault entry, `RunMcWKR` to `RunMcWKR`** (`hFt` [J], gen 23). -/
theorem kernel_entry_runMcWKR_vmfWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hFt : VmfFootWC (L := L) arI AR MR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro ad c ft h1 h2
  refine WP.spec_mono (kernel_entry_runMcWK_vmfWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu
    hFW hR.1.1 hFt ad c ft h1 h2) ?_
  rintro r ⟨σ', hO, hR'⟩
  exact ⟨σ', hO, runMcWKR_of hR hO hR'⟩

/-- **The unknown-syscall entry, `RunMcWKR` to `RunMcWKR`** (`hFt` [J], gen 23). -/
theorem kernel_entry_runMcWKR_sysUWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hFt : SysUFootWC (L := L) arI AR MR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n h1 h2 h3
  refine WP.spec_mono (kernel_entry_runMcWK_sysUWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu
    hFW hR.1.1 hFt n h1 h2 h3) ?_
  rintro r ⟨ev, σ', hK, hO, hR'⟩
  exact ⟨ev, σ', hK, hO, runMcWKR_of hR hO hR'⟩

/-- **The `int $N` entry, `RunMcWKR` to `RunMcWKR`** (`hFt` [J], gen 23). -/
theorem kernel_entry_runMcWKR_trapWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hFt : TrapFootWC (L := L) arI AR MR s a σ) :
    ∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
      syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro v h1 h2
  refine WP.spec_mono (kernel_entry_runMcWK_trapWC hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hDR hFpu hFW
    hR.1.1 hFt v h1 h2) ?_
  rintro r ⟨ev, σ', hK, hO, hR'⟩
  exact ⟨ev, σ', hK, hO, runMcWKR_of hR hO hR'⟩

/-- **The native syscall entry, `RunMcWKR` to `RunMcWKR`** (`hSS`, `hFt` [J], gen 23). -/
theorem kernel_entry_runMcWKR_sysWC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hSS : SysStabC (L := L) arI AR MR s a σ) (hFt : SysFootWC (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c h1 h2 h3 h4
  refine WP.spec_mono (kernel_entry_runMcWK_sysWC hR.1.1 hSS hFt n c h1 h2 h3 h4) ?_
  rintro r ⟨σ', hy, hR'⟩
  exact ⟨σ', hy, runMcWKR_sys hR hy hR'⟩

end

end Fl4Proofs.P3.Mc
