/-
P3 (p3J gen 27): **stage Q of the fault entries' footprints; the user-exception, VM-fault, unknown-syscall and
`int $N` clauses on `RunMcWKR` with no footprint premise.**

* P3JMcFlt's `jEvRef_userFt` / `jEvRef_vmfFt` and P3JMcFltS's `jEvRef_sysUFt` / `jEvRef_trapFt` at the multicore
  tops' globals (collapse A, Q: on the narrowed `MachPlat` / `IrqPlatA` themselves; the stage-Q transport copies
  `Fl4ProofsQ.P3.…` this module made are gone).
* **`userFootWC_holdsR`**, **`vmfFootWC_holdsR`**, **`sysUFootWC_holdsR`**, **`trapFootWC_holdsR`**: gen 23's
  `UserFootWC` / `VmfFootWC` / `SysUFootWC` / `TrapFootWC` [J] hold at every `RR` state (with globals the
  clause tops already take); `SInvX`, `MR` and `CKI` from `RunMcWK`'s `RunCK` (`jreach_invU3`).
* **`kernel_entry_runMcWKR_user`**, **`_vmf`**, **`_sysU`**, **`_trap`**: P3JMcLiftR's `…WC` tops with the
  footprint premise discharged — each clause `RunMcWKR` → `RunMcWKR` with U45nv's globals only.

No premise beyond the stated hypotheses; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcFltS
import Fl4Proofs.P3.P3JMcLiftR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`UserFootWC` [J] holds at every `RR` state** (module docstring). -/
theorem userFootWC_holdsR (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRR : SInvRr.RR σ) :
    UserFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n c hct hU
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hMR, -, -, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_userFt J hX hct hMR hCK hRR n c hU hARI hA hnd
    (MachPlatF.toT hM hIp) hKD (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **`VmfFootWC` [J] holds at every `RR` state** (module docstring). -/
theorem vmfFootWC_holdsR (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRR : SInvRr.RR σ) :
    VmfFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV ad c ft hct hVm
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hMR, -, -, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_vmfFt J hX hct hMR hCK hRR ad c ft hVm hARI hA hnd
    (MachPlatF.toT hM hIp) hKD (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **`SysUFootWC` [J] holds at every `RR` state** (module docstring). -/
theorem sysUFootWC_holdsR (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hSX : P1.StoreExt st)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRR : SInvRr.RR σ) :
    SysUFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n hct hU hD
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hMR, -, -, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_sysUFt hnd n J hX hct hMR hCK hRR hU hD hSX hARI hA
    (MachPlatF.toT hM hIp) hKD (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ _ _ => hr

set_option maxHeartbeats 4000000 in
/-- **`TrapFootWC` [J] holds at every `RR` state** (module docstring). -/
theorem trapFootWC_holdsR (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR) (hKD : MRKeepD arI MR)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRR : SInvRr.RR σ) :
    TrapFootWC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV v hct hv
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, hMR, -, -, -⟩ := jreach_invU3 hnd hJ17.1
  haveI := hV
  exact WP.spec_mono (Fl4Proofs.P3.jEvRef_trapFt hnd v hv J hX hct hMR hCK hRR hARI hA
    (MachPlatF.toT hM hIp) hKD (fun a => hT.mrt a) hT.mb hmax htu) fun r hr _ _ _ _ => hr

/-- **The user-exception entry, `RunMcWKR` to `RunMcWKR`, with no footprint premise** (module docstring). -/
theorem kernel_entry_runMcWKR_user [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_userWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (userFootWC_holdsR hARI hA hnd hM hIp hKD hT hmax htu s a σ hR.2)

/-- **The VM-fault entry, `RunMcWKR` to `RunMcWKR`, with no footprint premise** (module docstring). -/
theorem kernel_entry_runMcWKR_vmf [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_vmfWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (vmfFootWC_holdsR hARI hA hnd hM hIp hKD hT hmax htu s a σ hR.2)

/-- **The unknown-syscall entry, `RunMcWKR` to `RunMcWKR`, with no footprint premise** (module docstring). -/
theorem kernel_entry_runMcWKR_sysU [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysUWC hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR
    (sysUFootWC_holdsR hARI hA hnd hM hIp hKD hT hmax htu hSX s a σ hR.2)

/-- **The `int $N` entry, `RunMcWKR` to `RunMcWKR`, with no footprint premise** (module docstring). -/
theorem kernel_entry_runMcWKR_trap [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
      syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_trapWC hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hDR hFpu hFW hR
    (trapFootWC_holdsR hARI hA hnd hM hIp hKD hT hmax htu s a σ hR.2)

end

end Fl4Proofs.P3.Mc
