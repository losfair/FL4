/-
P3 (p3J gen 19): **the user-exception, VM-fault and unknown-syscall clauses with stable ghosts exposed, at U45nv's
premises**, and the three `RunMcW` clauses with a footprint premise (P3JStIrqTop's route for these clauses).

* **`FootAt Z H Cs s σ s' σ'`**: at every MDB ghost / VSpace sets `G' V'` with `JAtZ (Z.mv G' V') H Cs …` at the
  outcome, the FL4 run writes only `ProjW H Cs s`, `KhNoneKeep σ σ'` and `UtKeep Z.G G' s s'` (P3JStIrqTop's
  `IrqFoot` body). **`runMcW_of_st`**: `RunMcW` at `s`'s ghosts, `RunCK` and `JStab Z H Cs` at the outcome and
  `FootAt` give `RunMcW` there.
* **`user_stabU45`**, **`vmf_stabU45`**, **`sysU_stabU45`**: from `RunCK` and any `JAtZ Z H Cs` (with `VxE Z`),
  under U45nv's globals (subset) and the clause's own case conditions (non-idle; `UserHw` / `VmfHw` [P];
  `UnkSys` ∧ `NoDbgSys`), every outcome is `RunCK` **and** `JStab Z H Cs`. P3JStEvK's `Fl4ProofsK` copies of
  P3JStEv's stage-A lemmas, the finish record from U43 / U42, `JReachU40` / `CKI` at the outcome as in
  `irq_stabU45`. This discharges the ghost half of gen 18's `UserStab` [J] (and of the not yet stated VM-fault /
  unknown-syscall `…Stab`).
* **`UserFoot`**, **`VmfFoot`**, **`SysUFoot`** [J]: `FootAt` at every outcome of the clause, at every `JAtZ` ghosts of
  the entry state (what is left of `…Stab`). Not discharged (P1's footprint `Cur0W` is not `ProjW`-sharp: P3JStIrqTop).
* **`kernel_entry_runMcW_userF`**, **`kernel_entry_runMcW_vmfF`**, **`kernel_entry_runMcW_sysUF`**: the clauses on any
  core through `RunMcW`, with the matching `…Foot` premise.

Not covered: the native syscall and trap clauses (no stable-ghost run exists for them: the StPost line has the
accepted fast paths only, `kernel_entry_invSt` / `…ioSt` / `…tmSt` / `…rrSt`, not the general invocation).

Named premises: `UserFoot`, `VmfFoot`, `SysUFoot` [J] (above); U45nv's globals as in `kernel_entry_runCK`. No sorry.
New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStEvK
import Fl4Proofs.P3.P3JStIrqTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The footprint and carry facts of one step at every outcome ghosts** (module docstring). -/
def FootAt (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) (s' : S)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∀ (G' : MdbGhost) (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (a' : A),
    JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' →
    P1.WritesIn st s s' (ProjW (L := L) H Cs s) ∧ KhNoneKeep σ σ' ∧ UtKeep (L := L) Z.G G' s s'

/-- **`UserFoot` [J]** (module docstring). -/
def UserFoot (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∀ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' →
        FootAt (L := L) arI AR Z H Cs s σ r.1 σ' ⦄

/-- **`VmfFoot` [J]** (module docstring). -/
def VmfFoot (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType),
      σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∀ σ', EvOut false (.vmFaultEvent ft) σ σ' →
        FootAt (L := L) arI AR Z H Cs s σ r.1 σ' ⦄

/-- **`SysUFoot` [J]** (module docstring). -/
def SysUFoot (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64), σ.curThread ≠ σ.idleThread →
      UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∀ ev σ', KEvSpec (.sysU n) true ev → EvOut true ev σ σ' →
        FootAt (L := L) arI AR Z H Cs s σ r.1 σ' ⦄

variable {arI AR MR}

/-- **`RunMcW` at an outcome with stable ghosts and `FootAt`** (module docstring). -/
theorem runMcW_of_st {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : VxE Z)
    (hF : ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c ∧ FIdleW (L := L) s c)
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hC : RunCK (L := L) arI AR MR s' a' σ')
    (hSt : JStab (L := L) arI AR Z H Cs s' a' σ') (hFt : FootAt (L := L) arI AR Z H Cs s σ s' σ') :
    RunMcW (L := L) arI AR MR s' a' σ' := by
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := hSt
  obtain ⟨hW, hK, hU⟩ := hFt G' V' Ac' Lst' D' a' J'
  exact ⟨hC, jAtMcW_step J hF J' (@VxE.mv Z hV G' V') hW hK hU⟩

set_option maxHeartbeats 8000000 in
/-- **The user-exception clause at given ghosts, stable, at U45nv's premises** (module docstring). -/
theorem user_stabU45 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n c : U64) (hct : σ.curThread ≠ σ.idleThread) (hU : UserHw n c) :
    syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
      RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨⟨hJ17, hC⟩, hIoa⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  have hm := hX.sb.1.1.vim
  have hG := Fl4ProofsK.P3.SInvR.G5.user_entryStU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD ⟨hPAi, hT.mb⟩ hT
    hmax htu hRef hDR hFpu hJ17 J n c hct hU (KFinEv42.toK (kFinEv42_of hFpu hFW hA) hA)
  refine WP.spec_mono hG ?_
  rintro r ⟨σ', hO, hJ', hSt⟩
  exact ⟨σ', hO, ⟨⟨⟨hJ', EvOut.irqCarry hm hC hO⟩, EvOut.ioaRel hIoa hO⟩, cki_evOut hCK hO⟩, hSt⟩

set_option maxHeartbeats 8000000 in
/-- **The VM-fault clause at given ghosts, stable, at U45nv's premises** (module docstring). -/
theorem vmf_stabU45 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (ad c : U64) (ft : Fl4Spec.VMFaultType) (hct : σ.curThread ≠ σ.idleThread) (hV : VmfHw ad c ft σ) :
    syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
      RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨⟨hJ17, hC⟩, hIoa⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  have hm := hX.sb.1.1.vim
  have hG := Fl4ProofsK.P3.SInvR.G5.vmf_entryStU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD ⟨hPAi, hT.mb⟩ hT
    hmax htu hRef hDR hFpu hJ17 J ad c ft hct hV (KFinEv42.toK (kFinEv42_of hFpu hFW hA) hA)
  refine WP.spec_mono hG ?_
  rintro r ⟨σ', hO, hJ', hSt⟩
  exact ⟨σ', hO, ⟨⟨⟨hJ', EvOut.irqCarry hm hC hO⟩, EvOut.ioaRel hIoa hO⟩, cki_evOut hCK hO⟩, hSt⟩

set_option maxHeartbeats 8000000 in
/-- **The unknown-syscall clause at given ghosts, stable, at U45nv's premises** (module docstring). -/
theorem sysU_stabU45 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (n : I64) (hct : σ.curThread ≠ σ.idleThread) (hU : UnkSys (L := L) n s) (hND : NoDbgSys (L := L) arI n s a) :
    syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
      RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨⟨hJ17, hC⟩, hIoa⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  have hm := hX.sb.1.1.vim
  have hG := Fl4ProofsK.P3.SInvR.G5.sysU_entryStU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD ⟨hPAi, hT.mb⟩ hT
    hmax htu hRef hSX hDR hFpu hJ17 J n hct hU hND (fun _ _ _ _ => (KFinEv42.toK (kFinEv42_of hFpu hFW hA) hA))
  refine WP.spec_mono hG ?_
  rintro r ⟨ev, σ', hK, hO, hJ', hSt⟩
  exact ⟨ev, σ', hK, hO, ⟨⟨⟨hJ', EvOut.irqCarry hm hC hO⟩, EvOut.ioaRel hIoa hO⟩, cki_evOut hCK hO⟩, hSt⟩

set_option maxHeartbeats 4000000 in
/-- **The user-exception entry on any core, through `RunMcW`, with `UserFoot`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_userF [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : UserFoot (L := L) arI AR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c hct hu
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (user_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n c hct hu) (hFt Z H Cs Ac Lst D J hV n c hct hu)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hK⟩
  exact ⟨σ', hO, runMcW_of_st J hV hF hC' hSt (hK σ' hO)⟩

set_option maxHeartbeats 4000000 in
/-- **The VM-fault entry on any core, through `RunMcW`, with `VmfFoot`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_vmfF [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : VmfFoot (L := L) arI AR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro ad c ft hct hv
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (vmf_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J ad c ft hct hv)
    (hFt Z H Cs Ac Lst D J hV ad c ft hct hv)) ?_
  rintro r ⟨⟨σ', hO, hC', hSt⟩, hK⟩
  exact ⟨σ', hO, runMcW_of_st J hV hF hC' hSt (hK σ' hO)⟩

set_option maxHeartbeats 4000000 in
/-- **The unknown-syscall entry on any core, through `RunMcW`, with `SysUFoot`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcW_sysUF [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    (hFt : SysUFoot (L := L) arI AR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcW (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n hct hU hND
  obtain ⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := hR
  haveI := hV
  refine WP.spec_mono (spec_and2 (sysU_stabU45 hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hC J n hct hU hND) (hFt Z H Cs Ac Lst D J hV n hct hU hND)) ?_
  rintro r ⟨⟨ev, σ', hK, hO, hC', hSt⟩, hF'⟩
  exact ⟨ev, σ', hK, hO, runMcW_of_st J hV hF hC' hSt (hF' ev σ' hK hO)⟩

end

end Fl4Proofs.P3.Mc
