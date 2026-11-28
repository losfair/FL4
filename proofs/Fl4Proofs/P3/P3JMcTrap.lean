/-
P3 (p3J gen 22): **the trap and native-syscall clauses of the multicore run** (`RunMcWK` to `RunMcWK`).

* **`trap_stabU45`**: the `int $N` clause at given ghosts, stable, at U45nv's premises (P3JStTrapK's `Fl4ProofsK`
  copy of `trap_entryStU41`, the finish record from U43 / U42, `JReachU40` / `CKI` at the outcome as `sysU_stabU45`).
* **`TrapFootW`** [J]: the trap entry writes only the projection footprint `ProjW H Cs s` (same shape as P3JMcUt's
  `UserFootW` / `SysUFootW`). **`kernel_entry_runMcWK_trapW`**: the trap clause on any core, `RunMcWK` to `RunMcWK`,
  with `TrapFootW` only (`UtMem` by `utMem_of_stab`, `KhWF` by `khWF_evOut`, `CnWF` from `KhWF`).
* Native syscall: no stable-ghost run of the general invocation path exists (StPost has the accepted fast paths
  only; the syscall chain of U45nv ends in `RJ`, whose ghosts are existential, and its dispatch leaves
  (`KDispHypsKVU44`, `JPathMEU44`) are stated with `JAt` posts, so a stable copy means restating every invocation
  leaf). So the ghost half stays a premise:
  **`SysStab`** [J]: at every `JAtZ` ghosts of the entry state (with `VxE`), under the clause's case conditions
  (non-idle, `NativeSys`, the `TRAP_SYSCALLS` flag clear, the K6 dispatch facts `SysK6` at those ghosts), every run
  of `handle_syscall` ends at an outcome of `fl4KernelEntrySyscall true c` that is `RunCK` **and** `JStab Z H Cs`:
  exactly what a stable copy `sys_stabU45` of `kernel_entry_runCK`'s syscall clause would prove (the analogue of
  the proved `irq_stabU45` / `user_stabU45` / … / `trap_stabU45`). True on `CKI` runs as far as the ghosts go: no
  retype (no untyped cap), no detype, so `H`, `Cs`, the typed heap and every set but the MDB / VSpace sets stay.
  **`SysFootW`** [J]: the footprint, same shape as the others. **`kernel_entry_runMcWK_sysW`**: the native syscall
  clause on any core, `RunMcWK` to `RunMcWK` (`KhWF` by P3JKtSys's `kentry_khWF` from `CKI`).

Named premises: `TrapFootW`, `SysStab`, `SysFootW` [J] (above); U45nv's globals as in `kernel_entry_runCK`
(trap top). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JStTrapK
import Fl4Proofs.P3.P3JMcUt
import Fl4Proofs.P3.P3JKtSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 8000000 in
/-- **The `int $N` clause at given ghosts, stable, at U45nv's premises** (module docstring). -/
theorem trap_stabU45 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunCK (L := L) arI AR MR s a σ)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z]
    (v : U64) (hct : σ.curThread ≠ σ.idleThread) (hv : v.val < 256) :
    syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
      RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  obtain ⟨⟨⟨hJ17, hC⟩, hIoa⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -⟩ := jreach_invU3 hnd hJ17.1
  have hm := hX.sb.1.1.vim
  have hG := Fl4ProofsK.P3.SInvR.G5.trap_entryStU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD ⟨hPAi, hT.mb⟩ hT
    hmax htu hRef hDR hFpu hJ17 J v hct hv (fun _ _ _ _ => (KFinEv42.toK (kFinEv42_of hFpu hFW hA) hA))
  refine WP.spec_mono hG ?_
  rintro r ⟨ev, σ', hK, hO, hJ', hSt⟩
  exact ⟨ev, σ', hK, hO, ⟨⟨⟨hJ', EvOut.irqCarry hm hC hO⟩, EvOut.ioaRel hIoa hO⟩, cki_evOut hCK hO⟩, hSt⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`TrapFootW` [J]**: the `int $N` entry writes only the projection footprint (module docstring). -/
def TrapFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
      syscall.handle_trap_syscall st arI s a v ⦃ r => ∀ ev σ', KEvSpec (.trap v) true ev → EvOut true ev σ σ' →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- The native syscall clause's case condition on FL4's `TRAP_SYSCALLS` flag (U45nv's `hfl`). -/
def SysFlag (s : S) : Prop :=
  ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
    ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄

/-- The native syscall clause's K6 dispatch facts at the ghosts `Z H Cs` (`kernel_entry_runCK`'s per-entry
premise). -/
def SysK6 (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64)
    (c : Fl4Spec.Syscall) : Prop :=
  ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
    (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
      KDispHypsKVU44w (L := L) arI (fun l c => ¬ NK6 l c) AR (Z.mv Z.G V') H Cs D' s' a' σb n c

/-- **`SysStab` [J]**: the native syscall clause at given ghosts ends stable (module docstring: the statement a
stable-ghost copy of `kernel_entry_runCK`'s syscall clause would prove). -/
def SysStab (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
      σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        RunCK (L := L) arI AR MR r.1 r.2 σ' ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄

/-- **`SysFootW` [J]**: the native syscall entry writes only the projection footprint. -/
def SysFootW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
      σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
      syscall.handle_syscall st arI s a n ⦃ r => ∀ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

variable {arI AR MR}

set_option maxHeartbeats 4000000 in
/-- **The `int $N` entry on any core, `RunMcWK` to `RunMcWK`, with `TrapFootW`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcWK_trapW [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : TrapFootW (L := L) arI AR s a σ) :
    ∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
      syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro v hct hv
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  have := hV
  refine WP.spec_mono (spec_and2 (trap_stabU45 hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hDR hFpu hFW hC J v
    hct hv) (hFt Z H Cs Ac Lst D J hV v hct hv)) ?_
  rintro r ⟨⟨ev, σ', hKe, hO, hC', hSt⟩, hW⟩
  have hK' := khWF_evOut (KEvSpec.not_sys hKe) hK hO
  exact ⟨ev, σ', hKe, hO, runMcW_of_stK J hV hF hC' hSt (hW ev σ' hKe hO) (utMem_of_stab hSt hC'.2)
    (cnWF_of_khWF hK'), hK'⟩

set_option maxHeartbeats 4000000 in
/-- **The native syscall entry on any core, `RunMcWK` to `RunMcWK`, with `SysStab` and `SysFootW`** (module
docstring; `hSt`, `hFt` [J]). The K6 dispatch facts are asked at every ghosts of the entry state. -/
theorem kernel_entry_runMcWK_sysW {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hSS : SysStab (L := L) arI AR MR s a σ) (hFt : SysFootW (L := L) arI AR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c hct hns hfl hK6
  obtain ⟨⟨hC, Z, H, Cs, Ac, Lst, D, J, hV, hF⟩, hK⟩ := hR
  have hk6 := hK6 Z H Cs Ac Lst D J
  refine WP.spec_mono (spec_and2 (hSS Z H Cs Ac Lst D J hV n c hct hns hfl hk6)
    (hFt Z H Cs Ac Lst D J hV n c hct hns hfl hk6)) ?_
  rintro r ⟨⟨σ', h1, hC', hSt⟩, hW⟩
  have hK' : KhWF σ' := kentry_khWF true c hC.2 hK _ h1
  exact ⟨σ', h1, runMcW_of_stK J hV hF hC' hSt (hW σ' h1) (utMem_of_stab hSt hC'.2) (cnWF_of_khWF hK'), hK'⟩

end

end Fl4Proofs.P3.Mc
