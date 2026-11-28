/-
P3 (p3J gen 29): **the native syscall clause on `RunMcWKR` from one premise**: gen 23's two [J]s `SysStabC` and
`SysFootWC` replaced by one entry-level [J] (`SysStFtC`, implied by the old two) and, below it, by one
dispatch-level [J] (`DispStabFoot`).

* **`SysStFtC` [J]** (entry level): at a `RunMcWKR` state, at every `JAtZ` ghosts (with `VxE`), under the clause's
  case conditions (non-idle, `NativeSys`, `SysFlag`, the K6 facts `SysK6`), every run of `handle_syscall` ends at
  an outcome of `fl4KernelEntrySyscall true c` with `JStab Z H Cs` and `MR`, **and** writes only `ProjW H Cs s`.
  - **Narrowing (proved, `sysStFtC_of_old`)**: `SysStabC ∧ SysFootWC → SysStFtC` at every `RunMcWKR` state (its
    `MR` from the old post's `RunCK` by `jreach_invU3`, its footprint from `SysFootW` at the same outcome). The new
    statement drops the old post's `RunCK` (U40's reach and `CKI` at the outcome), which is now **proved**:
  - **`runCK_sysStep`**: a native syscall step from a `RunCK` state to an entry outcome related by `JStab` and `MR`
    is `RunCK` (`JReachU3.step` with `RJM` from `JStab` — `XTopAt.relTop`, `VxE.mv` —, the carried spec facts by
    `kentry_gpmOut` / `kentry_idleVtS` / `kentry_devRange` / `kentry_irqCarry` / `kentry_ioxV`, `CKI` by
    `kentry_cki`).
  - So `SysStFtC` gives back **both** old premises at the clause's state (`sysStab_of_stFt`, `sysFootW_of_stFt`),
    and **`kernel_entry_runMcWKR_sysSF`** is gen 25's `kernel_entry_runMcWKR_sysWC` with `hSS`, `hFt` replaced by
    `hSF : SysStFtC` (and `hnd`).
* **`DispStabFoot` [J]** (dispatch level; gen 28's proposed `DispStFtJ`): at a `RunMcWKR` state, at every `JAtZ`
  ghosts with `VxE`, under the same case conditions, P3JSysSt's `DispStabFootAt`: at every dispatch state of the
  entry (`KFrontB`, `BudgetAt σ σb true`) with `JAtZ (Z.mv Z.G V') H Cs`, `MR`, `CKI σb`, `RR σb`, every run of
  `dispatch_syscall … n` ends in `DispPostSt` — an outcome of the spec's `fl4HandleSyscall true c` from `σb` with
  `JStabR Z H Cs` / `MR` (unpreempted) or, preempted, a `preemptionPath` outcome with `JStab Z H Cs` / `MR` —
  and writes only `ProjW H Cs` of the dispatch state. **The ReplyRecv fast path needs no part of it**: where
  `fastpath.reply_recv` accepts, P1's `FastAgree` (from `FastAcc.of_rrpre`, `JAtZ.rrPreAt` / `rrPre5At`, global
  `StoreExt` [P]) gives the general path's post to the fast run (P3JSysSt).
  - **`sysStFtC_of_disp`**: `DispStabFoot → SysStFtC` with the clause tops' globals (P3JSysStK's
    `Fl4ProofsK…sys_entryStFU41`, the finish record by U43's `kFinAtR42_of`). **`sysStabC_sysFootWC_of_disp`**:
    at a `RunMcWKR` state `DispStabFoot` gives `SysStabC` **and** `SysFootWC` (both halves of `SysStabC`).
  - **`kernel_entry_runMcWKR_sysD`**: the native syscall clause, `RunMcWKR` → `RunMcWKR`, with `DispStabFoot` only
    (+ U45nv's globals as `kernel_entry_runMcWKR_sysU`, and the clause's per-entry K6 input as before).
  - Justification of `DispStabFoot` (FL4 Rust `syscall.rs` `dispatch_syscall`; l4v `handle_invocation` /
    `handle_recv` / `handle_yield` and the `ccorres` of those): on `CKI` states no untyped, SchedControl,
    IRQ-control or arch cap exists (P3JCkW `KW`), so no dispatch leaf retypes, detypes or installs a frame / VSpace:
    `H` (the objects), `Cs`, the typed heap `Z.th` and the buffer words `Z.B` stay, the MDB ghost and VSpace sets
    may change (`JStab`'s `Z.mv G V`); no TCB has an IPC-buffer frame cap, so every transfer writes registers only
    (gen 27's `xferOKRS_nb`), and every word a leaf writes lies in an `H` object, the kernel-state block or a node
    of `Cs` (`ProjW`). Not refuted on any leaf so far; gen 28's / this generation's leaves prove the footprint half
    for `handle_yield` and `receive_signal`.
  - **Not a narrowing of the old [J]s**: `DispStabFoot` speaks of mid-entry (dispatch) states, which neither
    `SysStabC` nor `SysFootWC` mentions, so it is not implied by them; it implies them (above). The strict
    narrowing is `SysStFtC`; `DispStabFoot` is its decomposition target (discharged leaf by leaf, P3JSysLeaf).

Named premises: `SysStFtC`, `DispStabFoot` [J] (above); U45nv's globals as `kernel_entry_runMcWKR_sysU` (+
`StoreExt` [P], already global there). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSysStK
import Fl4Proofs.P3.P3JMcLiftR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`SysStFtC` [J]**: the native syscall entry ends stable, with `MR`, and writes only `ProjW` (module
docstring; implied by gen 23's `SysStabC ∧ SysFootWC`, `sysStFtC_of_old`). -/
def SysStFtC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWKR (L := L) arI AR MR s a σ →
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
      σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
        JStab (L := L) arI AR Z H Cs r.1 r.2 σ' ∧ MR r.2 σ'.machineState ∧
        P1.WritesIn st s r.1 (ProjW (L := L) H Cs s) ⦄

/-- **`DispStabFoot` [J]**: the dispatch ends stable with its footprint at every dispatch state of the entry
(module docstring; P3JSysSt's `DispStabFootAt`). -/
def DispStabFoot (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWKR (L := L) arI AR MR s a σ →
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
      σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
      DispStabFootAt (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- **The narrowing**: gen 23's two [J]s give `SysStFtC` (module docstring). -/
theorem sysStFtC_of_old (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hSS : SysStabC (L := L) arI AR MR s a σ) (hFt : SysFootWC (L := L) arI AR MR s a σ) :
    SysStFtC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n c hct hns hfl hk6
  refine WP.spec_mono (spec_and2 (hSS hR.1.1 Z H Cs Ac Lst D J hV n c hct hns hfl hk6)
    (hFt hR.1.1 Z H Cs Ac Lst D J hV n c hct hns hfl hk6)) ?_
  rintro r ⟨⟨σ', hy, hC', hSt⟩, hW⟩
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, hMR, -, -, -⟩ := jreach_invU3 hnd hC'.1.1.1.1
  exact ⟨σ', hy, hSt, hMR, hW σ' hy⟩

/-- **A native syscall step to a stable, `MR` outcome keeps `RunCK`** (module docstring). -/
theorem runCK_sysStep (hnd : Fl4Spec.numDomains = 1) {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}
    (hR : RunCK (L := L) arI AR MR s a σ) {n : I64} {c : Fl4Spec.Syscall} (hct : σ.curThread ≠ σ.idleThread)
    (hn : NativeSys n c) (hs : syscall.handle_syscall st arI s a n = ok (s', a'))
    (hy : ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1)
    {Z : XSets} [VxE Z] {H : P1.Heap} {Cs : Set U64} (hSt : JStab (L := L) arI AR Z H Cs s' a' σ')
    (hM : MR a' σ'.machineState) : RunCK (L := L) arI AR MR s' a' σ' := by
  obtain ⟨⟨⟨⟨hJ3, hGp, hIv, hDv⟩, hB⟩, hR0⟩, hCK⟩ := hR
  obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ3
  have hU3 := sinvX_ut3 hX
  have hSg : SInvG.SpecGlobS σ := sinvX_sg hX
  have hm := hX.sb.1.1.vim
  obtain ⟨G', V', Ac', Lst', D', J'⟩ := hSt
  have hRJ : RJ (L := L) arI AR s' a' σ' :=
    ⟨J'.xtop.relTop, Z.mv G' V', H, Cs, Ac', Lst', D', J', @VxE.mv Z inferInstance G' V'⟩
  exact ⟨⟨⟨⟨JReachU3.step n c hJ3 hct hn hs hy ⟨hRJ, hM⟩,
    SInvGp.kentry_gpmOut c hSg hU3 hGp _ hy,
    SInvIV.kentry_idleVtS c hSg (sinvX_idleOut hX) hU3 hIv _ hy,
    SInvDV.kentry_devRange c hU3 hDv _ hy⟩, SInvIB.kentry_irqCarry true c hm hB _ hy⟩,
    hR0.frame (SInvIox.kentry_ioxV true c σ _ hy)⟩, SInvCk.kentry_cki true c hCK _ hy⟩

/-- `SysStFtC` gives gen 22's `SysStab` at the clause's `RunMcWKR` state. -/
theorem sysStab_of_stFt (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) (hSF : SysStFtC (L := L) arI AR MR s a σ) :
    SysStab (L := L) arI AR MR s a σ := by
  intro Z H Cs Ac Lst D J hV n c hct hns hfl hk6
  haveI := hV
  refine WP.spec_mono (spec_and_eq (hSF hR Z H Cs Ac Lst D J hV n c hct hns hfl hk6) fun _ h => h) ?_
  rintro ⟨s', a'⟩ ⟨⟨σ', hy, hSt, hM, -⟩, hs⟩
  exact ⟨σ', hy, runCK_sysStep hnd hR.1.1.1.1 hct hns hs hy hSt hM, hSt⟩

/-- `SysStFtC` gives gen 22's `SysFootW` at the clause's `RunMcWKR` state. -/
theorem sysFootW_of_stFt {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) (hSF : SysStFtC (L := L) arI AR MR s a σ) :
    SysFootW (L := L) arI AR s a σ := by
  intro Z H Cs Ac Lst D J hV n c hct hns hfl hk6
  exact WP.spec_mono (hSF hR Z H Cs Ac Lst D J hV n c hct hns hfl hk6) fun r ⟨_, _, _, _, hW⟩ _ _ => hW

/-- **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `SysStFtC`** (`hSF` [J]; module docstring). -/
theorem kernel_entry_runMcWKR_sysSF (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWKR (L := L) arI AR MR s a σ) (hSF : SysStFtC (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysWC hR (fun _ => sysStab_of_stFt hnd hR hSF) (fun _ => sysFootW_of_stFt hR hSF)

set_option maxHeartbeats 4000000 in
/-- **`DispStabFoot` gives `SysStFtC`** with the clause tops' globals (module docstring). -/
theorem sysStFtC_of_disp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hDF : DispStabFoot (L := L) arI AR MR s a σ) :
    SysStFtC (L := L) arI AR MR s a σ := by
  intro hR Z H Cs Ac Lst D J hV n c hct hns hfl hk6
  obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, hCK⟩, -⟩, -⟩ := hR.1.1
  haveI := hV
  refine WP.spec_mono (Fl4ProofsK.P3.SInvR.G5.sys_entryStFU41 hARI hA hnd (MachPlatF.toT hM hIp) hKD
    ⟨hPAi, hT.mb⟩ hT hmax htu hRef hSX hDR hFpu hJ17 hCK hR.2 J n c hct hns hfl
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => (kFinAtR42_of hFpu hFW hA).toK hA)
    (hDF hR Z H Cs Ac Lst D J hV n c hct hns hfl hk6)) ?_
  rintro r ⟨σ', hy, -, hSt, hM', hW⟩
  exact ⟨σ', hy, hSt, hM', hW⟩

set_option maxHeartbeats 4000000 in
/-- **At a `RunMcWKR` state `DispStabFoot` gives both of gen 23's [J]s** (module docstring). -/
theorem sysStabC_sysFootWC_of_disp [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hDF : DispStabFoot (L := L) arI AR MR s a σ) :
    SysStabC (L := L) arI AR MR s a σ ∧ SysFootWC (L := L) arI AR MR s a σ :=
  have hSF := sysStFtC_of_disp hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hDF
  ⟨fun _ => sysStab_of_stFt hnd hR hSF, fun _ => sysFootW_of_stFt hR hSF⟩

set_option maxHeartbeats 4000000 in
/-- **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with `DispStabFoot` only** (`hDF` [J]; module
docstring). -/
theorem kernel_entry_runMcWKR_sysD [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hDF : DispStabFoot (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysSF hnd hR
    (sysStFtC_of_disp hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hSX hDR hFpu hFW hDF)

end

end Fl4Proofs.P3.Mc
