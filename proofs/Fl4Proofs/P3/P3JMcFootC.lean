/-
P3 (p3J gen 23): **the footprint premises narrowed to the runs they are used on**, and the transfer footprint at
`U = ∅` inside `ProjW`.

* **Honesty fix.** Gen 22 found every `…FootW` premise (P3JMcUt / P3JMcTrap) **false as stated**: at a `JAtZ`
  state where some thread holds a frame cap in its IPC-buffer slot, a fault transfer (or a `send_signal` to a
  bound thread, #80/#85) writes a buffer word, and that word lies outside every `H` object (P1's `UserOK`), so
  outside `ProjW`. The same holds of `SysStab` off reachable states: its post asks `RunCK` (U40's reach) at the
  outcome, which a `JAtZ` state that is not itself `RunCK` gives no reason to have. So the premises are restated
  here with the antecedent they are actually applied under, the run predicate **`RunMcWK s a σ`** (P3JKtTop:
  `RunCK ∧ JAtMcW ∧ KhWF`, so in particular `CKI σ`):
  `IrqFootWC`, `UserFootWC`, `VmfFootWC`, `SysUFootWC`, `TrapFootWC`, `SysFootWC`, `SysStabC` [J], each
  `RunMcWK s a σ → <gen 22's premise>`. On such a state every typed-heap slot cap is a `KW` cap (`kw_of_cki`), so no
  TCB's buffer slot holds a frame cap and FL4's `lookup_ipc_buffer` is `0` (`lookup_ipc_buffer_cki`): the buffer
  write that refutes gen 22's statements cannot happen. Each old premise implies the new one (`….of_W`), and the six
  tops are re-derived from the narrowed premises (`kernel_entry_runMcWK_irqWC` / `_userWC` / `_vmfWC` / `_sysUWC` /
  `_trapWC` / `_sysWC`). Gen 22's statements are unchanged.
* **The `UserW` half on CKI states, composed with P1's transfer footprint.** P1's transfer lemmas
  (`XferHyps.buf`, `XferFootOK`, `XferW`) take a user-word set `U` with `BufOK U` of the buffer lookup. At a CKI
  `JAtZ` state:
  - **`bufOK_empty_cki`**: `lookup_ipc_buffer st s rcv t ⦃ BufOK ∅ ⦄` for every TCB of the typed heap;
  - **`userOK_empty`**: `UserOK … ∅` (trivially);
  - **`xferW_empty_projW`**: every word of the transfer footprint `XferW` at `U = ∅`, over P1's sets of `H`
    (`H.tcbs`, `H.omega`, `H.scs`, `H.scBits`, as `JAtZ.blk`), is a `ProjW H Cs s` word (TCB user context and low
    words: inside the TCB; `Ω` words: inside their object; SC words: inside the SC; `J.kern.heap` for the fit);
  - **`xferFoot_empty_projW`**: the same for `XferFoot Z.T ∅` (the transfer's user-context half).
  So with `U = ∅` the transfer writes nothing outside `ProjW`. What is not done: `XferHyps.buf` asks `BufOK U` at
  every `XG` state of the entry (reached from the entry state by `Cur0W` writes, which may write TCB low words, i.e.
  cap slots), not only at the `JAtZ` entry state; carrying "no frame cap in a buffer slot" through an entry's
  intermediate states needs a P1-side frame on the buffer slots (or `CKI` of the intermediate spec states).

Named premises: `IrqFootWC`, `UserFootWC`, `VmfFootWC`, `SysUFootWC`, `TrapFootWC`, `SysFootWC`, `SysStabC` [J]
(above); U45nv's globals as in `kernel_entry_runCK` (the tops). No sorry. New module; no existing statement
changed.
-/
import Fl4Proofs.P3.P3JMcTrap
import Fl4Proofs.P3.P3JMcBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

/-! ## The `UserW` half at `U = ∅` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`BufOK ∅` of FL4's buffer lookup at a `CKI` `JAtZ` state** (module docstring). -/
theorem bufOK_empty_cki {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hC : SInvCk.CKI σ) {t : U64} (ht : Z.th t = some .tcb) (rcv : Bool) :
    msg.lookup_ipc_buffer st s rcv t ⦃ b => P1.BufOK ∅ b ⦄ := by
  rw [lookup_ipc_buffer_cki J hC ht rcv]
  exact (WP.spec_ok _).2 (fun h => (h rfl).elim)

/-- `UserOK` of the empty user-word set. -/
theorem userOK_empty {T Cs Ω : Set U64} {H : P1.Heap} (s : S) : P1.UserOK st T Cs Ω H ∅ s := by
  intro b hb; simp at hb

/-- **The transfer's user-context half at `U = ∅` is inside `ProjW`** (module docstring). -/
theorem xferFoot_empty_projW {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : P1.XferFoot Z.T ∅ b) : ProjW (L := L) H Cs s b := by
  rcases hb with ⟨y, hy, K, hK, -, rfl⟩ | hb
  · have hH := J.zH.1 y hy
    have hfit := J.kern.heap.fits y _ hH
    simp only [P1.HKind.bits, Nat.reducePow] at hfit
    have hv := wa_v (a := y) (b := K) (by omega)
    exact Or.inl ⟨y, .tcb, hH, by rw [hv]; omega, by rw [hv]; simp only [P1.HKind.bits, Nat.reducePow]; omega⟩
  · simp at hb

/-- **The whole transfer footprint `XferW` at `U = ∅`, over P1's sets of `H`, is inside `ProjW`** (module
docstring). -/
theorem xferW_empty_projW {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Sg : Set U64} {k b : U64}
    (hb : P1.XferW (P1.Heap.tcbs H) ∅ (P1.Heap.omega H) Sg (P1.Heap.scs H) (P1.Heap.scBits H) k b) :
    ProjW (L := L) H Cs s b := by
  have hHp := J.kern.heap
  rcases hb with (⟨y, hy, K, hK, -, rfl⟩ | hb) | ⟨⟨y, hy, K, hK, rfl⟩ | ⟨hΩ, -⟩, -⟩ | ⟨c, ⟨z, hz⟩, hin⟩
  · have hH : H y = some .tcb := hy
    have hfit := hHp.fits y _ hH
    simp only [P1.HKind.bits, Nat.reducePow] at hfit
    have hv := wa_v (a := y) (b := K) (by omega)
    exact Or.inl ⟨y, .tcb, hH, by rw [hv]; omega, by rw [hv]; simp only [P1.HKind.bits, Nat.reducePow]; omega⟩
  · simp at hb
  · have hH : H y = some .tcb := hy
    have hfit := hHp.fits y _ hH
    simp only [P1.HKind.bits, Nat.reducePow] at hfit
    have hv := wa_v (a := y) (b := K) (by omega)
    exact Or.inl ⟨y, .tcb, hH, by rw [hv]; omega, by rw [hv]; simp only [P1.HKind.bits, Nat.reducePow]; omega⟩
  · obtain ⟨-, p, k', hp, -, hin⟩ := hΩ
    exact Or.inl ⟨p, k', hp, hin.1, hin.2⟩
  · have e : P1.Heap.scBits H c = z := by simp only [P1.Heap.scBits, hz]
    rw [e] at hin
    exact Or.inl ⟨c, .sc z, hz, hin.1, by simpa only [P1.HKind.bits] using hin.2⟩

end

/-! ## The narrowed premises -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **`IrqFootWC` [J]**: `IrqFootW` at `RunMcWK` states only (module docstring: gen 22's `IrqFootW` is false at
states with a frame cap in a buffer slot; `RunMcWK` gives `CKI`, which excludes them). -/
def IrqFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → IrqFootW (L := L) arI AR MR s a σ

/-- **`UserFootWC` [J]**: `UserFootW` at `RunMcWK` states only. -/
def UserFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → UserFootW (L := L) arI AR s a σ

/-- **`VmfFootWC` [J]**: `VmfFootW` at `RunMcWK` states only. -/
def VmfFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → VmfFootW (L := L) arI AR s a σ

/-- **`SysUFootWC` [J]**: `SysUFootW` at `RunMcWK` states only. -/
def SysUFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → SysUFootW (L := L) arI AR s a σ

/-- **`TrapFootWC` [J]**: `TrapFootW` at `RunMcWK` states only. -/
def TrapFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → TrapFootW (L := L) arI AR s a σ

/-- **`SysFootWC` [J]**: `SysFootW` at `RunMcWK` states only. -/
def SysFootWC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → SysFootW (L := L) arI AR s a σ

/-- **`SysStabC` [J]**: `SysStab` at `RunMcWK` states only (its post asks `RunCK` at the outcome, which an
unreachable entry state does not give). -/
def SysStabC (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcWK (L := L) arI AR MR s a σ → SysStab (L := L) arI AR MR s a σ

variable {arI AR MR}

theorem IrqFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : IrqFootW (L := L) arI AR MR s a σ) :
    IrqFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem UserFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : UserFootW (L := L) arI AR s a σ) :
    UserFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem VmfFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : VmfFootW (L := L) arI AR s a σ) :
    VmfFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem SysUFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : SysUFootW (L := L) arI AR s a σ) :
    SysUFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem TrapFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : TrapFootW (L := L) arI AR s a σ) :
    TrapFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem SysFootWC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : SysFootW (L := L) arI AR s a σ) :
    SysFootWC (L := L) arI AR MR s a σ := fun _ => h
theorem SysStabC.of_W {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : SysStab (L := L) arI AR MR s a σ) :
    SysStabC (L := L) arI AR MR s a σ := fun _ => h

/-! ## The six tops from the narrowed premises -/

/-- **The interrupt entry on any core, `RunMcWK` to `RunMcWK`, with `IrqFootWC`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_irqWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : IrqFootWC (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_irqW hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW hR (hFt hR)

/-- **The user-exception entry on any core, `RunMcWK` to `RunMcWK`, with `UserFootWC`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_userWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : UserFootWC (L := L) arI AR MR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_userW hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR (hFt hR)

/-- **The VM-fault entry on any core, `RunMcWK` to `RunMcWK`, with `VmfFootWC`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_vmfWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : VmfFootWC (L := L) arI AR MR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_vmfW hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR (hFt hR)

/-- **The unknown-syscall entry on any core, `RunMcWK` to `RunMcWK`, with `SysUFootWC`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_sysUWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : SysUFootWC (L := L) arI AR MR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_sysUW hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR (hFt hR)

/-- **The `int $N` entry on any core, `RunMcWK` to `RunMcWK`, with `TrapFootWC`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_trapWC [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : TrapFootWC (L := L) arI AR MR s a σ) :
    ∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
      syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_trapW hARI hA hnd hM hIp hKD hPAi hT hmax htu hRef hDR hFpu hFW hR (hFt hR)

/-- **The native syscall entry on any core, `RunMcWK` to `RunMcWK`, with `SysStabC` and `SysFootWC`** (`hSS`,
`hFt` [J]). -/
theorem kernel_entry_runMcWK_sysWC {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hSS : SysStabC (L := L) arI AR MR s a σ) (hFt : SysFootWC (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWK_sysW hR (hSS hR) (hFt hR)

end

end Fl4Proofs.P3.Mc
