/-
P3 (p3J gen 49): **`DispStabFootLzw.midSpec` (`MidSpecAt`) proved; top `kernel_entry_runMcWKR_sysLzx` with
`DispStabFootLzx` [J] = {midRecvSw}**.

`MidSpecAt σ` (P3JMidCls) asks, at every dispatch state `σb` of the entry (`BudgetAt σ σb true`) with `CKI`, for
every cap pointer, `MidStF` at every `ok` outcome `y` of the spec's first phase
`fl4HandleInvocationR true false false true true cptr`. Its six fields, each from an existing proof:
* the first phase's queue / action fact (`CQ ct`: ct current, runnable without a fault, in no ready queue, no
  switch to it pending) at `y.2`: XTopJointMidRunQ's **`midRunQ_shell`** from `CQ ∧ NQ` at `σb` and
  `JMidPerfHypQ` [W] at `σb`, which is XTopJointPerfI's **`jMidPerfHypQ_of2`** from `JPerfRegHyp` and
  `JPerfIrqSlotHyp` (the IRQ handler set / clear of the first phase included), both XTopJointKEntry27b's
  **`jPerfRegHyp_27b`** / **`jPerfIrqSlotHyp_27b`** from `SInvB σ` (the non-stable chain's discharge,
  KEntry27b; StPostRRTop uses it the same way). This gives `nq`, `nsw`, `run` (`CurRun`: the current thread is
  `ct` with its TCB runnable).
* `CQ ∧ NQ` at `σb`: **`midEntry_disp`** (new) — `MidEntry σ` by XTopJointMidRunS's `JAtZ.midEntry` at the entry
  state (`Entered σ` by `SInvX.entered`, the no-fault fact by `SInvAll.sinvB_disp` at `σ` itself), moved to `σb`
  through the `FaultIP` register write (`BudgetAt.shape27`: `σb`'s heap is `σ`'s with ct's TCB register-updated;
  ready queues, current thread unchanged), the no-fault fact at `σb` by `sinvB_disp`, the action by
  `BudgetAt.entered`.
* `ni`: `y.2.curThread = σb.curThread` (`CQ`), `y.2.idleThread = σb.idleThread` (SpecInvSgI6's
  `idk_fl4HandleInvocationR`), `Entered σb`.
* `vfh`: XTopJointKEntry27b's **`jMidVfhHyp_27b`** (`JMidVfhHyp` [J] discharged there from `SInvB σ`).
* `cki`: P3JCkS's **`ck_handleInvocationR`**.

* **`midSpecAt_of`**: `MidSpecAt σ` from `JAtZ … s a σ`, `SInvX σ`, `σ.curThread ≠ σ.idleThread`.
* **`DispStabFootLzx` [J]** {midRecvSw — `DispStabFootLzw`'s, verbatim}; **`dispStabFootLzw_of_Lzx`**
  (`midSpec` by `midSpecAt_of`, `SInvX` from `RunMcWKR` by `jreach_invU3`), **`dispStabFootLzx_of_Lzw`**
  (unconditional); top **`kernel_entry_runMcWKR_sysLzx`** (globals verbatim as `_sysLzw`, `KNo88` [S] as there:
  transitional, over-wide [S]; the proper native scope, via `LookAt`, excludes only entries whose invoked slot
  holds a Thread cap with label = 88).

Premise honesty: `DispStabFootLzx` is `DispStabFootLzw` without `midSpec` (implied by it); with the globals
(`hnd`) it implies it. Nothing weakened.

Named premises: `DispStabFootLzx` [J], `KNo88` [S] (P3JEptScope); globals as `_sysLzw`. No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.P3JEptScope
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 49) **`CQ ∧ NQ` of the current thread at a dispatch state, from the entry state** (module
docstring). -/
theorem midEntry_disp (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ σb : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread)
    (hBA : BudgetAt σ σb true) :
    Entered σb ∧ MidRun.CQ σb.curThread σb ∧ MidRun.NQ σb.curThread σb := by
  have hS := hX.sb
  have hni : Entered σ := hX.entered hct
  obtain ⟨x0, hk0, -⟩ := hS.1.2
  obtain ⟨-, ek, ect, -, -, eq0⟩ := BudgetAt.shape27 hnd hk0 hBA
  have ek' : σb.kheap = Function.update σ.kheap σ.curThread
      (some (.tcb (Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2)))) := ek
  obtain ⟨-, hnfb⟩ := SInvAll.sinvB_disp (x' := Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2))
    hS hct hk0 rfl rfl ek' ect
  have ek0 : σ.kheap = Function.update σ.kheap σ.curThread (some (.tcb x0)) := by
    rw [← hk0]; exact (Function.update_eq_self _ _).symm
  obtain ⟨-, hnf0⟩ := SInvAll.sinvB_disp (σb := σ) (x' := x0) hS hct hk0 rfl rfl ek0 rfl
  have hME := J.midEntry hni hnf0
  have hnib : Entered σb := BudgetAt.entered hnd hk0 hni hBA
  have hxb : ∀ x, σb.kheap σb.curThread = some (.tcb x) →
      x = Notif.setReg x0 .faultIP (x0.tcbArch.tcbContext.userRegs .nextIP - 2) := by
    intro x hx
    rw [ek', ect, Function.update_self] at hx
    simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
    exact hx.symm
  refine ⟨hnib, ⟨⟨rfl, fun x hx => ⟨?_, hnfb x hx⟩⟩, ?_, ?_⟩, ?_⟩
  · obtain rfl := hxb x hx
    exact hME.run x0 hk0
  · rw [ect, eq0]; exact hX.ctQ
  · rw [hnib.2]; intro e; cases e
  · intro p n q hp hq
    by_cases e : p = σ.curThread
    · subst e
      rw [ek', Function.update_self] at hp
      simp at hp
    · rw [ek', Function.update_of_ne e] at hp
      rw [ect]
      exact hME.nq p n q hp hq

set_option maxHeartbeats 4000000 in
/-- (p3J gen 49) **`MidSpecAt` proved** (module docstring): from the entry state's `JAtZ`, `SInvX` and a
non-idle current thread. -/
theorem midSpecAt_of (hnd : Fl4Spec.numDomains = 1) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ) (hct : σ.curThread ≠ σ.idleThread) :
    MidSpecAt σ := by
  intro σb hBA hCb cptr y hy hok
  have hS := hX.sb
  obtain ⟨hnib, hcq, hnqb⟩ := midEntry_disp hnd J hX hct hBA
  have hPQ : MidRun.JMidPerfHypQ true cptr σb :=
    MidRun.jMidPerfHypQ_of2 hcq hnqb (jPerfRegHyp_27b hnd hS hct hBA cptr) (jPerfIrqSlotHyp_27b hnd hS hBA cptr)
  obtain ⟨⟨hcy, hrs⟩, hrq, hsw⟩ := MidRun.midRunQ_shell true true cptr σb hcq hnqb hPQ y hy
  have hid : y.2.idleThread = σb.idleThread :=
    SInvG.idk_fl4HandleInvocationR (N := σb.idleThread) true false false true true cptr σb rfl y hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcy, hid]; exact hnib.1
  · rw [hcy]; exact hrq
  · exact jMidVfhHyp_27b hnd hS hBA cptr y hy hok
  · exact SInvCk.ck_handleInvocationR true false false true true cptr σb hCb y hy
  · intro x hx
    rw [hcy] at hx
    exact (hrs x hx).1
  · rw [hcy]; exact hsw

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- (p3J gen 49) **`DispStabFootLzx` [J]**: `DispStabFootLzw` without `midSpec` (module docstring). -/
structure DispStabFootLzx (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  /-- `DispStabFootLzw.midRecvSw`, verbatim. -/
  midRecvSw : RunMcWKR (L := L) arI AR MR s a σ →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64) (c : Fl4Spec.Syscall),
        σ.curThread ≠ σ.idleThread → MidSys n c → SysFlag (L := L) s → SysK6 (L := L) arI AR Z H Cs s a σ n c →
        MidRecvSw (L := L) arI AR MR Z H Cs s a σ n c

variable {arI AR MR}

/-- (p3J gen 49) **`DispStabFootLzx → DispStabFootLzw`** (`midSpec` by `midSpecAt_of`; module docstring). -/
theorem dispStabFootLzw_of_Lzx (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzx (L := L) arI AR MR s a σ) : DispStabFootLzw (L := L) arI AR MR s a σ where
  midSpec := fun hR _ _ _ _ _ _ J _ _ _ hct _ _ _ => by
    obtain ⟨⟨⟨⟨⟨hJ17, -⟩, -⟩, -⟩, -⟩, -⟩ := hR.1.1
    obtain ⟨_, _, _, _, _, _, -, hX, -, -, -, -, -, -, -⟩ := jreach_invU3 hnd hJ17.1
    exact midSpecAt_of hnd J hX hct
  midRecvSw := h.midRecvSw

/-- (p3J gen 49) **`DispStabFootLzw → DispStabFootLzx`** (the honesty claim: `DispStabFootLzx` is implied). -/
theorem dispStabFootLzx_of_Lzw {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : DispStabFootLzw (L := L) arI AR MR s a σ) : DispStabFootLzx (L := L) arI AR MR s a σ :=
  ⟨h.midRecvSw⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 49) **The native syscall entry, `RunMcWKR` to `RunMcWKR`, with label 88 scoped out (`hNo` [S]) and
`DispStabFootLzx` only** (`hLzx` [J] = {midRecvSw}; globals verbatim as `_sysLzw`; module docstring). `hNo :
KNo88` is transitional, over-wide [S]; the proper native scope, via `LookAt`, excludes only entries whose
invoked slot holds a Thread cap with label = 88. -/
theorem kernel_entry_runMcWKR_sysLzx [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ)
    (hNo : KNo88 (L := L) arI AR s a σ)
    (hLzx : DispStabFootLzx (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzw hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW hR hNo
    (dispStabFootLzw_of_Lzx hnd hLzx)

end

end

end Fl4Proofs.P3.Mc
