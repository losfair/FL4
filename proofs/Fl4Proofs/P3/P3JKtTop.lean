/-
P3 (line p3J, gen 21): **the heap-type invariant `KhWF` across the non-syscall entries** (spec side only; outside
the `JAtZ` cone), and gen 20's `…FootK` premises without `CnWF`.

* **`KhWF σ`** (l4v `valid_objs`' `a_type` part: `well_formed_cnode_n` of every CNode (`valid_cs_size`) and
  `valid_sched_context_size` of every SC): no heap object has a garbage `a_type`. It reads only P3JKtF's `ktV`
  (`khWF_of_ktV`), so every `KQ` step keeps it. It gives gen 20's `CnWF` (`cnWF_of_khWF`). `CnWF` alone is not
  kept by `set_object`: a malformed CNode and a malformed SC can share the garbage `a_type`, so the invariant is the
  stronger `KhWF`.
* `next_domain`, `schedule` (`kq_schedule`), the non-syscall events' `fl4CallKernel` (**`kq_fl4CallKernel_other`**),
  and `fl4SyscallFaultIP` keep `ktV`; **`khWF_evOut`**: every `EvOut fip ev` outcome of a non-syscall event from a
  `KhWF` state is `KhWF`.
* **`khWF_fInit`**: the spec boot state `JBootQ.fInitASt` is `KhWF` (IRQ CNodes `emptyCnode 0`, the idle TCB, the
  idle SC of size 0, the three global tables).
* Multicore run (namespace `Mc`): **`RunMcWK := RunMcW ∧ KhWF`**, **`StepU Z Cs s s' := WritesIn s s' (ProjW H Cs s)
  ∧ UtMem Z.th s s'`**, premises **`IrqFootU` / `UserFootU` / `VmfFootU` / `SysUFootU`** [J] = gen 20's `…FootK`
  with `StepU` for `StepK` (no `CnWF σ'`), and tops **`kernel_entry_runMcWK_irqU` / `_userU` / `_vmfU` / `_sysUU`**
  (from `RunMcWK` to `RunMcWK`; U45nv's globals as gen 20's tops). **`runMcWK_w2`**: the start at the 2-core boot
  witness.

Named premises: `IrqFootU`, `UserFootU`, `VmfFootU`, `SysUFootU` [J] (above); U45nv's globals as in
`kernel_entry_runCK`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JKtE
import Fl4Proofs.P3.P3JMcFootK
open Classical

namespace Fl4Proofs.P3.SInvKt
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000

theorem kq_nextDomain : KQ (nextDomain (Z := Unit)) := by
  unfold nextDomain
  exact dk_bind (dk_modify fun _ => rfl) fun _ => kq_doExtendedOp _

macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_nextDomain)

set_option maxHeartbeats 4000000 in
theorem kq_scheduleChooseNewThread : KQ (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_scheduleChooseNewThread)

set_option maxHeartbeats 4000000 in
theorem kq_schedule : KQ (schedule (Z := Unit)) := by
  unfold schedule; kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_schedule)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps the heap's types at every non-syscall event.** -/
theorem kq_fl4CallKernel_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    KQ (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  rw [fl4HandleEvent_other rep ev h]
  refine dk_bind (dke_handleE (kqe_handleEvent_other ev h) fun _ => by kq_auto) fun _ => ?_
  exact dk_bind kq_fl4Awaken fun _ => dk_bind kq_schedule fun _ => kq_activateThread

/-! ## The invariant -/

/-- **No heap object of a garbage type** (module docstring). -/
def KhWF (σ : State Unit) : Prop := ∀ o k, σ.kheap o = some k → ∀ n, aType k ≠ .aGarbage n

theorem khWF_of_ktV {σ σ' : State Unit} (e : ktV σ' = ktV σ) (h : KhWF σ) : KhWF σ' := by
  intro o k hk n hn
  have e1 := congrFun e o
  unfold ktV at e1
  rw [hk] at e1
  cases h0 : σ.kheap o with
  | none => rw [h0] at e1; cases e1
  | some k0 =>
    rw [h0] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    exact h o k0 h0 n (by rw [← e1, hn])

theorem cnWF_of_khWF {σ : State Unit} (h : KhWF σ) : Fl4Proofs.P3.Mc.CnWF σ := by
  intro o r cs hk
  by_contra hw
  exact h o _ hk (cteLevelBits + r) (by simp only [aType, if_neg hw])

/-- **`KhWF` at every outcome of a non-syscall event** (with or without the FaultIP write). -/
theorem khWF_evOut {fip : Bool} {ev : Event} (hev : ∀ c, ev ≠ .syscallEvent c) {σ σ' : State Unit} (h : KhWF σ)
    (hO : EvOut fip ev σ σ') : KhWF σ' := by
  cases fip with
  | false => exact khWF_of_ktV (kq_fl4CallKernel_other true ev hev σ _ hO) h
  | true =>
    obtain ⟨w, hw, hy⟩ := hO
    have h1 := khWF_of_ktV (kq_fl4SyscallFaultIP σ.curThread σ w hw) h
    exact khWF_of_ktV (kq_fl4CallKernel_other true ev hev w.2 _ hy) h1

/-- **`KhWF` at the spec boot state** (module docstring). -/
theorem khWF_fInit : KhWF Fl4Proofs.P3.JBootQ.fInitASt := by
  intro o k hk n hn
  have hB := Fl4Proofs.P3.JBootQ.bootHeap_fInit
  have hk' : Fl4Proofs.P3.JBoot.fInitKheap o = some k := hk
  rcases hB.obj o k hk' with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hB.tcb] at hk'; cases hk'; simp [aType] at hn
  · rw [hB.sc] at hk'; cases hk'
    simp only [aType] at hn
    rw [if_pos (by unfold validSchedContextSize minSchedContextBits untypedMaxBits; decide)] at hn
    cases hn
  · simp only [Fl4Proofs.P3.JBootQ.cn0, aType] at hn
    rw [if_pos (by
      unfold wellFormedCnodeN dom emptyCnode
      ext x; simp)] at hn
    cases hn
  all_goals simp [aType] at hn

end

end Fl4Proofs.P3.SInvKt

namespace Fl4Proofs.P3.Mc
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ Fl4Proofs.P3.SInvKt

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The multicore run predicate with the heap-type invariant** (module docstring). -/
def RunMcWK (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunMcW (L := L) arI AR MR s a σ ∧ KhWF σ

/-- **The FL4-side step facts** (`StepK` without `CnWF`). -/
def StepU (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s s' : S) : Prop :=
  P1.WritesIn st s s' (ProjW (L := L) H Cs s) ∧ UtMem (L := L) Z.th s s'

/-- **`IrqFootU` [J]**: gen 20's `IrqFootK` without `CnWF` (module docstring). -/
def IrqFootU (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∀ σ', EvOut false .interrupt σ σ' →
        StepU (L := L) Z H Cs s r.1 ⦄

/-- **`UserFootU` [J]**: gen 20's `UserFootK` without `CnWF`. -/
def UserFootU (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∀ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' →
        StepU (L := L) Z H Cs s r.1 ⦄

/-- **`VmfFootU` [J]**: gen 20's `VmfFootK` without `CnWF`. -/
def VmfFootU (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType),
      σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∀ σ', EvOut false (.vmFaultEvent ft) σ σ' →
        StepU (L := L) Z H Cs s r.1 ⦄

/-- **`SysUFootU` [J]**: gen 20's `SysUFootK` without `CnWF`. -/
def SysUFootU (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → ∀ (n : I64), σ.curThread ≠ σ.idleThread →
      UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∀ ev σ', KEvSpec (.sysU n) true ev → EvOut true ev σ σ' →
        StepU (L := L) Z H Cs s r.1 ⦄

variable {arI AR MR}

theorem irqFootK_of_U {s : S} {a : A} {σ : Fl4Spec.State Unit} (hK : KhWF σ)
    (h : IrqFootU (L := L) arI AR MR s a σ) : IrqFootK (L := L) arI AR MR s a σ :=
  fun Z H Cs Ac Lst D J hV w a1 hw => WP.spec_mono (h Z H Cs Ac Lst D J hV w a1 hw) fun r hr σ' hO =>
    ⟨(hr σ' hO).1, (hr σ' hO).2, cnWF_of_khWF (khWF_evOut (fun c e => by cases e) hK hO)⟩

theorem userFootK_of_U {s : S} {a : A} {σ : Fl4Spec.State Unit} (hK : KhWF σ)
    (h : UserFootU (L := L) arI AR s a σ) : UserFootK (L := L) arI AR s a σ :=
  fun Z H Cs Ac Lst D J hV n c hct hu => WP.spec_mono (h Z H Cs Ac Lst D J hV n c hct hu) fun r hr σ' hO =>
    ⟨(hr σ' hO).1, (hr σ' hO).2, cnWF_of_khWF (khWF_evOut (fun c e => by cases e) hK hO)⟩

theorem vmfFootK_of_U {s : S} {a : A} {σ : Fl4Spec.State Unit} (hK : KhWF σ)
    (h : VmfFootU (L := L) arI AR s a σ) : VmfFootK (L := L) arI AR s a σ :=
  fun Z H Cs Ac Lst D J hV ad c ft hct hv => WP.spec_mono (h Z H Cs Ac Lst D J hV ad c ft hct hv) fun r hr σ' hO =>
    ⟨(hr σ' hO).1, (hr σ' hO).2, cnWF_of_khWF (khWF_evOut (fun c e => by cases e) hK hO)⟩

theorem sysUFootK_of_U {s : S} {a : A} {σ : Fl4Spec.State Unit} (hK : KhWF σ)
    (h : SysUFootU (L := L) arI AR s a σ) : SysUFootK (L := L) arI AR s a σ :=
  fun Z H Cs Ac Lst D J hV n hct hU hND => WP.spec_mono (h Z H Cs Ac Lst D J hV n hct hU hND)
    fun r hr ev σ' hev hO =>
      ⟨(hr ev σ' hev hO).1, (hr ev σ' hev hO).2, cnWF_of_khWF (khWF_evOut (KEvSpec.not_sys hev) hK hO)⟩

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, `RunMcWK` to `RunMcWK`, with `IrqFootU`** (module docstring; `hFt` [J]). -/
theorem kernel_entry_runMcWK_irqU [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : IrqFootU (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  refine WP.spec_mono (kernel_entry_runMcW_irqK hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hDR hFpu hFW
    hR.1 (irqFootK_of_U hR.2 hFt) w a1 hw) ?_
  rintro r ⟨σ', hO, hC⟩
  exact ⟨σ', hO, hC, khWF_evOut (fun c e => by cases e) hR.2 hO⟩

set_option maxHeartbeats 4000000 in
/-- **The user-exception entry on any core, `RunMcWK` to `RunMcWK`, with `UserFootU`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_userU [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : UserFootU (L := L) arI AR s a σ) :
    ∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n c hct hu
  refine WP.spec_mono (kernel_entry_runMcW_userK hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW
    hR.1 (userFootK_of_U hR.2 hFt) n c hct hu) ?_
  rintro r ⟨σ', hO, hC⟩
  exact ⟨σ', hO, hC, khWF_evOut (fun c e => by cases e) hR.2 hO⟩

set_option maxHeartbeats 4000000 in
/-- **The VM-fault entry on any core, `RunMcWK` to `RunMcWK`, with `VmfFootU`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_vmfU [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : VmfFootU (L := L) arI AR s a σ) :
    ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro ad c ft hct hv
  refine WP.spec_mono (kernel_entry_runMcW_vmfK hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW
    hR.1 (vmfFootK_of_U hR.2 hFt) ad c ft hct hv) ?_
  rintro r ⟨σ', hO, hC⟩
  exact ⟨σ', hO, hC, khWF_evOut (fun c e => by cases e) hR.2 hO⟩

set_option maxHeartbeats 4000000 in
/-- **The unknown-syscall entry on any core, `RunMcWK` to `RunMcWK`, with `SysUFootU`** (`hFt` [J]). -/
theorem kernel_entry_runMcWK_sysUU [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWK (L := L) arI AR MR s a σ)
    (hFt : SysUFootU (L := L) arI AR s a σ) :
    ∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
        RunMcWK (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro n hct hU hND
  refine WP.spec_mono (kernel_entry_runMcW_sysUK hARI hA hnd hM hIp hKD hPAi hIA hT hmax htu hRef hSX hDR hFpu hFW
    hR.1 (sysUFootK_of_U hR.2 hFt) n hct hU hND) ?_
  rintro r ⟨ev, σ', hK, hO, hC⟩
  exact ⟨ev, σ', hK, hO, hC, khWF_evOut (KEvSpec.not_sys hK) hR.2 hO⟩

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.Mc

/-- **`RunMcWK` at the 2-core boot witness.** -/
theorem runMcWK_w2 : RunMcWK (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨runMcW_w2, SInvKt.khWF_fInit⟩

end Fl4Proofs.P3.JBootQ.M2
