/-
P3 (DESIGN.md §9), invariant line G1 (rd13b, KENTRY-PLAN rd12b handoff 1):
**per-arm `PerfA` for the arms that keep rd11a's frame** (spec side only).

* `NoErr m`: no outcome of `m` is an error (`noErr_liftE`, `noErr_bind`,
  `noErr_pure`, `noErr_ite`).
* **`perfA_sve`**: an arm whose perform is `SVE ∧ CFKE` with no error
  outcome has `PerfA` from `KP σ0 ∧ CB0` at its start (SpecInvRd12bC's
  `perfA_svm` for a perform that is not syntactically one `liftE`).
* Arms: **`perfA_irqControl`** (every IRQ control invocation, incl. the
  IOAPIC / MSI / remapped issue), **`perfA_irqAck`** (the IRQ handler ack),
  **`perfA_fl4Tcb`** (every FL4 TCB extension), **`perfA_cnodeInsert`**,
  **`perfA_cnodeMove`**, **`perfA_cnodeRotate`**, **`perfA_tlsBase`**,
  **`perfA_tcbFlags`**, **`perfA_ntfnControl`** (bind / unbind the bound
  notification), **`perfA_pml4Flush`**, **`perfA_deriveSubframe`**,
  **`perfA_testAndClear`**.
-/
import Fl4Proofs.P3.SpecInvRd12bD
open Classical

namespace Fl4Proofs.P3.SInvR.A13b
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b

noncomputable section

set_option maxHeartbeats 1000000

/-! ## No error outcome -/

/-- No outcome of `m` is an error. -/
def NoErr {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s, ∀ y ∈ (m.run s).1, ∀ e, y.1 ≠ .error e

theorem noErr_liftE {ε α : Type} (m : NonDet (State Unit) α) : NoErr (NonDetE.liftE (ε := ε) m) := by
  intro s y hy e he
  obtain ⟨x, -, rfl⟩ := ft_mem_liftE hy
  cases he

theorem noErr_pure {ε α : Type} (a : α) : NoErr (pure a : NonDetE (State Unit) ε α) := by
  intro s y hy e he
  rw [show y = (.ok a, s) from hy] at he
  cases he

theorem noErr_returnOk {ε α : Type} (a : α) : NoErr (NonDetE.returnOk a : NonDetE (State Unit) ε α) :=
  noErr_pure a

theorem noErr_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : NoErr m) (hf : ∀ a, NoErr (f a)) : NoErr (m >>= f) := by
  intro s y hy e he
  change y ∈ (NonDet.bind (ExceptT.run m) _ s).1 at hy
  obtain ⟨⟨r, s1⟩, hr, hy⟩ := hy
  cases r with
  | error e' => exact hm s _ hr e' rfl
  | ok a => exact hf a s1 y hy e he

theorem noErr_ite {ε α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : NoErr m1)
    (h2 : NoErr m2) : NoErr (if P then m1 else m2) := by
  split <;> assumption

/-- Walks binds / lifts / pure / if of an exception computation. -/
macro "ne_auto" : tactic => `(tactic| repeat' (first
  | exact noErr_liftE _
  | exact noErr_returnOk _
  | exact noErr_pure _
  | (unfold withoutPreemption; exact noErr_liftE _)
  | (refine noErr_bind ?_ fun _ => ?_)
  | (refine noErr_ite _ ?_ ?_)))

/-! ## The generic arm -/

/-- **An arm whose perform keeps every scheduler view and `cfS` and has no
error outcome**: `PerfA` from `KP σ0 ∧ CB0`. -/
theorem perfA_sve {σ0 s : State Unit} {bl call don : Bool} {oper : Fl4Invocation}
    (h1 : SVK.SVE (fl4PerformInvocation (Z := Unit) bl call don oper))
    (h2 : CFKE (fl4PerformInvocation (Z := Unit) bl call don oper))
    (h3 : NoErr (fl4PerformInvocation (Z := Unit) bl call don oper))
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don oper s := by
  intro y hy
  obtain ⟨k, c⟩ := ke_svcf hK hb (h1 s y hy) (h2 s y hy)
  exact ⟨fun _ _ => Or.inl ⟨k, Or.inl c⟩, fun e he => absurd he (h3 s y hy e)⟩

/-! ## Extra leaves -/

/-- Any machine operation keeps `cfS` (RdP's `cfk_doMachineOp` without the
unused `MKF` argument). -/
theorem cfk_dmo {α : Type} (mop : NonDet MachineState α) : CFK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h1] at h2
  obtain ⟨-, e2⟩ := h2
  simp only [Prod.mk.injEq] at e2 h3
  obtain ⟨-, rfl⟩ := e2
  rw [Set.mem_singleton_iff.1 h3] at hx
  rw [Set.mem_singleton_iff.1 hx]
  rfl
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_dmo _)

theorem sv_switchLocalFpuOwner (o : Option ObjRef) : SVK.SVM (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner saveFpuState loadFpuState setX64CurrentFpuOwner
  sv_auto
  all_goals (unfold NonDet.maybeM; split <;> sv_auto)

theorem sv_lazyFpuRestore (t : ObjRef) : SVK.SVM (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; sv_auto
  all_goals exact sv_switchLocalFpuOwner _

theorem cfk_lazyFpuRestore (t : ObjRef) : CFK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; cfk_auto

macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_fpuRelease _)
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact SVK.sv_rescheduleRequired')
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lazyFpuRestore _)
macro_rules | `(tactic| sv_leaf) => `(tactic| (with_reducible refine SVK.sv_threadSet' _ ?_ _); intro _; rfl)
macro_rules | `(tactic| cfk_leaf) => `(tactic| with_reducible exact cfk_lazyFpuRestore _)

/-! ## IRQ control / handler ack -/

theorem sv_updateIrqState (irq : Irq) (st : X64IRQState) : SVK.SVM (updateIrqState (Z := Unit) irq st) := by
  unfold updateIrqState; sv_auto

theorem sv_setIrqState (st : IrqState) (irq : Irq) : SVK.SVM (setIrqState (Z := Unit) st irq) := by
  unfold setIrqState; sv_auto

theorem sve_irqControl (i : Fl4IrqControlInvocation) : SVK.SVE (invokeFl4IrqControl (Z := Unit) i) := by
  unfold invokeFl4IrqControl
  split
  · rename_i j
    unfold invokeIrqControl; split
    · refine SVK.sve_liftE ?_; sv_auto
      all_goals first | exact sv_setIrqState _ _ | exact SVK.sv_capInsert _ _ _
    · unfold archInvokeIrqControl; split <;> (unfold withoutPreemption; refine SVK.sve_liftE ?_; sv_auto)
      all_goals first | exact sv_setIrqState _ _ | exact SVK.sv_capInsert _ _ _ | exact sv_updateIrqState _ _
  · unfold withoutPreemption; refine SVK.sve_liftE ?_; sv_auto
    all_goals first | exact sv_setIrqState _ _ | exact SVK.sv_capInsert _ _ _ | exact sv_updateIrqState _ _

theorem cfk_irqControl (i : Fl4IrqControlInvocation) : CFKE (invokeFl4IrqControl (Z := Unit) i) := by
  unfold invokeFl4IrqControl
  split
  · unfold invokeIrqControl; split
    · unfold setIrqState; cfk_auto
    · unfold archInvokeIrqControl setIrqState; split <;> (unfold withoutPreemption; cfk_auto)
  · unfold withoutPreemption setIrqState; cfk_auto

theorem ne_irqControl (i : Fl4IrqControlInvocation) : NoErr (invokeFl4IrqControl (Z := Unit) i) := by
  unfold invokeFl4IrqControl
  split
  · unfold invokeIrqControl; split
    · exact noErr_liftE _
    · unfold archInvokeIrqControl; split <;> (unfold withoutPreemption; exact noErr_liftE _)
  · unfold withoutPreemption; exact noErr_liftE _

/-- **Every IRQ control invocation.** -/
theorem perfA_irqControl {σ0 s : State Unit} (bl call don : Bool) (i : Fl4IrqControlInvocation)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeIRQControl i) s :=
  perfA_sve (by simp only [fl4PerformInvocation]; exact SVK.sve_bind (sve_irqControl i) fun _ => SVK.sve_returnOk _)
    (by simp only [fl4PerformInvocation]; exact Vs.dke_bind (cfk_irqControl i) fun _ => Vs.dke_returnOk _)
    (by simp only [fl4PerformInvocation]; exact noErr_bind (ne_irqControl i) fun _ => noErr_returnOk _) hK hb

/-- **The IRQ handler ack.** -/
theorem perfA_irqAck {σ0 s : State Unit} (bl call don : Bool) (irq : Irq)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeIRQHandler (.aCKIrq irq)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, invokeIrqHandler, archInvokeIrqHandler]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeIrqHandler, archInvokeIrqHandler]; cfk_auto)
    (by simp only [fl4PerformInvocation]; ne_auto) hK hb

/-! ## FL4 TCB extensions -/

theorem sve_fl4SetFlags (t : ObjRef) (c f : Data) :
    SVK.SVE (invokeFl4Tcb (Z := Unit) (.setFlags t c f)) := by
  simp only [invokeFl4Tcb, Fl4Spec.setFlags]
  refine SVK.sve_liftE ?_
  sv_auto
  all_goals (unfold NonDet.when; split <;> sv_auto)

/-- **Every FL4 TCB extension invocation.** -/
theorem perfA_fl4Tcb {σ0 s : State Unit} (bl call don : Bool) (i : Fl4TcbInvocation)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeFl4TCB i) s := by
  cases i <;> refine perfA_sve ?_ ?_ ?_ hK hb <;> simp only [fl4PerformInvocation, invokeFl4Tcb, Fl4Spec.setFlags]
  all_goals first
    | (ne_auto; done)
    | (sv_auto; done)
    | (cfk_auto; done)
    | exact sve_fl4SetFlags _ _ _

/-! ## CNode insert / move / rotate -/

theorem perfA_cnodeInsert {σ0 s : State Unit} (bl call don : Bool) (c : Cap) (a b : CslotPtr)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeCNode (.insertCall c a b)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (by simp only [fl4PerformInvocation, invokeCnode]; ne_auto) hK hb

theorem perfA_cnodeMove {σ0 s : State Unit} (bl call don : Bool) (c : Cap) (a b : CslotPtr)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeCNode (.moveCall c a b)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (by simp only [fl4PerformInvocation, invokeCnode]; ne_auto) hK hb

theorem perfA_cnodeRotate {σ0 s : State Unit} (bl call don : Bool) (c1 c2 : Cap) (a b d : CslotPtr)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeCNode (.rotateCall c1 c2 a b d)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove, capSwap]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (by simp only [fl4PerformInvocation, invokeCnode]; ne_auto) hK hb

/-! ## TCB register-free arms -/

theorem perfA_tlsBase {σ0 s : State Unit} (bl call don : Bool) (t : ObjRef) (v : Data)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeTCB (.setTLSBase t v)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo]; cfk_auto)
    (by simp only [fl4PerformInvocation, invokeTcb]; ne_auto) hK hb

theorem perfA_tcbFlags {σ0 s : State Unit} (bl call don : Bool) (t : ObjRef) (c f : TcbFlags)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeTCB (.setFlags t c f)) s := by
  refine perfA_sve ?_ ?_ ?_ hK hb <;> simp only [fl4PerformInvocation, invokeTcb, archPostSetFlags, Fl4Spec.setFlags]
  · sv_auto
  · cfk_auto
  · ne_auto

theorem perfA_ntfnControl {σ0 s : State Unit} (bl call don : Bool) (t : ObjRef) (n : Option ObjRef)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) : PerfA σ0 bl call don (.invokeTCB (.notificationControl t n)) s := by
  cases n
  · exact perfA_sve (by simp only [fl4PerformInvocation, invokeTcb, unbindNotification, doUnbindNotification]; sv_auto)
      (by simp only [fl4PerformInvocation, invokeTcb]; cfk_auto)
      (by simp only [fl4PerformInvocation, invokeTcb]; ne_auto) hK hb
  · exact perfA_sve (by simp only [fl4PerformInvocation, invokeTcb, bindNotification]; sv_auto)
      (by simp only [fl4PerformInvocation, invokeTcb, bindNotification]; cfk_auto)
      (by simp only [fl4PerformInvocation, invokeTcb]; ne_auto) hK hb

/-! ## FL4's arch extensions -/

theorem perfA_deriveSubframe {σ0 s : State Unit} (bl call don : Bool) (i : Fl4SubframeInvocation)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeArchObject (.deriveSubframe i)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performDeriveSubframe]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; ne_auto) hK hb

theorem perfA_testAndClear {σ0 s : State Unit} (bl call don : Bool) (p : ObjRef)
    (hK : A11.KP σ0 s) (hb : A11.CB0 s) :
    PerfA σ0 bl call don (.invokeArchObject (.testAndClearAccessed p)) s :=
  perfA_sve (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performTestAndClearAccessed]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; ne_auto) hK hb

end

end Fl4Proofs.P3.SInvR.A13b
