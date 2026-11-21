/-
P3 (DESIGN.md §9), invariant line G1 (rd14g, rd14f handoff (c)): **`PerfF` for
rd13b's frame arms** (rd14b's `Cov` but Notification / Endpoint; spec side
only).

* **`perfF_sve`** / **`perfF_svm`**: a perform that is an `SVS ∧ cfS` step
  (rd13b's `perfA_sve` / rd12b's `perfA_svm` shape) and keeps rd14c's `QT ct`
  has `PerfF` (rd14g C's `perfF_q`: RT / CBa of ct carried by `SVS` from the
  Restart state, where rd14g C's `rtc_ec` gives them).
* `QT ct` by rd8d's `TV` family (`qt_of_tv`: no TCB's state, fault or SC is
  written by these arms); the `SVS` / `cfS` facts as in rd13b / rd12b.
* The arms: Domain, IRQ control, IRQ ack, FL4 TCB, CNode insert / move /
  rotate, TCB setTLSBase / setFlags / notificationControl / register arms
  without suspend / resume, every l4v arch arm but ASID control, PML4 flush,
  DeriveSubframe, TestAndClearAccessed; `CovFF`, **`armF_covFF`**.
* Notification: rd14b's `bl_sendSignal` / `cp_sendSignalU` give `TB`, `qt_sendSignal`
  (`qt14g_auto`: only Running / Restart / Inactive writes); **`perfF_notification`**, `CovN`.
* `CF14g2 := CF14g ∨ CovFF ∨ CovN`, `armFU_cf14g2`; tops **`kcall_rdyOffG2`** /
  **`kentry_rdyOffG2`** (no PerfA input; PerfF asked only outside `CF14g2`).
-/
import Fl4Proofs.P3.SpecInvRd14gD
open Classical

namespace Fl4Proofs.P3.SInvR.A14g
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvQ Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.A12b Fl4Proofs.P3.SInvR.A13b Fl4Proofs.P3.SInvR.A14b Fl4Proofs.P3.SInvR.A14c
open Fl4Proofs.P3.SInvR.A14d Fl4Proofs.P3.SInvR.A14e Fl4Proofs.P3.SInvR.A14f

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The generic arm -/

theorem perfF_sve {σ0 u : State Unit} {oper : Fl4Invocation} (h : RF σ0 u)
    (h1 : SVK.SVE (fl4PerformInvocation (Z := Unit) false false true oper))
    (h2 : CFKE (fl4PerformInvocation (Z := Unit) false false true oper))
    (h3 : IKE (QT σ0.curThread) (fl4PerformInvocation (Z := Unit) false false true oper)) :
    PerfF σ0 oper u := by
  obtain ⟨hR, hC⟩ := rtc_ec h.bs (ec_of_tb h.tb)
  refine perfF_q fun y hy _ _ => ?_
  have hS := h1 u y hy
  exact ⟨cf_curThread ((h2 u y hy).trans h.tb.cf), h3 u h.qt y hy, B8d.rT_svs hR hS, B8i.cba_sv hC hS⟩

theorem perfF_svm {σ0 u : State Unit} {oper : Fl4Invocation} {β : Type} {m : NonDet (State Unit) β}
    (hm : ∀ s, (fl4PerformInvocation (Z := Unit) false false true oper).run s =
      (NonDetE.liftE (ε := Unit) (m >>= fun _ => pure [])).run s)
    (h : RF σ0 u) (h1 : SVK.SVM m) (h2 : CFK m) (h3 : IK (QT σ0.curThread) m) : PerfF σ0 oper u := by
  obtain ⟨hR, hC⟩ := rtc_ec h.bs (ec_of_tb h.tb)
  refine perfF_q fun y hy _ _ => ?_
  rw [hm] at hy
  obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hy
  obtain ⟨v, hv, hw⟩ := hw
  have hw' := Set.mem_singleton_iff.1 hw
  subst hw'
  have hS := h1 u v hv
  exact ⟨cf_curThread ((h2 u v hv).trans h.tb.cf), h3 u h.qt v hv, B8d.rT_svs hR hS, B8i.cba_sv hC hS⟩

/-! ## The arms -/

theorem perfF_domain {σ0 u : State Unit} (d : DomainInvocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeDomain d) u :=
  perfF_svm (m := invokeDomain (Z := Unit) d) (fun _ => rfl) h (sv_invokeDomain d) (cfk_invokeDomain d)
    (qt_of_tv _ fun _ => by
      unfold invokeDomain; split
      · unfold invokeSetDomain archPrepareSetDomain setDomain threadSetDomain; tv_auto
      · unfold domainSetStart; tv_auto
      · unfold domainScheduleConfigure; tv_auto)

theorem perfF_irqControl {σ0 u : State Unit} (i : Fl4IrqControlInvocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeIRQControl i) u :=
  perfF_sve h (by simp only [fl4PerformInvocation]; exact SVK.sve_bind (sve_irqControl i) fun _ => SVK.sve_returnOk _)
    (by simp only [fl4PerformInvocation]; exact Vs.dke_bind (cfk_irqControl i) fun _ => Vs.dke_returnOk _)
    (qt_of_tv _ fun _ => by
      simp only [fl4PerformInvocation, invokeFl4IrqControl, invokeIrqControl, archInvokeIrqControl, setIrqState,
        updateIrqState, withoutPreemption]
      tv_auto)

theorem perfF_irqAck {σ0 u : State Unit} (irq : Irq) (h : RF σ0 u) :
    PerfF σ0 (.invokeIRQHandler (.aCKIrq irq)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, invokeIrqHandler, archInvokeIrqHandler]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeIrqHandler, archInvokeIrqHandler]; cfk_auto)
    (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, invokeIrqHandler, archInvokeIrqHandler]; tv_auto)

theorem perfF_fl4Tcb {σ0 u : State Unit} (i : Fl4TcbInvocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeFl4TCB i) u := by
  cases i <;> refine perfF_sve h ?_ ?_ ?_ <;> simp only [fl4PerformInvocation, invokeFl4Tcb, Fl4Spec.setFlags]
  all_goals first
    | (sv_auto; done)
    | (cfk_auto; done)
    | exact sve_fl4SetFlags _ _ _
    | (refine qt_of_tv _ fun _ => ?_; tv_auto; done)
    | (refine qt_of_tv _ fun _ => ?_; tv_auto; all_goals (unfold NonDet.when; split <;> tv_auto); done)

theorem perfF_cnodeInsert {σ0 u : State Unit} (c : Cap) (a b : CslotPtr) (h : RF σ0 u) :
    PerfF σ0 (.invokeCNode (.insertCall c a b)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; tv_auto)

theorem perfF_cnodeMove {σ0 u : State Unit} (c : Cap) (a b : CslotPtr) (h : RF σ0 u) :
    PerfF σ0 (.invokeCNode (.moveCall c a b)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove]; tv_auto)

theorem perfF_cnodeRotate {σ0 u : State Unit} (c1 c2 : Cap) (a b d : CslotPtr) (h : RF σ0 u) :
    PerfF σ0 (.invokeCNode (.rotateCall c1 c2 a b d)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove, capSwap]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeCnode, withoutPreemption]; cfk_auto)
    (qt_of_tv _ fun _ => by
      simp only [fl4PerformInvocation, invokeCnode, withoutPreemption, capMove, capSwap]; tv_auto)

theorem perfF_tlsBase {σ0 u : State Unit} (t : ObjRef) (v : Data) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.setTLSBase t v)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo]; sv_auto)
    (by simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo]; cfk_auto)
    (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo]; tv_auto)

theorem perfF_tcbFlags {σ0 u : State Unit} (t : ObjRef) (c f : TcbFlags) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.setFlags t c f)) u := by
  refine perfF_sve h ?_ ?_ ?_ <;> simp only [fl4PerformInvocation, invokeTcb, archPostSetFlags, Fl4Spec.setFlags]
  · sv_auto
  · cfk_auto
  · exact qt_of_tv _ fun _ => by tv_auto

theorem perfF_ntfnControl {σ0 u : State Unit} (t : ObjRef) (n : Option ObjRef) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.notificationControl t n)) u := by
  cases n
  · exact perfF_sve h (by simp only [fl4PerformInvocation, invokeTcb, unbindNotification, doUnbindNotification]; sv_auto)
      (by simp only [fl4PerformInvocation, invokeTcb]; cfk_auto)
      (qt_of_tv _ fun _ => by
        simp only [fl4PerformInvocation, invokeTcb, unbindNotification, doUnbindNotification]; tv_auto)
  · exact perfF_sve h (by simp only [fl4PerformInvocation, invokeTcb, bindNotification]; sv_auto)
      (by simp only [fl4PerformInvocation, invokeTcb, bindNotification]; cfk_auto)
      (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, invokeTcb, bindNotification]; tv_auto)

theorem perfF_readRegisters {σ0 u : State Unit} (src : ObjRef) (n a : _) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.readRegisters src false n a)) u := by
  refine perfF_sve h ?_ ?_ ?_ <;>
    simp only [fl4PerformInvocation, invokeTcb, NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · exact qt_of_tv _ fun _ => by tv_auto

theorem perfF_writeRegisters {σ0 u : State Unit} (dest : ObjRef) (v a : _) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.writeRegisters dest false v a)) u := by
  refine perfF_sve h ?_ ?_ ?_ <;>
    simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo, archPostModifyRegisters,
      NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · exact qt_of_tv _ fun _ => by tv_auto

theorem perfF_copyRegisters {σ0 u : State Unit} (dest src : ObjRef) (f i : Bool) (a : _) (h : RF σ0 u) :
    PerfF σ0 (.invokeTCB (.copyRegisters dest src false false f i a)) u := by
  refine perfF_sve h ?_ ?_ ?_ <;>
    simp only [fl4PerformInvocation, invokeTcb, archGetSanitiseRegisterInfo, archPostModifyRegisters,
      NonDet.when, Bool.false_eq_true, ↓reduceIte]
  · sv_auto
  · cfk_auto
  · exact qt_of_tv _ fun _ => by tv_auto

theorem perfF_deriveSubframe {σ0 u : State Unit} (i : Fl4SubframeInvocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeArchObject (.deriveSubframe i)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performDeriveSubframe]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (qt_of_tv _ fun _ => by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performDeriveSubframe]; tv_auto)

theorem perfF_testAndClear {σ0 u : State Unit} (p : ObjRef) (h : RF σ0 u) :
    PerfF σ0 (.invokeArchObject (.testAndClearAccessed p)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performTestAndClearAccessed]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (qt_of_tv _ fun _ => by
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation, performTestAndClearAccessed]; tv_auto)

theorem perfF_pml4Flush {σ0 u : State Unit} (i : Fl4Pml4Invocation) (h : RF σ0 u) :
    PerfF σ0 (.invokeArchObject (.pml4Flush i)) u :=
  perfF_sve h (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archNoReturn]; sv_auto)
    (by simp only [fl4PerformInvocation, fl4ArchPerformInvocation]; cfk_auto)
    (qt_of_tv _ fun _ => by
      cases i
      simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archNoReturn, performPml4Flush, flushAll]
      tv_auto)

theorem perfF_archSpec {σ0 u : State Unit} (i : ArchInvocation) (hi : ∀ o, i ≠ .invokeASIDControl o)
    (h : RF σ0 u) : PerfF σ0 (.invokeArchObject (.spec i)) u := by
  cases i
  case invokeASIDControl o => exact absurd rfl (hi o)
  all_goals refine perfF_sve h ?_ ?_ ?_ <;>
    simp only [fl4PerformInvocation, fl4ArchPerformInvocation, archPerformInvocation, archNoReturn]
  all_goals first
    | (cfk_auto; done)
    | (refine SVK.sve_liftE ?_; sv_auto; done)
    | (refine qt_of_tv _ fun _ => ?_; tv_auto; done)
    | skip

/-- rd14b's `Cov` without Notification / Endpoint. -/
def CovFF : Fl4Invocation → Prop
  | .invokeDomain _ => True
  | .invokeIRQControl _ => True
  | .invokeIRQHandler (.aCKIrq _) => True
  | .invokeFl4TCB _ => True
  | .invokeCNode (.insertCall _ _ _) => True
  | .invokeCNode (.moveCall _ _ _) => True
  | .invokeCNode (.rotateCall _ _ _ _ _) => True
  | .invokeTCB (.setTLSBase _ _) => True
  | .invokeTCB (.setFlags _ _ _) => True
  | .invokeTCB (.notificationControl _ _) => True
  | .invokeTCB (.readRegisters _ false _ _) => True
  | .invokeTCB (.writeRegisters _ false _ _) => True
  | .invokeTCB (.copyRegisters _ _ false false _ _ _) => True
  | .invokeArchObject (.spec (.invokeASIDControl _)) => False
  | .invokeArchObject _ => True
  | _ => False

theorem armF_covFF : ArmF CovFF := by
  intro σ0 u b hc h
  match b, hc with
  | .invokeDomain d, _ => exact perfF_domain d h
  | .invokeIRQControl i, _ => exact perfF_irqControl i h
  | .invokeIRQHandler (.aCKIrq irq), _ => exact perfF_irqAck irq h
  | .invokeFl4TCB i, _ => exact perfF_fl4Tcb i h
  | .invokeCNode (.insertCall c a d), _ => exact perfF_cnodeInsert c a d h
  | .invokeCNode (.moveCall c a d), _ => exact perfF_cnodeMove c a d h
  | .invokeCNode (.rotateCall c1 c2 a d e), _ => exact perfF_cnodeRotate c1 c2 a d e h
  | .invokeTCB (.setTLSBase t v), _ => exact perfF_tlsBase t v h
  | .invokeTCB (.setFlags t c f), _ => exact perfF_tcbFlags t c f h
  | .invokeTCB (.notificationControl t n), _ => exact perfF_ntfnControl t n h
  | .invokeTCB (.readRegisters src false n a), _ => exact perfF_readRegisters src n a h
  | .invokeTCB (.writeRegisters d false v a), _ => exact perfF_writeRegisters d v a h
  | .invokeTCB (.copyRegisters d src false false f i a), _ => exact perfF_copyRegisters d src f i a h
  | .invokeArchObject (.spec (.invokePageTable i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokePageDirectory i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokePDPT i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokePage i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokeASIDPool i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokeIOPort i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.spec (.invokeIOPortControl i)), _ => exact perfF_archSpec _ (fun _ e => by cases e) h
  | .invokeArchObject (.pml4Flush i), _ => exact perfF_pml4Flush i h
  | .invokeArchObject (.deriveSubframe i), _ => exact perfF_deriveSubframe i h
  | .invokeArchObject (.testAndClearAccessed p), _ => exact perfF_testAndClear p h
  | .invokeArchObject (.spec (.invokeASIDControl _)), hc => exact False.elim hc
  | .invokeUntyped _, hc => exact False.elim hc
  | .invokeEndpoint _ _ _ _, hc => exact False.elim hc
  | .invokeNotification _ _, hc => exact False.elim hc
  | .invokeReply _ _, hc => exact False.elim hc
  | .invokeSchedContext _, hc => exact False.elim hc
  | .invokeSchedControl _, hc => exact False.elim hc
  | .invokeIRQHandler (.setIRQHandler _ _ _), hc => exact False.elim hc
  | .invokeIRQHandler (.clearIRQHandler _), hc => exact False.elim hc
  | .invokeCNode (.revokeCall _), hc => exact False.elim hc
  | .invokeCNode (.deleteCall _), hc => exact False.elim hc
  | .invokeCNode (.cancelBadgedSendsCall _), hc => exact False.elim hc
  | .invokeTCB (.readRegisters _ true _ _), hc => exact False.elim hc
  | .invokeTCB (.writeRegisters _ true _ _), hc => exact False.elim hc
  | .invokeTCB (.copyRegisters _ _ true _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.copyRegisters _ _ false true _ _ _), hc => exact False.elim hc
  | .invokeTCB (.threadControlCaps _ _ _ _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.threadControlSched _ _ _ _ _ _), hc => exact False.elim hc
  | .invokeTCB (.suspend _), hc => exact False.elim hc
  | .invokeTCB (.resume _), hc => exact False.elim hc

/-! ## Notification -/

set_option maxHeartbeats 4000000 in
theorem qt_sendSignal (t ep : ObjRef) (bd : Badge) : IK (QT t) (sendSignal (Z := Unit) ep bd) := by
  unfold sendSignal; qt14g_auto

theorem perfF_notification {σ0 u : State Unit} (ep : ObjRef) (bd : Badge) (h : RF σ0 u) :
    PerfF σ0 (.invokeNotification ep bd) u := by
  refine perfF_tbq h.bs fun y hy a ha => ?_
  have hy' : y ∈ ((withoutPreemption (sendSignal (Z := Unit) ep bd) >>= fun _ =>
      (NonDetE.returnOk [] : PMonad Unit (List Data))).run u).1 := hy
  obtain ⟨z, hz, ⟨u0, -, hy2⟩ | ⟨e, he, -⟩⟩ := ft_mem_bindE hy'
  · unfold withoutPreemption at hz
    obtain ⟨w, hw, rfl⟩ := ft_mem_liftE hz
    have ey : y = (.ok [], w.2) := Set.mem_singleton_iff.1 hy2
    subst ey
    have hbl := bl_sendSignal σ0.curThread σ0.curSc ep bd u
      ⟨fun p x' hx' e => by subst e; exact h.bd x' hx', h.sc⟩ w hw
    exact ⟨⟨(cfk_sendSignal' ep bd u w hw).trans h.kp.1,
      (cp_sendSignalU ep bd σ0 σ0.curSc u ⟨A11.kp_curSc h.kp, h.kp.2.1⟩ w hw).2,
      fun x hx => hbl.1 σ0.curThread x hx rfl, hbl.2⟩, qt_sendSignal _ ep bd u h.qt w hw⟩
  · unfold withoutPreemption at hz
    obtain ⟨w, -, rfl⟩ := ft_mem_liftE hz
    cases he

def CovN : Fl4Invocation → Prop
  | .invokeNotification _ _ => True
  | _ => False

theorem armF_covN : ArmF CovN := by
  intro σ0 u b hc h
  cases b
  case invokeNotification ep bd => exact perfF_notification ep bd h
  all_goals exact (hc : False).elim

/-- rd14g D's covered set, the frame arms and Notification. -/
def CF14g2 (b : Fl4Invocation) : Prop := CF14g b ∨ CovFF b ∨ CovN b

theorem armFU_cf14g2 : ArmFU CF14g2 := armFU_cf14g.or ((armFU_of armF_covFF).or (armFU_of armF_covN))

/-- **Today's tops**: no `PerfA` input; `PerfF` asked only outside `CF14g2` (Endpoint, SchedControl
configure, CNode delete / revoke, ThreadControlCaps / ThreadControlSched). -/
theorem kcall_rdyOffG2 {σ : State Unit} (hnd : numDomains = 1) (rep : Bool) (ev : Event) (h : B8w.SInvW σ)
    (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hF : ∀ c, ev = .syscallEvent c → InvFc CF14g2 c σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, B8w.SInvW y.2 :=
  kcall_rdyOffF armAKU_all armFU_cf14g2 hnd rep ev h hev (fun c _ => invRc_all c σ) hF

theorem kentry_rdyOffG2 {σ : State Unit} (hnd : numDomains = 1) (c : Syscall) (h : B8w.SInvW σ)
    (hct : σ.curThread ≠ σ.idleThread)
    (hW : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, InvFc CF14g2 c w.2) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, B8w.SInvW y.2 :=
  kentry_rdyOffF armAKU_all armFU_cf14g2 hnd c h hct fun w hw => ⟨invRc_all c w.2, hW w hw⟩

end

end Fl4Proofs.P3.SInvR.A14g
