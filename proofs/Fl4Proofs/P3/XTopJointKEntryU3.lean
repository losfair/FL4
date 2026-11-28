/-
P3 (DESIGN.md §9), invariant line G4 (g5i, KENTRY-PLAN g5i): **the native
syscall step without an exit premise**. With SpecInvUtZP's `perfGapZ`, `ZR`
(`SpecUtZ ∧ UtPgR`) holds at every syscall exit (`SInvUZ.kentry_zr`), so the
induction `JReachU3` is `JReachU2` whose `step` asks neither `SpecUtZ σ'` nor
`UtPgR σ'` (`JReachU3.toU2` / `JReachU3.ofU2`: the same states), and
**`kernel_entry_reachU3`** is m73's `kernel_entry_reachU2F` (no
`FastFaultOK`) whose syscall clause ends in `SpecUtZ σ' ∧ UtPgR σ' ∧ JReachU3`
with no premise.
-/
import Fl4Proofs.P3.XTopJointKEntryU2F
import Fl4Proofs.P3.SpecInvUtZP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- The carried untyped invariant is part of `SInvX`. -/
theorem sinvX_ut3 {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvU.UtInv3 σ := hX.1.1.1.1.1.1.1.1.ut

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states** (module docstring): `JReachU2` with a native syscall step
asking nothing of its exit. -/
inductive JReachU3 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → SInvIP σ → MR a σ.machineState → SInvUZ.UtPgR σ →
        JReachU3 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachU3 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachU3 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachU3 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachU3 s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachU3 s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' →
      JReachU3 s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachU3 s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachU3 s' a' σ'
  | trap {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (v : U64)
      (ev : Fl4Spec.Event) :
      JReachU3 s a σ → σ.curThread ≠ σ.idleThread → v.val < 256 → KEvSpec (.trap v) true ev →
      syscall.handle_trap_syscall st arI s a v = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachU3 s' a' σ'
  | sysU {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (ev : Fl4Spec.Event) :
      JReachU3 s a σ → σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      KEvSpec (.sysU n) true ev → syscall.handle_syscall st arI s a n = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachU3 s' a' σ'

variable {arI AR MR}

/-- Every `JReachU2` state is a `JReachU3` state (the step's exit premises dropped). -/
theorem JReachU3.ofU2 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachU2 (L := L) arI AR MR s a σ) :
    JReachU3 (L := L) arI AR MR s a σ := by
  induction h with
  | start J hvx hX hI hR hP => exact JReachU3.start J hvx hX hI hR hP
  | step n c _ hct hn hv hy hRJ _ _ ih => exact JReachU3.step n c ih hct hn hv hy hRJ
  | irq w _ hI hv hO hRJ ih => exact JReachU3.irq w ih hI hv hO hRJ
  | user n c _ hct hU hv hO hRJ ih => exact JReachU3.user n c ih hct hU hv hO hRJ
  | vmf ad c ft _ hct hV hv hO hRJ ih => exact JReachU3.vmf ad c ft ih hct hV hv hO hRJ
  | trap v ev _ hct hv8 hK hv hO hRJ ih => exact JReachU3.trap v ev ih hct hv8 hK hv hO hRJ
  | sysU n ev _ hct hU hD hK hv hO hRJ ih => exact JReachU3.sysU n ev ih hct hU hD hK hv hO hRJ

/-- **Every `JReachU3` state is a `JReachU2` state**: the syscall exit's `SpecUtZ ∧ UtPgR`
from `ZR` (`SInvUZ.kentry_zr`, no premise). -/
theorem JReachU3.toU2 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachU3 (L := L) arI AR MR s a σ) : JReachU2 (L := L) arI AR MR s a σ := by
  induction h with
  | start J hvx hX hI hR hP => exact JReachU2.start J hvx hX hI hR hP
  | step n c _ hct hn hv hy hRJ ih =>
    obtain ⟨-, -, -, -, -, -, -, hX, -⟩ := jreach_invU2 hnd ih
    have hZ := SInvUZ.kentry_zr c (sinvX_ut3 hX) ih.zr _ hy
    exact JReachU2.step n c ih hct hn hv hy hRJ (specUtZ_of_zr hZ) (SInvUZ.zr_iff.1 hZ).2
  | irq w _ hI hv hO hRJ ih => exact JReachU2.irq w ih hI hv hO hRJ
  | user n c _ hct hU hv hO hRJ ih => exact JReachU2.user n c ih hct hU hv hO hRJ
  | vmf ad c ft _ hct hV hv hO hRJ ih => exact JReachU2.vmf ad c ft ih hct hV hv hO hRJ
  | trap v ev _ hct hv8 hK hv hO hRJ ih => exact JReachU2.trap v ev ih hct hv8 hK hv hO hRJ
  | sysU n ev _ hct hU hD hK hv hO hRJ ih => exact JReachU2.sysU n ev ih hct hU hD hK hv hO hRJ

/-- **The unified invariant at every `JReachU3` state** (`jreach_invU2`'s). -/
theorem jreach_invU3 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachU3 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧ VxE Z :=
  jreach_invU2 hnd (h.toU2 hnd)

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **Refinement at every `JReachU3` state** (module docstring): m73's `kernel_entry_reachU2F`
with the native syscall clause asking no exit premise. -/
theorem kernel_entry_reachU3V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU3 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        LargeFrOK Z.G (L.mem s) →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKV42 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  have hJ2 := hJ.toU2 hnd
  have hZ := hJ2.zr
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU2FV hARI hA hnd hM hKD hIo hIoa hPA hIA hmrt hmb hT hmax htu hRef hPI hSX hJ2
  refine ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hLF hflag hK hDL hFin => ?_, fun w a1 hIh hFin => ?_, fun n c hct hU hFin => ?_,
    fun ad c ft hct hV hFin => ?_, fun v hct hv hFin => ?_, fun n hct hU hD hFin => ?_⟩
  · refine WP.spec_mono (hSys n c hct hn hLF hflag hK hDL hFin) fun r ⟨σ', hy, hRJ, hX', hM', h1, h2, hk⟩ => ?_
    have hZ' := SInvUZ.kentry_zr c (sinvX_ut3 hX) hZ _ hy
    exact ⟨σ', hy, hRJ, hX', hM', h1, h2, specUtZ_of_zr hZ', (SInvUZ.zr_iff.1 hZ').2,
      JReachU3.ofU2 (hk (specUtZ_of_zr hZ') (SInvUZ.zr_iff.1 hZ').2)⟩
  · exact WP.spec_mono (hIrq w a1 hIh hFin) fun r ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, JReachU3.ofU2 hk⟩
  · exact WP.spec_mono (hUs n c hct hU hFin) fun r ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, JReachU3.ofU2 hk⟩
  · exact WP.spec_mono (hVm ad c ft hct hV hFin) fun r ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO, hRJ, hX', hM', h1, h2, h3, JReachU3.ofU2 hk⟩
  · exact WP.spec_mono (hTr v hct hv hFin) fun r ⟨ev, σ', hK, hO, hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨ev, σ', hK, hO, hRJ, hX', hM', h1, h2, h3, JReachU3.ofU2 hk⟩
  · exact WP.spec_mono (hSU n hct hU hD hFin) fun r ⟨ev, σ', hK, hO, hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨ev, σ', hK, hO, hRJ, hX', hM', h1, h2, h3, JReachU3.ofU2 hk⟩

end

end

end Fl4Proofs.P3.SInvR.G5
