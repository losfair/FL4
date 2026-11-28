/-
P3 (DESIGN.md §9), invariant line G4 (g5h, from g5g's WIP; KENTRY-PLAN g5h):
**`ZR` (l4v `untyped_ranges_zero` with `valid_untyped` for data pages)
carried by the induction**: `JReachU2` / `jreach_invU2` /
`kernel_entry_reachU2` is g5f's `JReachU` with the event constructors
(interrupt, user exception, VM fault, `int $N`, unknown syscall) asking no
exit premise, and the native-syscall constructor asking `SpecUtZ σ' ∧ UtPgR σ'`
of its exit (the untyped perform, SpecInvUtZS4's `PerfGapZ`, is not proved);
the syscall clause is m72's `kernel_entryJ42H` (no `hRP5`).

* The carried invariant is SpecInvUtZW's `ZR` = `SpecUtZ ∧ UtPgR` (`zr_iff`,
  `specUtZ_iff`). `start` asks `UtPgR σ` (one state; lead decision
  2026-11-20: any state with the invariants). Every event keeps `ZR` with no
  premise (`SInvUZ.kcall_zr_other`; the FaultIP write by
  `SInvUZ.zr_fl4SyscallFaultIP`): `zr_evOut`.
* `JReachU2.zr`, `JReachU2.toU` (every `JReachU2` state is a `JReachU` state:
  the `SpecUtZ σ'` of each event exit from `ZR`), **`jreach_invU2`**,
  **`kernel_entry_reachU2`** (`kernel_entry_reachUH`'s clauses; the event
  clauses end in `SpecUtZ σ' ∧ JReachU2`, the syscall clause in `SpecUtZ σ' →
  UtPgR σ' → JReachU2`).
-/
import Fl4Proofs.P3.XTopJointKEntryUH
import Fl4Proofs.P3.SpecInvUtZS4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## `SpecUtZ` and `ZR` -/

theorem specUtZ_iff {σ : Fl4Spec.State Unit} : SpecUtZ σ ↔ SInvUZ.SpecUtZ' σ := by
  constructor
  · intro h p cref b n f hc a h1 h2
    exact h (p, cref) b n f (by rw [SInv.vfh_capAt]; exact hc) a h1 h2
  · intro h sl b n f hc a h1 h2
    exact h sl.1 sl.2 b n f (by rw [← SInv.vfh_capAt]; exact hc) a h1 h2

theorem zr_of_utz {σ : Fl4Spec.State Unit} (h1 : SpecUtZ σ) (h2 : SInvUZ.UtPgR σ) : SInvUZ.ZR σ :=
  SInvUZ.zr_iff.2 ⟨specUtZ_iff.1 h1, h2⟩

theorem specUtZ_of_zr {σ : Fl4Spec.State Unit} (h : SInvUZ.ZR σ) : SpecUtZ σ :=
  specUtZ_iff.2 (SInvUZ.zr_iff.1 h).1

/-- **`ZR` at every event outcome** (no premise; across the FaultIP write). -/
theorem zr_evOut {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (h : SInvUZ.ZR σ)
    (hev : ∀ c, ev ≠ .syscallEvent c) (hO : EvOut fip ev σ σ') : SInvUZ.ZR σ' := by
  cases fip with
  | false => exact SInvUZ.kcall_zr_other true ev hev h _ hO
  | true =>
    obtain ⟨w, hw, hy⟩ := hO
    exact SInvUZ.kcall_zr_other true ev hev (SInvUZ.zr_fl4SyscallFaultIP _ σ h w hw) _ hy

/-! ## The induction -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states, every carried invariant in one induction**
(module docstring): `JReachU`'s steps; only a native syscall asks `SpecUtZ ∧ UtPgR` of its exit. -/
inductive JReachU2 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → SInvIP σ → MR a σ.machineState → SInvUZ.UtPgR σ →
        JReachU2 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachU2 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → SInvUZ.UtPgR σ' → JReachU2 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachU2 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachU2 s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachU2 s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' →
      JReachU2 s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachU2 s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachU2 s' a' σ'
  | trap {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (v : U64)
      (ev : Fl4Spec.Event) :
      JReachU2 s a σ → σ.curThread ≠ σ.idleThread → v.val < 256 → KEvSpec (.trap v) true ev →
      syscall.handle_trap_syscall st arI s a v = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachU2 s' a' σ'
  | sysU {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (ev : Fl4Spec.Event) :
      JReachU2 s a σ → σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      KEvSpec (.sysU n) true ev → syscall.handle_syscall st arI s a n = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachU2 s' a' σ'


variable {arI AR MR}

/-- `ZR` at every `JReachU2` state. -/
theorem JReachU2.zr {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachU2 (L := L) arI AR MR s a σ) :
    SInvUZ.ZR σ := by
  induction h with
  | start _ _ _ hI _ hP => exact zr_of_utz hI.utZ hP
  | step n c _ _ _ _ _ _ hU hP _ => exact zr_of_utz hU hP
  | irq w _ _ _ hO _ ih => exact zr_evOut ih (fun _ h => by cases h) hO
  | user n c _ _ _ _ hO _ ih => exact zr_evOut ih (fun _ h => by cases h) hO
  | vmf ad c ft _ _ _ _ hO _ ih => exact zr_evOut ih (fun _ h => by cases h) hO
  | trap v ev _ _ _ hK _ hO _ ih => exact zr_evOut ih hK.not_sys hO
  | sysU n ev _ _ _ _ hK _ hO _ ih => exact zr_evOut ih hK.not_sys hO

/-- Every `JReachU2` state is a `JReachU` state (the event exits' `SpecUtZ` from `ZR`). -/
theorem JReachU2.toU {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachU2 (L := L) arI AR MR s a σ) :
    JReachU (L := L) arI AR MR s a σ := by
  induction h with
  | start J hvx hX hI hR _ => exact JReachU.start J hvx hX hI hR
  | step n c _ hct hn hv hy hRJ hU _ ih => exact JReachU.step n c ih hct hn hv hy hRJ hU
  | irq w h0 hI hv hO hRJ ih =>
    exact JReachU.irq w ih hI hv hO hRJ (specUtZ_of_zr (zr_evOut h0.zr (fun _ h => by cases h) hO))
  | user n c h0 hct hU hv hO hRJ ih =>
    exact JReachU.user n c ih hct hU hv hO hRJ (specUtZ_of_zr (zr_evOut h0.zr (fun _ h => by cases h) hO))
  | vmf ad c ft h0 hct hV hv hO hRJ ih =>
    exact JReachU.vmf ad c ft ih hct hV hv hO hRJ (specUtZ_of_zr (zr_evOut h0.zr (fun _ h => by cases h) hO))
  | trap v ev h0 hct hv8 hK hv hO hRJ ih =>
    exact JReachU.trap v ev ih hct hv8 hK hv hO hRJ (specUtZ_of_zr (zr_evOut h0.zr hK.not_sys hO))
  | sysU n ev h0 hct hU hD hK hv hO hRJ ih =>
    exact JReachU.sysU n ev ih hct hU hD hK hv hO hRJ (specUtZ_of_zr (zr_evOut h0.zr hK.not_sys hO))

/-- **The unified invariant at every `JReachU2` state**: `jreach_invU`'s and `UtPgR`. -/
theorem jreach_invU2 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachU2 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧ VxE Z := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hvx⟩ := jreach_invU hnd h.toU
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, (SInvUZ.zr_iff.1 h.zr).2, hvx⟩

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **Refinement at every `JReachU2` state** (module docstring): `kernel_entry_reachU`'s
clauses; every event outcome is a `JReachU2` state with no exit premise; a native
syscall's outcome is one once `SpecUtZ ∧ UtPgR` holds there. -/
theorem kernel_entry_reachU2V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU2 (L := L) arI AR MR s a σ) :
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
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ (SpecUtZ σ' → SInvUZ.UtPgR σ' → JReachU2 (L := L) arI AR MR r.1 r.2 σ') ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU2 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        P1.FastFaultOK (L := L) arI s a n →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU2 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hvx⟩ := jreach_invU hnd hJ.toU
  have hZ := hJ.zr
  have hIO : SpecIoP σ ∧ SInvIo.IoNoOverlap σ := ⟨hI.ioP, hI.ioN⟩
  refine ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, (SInvUZ.zr_iff.1 hZ).2,
    fun n c hct hn hLF hflag hK hDL hFin => ?_,
    fun w a1 hIh hFin => ?_, fun n c hct hU hFin => ?_, fun ad c ft hct hV hFin => ?_,
    fun v hct hv hFin => ?_, fun n hct hU hD hFF hFin => ?_⟩
  · have hE := kernel_entryJ42H (MR := MR) s a σ J hct hR hX hI hLF n c hn hflag hK hDL hFin hARI hA hnd hM hKD
      hIo hIoa hPA hIA hmrt hmb hT hmax htu hRef hPI hSX
    obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hM', hX', h1, h2⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hy, hRJ, hX', hM', h1, h2, fun hU hP => JReachU2.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩ hU hP⟩
  · have hE := jEvRef_irqA J hX hIh hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    obtain ⟨h1, h2⟩ := ioi_evOut hIO hO
    exact ⟨σ', hO, hRJM.1, kcall_sinvX hnd true .interrupt hX (fun h => absurd rfl h) _ hO, hRJM.2, h1, h2,
      specUtZ_of_zr (zr_evOut hZ (fun _ h => by cases h) hO), JReachU2.irq w hJ hIh hv hO hRJM⟩
  · have hE := jEvRef_user n c J hX hct hR (jFltHyp_user hnd hM hKD hA hX hct n c hU) hFin hARI hA hnd hM hKD hmrt
      hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_user_exception st arI s a n c = (KEv.user n c).run st arI s a from rfl, hv, WP.spec_ok]
    obtain ⟨h1, h2⟩ := ioi_evOut hIO hO
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2, h1, h2,
      specUtZ_of_zr (zr_evOut hZ (fun _ h => by cases h) hO), JReachU2.user n c hJ hct hU hv hO hRJM⟩
  · have hE := jEvRef_vmf ad c ft J hX hct hR (jFltHyp_vmf hnd hM hKD hA hX hct ad c ft hV) hFin hARI hA hnd hM hKD
      hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_vm_fault st arI s a ad c = (KEv.vmf ad c).run st arI s a from rfl, hv, WP.spec_ok]
    obtain ⟨h1, h2⟩ := ioi_evOut hIO hO
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2, h1, h2,
      specUtZ_of_zr (zr_evOut hZ (fun _ h => by cases h) hO), JReachU2.vmf ad c ft hJ hct hV hv hO hRJM⟩
  · have hE := jEvRef_trap hnd v hv J hX hct hR hFin hARI hA hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hrun, ev, σ', hK, hO, hRJM⟩ := spec_exists hE
    rw [hrun, WP.spec_ok]
    obtain ⟨h1, h2⟩ := ioi_evOut hIO hO
    exact ⟨ev, σ', hK, hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun _ => sinvX_fip hX) hO, hRJM.2, h1, h2,
      specUtZ_of_zr (zr_evOut hZ hK.not_sys hO), JReachU2.trap v ev hJ hct hv hK hrun hO hRJM⟩
  · have hE := jEvRef_sysU hnd n J hX hct hR hU hD hSX hFF hFin hARI hA hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hrun, ev, σ', hK, hO, hRJM⟩ := spec_exists hE
    rw [hrun, WP.spec_ok]
    obtain ⟨h1, h2⟩ := ioi_evOut hIO hO
    exact ⟨ev, σ', hK, hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun _ => sinvX_fip hX) hO, hRJM.2, h1, h2,
      specUtZ_of_zr (zr_evOut hZ hK.not_sys hO), JReachU2.sysU n ev hJ hct hU hD hK hrun hO hRJM⟩

end

end

end Fl4Proofs.P3.SInvR.G5
