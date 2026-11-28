/-
P3x for virtualization (line virt, gen 13, item 1, witness): **`kernel_entry_reachV3F` (the virt top on FL4's step
`fl4CallKernelVF onCore remoteCur`) at the p3J root-thread witness** — VirtWit10's theorem on the F top.

* `V3OutF arI AR MR onCore remoteCur s a σ`: the conclusion of `kernel_entry_reachV3F` verbatim (VirtWit10's
  `V3Out` with the F exits); `kernel_entry_reachV3F_out`.
* **`kernel_entry_reachV3F_w1I1_hvk`**, **`kernel_entry_reachV3F_w1I1`** (`O : OpaqueWK` [P], `hag : WitAgree` [P],
  any `onCore`, any `remoteCur`), **`kernel_entry_reachV3F_w1I1_nonvac`** (∧ `JBootQ.σ1_nonIdle`): every global
  premise discharged exactly as in VirtWit10 (`u40_w1I1`, `noVirt_warI1`, `nr_σ1Q`, `hvk_iff_agree_w`).

`remoteCur` is not constrained anywhere (VirtKEntryV3F's docstring: FL4's `signal_completes` is consulted only for a
`runningVM` thread, and the top's states are `NR`); at the witness it is satisfiable trivially — any function,
e.g. FL4's own per-core current-thread table, is allowed. Named premises: `OpaqueWK` [P], `WitAgree` [P] (as
VirtWit10). No new [J]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtKEntryV3F
import Fl4Proofs.P3.VirtWit10
open Aeneas Aeneas.Std Result

/-! ## The conclusion of `kernel_entry_reachV3F`, named -/

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- The conclusion of `kernel_entry_reachV3F` (VirtKEntryV3F), verbatim, as a predicate of its parameters. -/
def V3OutF (onCore remoteCur : Fl4Spec.ObjRef → Bool) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU32 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur true c σ).1 ∧
            (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', VirtF13.EvOutVF onCore remoteCur .interrupt σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', VirtF13.EvOutVF onCore remoteCur (.userLevelFault n.bv c.bv) σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', VirtF13.EvOutVF onCore remoteCur (.vmFaultEvent ft) σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ VirtF13.EvOutVTF onCore remoteCur ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ VirtF13.EvOutVTF onCore remoteCur ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄)

set_option maxHeartbeats 8000000 in
/-- `kernel_entry_reachV3F` with its conclusion folded into `V3OutF` (same premises). -/
theorem kernel_entry_reachV3F_out [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hvk : Fl4Spec.virtKind = .none) (hvirt : ∀ a : A, arI.virtualization a = ok 0#u64)
    (onCore remoteCur : Fl4Spec.ObjRef → Bool)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) (hNR : VirtR7e.NR σ) :
    V3OutF (L := L) arI AR MR onCore remoteCur s a σ :=
  kernel_entry_reachV3F arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hvk hvirt
    onCore remoteCur hJ hNR

end

end

end Fl4Proofs.P3.SInvR.G5

/-! ## The F top at the witness -/

namespace Fl4Proofs.P3.VirtWit13
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P2.Wit Fl4Proofs.P3.VirtWit10

noncomputable section

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachV3F` at the p3J root-thread witness, with `hvk` itself.** -/
theorem kernel_entry_reachV3F_w1I1_hvk (O : JBoot.OpaqueWK) (hvk : virtKind = .none)
    (onCore remoteCur : ObjRef → Bool) :
    V3OutF (L := wL) JBoot.warI1 wAR ipiMR onCore remoteCur JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, hJ⟩ := JBootQ.u40_w1I1 O
  exact kernel_entry_reachV3F_out JBoot.warI1 wAR ipiMR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    h17 hvk noVirt_warI1 onCore remoteCur hJ.1 nr_σ1Q

/-- **The virt top on FL4's step at the p3J root-thread witness** (module docstring), under `OpaqueWK` [P] and
`WitAgree` [P], for every `onCore` and `remoteCur`. -/
theorem kernel_entry_reachV3F_w1I1 (O : JBoot.OpaqueWK) (hag : WitAgree) (onCore remoteCur : ObjRef → Bool) :
    V3OutF (L := wL) JBoot.warI1 wAR ipiMR onCore remoteCur JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 :=
  kernel_entry_reachV3F_w1I1_hvk O (hvk_iff_agree_w.2 hag) onCore remoteCur

/-- **Non-vacuity**: the same, and the start's current thread is not idle. -/
theorem kernel_entry_reachV3F_w1I1_nonvac (O : JBoot.OpaqueWK) (hag : WitAgree) (onCore remoteCur : ObjRef → Bool) :
    V3OutF (L := wL) JBoot.warI1 wAR ipiMR onCore remoteCur JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 ∧
      JBootQ.σ1.curThread ≠ JBootQ.σ1.idleThread :=
  ⟨kernel_entry_reachV3F_w1I1 O hag onCore remoteCur, JBootQ.σ1_nonIdle⟩

end

end Fl4Proofs.P3.VirtWit13
