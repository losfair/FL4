/-
P3x for virtualization (line virt, gen 10, item 1): **`kernel_entry_reachV3` at the p3J root-thread witness, in one
theorem** — every premise of the virt top except `hvk` holds there (under p3J's `OpaqueWK` [P]), and `hvk` is
replaced by exactly what it reduces to at the witness: the platform agreement.

* `V3Out arI AR MR onCore s a σ`: the conclusion of `kernel_entry_reachV3` verbatim (copied from VirtKEntryV3, with
  its parameters abstracted, no other change); **`kernel_entry_reachV3_out`**: `kernel_entry_reachV3` restated with
  that conclusion (same premises, proof `kernel_entry_reachV3 …`).
* **`nr_σ1Q`**: `VirtR7e.NR JBootQ.σ1` (p3J's gen-15 root-thread state, the start of `u40_w1I1`). Same proof as
  VirtWit9's `nr_σ1` over JBootQ's `kh1_some` / `rootTcb_map` / `rootCs_cases` (the base heap `fInitKheap` is
  shared with jboot, so VirtWit9's `fInit_noVirtCaps` / `fInit_noVirtObjects` / `fInit_noRunVM` apply as they are).
* **`hvk_iff_agree_w`**: at the witness arch `warI1` (which reports 0, `noVirt_warI1`), `virtKind = .none` ⇔
  `WitAgree` := `∀ a r, warI1.virtualization a = ok r → r.val = virtKind.code` — the VIRT-PLAN §11.1 platform
  agreement "`Arch::virtualization() = virtKind.code`" [P] at the witness. `virtKind` is the opaque
  `virtPlatform.kind`, so neither side is provable or refutable in the theory; this is the whole content of `hvk`
  there.
* **`kernel_entry_reachV3_w1I1`** (`O : OpaqueWK` [P], `hag : WitAgree` [P], any `onCore`):
  `V3Out warI1 wAR ipiMR onCore JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1`. Every global premise of
  `kernel_entry_reachV3` is discharged: the 17 U36I platform premises and the start `JReachU36I` from `u40_w1I1`
  (its `JReachU40` start's first component), `hvirt` from `noVirt_warI1`, `hNR` from `nr_σ1Q`, `hvk` from `hag`
  by `hvk_iff_agree_w`.
* **`kernel_entry_reachV3_w1I1_nonvac`**: the same together with `JBootQ.σ1_nonIdle` (the syscall / user-exception /
  VM-fault / trap / unknown-syscall clauses, which all ask `σ.curThread ≠ σ.idleThread`, are not vacuous at this
  start), and `kernel_entry_reachV3_w1I1_hvk` (the same with `hvk` itself in place of `hag`).

Named premises: `OpaqueWK` [P] (p3J, JBootU34: one domain, timer constants, `setDeadlineImpl` determinism, a port
value) and `WitAgree` [P] (the platform agreement, the form `hvk` [S] takes at the witness). The per-entry
antecedents of the clauses (U36I's [J]s, e.g. `KDispHypsKVU32`) stay where `kernel_entry_reachV3` has them.
No new [J]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtKEntryV3
import Fl4Proofs.P3.VirtWit9
import Fl4Proofs.P3.JBootQ1U40
import Fl4Proofs.P3.P3JVtxR
open Aeneas Aeneas.Std Result

/-! ## `NR` at p3J's root-thread state `JBootQ.σ1` -/

namespace Fl4Proofs.P3.VirtWit10
open Fl4Spec Fl4Proofs.P3

noncomputable section

theorem σ1Q_noVirtCaps : NoVirtCaps JBootQ.σ1 := by
  intro p ko hk c hc hv
  rcases JBootQ.kh1_some hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, -, h⟩
  · obtain ⟨l, hl⟩ := hc
    rcases JBootQ.rootTcb_map hl with ⟨-, rfl⟩ | rfl
    · exact hv
    · exact hv
  · obtain ⟨l, hl⟩ := hc
    cases hl
  · obtain ⟨l, hl⟩ := hc
    rcases JBootQ.rootCs_cases hl with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hv
    · exact hv
  · exact VirtWit9.fInit_noVirtCaps p ko h c hc hv

theorem σ1Q_noVirtObjects : NoVirtObjects JBootQ.σ1 := by
  intro p ao hk
  rcases JBootQ.kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h⟩
  · cases e
  · cases e
  · cases e
  · exact VirtWit9.fInit_noVirtObjects p ao h

theorem σ1Q_noRunVM : VirtR7d.NoRunVM JBootQ.σ1 := by
  intro p x hk
  rcases JBootQ.kh1_some hk with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h⟩
  · cases e; intro h; cases h
  · cases e
  · cases e
  · exact VirtWit9.fInit_noRunVM p x h

/-- **`NR` at p3J's root-thread state** `JBootQ.σ1` (the start of `u40_w1I1`). -/
theorem nr_σ1Q : VirtR7e.NR JBootQ.σ1 :=
  VirtNvK2.nr_boot σ1Q_noVirtCaps σ1Q_noVirtObjects σ1Q_noRunVM

/-! ## `hvk` at the witness arch: exactly the platform agreement -/

/-- **[P] The platform agreement at the witness arch** (VIRT-PLAN §11.1, "`Arch::virtualization() =
virtKind.code`"): the opaque spec backend constant is the one `warI1` reports. -/
def WitAgree : Prop :=
  ∀ a r, JBoot.warI1.virtualization a = ok r → r.val = virtKind.code

/-- **At the witness, `hvk` is exactly the platform agreement.** -/
theorem hvk_iff_agree_w : virtKind = .none ↔ WitAgree :=
  ⟨fun hvk => VirtWit9.agree_of_hvk JBoot.warI1 hvk noVirt_warI1,
   fun hag => VirtWit9.hvk_of_agree JBoot.warI1 JBootQ.σ1.machineState (noVirt_warI1 _)
     (hag JBootQ.σ1.machineState)⟩

end

end Fl4Proofs.P3.VirtWit10

/-! ## The conclusion of `kernel_entry_reachV3`, named -/

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- The conclusion of `kernel_entry_reachV3`, verbatim, as a predicate of its parameters. -/
def V3Out (onCore : Fl4Spec.ObjRef → Bool) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
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
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧
            (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', VirtExtTop.EvOutV onCore .interrupt σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', VirtExtTop.EvOutV onCore (.userLevelFault n.bv c.bv) σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', VirtExtTop.EvOutV onCore (.vmFaultEvent ft) σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ VirtKEntryV.EvOutVT onCore ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ VirtKEntryV.EvOutVT onCore ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄)

set_option maxHeartbeats 8000000 in
/-- `kernel_entry_reachV3` with its conclusion folded into `V3Out` (same premises). -/
theorem kernel_entry_reachV3_out [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hvk : Fl4Spec.virtKind = .none) (hvirt : ∀ a : A, arI.virtualization a = ok 0#u64)
    (onCore : Fl4Spec.ObjRef → Bool)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) (hNR : VirtR7e.NR σ) :
    V3Out (L := L) arI AR MR onCore s a σ :=
  kernel_entry_reachV3 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hvk hvirt
    onCore hJ hNR

end

end

end Fl4Proofs.P3.SInvR.G5

/-! ## The virt top at the witness -/

namespace Fl4Proofs.P3.VirtWit10
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachV3` at the p3J root-thread witness, with `hvk` itself**: every other global premise is
discharged (`u40_w1I1`, `noVirt_warI1`, `nr_σ1Q`). -/
theorem kernel_entry_reachV3_w1I1_hvk (O : JBoot.OpaqueWK) (hvk : virtKind = .none)
    (onCore : ObjRef → Bool) :
    V3Out (L := wL) JBoot.warI1 wAR ipiMR onCore JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, hJ⟩ := JBootQ.u40_w1I1 O
  exact kernel_entry_reachV3_out JBoot.warI1 wAR ipiMR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    h17 hvk noVirt_warI1 onCore hJ.1 nr_σ1Q

/-- **The virt top at the p3J root-thread witness** (module docstring): `kernel_entry_reachV3`'s conclusion at
`wst` / `warI1` / `wAR` / `ipiMR`, start `JBootQ.w1` / `JBootQ.σ1`, under `OpaqueWK` [P] and the platform
agreement `WitAgree` [P] (`⇔ hvk` there, `hvk_iff_agree_w`). -/
theorem kernel_entry_reachV3_w1I1 (O : JBoot.OpaqueWK) (hag : WitAgree) (onCore : ObjRef → Bool) :
    V3Out (L := wL) JBoot.warI1 wAR ipiMR onCore JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 :=
  kernel_entry_reachV3_w1I1_hvk O (hvk_iff_agree_w.2 hag) onCore

/-- **Non-vacuity**: the same, and the start's current thread is not idle (so every clause guarded by
`σ.curThread ≠ σ.idleThread` applies at the first entry). -/
theorem kernel_entry_reachV3_w1I1_nonvac (O : JBoot.OpaqueWK) (hag : WitAgree) (onCore : ObjRef → Bool) :
    V3Out (L := wL) JBoot.warI1 wAR ipiMR onCore JBootQ.w1 JBootQ.σ1.machineState JBootQ.σ1 ∧
      JBootQ.σ1.curThread ≠ JBootQ.σ1.idleThread :=
  ⟨kernel_entry_reachV3_w1I1 O hag onCore, JBootQ.σ1_nonIdle⟩

end

end Fl4Proofs.P3.VirtWit10
