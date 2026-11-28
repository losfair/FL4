/-
P3 (issue #16, g7e): **`kernel_entry_reachU8`** = `kernel_entry_reachU10`
(the strongest top: U9's guarded `vsReach`, U7's dispatch bundle
`KDispHypsKVU7`, A16 narrowed) with the finish bundles of U5 and the D6
`tail` removed:

* syscall finish: `KFinAtR8` (G7eTail) = `KFinAtR31` without `sni`, `send`
  (theorems, ScSniProof, as U5) and `tail` (now a theorem, `kfin_tail_of`),
  with **`idle : IdleVt σ` [J]** (INV-PLAN §1.U3L D7) at the finish state;
* event finishes: `KFinEv8` (`KFinAtR8` at every handled-event state).

The conversion to U10's bundles needs `FpuOwnOK` at the finish states: from
`SInvB` at the entry (`SInvX.sb`): `sinvB_front_fo` for syscalls,
G7eFo's `kcall_fo_ev` / `kcall_fo_fip` for the events. As U5, the top takes
`hDR : SetDlDetR MR` [P] (the timer's opaque deadline write determinate at an
`MR` state), which `sni` needs.

Premises removed (relative to U10): D4 `sni`, D5 `send`, D6 `tail`
(the narrowed [W] CR3 relation after `schedule`). Added: D7 `IdleVt` [J] per
finish state; `hDR` [P] (U5's).
-/
import Fl4Proofs.P3.XTopJointKEntryU10
import Fl4Proofs.P3.G7eTail
import Fl4Proofs.P3.G7eFo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU10` with the finish bundles `KFinAtR8` / `KFinEv8`: no D6 `tail`, D4/D5 gone
(`KFinAtR5`), `IdleVt` [J] asked instead** (module docstring). -/
theorem kernel_entry_reachU8V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU3 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU7 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR8 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv8 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv8 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv8 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv8 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv8 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU10V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hJ
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  have hARK := hARI.toARKeep
  have hS := hX.sb
  have toE : ∀ {ev : Fl4Spec.Event} {Kf : S → A → Prop}, (∀ c, ev ≠ .syscallEvent c) →
      (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) → KFinEv8 (L := L) arI AR ev Kf σ →
      KFinEv (L := L) arI AR ev Kf σ := fun hev hev' F =>
    (F.to hnd hA hARK hRef hD hT (fun x hx o e => SInvF.fpuOwnOK_of_ft
      (SInvF.kcall_fo_ev true _ hev (SInvAll.SInvB.entryJEv hS hev').ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut
        hS.1.1.live hS.1.1.ft x hx) o e)).to hA hD
  have toF : ∀ {ev : Fl4Spec.Event} {Kf : S → A → Prop}, (∀ c, ev ≠ .syscallEvent c) → ev ≠ .interrupt →
      σ.curThread ≠ σ.idleThread → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      KFinEv8 (L := L) arI AR ev Kf w.2 → KFinEv (L := L) arI AR ev Kf w.2 := fun hev hint hct w hw F =>
    (F.to hnd hA hARK hRef hD hT (fun x hx o e => SInvF.fpuOwnOK_of_ft
      (SInvF.kcall_fo_fip true _ hev hint (SInvAll.SInvB.entryJ hS hct).ctAct ⟨hS.1.1.nq, hS.1.1.epq⟩ hS.1.1.ut
        hS.1.1.live hS.1.1.ft w hw x hx) o e)).to hA hD
  exact ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => ((hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to5 hnd hA hARK
        hRef hD hT J' (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e)).to31 hA hD),
    fun w a1 hw hF => hIrq w a1 hw (toE (fun c e => by cases e) (fun h => absurd rfl h) hF),
    fun n c hct hu hF => hUs n c hct hu (toE (fun c e => by cases e) (fun _ => hct) hF),
    fun ad c ft hct hv hF => hVm ad c ft hct hv (toE (fun c e => by cases e) (fun _ => hct) hF),
    fun v hct hv hF => hTr v hct hv (fun ev he w hw => toF he.not_sys (by cases he <;> intro e <;> cases e) hct w hw
      (hF ev he w hw)),
    fun n hct hu hnd' hF => hSU n hct hu hnd' (fun ev he w hw => toF he.not_sys (by cases he <;> intro e <;> cases e)
      hct w hw (hF ev he w hw))⟩

end

end

end Fl4Proofs.P3.SInvR.G5
