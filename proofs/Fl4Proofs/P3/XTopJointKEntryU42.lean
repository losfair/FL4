/-
P3 (line p3J, gen 10): **`kernel_entry_reachU42`** = `kernel_entry_reachU41` with the idle half of the
per-entry `ArchSwF` [P] removed (it is a theorem where it is used).

* P3KGen1 / P3KFin / P3KGen: U41's proof transported (P3KXport) with `ArchSwF` ↦ `ArchSwF'` (ArchSwIdle:
  the idle half asks `IdleVt σ`, and is a theorem there, `archSwFI_of`). The pre-g7e finish path
  (`KFinAtR5/31/27/KFinAtR` records, `jat_finishJRNM/JRN/JRP`, `jat_scheduleSR2ZRP/FR2ZR/WP0FZR`) is moved
  onto the g7e scheduler chain (`jat_scheduleWP0FZRI` on the transported `schedule_refinesWP0FRA`, `RootFr`
  from `IdleVt` carried in the records as `FinRootR`); ScNextDomCFR's `schedule_refinesWP0FR` and the
  `cn_*0F` / `scnt_refines0F` chain leave the cone. Every other constant of U41's cone using these ↦ its
  kernel-checked copy `Fl4ProofsK…`.
* `KFinAtR42` = `KFinAtR41` with `arch : ArchSwFT` (the thread half only); `KFinEv42`.
  `KFinAtR42.toK` / `KFinEv42.toK` (into the transported records, with `archSwFI_of` from `ArchTotal`),
  `KFinAtR41.to42` / `KFinEv41.to42` (`ArchSwF → ArchSwFT`, the first half).
* **Premise diff U41 → U42**: the syscall clause's `KFinAtR41 …` ↦ `KFinAtR42 …` and every event's
  `KFinEv41 …` ↦ `KFinEv42 …` (`ArchSwF` ↦ its thread half `ArchSwFT`: the idle half dropped). No new
  premise: the idle half follows from `ArchTotal` (already U41's `hA`), with no determinism premise since
  the spec's CR3 write `setCurrentCr3` is a plain state update. Start (`JReachU40`) and conclusion
  verbatim. [W] 0.
* **`kernel_entry_reachU41_of42`**: U41's statement verbatim, from U42.

Named premises: U41's (XTopJointKEntryU41) with `KFinAtR41.arch : ArchSwF` [P] narrowed to
`KFinAtR42.arch : ArchSwFT` [P] (set_vm_root against archSwitchToThread). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU41
import Fl4Proofs.P3.P3KGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR41` with the thread half of `ArchSwF` only.** -/
structure KFinAtR42 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `ArchSwFT`: FL4's `set_vm_root` refines `archSwitchToThread` (ArchSwIdle). -/
  arch : ArchSwFT st arI Z.N Z.T Z.C Z.c

/-- `KFinEv41` with `KFinAtR42`. -/
def KFinEv42 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR42 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinAtR42.toK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR42 (L := L) arI AR Z H Cs s a σ) (hA : P0.ArchTotal arI) :
    Fl4ProofsK.P3.SInvR.G5.KFinAtR41 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch.toN hA⟩

theorem KFinAtR41.to42 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR41 (L := L) arI AR Z H Cs s a σ) :
    KFinAtR42 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch.1⟩

theorem KFinEv42.toK {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv42 (L := L) arI AR ev Kf σ) (hA : P0.ArchTotal arI) :
    Fl4ProofsK.P3.SInvR.G5.KFinEv41 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).toK hA

theorem KFinEv41.to42 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv41 (L := L) arI AR ev Kf σ) :
    KFinEv42 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).to42

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU42`** (module docstring). -/
theorem kernel_entry_reachU42 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    (hFpu : FpuImplDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU40 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIB.IrqCapBound σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU39 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR42 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv42 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv42 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv42 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv42 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv42 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU40 (L := L) arI AR MR r.1 r.2 σ' ⦄)   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    Fl4ProofsK.P3.SInvR.G5.kernel_entry_reachU41 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    exact hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').toK hA)
  · intro w a1 hIh hE; exact hIrq w a1 hIh (hE.toK hA)
  · intro n c hct hU hE; exact hUs n c hct hU (hE.toK hA)
  · intro ad c ft hct hVm' hE; exact hVm ad c ft hct hVm' (hE.toK hA)
  · intro v hct hv hE; exact hTr v hct hv (fun ev hev w hw => (hE ev hev w hw).toK hA)
  · intro n hct hU hD hE; exact hSU n hct hU hD (fun ev hev w hw => (hE ev hev w hw).toK hA)


end

end

end Fl4Proofs.P3.SInvR.G5
