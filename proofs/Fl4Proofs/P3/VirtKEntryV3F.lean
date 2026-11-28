/-
P3x for virtualization (line virt, gen 13, item 1, top): **`kernel_entry_reachV3F` = `kernel_entry_reachV3` against
the FL4-faithful extended spec `fl4CallKernelVF onCore remoteCur` (`Ext/VirtKernelF`, gen 12).**

Statement: VirtKEntryV3's text with `fl4KernelEntrySyscallV onCore` → `fl4KernelEntrySyscallVF onCore remoteCur`,
`VirtExtTop.EvOutV onCore` → `VirtF13.EvOutVF onCore remoteCur`, `VirtKEntryV.EvOutVT onCore` →
`VirtF13.EvOutVTF onCore remoteCur`, and the parameter `remoteCur` (universally quantified, like `onCore`).
Proof: `kernel_entry_reachV3`, then each exit moved by VirtF13 (`kentryVF_of_V`, `evOutVF_of_V`,
`evOutVTF_of_V`): on an `NR` state in scope both the `V` and the `F` step are the ported step. The syscall clause's
scope `ScopeE8 c σ` is derived from the clause's own dispatch premise `hK` by VirtScope8B's `scopeE8_of_hK`
exactly as in `kernel_entry_reachV2`; the other clauses' events are not syscall events (interrupt, faults;
`KEvSpec.not_sys` for trap / unknown syscall), so their scope is vacuous.

`remoteCur` (FL4 `notification::send_signal` → `vcpu::signal_completes`, `node_get(cpu, CUR_THREAD) == t` for the
bound thread's core) needs **no premise**: it is only consulted for a `runningVM` thread, and every state the
top speaks about is `NR` (no `runningVM` thread), so the statement holds for every `remoteCur`.

Premise diff against `kernel_entry_reachV3`: **none** (same global premises `hvk` [S], `hvirt` [P], U36I's
platform premises, `hNR`; per-clause antecedents verbatim). New parameter `remoteCur`, unconstrained.
No [J]/[P]/[W]/[S] added. New file only.
-/
import Fl4Proofs.P3.VirtKEntryV3
import Fl4Proofs.P3.VirtF13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **The virt top on FL4's step**: `kernel_entry_reachV3` with every exit an outcome of `fl4CallKernelVF onCore
remoteCur` / `fl4KernelEntrySyscallVF onCore remoteCur` (FL4's VMEnter report, #80/#81/#85), for every `onCore`
and `remoteCur`. Same premises as `kernel_entry_reachV3` (module docstring). -/
theorem kernel_entry_reachV3F [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
  := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachV3 arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hvk hvirt
      onCore hJ hNR
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    have hni := hX.entered hct
    have hS := hX.sb
    have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
    have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x) :=
      fun x hk => ⟨nowAgree_F arI hM hR hS.1.1.vmt, curInv_faultIPSt hk hC, offReady_faultIPSt hX.offReady,
        Or.inr hX.ctQ⟩
    have hr := scopeE8_of_hK arI hvk hvirt J hNR hni hB hS.1.1.ns hARI.toARKeep hA hnd (fun a => hT.mrt a)
      (fun a => hT.mb a) hmax htu hn hK
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', VirtF13.kentryVF_of_V hvk onCore remoteCur hNR hr h1, h2⟩
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', VirtF13.evOutVF_of_V hvk onCore remoteCur (fun c h => by cases h) hNR h1, h2⟩
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', VirtF13.evOutVF_of_V hvk onCore remoteCur (fun c h => by cases h) hNR h1, h2⟩
  · intro ad c ft hct hVm' hE
    refine WP.spec_mono (hVm ad c ft hct hVm' hE) ?_
    rintro r ⟨σ', h1, h2⟩
    exact ⟨σ', VirtF13.evOutVF_of_V hvk onCore remoteCur (fun c h => by cases h) hNR h1, h2⟩
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, h2⟩
    exact ⟨ev, σ', hK, VirtF13.evOutVTF_of_V hvk onCore remoteCur (fun c => hK.not_sys c) hNR hO, h2⟩
  · intro n hct hU hD hE
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, h2⟩
    exact ⟨ev, σ', hK, VirtF13.evOutVTF_of_V hvk onCore remoteCur (fun c => hK.not_sys c) hNR hO, h2⟩

end

end

end Fl4Proofs.P3.SInvR.G5
