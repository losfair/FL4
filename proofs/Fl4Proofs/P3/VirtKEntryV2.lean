/-
P3x for virtualization (line virt, gen 8, item 1, top): **`kernel_entry_reachV2` = gen 7's `kernel_entry_reachV`
(U36I against the extended spec at `virtKind = none`, `NR` at every exit) without the syscall clause's route-scope
premise** (statement: VirtKEntryV's text with the edits below).

* Syscall clause: the antecedent `VirtAgree.ScopeE6 c σ` [S] is **gone**. It is derived from the clause's own
  `hK` (U36I's dispatch premise) by VirtScope8B's `scopeE8_of_hK` in the narrowed form `VirtScope8.ScopeE8`
  (the syscall's own first-phase flag; gen 8 finding: `ScopeE6`, which also asks the flag the spec never decodes,
  is not derivable from `hK`, VirtScope8's docstring), with the budget premises discharged from `SInvX`,
  `MachPlatF`, `TimeAgree` as in StPostRRReach; the exit is moved by `VirtScope8.kentryV_post8`.
* Trap / unknown-syscall clauses: `∀ ev, KEvSpec … true ev → ∀ c, ev = .syscallEvent c → ScopeE8 c σ` [S]
  (gen 7's with the narrowed `ScopeE8`, weaker by `scopeE8_of6`; these clauses carry no dispatch premise to derive
  it from). `evOutVT_of8`: `VirtKEntryV.evOutVT_of` on `ScopeE8`.

Premise diff against `kernel_entry_reachV`: **removed** `ScopeE6 c σ` [S] (syscall clause); **added**
`hvirt : ∀ a, arI.virtualization a = ok 0` [P] (gen 2's, now at the top: FL4's backend reports no VT-x, the FL4
side of `hvk`); **changed** trap / unknown-syscall scope `ScopeE6` → `ScopeE8` (weaker). Everything else verbatim.
No [J]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtScope8B
import Fl4Proofs.P3.VirtKEntryV
import Fl4Proofs.P3.VirtVcpuExit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtKEntryV2
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtR7e Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtAgree Fl4Proofs.P3.VirtScope8

noncomputable section

/-- **`VirtKEntryV.evOutVT_of` on the narrowed scope.** -/
theorem evOutVT_of8 (hvk : virtKind = .none) (onCore : ObjRef → Bool) {ev : Event} {σ σ' : State Unit}
    (hs : NR σ) (hsc : ∀ c, ev = .syscallEvent c → ScopeE8 c σ) (h : EvOut true ev σ σ') :
    VirtKEntryV.EvOutVT onCore ev σ σ' ∧ NR σ' := by
  obtain ⟨w, hw, hO⟩ := h
  have nw : NR w.2 := VirtExtTop.nr_fl4SyscallFaultIP _ σ hs w hw
  have hr : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt w.2 t → OffRouteS8 c t := fun c e t ht => hsc c e w hw t ht
  refine ⟨⟨w, hw, ?_⟩, nr_fl4CallKernel8 hvk true ev nw hr _ hO⟩
  rw [fl4CallKernelV_eqNR8 hvk onCore true ev nw hr]
  exact hO

/-! ## Gen 8 item 2: `CtTcb` from `SInvX` -/

/-- **l4v `cur_tcb` at every `SInvX` state** (`SInvB`'s `CtExit`: the current thread is a TCB, running or idle). -/
theorem ctTcb_of_sinvX {σ : State Unit} (hX : SInvR.G4.SInvX σ) : VirtVcpuExit.CtTcb σ :=
  let ⟨x, hk, _⟩ := hX.sb.1.2
  ⟨x, hk⟩

/-- **`fl4VcpuExitV_eqNR` with `hct` discharged** from `SInvX` (which `kernel_entry_reachV2` gives at its entry and
at every exit). -/
theorem fl4VcpuExitV_eqNRX (onCore : ObjRef → Bool) (irq : Option Irq) (stalled : Bool) {σ : State Unit}
    (hs : NR σ) (hX : SInvR.G4.SInvX σ) :
    fl4VcpuExitV (Z := Unit) onCore irq stalled σ =
      (NonDet.unless stalled (do updateTimeStamp (Z := Unit); let _ ← checkBudget; pure ()) >>= fun _ =>
        (match irq with
          | some i => handleInterrupt (Z := Unit) i
          | none => pure ()) >>= fun _ =>
        fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ :=
  VirtVcpuExit.fl4VcpuExitV_eqNR onCore irq stalled hs (ctTcb_of_sinvX hX)

theorem nr_fl4VcpuExitVX (onCore : ObjRef → Bool) (irq : Option Irq) (stalled : Bool) {σ : State Unit}
    (hs : NR σ) (hX : SInvR.G4.SInvX σ) : ∀ y ∈ (fl4VcpuExitV (Z := Unit) onCore irq stalled σ).1, NR y.2 :=
  VirtVcpuExit.nr_fl4VcpuExitV onCore irq stalled hs (ctTcb_of_sinvX hX)

end

end Fl4Proofs.P3.VirtKEntryV2

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachV` without the syscall clause's route scope** (module docstring). -/
theorem kernel_entry_reachV2 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
        (∀ ev, KEvSpec (.trap v) true ev → ∀ c, ev = .syscallEvent c → VirtScope8.ScopeE8 c σ) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ VirtKEntryV.EvOutVT onCore ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ c, ev = .syscallEvent c → VirtScope8.ScopeE8 c σ) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ VirtKEntryV.EvOutVT onCore ev σ σ' ∧
          (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧ VirtR7e.NR σ' ⦄)
  := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU36I arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
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
    exact VirtScope8.kentryV_post8 hvk onCore hNR hr (hSys n c hct hn hfl hK hDL hFin)
  · intro w a1 hIh hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hIrq w a1 hIh hE)
  · intro n c hct hU hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hUs n c hct hU hE)
  · intro ad c ft hct hVm' hE
    exact VirtExtTop.evV_post hvk onCore (fun c h => by cases h) hNR (hVm ad c ft hct hVm' hE)
  · intro v hct hv hE hsc
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', hK, hO, hrest⟩
    obtain ⟨e1, e2⟩ := VirtKEntryV2.evOutVT_of8 hvk onCore hNR (hsc ev hK) hO
    exact ⟨ev, σ', hK, e1, hrest, e2⟩
  · intro n hct hU hD hE hsc
    refine WP.spec_mono (hSU n hct hU hD hE) ?_
    rintro r ⟨ev, σ', hK, hO, hrest⟩
    obtain ⟨e1, e2⟩ := VirtKEntryV2.evOutVT_of8 hvk onCore hNR (hsc ev hK) hO
    exact ⟨ev, σ', hK, e1, hrest, e2⟩

end

end

end Fl4Proofs.P3.SInvR.G5
