/-
P3 (issue #16, sd7-2): **`kernel_entry_reachU15`** = g7a-3's `kernel_entry_reachU11`
without C27 `devGpm` and without D7 `idle` (INV-PLAN §1.U3L): s27's U12 and sd7's U13
combined.

* **`JReachU15 s a σ := JReachU3 s a σ ∧ GpmOutV σ ∧ IdleVtS σ`** (`JReachU3`, `JAtZ`,
  `RelTopM`, `JExt` unchanged): both spec-only facts carried with the reachable states,
  each asked at one state, the start state (`JReachU15.start`; both hold at boot,
  `boot_gpmOut`, `boot_idleVtS`).
* The proof runs U12 (at `⟨hJ.1, hJ.2.1⟩`): C27 at the dispatch states from `GpmOutV`
  (`devGpm_of`, inside U12); D7 at the finish states from `IdleVtS` (U13's
  `KFinAtR13.to11` / `KFinEv13.to11` with `front_idleVtS` / `handleE_idleVtS`). Each
  exit ends in `JReachU15`: U12's exit gives `JReachU3 ∧ GpmOutV` (s27's
  `kentry_gpmOut` / `kcall_gpmOut` / `fipEv_gpmOut`), and `IdleVtS σ'` comes from
  `kentry_idleVtS` / `evOut_idleVtS`.

Premises removed (relative to U11): C27 `devGpm` [J] (`KDispHypsKVU12`, as U12) and D7
`idle` [J] (`KFinAtR13` / `KFinEv13`, as U13). Added: none.
-/
import Fl4Proofs.P3.XTopJointKEntryU12
import Fl4Proofs.P3.XTopJointKEntryU13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with both spec facts** (module docstring). -/
abbrev JReachU15 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU3 (L := L) arI AR MR s a σ ∧ SInvGp.GpmOutV σ ∧ SInvIV.IdleVtS σ

variable {arI AR MR}

/-- The base: a start state of `JReachU3` with both spec facts (one state). -/
theorem JReachU15.start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hvx : VxE Z) (hX : SInvX σ)
    (hI : SInvIP σ) (hM : MR a σ.machineState) (hP : SInvUZ.UtPgR σ) (hG : SInvGp.GpmOutV σ)
    (hV : SInvIV.IdleVtS σ) : JReachU15 (L := L) arI AR MR s a σ :=
  ⟨JReachU3.start J hvx hX hI hM hP, hG, hV⟩

variable (arI AR MR)

set_option maxHeartbeats 8000000 in
/-- (f6) `VxE Z` exposed (the same proof). **`kernel_entry_reachU11` without C27 `devGpm` and D7 `idle`** (module docstring). -/
theorem kernel_entry_reachU15V [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU15 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      VxE Z ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU12 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU15 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  have hV := hJ.2.2
  obtain ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU12V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR
      (And.intro hJ.1 hJ.2.1)
  have hG := sinvX_sg hX
  have hO := sinvX_idleOut hX
  have hU := sinvX_ut3 hX
  have hVh : ∀ ev, ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, SInvIV.IdleVtS x.2 :=
    fun ev => SInvIV.handleE_idleVtS true ev hG hO hU hV
  have hVf : ∀ ev, ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run w.2).1, SInvIV.IdleVtS x.2 :=
    fun ev w hw x hx => SInvIV.front_idleVtS σ.curThread true ev hG hO hU hV x ⟨w, hw, hx⟩
  refine ⟨Z, H, Cs, Ac, Lst, D, hvx, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => ?_, fun w a1 hIh hE => ?_, fun n c hct hU' hE => ?_,
    fun ad c ft hct hVm' hE => ?_, fun v hct hv hE => ?_, fun n hct hU' hD hE => ?_⟩
  · refine WP.spec_mono (hSys n c hct hn hfl hK hDL fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
      (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to11 J'
        (SInvIV.front_idleVtS σ.curThread true (.syscallEvent c) hG hO hU hV x hx)) fun r h => ?_
    obtain ⟨σ', hy, hRJ, hX', hM', h1, h2, h3, h4, hk, hg⟩ := h
    exact ⟨σ', hy, hRJ, hX', hM', h1, h2, h3, h4, hk, hg, SInvIV.kentry_idleVtS c hG hO hU hV _ hy⟩
  · refine WP.spec_mono (hIrq w a1 hIh (hE.to11 (hVh _))) fun r h => ?_
    obtain ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg⟩ := h
    exact ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg, evOut_idleVtS hX hV hO'⟩
  · refine WP.spec_mono (hUs n c hct hU' (hE.to11 (hVh _))) fun r h => ?_
    obtain ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg⟩ := h
    exact ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg, evOut_idleVtS hX hV hO'⟩
  · refine WP.spec_mono (hVm ad c ft hct hVm' (hE.to11 (hVh _))) fun r h => ?_
    obtain ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg⟩ := h
    exact ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, hg, evOut_idleVtS hX hV hO'⟩
  · refine WP.spec_mono (hTr v hct hv fun ev hK w hw => (hE ev hK w hw).to11 (hVf ev w hw)) fun r h => ?_
    obtain ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, hg⟩ := h
    exact ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, hg, evOut_idleVtS hX hV hO'⟩
  · refine WP.spec_mono (hSU n hct hU' hD fun ev hK w hw => (hE ev hK w hw).to11 (hVf ev w hw)) fun r h => ?_
    obtain ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, hg⟩ := h
    exact ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, hg, evOut_idleVtS hX hV hO'⟩

end

end

end Fl4Proofs.P3.SInvR.G5
