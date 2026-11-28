/-
P3 (p1g): **P1's kernel-entry conclusion from U29**, non-vacuously.

The P1 kernel-entry tops (`kernel_entry.entry_of` .. `entry_of10`) ask premise
bundles (`EntryHyps0`, `P3Place`, `InvHyps`, `Hyps4`) that are contradictory
(P1/EntryVacuous), so they say nothing about the kernel. Their conclusion, that
the exit state satisfies `EntryInv` over some sets, holds at every state P3's
joint refinement reaches:

* `JAtZ.entryInv`: a `JAtZ` state whose spec state has the action resume
  (`SInvX`'s `RS`, at every kernel entry and exit) satisfies P1's `EntryInv` over the sets
  drawn from `H`.
* `JAt.entInvAt` / `EntInvAt`: the same with the sets existential.
* `JAtZ.canBlockX` / `JAtZ.timeoutTyped`: the facts `blkU` / `tmoOK` / `tmoAny` were to claim, in
  their true form: `CanBlock` of the current thread where it is not the idle
  thread, at an entry state; the handler caps of every TCB typed.
* **`kernel_entry_entryInvU29`**: `kernel_entry_reachU29`'s premises, post
  `EntInvAt` at the exit of each of its six entry kinds (native syscalls,
  interrupts, user exceptions, VM faults, trapped and unknown syscalls; `σ.curThread ≠ σ.idleThread`
  asked at all but the interrupt, as U29). Wider than the P1 tops (fault
  entries), with two differences: the exit's cores `Cs` are existential with the
  other sets (`JAtZ`'s), and the entry is at a `JReachU17` state, not at any
  `EntryInv` state.

No premise beyond U29's. (Collapse A, Q: U29's syscall clause takes `JDecMRLKQ` = `JDecMRLK ∧ IrqAckU` and its
platform records are the narrowed `MachPlat` / `IrqPlatA`; this statement follows.)
-/
import Fl4Proofs.P3.XTopJointKEntryU29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **P1's `EntryInv` at a joint state with the action resume** (module docstring). -/
theorem JAtZ.entryInv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction = .resumeCurThread) :
    P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s := by
  have hC : CurInv σ := J.curInv (by rw [hres]; intro e; cases e)
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨hscC, hsc0, htw, hts, hact, hnr, hnb⟩ := CurInv.facts hS J.inv hC
  have hct : nodeW st s Z.c layout.node.CUR_THREAD ∈ Z.T := hc.curT
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have ecur : L.curW s = nodeW st s Z.c layout.node.CUR_THREAD := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  have ecsc : L.cscW s = nodeW st s Z.c layout.node.CUR_SC := by
    show L.mem s (L.nodeAt s (L.cpu s) _) = _; rw [hc.cur]; rfl
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  have hxa : Fl4Spec.scActive x = true := by
    by_cases hi : (nodeW st s Z.c layout.node.CUR_SC).bv = σ.idleSc
    · exact hx.active_of_rmax (hx.idle hi)
    · exact hact hi x n hk
  have hscS : nodeW st s Z.c layout.node.CUR_SC ∈ P1.Heap.scs H := ⟨_, (hJ.sc _ x n hsc0 hk).2⟩
  have hcA : L.cscW s ∈ Ac := by
    rw [ecsc]; exact (J.blk.2.2.2.1.act _ hscS).2 (fun e => hx.rmax_ne hxa (by rw [e]; rfl))
  refine ⟨J.blk.1, J.blk.2.1, J.blk.2.2.1, J.blk.2.2.2.1, J.blk.2.2.1.2.2.tm, hcA, ?_, fun _ => ?_⟩
  · rw [ecur]; exact actionW_ne_of hS hct (by rw [hres]; intro e; cases e)
  · rw [ecur, ecsc, hts]

/-- `EntryInv` over some sets. -/
def EntInvAt (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : Prop :=
  ∃ (H : P1.Heap) (Cs Ac : Set U64),
    P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s

theorem JAt.entInvAt (h : JAt (L := L) arI AR s a σ) (hX : SInvX σ) : EntInvAt st s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -⟩ := h
  exact ⟨H, Cs, Ac, J.entryInv hX.cr.2⟩

/-- **`CanBlock` of the current thread at an entry state, not the idle thread**:
the true form of `EntryHyps0.blkU` / `tmoOK`. -/
theorem JAtZ.canBlockX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hX : SInvX σ)
    (hct : σ.curThread ≠ σ.idleThread) : P1.CanBlock st (P1.Heap.tcbs H) Ac s (L.curW s) := by
  have hE := hX.entered hct
  obtain ⟨hcu, x, hk, hr⟩ := J.curRunnable hE (cur_thread_curW (L := L) s)
  have hcT : L.curW s ∈ Z.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
  exact J.canBlockCur hcT (J.curEq (cur_thread_curW (L := L) s)).1 hk hr hE hX.ctQ

/-- **The handler caps of every TCB typed** at a joint state: the true form of
`EntryHyps0.tmoOK`'s cap part and `P3Place.tmoAny`. -/
theorem JAtZ.timeoutTyped (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : U64} (hsl : IsSlot Z.th sl) :
    obj.Slot.cap st sl s ⦃ c => P1.CapTyped H (P1.Heap.replies H) (P1.Heap.ntfns H) c ⦄ := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact hJ.slotCapTyped (Or.inl hsl)

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **Every kernel entry from a reachable joint state ends in P1's `EntryInv`**
(module docstring): `kernel_entry_reachU29`'s premises. -/
theorem kernel_entry_entryInvU29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      P1.EntryInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r => EntInvAt st r.1 ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => EntInvAt st r.1 ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => EntInvAt st r.1 ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => EntInvAt st r.1 ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => EntInvAt st r.1 ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => EntInvAt st r.1 ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, J.entryInv hX.cr.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    refine WP.spec_mono (hSys n c hct hn hfl hK hDL hFin) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'
  · intro w a1 hIh hE
    refine WP.spec_mono (hIrq w a1 hIh hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'
  · intro n c hct hU hE
    refine WP.spec_mono (hUs n c hct hU hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'
  · intro ad c ft hct hV hE
    refine WP.spec_mono (hVm ad c ft hct hV hE) ?_
    rintro r ⟨σ', -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'
  · intro v hct hv hE
    refine WP.spec_mono (hTr v hct hv hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'
  · intro n hct hU hND hE
    refine WP.spec_mono (hSU n hct hU hND hE) ?_
    rintro r ⟨ev, σ', -, -, hRJ, hX', -⟩
    exact JAt.entInvAt hRJ.2 hX'

end

end

end Fl4Proofs.P3.SInvR.G5
