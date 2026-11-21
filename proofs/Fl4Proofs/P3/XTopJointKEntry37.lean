/-
P3 (DESIGN.md §9), invariant line G4 (g4b, KENTRY-PLAN g4b): **`JDispMR` [W]
narrowed to the invoking syscalls.** The receiving syscalls (`SysRecv`,
`SysNBRecv`, `SysWait`, `SysNBWait`) and `SysYield` touch no machine field
`MR` reads on either side, so their `MR` completion holds with the same
outcome:

* FL4: `dispatch_recv_mr` / `dispatch_yield_mr`: `dispatch_syscall` reads two
  registers and runs `handle_recv` / `handle_yield`, whose arch operations
  keep `MR` at a fixed machine state (`MKD.syscall_handle_recv` /
  `MKD.syscall_handle_yield`, MachKeepF).
* spec: their branches are `withoutPreemption` of `handleRecv` / `handleYield`
  (`MachT.mtk_handleRecvG` / `mtk_handleYieldG`, MachFieldFamS): every outcome
  is ok and keeps the four machine fields.
* `JDispMR.of_keep`: those two facts give `JDispMR` (the related outcome
  itself has `MR`, by `MachPlat.frame`).

`JDispMRI` [W] = `JDispMR` asked only for `InvSys` / `MidSys` numbers
(Send / NBSend / Call and ReplyRecv / NBSendRecv / NBSendWait); `jDispMR_of`
gives `JDispMR` for every native syscall. NEW TOP `kernel_entryJ37` (=
`kernel_entryJ36` with `hDM : JDispMRI`) and `kernel_entry_reachMI`.
-/
import Fl4Proofs.P3.XTopJointKEntry36
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`JDispMR` from an `MR`-keeping FL4 run and a spec branch that keeps the
machine fields and never fails** (module docstring). -/
theorem JDispMR.of_keep (hM : MachPlat arI MR) {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64}
    {c : Fl4Spec.Syscall}
    (hW : MR a σ.machineState → syscall.dispatch_syscall st arI s a n ⦃ r => MR r.2 σ.machineState ⦄)
    (hF : ∀ y ∈ ((Fl4Spec.fl4HandleSyscall (Z := Unit) true c).run σ).1,
      MachF.msF y.2 = MachF.msF σ ∧ y.1 = .ok ()) :
    JDispMR (L := L) arI AR MR s a σ n c := by
  intro hR
  refine WP.spec_mono (hW hR) ?_
  rintro r hMr ⟨y, hy, ⟨h1, h2, h3⟩ | ⟨h1, -⟩⟩
  · exact ⟨y, hy, Or.inl ⟨h1, h2, h3, msF_mr hM hMr (hF y hy).1⟩⟩
  · rw [(hF y hy).2] at h1; cases h1

/-- **FL4's receiving dispatch keeps `MR`** (module docstring). -/
theorem dispatch_recv_mr (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {s : S} {a : A} {n : I64}
    {bl cr : Bool} (hn : RecvSys n bl cr) {c0 : Fl4Spec.MachineState} (h : MR a c0) :
    syscall.dispatch_syscall st arI s a n ⦃ r => MR r.2 c0 ⦄ := by
  have hct := cur_thread_eq (L := L) s
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.CAP) ?_
  rintro c0' -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.REPLY) ?_
  rintro c1 -
  rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBRecv ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBRecv fl4_abi.syscall.SysRecv; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h
  · rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBSend; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysCall; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysNBRecv; decide)]
    rw [if_neg (show fl4_abi.syscall.SysNBWait ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysNBWait fl4_abi.syscall.SysWait; decide)]
    rw [if_pos rfl]
    exact MKD.syscall_handle_recv L.total hA hKD h

/-- **FL4's yield dispatch keeps `MR`** (module docstring). -/
theorem dispatch_yield_mr (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {s : S} {a : A}
    {c0 : Fl4Spec.MachineState} (h : MR a c0) :
    syscall.dispatch_syscall st arI s a fl4_abi.syscall.SysYield ⦃ r => MR r.2 c0 ⦄ := by
  have hct := cur_thread_eq (L := L) s
  unfold syscall.dispatch_syscall
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.CAP) ?_
  rintro c0' -
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s _ layout.reg.REPLY) ?_
  rintro c1 -
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSend by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSend; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysCall by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysCall; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBWait; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysReplyRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysReplyRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendRecv by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendRecv; decide)]
  rw [if_neg (show fl4_abi.syscall.SysYield ≠ fl4_abi.syscall.SysNBSendWait by unfold fl4_abi.syscall.SysYield fl4_abi.syscall.SysNBSendWait; decide)]
  rw [if_pos trivial]
  exact MKD.syscall_handle_yield L.total hA hKD h

variable (arI) in
/-- **[W] `JDispMR` for the invoking syscalls only** (module docstring). -/
def JDispMRI (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  (∀ call bl don, InvSys n call bl don → JDispMR (L := L) arI AR MR s a σ n c) ∧
  (MidSys n c → JDispMR (L := L) arI AR MR s a σ n c)

/-- **`JDispMR` for every native syscall from `JDispMRI`** (module docstring). -/
theorem jDispMR_of (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hA : P0.ArchTotal arI) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hn : NativeSys n c)
    (h : JDispMRI (L := L) arI AR MR s a σ n c) : JDispMR (L := L) arI AR MR s a σ n c := by
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · exact h.1 call bl don hi
  · refine JDispMR.of_keep hM (fun hR => dispatch_recv_mr hKD hA hr hR) ?_
    rw [fl4HandleSyscall_recv true bl cr]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption (MachT.mtk_handleRecvG bl cr) y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · refine JDispMR.of_keep hM (fun hR => dispatch_yield_mr hKD hA hR) ?_
    have e : Fl4Spec.fl4HandleSyscall (Z := Unit) true .sysYield = Fl4Spec.withoutPreemption Fl4Spec.handleYield := rfl
    rw [e]
    intro y hy
    obtain ⟨h1, h2⟩ := MachT.mtk_withoutPreemption MachT.mtk_handleYieldG y hy
    exact ⟨congrArg Prod.fst h1, h2⟩
  · exact h.2 hm

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ36` with `hDM`
asked only for the invoking syscalls (`JDispMRI`). -/
theorem kernel_entryJ37 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDM : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        JDispMRI (L := L) arI AR MR s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ :=
  kernel_entryJ36 s a σ J hct hR hX n c hn hflag hK
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' => jDispMR_of hM hKD hA hn (hDM σb hBA V' Ac' Lst' D' s' a' hF J'))
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hFast

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entry_reachM` with `hDM` asked only for the invoking syscalls**
(`JDispMRI`, via `kernel_entryJ37`'s `jDispMR_of`). -/
theorem kernel_entry_reachMI [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachM (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          JDispMRI (L := L) arI AR MR s' a' σb n c) →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachM (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, hAll⟩ := kernel_entry_reachM hARI hA hnd hM hKD hPA hIA hmrt hmb hT
    hmax htu hRef hPI hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast =>
    hAll n c hct hn hflag hK (fun σb hBA V' Ac' Lst' D' s' a' hF J' =>
      jDispMR_of hM hKD hA hn (hDM σb hBA V' Ac' Lst' D' s' a' hF J')) hFin hFast⟩

end

end

end Fl4Proofs.P3
