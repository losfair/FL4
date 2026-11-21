/-
P3 (DESIGN.md §9), invariant line G4 (g4b, KENTRY-PLAN g4b; g4a's handoff
(G-b)): **`MR` at the exit of the syscall entry**, and the induction
`JReachM` / `jreach_invM` / `kernel_entry_reachM` whose step relation is the
one the refinement now delivers (`RJ ∧ MR`).

* `jat_finishJRNM`: FL4's `finish` from `JAtZR` with `MR a σ.ms` ends related
  (`RJ`) to an outcome of the spec's `fl4Awaken; schedule; activateThread` and
  `MR` holds there: `jat_finishJRN` with the FL4 walk `MKD.syscall_finish`
  (MachKeepF: every arch operation reached keeps `MR` at a fixed machine
  state, `MRKeepD`) and the spec frame `MachT.mtk_finish` (MachFieldFamS: the
  four machine fields `MR` reads are kept), by `MachPlat.frame`.
* `PPQJIM` / `DispPostRM`: `PPQJI` / `DispPostR` with `MR` at the chosen
  outcome. `JDispMR` [W] (the one carry left open, narrowed from g4a's "MR at
  the exit"): at a dispatch state with `MR`, every run of `dispatch_syscall`
  that `DispPostR` relates to some spec outcome is related (`DispPostRM`) to
  an outcome where `MR` holds. Pointwise and existential on purpose: the spec
  at `State Unit` is nondeterministic in the oracle positions (`orChoiceE`
  of `preemptionPoint` is a free choice there, `StateExt.wrapExtBool`), so
  "every related outcome has `MR`" is false (two outcomes differing only in
  `timeState` / `irqState`); only the outcome the FL4 run matches has it.
  l4v: the machine state is shared, every `do_machine_op` of the abstract
  run is matched by the concrete one (`corres` of `preemption_point`,
  `maskInterrupt`, ...).
* `kernel_entryJ13PUGM` = `kernel_entryJ13PUG` (same body) with `MR` carried
  to every exit: the stopping budget check (`budget_mr_at` at `false`), the
  dispatch's ok outcomes and its preempted outcomes (`JDispMR`), then
  `finish` (`jat_finishJRNM`, `kPreFinAtGM`). Post `KPostM` = `KPost` with
  `MR r.2 σ'.ms`.
* **`kernel_entryJ36`** = `kernel_entryJ35` with post `KPostXM` (`KPostX` and
  `MR`), one more per-state premise `hDM` (`JDispMR`, asked at the same
  dispatch states as `hK`), `hFast` asked for `KPostM`.
* `JReachM`: `start` as `JReach`; `step` along `RJM := RJ ∧ MR`, the exit
  relation `kernel_entryJ36` delivers. `jreach_invM`, and
  **`kernel_entry_reachM`**: every related exit is again reachable (no `MR →`
  left: g4a's gap (G-b) is closed up to `JDispMR`).
-/
import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.MachKeepF
import Fl4Proofs.P3.MachFieldFamS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The finish with `MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`jat_finishJRN` with `MR` after** (module docstring). -/
theorem jat_finishJRNM {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hN : NativeScope σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ)
    (hnd : Fl4Spec.numDomains = 1) (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hAN : ArchNdF st Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : MR a σ.machineState) :
    syscall.finish st arI s a ⦃ r => ∃ σ',
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ MR r.2 σ'.machineState ⦄ := by
  refine WP.spec_mono (WP.spec_and (jat_finishJRN s a σ J hN hd hnd hAT hVt hmb hA hAN hFO hsni hsend hT hTail hmax
    htu) (MKD.syscall_finish L.total hAT hKD hR)) ?_
  rintro r ⟨⟨_, σ', _, _, hmem, hRJ, _⟩, hMR⟩
  exact ⟨σ', hmem, hRJ, msF_mr hM hMR (congrArg Prod.fst (MachT.mtk_finish hmem))⟩

end

/-! ## The dispatch posts with `MR` and the open carry -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`PPQJI` with `MR` at the path's outcome.** -/
def PPQJIM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (σ1 : Fl4Spec.State Unit)
    (r : S × A) : Prop :=
  ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, JAt (L := L) arI AR r.1 r.2 z.2 ∧ MR r.2 z.2.machineState

/-- **`DispPostR` (at `PPQJI`) with `MR` at the chosen outcome.** -/
def DispPostRM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
    (m : Fl4Spec.PMonad Unit Unit) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ y ∈ (m.run σ).1,
    (y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧ (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64)
      (Lst : U64 → List U64) (D : Set U64), JAtZR (L := L) arI AR Z H Cs Ac Lst D r.1 r.2 y.2) ∧
      MR r.2 y.2.machineState) ∨
    (y.1 = .error () ∧ PPQJIM (L := L) arI AR MR y.2 r)

/-- **[W] The dispatch's `MR` completion** (module docstring): at a dispatch
state with `MR`, a run of `dispatch_syscall` related by `DispPostR` is
related by `DispPostRM`. -/
def JDispMR (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop :=
  MR a σ.machineState → syscall.dispatch_syscall st arI s a n ⦃ r =>
    DispPostR (L := L) arI AR (PPQJI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r →
    DispPostRM (L := L) arI AR MR (Fl4Spec.fl4HandleSyscall true c) σ r ⦄

/-- **`KPost` with `MR` at the chosen outcome.** -/
def KPostM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState

/-- **`KPostX` with `MR`**: the post of `kernel_entryJ36`. -/
def KPostXM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState ∧ SInvX σ'

variable {arI}

theorem KPostM.toK {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostM (L := L) arI AR MR c σ r) : KPost (L := L) arI AR c σ r :=
  h.imp id fun ⟨σ', h1, h2, _⟩ => ⟨σ', h1, h2⟩

end

/-! ## `kernel_entryJ13PUG` with `MR` at every exit -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`kPreFinAtG` from `PPQJIM`, with `MR` after.** -/
theorem kPreFinAtGM {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' r.1 r.2 x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' r.1 r.2 x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS0 : NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hM : MachPlat arI MR) (hKD : MRKeepD arI MR)
    (σ1 : Fl4Spec.State Unit) (hPA : PreemptedAt c σ σ1) (hQ : PPQJIM (L := L) arI AR MR σ1 r) :
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ∧ MR r'.2 σ'.machineState ⦄ := by
  obtain ⟨z, hz, ⟨Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩, hMz⟩ := hQ
  obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
  have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
    mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
  have F := hFin _ hx Zm Hm Csm Acm Lstm Dm Jm.toR
  exact WP.spec_mono (jat_finishJRNM r.1 r.2 z.2 Jm.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMz)
      fun r' ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨z, hz, σ', hmem, hRJ, hM'⟩

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUG` with `MR` at every exit** (module docstring); same
body, `hDM` at the dispatch states. -/
theorem kernel_entryJ13PUGM [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDM : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        JDispMR (L := L) arI AR MR s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
  have hMK := hKD.toK
  have hct := cur_thread_eq (L := L) s
  generalize L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) = ct at hct
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hctT
  have hxs := hI.1.toE.at_tcb hctT hk
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  -- the FaultIP write
  unfold syscall.handle_syscall_old
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s ct layout.reg.NEXT_IP) ?_
  rintro nx hnx
  simp only [lift, bind_ok]
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.FAULT_IP _) ?_
  rintro s1 rfl
  generalize hv : core.num.U64.wrapping_sub nx 2#u64 = v
  have hvb : v.bv = x.tcbArch.tcbContext.userRegs .nextIP - 2 := by
    rw [← hv, core.num.U64.wrapping_sub_bv_eq, hnx, ← hxs.regs .nextIP, regIdx_nextIP]; rfl
  have hX2 := reg_wr_irel J.ip hI hctT hk Fl4Spec.Register.faultIP (by decide) v
  rw [regIdx_faultIP] at hX2
  obtain ⟨V0, J0⟩ := J.regWrJ hctT hk Fl4Spec.Register.faultIP v (by rw [regIdx_faultIP]; exact hX2)
  rw [regIdx_faultIP, hvb] at J0
  rw [← hcur] at J0
  have hF : ((), faultIPSt σ σ.curThread x) ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1 := by
    rw [fl4SyscallFaultIP_eq hk']; exact Set.mem_singleton _
  have hni0 : Entered (faultIPSt σ σ.curThread x) := hni
  have hBu := hB x hk'
  -- the trap flag and the number range
  refine WP.spec_bind (hflag ct v hct) ?_
  rintro f hf
  simp only [hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg hn.range.1, if_neg hn.range.2]
  -- budget_ok
  have hAK := hARI.toARKeep
  have hBud : syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart)
          (faultIPSt σ σ.curThread x) = ({(true, σ')}, False) ∧
        σ'.kheap = (faultIPSt σ σ.curThread x).kheap ∧ σ'.curThread = (faultIPSt σ σ.curThread x).curThread ∧
        σ'.curSc = (faultIPSt σ σ.curThread x).curSc ∧
        σ'.schedulerAction = (faultIPSt σ σ.curThread x).schedulerAction ∧
        σ'.idleThread = (faultIPSt σ σ.curThread x).idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V0) H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget (faultIPSt σ σ.curThread x)).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
    exact JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA
      hnd hmrt hmb hmax htu
  refine WP.spec_bind (WP.spec_and (spec_and_eq hBud fun _ h => h) (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨hTr, hFa⟩, hbeq⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J'⟩ := hFa rfl
    obtain ⟨b', σb⟩ := z
    simp only at hz1; subst hz1
    show (do
      let (s3, a2) ← (if false = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNM s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hNSb : NativeScope σb := SInvN.ns_of_kheap ekh (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF)
    have hfr : KFrontB (L := L) arI s a s2 a1 := ⟨ct, v, hct, hbeq⟩
    refine WP.spec_bind (spec_and_eq (WP.spec_and (dispatch_all13PUN s2 a1 σb J' hnib n c hn
      (hK σb hBA V0 _ _ _ s2 a1 hfr J') hMRσb hVIσb hNSb hARI hA hnd hM hMK hPA hIA hmrt hmax htu)
      (hDM σb hBA V0 _ _ _ s2 a1 hfr J' hMRσb))
      fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨hDP, hDMp⟩, hdeq⟩
    obtain ⟨y, hy, ⟨hy1, hR, hJ, hMy⟩ | ⟨hy1, hQ⟩⟩ := hDMp hDP
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
      exact WP.spec_mono (jat_finishJRNM s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMy)
        fun r ⟨σ', hmem, hRJ, hM'⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtGM (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu hM hKD σ1 hPA hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ, hM'⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩

end

/-! ## The top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ35` with `MR` at the
chosen outcome (`KPostXM`), given `hDM` [W] (`JDispMR` at the dispatch
states) and `hFast` [P] for `KPostM`. Every other premise as J35. -/
theorem kernel_entryJ36 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
        JDispMR (L := L) arI AR MR s' a' σb n c)
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
    syscall.handle_syscall st arI s a n ⦃ r => KPostXM (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hE := hX.epQAll
  have hQ := hX.ctQ
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x) :=
    fun _ _ => offReady_faultIPSt hX.offReady
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hG : syscall.handle_syscall_old st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ :=
    kernel_entryJ13PUGM s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
      (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
        ((((((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to33 J'
          (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI)).to32
          (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b.to27 hnd hS hni hE hBA).to26
          hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA
          hA hnd hM hKD hmax htu)
      hDM
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27.toR
          (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
      hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu
  have hP : syscall.handle_syscall st arI s a n ⦃ r => KPostM (L := L) arI AR MR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hP ?_
  rintro r (hF | ⟨σ', hy, hRJ, hM'⟩)
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hM', kentry_sinvX hnd c hX hct _ hy⟩

end

/-! ## The induction along `RJ ∧ MR` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The exit relation `kernel_entryJ36` delivers**: `RJ` and `MR`. -/
abbrev RJM (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RJ (L := L) arI AR s a σ ∧ MR a σ.machineState

/-- **The reachable joint states along `RJM`** (module docstring): `start` as
`JReach`; `step` a native syscall from a non-idle thread whose FL4 entry
returns `(s', a')`, with a spec outcome `σ'` of the entry related to it by
the refinement's exit relation `RJM` (which `kernel_entry_reachM` produces;
a related outcome without `MR` need not be reachable, module docstring). -/
inductive JReachM : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → MR a σ.machineState → JReachM s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachM s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachM s' a' σ'

variable {arI AR MR}

/-- `JReachM` is `JReach` (the same steps, `RJM` split). -/
theorem JReachM.toJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachM (L := L) arI AR MR s a σ) :
    JReach (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact JReach.start J hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReach.step n c ih hct hn hv hy hRJ.1 hRJ.2

/-- **The invariant** (`jreach_inv` along `RJM`). -/
theorem jreach_invM (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachM (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ MR a σ.machineState :=
  jreach_inv hnd h.toJ

set_option maxHeartbeats 4000000 in
/-- **Refinement at every reachable state, closed under the step**
(`kernel_entry_reach` with `kernel_entryJ36`): at a reachable state, at the
ghosts `jreach_invM` gives, the syscall entry from a non-idle thread refines
the spec's, and every exit is related (`RJ`), satisfies `SInvX` and `MR`, and
is reachable again. Per-state premises: g4a's (`hflag`, `hK`, `hFin`,
`hFast` now for `KPostM`) and `hDM` [W]. -/
theorem kernel_entry_reachM [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
          JDispMR (L := L) arI AR MR s' a' σb n c) →
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
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invM hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast => ?_⟩
  have hE := kernel_entryJ36 (MR := MR) s a σ J hct hR hX n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA hIA
    hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, hP⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  rcases hP with hF | ⟨σ', hy, hRJ, hM', hX'⟩
  · exact Or.inl hF
  · exact Or.inr ⟨σ', hy, hRJ, hX', hM', JReachM.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩

end

end

end Fl4Proofs.P3
