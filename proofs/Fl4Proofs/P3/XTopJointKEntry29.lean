/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, KENTRY-PLAN g3d):
**`kernel_entryJ29` = `kernel_entryJ28` (g3b: no `hNS` / `hNSR`) with g3c's
discharges (`kernel_entryJ27b`: `JPerfRegHyp`, `JPerfIrqSlotHyp`, `JMidVfhHyp`,
`JEntryAt.epQ`)**, and **`kernel_entryJ29G`** = `kernel_entryJ29` with the two
∀-ghost premises `hK` / `hFin` re-scoped (INV-PLAN §3 / "Top risks" 5).

* `kernel_entryJ29`: a wrapper over J28 (`KDispHypsKV27b.to27`); premises J28's
  plus `hE : EpQAll σ` [J], with `hK` asking `KDispHypsKV27b`.
* Re-scoping. J28's body (`kernel_entryJ13PUN`) applies `hK` once, at the dispatch
  state σb, at the ghosts `Z.mv Z.G V0`, `H`, `Cs` (`V0` from the `FaultIP` write,
  `Ac' Lst' D'` from `budgetOkB`) and at the FL4 state `(s2, a1)` the passing
  `budget_ok` returns; and `hFin` three times, at the FL4 state `finish` starts
  from (`budget_ok`'s stopping outcome, or `dispatch_syscall`'s outcome after a
  passing one, also on the preemption path). As stated, `hK` / `hFin` quantify
  over EVERY FL4 state `s'` (and every ghost) jointly related to σb / the front
  outcome by `JAtZ` / `JAtZR`; their fields that `JAtZ` does not determine
  (`JEntryAtR2.flags`, `handlers`, `vsTyp`, …, `KFinAtR27.hd`'s FL4 word, `tail`)
  are then asked at FL4 states the run never reaches, so no per-state invariant
  can discharge them. `kernel_entryJ13PUG` is `kernel_entryJ13PUN` (same body)
  with `hK` asked only at the carried ghosts and at FL4 states `KFrontB` (the
  current thread's `FaultIP` write, then a passing `budget_ok`), and `hFin` only at
  FL4 states `KFrontF` (the same write, `budget_ok`, then `dispatch_syscall` when it
  passes): the FL4 side's counterpart of `BudgetAt` / `specFront`. The value
  written to `FAULT_IP` is left universally quantified (any `v`); everything else
  is the actual run. The equations come from `Sched.spec_and_eq` on the two
  calls; `kPreFinAtG` is `kPreFinHypJI_ofN` at one FL4 state.
* `kernel_entryJ29G`: J29's premises with the re-scoped `hK` / `hFin`
  (strictly weaker hypotheses: J29 follows from it).
-/
import Fl4Proofs.P3.XTopJointKEntry28
import Fl4Proofs.P3.XTopJointKEntry27b
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## J28 with g3c's discharges -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ28` with `kernel_entryJ27b`'s discharges** (module docstring).
Premises: J28's, `hK` asking `KDispHypsKV27b` (no `JEntryAt.epQ`, no mid perf /
IRQ-slot / handler facts), plus `hE : EpQAll σ` [J] (l4v `valid_ep` with
`valid_sched`'s released-queue / action slices at σ; epq2's `kentry_epQAll` /
`kcall_epQAll` carry it). -/
theorem kernel_entryJ29 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ28 s a σ J hni hR hS hQ n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' =>
      (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to27 hnd hS hni hE hBA)
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu

end

/-! ## The FL4 front: the states the run reaches -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's dispatch states** (module docstring): the current thread's `FAULT_IP`
written (any value), then a passing `budget_ok`. The FL4 side of `BudgetAt σ σb true`. -/
def KFrontB (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ ct v, sched.cur_thread st s = ok ct ∧
    syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a = ok (true, s', a')

/-- **FL4's front-end outcomes** (module docstring): the `FAULT_IP` write, `budget_ok`,
and `dispatch_syscall` when it passes; the state `finish` starts from. The FL4 side of
`specFront`. -/
def KFrontF (n : I64) (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ ct v b s2 a2, sched.cur_thread st s = ok ct ∧
    syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a = ok (b, s2, a2) ∧
    ((b = false ∧ s' = s2 ∧ a' = a2) ∨ (b = true ∧ syscall.dispatch_syscall st arI s2 a2 n = ok (s', a')))

end

/-! ## `kernel_entryJ13PUN` with `hK` / `hFin` at the run's FL4 states -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`kPreFinHypJI_ofN` at one FL4 state `r`** (module docstring): `hFin` asked
only at `r`. -/
theorem kPreFinAtG {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' r.1 r.2 x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' r.1 r.2 x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS0 : NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (σ1 : Fl4Spec.State Unit) (hPA : PreemptedAt c σ σ1) (hQ : PPQJI (L := L) arI AR σ1 r) :
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ⦄ := by
  obtain ⟨z, hz, Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩ := hQ
  obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
  have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
    mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
  have F := hFin _ hx Zm Hm Csm Acm Lstm Dm Jm.toR
  exact WP.spec_mono (jat_finishJRN r.1 r.2 z.2 Jm.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu)
      fun r' ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨z, hz, σ', hmem, hRJ⟩

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUN` with `hK` at the carried ghosts and `KFrontB` states,
`hFin` at `KFrontF` states** (module docstring); same body. -/
theorem kernel_entryJ13PUG [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hMK : MRKeep arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
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
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    exact WP.spec_mono (jat_finishJRN s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPost (L := L) arI AR c σ r ⦄
    rw [if_pos rfl]
    have hb : (true, σb) ∈ (specBudget (faultIPSt σ σ.curThread x)).1 := by
      unfold specBudget
      rw [he]; exact Set.mem_singleton _
    have hBA : BudgetAt σ σb true := ⟨_, hF, hb⟩
    obtain ⟨hMRσb, hVIσb⟩ := budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd (show (true, σb) ∈ _ by rw [he]; exact Set.mem_singleton _)
      hMRb hVI
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    have hNSb : NativeScope σb := SInvN.ns_of_kheap ekh (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF)
    refine WP.spec_bind (spec_and_eq (dispatch_all13PUN s2 a1 σb J' hnib n c hn
      (hK σb hBA V0 _ _ _ s2 a1 ⟨ct, v, hct, hbeq⟩ J') hMRσb hVIσb hNSb hARI hA hnd hM hMK hPA hIA hmrt hmax htu)
      fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩, hdeq⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2
        ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ JmR
      exact WP.spec_mono (jat_finishJRN s3 a2 σm JmR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtG (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu σ1 hPA hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩

end

/-! ## The re-scoped top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ29` with `hK` / `hFin` at the run's own FL4 states and the
carried ghosts** (module docstring). `hK` is asked at the dispatch state σb only at
the ghosts `Z.mv Z.G V'`, `H`, `Cs` and at FL4 states `KFrontB` (the `FAULT_IP`
write and a passing `budget_ok`); `hFin` at the front-end outcomes only at FL4
states `KFrontF`. Every other premise as J29. -/
theorem kernel_entryJ29G [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hct : σ.curThread ≠ σ.idleThread := hni.1
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  exact kernel_entryJ13PUG s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
    (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
    (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
      (((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to27 hnd hS hni hE hBA).to26 hnd hS hni hQ hB hBA).to25 hA hmax
        htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA hA hnd hM hKD hmax htu)
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
      (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').toR (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
    hARI hA hnd hM hKD.toK hPA hIA hmrt hmb hT hmax htu

/-- **J29G's premises are weaker than J29's**: the re-scoped `hK` / `hFin` are
instances of J29's (so J29 is a corollary; the converse is the point of J29G). -/
theorem kernel_entryJ29_of_G [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs : Set U64} {σ : Fl4Spec.State Unit} {s : S} {a : A} {n : I64} {c : Fl4Spec.Syscall}
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2) :
    (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV27b (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) ∧
    (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR27 (L := L) arI AR Z' H' Cs' s' a' x.2) :=
  ⟨fun σb hBA V' Ac' Lst' D' s' a' _ J' => hK σb hBA _ H Cs Ac' Lst' D' s' a' J',
    fun x hx Z' H' Cs' Ac' Lst' D' s' a' _ J' => hFin x hx Z' H' Cs' Ac' Lst' D' s' a' J'⟩

end

end

end Fl4Proofs.P3
