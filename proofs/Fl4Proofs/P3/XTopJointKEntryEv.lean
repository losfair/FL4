/-
P3 (DESIGN.md §9), invariant line G4 (g4e, KENTRY-PLAN g4e; g4c's handoff
"`fl4CallKernel` for the other events"): **the induction with event steps**,
and the syscall top with both g4c's no-fail post and g4b's `MR` carry.

* `KPostMS` / `KPostXMS`: an outcome σ' of the spec syscall entry (no
  spec-fails disjunct, g4c) with `RJ` and `MR` (g4b), and `SInvX σ'`.
* `kPreFinAtGMS` / `kernel_entryJ13PUGMS`: g4b's `kPreFinAtGM` /
  `kernel_entryJ13PUGM` (same bodies) with the post `KPostMS`. As g4c found
  for `kernel_entryJ13PUG`, the fail disjunct was produced only at the
  preemption branch, from `kPreFinAtGM`'s left disjunct, which its own proof
  never produces.
* **`kernel_entryJ37N`**: `kernel_entryJ37`'s premises (`hDM : JDispMRI`
  [W]), `hFast` [P] at `KPostMS`, post `KPostXMS`.
* Events. No joint refinement theorem exists for any non-syscall FL4 entry
  (`handle_interrupt_entry`, `handle_user_exception`, `handle_vm_fault`, the
  unknown-syscall arm of `handle_syscall`, `handle_trap_syscall`; KENTRY-PLAN
  g4e (1)): only pieces (`JAtZ.handleIrqJIN`, `JAtZ.budgetOkB`, the
  cap-fault `faultHypJZ*` family, `jat_finishJRNM`). `KEv` names those FL4
  entries, `KEvSpec` the spec event each refines (with `fip` when the spec
  event follows the FaultIP write of the current thread: the unknown syscall
  and `int $N` entries, as FL4 writes `FAULT_IP` before deciding), `EvOut` the
  spec outcome. **`JEvRef` [W]** is the named per-step premise: the FL4 entry
  at this state returns and is related (`RJM := RJ ∧ MR`, no spec-fails
  disjunct) to an outcome of the spec event. **`SInvXFip` [W]** (only for
  the two `fip` entries): `SInvX` after the FaultIP write at this state
  (`kcall_sinvX` covers `fl4CallKernel` only; the FaultIP prefix is carried
  for the syscall events inside `kentry_sinvX`, not as a separate lemma).
* **`JReachE`**: `start` (any `JAtZ ∧ SInvX ∧ MR` state), `step` (a native
  syscall along `RJM`, as `JReachM`), `event` (an FL4 event entry along
  `RJM` to an `EvOut` outcome). **`jreach_invE`**: `JAtZ ∧ SInvX ∧ MR` at
  every reachable state (`kentry_sinvX` / `kcall_sinvX`). **`kernel_entry_reachE`**:
  at a reachable state, the syscall entry (via `kernel_entryJ37N`) and every
  event entry with its `JEvRef` end in a related outcome with `SInvX`, `MR`,
  reachable again: one induction for `JAtZ ∧ SInvX ∧ MR`, no spec-fails case,
  no `MR` premise in any step.
-/
import Fl4Proofs.P3.XTopJointKEntryNF
import Fl4Proofs.P3.XTopJointKEntry37
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The posts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KPostM` without the spec-fails disjunct** (module docstring). -/
def KPostMS (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState

/-- **`KPostXM` without the spec-fails disjunct**: the post of `kernel_entryJ37N`. -/
def KPostXMS (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState ∧ SInvX σ'

variable {arI}

theorem KPostMS.toM {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostMS (L := L) arI AR MR c σ r) : KPostM (L := L) arI AR MR c σ r :=
  Or.inr h

theorem KPostXMS.toXM {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostXMS (L := L) arI AR MR c σ r) :
    KPostXM (L := L) arI AR MR c σ r :=
  Or.inr h

theorem KPostXMS.toXS {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {c : Fl4Spec.Syscall}
    {σ : Fl4Spec.State Unit} {r : S × A} (h : KPostXMS (L := L) arI AR MR c σ r) :
    KPostXS (L := L) arI AR c σ r :=
  let ⟨σ', h1, h2, _, h4⟩ := h; ⟨σ', h1, h2, h4⟩

end

/-! ## `kernel_entryJ13PUGM` without the spec-fails disjunct -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`kPreFinAtGM` without the spec-fails disjunct** (module docstring). -/
theorem kPreFinAtGMS {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
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
    syscall.finish st arI r.1 r.2 ⦃ r' =>
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
      fun r' ⟨σ', hmem, hRJ, hM'⟩ => ⟨z, hz, σ', hmem, hRJ, hM'⟩

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUGM` with the post `KPostMS`** (module docstring); same
body. -/
theorem kernel_entryJ13PUGMS [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄ := by
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
      syscall.finish st arI s3 a2) ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    have hMσb := (budget_mr_at (σ0 := faultIPSt σ σ.curThread x) hM hnd hz hMRb hVI).1
    exact WP.spec_mono (jat_finishJRNM s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hM hKD hMσb)
      fun r ⟨σ', hmem, hRJ, hM'⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄
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
        fun r ⟨σ', hmem, hRJ, hM'⟩ => ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtGMS (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu hM hKD σ1 hPA hQ) ?_
      rintro r ⟨z, hz, σ', hmem, hRJ, hM'⟩
      have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
      exact ⟨σ', mem_kentry hx hmem, hRJ, hM'⟩


end

/-! ## The syscall top: no spec-fails disjunct and `MR` at the exit -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The newest syscall top** (module docstring): `kernel_entryJ37`'s premises,
`hFast` [P] at `KPostMS`, post `KPostXMS` (an outcome with `RJ`, `MR` and
`SInvX`; no spec-fails disjunct). -/
theorem kernel_entryJ37N [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
      FastRR (L := L) (arI := arI) s a n (fun r => KPostMS (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXMS (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hE := hX.epQAll
  have hQ := hX.ctQ
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x) :=
    fun _ _ => offReady_faultIPSt hX.offReady
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  have hG : syscall.handle_syscall_old st arI s a n ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄ :=
    kernel_entryJ13PUGMS s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
      (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
        ((((((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to33 J'
          (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI)).to32
          (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b.to27 hnd hS hni hE hBA).to26
          hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA
          hA hnd hM hKD hmax htu)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' => jDispMR_of hM hKD hA hn (hDM σb hBA V' Ac' Lst' D' s' a' hfr J'))
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27.toR
          (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
      hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu
  have hP : syscall.handle_syscall st arI s a n ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hP ?_
  rintro r ⟨σ', hy, hRJ, hM'⟩
  exact ⟨σ', hy, hRJ, hM', kentry_sinvX hnd c hX hct _ hy⟩

end

/-! ## The non-syscall entries -/

/-- **The non-syscall FL4 entries** (module docstring): an interrupt
(`handle_interrupt_entry`), a user exception (`handle_user_exception`), a
user page fault (`handle_vm_fault`), a syscall number `handle_syscall` treats
as unknown (out of range, or trapped by `TRAP_SYSCALLS`), and x86 `int $N`
(`handle_trap_syscall`). Not here: `handle_debug_exception` (the hardware
debug API has no spec event) and `handle_vcpu_exit` (VT-x), both [S]. -/
inductive KEv where
  | irq (w : U64)
  | user (number code : U64)
  | vmf (addr code : U64)
  | sysU (n : I64)
  | trap (vector : U64)

/-- The FL4 function each `KEv` runs. -/
def KEv.run {S A : Type} (st : machine.Store S) (arI : machine.Arch A) : KEv → S → A → Result (S × A)
  | .irq w, s, a => syscall.handle_interrupt_entry st arI s a w
  | .user n c, s, a => syscall.handle_user_exception st arI s a n c
  | .vmf ad c, s, a => syscall.handle_vm_fault st arI s a ad c
  | .sysU n, s, a => syscall.handle_syscall st arI s a n
  | .trap v, s, a => syscall.handle_trap_syscall st arI s a v

/-- **The spec event each FL4 entry refines** and whether the FaultIP write
comes first (`fip`): l4v's `Interrupt`, `UserLevelFault`, `VMFaultEvent`
(the fault kind from the error code), `UnknownSyscall` (the number FL4
reports, trapped or not); `int $N` is an unknown syscall, or under
`TRAP_SYSCALLS` the #GP user exception FL4 raises. The exact argument
values are part of the per-step premise `JEvRef`. -/
inductive KEvSpec : KEv → Bool → Fl4Spec.Event → Prop
  | irq (w : U64) : KEvSpec (.irq w) false .interrupt
  | user (n c : U64) : KEvSpec (.user n c) false (.userLevelFault n.bv c.bv)
  | vmf (ad c : U64) (ft : Fl4Spec.VMFaultType) : KEvSpec (.vmf ad c) false (.vmFaultEvent ft)
  | sysU (n : I64) (m : Nat) : KEvSpec (.sysU n) true (.unknownSyscall m)
  | trapU (v : U64) (m : Nat) : KEvSpec (.trap v) true (.unknownSyscall m)
  | trapF (v : U64) (w1 w2 : Fl4Spec.Word) : KEvSpec (.trap v) true (.userLevelFault w1 w2)

/-- A `KEvSpec` event is not a syscall event. -/
theorem KEvSpec.not_sys {e : KEv} {fip : Bool} {ev : Fl4Spec.Event} (h : KEvSpec e fip ev) :
    ∀ c, ev ≠ .syscallEvent c := by
  cases h <;> intro c e <;> cases e

/-- **An outcome of the spec event**, after the FaultIP write of the current
thread when `fip`. -/
def EvOut (fip : Bool) (ev : Fl4Spec.Event) (σ σ' : Fl4Spec.State Unit) : Prop :=
  match fip with
  | false => ((), σ') ∈ (Fl4Spec.fl4CallKernel (Z := Unit) true ev σ).1
  | true => ∃ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ((), σ') ∈ (Fl4Spec.fl4CallKernel (Z := Unit) true ev w.2).1

/-- **[W] `SInvX` after the FaultIP write at this state** (module docstring;
asked only for the `fip` entries, at their entry state). -/
def SInvXFip (σ : Fl4Spec.State Unit) : Prop :=
  ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, SInvX w.2

/-- **`SInvX` at every event outcome** (`kcall_sinvX`; across the FaultIP
write by `SInvXFip`, which keeps the current and idle thread). -/
theorem sinvX_evOut (hnd : Fl4Spec.numDomains = 1) {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit}
    (hX : SInvX σ) (hev : ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) (hF : fip = true → SInvXFip σ)
    (h : EvOut fip ev σ σ') : SInvX σ' := by
  cases fip with
  | false => exact kcall_sinvX hnd true ev hX hev _ h
  | true =>
    obtain ⟨w, hw, hy⟩ := h
    have hc := SInvR.A8.cfk_fip σ.curThread σ w hw
    have ect : w.2.curThread = σ.curThread := congrArg (fun p => p.2.2.1) hc
    have eid : w.2.idleThread = σ.idleThread := congrArg (fun p => p.2.2.2.1) hc
    exact kcall_sinvX hnd true ev (hF rfl w hw) (fun he => by rw [ect, eid]; exact hev he) _ hy

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[W] The per-step premise of an event** (module docstring): the FL4
entry `e` at this state returns, related (`RJM`: `RJ ∧ MR`) to an outcome
of the spec event. Missing as a theorem for every `KEv` (KENTRY-PLAN g4e
(1)); its [P] part is that the entry's arguments are the ones the spec
reads from the machine (the pending line, the fault address and kind). -/
def JEvRef (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (e : KEv) (fip : Bool)
    (ev : Fl4Spec.Event) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  e.run st arI s a ⦃ r => ∃ σ', EvOut fip ev σ σ' ∧ RJM (L := L) arI AR MR r.1 r.2 σ' ⦄

end

/-! ## The induction with event steps -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with syscall and event steps** (module
docstring). `event`'s `fip = true → SInvXFip σ` is the [W] carry of the two
`fip` entries, asked at the step. -/
inductive JReachE : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → MR a σ.machineState → JReachE s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE s' a' σ'
  | event {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (e : KEv)
      (fip : Bool) (ev : Fl4Spec.Event) :
      JReachE s a σ → KEvSpec e fip ev → (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) →
      (fip = true → SInvXFip σ) → e.run st arI s a = ok (s', a') → EvOut fip ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE s' a' σ'

variable {arI AR MR}

/-- Every `JReachM` state is a `JReachE` state. -/
theorem JReachM.toE {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachM (L := L) arI AR MR s a σ) :
    JReachE (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact JReachE.start J hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE.step n c ih hct hn hv hy hRJ

/-- **The invariant** (module docstring): every state reachable by syscall
and event steps carries `JAtZ` at some ghosts, `SInvX` and `MR`. -/
theorem jreach_invE (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachE (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ MR a σ.machineState := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact ⟨⟨_, _, _, _, _, _, J⟩, hX, hR⟩
  | @step s a σ s' a' σ' n c _ hct _ _ hy hRJ ih => exact ⟨hRJ.1.2, kentry_sinvX hnd c ih.2.1 hct _ hy, hRJ.2⟩
  | @event s a σ s' a' σ' e fip ev _ _ hev hF _ hO hRJ ih =>
    exact ⟨hRJ.1.2, sinvX_evOut hnd ih.2.1 hev hF hO, hRJ.2⟩

set_option maxHeartbeats 4000000 in
/-- **Refinement at every reachable state, syscalls and events** (module
docstring): at a state reachable by syscall and event steps, at the ghosts
`jreach_invE` gives, (i) the syscall entry from a non-idle thread
(`kernel_entryJ37N`'s per-state premises) and (ii) every event entry with its
per-step premise `JEvRef` (and `SInvXFip` for the `fip` entries) end in a
related outcome (no spec-fails case) with `SInvX` and `MR`, which is again
reachable. -/
theorem kernel_entry_reachE [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachE (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
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
          FastRR (L := L) (arI := arI) s a n (fun r => KPostMS (L := L) arI AR MR c σ r)) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            JReachE (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (e : KEv) (fip : Bool) (ev : Fl4Spec.Event), KEvSpec e fip ev →
        (ev ≠ .interrupt → σ.curThread ≠ σ.idleThread) → (fip = true → SInvXFip σ) →
        JEvRef (L := L) arI AR MR e fip ev s a σ →
        e.run st arI s a ⦃ r => ∃ σ', EvOut fip ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invE hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast => ?_,
    fun e fip ev hK hev hF hE => ?_⟩
  · have hE := kernel_entryJ37N (MR := MR) s a σ J hct hR hX n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA hIA
      hmrt hmb hT hmax htu hRef hPI hFast
    obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hM', hX'⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hy, hRJ, hX', hM', JReachE.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩
  · obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX hev hF hO, hRJM.2,
      JReachE.event e fip ev hJ hK hev hF hv hO hRJM⟩

end

end

end Fl4Proofs.P3
