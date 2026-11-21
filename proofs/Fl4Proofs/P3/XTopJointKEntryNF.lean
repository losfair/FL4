/-
P3 (DESIGN.md §9), invariant line G4 (KENTRY-PLAN g4a (6) item (G-a), g4c):
**the spec-fails disjunct of the entry's post is gone.**

* Where the disjunct came from. In the whole chain under `kernel_entryJ35`
  (J35 → J34 → J33 → J33G → J32 → J31 → J30 → J29G → `kernel_entryJ13PUG`) the
  left disjunct of `KPost` ("the spec entry fails") is produced at exactly one
  place: the preemption branch of `kernel_entryJ13PUG`, from the left disjunct of
  `kPreFinAtG`'s post (a failing `preemptionPath`). `kPreFinAtG`'s proof never
  produces that disjunct: its input `PPQJI` already names an outcome of
  `preemptionPath`, and `jat_finishJRN` relates an outcome after it. Every other
  branch (budget stop, dispatch to completion) already ends in an outcome. The
  joint proofs construct the spec outcome step by step from the joint relation
  (`JAtZ`, its per-kind object and cap relations), so the spec's asserts on the
  path they follow are discharged there; the "(m)" sites of g4c's inventory never
  need a spec-only typing invariant on this route.
* `kPreFinAtGS` / `kernel_entryJ13PUGS`: the same statements and proofs with the
  post `KPostS` (only the outcome disjunct of `KPost`).
* `kentry_genS`: `kernel_entryJ34`'s general path with `KPostS`, composed from the
  wrappers J29G → J34 (their bundle conversions inlined; no new premise).
* **`kernel_entryJ36N`**: `kernel_entryJ35`'s premises (the fast-path premise
  `hFast` is m57's `FastRR` at the post `KPostS`: the fast path keeps what the
  general path guarantees, for that post), post **`KPostXS`**: an outcome σ' of
  the spec entry with `RJ` and `SInvX σ'` — no spec-fails disjunct.
* **`kentry_nofailJ`**: at the same premises, the spec syscall entry has an
  outcome (its result set is nonempty) and the FL4 entry returns. NOT l4v's
  `no_fail` (no branch fails): it says the entry is not stuck, which is all the
  induction needs.
* **`kernel_entry_reachN`**: `kernel_entry_reach` with the post `KPostXS`: every
  run from a reachable state lands in a related outcome that is again reachable
  given `MR` at the exit (g4a's (G-b)).
-/
import Fl4Proofs.P3.XTopJointKEntry35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KPost` without the spec-fails disjunct**: an outcome of the spec entry is
related (`RJ`). -/
def KPostS (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ'

theorem KPostS.toKPost {AR : A → Fl4Spec.Cr3 → Prop} {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : KPostS (L := L) arI AR c σ r) : KPost (L := L) arI AR c σ r := Or.inr h

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`kPreFinHypJI_ofN` at one FL4 state `r`** (module docstring): `hFin` asked
only at `r`. -/
theorem kPreFinAtGS {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' r.1 r.2 x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' r.1 r.2 x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS0 : NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (σ1 : Fl4Spec.State Unit) (hPA : PreemptedAt c σ σ1) (hQ : PPQJI (L := L) arI AR σ1 r) :
    syscall.finish st arI r.1 r.2 ⦃ r' =>
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
      fun r' ⟨_, σ', _, _, hmem, hRJ, _⟩ => ⟨z, hz, σ', hmem, hRJ⟩

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUN` with `hK` at the carried ghosts and `KFrontB` states,
`hFin` at `KFrontF` states** (module docstring); same body. -/
theorem kernel_entryJ13PUGS [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostS (L := L) arI AR c σ r ⦄ := by
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
      syscall.finish st arI s3 a2) ⦃ r => KPostS (L := L) arI AR c σ r ⦄
    rw [if_neg (by decide)]
    simp only [bind_ok]
    have hx : ((.ok (), σb) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hz mem_whenE_false))
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1
      ⟨ct, v, false, s2, a1, hct, hbeq, Or.inl ⟨rfl, rfl, rfl⟩⟩ J'.toR
    exact WP.spec_mono (jat_finishJRN s2 a1 σb J'.toR (SInvN.ns_front true c hNS0 _ hx) F.hd hnd hA F.vt hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => ⟨σ', mem_kentry hx hmem, hRJ⟩
  · -- the system call runs
    obtain ⟨σb, he, ekh, ect, ecs, eact, eidle, hCb, hOb, Ac', Lst', D', J'⟩ := hTr rfl
    show (do
      let (s3, a2) ← (if true = true then syscall.dispatch_syscall st arI s2 a1 n else ok (s2, a1))
      syscall.finish st arI s3 a2) ⦃ r => KPostS (L := L) arI AR c σ r ⦄
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
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (kPreFinAtGS (r := (s3, a2))
        (fun x hx Z' H' Cs' Ac' Lst' D' J' =>
          hFin x hx Z' H' Cs' Ac' Lst' D' s3 a2 ⟨ct, v, true, s2, a1, hct, hbeq, Or.inr ⟨rfl, hdeq⟩⟩ J')
        hA hnd hmb hNS0 hT hmax htu σ1 hPA hQ) ?_
      rintro r ⟨z, hz, σ', hmem, hRJ⟩
      have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
      exact ⟨σ', mem_kentry hx hmem, hRJ⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G4
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entryJ34`'s general path with the post `KPostS`** (module
docstring): `kernel_entryJ13PUGS` under J34's premises, the bundle conversions of
J29G … J33G inlined. -/
theorem kentry_genS [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ)
    (hR : MR a σ.machineState) (hS : SInvAll.SInvB σ) (hE : SInvE.EpQAll σ)
    (hQ : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV33 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
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
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPostS (L := L) arI AR c σ r ⦄ := by
  have hct : σ.curThread ≠ σ.idleThread := hni.1
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  exact kernel_entryJ13PUGS s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
    (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
    (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
      ((((((((hK σb hBA V' Ac' Lst' D' s' a' hfr J').to32
        (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b).to27 hnd hS hni hE hBA).to26 hnd hS
        hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA hA hnd hM hKD
        hmax htu)
    (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
      ((hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27).toR
        (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
    hARI hA hnd hM hKD.toK hPA hIA hmrt hmb hT hmax htu

variable (arI) in
/-- **`KPostX` without the spec-fails disjunct**: an outcome σ' of the spec
entry, related (`RJ`) and satisfying `SInvX`. -/
def KPostXS (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ'

theorem KPostXS.toX {AR : A → Fl4Spec.Cr3 → Prop} {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : KPostXS (L := L) arI AR c σ r) : KPostX (L := L) arI AR c σ r := Or.inr h

set_option maxHeartbeats 4000000 in
/-- **The newest top** (module docstring): `kernel_entryJ35`'s premises, `hFast`
at the post `KPostS`, and the post `KPostXS` (no spec-fails disjunct). -/
theorem kernel_entryJ36N [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
      FastRR (L := L) (arI := arI) s a n (fun r => KPostS (L := L) arI AR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostXS (L := L) arI AR c σ r ⦄ := by
  have hG := kentry_genS (MR := MR) s a σ J (hX.entered hct) hR hX.sb hX.epQAll hX.ctQ n c hn hflag
    (fun _ _ => offReady_faultIPSt hX.offReady)
    (fun σb hBA V' Ac' Lst' D' s' a' hF J' => (hK σb hBA V' Ac' Lst' D' s' a' hF J').to33 J'
      (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI))
    hFin hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu
  have hE : syscall.handle_syscall st arI s a n ⦃ r => KPostS (L := L) arI AR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastRR.acc hflag hn.range hrr (hFast hrr))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hE ?_
  rintro r ⟨σ', hy, hRJ⟩
  exact ⟨σ', hy, hRJ, kentry_sinvX hnd c hX hct _ hy⟩

set_option maxHeartbeats 4000000 in
/-- **(G-a) at the joint level** (module docstring): at a `JAtZ` state with
`SInvX`, the [S] scope and J36's other premises, the FL4 entry returns and the
spec syscall entry has an outcome (related to FL4's exit). -/
theorem kentry_nofailJ [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
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
      FastRR (L := L) (arI := arI) s a n (fun r => KPostS (L := L) arI AR c σ r)) :
    ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ SInvX σ' ∧
      ∃ r, syscall.handle_syscall st arI s a n = ok r ∧ RJ (L := L) arI AR r.1 r.2 σ' := by
  obtain ⟨r, hv, σ', hy, hRJ, hX'⟩ := spec_exists (kernel_entryJ36N (MR := MR) s a σ J hct hR hX n c hn hflag hK hFin
    hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hFast)
  exact ⟨σ', hy, hX', r, hv, hRJ⟩

end

/-! ## The induction with the strengthened post -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`kernel_entry_reach` without the spec-fails disjunct** (module docstring):
at a reachable state, every run of the entry lands in a related outcome of the
spec entry with `SInvX`, reachable again given `MR` at the exit. -/
theorem kernel_entry_reachN [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReach (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv → FastRR (L := L) (arI := arI) s a n (fun r => KPostS (L := L) arI AR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧
          (MR r.2 σ'.machineState → JReach (L := L) arI AR MR r.1 r.2 σ') ⦄ := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_inv hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hFin hFast => ?_⟩
  have hE := kernel_entryJ36N (MR := MR) s a σ J hct hR hX n c hn hflag hK hFin hARI hA hnd hM hKD hPA hIA
    hmrt hmb hT hmax htu hRef hPI hFast
  obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hX'⟩ := spec_exists hE
  rw [hv, WP.spec_ok]
  exact ⟨σ', hy, hRJ, hX', fun hM' => JReach.step n c hJ hct hn hv hy hRJ hM'⟩

end

end

end Fl4Proofs.P3.SInvR.G4
