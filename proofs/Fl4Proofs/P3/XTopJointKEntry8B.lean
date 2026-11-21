/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN budtr): **`kernel_entryJ8B`:
`kernel_entryJ8` with the budget premise `KBudget.tmo` (false in reachable
states: a receiver waiting on the current thread's timeout-handler endpoint
satisfies neither disjunct) replaced by `ct_not_in_q`.**

* `KBudgetB`: `KBudget` (XTopJointKEntry) with `tmo : NoTmoSend σ0 ∨ (∀ d p,
  σ0.curThread ∉ σ0.readyQueues d p)` [J] (l4v `ct_not_in_q`: the current
  thread is not queued while `scheduler_action = resume_cur_thread`, which
  `Entered` gives; the same fact as `JEntryAt.ctnq` one step later). The old
  second disjunct's other conjuncts are derived: Running/Restart from
  `JAtZ.curRun` (`CurRunM.run` under `Entered`) and `NativeScope` (the top's
  existing [S] `hNSR` at the entry's `JAtZR`); the endpoint handler and the
  non-round-robin SC from `¬ NoTmoSend`; the handler endpoint's state is
  free: idle/sending by `JAtZ.budgetOkT`, receiving by XTopJointBudgetTR's
  `JAtZ.budgetOkTR`. `KBudget.toB`: the old premise implies the new.
* `JAtZ.budgetOkB`: `budget_ok` at an entry state under `KBudgetB`, both
  outcomes (the `hBud` block of `kernel_entryJ8`, every case).
* `kernel_entryJ8B` = `kernel_entryJ8` with `hB : … → KBudgetB …`.
-/
import Fl4Proofs.P3.XTopJointKEntry8
import Fl4Proofs.P3.XTopJointBudgetTR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The budget-check premises at the entry state after the `FaultIP`
write, the timeout case unrestricted** (module docstring): the clock [P]
`NowAgree`, `CurInv` and `OffReady` [J] as `KBudget`; `tmo` [J] l4v
`ct_not_in_q` unless no timeout-fault send is possible. -/
structure KBudgetB (a : A) (σ0 : Fl4Spec.State Unit) : Prop where
  now : NowAgree arI a σ0
  cur : CurInv σ0
  off : OffReady σ0
  tmo : NoTmoSend σ0 ∨ ∀ d p, σ0.curThread ∉ σ0.readyQueues d p

variable {arI}

theorem KBudget.toB {a : A} {σ0 : Fl4Spec.State Unit} (h : KBudget arI a σ0) : KBudgetB arI a σ0 :=
  ⟨h.now, h.cur, h.off, h.tmo.imp id fun h' => h'.1⟩

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`budget_ok` at an entry state under `KBudgetB`** (module docstring):
`kernel_entryJ8`'s `hBud` for every timeout-handler case. -/
theorem JAtZ.budgetOkB {s : S} {a : A} {σ0 : Fl4Spec.State Unit}
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ0) (hni0 : Entered σ0) (hBu : KBudgetB arI a σ0)
    (hNS0 : NativeScope σ0) (hAK : ARKeep arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0 =
          ({(true, σ')}, False) ∧
        σ'.kheap = σ0.kheap ∧ σ'.curThread = σ0.curThread ∧ σ'.curSc = σ0.curSc ∧
        σ'.schedulerAction = σ0.schedulerAction ∧ σ'.idleThread = σ0.idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := by
  have hF : ∀ hnt : NoTmoSend σ0, syscall.budget_ok st arI s a ⦃ r =>
      (r.1 = true → ∃ σ', (Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0 =
          ({(true, σ')}, False) ∧
        σ'.kheap = σ0.kheap ∧ σ'.curThread = σ0.curThread ∧ σ'.curSc = σ0.curSc ∧
        σ'.schedulerAction = σ0.schedulerAction ∧ σ'.idleThread = σ0.idleThread ∧
        CurInv σ' ∧ OffReady σ' ∧ ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' r.2.1 r.2.2 σ') ∧
      (r.1 = false → ∃ z ∈ (specBudget σ0).1, z.1 = false ∧
        ∃ (Z' : XSets) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2) ⦄ := fun hnt =>
    WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J'⟩
          unfold specBudget
          rw [he]; exact Set.mem_singleton _⟩
  rcases hBu.tmo with hnt | hnq
  · exact hF hnt
  by_cases hnt : NoTmoSend σ0
  · exact hF hnt
  -- an endpoint timeout handler and a non-round-robin SC
  unfold NoTmoSend at hnt
  push_neg at hnt
  obtain ⟨⟨xt, hkt, hep⟩, ⟨y, m, hky, hy⟩⟩ := hnt
  have hper : ∀ x n, σ0.kheap σ0.curSc = some (.schedContext x n) → x.scPeriod ≠ 0 := fun x n h => by
    rw [hky] at h; cases h; exact hy
  obtain ⟨p, bd, rr, hth⟩ : ∃ p bd rr, xt.tcbTimeoutHandler = .endpointCap p bd rr := by
    revert hep; cases xt.tcbTimeoutHandler <;> simp [Fl4Spec.isEpCap]
  have hrr : xt.tcbState = .running ∨ xt.tcbState = .restart := by
    have hrun := J0.curRun.run hni0 xt hkt
    have hvm := hNS0 _ xt hkt
    revert hrun hvm; cases xt.tcbState <;> simp [Fl4Spec.runnable]
  by_cases hkl : ∃ l, σ0.kheap p = some (.endpoint (.recvEP l))
  · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkTR hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hmax htu hnq hkt hrr hth hper hkl))
      fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩
  · have hcb : ∀ xe, σ0.kheap p = some (.endpoint xe) → Endp.CanBlock false xe := fun xe h => by
      cases xe with
      | idleEP => trivial
      | sendEP q => rfl
      | recvEP q => exact absurd ⟨q, h⟩ hkl
    exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb))
      fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ8`
with `KBudgetB` for `KBudget` (`tmo`: `ct_not_in_q` [J] unless no
timeout-fault send; every timeout-handler endpoint state covered; module
docstring). -/
theorem kernel_entryJ8B [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps8 (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hPF := kPreFinHypJI_of hFin hA hnd hmb hNS hNSR hT hmax htu
  have hvm := hvm_of_ns hNS
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
  have hBud := JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (hNSR _ _ _ _ _ _ _ _ _ J0.toR) hAK hA hnd hmrt hmb hmax htu
  refine WP.spec_bind hBud ?_
  rintro ⟨b, s2, a1⟩ ⟨hTr, hFa⟩
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
    have F := hFin _ hx Z' H Cs Ac' Lst' D' s2 a1 J'.toR
    exact WP.spec_mono (jat_finishJR s2 a1 σb J'.toR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR H Cs) hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
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
    have hnib : Entered σb := ⟨by rw [ect, eidle]; exact hni0.1, by rw [eact]; exact hni0.2⟩
    refine WP.spec_bind (dispatch_all8 s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      have F := hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 JmR
      exact WP.spec_mono (jat_finishJR s3 a2 σm JmR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR Hm Csm) hmb
        F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
    · obtain ⟨u, σ1⟩ := y
      simp only at hy1; subst hy1
      have hPA : PreemptedAt c σ σ1 := ⟨σb, hBA, hy⟩
      refine WP.spec_mono (hPF σ1 hPA (s3, a2) hQ) ?_
      rintro r (hfail | ⟨z, hz, σ', hmem, hRJ⟩)
      · exact Or.inl (fail_kentry hF hb hy hfail)
      · have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
          mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
        exact Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩


end

end

end Fl4Proofs.P3
