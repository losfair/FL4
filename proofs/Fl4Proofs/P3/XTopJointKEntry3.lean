/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch8 (2) (iii)):
**`kernel_entryJ3`: `kernel_entryJ2` with the mid dispatch allowed to end in
`JAtZS`** (XTopJointJAtZS).

`KDispHyps.mid` [W] was false in reachable states (sch8 (2): NBSendRecv /
NBSendWait whose send wakes a waiting receiver and whose receive then blocks
the current thread end with `switchThread u` over a blocked current thread,
where `JAt` fails). `KDispHypsS.mid` asks only `DispPostS` (`JAtS` at an ok
outcome). The finish from such a `SwBlk` outcome is `KFinSwHyp` [W] (to be
proved by sch8 (ii)); a `JAtZ` outcome goes to `jat_finishJ2` as before.
`dispatch_allS`: `dispatch_allK` into `DispPostS`. `KDispHyps.toS`: the old
premise implies the new one.
-/
import Fl4Proofs.P3.XTopJointKEntry2
import Fl4Proofs.P3.XTopJointJAtZS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`DispPost` with `JAtZS` at an ok outcome** (module docstring). -/
def DispPostS (AR : A → Fl4Spec.Cr3 → Prop) (Q : Fl4Spec.State Unit → S × A → Prop) (m : Fl4Spec.PMonad Unit Unit)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ y ∈ (m.run σ).1,
    (y.1 = .ok () ∧ RelTopM (L := L) r.1 y.2 ∧ JAtS (L := L) arI AR r.1 r.2 y.2) ∨ (y.1 = .error () ∧ Q y.2 r)

/-- **`KDispHyps` with the mid dispatch ending in `DispPostS`**: `mid` [W]
(M6) is the whole ReplyRecv / NBSendRecv / NBSendWait dispatch, whose ok
outcome may be a `SwBlk` state (the send woke a waiting receiver, the receive
blocked the current thread), where `JAt` is false but `JAtS` holds; `inv`,
`recv` as `KDispHyps`. -/
structure KDispHypsS (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : MidSys n c → syscall.dispatch_syscall st arI s a n ⦃ r =>
    DispPostS (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄

/-- **[W] `finish` from a pending switch over the blocked current thread**
(sch8 (2) option (b), step (ii)): at an ok outcome `x` of the entry's front
(FaultIP write, budget check, dispatch) that is a `JAtZS` state with `SwBlk`,
FL4's `finish` refines `fl4Awaken; schedule; activateThread` with `RJ`
after. l4v: `call_kernel`'s `schedule` from `invs` with
`scheduler_act_sane` (Schedule_AI `schedule_invs`). Missing at J: the
timers (`JAtZ.fireJ`'s signal cone) and `schedule_refinesWP0F` from `JAtZS`
(KENTRY-PLAN sch8 (i): in the switch branch the spec does not enqueue the
non-runnable current thread and the new current thread is the idle thread or a
schedulable one, so `CurInv` of the old one is not needed). Not false in
reachable states: after `schedule` the action is `resumeCurThread` and the
chosen thread's `CurInv` holds (`newcur_ofF`), so `JAtZ` holds again. -/
def KFinSwHyp (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ (specFront c σ).1, x.1 = .ok () → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
    (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
    JAtZS (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → SwBlk x.2 →
    syscall.finish st arI s' a' ⦃ r => ∃ σ',
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) x.2).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ⦄

variable {arI}

theorem DispPost.toS {AR : A → Fl4Spec.Cr3 → Prop} {Q : Fl4Spec.State Unit → S × A → Prop}
    {m : Fl4Spec.PMonad Unit Unit} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : DispPost (L := L) arI AR Q m σ r) : DispPostS (L := L) arI AR Q m σ r :=
  let ⟨y, hy, hh⟩ := h; ⟨y, hy, hh.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.toS⟩) id⟩

theorem KDispHyps.toS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs D : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (h : KDispHyps (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsS (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨h.inv, h.recv, fun hm => WP.spec_mono (h.mid hm) fun _ ⟨y, hy, hh⟩ =>
    ⟨y, hy, hh.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3.toS⟩) id⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`dispatch_syscall` for every native system call at `J`** after a
passing budget check, ending in `DispPostS` (`JAtZS` allowed at an ok outcome). -/
theorem dispatch_allS [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHypsS (L := L) arI AR Z H Cs D s a σ n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypK (L := L) arI AR)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostS (L := L) arI AR (PPQ (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJEPZK s a σ J _ hct n call bl don hi hG hE hP hARI hA hnd hPP hmrt hIP hNS hRest)
      fun _ h => h.toS
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toS⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hmb a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toS⟩⟩
  · exact hK.mid hm

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ2`
with `KDispHypsS` (the mid dispatch may end in `JAtZS`: a pending switch over
the blocked current thread, `SwBlk`) and the finish from such a state named
`hSw` (`KFinSwHyp` [W]). Other premises as `kernel_entryJ2`. -/
theorem kernel_entryJ3 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsS (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAt2 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hPF : KPreFinHyp (L := L) arI AR c σ) (hSw : KFinSwHyp (L := L) arI AR c σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypK (L := L) arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
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
    rcases hBu.tmo with hnt | ⟨hnq, xt, hkt, hrr, p, bd, rr, hth, hper, hcb⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkF hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnt)) fun r ⟨h1, h2⟩ => ⟨h1, fun hf => by
          obtain ⟨σ', he, Ac', Lst', D', J'⟩ := h2 hf
          refine ⟨(false, σ'), ?_, rfl, _, Ac', Lst', D', J'⟩
          unfold specBudget faultIPSt
          rw [he]; exact Set.mem_singleton _⟩
    · exact WP.spec_mono (WP.spec_and (J0.budgetOkJ hAK hA hnd hBu.now hBu.cur hBu.off hmb)
        (J0.budgetOkT hAK hA hnd hBu.now hni0 hBu.cur hmrt hmb hnq hkt hrr hth hper hcb)) fun r ⟨h1, h2⟩ =>
          ⟨h1, fun hf => by
            obtain ⟨z, hz, hz1, V, Ac', Lst', D', J'⟩ := h2 hf
            exact ⟨z, hz, hz1, _, Ac', Lst', D', J'⟩⟩
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
    have F := (hFin _ hx Z' H Cs Ac' Lst' D' s2 a1 J').toK hNS
    exact WP.spec_mono (jat_finishJ2 s2 a1 σb J' F.hd hnd hA F.vt F.w hmb F.arch F.archNd F.fo F.sni F.send hT
      F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
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
    refine WP.spec_bind (dispatch_allS s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hRest hmax htu) ?_
    rintro ⟨s3, a2⟩ ⟨y, hy, ⟨hy1, hR, hJ⟩ | ⟨hy1, hQ⟩⟩
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmS⟩ := hJ
      obtain ⟨u, σm⟩ := y
      simp only at hy1; subst hy1
      have hx : ((.ok (), σm) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
        mem_specFront hF (mem_handleE_ok (mem_fl4HandleEvent hb (mem_whenE_true hy)))
      rcases JmS.toJ_or with Jm | hsw
      swap
      · exact WP.spec_mono (hSw _ hx rfl Zm Hm Csm Acm Lstm Dm s3 a2 JmS hsw)
          fun r ⟨σ', hmem, hRJ⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
      have F := (hFin _ hx Zm Hm Csm Acm Lstm Dm s3 a2 Jm).toK hNS
      exact WP.spec_mono (jat_finishJ2 s3 a2 σm Jm F.hd hnd hA F.vt F.w hmb F.arch F.archNd F.fo F.sni F.send hT
        F.tail hmax htu hvm) fun r ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨σ', mem_kentry hx hmem, hRJ⟩
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
