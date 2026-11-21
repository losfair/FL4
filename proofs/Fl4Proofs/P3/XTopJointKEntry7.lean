/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch12 (3)): **`kernel_entryJ7`:
`kernel_entryJ6` with the failing-spec case (b) of `KPreFinRestHypC` closed
for the covered preemption holes.**

Under `IrqPlatI` [P] (XTopJointIrqZI: the pending line is not inactive) the
covered preemption paths end in `PPQJI` (`JAt` after, no spec failure), so a
`PPQCI` state without `JAt` after the path is a `RestE` hole (kp's
`JPreemptRestHypE` output).

* `KDispHypsRI`: `KDispHypsR` with `mid` [W] ending in `PPQCI` (as the proved
  invoking dispatches now do, `dispatch_invokeJEPZECI`).
* `KPreFinRestHypI` [W]: `KPreFinRestHypC` at `RestE` holes only.
* `dispatch_allRI`, `kPreFinHypCI_of`, `kernel_entryJ7`.
-/
import Fl4Proofs.P3.XTopJointIrqZI
import Fl4Proofs.P3.XTopJointKEntry6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsR` with `mid` [W] ending in `PPQCI`**
(module docstring); `inv`, `recv` as `KDispHyps`. -/
structure KDispHypsRI (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : MidSys n c → syscall.dispatch_syscall st arI s a n ⦃ r =>
    DispPostR (L := L) arI AR (PPQCI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄


/-- **[W] `finish` after a preempted invocation at a `RestE` hole where `JAt`
fails after the path** (KPreFinRestHypC without its (b) part for the covered
holes: under `IrqPlatI` the covered preemption paths end in `JAt` with no spec
failure; what is left is exactly the output of kp's `JPreemptRestHypE`). -/
def KPreFinRestHypI (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σ1, PreemptedAt c σ σ1 → RestE σ1 → ∀ r : S × A, PPQ (L := L) arI AR σ1 r →
    (¬ ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, JAt (L := L) arI AR r.1 r.2 z.2) →
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ⦄

def KPreFinHypCI (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σ1, PreemptedAt c σ σ1 → ∀ r : S × A, PPQCI (L := L) arI AR σ1 r →
    syscall.finish st arI r.1 r.2 ⦃ r' => (Fl4Spec.preemptionPath (Z := Unit) σ1).2 ∨
      ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, ∃ σ',
        ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) z.2).1 ∧
        RJ (L := L) arI AR r'.1 r'.2 σ' ⦄


variable {arI}

set_option maxHeartbeats 4000000 in
/-- **`dispatch_allR` ending in `PPQCI`** (with `IrqPlatI`). -/
theorem dispatch_allRI [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c) (hK : KDispHypsRI (L := L) arI AR Z H Cs D s a σ n c)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlatI (L := L) arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.dispatch_syscall st arI s a n ⦃ r =>
      DispPostR (L := L) arI AR (PPQCI (L := L) arI AR) (Fl4Spec.fl4HandleSyscall true c) σ r ⦄ := by
  have hct := cur_thread_eq (L := L) s
  rcases hn with ⟨call, bl, don, hi, rfl⟩ | ⟨bl, cr, hr, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · obtain ⟨hG, hE, hP⟩ := hK.inv _ call bl don hct hi
    exact WP.spec_mono (dispatch_invokeJEPZECI s a σ J _ hct n call bl don hi hG hE hP hARI hA hnd hPP hmrt hIP hNS hRest)
      fun _ h => h.toR
  · obtain ⟨hnq, hvfh⟩ := hK.recv bl cr hr
    exact WP.spec_mono (dispatch_recvJL true hA s a σ J hni hct hnq hvfh n bl cr hr hmax (htu a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact WP.spec_mono (dispatch_yieldJ true hA s a σ J hni hct (hmrt a) (hmb a))
      fun _ ⟨y, hy, h1, h2⟩ => ⟨y, hy, Or.inl ⟨h1, h2.1, h2.2.toRE⟩⟩
  · exact hK.mid hm


variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`KPreFinHypCI` from `KPreFinRestHypI`** (`kPreFinHypC_of` over `PPQCI`: a `PPQJI` state has `JAt` after the path). -/
theorem kPreFinHypCI_of {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit}
    (hR : KPreFinRestHypI (L := L) arI AR c σ)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    KPreFinHypCI (L := L) arI AR c σ := by
  intro σ1 hPA r hQ
  by_cases hJ : ∃ z ∈ (Fl4Spec.preemptionPath (Z := Unit) σ1).1, JAt (L := L) arI AR r.1 r.2 z.2
  · obtain ⟨z, hz, Zm, Hm, Csm, Acm, Lstm, Dm, Jm⟩ := hJ
    obtain ⟨σb, ⟨σ0, hF, hb⟩, hy⟩ := hPA
    have hx : ((.ok z.1, z.2) : Except Unit Unit × Fl4Spec.State Unit) ∈ (specFront c σ).1 :=
      mem_specFront hF (mem_handleE_err (mem_fl4HandleEvent hb (mem_whenE_true hy)) (mem_liftE hz))
    have F := hFin _ hx Zm Hm Csm Acm Lstm Dm r.1 r.2 Jm.toR
    exact WP.spec_mono (jat_finishJR r.1 r.2 z.2 Jm.toR F.hd hnd hA F.vt (signalRestJHypZR_of_ns hNSR Hm Csm) hmb
      F.arch F.archNd F.fo F.sni F.send hT F.tail hmax htu (hvm_of_ns hNS))
      fun r' ⟨_, σ', _, _, hmem, hRJ, _⟩ => Or.inr ⟨z, hz, σ', hmem, hRJ⟩
  · rcases hQ with hQ | ⟨hRE, hQ⟩
    · exact absurd hQ hJ
    · exact hR σ1 hPA hRE r hQ hJ


set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ6`
with `IrqPlatI` [P] for `IrqPlat`, `KDispHypsRI` (mid [W] ending in `PPQCI`)
and `KPreFinRestHypI` [W] (only `RestE` holes) for `KPreFinRestHypC` (module
docstring). -/
theorem kernel_entryJ7 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHypsRI (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hPR : KPreFinRestHypI (L := L) arI AR c σ)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlatI (L := L) arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hRest : JPreemptRestHypE (L := L) arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ := by
  have hPF := kPreFinHypCI_of hPR hFin hA hnd hmb hNS hNSR hT hmax htu
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
    refine WP.spec_bind (dispatch_allRI s2 a1 σb J' hnib n c hn
      (hK σb hBA _ _ _ _ _ _ s2 a1 J') hARI hA hnd hPP hmrt hmb hIP hNS hRest hmax htu) ?_
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
