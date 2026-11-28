/-
P3 (DESIGN.md §9), invariant line G4 (g5f, KENTRY-PLAN g5f): **one induction
for every carried spec invariant**, `JReachU` / `jreach_invU` /
`kernel_entry_reachU`, whose invariant is
`JAtZ ∧ SInvX ∧ SInvW ∧ SInvIP (SpecIoP, IoNoOverlap, SpecUtZ) ∧ MR ∧ FlagsRel`.

Before g5f the carries lived in three inductions: `JReachE4` (g4i: every event
entry, `SInvX ∧ MR`), `JReachIP` (g5c / g5d: native syscalls only, with
`SInvIP`, `FlagsRel`), and the readiness line's `SInvW` (inside `SInvX`, the
first conjunct, `SInvX.w`; rd14h's `kentry_rdyOff9` / `kcall_rdyOff9`). m69's
`kernel_entryJ34FW` reads `SInvW` at the entry, so it is a projection here.

* **The syscall top `kernel_entryJ42`** combines the best current syscall
  routes in one statement:
  - the MD line's dispatch (g4j / g4k, `kernel_entryJ41V`): `hDL : JDecMRLK
    VtxK` [W] at the dispatch states in place of `JDispMRI` [W];
  - the no-fail post (g4c / g4e): `kernel_entryJ13PUGMD4S` is
    `kernel_entryJ13PUGMD4` (same body) with the post `KPostMS`; as g4c found,
    the spec-fails disjunct came only from `kPreFinAtGM`, whose `…S` form
    `kPreFinAtGMS` never produces it;
  - the E line's dispatch bundle (g5a / g5b / g5d): `KDispHypsKV42` =
    `KDispHypsKV36E` without `JVtxHypMU` (= `KDispHypsKV41` with g5b's
    reductions), converted at the dispatch state by `KDispHypsKV42.to41`
    (`FlagsRel` by `JAtZ.flagsRel` there, `SInvIR` / `valid_irq_handlers` by
    `sinvIR_disp` / `vih_disp`, `LargeFrOK` carried from the entry by
    `front_slotsSame`), then `KDispHypsKV41.to35` with `hDL`;
  - the ReplyRecv route of m66 / m69 (`kernel_entryJ34FW`): `FastAcc.of_rrpre`
    with `JAtZ.rrPreAt`, whose `hRV` is `SInvW.rv` of the carried `SInvW`, so
    only m67's `hRP5 : RRPreAt5` [J] is asked (no `FastRR` [P]);
  - the post: an outcome with `RJ`, `MR`, `SInvX` and `SpecIoP ∧ IoNoOverlap`
    (`kentry_ioi`).
* **`JReachU`**: `start` (any `JAtZ ∧ SInvX ∧ SInvIP ∧ MR` state) and the
  steps of `JReachE4` (native syscall, interrupt from any thread, user
  exception, VM fault, `int $N`, unknown syscall), each also asking
  **`SpecUtZ σ'`** of its exit (the one open carry: l4v
  `untyped_ranges_zero`, KENTRY-PLAN g5c (3) / g5d (4), size L).
  `JReachU.toE4`; `JReachU.sinv` (`SInvIP` by `kentry_ioi` / `kcall_ioi`,
  across the FaultIP write by `ioi_fip`); **`jreach_invU`**.
* **`kernel_entry_reachU`**: at every `JReachU` state, at the ghosts the
  invariant gives, the native syscall (`kernel_entryJ42`) and every event
  entry (g4i's `jEvRef_*`) end in a related outcome with `SInvX`, `MR`,
  `SpecIoP`, `IoNoOverlap`, reachable again once `SpecUtZ` holds there.
-/
import Fl4Proofs.P3.XTopJointKEntryEv7
import Fl4Proofs.P3.XTopJointKEntry41V
import Fl4Proofs.P3.XTopJointKEntry38E
import Fl4Proofs.P3.XTopJointKEntryRRF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

/-- **`IOI` across the FaultIP write** (it writes one TCB register: the caps
and the allocated ports are kept). -/
theorem ioi_fip (t : ObjRef) : IKH IOI (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_ioi (fun _ => SInvV.hv_fl4SyscallFaultIP t) (fun _ => iok_fl4SyscallFaultIP t)

end Fl4Proofs.P3.SInvIo

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- **`SpecIoP ∧ IoNoOverlap` at every event outcome** (`kcall_ioi`; across
the FaultIP write by `ioi_fip`). -/
theorem ioi_evOut {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit}
    (h : SpecIoP σ ∧ SInvIo.IoNoOverlap σ) (hO : EvOut fip ev σ σ') : SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' := by
  cases fip with
  | false => exact SInvIo.kcall_ioi h _ hO
  | true =>
    obtain ⟨w, hw, hy⟩ := hO
    exact SInvIo.kcall_ioi (SInvIo.ioi_iff.1 (SInvIo.ioi_fip _ σ (SInvIo.ioi_iff.2 h) w hw)) _ hy

/-! ## `kernel_entryJ13PUGMD4` without the spec-fails disjunct -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 16000000 in
/-- **`kernel_entryJ13PUGMD4` with the post `KPostMS`** (module docstring;
the same body, the preemption branch by `kPreFinAtGMS`). -/
theorem kernel_entryJ13PUGMD4S [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ)
    (hR : MR a σ.machineState) (hVI : ValidIrqMasks σ) (hNS0 : NativeScope σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudgetB arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHyps13PU (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
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
          JAtZ (L := L) arI AR Z' H Cs Ac' Lst' D' r.2.1 r.2.2 z.2 ∧ VxE Z') ⦄ := by
    exact JAtZ.budgetOkB (σ0 := faultIPSt σ σ.curThread x) J0 hni0 hBu (SInv.ns_fl4SyscallFaultIP σ.curThread σ hNS0 _ hF) hAK hA
      hnd hmrt hmb hmax htu
  refine WP.spec_bind (WP.spec_and (spec_and_eq hBud fun _ h => h) (budget_ok_mr hM hMK hA hR _)) ?_
  rintro ⟨b, s2, a1⟩ ⟨⟨⟨hTr, hFa⟩, hbeq⟩, hMRb⟩
  cases b
  · -- the budget check stops the system call
    obtain ⟨z, hz, hz1, Z', Ac', Lst', D', J', _⟩ := hFa rfl
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
    refine WP.spec_bind (spec_and_eq (dispatch_all13PUNM4 s2 a1 σb J' hnib n c hn
      (hK σb hBA V0 _ _ _ s2 a1 hfr J') (hDL σb hBA V0 _ _ _ s2 a1 hfr J') hMRσb hVIσb hNSb hARI hA hnd hM hKD hIo hIoa hPA hIA
      hmrt hmax htu)
      fun _ h => h) ?_
    rintro ⟨s3, a2⟩ ⟨hDMp, hdeq⟩
    obtain ⟨y, hy, ⟨hy1, hR, hJ, hMy⟩ | ⟨hy1, hQ⟩⟩ := hDMp
    · obtain ⟨Zm, Hm, Csm, Acm, Lstm, Dm, JmR, _⟩ := hJ
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

/-! ## The dispatch bundle: `KDispHypsKV36E` without `JVtxHypMU` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KDispHypsKV41` with g5b's reductions** (= `KDispHypsKV36E` without
`JVtxHypMU`, which `hDL` gives at the same state): `JEntryAtR6` (the three
[P] fields and `vsTyp` [J]) and `JPathAtM36E` (no Frame `hno`). -/
structure KDispHypsKV42 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets)
    (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtM36E (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryAtR6 (L := L) arI AR Z s a σ ∧
    JPathAtM36E (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg))

variable {arI}

/-- `KDispHypsKV42` to `KDispHypsKV41` at a `JAtZ` state (`FlagsRel` from the
state's `JAtZ`, `valid_irq_handlers`, `SInvIR`, `LargeFrOK`). -/
theorem KDispHypsKV42.to41 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : SInvV.ValidIrqHandlers σ) (hI : SInvIR σ)
    (hLF : LargeFrOK Z.G (L.mem s)) (h : KDispHypsKV42 (L := L) arI AR Z H Cs D s a σ n c) :
    KDispHypsKV41 (L := L) arI AR Z H Cs D s a σ n c :=
  ⟨fun ct call bl don hct hi => let ⟨e, p⟩ := h.inv ct call bl don hct hi;
      ⟨(e.toR5 J.flagsRel).toR3V J hV hI, (p.to35E J.xtop.rel.2.1.2.2.1 hLF).to35 J⟩,
    fun ct rg sr cr hct hm => let ⟨e, p⟩ := h.mid ct rg sr cr hct hm;
      ⟨(e.toR5 J.flagsRel).toR3V J hV hI, (p.to35E J.xtop.rel.2.1.2.2.1 hLF).to35 J⟩⟩

end

/-! ## The syscall top -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The post of `kernel_entryJ42`**: an outcome of the spec entry (no
spec-fails disjunct) related by `RJ`, with `MR`, `SInvX`, `SpecIoP` and
`IoNoOverlap`. -/
def KPostU (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (c : Fl4Spec.Syscall)
    (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
    MR r.2 σ'.machineState ∧ SInvX σ' ∧ SpecIoP σ' ∧ SInvIo.IoNoOverlap σ'

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **The unified syscall top** (module docstring). Premises: `J` (carried),
`hct` [S], `hR` (`MR`, carried), `hX : SInvX σ` (carried; `SInvW` = `hX.w`),
`hI : SInvIP σ` (carried), `hLF : LargeFrOK` [J] FL4 at the entry, `hn` [S],
`hflag` [S], `hK : KDispHypsKV42` and `hDL : JDecMRLKQ VtxK` [W] at the
dispatch states, `hFin : KFinAtR31` at the front outcomes, the [P] bundle,
`hRP5 : RRPreAt5` [J] (m67's `nvm`, ReplyRecv only).
`hSX : StoreExt` [P]: the fast path's BLOCK_OBJ / STATE write order (`P1.rr_same`). -/
theorem kernel_entryJ42 [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ) (hI : SInvIP σ) (hLF : LargeFrOK Z.G (L.mem s))
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV42 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDL : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        ∀ ct', sched.cur_thread st s' = ok ct' → JDecMRLKQ (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct')
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st)
    (hRP5 : n = fl4_abi.syscall.SysReplyRecv → P1.RRPreAt5 (L := L) arI s a) :
    syscall.handle_syscall st arI s a n ⦃ r => KPostU (L := L) arI AR MR c σ r ⦄ := by
  have hni := hX.entered hct
  have hS := hX.sb
  have hE := hX.epQAll
  have hQ := hX.ctQ
  have hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → OffReady (faultIPSt σ σ.curThread x) :=
    fun _ _ => offReady_faultIPSt hX.offReady
  have hC : CurInv σ := J.cur.resolve_left (by rw [hni.2]; intro e; cases e)
  obtain ⟨x0, hk0, -⟩ := hS.1.2
  have hK35 : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c :=
    fun σb hBA V' Ac' Lst' D' s' a' hF J' =>
      ((hK σb hBA V' Ac' Lst' D' s' a' hF J').to41 J' (vih_disp hnd hk0 hBA hS.1.1.vih)
        (sinvIR_disp hnd hk0 hBA hI.toIR)
        (hLF.of_same (fun y hy => ((J.xtop.rel.2.1.2.2.1.members y).1 hy).1)
          (front_slotsSame J hARI.toARKeep hA hF))).to35 (hDL σb hBA V' Ac' Lst' D' s' a' hF J')
  have hG : syscall.handle_syscall_old st arI s a n ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄ :=
    kernel_entryJ13PUGMD4S s a σ J hni hR hS.1.1.vim hS.1.1.ns n c hn hflag
      (fun x hk => ⟨hM.nowAgree hR hS.1.1.vmt, curInv_faultIPSt hk hC, hB x hk, Or.inr hQ⟩)
      (fun σb hBA V' Ac' Lst' D' s' a' hfr J' =>
        ((((((((hK35 σb hBA V' Ac' Lst' D' s' a' hfr J').to33 J'
          (jEntryGlobM32_of _ hARI hA hnd hPA hT hmax htu hRef hPI)).to32
          (liveDN_front hnd J J.live hS hARI.toARKeep hA hfr hBA)).to31).to27b.to27 hnd hS hni hE hBA).to26
          hnd hS hni hQ hB hBA).to25 hA hmax htu hmb J' (hBA.enteredP hnd hni)).to23 hA hmax htu).to13PU J' hBA
          hA hnd hM hKD hmax htu)
      hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hfr J').to27.toR
          (fun o e => SInvAll.sinvB_front_fo true c hS hct x hx o e))
      hARI hA hnd hM hKD hIo hIoa hPA hIA hmrt hmb hT hmax htu
  have hP : syscall.handle_syscall st arI s a n ⦃ r => KPostMS (L := L) arI AR MR c σ r ⦄ := by
    by_cases hrr : n = fl4_abi.syscall.SysReplyRecv
    · exact P1.FastAgree.spec st arI (P1.FastAgree.of_acc st arI P1.LawfulStore.total hA
        (FastAcc.of_rrpre hSX hflag hn.range hrr (J.rrPreAt hni hR hS hQ hB hARI hA hnd hM hmrt hmb hmax htu
          (Fl4Proofs.P3.SInvW.rv hX.w) (hRP5 hrr)))) hG
    · rw [handle_syscall_eq_general_of hflag hn.range hrr, P1.handle_syscall_general_eq]; exact hG
  refine WP.spec_mono hP ?_
  rintro r ⟨σ', hy, hRJ, hM'⟩
  obtain ⟨h1, h2⟩ := SInvIo.kentry_ioi ⟨hI.ioP, hI.ioN⟩ _ hy
  exact ⟨σ', hy, hRJ, hM', kentry_sinvX hnd c hX hct _ hy, h1, h2⟩

end

/-! ## The unified induction -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states, every carried invariant in one induction**
(module docstring): `JReachE4`'s steps, each asking `SpecUtZ` of its exit. -/
inductive JReachU : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → SInvIP σ → MR a σ.machineState → JReachU s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachU s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachU s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachU s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachU s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachU s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' →
      JReachU s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachU s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachU s' a' σ'
  | trap {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (v : U64)
      (ev : Fl4Spec.Event) :
      JReachU s a σ → σ.curThread ≠ σ.idleThread → v.val < 256 → KEvSpec (.trap v) true ev →
      syscall.handle_trap_syscall st arI s a v = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachU s' a' σ'
  | sysU {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (ev : Fl4Spec.Event) :
      JReachU s a σ → σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      KEvSpec (.sysU n) true ev → syscall.handle_syscall st arI s a n = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → SpecUtZ σ' → JReachU s' a' σ'

variable {arI AR MR}

/-- Every `JReachU` state is a `JReachE4` state (forget `SpecUtZ`). -/
theorem JReachU.toE4 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachU (L := L) arI AR MR s a σ) :
    JReachE4 (L := L) arI AR MR s a σ := by
  induction h with
  | start J hvx hX _ hR => exact JReachE4.start J hvx hX hR
  | step n c _ hct hn hv hy hRJ _ ih => exact JReachE4.step n c ih hct hn hv hy hRJ
  | irq w _ hI hv hO hRJ _ ih => exact JReachE4.irq w ih hI hv hO hRJ
  | user n c _ hct hU hv hO hRJ _ ih => exact JReachE4.user n c ih hct hU hv hO hRJ
  | vmf ad c ft _ hct hV hv hO hRJ _ ih => exact JReachE4.vmf ad c ft ih hct hV hv hO hRJ
  | trap v ev _ hct hv8 hK hv hO hRJ _ ih => exact JReachE4.trap v ev ih hct hv8 hK hv hO hRJ
  | sysU n ev _ hct hU hD hK hv hO hRJ _ ih => exact JReachE4.sysU n ev ih hct hU hD hK hv hO hRJ

/-- `SInvIP` at every `JReachU` state: `SpecIoP ∧ IoNoOverlap` by
`kentry_ioi` / `ioi_evOut` along every step, `SpecUtZ` from the step. -/
theorem JReachU.sinv {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachU (L := L) arI AR MR s a σ) :
    SInvIP σ := by
  induction h with
  | start _ _ _ hI _ => exact hI
  | step n c _ _ _ _ hy _ hU ih =>
    obtain ⟨h1, h2⟩ := SInvIo.kentry_ioi ⟨ih.ioP, ih.ioN⟩ _ hy
    exact ⟨h1, h2, hU⟩
  | irq w _ _ _ hO _ hU ih => obtain ⟨h1, h2⟩ := ioi_evOut ⟨ih.ioP, ih.ioN⟩ hO; exact ⟨h1, h2, hU⟩
  | user n c _ _ _ _ hO _ hU ih => obtain ⟨h1, h2⟩ := ioi_evOut ⟨ih.ioP, ih.ioN⟩ hO; exact ⟨h1, h2, hU⟩
  | vmf ad c ft _ _ _ _ hO _ hU ih => obtain ⟨h1, h2⟩ := ioi_evOut ⟨ih.ioP, ih.ioN⟩ hO; exact ⟨h1, h2, hU⟩
  | trap v ev _ _ _ _ _ hO _ hU ih => obtain ⟨h1, h2⟩ := ioi_evOut ⟨ih.ioP, ih.ioN⟩ hO; exact ⟨h1, h2, hU⟩
  | sysU n ev _ _ _ _ _ _ hO _ hU ih => obtain ⟨h1, h2⟩ := ioi_evOut ⟨ih.ioP, ih.ioN⟩ hO; exact ⟨h1, h2, hU⟩

/-- **The unified invariant**: every `JReachU` state carries, at some ghosts,
`JAtZ ∧ SInvX ∧ SInvW ∧ SInvIP ∧ IoNoOverlap ∧ MR ∧ FlagsRel`. -/
theorem jreach_invU (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachU (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ VxE Z := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J, hvx⟩, hX, hR⟩ := jreach_invE4 hnd h.toE4
  have hI := h.sinv
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hX.w, hI, hI.ioN, hR, J.flagsRel, hvx⟩

end

end

end Fl4Proofs.P3.SInvR.G5
