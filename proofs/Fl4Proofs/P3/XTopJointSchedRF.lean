/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md sch4 (A)): **`schedule`
and `finish` at `J` with the arch switch up to the FPU**.
`jat_scheduleFRF`, `jat_scheduleSRF`, `jat_finishJF` supersede
XTopJointSchedR's `jat_scheduleFRF`, `jat_scheduleSRF`, `jat_finishJF` (same
proofs, same conclusions): their arch premise `ArchSwF` [P] is false
whenever the spec has an FPU owner (its `ArchKeeps` keeps the heap, but the
spec's `lazy_fpu_restore` saves the FPU image into the old owner's TCB);
here it is `ArchSwF` [P] (ScArchF: the heap up to TCBs' saved FPU image and
`tcbCurFpu`, registers kept), through ScScheduleF's `schedule_refinesWPF`.
The J side needs nothing new: JAtZ reads no spec FPU field and the spec
facts after `schedule` come from `schedule σ1 = {σ'}` (`schs_schedule`'s
`SchStep` already tolerates FPU changes).

Premise `hFO : FpuOwnOK σ` [J] at the ENTRY state only (l4v X64
`valid_cur_fpu`, a reachable-state invariant; ScArchF's `FpuOwnOK`): what
`ArchSwF` needs at the switch state is derived from it by `fpuOwnOK_fires`
(sch5 (A): the timers' signals keep the owner, ScFpuOwnK's `owF_fires`, and
the J relation keeps the related TCBs; sch4 had `∀ σ1, Fires σ σ1 →
FpuOwnOK σ1` [S] here).
-/
import Fl4Proofs.P3.XTopJointSchedR
import Fl4Proofs.P3.ScScheduleF
import Fl4Proofs.P3.ScFpuOwnK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`FpuOwnOK` [J] after FL4's TCB timers from `FpuOwnOK` at the entry**
(sch5 (A)): the timers keep the owner (`owF_fires`); the owner is a spec TCB at
entry, hence a related TCB (`JAtZ.obj`, ObjCover), and every related TCB is a
spec TCB after the timers (`NtfnStateRel.tcb`). -/
theorem fpuOwnOK_fires {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ σ1 : Fl4Spec.State Unit} {m : U64 → U64}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hF : Fires σ σ1) (hN : NtfnStateRel Z.N Z.T m σ1)
    (hfo : FpuOwnOK σ) : FpuOwnOK σ1 := by
  intro o ho
  rw [owF_fires hF] at ho
  obtain ⟨x, hx⟩ := hfo o ho
  obtain ⟨t, ht, rfl⟩ := J.obj.tcb o x hx
  obtain ⟨y, hy, -⟩ := hN.tcb t ht
  exact ⟨y, hy⟩


set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` refines the spec's at `J`** (KENTRY-PLAN.md M7):
`jat_scheduleF`'s proof with the spec outcome kept: some `Fires σ σ1`, then
`Fl4Spec.schedule σ1 = {((), σ')}`, with `RJ`, `JAtZ`, `CurInv` and
`CurRunW` at `σ'`. -/
theorem jat_scheduleFRF {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hSig : SignalJHyp (L := L) arI AR H Cs)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ := by
  have h0Cs : 0#u64 ∈ Cs := J.kern.cs0
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  have hB := J.blk
  obtain ⟨⟨Q, R, hq⟩, hBd, hXi, hSc, hSg⟩ := id hB
  have hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn := fun _ h => h
  have hal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    P1.nodeAt_aligned (hq.nodes 0#u64 h0Cs) (by simp) (by simp)
  have hfire2 : timer.fire st arI s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st Z.N Z.T Z.C Z.c r.1 σ1 ∧
      NtfnStateRel Z.N Z.T (L.mem r.1) σ1 ∧ NSC Z.N Z.C σ1 ∧ SchedPreW Z.T Z.C σ1 ∧
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 r.1 r.2 σ1) ∧
        timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s ∧ FpuOwnOK σ1) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and (J.fireJ hSig) (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    have hd1' : σ1.domainTime ≠ 0 := by rw [hd1]; exact hd
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, J1.schedPreW hd1',
      ⟨V1, Ac1, Lst1, D1, J1⟩, hf, hk.1, fpuOwnOK_fires J h1 J1.xtop.fin.1.1.2.2.1 hFO⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_refinesWPF s a σ hS hR J.nsc hnd hfire2 (fun _ _ h => h.2.2.2) hA hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf, -⟩, hw, hrun⟩,
    hkw⟩, ⟨htinv, hRest⟩⟩
  simp only [WP.uncurry'_pair] at hkw htinv
  obtain ⟨rf', hrf', -, hkw⟩ := hkw
  obtain rfl : rf = rf' := by simpa using (hrf'.symm.trans hfr).symm
  have hTl := hRest rf σ1 σ' D1 hF hsc hw hS' hI' hC' hA'
  obtain ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', -, -, -, -⟩ := htinv
  have hks' : L.ksb s' = L.ksb s := hkw.1.trans hkf
  have hnA : L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS = L.nodeAt s 0#u64 layout.node.DEBUG_TCBS :=
    P1.nodeAt_of_ksb hkf _ _
  have hdbg : L.mem s' (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) =
      L.mem rf.1 (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS) := by
    exact hkw.mem_eq (by rw [hnA]; exact hal) (P1.dbg0_not_schedW J1.blk h0Cs)
  have hdw : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val ≠ (P1.stA (L.curW s')).val := by
    have hN0 := hq'.nodes 0#u64 h0Cs
    have hct : L.curW s' ∈ P1.Heap.tcbs H := hq'.curT
    have hv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp)
    have hsv := P1.field_val (hq'.tcbs _ hct) (K := 3328#u64) (by decide)
    have hdj := hN0.disj _ hct
    have hv' : (L.nodeAt rf.1 0#u64 layout.node.DEBUG_TCBS).val = L.nodeBase s' 0#u64 + 88 := by
      rw [hnA, ← P1.nodeAt_of_ksb hks' 0#u64 layout.node.DEBUG_TCBS, hv, P1.debug_val]
    have hsv' : (P1.stA (L.curW s')).val = (L.curW s').val + 3328 := by
      rw [P1.stA_eq, hsv]; rfl
    rw [hv', hsv']
    have e12 : (2 : Nat) ^ 12 = 4096 := rfl
    rw [e12] at hdj
    omega
  obtain ⟨σ3, ho3, hr3, he3⟩ := hrun
  have hK1 : SchStep (fun _ => False) σ1 σ' := (schs_schedule.of_eq hsc).1
  have hL1 : LK (fun _ => False) σ1 σ' := lkm_schedule σ1 ((), σ') (by rw [hsc]; exact Set.mem_singleton _)
  have hwT := WritesIn.tfoot_of_kfoot hw
  have hSS : SlotsSame Z.th (L.mem rf.1) (L.mem s') :=
    slotsSame_of_iw J1.xtop.rel.1 J1.xtop.rel.2.2.2.2.2.1 J1.xtop.rel.2.2.2.2.2.2 hwT
      fun b hb => tfoot_iw J1.xtop.fin.1.1.1 hb
  obtain ⟨Qc, Rc, hcc, hsc'⟩ := hS'.lists
  obtain ⟨hth, hvt⟩ := hVt _ _ _ _ _ _ _ J1 _ hcc.curT
  have hcur : Vs.CurOK st Z.th s' σ' :=
    ⟨_, hsc'.curThread.symm, hth, fun p asid h => hvt p asid (by
      rwa [hSS.capAt ⟨_, 1, Or.inr ⟨hth, by decide⟩, rfl⟩] at h)⟩
  have hX' : XTopAt (L := L) AR (Z.mv Z.G V1) s' a' σ' :=
    xtop_sched_step J1.xtop J1.ip J1.nk hwT (ct := σ1.curThread)
      { hK1 with kh := fun p => (hK1.kh p).mono False.elim } hS' hR' hcur hTl.ar
  have hSOK1 := (schs_schedule.of_eq hsc).2
  have hY1 : YieldRel Z.T Z.C (L.mem s') σ' :=
    (ScAll.of_k J1.xtop.fin.1.1.1 J1.rp J1.yld J1.mcp J1.call J1.rfree ⟨⟨hS', hR', hN', hI'⟩, hw, hSOK1⟩).2.1
  have hdead : ∀ q ∈ D1, Sched.DeadP (L := L) H s' q := fun q hq =>
    J1.deadP_sch_step hX' hwT hK1 hL1 hA' (J1.ymd hS' hY1 ((hSOK1.ykeep rfl).dk q.bv)) (fun h => h)
      (J1.jcov.dead q hq)
  have hT2 : SchTailHyps (L := L) AR (Z.mv Z.G V1) H Cs D1 rf.1 s' a' σ' Ac :=
    ⟨hcur, hTl.ar, hdbg, hdw, hdead,
      ⟨⟨Q', R', hq'⟩, hBd', hXi', hSc', hSg.ksb' hks'⟩, P1.dbgKeep_schedW J1.blk J1.kern.ksbFit hkw⟩
  obtain ⟨Lst', J'⟩ := J1.sch_tail hsc hw hS' hR' hN' hI' hC' hA' (RunW.scAndTimer (hr3 J1.curRun) he3)
    (OffOK.scAndTimer ho3 he3) (bsa_schedule J1.bsa hsc) hT2
  exact ⟨σ1, σ', hF, hsc, ⟨J'.xtop.relTop, _, _, _, _, _, _, J'⟩, ⟨V1, Ac, Lst', D1, J'⟩, hC',
    RunW.scAndTimer (hr3 J1.curRun) he3⟩


/-- **`jat_scheduleFRF` with `SignalJHyp` reduced to the waking signals**
(`signalJHyp_of`, as `jat_scheduleS`). -/
theorem jat_scheduleSRF {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄) :
    sched.schedule st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), Fires σ σ1 ∧
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
      (∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ') ∧ CurInv σ' ∧ CurRunW σ' ⦄ :=
  jat_scheduleFRF s a σ J hd hnd hAT hVt (signalJHyp_of hAT hW hmb) hA hFO hsni hsend hT hTail


set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` (`schedule`, then `activate_thread`) at `J`**, against
the Ext entry's tail `fl4Awaken >>= schedule >>= activateThread` (Ext/Entry's
`fl4CallKernel` after the event): an outcome `σ1` of `fl4Awaken` (FL4's TCB
timers, Ext/Timer) from which the spec's `schedule >>= activateThread` has
the one outcome `σ'`, hence `σ'` an outcome of the whole tail; `RJ` and
`JAtZ` at `σ'` (`jat_scheduleSRF`, then `JAtZ.activateJ` from its
`CurRunW`). Premises: `jat_scheduleSRF`'s, the platform's
`ticks_to_us`/`getMaxTicksToUs` [P] at every arch state, and `hvm` [S]
(scope, not an invariant gap): the current thread of a `JAt` state is not
`RunningVM` (VT-x is outside the native scope: IpcLeaves' `NativeScope`,
DESIGN §9; the ported `activateThread` has no `RunningVM` branch, seL4's C
one has; Fl4Spec is not changed, lead decision D2). -/
theorem jat_finishJF {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSwF st arI Z.N Z.T Z.C Z.c) (hFO : FpuOwnOK σ)
    (hsni : SniHyp st arI Z.N Z.T Z.C Z.c) (hsend : SendHyp st arI Z.N Z.T Z.C Z.c) (hT : TimeAgree arI)
    (hTail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFoot st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hvm : ∀ s1 a1 σ1, JAt (L := L) arI AR s1 a1 σ1 → ∀ x, σ1.kheap σ1.curThread = some (.tcb x) →
      x.tcbState ≠ .runningVM) :
    syscall.finish st arI s a ⦃ r => ∃ (σ1 σ' : Fl4Spec.State Unit), ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 ∧
      (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) ∧
      ((), σ') ∈ ((Fl4Spec.fl4Awaken (Z := Unit) >>= fun _ => Fl4Spec.schedule >>= fun _ => Fl4Spec.activateThread) σ).1 ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  unfold syscall.finish
  refine WP.spec_bind (jat_scheduleSRF s a σ J hd hnd hAT hVt hW hmb hA hFO hsni hsend hT hTail) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, hsc, -, ⟨V1, Ac1, Lst1, D1, J1⟩, -, hcr⟩
  refine WP.spec_mono (J1.activateJ hAT hmax (htu a1) hcr (hvm _ _ _ ⟨_, _, _, _, _, _, J1⟩)) ?_
  rintro r ⟨σ', ha, hRJ, V2, Ac2, Lst2, D2, J2⟩
  have hsa : (Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1 = ({((), σ')}, False) := by
    rw [Notif.nd_bind_one hsc]; exact ha
  refine ⟨σ1, σ', mem_fl4Awaken_of hF, hsa, ⟨((), σ1), mem_fl4Awaken_of hF, ?_⟩, hRJ, V2, Ac2, Lst2, D2, J2⟩
  show ((), σ') ∈ ((Fl4Spec.schedule (Z := Unit) >>= fun _ => Fl4Spec.activateThread) σ1).1
  rw [hsa]; exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
