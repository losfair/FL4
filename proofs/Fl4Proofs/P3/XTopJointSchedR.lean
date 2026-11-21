/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN.md M7, M5; item 11): **`schedule`
and `activate_thread` at `J` against the spec's outcomes**.

* `jat_scheduleFR`: ScFireJ's `jat_scheduleF` (same premises, same proof)
  with the spec's outcome in the conclusion: FL4's `sched.schedule` from
  `JAtZ` ends, for some `σ1 σ'`, in `Fires σ σ1` (FL4's TCB timers, l4h 0003,
  M8), `Fl4Spec.schedule σ1 = {((), σ')}` (no failure), `RJ` at `σ'`, `JAtZ`
  at `σ'` (fresh VSpace sets), `CurInv σ'` and `CurRunW σ'` (the current
  thread runnable or the idle thread: what `activateThread` reads).
  `jat_scheduleSR`: the same with `SignalJHyp` reduced (`signalJHyp_of`).
  `hd` (domain time nonzero, a `jat_scheduleF` premise kept): FALSE right
  after DomainScheduleSetStart (spec `domainSetStart`: `domainTime := 0`,
  then `schedule`'s `nextDomain` branch, not proved at `schedule_refinesWP`);
  see KENTRY-PLAN.md sch1.
* `JAtZ.activateJ` (M5): FL4's `activate_thread` refines `activateThread`
  at `J` from `CurRunW` (`jat_scheduleFR`'s post): the yield completion
  (`JAtZ.completeYieldJa`, `completeYieldTo_sframe` keeps every state),
  then `JAtZ.actRestJ` (`Restart`: next IP := fault IP, `JAtZ.regWrJ`,
  then `Running`, `JAtZ.runJ`; `Running`/idle: nothing). The spec's failing
  branch is unreachable from `CurRunW` but for `RunningVM` ([S] `hvm`,
  native scope; the ported `activateThread` lacks seL4 C's `RunningVM`
  case).
* `jat_finishJ`: FL4's `syscall::finish` against the Ext entry's tail
  `fl4Awaken >>= schedule >>= activateThread` (Ext/Timer, Ext/Entry's
  `fl4CallKernel`, KENTRY-PLAN.md D1): one `fl4Awaken` outcome `σ1`
  (`Fires σ σ1`, `fires_iff`) from which `schedule >>= activateThread` has
  the one outcome `σ'`, so `σ'` is an outcome of the whole tail.
-/
import Fl4Proofs.P3.ScSignalJ
import Fl4Proofs.P3.XTopJointDispatch
import Fl4Proofs.P3.XTopJointYield
import Fl4Proofs.P3.XTopJointReply
import Fl4Proofs.P3.ScJointYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}


set_option maxHeartbeats 4000000 in
/-- **FL4's `schedule` refines the spec's at `J`** (KENTRY-PLAN.md M7):
`jat_scheduleF`'s proof with the spec outcome kept: some `Fires σ σ1`, then
`Fl4Spec.schedule σ1 = {((), σ')}`, with `RJ`, `JAtZ`, `CurInv` and
`CurRunW` at `σ'`. -/
theorem jat_scheduleFR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hSig : SignalJHyp (L := L) arI AR H Cs)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
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
        timer.fire st arI s a = ok r ∧ L.ksb r.1 = L.ksb s) ⦄ := by
    refine WP.spec_mono (P1.spec_eq' (WP.spec_and (J.fireJ hSig) (P1.timer.fire.kw hAT hNt s a hB))) ?_
    rintro ⟨s1, a1⟩ ⟨hf, ⟨σ1, V1, Ac1, Lst1, D1, h1, hd1, J1⟩, hk⟩
    simp only [WP.uncurry'_pair] at hk
    have hd1' : σ1.domainTime ≠ 0 := by rw [hd1]; exact hd
    exact ⟨σ1, h1, J1.xtop.fin.1.1.1, J1.xtop.fin.1.1.2.2.1, J1.nsc, J1.schedPreW hd1',
      ⟨V1, Ac1, Lst1, D1, J1⟩, hf, hk.1⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_refinesWP s a σ hS hR J.nsc hnd hfire2 hA hsni hsend hT)
    (P1.sched.schedule.kw hAT hNt s a hB)) (WP.spec_and (P1.sched.schedule.tinv hAT hNt s a Q R hq hBd hSc hXi hSg)
      hTail)) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨σ1, σ', hF, hsc, hS', hR', hN', hI', hC', hA', rf, ⟨⟨V1, Ac1, Lst1, D1, J1⟩, hfr, hkf⟩, hw, hrun⟩,
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


/-- **`jat_scheduleFR` with `SignalJHyp` reduced to the waking signals**
(`signalJHyp_of`, as `jat_scheduleS`). -/
theorem jat_scheduleSR {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
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
  jat_scheduleFR s a σ J hd hnd hAT hVt (signalJHyp_of hAT hW hmb) hA hsni hsend hT hTail

end

/-! ## `activate_thread` at `J` (M5) -/

section Spec
open Fl4Spec

/-- The spec's `activateThread` after the yield completion: the state
dispatch (`running` nothing, `restart` the restart PC, idle nothing, any
other state `fail`). -/
def actRest (t : ObjRef) : SMonad Unit Unit := do
  let state ← getThreadState t
  match state with
  | .running => return ()
  | .restart => do
      let pc ← asUser t getRestartPC
      asUser t <| setNextPC pc
      setThreadState t .running
  | .idleThreadState => archActivateIdleThread t
  | _ => NonDet.fail

theorem activateThread_eq {σ : State Unit} {x : Tcb} (hk : σ.kheap σ.curThread = some (.tcb x)) :
    activateThread (Z := Unit) σ =
      ((NonDet.when (x.tcbYieldTo ≠ none) (completeYieldTo σ.curThread) : SMonad Unit Unit) >>= fun _ =>
        actRest σ.curThread) σ := by
  unfold activateThread
  show (NonDet.gets _ >>= _) σ = _
  rw [Notif.nd_bind_one (show NonDet.gets (fun s : State Unit => s.curThread) σ = ({(σ.curThread, σ)}, False) from rfl)]
  rw [Notif.nd_bind_one (Endp.getTcbObjRef_eq _ hk)]
  rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

theorem regIdx_nextIP : regIdx Fl4Spec.Register.nextIP = layout.reg.NEXT_IP := by
  unfold layout.reg.NEXT_IP; rfl

theorem regIdx_faultIP : regIdx Fl4Spec.Register.faultIP = layout.reg.FAULT_IP := by
  unfold layout.reg.FAULT_IP; rfl

set_option maxHeartbeats 16000000 in
/-- **`activate_thread`'s state dispatch at `J`** (after the yield): a
`Restart` current thread gets its fault IP as its next IP (`JAtZ.regWrJ`)
and runs (`JAtZ.runJ`); a `Running` or idle one is left alone. -/
theorem JAtZ.actRestJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hcr : CurRunW σ)
    (hvm : ∀ x, σ.kheap ct.bv = some (.tcb x) → x.tcbState ≠ .runningVM) :
    (do
      let st0 ← obj.Tcb.state st ct s
      if st0 = sched.TS_RESTART then
        let pc ← obj.Tcb.reg st ct s layout.reg.FAULT_IP
        let s2 ← obj.Tcb.set_reg st ct s layout.reg.NEXT_IP pc
        let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok (s3, a)
      else ok (s, a)) ⦃ r => ∃ σ', actRest ct.bv σ = ({((), σ')}, False) ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
        ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨x, hk, hTR⟩ := hI.1.tcb ct hct
  have hst : (L.mem s (tStA ct)).val = tsCode x.tcbState := hTR.st
  have hk' : σ.kheap σ.curThread = some (.tcb x) := by rw [hcur]; exact hk
  have hxs := hI.1.toE.at_tcb hct hk
  have hrun : x.tcbState = .running ∨ x.tcbState = .restart ∨ x.tcbState = .idleThreadState := by
    rcases hcr with h | h
    · have h1 := h x hk'
      have h2 := hvm x hk
      revert h1 h2
      generalize x.tcbState = ts
      cases ts <;> simp [Fl4Spec.runnable]
    · obtain ⟨xi, hki, -, hsi, -⟩ := J.act.2
      rw [← h, hk'] at hki; cases hki; exact Or.inr (Or.inr hsi)
  step with Notif.obj.Tcb.state.spec as ⟨v, hv⟩
  subst hv
  by_cases hrs : x.tcbState = .restart
  · have hv2 : L.mem s (tStA ct) = sched.TS_RESTART :=
      UScalar.eq_of_val_eq (by rw [hst, hrs]; unfold sched.TS_RESTART; rfl)
    rw [if_pos hv2]
    step with Endp.obj.Tcb.reg.spec as ⟨pc, hpc⟩
    step with Endp.obj.Tcb.set_reg.spec as ⟨s2, hs2⟩
    subst hs2
    have hX2 := reg_wr_irel J.ip hI hct hk Fl4Spec.Register.nextIP (by decide) pc
    rw [regIdx_nextIP] at hX2
    obtain ⟨V2, J2⟩ := J.regWrJ hct hk Fl4Spec.Register.nextIP pc (by rw [regIdx_nextIP]; exact hX2)
    rw [regIdx_nextIP] at J2
    have hk2 : (updK σ ct.bv (.tcb (setReg x Fl4Spec.Register.nextIP pc.bv))).kheap ct.bv =
        some (.tcb (setReg x Fl4Spec.Register.nextIP pc.bv)) := by simp [updK]
    refine WP.spec_bind (J2.runJ hct hk2 hrs) ?_
    rintro s3 ⟨Lst3, D3, J3⟩
    refine (WP.spec_ok _).2 ⟨_, ?_, J3.xtop.relTop, ⟨_, _, _, _, _, _, J3⟩, V2, Ac, Lst3, D3, J3⟩
    have hreg : x.tcbArch.tcbContext.userRegs .faultIP = pc.bv := by
      rw [← hxs.regs .faultIP, regIdx_faultIP, hpc]
    unfold actRest
    rw [Notif.nd_bind_one (getThreadState_eq hk), hrs]
    show (Fl4Spec.asUser ct.bv (Fl4Spec.getRegister .faultIP) >>= fun pc =>
      Fl4Spec.asUser ct.bv (Fl4Spec.setRegister .nextIP pc) >>= fun _ =>
      Fl4Spec.setThreadState ct.bv .running) σ = _
    rw [Notif.nd_bind_one (asUser_getRegister_eq hk .faultIP), hreg,
      Notif.nd_bind_one (asUser_setRegister_eq .nextIP pc.bv hk), setThreadState_eq' hk2]
  · have hv2 : L.mem s (tStA ct) ≠ sched.TS_RESTART := fun e =>
      hrs (Vs.tsCode_two (by rw [← hst, e]; unfold sched.TS_RESTART; rfl))
    rw [if_neg hv2]
    refine (WP.spec_ok _).2 ⟨σ, ?_, J.xtop.relTop, ⟨_, _, _, _, _, _, J⟩, Z.vs, Ac, Lst, D, J⟩
    unfold actRest
    rw [Notif.nd_bind_one (getThreadState_eq hk)]
    rcases hrun with e | e | e
    · rw [e]; rfl
    · exact absurd e hrs
    · rw [e]; rfl

set_option maxHeartbeats 16000000 in
/-- **FL4's `activate_thread` refines the spec's at `J`** (KENTRY-PLAN.md
M5): from `JAtZ` with the current thread runnable or idle (`CurRunW`, what
`jat_scheduleFR` gives after `schedule`), the yield completed when the
current thread yields (`JAtZ.completeYieldJa`, the spec's
`completeYieldTo`, which keeps every thread's state, `completeYieldTo_sframe`),
then the state dispatch (`JAtZ.actRestJ`). The spec's `activateThread` does
not fail: its failing branch is a current thread neither running, restarted
nor idle, excluded by `CurRunW` except `RunningVM` (`hvm`, below). Named:
`hvm` [S] (scope) the current thread is not `RunningVM` (VT-x, outside the native
scope, IpcLeaves' `NativeScope`, DESIGN §9; seL4's C `activateThread` treats
`ThreadState_RunningVM` as `Running` under `CONFIG_VTX`, the ported
`activateThread` has no such branch and fails), and the platform's
`ticks_to_us`/`getMaxTicksToUs` [P] (`hmax`, `htu`, as `completeYieldJ`). -/
theorem JAtZ.activateJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hcr : CurRunW σ) (hvm : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbState ≠ .runningVM) :
    sched.activate_thread st arI s a ⦃ r => ∃ σ', Fl4Spec.activateThread (Z := Unit) σ = ({((), σ')}, False) ∧
      RJ (L := L) arI AR r.1 r.2 σ' ∧ ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  unfold sched.activate_thread
  step with Sched.sched.cur_thread.spec' as ⟨ct, ect⟩
  have hct : sched.cur_thread st s = ok ct := by rw [ect]; exact cur_thread_eq s
  obtain ⟨hcur, -⟩ := J.curEq hct
  have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
  obtain ⟨xc, hkc, eyt⟩ := J.yld.tcb ct hctT
  have hkc' : σ.kheap σ.curThread = some (.tcb xc) := by rw [hcur]; exact hkc
  have hspec := activateThread_eq hkc'
  rw [hcur] at hspec
  step with P1.obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ σ1,
      (Fl4Spec.NonDet.when (xc.tcbYieldTo ≠ none) (Fl4Spec.completeYieldTo ct.bv) : Fl4Spec.SMonad Unit Unit) σ =
        ({((), σ1)}, False) ∧ σ1.curThread = ct.bv ∧ CurRunW σ1 ∧
      (∀ x, σ1.kheap ct.bv = some (.tcb x) → x.tcbState ≠ .runningVM) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ1) ?_ ?_
  · by_cases h0 : L.mem s (P1.yieldA ct) = 0#u64
    · have hb : (L.mem s (P1.yieldA ct) != 0#u64) = false := by simp [h0]
      simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hxn : xc.tcbYieldTo = none := by rw [eyt, h0, Notif.optRef_zero]
      refine ⟨σ, ?_, hcur, hcr, fun x hx => hvm x (by rw [hcur]; exact hx), Z.vs, Ac, Lst, D, J⟩
      rw [nd_when_false_y (by rw [hxn]; simp)]; rfl
    · have hb : (L.mem s (P1.yieldA ct) != 0#u64) = true := by simp [h0]
      simp only [hb, ↓reduceIte]
      have hyt : xc.tcbYieldTo = some (L.mem s (P1.yieldA ct)).bv := by rw [eyt, Notif.optRef_ne h0]
      obtain ⟨-, y, n, hky, -⟩ := J.yld.toSc ct hctT h0
      refine WP.spec_mono (J.completeYieldJa hAT hmax htu hctT) ?_
      rintro ⟨s1, a1⟩ ⟨-, σ1, hcy, V, Ac1, Lst1, D1, J1⟩
      obtain ⟨hsf, -, -⟩ := completeYieldTo_sframe hkc hyt hky hcy
      have hcur1 : σ1.curThread = ct.bv := hsf.cur.trans hcur
      obtain ⟨xc1, hkc1, hst1, -⟩ := hsf.tcb _ xc hkc
      refine ⟨σ1, ?_, hcur1, ?_, fun x hx => ?_, V, Ac1, Lst1, D1, J1⟩
      · unfold Fl4Spec.NonDet.when
        rw [if_pos (by rw [hyt]; simp)]
        exact hcy
      · rcases hcr with h | h
        · refine Or.inl fun x hx => ?_
          rw [hcur1, hkc1] at hx; cases hx
          rw [hst1]; exact h xc hkc'
        · exact Or.inr (by rw [hsf.cur, hsf.idle]; exact h)
      · rw [hkc1] at hx; cases hx
        rw [hst1]; exact hvm xc hkc'
  rintro ⟨s1, a1⟩ ⟨σ1, hw1, hcur1, hcr1, hvm1, V1, Ac1, Lst1, D1, J1⟩
  rw [Notif.nd_bind_one hw1] at hspec
  refine WP.spec_mono (J1.actRestJ hctT hcur1 hcr1 hvm1) ?_
  rintro r ⟨σ', he, hRJ, V2, Ac2, Lst2, D2, J2⟩
  exact ⟨σ', hspec.trans he, hRJ.1, hRJ.2, V2, Ac2, Lst2, D2, J2⟩

/-- P3's `Fires` (ScAwaken) is Ext/Timer's `fl4TimerFires` (the definitions
are the same; ScAwaken's is kept to avoid rebuilding its cone). -/
theorem fires_iff {σ σ1 : Fl4Spec.State Unit} : Fires σ σ1 ↔ Fl4Spec.fl4TimerFires σ σ1 := Iff.rfl

/-- `Fires` is an outcome of `fl4Awaken`. -/
theorem mem_fl4Awaken_of {σ σ1 : Fl4Spec.State Unit} (h : Fires σ σ1) :
    ((), σ1) ∈ (Fl4Spec.fl4Awaken (Z := Unit) σ).1 := Fl4Spec.mem_fl4Awaken.2 (fires_iff.1 h)

set_option maxHeartbeats 4000000 in
/-- **FL4's `finish` (`schedule`, then `activate_thread`) at `J`**, against
the Ext entry's tail `fl4Awaken >>= schedule >>= activateThread` (Ext/Entry's
`fl4CallKernel` after the event): an outcome `σ1` of `fl4Awaken` (FL4's TCB
timers, Ext/Timer) from which the spec's `schedule >>= activateThread` has
the one outcome `σ'`, hence `σ'` an outcome of the whole tail; `RJ` and
`JAtZ` at `σ'` (`jat_scheduleSR`, then `JAtZ.activateJ` from its
`CurRunW`). Premises: `jat_scheduleSR`'s, the platform's
`ticks_to_us`/`getMaxTicksToUs` [P] at every arch state, and `hvm` [S]
(scope, not an invariant gap): the current thread of a `JAt` state is not
`RunningVM` (VT-x is outside the native scope: IpcLeaves' `NativeScope`,
DESIGN §9; the ported `activateThread` has no `RunningVM` branch, seL4's C
one has; Fl4Spec is not changed, lead decision D2). -/
theorem jat_finishJ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hd : σ.domainTime ≠ 0) (hnd : Fl4Spec.numDomains = 1)
    (hAT : P0.ArchTotal arI)
    (hVt : ∀ (V1 : XVs) (s1 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (Ac1 : Set U64) (Lst1 : U64 → List U64)
      (D1 : Set U64), JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s1 a1 σ1 → ∀ t ∈ Z.T,
        Z.th t = some .tcb ∧ ∀ p asid, capAt (L.mem s1) (slotOf t 1) = ok (.Pml4 p true asid) → asid ≠ 0#u64)
    (hW : SignalRestJHyp (L := L) arI AR H Cs) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hA : ArchSw st arI Z.N Z.T Z.C Z.c)
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
  refine WP.spec_bind (jat_scheduleSR s a σ J hd hnd hAT hVt hW hmb hA hsni hsend hT hTail) ?_
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
