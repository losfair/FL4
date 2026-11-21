/-
P3 (DESIGN.md §9), scheduler (KENTRY-PLAN.md sch9 (1)): **`schedule` from
`CurInvR`** (XTopJointJAtZR): `SchedPreW0R` (ScNextDomC's `SchedPreW0` with
`cur : CurInvR`), `awaken_refinesW0R` (the spec's `awaken` never sets
`resumeCurThread`: `CurInv` after only where it was asked before), and
`schedule_refinesWP0FR` (ScNextDomCF's `schedule_refinesWP0F`, copied): the
resume branch takes `CurInv` from `CurInvR` at the resumed action; the
switch branch no longer reads the old current thread's `CurInv` (the new
current thread is the idle thread or schedulable at the switch state,
`newcur_of2F`, as in the choose branch). So a pending switch over a blocked
current thread (`SwBlk`) is covered.
-/
import Fl4Proofs.P3.ScNextDomCF
import Fl4Proofs.P3.XTopJointJAtZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

/-- `SchedPreW0` with `cur : CurInvR` (module docstring). -/
def SchedPreW0R (T C : Set U64) (σ : State Unit) : Prop :=
  Inv σ ∧ CurInvR σ ∧ OffOK σ ∧ ActIdle σ ∧ CurOwnW T C σ

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

theorem awaken_refinesW0R {A : Type} {ar : machine.Arch A} {N C : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW0R T C σ1 ∧ Pf r σ1 ⦄) :
    sched.awaken st ar s a ⦃ r => ∃ σ1 σ2, Fires σ σ1 ∧ Fl4Spec.awaken (Z := Unit) σ1 = ({((), σ2)}, False) ∧
      SchedRel st N T C c r.1 σ2 ∧ NtfnStateRel N T (L.mem r.1) σ2 ∧ NSC N C σ2 ∧ SchedPreW0R T C σ2 ∧ Calm σ1 σ2 ∧
      (σ1.schedulerAction = .chooseNewThread → σ2.schedulerAction = .chooseNewThread) ∧
      (σ1.schedulerAction ≠ .resumeCurThread → σ2.schedulerAction ≠ .resumeCurThread) ∧
      (∀ u ∈ σ2.releaseQueue, u ∈ σ1.releaseQueue) ∧
      ∃ rf : S × A, Pf rf σ1 ∧ r.2 = rf.2 ∧ WritesIn st rf.1 r.1 (SFoot st T c rf.1) ⦄ := by
  unfold sched.awaken
  refine WP.spec_bind hfire ?_
  rintro ⟨s1, a1⟩ ⟨σ1, hF, hS1, hR1, hN1, ⟨hI1, hC1, hO1, ⟨hA1, hId1⟩, hW1⟩, hPf⟩
  refine WP.spec_bind (awaken_loop_refines s1 σ1 hS1 hR1 hN1 hI1 hA1 _ (rel_len_lt hS1)) ?_
  rintro s2 ⟨σ2, h2, hS2, hR2, hN2, hI2, ⟨hA2, hcn2, hnr2⟩, hc2, hsub, hw2⟩
  rw [WP.spec_ok]
  refine ⟨σ1, σ2, hF, h2, hS2, hR2, hN2, ⟨hI2, ?_, hO1.calm hc2, ⟨hA2, hId1.sub hc2 hsub⟩,
    hW1.sub hc2 hsub⟩, hc2, hcn2, hnr2, hsub, (s1, a1), hPf, rfl, hw2⟩
  exact fun e => (hC1 (Classical.byContradiction fun h => hnr2 h e)).sub hc2 hsub



end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem schedule_refinesWP0FR {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hnd : Fl4Spec.numDomains = 1) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW0R T C σ1 ∧
      ((σ1.domainTime ≠ 0 ∨ NdOK (L := L) r.1 σ1) ∧
        (∀ n ∈ N, n.val + 40 ≤ (L.ksb r.1).val ∨ (L.ksb r.1).val + 13568 ≤ n.val) ∧ Pf r σ1) ⦄)
    (hPo : ∀ r σ1, Pf r σ1 → FpuOwnOK σ1)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c)
    (hsni : SniHyp st ar N T C c) (hsend : SendHyp st ar N T C c)
    (hT : TimeAgree ar) :
    sched.schedule st ar s a ⦃ r => ∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      ActIdle σ' ∧ ∃ rf : S × A, Pf rf σ1 ∧ WritesIn st rf.1 r.1 (KFootN st T N C c rf.1 σ1) ∧
      ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1 → RunW σ3) ∧
        Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
  unfold sched.schedule
  refine WP.spec_bind (awaken_refinesW0R s a σ hfire) ?_
  rintro ⟨s1, a1⟩ ⟨σ1, σ2, hF, haw, hS2, hR2, hN2, ⟨hI2, hC2w, hO2, ⟨hA2, hId2⟩, hW2⟩, hcalm, -, hnr12, -,
    rf, ⟨hdt1, hNk1, hPf⟩, -, hwA⟩
  have hSK2 := (SchK.of_eq schs_awaken haw).1
  have hdt2 : σ2.domainTime ≠ 0 ∨ NdOK (L := L) s1 σ2 :=
    hdt1.imp (fun h => by rw [hcalm.2.2.2.2.2.2.2.1]; exact h)
      (fun h => h.sfoot' hS2 hwA hSK2.dl (DI.of_eq di_awaken haw) hSK2.dsi)
  have hNk2 : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s1).val ∨ (L.ksb s1).val + 13568 ≤ n.val := by
    rw [hwA.1]; exact hNk1
  have hM2 : RunM σ1 → RunM σ2 := fun h => h.calm hcalm hnr12
  have hfo2 : FpuOwnOK σ2 := (hPo rf σ1 hPf).of (ow_awaken.of_eq haw) hcalm.1
  have hsp := schedule_unfold haw hnd
  simp only [check_domain_time_refines, bind_ok]
  obtain ⟨Q, R, hc, hs⟩ := hS2.lists
  -- the outgoing SC's owner `u0`, or (unbound) the SC itself, which no thread names
  obtain ⟨u0, hown0, hback, hnr0, hcsc⟩ : ∃ u0 : Fl4Spec.ObjRef,
      (∀ x n, σ2.kheap σ2.curSc = some (.schedContext x n) → x.scTcb = some u0 ∨ x.scTcb = none) ∧
      (∀ xt, σ2.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ2.curSc) ∧
      (0 < σ2.consumedTime → u0 ∉ σ2.releaseQueue) ∧ ∃ sc ∈ C, sc.bv = σ2.curSc := by
    rcases hW2 with ⟨u0w, hu0T, xt0, hkt0, hxs0, hown0, hnr0⟩ | ⟨⟨sc, hscC, hscv⟩, hun⟩
    · refine ⟨u0w.bv, fun x n hx => Or.inl (hown0 x n hx), fun xt hk => ?_, hnr0, ?_⟩
      · rw [hkt0] at hk; cases hk; exact hxs0
      · obtain ⟨x', hk', -, -, hsct, -⟩ := hs.tcb u0w hu0T
        rw [hkt0] at hk'; cases hk'
        rw [hxs0] at hsct
        obtain ⟨h0, hbv⟩ := optRef_some hsct.symm
        exact ⟨_, hs.scMem _ hu0T h0, hbv⟩
    · obtain ⟨y, n, hky, -⟩ := hs.scs sc hscC
      rw [hscv] at hky
      refine ⟨σ2.curSc, fun x n hx => Or.inr (hun x n hx), fun xt hk => ?_, fun _ hm => ?_, sc, hscC, hscv⟩
      · rw [hky] at hk; cases hk
      · obtain ⟨xu, -, -, -, h1, -⟩ := hI2.rel _ hm
        rw [hky] at h1; cases h1
  -- the tail after a branch ending in `σ3`
  have tail : ∀ (s3 : S) (a2 : A) (σ3 : Fl4Spec.State Unit),
      SchedRel st N T C c s3 σ3 → NtfnStateRel N T (L.mem s3) σ3 → NSC N C σ3 → Inv σ3 →
      (∃ xt scp, σ3.kheap σ3.curThread = some (.tcb xt) ∧ xt.tcbSchedContext = some scp ∧
        NotIpcBlk xt.tcbState ∧ σ3.curThread ∉ σ3.releaseQueue ∧
        (scp ≠ σ3.idleSc → ∀ x n, σ3.kheap scp = some (.schedContext x n) → Fl4Spec.scActive x = true)) →
      HeapEqUpToFpu σ2 σ3 → σ3.releaseQueue = σ2.releaseQueue → σ3.curSc = σ2.curSc →
      σ3.consumedTime = σ2.consumedTime → σ3.curTime = σ2.curTime → σ3.idleThread = σ2.idleThread →
      σ3.idleSc = σ2.idleSc →
      (∀ σ', Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) →
        Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False)) →
      WritesIn st s1 s3 (SFootN st T c s1) → (RunM σ1 → RunW σ3) →
      (do
        let s4 ← sched.set_action st s3 sched.ACTION_RESUME_CURRENT
        let (s5, a3) ← sched.switch_sched_context st ar s4 a2
        let c ← st.cur_cpu s5
        let i ← obj.node_get st s5 c layout.node.REPROGRAM
        let (s6, a4) ←
          if i != 0#u64
          then
            do
            let (s7, a5) ← sched.set_next_interrupt st ar s5 a3
            let s8 ← obj.node_set st s7 c layout.node.REPROGRAM 0#u64
            ok (s8, a5)
          else ok (s5, a3)
        smp.send_pending st ar s6 a4) ⦃ r => ∃ σ1' σ', Fires σ σ1' ∧
          Fl4Spec.schedule (Z := Unit) σ1' = ({((), σ')}, False) ∧
          SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
          ActIdle σ' ∧ ∃ rf : S × A, Pf rf σ1' ∧ WritesIn st rf.1 r.1 (KFootN st T N C c rf.1 σ1') ∧
          ∃ σ3 : Fl4Spec.State Unit, OffOK σ3 ∧ (RunM σ1' → RunW σ3) ∧
            Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False) ⦄ := by
    intro s3 a2 σ3 hS3 hR3 hN3 hI3 hnc hk3 hr3 hcs3 hcn3 htm3 hid3 hisc3 hspec hw3 hrw3
    refine WP.spec_mono (tail_refines s3 a2 σ3 hS3 hR3 hN3 hI3 hnc
      (by rw [hcs3]; exact hcsc) (u0 := u0) (fun x n hx => hown0 x n (by rw [← hcs3]; exact hk3.sc.1 hx))
      (fun xt hx => by obtain ⟨x0, hx0, e⟩ := hk3.tcb_back hx; rw [hcs3, e.sc]; exact hback x0 hx0) (fun h0 hm => hnr0 (by rw [← hcn3]; exact h0) (by rw [← hr3]; exact hm))
      (hO2.fpu hk3 hcs3 hcn3 htm3) hT hsni hsend) ?_
    rintro r ⟨σ', h', a1, a2, a3, a4, a5, a6, a7⟩
    exact ⟨σ1, σ', hF, hspec σ' h', a1, a2, a3, a4, a5,
      a6 (IdleOK.fpu hId2 hid3 hk3 (fun hm => by rw [hr3] at hm; exact hm)), rf, hPf,
      WritesIn.kfootN_trans (WritesIn.sfootN_trans (WritesIn.sfootN_of hwA) hw3)
        (SzKeepC.of (SzKeep.fpu (HeapEqUpToFpu.eq_trans hcalm.1 hk3))) a7, σ3, hO2.fpu hk3 hcs3 hcn3 htm3, hrw3, h'⟩
  step with sched.action.spec' as ⟨act, hact⟩
  rw [hc.cur] at hact
  subst hact
  have ha := hS2.act
  by_cases h0 : nodeW st s1 c layout.node.SCHED_ACTION = 0#u64
  · -- resume
    have hres : σ2.schedulerAction = .resumeCurThread := by
      cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
        first | rfl | (rw [h0] at ha; exact absurd ha (by decide)) | exact absurd h0 ha.1
    have hb : (nodeW st s1 c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = false := by
      rw [resume_val', h0]; rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine tail s1 a1 σ2 hS2 hR2 hN2 hI2
      (newcur_of (Or.inr (Or.inr rfl)) rfl rfl hId2 (hC2w hres)) (HeapEqUpToFpu.refl _) rfl rfl rfl rfl rfl rfl (fun σ' h' => ?_)
      (WritesIn.refl _ _) (fun h => (hM2 h).resolve_left fun e => e hres)
    rw [hsp, hres]; rw [resume_self hres] at h'; exact h'
  · have hb : (nodeW st s1 c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true := by
      rw [resume_val']; simpa using h0
    simp only [hb, ↓reduceIte]
    have hct := hc.curT
    have ect : σ2.curThread = (nodeW st s1 c layout.node.CUR_THREAD).bv := hs.curThread
    step with sched.cur_thread.spec' as ⟨ct, hct'⟩
    rw [hc.cur] at hct'
    subst hct'
    step with sched.is_schedulable.spec' as ⟨wr, hwr⟩
    rw [schedulable_eq hR2 hS2 hct] at hwr
    subst hwr
    refine WP.spec_bind (enq_ct_refines s1 σ2 hS2 hct ect) ?_
    rintro s4 ⟨σ4, hw4, hq4, ha4, htk4, hcs4, hct4, hf4, hS4, hwq4⟩
    have hR4 := hR2.frame hS2.placed hf4 (KView.of_kheap hq4.1)
    have hN4 : NSC N C σ4 := fun n hn x p hx hp => hN2 n hn x p (by rw [← hq4.1]; exact hx) hp
    have hI4 := hI2.qchange hq4
    have hfo4 : FpuOwnOK σ4 := hfo2.of ((ow_when _ (ow_tcbSchedAction _ _)).of_eq hw4) hq4.1
    have hSK4 := (SchK.of_eq (schs_when _ (schs_tcbSchedAction _ _)) hw4).1
    have hdt4 : σ4.domainTime ≠ 0 ∨ NdOK (L := L) s4 σ4 :=
      hdt2.imp (fun h => by rw [htk4.2.2.2.2.1]; exact h)
        (fun h => h.sfoot' hS4 hwq4 hSK4.dl (DI.of_eq (di_when _ (di_tcbSchedAction _ _)) hw4) hSK4.dsi)
    have hNk4 : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s4).val ∨ (L.ksb s4).val + 13568 ≤ n.val := by
      rw [hwq4.1]; exact hNk2
    -- what a branch ending in `σ3` from `σ4` gives
    have conv : ∀ σ3 : Fl4Spec.State Unit,
        (σ3.curThread = σ4.idleThread ∨ Fl4Spec.schedulable σ3.curThread σ4 = true) →
        HeapEqUpToFpu σ4 σ3 → σ3.releaseQueue = σ4.releaseQueue → σ3.curSc = σ4.curSc → TK0 σ4 σ3 →
        (σ3.curThread = σ2.idleThread ∨ Fl4Spec.schedulable σ3.curThread σ2 = true ∨ σ3.curThread = σ2.curThread) ∧
        HeapEqUpToFpu σ2 σ3 ∧ σ3.releaseQueue = σ2.releaseQueue ∧ σ3.curSc = σ2.curSc ∧
        σ3.consumedTime = σ2.consumedTime ∧ σ3.curTime = σ2.curTime ∧ σ3.idleThread = σ2.idleThread ∧
        σ3.idleSc = σ2.idleSc := by
      intro σ3 hnc hk hr hcs htk
      refine ⟨?_, HeapEqUpToFpu.eq_trans hq4.1 hk, hr.trans hq4.2.1, hcs.trans hcs4, htk.2.1.trans htk4.2.1, htk.1.trans htk4.1,
        htk.2.2.1.trans htk4.2.2.1, htk.2.2.2.2.trans htk4.2.2.2.2.2⟩
      rcases hnc with h | h
      · exact Or.inl (h.trans htk4.2.2.1)
      · exact Or.inr (Or.inl (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h))
    by_cases h1 : nodeW st s1 c layout.node.SCHED_ACTION = 1#u64
    · -- choose a new thread
      have hcn : σ2.schedulerAction = .chooseNewThread := by
        cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
          first | rfl | exact absurd ha h0 | exact absurd h1 ha.2.1
      rw [choose_val']
      simp only [h1, ↓reduceIte]
      refine WP.spec_bind (scnt_refines0F s4 a1 σ4 hS4 hR4 hN4 hI4 hA hAN hfo4 hNk4 hdt4) ?_
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3, hwb3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3
        (newcur_of2F (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g3 hId2)
        g2 g3 g4 g5 g6 g7 g8 (fun σ' h' => ?_) (WritesIn.sfootN_trans (WritesIn.sfootN_of hwq4) hwb3)
        (fun _ => RunW.of_new2F (σ := σ2) (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g7)
      rw [hsp, hcn]
      exact (nd_bind_one hw4 _).trans ((nd_bind_one h3 _).trans h')
    · -- switch to the candidate
      have hwT : nodeW st s1 c layout.node.SCHED_ACTION ∈ T := by
        rcases hS2.actW with e | e | e
        · exact absurd e h0
        · exact absurd e h1
        · exact e
      have hsw : σ2.schedulerAction = .switchThread (nodeW st s1 c layout.node.SCHED_ACTION).bv := by
        cases e : σ2.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
          first | exact absurd ha h0 | exact absurd ha h1 | rw [ha.2.2]
      have hb1 : ¬ nodeW st s1 c layout.node.SCHED_ACTION = sched.ACTION_CHOOSE_NEW := by rw [choose_val']; exact h1
      simp only [hb1, ↓reduceIte]
      have hsch4 : Fl4Spec.schedulable (nodeW st s1 c layout.node.SCHED_ACTION).bv σ4 = true := by
        rw [schedulable_heap hq4.1 hq4.2.1]; exact hA2 _ hsw
      have hidle4 : σ4.curThread = σ4.idleThread →
          Fl4Spec.schedulable (nodeW st s1 c layout.node.CUR_THREAD).bv σ2 = false := by
        intro hi
        rw [hct4, htk4.2.2.1, ect] at hi
        rw [hi]
        obtain ⟨x, hx1, -, hx3, -⟩ := hId2
        by_contra hne
        obtain ⟨x', -, -, -, hk', -, hr', -⟩ := schedulable_inv (by simpa using hne)
        rw [hx1] at hk'; cases hk'
        rw [hx3] at hr'; cases hr'
      have hwhen : Fl4Spec.NonDet.when (Fl4Spec.schedulable (nodeW st s1 c layout.node.CUR_THREAD).bv σ2 = true)
          (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ4.curThread) σ2 = ({((), σ4)}, False) := by
        rw [hct4, ← ect]; exact hw4
      refine WP.spec_bind (switch_branch_refines0F s4 a1 σ2 σ4 hS4 hR4 hN4 hI4 hA hAN hfo4 hNk4 hdt4 hwT hsch4 _ hidle4 hwhen) ?_
      rintro ⟨s3, a2⟩ ⟨σ3, h3, hS3, hR3, hN3, hI3, hnc3, hcs3, hr3, hk3, htk3, hwb3⟩
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := conv σ3 hnc3 hk3 hr3 hcs3 htk3
      refine tail s3 a2 σ3 hS3 hR3 hN3 hI3
        (newcur_of2F (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g3 hId2)
        g2 g3 g4 g5 g6 g7 g8 (fun σ' h' => ?_) (WritesIn.sfootN_trans (WritesIn.sfootN_of hwq4) hwb3)
        (fun _ => RunW.of_new2F (σ := σ2) (by
          rcases hnc3 with h | h
          · exact Or.inl (h.trans htk4.2.2.1)
          · exact Or.inr (by rw [← schedulable_heap (σ' := σ4) hq4.1 hq4.2.1]; exact h)) g2 g7)
      rw [hsp, hsw]
      rw [hct4, ← ect] at h3
      exact (nd_bind_one h3 _).trans h'



end

end

end Fl4Proofs.P3.Sched
