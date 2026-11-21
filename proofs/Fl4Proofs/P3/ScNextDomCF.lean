/-
P3 (DESIGN.md §9), scheduler: **`schedule` with the domain switch, up to
the FPU** (KENTRY-PLAN.md sch5 (B)): ScNextDomC's `cn_refines0`,
`cn_enq0`/`cn_app0`, `switch_branch_refines0`, `schedule_refinesWP0` with
the corrected arch premises of sch4 (A): `ArchSwF`/`ArchNdF` [P] (ScArchF,
ScNextDomF) in place of `ArchSw`/`ArchNd` (false whenever the spec has an
FPU owner), `FpuOwnOK` [J] (l4v X64 `valid_cur_fpu`) at the switch state
(carried from the fire predicate across `awaken` and the queue operations
as in ScScheduleF: `ow_awaken`, `ow_tcbSchedAction`), and
`HeapEqUpToFpu σ σ'` for `σ'.kheap = σ.kheap` in the posts. Same proofs
(scripted copy, ScScheduleF's changes applied to ScNextDomC).
`schedule_refinesWP0F` supersedes `schedule_refinesWP0`.
-/
import Fl4Proofs.P3.ScNextDomC
import Fl4Proofs.P3.ScNextDomF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem cn_refines0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) (enq : Bool) :
    (do
      let s5 ← if enq then sched.enqueue st s t else sched.append st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) (if enq then Fl4Spec.tcbSchedEnqueue else Fl4Spec.tcbSchedAppend) t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, scp, -, -, hk, hsc, -, -, -, hnr⟩ := schedulable_inv hsch
  have hrel0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    exact hnr (by rw [hs.rel]; exact List.mem_map_of_mem ((hc.released t ht).1 hne))
  -- the queue operation
  have hq : (if enq then sched.enqueue st s t else sched.append st s t) ⦃ s5 => ∃ σ5,
      Fl4Spec.tcbSchedAction (Z := Unit) (if enq then Fl4Spec.tcbSchedEnqueue else Fl4Spec.tcbSchedAppend) t.bv σ =
        ({((), σ5)}, False) ∧ QChange σ σ5 ∧ (σ5.schedulerAction = σ.schedulerAction ∧ TK σ σ5 ∧
          σ5.curSc = σ.curSc ∧ σ5.idleThread = σ.idleThread) ∧
        FootEq N T (L.mem s) (L.mem s5) ∧ SchedRel st N T C c s5 σ5 ∧ WritesIn st s s5 (SFoot st T c s) ∧
        σ5.domainList = σ.domainList ∧ σ5.domainIndex = σ.domainIndex ∧ σ5.domainStartIndex = σ.domainStartIndex ⦄ := by
    cases enq
    · refine WP.spec_mono (WP.spec_and (append_refines s σ hS t ht (fun _ => hrel0)) (append_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5, ?_⟩ <;> rw [← e]
      · exact qchange_append hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
    · refine WP.spec_mono (WP.spec_and (enqueue_refines s σ hS t ht (fun _ => hrel0)) (enqueue_sfoot hS ht)) ?_
      rintro s5 ⟨⟨σ5, he, -, -, hf, hS5⟩, hw5⟩
      have e := pair_eq (he.symm.trans (tcbSchedAction_gen hk _))
      refine ⟨σ5, he, ?_, ?_, hf, hS5, hw5, ?_⟩ <;> rw [← e]
      · exact qchange_enqueue hk hsch
      · exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩
  refine WP.spec_bind hq ?_
  rintro s5 ⟨σ5, he, hq5, ⟨-, htk5, hcs5, hid5⟩, hf5, hS5, hw5, hdl5, hdi5, hds5⟩
  have hR5 := hR.frame hS.placed hf5 (KView.of_kheap hq5.1)
  have hI5 := hI.qchange hq5
  step with sched.set_action.spec' as ⟨s6, hs6⟩
  subst hs6
  have hc5 := hS5.lists.choose_spec.choose_spec.1.cur
  rw [hc5, choose_val']
  have hS6 := hS5.set_action (Or.inr (Or.inl rfl)) (a := .chooseNewThread) rfl
  have hf6 : FootEq N T (L.mem s5) (L.mem (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)) :=
    node_wr_foot hS5 (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  set σ6 : Fl4Spec.State Unit := { σ5 with schedulerAction := .chooseNewThread }
  have hR6 : NtfnStateRel N T (L.mem (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)) σ6 :=
    hR5.frame hS5.placed hf6 (KView.of_kheap rfl)
  have hN6 : NSC N C σ6 := fun n hn x0 p hx hp => hN n hn x0 p (by rw [← hq5.1]; exact hx) hp
  have hI6 : Inv σ6 := hI5.congr rfl rfl rfl rfl
  have hw6 : WritesIn st s5 (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64) (SFoot st T c s5) :=
    sfoot_wr_node hS5.lists.choose_spec.choose_spec.1.node (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION]) _
  have hdt6 : σ6.domainTime ≠ 0 ∨ NdOK (L := L) (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64) σ6 :=
    hdt.imp (fun h => by show σ5.domainTime ≠ 0; rw [htk5.2.2.2.2.1]; exact h)
      (fun h => (h.sfoot hS hw5 hdl5 hdi5 hds5).sfoot hS5 hw6 rfl rfl rfl)
  have hNk6 : ∀ n ∈ N, n.val + 40 ≤ (L.ksb (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)).val ∨
      (L.ksb (L.wr s5 (L.nodeAt s5 c layout.node.SCHED_ACTION) 1#u64)).val + 13568 ≤ n.val := by
    rw [hw6.1, hw5.1]; exact hNk
  have hfo6 : FpuOwnOK σ6 := hfo.of (show σ5.archState.x64CurrentFpuOwner = σ.archState.x64CurrentFpuOwner from OW.of_eq (ow_tcbSchedAction _ _) he) hq5.1
  refine WP.spec_mono (scnt_refines0F _ a σ6 hS6 hR6 hN6 hI6 hA hAN hfo6 hNk6 hdt6) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨σ', ?_, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nd_bind_one he, nd_bind_one (setAction_eq σ5 _)]; exact h1
  · rcases h6 with h6 | h6
    · exact Or.inl (h6.trans hid5)
    · exact Or.inr (by rw [← schedulable_heap (σ' := σ6) hq5.1 hq5.2.1]; exact h6)
  · rw [h7]; exact hcs5
  · rw [h8]; exact hq5.2.1
  · exact HeapEqUpToFpu.eq_trans (σ2 := σ6) hq5.1 h9
  · exact (TK.tk0 htk5).trans h10
  · exact WritesIn.sfootN_trans (WritesIn.sfootN_of (WritesIn.sfoot_trans hw5 hw6)) h11


theorem cn_enq0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    (do
      let s5 ← sched.enqueue st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ :=
  cn_refines0F s a σ hS hR hN hI hA hAN hfo hNk hdt ht hsch true

theorem cn_app0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) :
    (do
      let s5 ← sched.append st s t
      let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
      sched.schedule_choose_new_thread st ar s6 a) ⦃ r => ∃ σ', (do
        Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedAppend t.bv
        Fl4Spec.setSchedulerAction .chooseNewThread
        Fl4Spec.scheduleChooseNewThread) σ =
      ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ :=
  cn_refines0F s a σ hS hR hN hI hA hAN hfo hNk hdt ht hsch false





theorem switch_branch_refines0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ0 σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hA : ArchSwF st ar N T C c) (hAN : ArchNdF st N T C c) (hfo : FpuOwnOK σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (hdt : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) {t : U64} (ht : t ∈ T)
    (hsch : Fl4Spec.schedulable t.bv σ = true) (wr : Bool)
    (hidle : σ.curThread = σ.idleThread → wr = false)
    (hwhen : Fl4Spec.NonDet.when (wr = true) (Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue σ.curThread) σ0 =
      ({((), σ)}, False)) :
    (do
      let ct1 ← sched.cur_thread st s
      let t1 ← sched.idle_thread st s
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq ct1 t1
      let fastfail ←
        if b
        then ok true
        else
          do
          let i ← obj.Tcb.prio st t s
          let i1 ← obj.Tcb.prio st ct1 s
          if i < i1
          then ok true
          else ok false
      if fastfail
      then
        let i ← sched.cur_domain st s
        let i1 ← obj.Tcb.prio st t s
        let b1 ← sched.is_highest_prio st s i i1
        if b1
        then
          if wr
          then
            let i2 ← obj.Tcb.prio st ct1 s
            if i1 = i2
            then
              let s5 ← sched.append st s t
              let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
              sched.schedule_choose_new_thread st ar s6 a
            else sched.switch_to_thread st ar s a t
          else sched.switch_to_thread st ar s a t
        else
          let s5 ← sched.enqueue st s t
          let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
          sched.schedule_choose_new_thread st ar s6 a
      else
        if wr
        then
          let i ← obj.Tcb.prio st t s
          let i1 ← obj.Tcb.prio st ct1 s
          if i = i1
          then
            let s5 ← sched.append st s t
            let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
            sched.schedule_choose_new_thread st ar s6 a
          else sched.switch_to_thread st ar s a t
        else sched.switch_to_thread st ar s a t) ⦃ r => ∃ σ',
      Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xa, hka, -, -, -, hpa⟩ := hs.tcb t ht
  have hct := hc.curT
  obtain ⟨xc, hkc, -, -, -, hpc⟩ := hs.tcb _ hct
  rw [← hs.curThread] at hkc
  -- the spec up to the `if`
  have hsp : ∀ (cp : Fl4Spec.Priority) (X : Fl4Spec.SMonad Unit Unit),
      (σ.curThread ≠ σ.idleThread → cp = xc.tcbPriority) → (σ.curThread = σ.idleThread → cp = 0) →
      ((if decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else if wr = true ∧ cp = xa.tcbPriority then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else do
          Fl4Spec.guardedSwitchTo t.bv
          Fl4Spec.setSchedulerAction .resumeCurThread) : Fl4Spec.SMonad Unit Unit) σ = X σ →
      Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 = X σ := by
    intro cp X hcp1 hcp2 hX
    unfold Fl4Spec.scheduleSwitchThreadBranch
    rw [nd_bind_one hwhen, nd_gets_bind, nd_bind_one (threadGet_eq _ hka)]
    by_cases hne : σ.curThread ≠ σ.idleThread
    · rw [if_pos hne, nd_bind_one (threadGet_eq _ hkc), ← hcp1 hne]
      unfold Fl4Spec.scheduleSwitchThreadFastfail
      beta_reduce
      rw [nd_bind_one (show (pure (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp)) :
        Fl4Spec.SMonad Unit Bool) σ = ({(_, σ)}, False) from rfl), nd_gets_bind, nd_gets_bind]
      exact hX
    · rw [if_neg hne, nd_bind_one (show (pure 0 : Fl4Spec.SMonad Unit Fl4Spec.Priority) σ = ({(0, σ)}, False) from rfl),
        ← hcp2 (not_not.1 hne)]
      unfold Fl4Spec.scheduleSwitchThreadFastfail
      beta_reduce
      rw [nd_bind_one (show (pure (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp)) :
        Fl4Spec.SMonad Unit Bool) σ = ({(_, σ)}, False) from rfl), nd_gets_bind, nd_gets_bind]
      exact hX
  have hp : (L.mem s (prioA t)).val < 256 := hc.prio t ht
  have hpa' : specPrio (L.mem s (prioA t)) = xa.tcbPriority := specPrio_eq hpa
  have post : ∀ (cp : Fl4Spec.Priority) (X : Fl4Spec.SMonad Unit Unit),
      (σ.curThread ≠ σ.idleThread → cp = xc.tcbPriority) → (σ.curThread = σ.idleThread → cp = 0) →
      ((if decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < cp) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else if wr = true ∧ cp = xa.tcbPriority then do
          Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend t.bv
          Fl4Spec.setSchedulerAction .chooseNewThread
          Fl4Spec.scheduleChooseNewThread
        else do
          Fl4Spec.guardedSwitchTo t.bv
          Fl4Spec.setSchedulerAction .resumeCurThread) : Fl4Spec.SMonad Unit Unit) σ = X σ →
      ∀ r : S × A, (∃ σ', X σ = ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s)) →
      ∃ σ', Fl4Spec.scheduleSwitchThreadBranch (Z := Unit) t.bv σ.curThread wr σ0 =
        ({((), { σ' with schedulerAction := .resumeCurThread })}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
        σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧ TK0 σ σ' ∧ P1.WritesIn st s r.1 (SFootN st T c s) := by
    intro cp X h1 h2 hX r ⟨σ', e, rest⟩
    exact ⟨σ', (hsp cp X h1 h2 hX).trans e, rest⟩
  have SW := fun cp h1 h2 hX => WP.spec_mono (WP.spec_mono (sw_refinesF s a σ hS hR hN hI hA hfo ht hsch)
    fun r ⟨σ', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ =>
      ⟨σ', g1, g2, g3, g4, g5, g6, g7, g8, g9, TK.tk0 g10, WritesIn.sfootN_of g11⟩) (post cp _ h1 h2 hX)
  have CE := fun cp h1 h2 hX => WP.spec_mono (cn_enq0F s a σ hS hR hN hI hA hAN hfo hNk hdt ht hsch)
    (post cp _ h1 h2 hX)
  have CA := fun cp h1 h2 hX => WP.spec_mono (cn_app0F s a σ hS hR hN hI hA hAN hfo hNk hdt ht hsch)
    (post cp _ h1 h2 hX)
  step with sched.cur_thread.spec' as ⟨ct1, hct1⟩
  rw [hc.cur] at hct1
  subst hct1
  step with sched.idle_thread.spec2 as ⟨t1, ht1⟩
  rw [hc.cur] at ht1
  subst ht1
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok]
  by_cases hci : nodeW st s c layout.node.CUR_THREAD = nodeW st s c layout.node.IDLE_THREAD
  · have hcid : σ.curThread = σ.idleThread := by rw [hs.curThread, hs.idleTh, hci]
    have hwr := hidle hcid
    subst hwr
    simp only [hci, decide_true, ↓reduceIte, bind_ok]
    step with sched.cur_domain.spec' as ⟨i, hi⟩
    step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
    subst hi hi1
    refine WP.spec_bind (is_highest_prio_refines s σ hS _ hp) ?_
    intro b1 hb1
    rw [hpa'] at hb1
    by_cases hb : b1 = true
    · simp only [hb, ↓reduceIte, Bool.false_eq_true]
      refine SW 0 (fun h => absurd hcid h) (fun _ => rfl) ?_
      rw [if_neg (by rw [← hb1, hb]; simp), if_neg (by simp)]
    · have hb' : b1 = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ↓reduceIte]
      refine CE 0 (fun h => absurd hcid h) (fun _ => rfl) ?_
      rw [if_pos ⟨by simp [hcid], by rw [← hb1, hb']; simp⟩]
  · have hcid : σ.curThread ≠ σ.idleThread := by
      rw [hs.curThread, hs.idleTh]; exact bv_ne hci
    simp only [hci, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hpc' : (L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))).val = xc.tcbPriority.toNat := hpc
    step with obj.Tcb.prio.spec as ⟨i, hi⟩
    step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
    subst hi hi1
    have hcp1 : σ.curThread ≠ σ.idleThread → xc.tcbPriority = xc.tcbPriority := fun _ => rfl
    have hcp2 : σ.curThread = σ.idleThread → xc.tcbPriority = 0 := fun h => absurd h hcid
    have heq : (L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))) ↔
        xc.tcbPriority = xa.tcbPriority := (prio_eq_iff hpa hpc').trans eq_comm
    by_cases hlt : L.mem s (prioA t) < L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
    · have hlt' : xa.tcbPriority < xc.tcbPriority := (prio_lt_iff hpa hpc').1 hlt
      simp only [hlt, ↓reduceIte, bind_ok]
      step with sched.cur_domain.spec' as ⟨i, hi⟩
      step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
      subst hi hi1
      refine WP.spec_bind (is_highest_prio_refines s σ hS _ hp) ?_
      intro b1 hb1
      rw [hpa'] at hb1
      by_cases hb : b1 = true
      · simp only [hb, ↓reduceIte]
        have hc1 : ¬ (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < xc.tcbPriority) = true ∧
            ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true) := by
          rw [← hb1, hb]; simp
        cases wr
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (by simp)])
        · simp only [↓reduceIte]
          step with obj.Tcb.prio.spec as ⟨i2, hi2⟩
          subst hi2
          by_cases he : L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
          · simp only [he, ↓reduceIte]
            exact CA _ hcp1 hcp2 (by rw [if_neg hc1, if_pos ⟨rfl, heq.1 he⟩])
          · simp only [he, ↓reduceIte]
            exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (fun h => he (heq.2 h.2))])
      · have hb' : b1 = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte]
        exact CE _ hcp1 hcp2 (by rw [if_pos ⟨by simp [hcid, hlt'], by rw [← hb1, hb']; simp⟩])
    · have hc1 : ¬ (decide (σ.curThread ≠ σ.idleThread → xa.tcbPriority < xc.tcbPriority) = true ∧
          ¬ (@decide (Fl4Spec.isHighestPrio σ.curDomain xa.tcbPriority σ) (Classical.propDecidable _)) = true) :=
        fun h => hlt ((prio_lt_iff hpa hpc').2 (by simpa [hcid] using h.1))
      simp only [hlt, Bool.false_eq_true, ↓reduceIte, bind_ok]
      cases wr
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (by simp)])
      · simp only [↓reduceIte]
        step with obj.Tcb.prio.spec as ⟨i, hi⟩
        step with obj.Tcb.prio.spec as ⟨i1, hi1⟩
        subst hi hi1
        by_cases he : L.mem s (prioA t) = L.mem s (prioA (nodeW st s c layout.node.CUR_THREAD))
        · simp only [he, ↓reduceIte]
          exact CA _ hcp1 hcp2 (by rw [if_neg hc1, if_pos ⟨rfl, heq.1 he⟩])
        · simp only [he, ↓reduceIte]
          exact SW _ hcp1 hcp2 (by rw [if_neg hc1, if_neg (fun h => he (heq.2 h.2))])



theorem schedule_refinesWP0F {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hnd : Fl4Spec.numDomains = 1) {Pf : S × A → Fl4Spec.State Unit → Prop}
    (hfire : timer.fire st ar s a ⦃ r => ∃ σ1, Fires σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧
      NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ SchedPreW0 T C σ1 ∧
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
  refine WP.spec_bind (awaken_refinesW0 s a σ hfire) ?_
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
      (newcur_of (Or.inr (Or.inr rfl)) rfl rfl hId2 (hC2w.resolve_left (by rw [hres]; intro e; cases e))) (HeapEqUpToFpu.refl _) rfl rfl rfl rfl rfl rfl (fun σ' h' => ?_)
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
        (newcur_ofF g1 g2 g3 hId2 (hC2w.resolve_left (by rw [hsw]; intro e; cases e)))
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
