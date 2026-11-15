/-
P3 (DESIGN.md §9), scheduling contexts: **`check_budget` and
`check_budget_restart` refine l4v `check_budget` and `check_budget_restart`**
(`check_budget_refines`, `check_budget_restart_refines`) and keep `Inv`.
FL4 is built with one domain, so the spec's `numDomains` is a hypothesis
(`hnd`); the rest is `charge_budget_refines`'s.
-/
import Fl4Proofs.P3.ScCharge6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem is_cur_domain_expired_eq (s : S) : sched.is_cur_domain_expired st s = ok false := by
  unfold sched.is_cur_domain_expired
  rw [show layout.NUM_DOMAINS = 1#u64 by unfold layout.NUM_DOMAINS fl4_abi.config.NUM_DOMAINS; rfl]
  rfl

theorem is_runnable_spec (s : S) (t : obj.Tcb) :
    sched.is_runnable st s t ⦃ b => b = decide (L.mem s (tStA t) = sched.TS_RUNNING ∨
      L.mem s (tStA t) = sched.TS_RESTART ∨ L.mem s (tStA t) = sched.TS_RUNNING_VM) ⦄ := by
  unfold sched.is_runnable
  step
  repeat' split
  all_goals simp_all [tStA, stA]

/-- A runnable thread is in no notification's queue. -/
theorem not_in_ntfnQueue {N T : Set U64} {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : NtfnStateRel N T m σ)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (hrun : Fl4Spec.runnable x.tcbState = true) :
    ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue := by
  intro n hn z hz hm
  obtain ⟨z', hz', hr⟩ := hR.ntfn n hn
  rw [hz] at hz'; cases hz'
  have hst := (hR.at_tcb ht hk).st
  have obj := hr.obj
  revert hm obj
  cases z.ntfnObj with
  | idleNtfn => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
  | activeNtfn b => intro hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
  | waitingNtfn q =>
    intro hm obj
    obtain ⟨-, xs, -, rfl, -, hb⟩ := obj
    have h6 := (hb t (mem_map_bv.1 hm)).1
    rw [hst] at h6
    cases e : x.tcbState <;> simp_all [tsCode, Fl4Spec.runnable]

/-- **`check_budget` refines l4v `check_budget`** and keeps the invariant. -/
theorem check_budget_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = Fl4Spec.idleScPtr)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ Fl4Spec.idleScPtr → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hnb : ∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      ∀ q, xt.tcbState ≠ .blockedOnNotification q)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' → NtfnStateRel N T (L.mem s') σ' →
      NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ∧ (IdleOK σ' → IdleOK σ'') ⦄) :
    sched.check_budget st ar s a ⦃ r => ∃ σ', Fl4Spec.checkBudget (Z := Unit) σ = ({(r.1, σ')}, False) ∧
      SchedRel st N T C c r.2.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.2.1) σ' ∧ NSC N C σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv) ∧
      (OffReady σ → OffOK σ') ∧ (ActIdle σ → ActIdle σ') ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  unfold sched.check_budget
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.consumed.spec' as ⟨cn, hcn⟩
  rw [hc.cur] at hsc' hcn
  subst hsc' hcn
  refine WP.spec_bind (sufficient_refines s a σ hS hscC hk _ hmb) ?_
  intro b hb
  have hsp : Fl4Spec.checkBudget (Z := Unit) σ = (if b = true then
      (do let domExp ← Fl4Spec.NonDet.gets Fl4Spec.isCurDomainExpired; return !domExp) σ
      else (do
        let consumed ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.consumedTime
        Fl4Spec.chargeBudget consumed true
        return false) σ) := by
    unfold Fl4Spec.checkBudget
    rw [nd_gets_bind, nd_gets_bind, hs.curSc, hs.consumed, nd_bind_one hb]
    cases b <;> rfl
  by_cases hbt : b = true
  · simp only [hbt, ↓reduceIte]
    rw [is_cur_domain_expired_eq]
    simp only [bind_ok, WP.spec_ok]
    refine ⟨σ, ?_, hS, hI, hR, hN, Or.inr (HeadKeeps.refl σ _), fun ho => ho.ok fun y m hy => ?_, id⟩
    · rw [hsp, if_pos hbt, nd_gets_bind]
      have : Fl4Spec.isCurDomainExpired σ = false := by simp [Fl4Spec.isCurDomainExpired, hnd]
      rw [this]; rfl
    rw [hs.curSc, hk] at hy; cases hy
    rw [getScRefillSufficient_eq hk (by rw [hx.refills]; exact refills_ne hx.wf)] at hb
    have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb))).1
    rw [hs.consumed]; exact eb.trans hbt
  · simp only [Bool.not_eq_true] at hbt
    simp only [hbt, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (charge_budget_refines s a σ hS hR hN hI hscC hsc0 htw hts hidle hact hnr hnb hmrt hmb
      hval hto _ true) ?_
    rintro ⟨s1, a1⟩ ⟨σ', h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine (WP.spec_ok _).2 ⟨σ', ?_, h2, h3, h4, h5, h6, fun _ hc => by rw [h7] at hc; exact absurd hc (by decide), h8⟩
    rw [hsp, if_neg (by rw [hbt]; exact Bool.false_ne_true), nd_gets_bind, hs.consumed, nd_bind_one h1]
    rfl

/-- Restarting a runnable thread keeps the invariant. -/
theorem Inv.restart {σ : Fl4Spec.State Unit} (h : Inv σ) {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hrun : Fl4Spec.runnable x.tcbState = true) :
    Inv (stsAct (updK σ p (.tcb { x with tcbState := .restart })) p) := by
  have h1 : Inv (updK σ p (.tcb { x with tcbState := .restart })) := by
    refine h.stable (NtfnStep.tcb hk .restart x.tcbArch) fun q y z hy hz => ?_
    by_cases e : q = p
    · subst e
      rw [hk] at hy; cases hy
      simp only [updK_kheap, Function.update_self, Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hz
      subst hz
      refine Or.inr ⟨rfl, fun e => ?_, Or.inl (Or.inl hrun)⟩
      rw [e] at hrun; cases hrun
    · simp only [updK_kheap, ne_eq, e, not_false_eq_true, Function.update_of_ne] at hz
      rw [hy] at hz; cases hz; exact Or.inl rfl
  exact h1.qchange (qchange_stsAct _ _)

/-- **`check_budget_restart` refines l4v `check_budget_restart`** and keeps
the invariant. -/
theorem check_budget_restart_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = Fl4Spec.idleScPtr)
    (hact : (nodeW st s c layout.node.CUR_SC).bv ≠ Fl4Spec.idleScPtr → ∀ x n,
      σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hnr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hnb : ∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      ∀ q, xt.tcbState ≠ .blockedOnNotification q)
    (hnd : Fl4Spec.numDomains = 1)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' →
      faults.valid_timeout_handler st s' (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
        Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ' =
          ({(b, σ')}, False) ⦄)
    (hto : ∀ (s' : S) (σ' : Fl4Spec.State Unit), SchedRel st N T C c s' σ' → NtfnStateRel N T (L.mem s') σ' →
      NSC N C σ' → InvBut σ' (nodeW st s c layout.node.CUR_THREAD).bv →
      faults.handle_timeout st ar s' a (nodeW st s c layout.node.CUR_THREAD)
        (error.Fault.Timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ'',
        Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
          (.timeout (L.mem s' (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ' = ({((), σ'')}, False) ∧
        SchedRel st N T C c r.1 σ'' ∧ Inv σ'' ∧ NtfnStateRel N T (L.mem r.1) σ'' ∧ NSC N C σ'' ∧
        σ''.consumedTime = σ'.consumedTime ∧ (IdleOK σ' → IdleOK σ'') ⦄) :
    sched.check_budget_restart st ar s a ⦃ r => ∃ σ',
      Fl4Spec.checkBudgetRestart (Z := Unit) σ = ({(r.1, σ')}, False) ∧
      SchedRel st N T C c r.2.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.2.1) σ' ∧ NSC N C σ' ∧
      (CurInv σ → σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧ (OffReady σ → OffOK σ') ∧
      (ActIdle σ → ActIdle σ') ⦄ := by
  have hkp : ∃ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) := by
    obtain ⟨Q, R, hc, hs⟩ := hS.lists
    obtain ⟨x, n, hk, -⟩ := hs.scs _ hscC
    exact ⟨x, n, hk⟩
  unfold sched.check_budget_restart
  refine WP.spec_bind (check_budget_refines s a σ hS hR hN hI hscC hsc0 htw hts hidle hact hnr hnb hnd hmrt hmb
    hval hto) ?_
  rintro ⟨r, s1, a1⟩ ⟨σ1, h1, hS1, hI1, hR1, hN1, h6, ho6, hA6⟩
  have hc6 : CurInv σ → σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := fun hc =>
    h6.imp id fun hK => hc.keeps hK hkp
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  step with sched.cur_thread.spec' as ⟨ct, hct⟩
  rw [hc1.cur] at hct
  subst hct
  have hctT : nodeW st s1 c layout.node.CUR_THREAD ∈ T := hc1.curT
  obtain ⟨xt, hkt, -⟩ := hs1.tcb _ hctT
  have hsp : Fl4Spec.checkBudgetRestart (Z := Unit) σ =
      (if ¬ r = true ∧ Fl4Spec.runnable xt.tcbState = true then
        (Fl4Spec.setThreadState (nodeW st s1 c layout.node.CUR_THREAD).bv .restart >>= fun _ => pure r) σ1
      else ({(r, σ1)}, False)) := by
    unfold Fl4Spec.checkBudgetRestart
    rw [nd_bind_one h1, nd_gets_bind, hs1.curThread, nd_bind_one (getThreadState_eq hkt)]
    unfold Fl4Spec.NonDet.when
    split_ifs
    · rfl
    · rw [nd_bind_one (rfl : Fl4Spec.NonDet.pure () σ1 = ({((), σ1)}, False))]; rfl
  by_cases hr : r = true
  · simp only [hr, ↓reduceIte, WP.spec_ok]
    exact ⟨σ1, by rw [hsp, if_neg (fun h => h.1 hr), hr], hS1, hI1, hR1, hN1, hc6, ho6, hA6⟩
  · have hr' : r = false := by simpa using hr
    subst hr'
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with is_runnable_spec as ⟨b, hb⟩
    have hb' : b = Fl4Spec.runnable xt.tcbState := by
      rw [hb, Bool.eq_iff_iff, decide_eq_true_iff]; exact runnable_iff (hR1.at_tcb hctT hkt).st
    subst hb'
    by_cases hrun : Fl4Spec.runnable xt.tcbState = true
    · simp only [hrun, ↓reduceIte]
      have hv : (sched.TS_RESTART).val = tsCode .restart := by rw [tsVals.2.1]; rfl
      refine WP.spec_bind (set_thread_state_refines s1 σ1 hR1 hS1 hctT hkt
        (not_in_ntfnQueue hR1 hctT hkt hrun) _ .restart hv (fun _ h => by cases h)) ?_
      rintro s2 ⟨σ2, h2, hR2, hS2⟩
      simp only [WP.spec_ok]
      rw [setThreadState_eq _ hkt] at h2
      have e2 := pair_eq h2
      subst e2
      refine ⟨_, ?_, hS2, hI1.restart hkt hrun, hR2, fun n hn x p hx hp => ?_, fun hc => ?_,
        fun ho => (ho6 ho).restart _, fun hA => ((hA6 hA).updState hkt hrun .restart rfl).ofSts _⟩
      · rw [hsp, if_pos ⟨Bool.false_ne_true, hrun⟩, nd_bind_one (setThreadState_eq _ hkt)]; rfl
      · rw [stsAct_kheap] at hx
        have hx' : σ1.kheap n.bv = some (.notification x) := by
          by_cases e : n.bv = (nodeW st s1 c layout.node.CUR_THREAD).bv
          · rw [e] at hx; simp at hx
          · simpa [e] using hx
        exact hN1 n hn x p hx' hp
      · have e : (nodeW st s1 c layout.node.CUR_THREAD).bv = σ1.curThread := hs1.curThread.symm
        have hkt' : σ1.kheap σ1.curThread = some (.tcb xt) := e ▸ hkt
        rcases hc6 hc with h7 | h7
        · rcases stsAct_action (updK σ1 (nodeW st s1 c layout.node.CUR_THREAD).bv
            (.tcb { xt with tcbState := .restart })) (nodeW st s1 c layout.node.CUR_THREAD).bv with e' | e'
          · exact Or.inl e'
          · exact Or.inl (e'.trans h7)
        · rw [e]; exact Or.inr (h7.restart hkt')
    · simp only [Bool.not_eq_true] at hrun
      simp only [hrun, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨σ1, by rw [hsp, if_neg (fun h => by rw [hrun] at h; exact Bool.false_ne_true h.2)], hS1, hI1, hR1, hN1,
        hc6, ho6, hA6⟩

end

end

end Fl4Proofs.P3.Sched
