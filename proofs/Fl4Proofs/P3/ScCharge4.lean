/-
P3 (DESIGN.md §9), scheduling contexts: **`end_timeslice` refines l4v
`end_timeslice`** (`end_timeslice_refines`), restoring `Inv` from `InvBut`
for the current thread. The timeout-fault branch (`handle_timeout`, IPC) and
the timeout-handler test (a CSpace read) are hypotheses (`hto`, `hval`).
-/
import Fl4Proofs.P3.ScCharge3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`end_timeslice` refines `end_timeslice`.** -/
theorem end_timeslice_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    (hI : InvBut σ (nodeW st s c layout.node.CUR_THREAD).bv)
    (hsc : nodeW st s c layout.node.CUR_SC ∈ C) (hsc0 : nodeW st s c layout.node.CUR_SC ≠ 0#u64)
    (htw : L.mem s (scW (nodeW st s c layout.node.CUR_SC) 24#u64) = nodeW st s c layout.node.CUR_THREAD)
    (hts : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) = nodeW st s c layout.node.CUR_SC)
    (hsch : Fl4Spec.schedulable (nodeW st s c layout.node.CUR_THREAD).bv σ = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hval : faults.valid_timeout_handler st s (nodeW st s c layout.node.CUR_THREAD) ⦃ b =>
      Fl4Spec.isValidTimeoutHandler (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv σ = ({(b, σ)}, False) ⦄)
    (hto : faults.handle_timeout st ar s a (nodeW st s c layout.node.CUR_THREAD)
      (error.Fault.Timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64))) ⦃ r => ∃ σ',
      Fl4Spec.handleTimeout (Z := Unit) (nodeW st s c layout.node.CUR_THREAD).bv
        (.timeout (L.mem s (scW (nodeW st s c layout.node.CUR_SC) 48#u64)).bv) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄)
    (can : Bool) :
    sched.end_timeslice st ar s a can ⦃ r => ∃ σ', Fl4Spec.endTimeslice (Z := Unit) can σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
      σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscd
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hct : ct ∈ T := hc.curT
  have hrr : decide (L.rperiod s sc = 0#u64) = decide (x.scPeriod = 0) := by
    apply decide_eq_decide.2
    rw [hx.period]
    exact ⟨fun h => by rw [h]; rfl, fun h => eq_of_bv (by rw [h]; rfl)⟩
  have hrap := rap_refines s a σ hS hR hI hsc hct htw hts hsc0 hsch hmb
  obtain ⟨tx, hkt, _, _, _, _⟩ := hs.tcb ct hct
  have hst := (hR.at_tcb hct hkt).st
  have hvm : L.mem s (tStA ct) = sched.TS_RUNNING_VM ↔ tx.tcbState = .runningVM := by
    have e8 : sched.TS_RUNNING_VM = 8#u64 := by unfold sched.TS_RUNNING_VM; rfl
    have he : ∀ x y : U64, x = y ↔ x.val = y.val := fun x y => ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    rw [e8, he, hst]
    cases tx.tcbState <;> simp [tsCode]
  have hguard : (do
      let state ← obj.Tcb.state st ct s
      if state != sched.TS_RUNNING_VM then faults.valid_timeout_handler st s ct else ok false) ⦃ b =>
      (if tx.tcbState = .runningVM then pure false else Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv) σ =
        ({(b, σ)}, False) ⦄ := by
    step with Notif.obj.Tcb.state.spec as ⟨state, hstate⟩
    rw [hstate]
    by_cases hvm' : tx.tcbState = .runningVM
    · have hw := hvm.mpr hvm'
      simp [hw, hvm', pure, Fl4Spec.NonDet.pure]
    · have hw := fun e => hvm' (hvm.mp e)
      simpa only [bne_iff_ne, if_pos hw, if_neg hvm'] using hval
  have hspec : ∀ v : Bool, (if tx.tcbState = .runningVM then pure false else Fl4Spec.isValidTimeoutHandler (Z := Unit) ct.bv) σ = ({(v, σ)}, False) →
      Fl4Spec.endTimeslice (Z := Unit) can σ =
      (if can = true ∧ ¬ decide (x.scPeriod = 0) = true ∧ v = true then
        Fl4Spec.handleTimeout ct.bv (.timeout (L.mem s (scW sc 48#u64)).bv) σ
      else (do
          let ready ← Fl4Spec.getScRefillReady (Z := Unit) sc.bv
          let sufficient ← Fl4Spec.getScRefillSufficient sc.bv 0
          if ready = true ∧ sufficient = true then Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend ct.bv
          else Fl4Spec.postpone sc.bv) σ) := by
    intro v hv
    unfold Fl4Spec.endTimeslice
    rw [nd_gets_bind, hs.curSc, nd_bind_one (isRoundRobin_eq hk), nd_gets_bind, hs.curThread, nd_bind_one (getThreadState_eq hkt)]
    by_cases hvm' : tx.tcbState = .runningVM
    all_goals simp only [hvm', ↓reduceIte] at hv ⊢
    all_goals rw [nd_bind_one hv]
    all_goals split_ifs
    all_goals first | (rw [nd_bind_one (getSchedContext_eq hk), hx.badge]) | rfl
  unfold sched.end_timeslice
  step with sched.cur_sc.spec' as ⟨sc', hsc'⟩
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur] at hsc' hct'
  subst hsc' hct'
  step with sporadic.is_round_robin.spec as ⟨rr, hrr'⟩
  rw [← Aeneas.Std.bind_assoc]
  refine WP.spec_bind hguard ?_
  intro v hv
  have hA : ¬ (can = true ∧ ¬ decide (x.scPeriod = 0) = true ∧ v = true) → (do
      let b ← sporadic.ready st s sc
      if b then do
        let b1 ← sporadic.sufficient st ar s a sc 0#u64
        if b1 then do
          let s1 ← sched.append st s ct
          ok (s1, a)
        else do
          let s1 ← sched.postpone st s sc
          ok (s1, a)
      else do
        let s1 ← sched.postpone st s sc
        ok (s1, a)) ⦃ r => ∃ σ', Fl4Spec.endTimeslice (Z := Unit) can σ = ({((), σ')}, False) ∧
          SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧
          σ'.consumedTime = σ.consumedTime ∧ (IdleOK σ → IdleOK σ') ⦄ := fun hn =>
    WP.spec_mono hrap fun r ⟨_, σ', h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨σ', by rw [hspec v hv, ite_f hn]; exact h1, h2, h3, h5, hN.kview hR h4, h6, h7⟩
  by_cases hcan : can = true
  · rw [if_pos hcan]
    by_cases hr : rr = true
    · rw [if_pos hr]
      exact hA (fun h => h.2.1 (hrr ▸ hrr' ▸ hr))
    · rw [if_neg hr]
      by_cases hvv : v = true
      · rw [if_pos hvv]
        step with obj.Sc.badge.spec' as ⟨bd, hbd⟩
        subst hbd
        refine WP.spec_mono hto fun r ⟨σ', h1, h2⟩ => ⟨σ', ?_, h2⟩
        rw [hspec v hv, ite_t ⟨hcan, fun h => hr (hrr' ▸ hrr ▸ h), hvv⟩]; exact h1
      · rw [if_neg hvv]
        exact hA (fun h => hvv h.2.2)
  · rw [if_neg hcan]
    exact hA (fun h => hcan h.1)
end

end

end Fl4Proofs.P3.Sched
