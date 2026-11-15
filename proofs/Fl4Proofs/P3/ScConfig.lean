/-
P3 (DESIGN.md §9), scheduling contexts: **SchedControl `ConfigureFlags`**
against l4v `invoke_sched_control_configure_flags`.

* Spec side: `refill_new` (`refillNew_eq`), the refills `refill_new` and
  `refill_update` leave (`RefOK`, `RRok`), the reconfiguration of an SC
  whose bound thread is in no queue (`InvBut.scReconf`: `Inv` except `rd`
  for that thread, restored by `sched_context_resume`, `InvBut.resume`),
  and the invocation from its steps (`cfg_spec`).
* FL4 side: `release_remove_refines`, `refill_new_refines`, the steps
  `cfg_pre_refines` (stall, release-queue removal, dequeue, `commit_time`),
  `cfg_refill_refines`, `cfg_resume_refines` (migrate, `resume`, the switch
  or reschedule), `cfg_tail_refines` (badge, sporadic flag), and
  `configure_flags_refines`, ending in `Inv` (and `ActIdle` when the action
  is `resume_cur_thread` at entry and the SC is not the idle SC). On one
  core `remote_tcb_stall` and `migrate_tcb` do nothing (proved).
-/
import Fl4Proofs.P3.ScScheduleTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The refills `refill_new` leaves: the budget now, and an empty tail for a
round-robin SC. -/
def newRefills (now b per : Ticks) : List Refill :=
  if per = 0 then [{ rTime := now, rAmount := b }, { rTime := now, rAmount := 0 }]
  else [{ rTime := now, rAmount := b }]

/-- The SC after `refill_new`. -/
def newSC (x : SchedContext) (now : Ticks) (mr : Nat) (b per : Ticks) : SchedContext :=
  { x with scPeriod := per, scBudget := b, scRefillMax := mr, scRefills := newRefills now b per }

theorem refillNew_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (mr : Nat) (b per : Ticks) :
    refillNew (Z := Unit) p mr b per σ = ({((), updSc σ p (newSC x σ.curTime mr b per) n)}, False) := by
  have k : ∀ (z : SchedContext) (σ' : State Unit), (updSc σ' p z n).kheap p = some (.schedContext z n) :=
    fun z σ' => by simp [updK]
  unfold refillNew
  rw [nd_gets_bind, nd_bind_one (updateSchedContext_eq hk _), nd_bind_one (updateSchedContext_eq (k _ _) _),
    nd_bind_one (updateSchedContext_eq (k _ _) _), nd_pure_bind', nd_bind_one (updateSchedContext_eq (k _ _) _)]
  simp only [updSc_updSc]
  unfold maybeAddEmptyTail
  rw [nd_bind_one (isRoundRobin_eq (k _ _))]
  unfold NonDet.when
  by_cases hp : per = 0
  · simp only [scRefillsUpdate, scRefillMaxUpdate, scBudgetUpdate, scPeriodUpdate, hp, decide_true, ↓reduceIte]
    rw [nd_bind_one (getRefillHead_eq (k _ _) (by simp)), nd_pure_bind', refillAddTail_eq (k _ _), updSc_updSc]
    simp [newSC, newRefills, refillHd, Fl4Spec.the, hp]
  · simp only [scRefillsUpdate, scRefillMaxUpdate, scBudgetUpdate, scPeriodUpdate, hp, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    unfold newSC newRefills
    rw [if_neg hp]
    rfl

theorem newSC_ok (x : SchedContext) (now : Ticks) (mr : Nat) {b : Ticks} (per : Ticks) (hb : MIN_BUDGET ≤ b) :
    (per ≠ 0 → RefOK (newSC x now mr b per)) ∧ (per = 0 → RRok (newSC x now mr b per)) := by
  have hpos : 0 < b.toNat := by
    have h0 := min_budget_pos; rw [BitVec.lt_def] at h0; rw [BitVec.le_def] at hb; omega
  have hlt := b.isLt
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · unfold RefOK newSC newRefills; rw [if_neg hp]
    refine ⟨by simp, fun r hr => ?_, by simpa using hlt, by unfold refillHd; exact hb⟩
    simp only [List.mem_singleton] at hr; subst hr; exact hpos
  · unfold RRok newSC newRefills; rw [if_pos hp]
    refine ⟨by simp, by simpa using hlt, by unfold refillHd; exact hb⟩

/-- The refills `refill_update` leaves are valid for a periodic SC whose old
head held at least `MIN_BUDGET`, for a budget of at least `MIN_BUDGET`. -/
theorem rUpd_ok (x : SchedContext) {H : Refill} (now : Ticks) {np nb : Ticks} (nm : Nat)
    (hH : MIN_BUDGET ≤ H.rAmount) (hb : MIN_BUDGET ≤ nb) (hnp : np ≠ 0) :
    RefOK (rUpdY x (rUpdS H now np nb) np nb nm) := by
  have hm0 := min_budget_pos; rw [BitVec.lt_def] at hm0
  rw [BitVec.le_def] at hH hb
  unfold RefOK rUpdY rUpdS rUpdL'
  have ha : (rUpdSHd H now).rAmount = H.rAmount := rUpdSHd_amount H now
  by_cases hc : nb ≤ (rUpdSHd H now).rAmount
  · rw [if_pos hc, if_neg hnp]
    refine ⟨by simp, fun r hr => ?_, by simpa using nb.isLt, by unfold refillHd; rw [BitVec.le_def]; exact hb⟩
    simp only [List.mem_singleton] at hr; subst hr; show 0 < nb.toNat; omega
  · rw [if_neg hc]
    have hc' : H.rAmount.toNat < nb.toNat := by rw [← ha]; rw [BitVec.le_def] at hc; omega
    have hsub : (nb - (rUpdSHd H now).rAmount).toNat = nb.toNat - H.rAmount.toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ha]; omega), ha]
    refine ⟨by simp, fun r hr => ?_, ?_, by
      unfold refillHd; show MIN_BUDGET ≤ (rUpdSHd H now).rAmount; rw [BitVec.le_def, ha]; exact hH⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [ha]; omega
      · show 0 < (nb - (rUpdSHd H now).rAmount).toNat; rw [hsub]; omega
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      show (rUpdSHd H now).rAmount.toNat + ((nb - (rUpdSHd H now).rAmount).toNat + 0) < 2 ^ 64
      rw [hsub, ha]; have := nb.isLt; omega

/-- **Reconfiguring an SC whose bound thread is in no queue** keeps `Inv`
except `rd` for that thread. -/
theorem InvBut.scReconf {σ : State Unit} {p u0 : ObjRef} (h : InvBut σ u0) {y y' : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (htc : y'.scTcb = y.scTcb)
    (hne' : y'.scRefills ≠ []) (hok : scActive y' = true → y'.scPeriod ≠ 0 → RefOK y')
    (hrr : scActive y' = true → y'.scPeriod = 0 → RRok y')
    (hown : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p → u = u0)
    (hnq : NotQueued σ u0) : InvBut (updSc σ p y' m) u0 := by
  have hkp : ∀ q, q ≠ p → (updSc σ p y' m).kheap q = σ.kheap q := fun q hq => by simp [updK, hq]
  have hky : (updSc σ p y' m).kheap p = some (.schedContext y' m) := by simp [updK]
  have hnr' : ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p :=
    fun u hu x hx hp => hnq.2 (hown u x hx hp ▸ hu)
  have htcb : ∀ u x, (updSc σ p y' m).kheap u = some (.tcb x) → σ.kheap u = some (.tcb x) := fun u x hx => by
    by_cases e : u = p
    · subst e; rw [hky] at hx; cases hx
    · rw [hkp u e] at hx; exact hx
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hu0 hx hc => ?_, fun q w n hw ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w n hw => ?_, fun q w n hw => ?_⟩
  · obtain ⟨x, scp, w, n, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnq.1 d q (hown u x h1 (e ▸ h2) ▸ hu)
    exact ⟨x, scp, w, n, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · obtain ⟨x, scp, w, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnr' u hu x h1 (e ▸ h2)
    exact ⟨x, scp, w, n, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have hap : a ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hbp : b ≠ p := by rintro rfl; rw [hk] at g1; cases g1
    have hpa : pa ≠ p := fun e => hnr' a ha xa h1 (e ▸ h2)
    have hpb : pb ≠ p := fun e => hnr' b hb xb g1 (e ▸ g2)
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) (h.ne _ _ _ h4),
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) (h.ne _ _ _ g4)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4), specRt_eq g1 g2 g4 (h.ne _ _ _ g4)] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    have hsp : scp ≠ p := fun e => hu0 (hown u x hx0 (e ▸ h2))
    rw [hkp scp hsp] at h3
    exact h.rd u x hu0 hx0 hc x scp w n hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hok ha
    · rw [hkp q e] at hw; exact h.refills q w n hw ha
  · obtain ⟨w, n, h1, h2⟩ := h.back u x q (htcb u x hx) hq
    by_cases e : q = p
    · subst e; rw [hk] at h1; cases h1
      exact ⟨y', m, hky, by rw [htc]; exact h2⟩
    · exact ⟨w, n, by rw [hkp q e]; exact h1, h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hky] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, n, h1⟩ := h.ntfnSc q x q' hx0 hq
    by_cases e : q' = p
    · subst e; exact ⟨y', m, hky⟩
    · exact ⟨w, n, by rw [hkp q' e]; exact h1⟩
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hne'
    · rw [hkp q e] at hw; exact h.ne q w n hw
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hrr
    · rw [hkp q e] at hw; exact h.rr q w n hw

theorem tcbReleaseRemove_not {σ : State Unit} {t : ObjRef} (ht : t ∉ σ.releaseQueue) :
    tcbReleaseRemove (Z := Unit) t σ = ({((), σ)}, False) := by
  unfold tcbReleaseRemove
  rw [nd_gets_bind]
  unfold NonDet.when
  rw [if_neg (fun h => ht (by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil h1
    rw [e] at h2 ⊢; simp only [List.head?_cons, the_some] at h2; rw [h2]; exact List.mem_cons_self))]
  rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl), nd_pure_bind']
  unfold setReleaseQueue tcbSchedDequeue
  rw [List.filter_eq_self.2 fun a ha => by
    have : t ≠ a := fun e => ht (e ▸ ha)
    simpa using this]
  rfl

theorem tcbReleaseRemove_mid {σ : State Unit} {t : ObjRef} (hh : σ.releaseQueue.head? ≠ some t) :
    tcbReleaseRemove (Z := Unit) t σ =
      ({((), setRel σ (σ.releaseQueue.filter fun x => decide (t ≠ x)) σ.reprogramTimer)}, False) := by
  unfold tcbReleaseRemove
  rw [nd_gets_bind]
  unfold NonDet.when
  rw [if_neg (fun h => hh (by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil h1
    rw [e] at h2 ⊢; simp only [List.head?_cons, the_some] at h2; rw [h2]; rfl))]
  rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl), nd_pure_bind']
  rfl

theorem InvBut.qchange {σ σ' : State Unit} {t : ObjRef} (h : InvBut σ t) (hq : QChange σ σ') : InvBut σ' t := by
  obtain ⟨hk, hr, ht, hm⟩ := hq
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_, fun p y n hy => ?_⟩
  · rw [hk]
    rcases hm d p u hu with hu | hs
    · exact h.rq d p u hu
    · obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      exact ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩
  · rw [hr] at hu; rw [hk]; exact h.rel u hu
  · rw [hr]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, -⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, -⟩ := h.rel b hb
    rw [specRt_eq (by rw [hk]; exact h1) h2 (by rw [hk]; exact h4) (h.ne _ _ _ h4),
      specRt_eq (by rw [hk]; exact g1) g2 (by rw [hk]; exact g4) (h.ne _ _ _ g4)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4), specRt_eq g1 g2 g4 (h.ne _ _ _ g4)] at hab
    exact hab
  · rw [hk] at hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hk] at h1 h3; rw [hr] at h5
    rw [released_congr ht]
    exact h.rd u x hut hx hc x' scp y n h1 h2 h3 h4 h5
  · rw [hk] at hy; exact h.refills p y n hy
  · rw [hk] at hx ⊢; exact h.back u x p hx hp
  · rw [hk] at hx ⊢; exact h.ntfnSc q x p hx hp
  · rw [hk] at hy; exact h.ne p y n hy
  · rw [hk] at hy; exact h.rr p y n hy

/-- **Removing a thread from the release queue** keeps `Inv` except `rd` for
it. -/
theorem Inv.relRemove {σ : State Unit} (h : Inv σ) (t : ObjRef) (bb : Bool) :
    InvBut (setRel σ (σ.releaseQueue.filter fun x => decide (t ≠ x)) bb) t := by
  have hsub : ∀ u, u ∈ (σ.releaseQueue.filter fun x => decide (t ≠ x)) → u ∈ σ.releaseQueue ∧ u ≠ t :=
    fun u hu => by
      rw [List.mem_filter] at hu; exact ⟨hu.1, fun e => by subst e; simp at hu⟩
  refine ⟨h.rq, fun u hu => h.rel u (hsub u hu).1, ?_, fun u x hut hx hc => ?_, h.refills, h.back, h.ntfnSc,
    h.ne, h.rr⟩
  · have hs := h.sorted.filter (fun x => decide (t ≠ x))
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hs
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, -⟩ := h.rel a (hsub a ha).1
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, -⟩ := h.rel b (hsub b hb).1
    rw [specRt_eq (σ := setRel σ _ bb) h1 h2 h4 (h.ne _ _ _ h4), specRt_eq (σ := setRel σ _ bb) g1 g2 g4 (h.ne _ _ _ g4)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4), specRt_eq g1 g2 g4 (h.ne _ _ _ g4)] at hab
    exact hab
  · intro x' scp y n h1 h2 h3 h4 h5
    refine h.rd u x hx hc x' scp y n h1 h2 h3 h4 fun hm => h5 ?_
    show u ∈ σ.releaseQueue.filter _
    rw [List.mem_filter]; exact ⟨hm, by simpa using fun e => hut e.symm⟩

/-- **`sched_context_resume` restores `Inv`** from `Inv` except `rd` for the
bound thread `t`, in no queue, whose SC is released if `t` is in `inClass`
but not runnable. -/
theorem InvBut.resume {σ σ' : State Unit} {t p : ObjRef} (h : InvBut σ t) {x : Tcb} {y : SchedContext} {n : Nat}
    (kp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (kt : σ.kheap t = some (.tcb x))
    (hxp : x.tcbSchedContext = some p) (hnq : NotQueued σ t)
    (hr : runnable x.tcbState = false → inClass x.tcbState → scActive y = true → released σ y)
    (he : schedContextResume (Z := Unit) p σ = ({((), σ')}, False)) : Inv σ' := by
  have hne : y.scRefills ≠ [] := h.ne p y n kp
  rw [resume_spec_eq kp hyt kt hne
    (fun hs => by
      obtain ⟨x', scp, y', m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
    (fun _ => hnq.1 _ _)] at he
  split_ifs at he with hc
  · obtain ⟨x', scp, y', m, h1, h2, hrun, h4, hact, -⟩ := schedulable_inv hc.1
    rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h4; cases h4
    obtain ⟨b, hp⟩ := postpone_eq kp hyt kt (specRt σ) (fun u hu => by
      rcases hu with rfl | hu
      · exact ⟨x, p, y, n, kt, hxp, kp, hne, specRt_eq kt hxp kp hne⟩
      · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
        exact ⟨xu, scp, yu, nu, h1, h2, h4, h.ne _ _ _ h4, specRt_eq h1 h2 h4 (h.ne _ _ _ h4)⟩)
    rw [hp] at he
    rw [pair_eq he]
    exact h.postponed kt hxp hrun kp hact b
  · rw [pair_eq he]
    refine h.inv fun x' hx' hcl => ?_
    rw [kt] at hx'; cases hx'
    intro x'' scp y' m h1 h2 h3 h4 h5
    rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h3; cases h3
    cases hrun : runnable x.tcbState
    · exact hr hrun hcl h4
    · have hs := schedulable_of kt hxp hrun kp h4 h5
      have := not_and.1 hc hs
      simpa [released] using this

/-- `sched_context_resume` of a bound thread `t` keeps `Calm` and the action,
and adds at most `t` to the release queue. -/
theorem resume_keep {σ σ' : State Unit} {t p : ObjRef} (h : InvBut σ t) {x : Tcb} {y : SchedContext} {n : Nat}
    (kp : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (kt : σ.kheap t = some (.tcb x))
    (hxp : x.tcbSchedContext = some p) (hnq : NotQueued σ t)
    (he : schedContextResume (Z := Unit) p σ = ({((), σ')}, False)) :
    Calm σ σ' ∧ σ'.schedulerAction = σ.schedulerAction ∧ ∀ u ∈ σ'.releaseQueue, u = t ∨ u ∈ σ.releaseQueue := by
  have hne : y.scRefills ≠ [] := h.ne p y n kp
  rw [resume_spec_eq kp hyt kt hne
    (fun hs => by
      obtain ⟨x', scp, y', m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
      rw [kt] at h1; cases h1; rw [hxp] at h2; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
    (fun _ => hnq.1 _ _)] at he
  split_ifs at he with hc
  · obtain ⟨b, hp⟩ := postpone_eq kp hyt kt (specRt σ) (fun u hu => by
      rcases hu with rfl | hu
      · exact ⟨x, p, y, n, kt, hxp, kp, hne, specRt_eq kt hxp kp hne⟩
      · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
        exact ⟨xu, scp, yu, nu, h1, h2, h4, h.ne _ _ _ h4, specRt_eq h1 h2 h4 (h.ne _ _ _ h4)⟩)
    rw [hp] at he
    rw [pair_eq he]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun u hu => mem_specInsT.1 hu⟩
  · rw [pair_eq he]
    exact ⟨Calm.refl σ, rfl, fun u hu => Or.inr hu⟩

/-- An SC's fields other than its refills, refill max, period and TCB
replaced keep `Inv`. -/
theorem Inv.scFields {σ : State Unit} (h : Inv σ) {p : ObjRef} {y y' : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (e1 : y'.scRefills = y.scRefills)
    (e2 : y'.scRefillMax = y.scRefillMax) (e3 : y'.scPeriod = y.scPeriod) (e4 : y'.scTcb = y.scTcb) :
    Inv (updSc σ p y' m) := by
  refine ((h.toBut p).scUpd hk e1 e2 e3 e4).inv fun x hx => ?_
  simp [updK] at hx

/-- `invoke_sched_control_configure_flags`'s refill step (without the
continuation). -/
def cfgRefill (p : ObjRef) (tcbOpt : Option ObjRef) (b per : Ticks) (mr : Nat) : SMonad Unit Unit :=
  if per = b then refillNew p MIN_REFILLS b 0
  else do
    let active ← getScActive p
    if active = true ∧ tcbOpt ≠ none then do
      let tcbPtr ← NonDet.assertOpt tcbOpt
      let st ← getThreadState tcbPtr
      if runnable st = true then refillUpdate p per b mr else refillNew p mr b per
    else refillNew p mr b per

/-- `invoke_sched_control_configure_flags`'s step after the refills. -/
def cfgResume (p : ObjRef) (tcbOpt : Option ObjRef) : SMonad Unit Unit :=
  NonDet.when (tcbOpt ≠ none) do
    schedContextResume p
    let tcbPtr ← NonDet.assertOpt tcbOpt
    let st ← getThreadState tcbPtr
    let ct ← NonDet.gets fun s : State Unit => s.curThread
    if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr)

/-- `invoke_sched_control_configure_flags`'s first step. -/
def cfgPre (p : ObjRef) (tcbOpt : Option ObjRef) : SMonad Unit Unit :=
  NonDet.when (tcbOpt ≠ none) do
    let tcbPtr ← NonDet.assertOpt tcbOpt
    tcbReleaseRemove tcbPtr
    tcbSchedAction tcbSchedDequeue tcbPtr
    let curSc ← NonDet.gets fun s : State Unit => s.curSc
    NonDet.when (curSc = p) commitTime

/-- **`invoke_sched_control_configure_flags` from its steps.** -/
theorem cfg_spec {σ σ1 σ2 σ3 σ4 σ5 : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {b per : Ticks} {mr : Nat} {bd fl : Data}
    (h1 : cfgPre p x.scTcb σ = ({((), σ1)}, False)) {y1 : SchedContext} {n1 : Nat}
    (hk1 : σ1.kheap p = some (.schedContext y1 n1))
    (htcb : ∀ t, x.scTcb = some t → ∃ xt, σ1.kheap t = some (.tcb xt))
    (h2 : cfgRefill p x.scTcb b per mr σ1 = ({((), σ2)}, False))
    (h3 : cfgResume p x.scTcb σ2 = ({((), σ3)}, False))
    (h4 : setScObjRef (Z := Unit) scBadgeUpdate p bd σ3 = ({((), σ4)}, False))
    (h5 : setScObjRef (Z := Unit) scSporadicUpdate p (testBit fl scSporadicFlag) σ4 = ({((), σ5)}, False)) :
    invokeSchedControlConfigureFlags (Z := Unit) (.invokeSchedControlConfigureFlags p b per mr bd fl) σ =
      ({((), σ5)}, False) := by
  have tail : ((do
      cfgResume p x.scTcb
      setScObjRef (Z := Unit) scBadgeUpdate p bd
      setScObjRef (Z := Unit) scSporadicUpdate p (testBit fl scSporadicFlag)) : SMonad Unit Unit) σ2 =
      ({((), σ5)}, False) := by
    rw [nd_bind_one h3, nd_bind_one h4]; exact h5
  unfold invokeSchedControlConfigureFlags
  dsimp only
  rw [nd_bind_one (getSchedContext_eq hk)]
  unfold cfgPre at h1
  rw [nd_bind_one h1]
  unfold cfgRefill at h2
  unfold cfgResume at tail
  by_cases e : per = b
  · rw [if_pos e] at h2 ⊢; rw [nd_bind_one h2]; exact tail
  · rw [if_neg e] at h2 ⊢
    rw [nd_bind_one (getScActive_eq hk1)] at h2 ⊢
    split_ifs at h2 ⊢ with hc
    · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 hc.2
      obtain ⟨xt, hkt⟩ := htcb t ht
      rw [ht, nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ1 = ({(t, σ1)}, False) from rfl),
        nd_bind_one (getThreadState_eq hkt)] at h2 ⊢
      split_ifs at h2 ⊢
      · rw [nd_bind_one h2]; rw [ht] at tail; exact tail
      · rw [nd_bind_one h2]; rw [ht] at tail; exact tail
    · rw [nd_bind_one h2]; exact tail

theorem InvBut.headMin {σ : State Unit} {t : ObjRef} (h : InvBut σ t) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true) : MIN_BUDGET ≤ (refillHd y).rAmount := by
  by_cases hp : y.scPeriod = 0
  · exact (h.rr p y n hk ha hp).2.2
  · exact (h.refills p y n hk ha hp).2.2.2

theorem newSC_released {σ : State Unit} (x : SchedContext) (mr : Nat) {b : Ticks} (per : Ticks)
    (hb : MIN_BUDGET ≤ b) : released σ (newSC x σ.curTime mr b per) := by
  have hd : refillHd (newSC x σ.curTime mr b per) = { rTime := σ.curTime, rAmount := b } := by
    unfold refillHd newSC newRefills; split <;> rfl
  refine ⟨?_, ?_⟩ <;> rw [hd]
  · show decide (σ.curTime + 0 ≤ σ.curTime) = true; simp
  · exact suff0_of hb

/-- **`possible_switch_to` of a runnable thread bound to an active SC keeps
`Inv`** (it does nothing if the thread is released). -/
theorem Inv.psw {σ σ' : State Unit} (h : Inv σ) {t p : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some p) (hrun : runnable x.tcbState = true)
    (hkp : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) :
    Inv σ' ∧ σ'.kheap = σ.kheap ∧ σ'.curThread = σ.curThread := by
  by_cases hr : t ∈ σ.releaseQueue
  · rw [possibleSwitchTo_unfold hk, if_neg (fun h => h.2 (by simp [inReleaseQueue, hr]))] at he
    rw [pair_eq he]; exact ⟨h, rfl, rfl⟩
  · have hs := schedulable_of hk hsc hrun hkp ha hr
    have hq := possibleSwitchTo_qchange h hs he
    exact ⟨h.qchange hq, hq.1, (possibleSwitchTo_calm h hs he).2.1⟩

/-- `possible_switch_to` of a runnable thread bound to an active SC keeps
`ActIdle`. -/
theorem ActIdle.psw {σ σ' : State Unit} (hA : ActIdle σ) (h : Inv σ) {t p : ObjRef} {x : Tcb} {y : SchedContext}
    {n : Nat} (hk : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some p) (hrun : runnable x.tcbState = true)
    (hkp : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true)
    (he : Fl4Spec.possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) : ActIdle σ' := by
  by_cases hr : t ∈ σ.releaseQueue
  · rw [possibleSwitchTo_unfold hk, if_neg (fun h => h.2 (by simp [inReleaseQueue, hr]))] at he
    rw [pair_eq he]; exact hA
  · exact hA.possibleSwitchTo h (schedulable_of hk hsc hrun hkp ha hr) he

end Spec


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `refill_new`'s ring as a list. -/
def newL (now b p : U64) : List sporadic.Refill :=
  if p = 0#u64 then [⟨now, b⟩, ⟨now, 0#u64⟩] else [⟨now, b⟩]
/-- `release_remove` of a release-queue member that is not the head leaves
`REPROGRAM` alone. -/
theorem release_remove_norepr {T : Set U64} (s : S) (t : U64) (xs : List U64) (hT : TcbPlaced T) (ht : t ∈ T)
    (hN : NodePlaced st T s (L.mem s (affA t))) (hN' : NodePlaced st T s (L.cpu s))
    (h : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) xs)
    (hq1 : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64) (htx : t ∈ xs)
    (hhd : L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.RELEASE_HEAD) ≠ t) :
    sched.release_remove st s t ⦃ s' =>
      L.mem s' (L.nodeAt s' (L.mem s (affA t)) layout.node.REPROGRAM) =
        L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.REPROGRAM) ⦄ := by
  unfold sched.release_remove
  step as ⟨b, b_post⟩
  have hb : b = true := by rw [b_post]; exact decide_eq_true hq1
  simp only [hb, ↓reduceIte]
  step as ⟨cpu, cpu_post⟩
  step as ⟨i, i_post⟩
  subst cpu_post
  rw [if_neg (by rw [i_post]; exact hhd)]
  simp only [bind_ok]
  refine WP.spec_mono (release_remove_tail s _ t xs hT ht hN h htx) ?_
  intro s' hw
  exact node_qfoot hT h.mem hN hN' ht hw hN (by rw [repr_val]; omega) (by rw [repr_val])
    (fun _ => by rw [repr_val]; simp [RelHT]) (fun _ => by rw [repr_val]; omega)

/-- **`release_remove` refines `tcb_release_remove`**, for any thread. -/
theorem release_remove_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => ∃ σ', Fl4Spec.tcbReleaseRemove (Z := Unit) t.bv σ =
      ({((), σ')}, False) ∧ (∃ b, σ' = setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) b) ∧
      FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  by_cases htR : t ∈ R
  · obtain ⟨a, R0, hR⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem htR)
    by_cases ha : a = t
    · subst ha
      have hq : σ.releaseQueue = a.bv :: R0.map UScalar.bv := by rw [hs.rel, hR]; rfl
      refine WP.spec_mono (release_remove_head_refines s σ hS ht hq) ?_
      rintro s' ⟨h1, h2, h3⟩
      have hnd := hc.release.nodup
      rw [hR] at hnd
      have hflt : (σ.releaseQueue.filter fun x => decide (a.bv ≠ x)) = R0.map UScalar.bv := by
        rw [hq]; exact filter_ne_head (by rw [mem_map_bv]; exact (List.nodup_cons.1 hnd).1)
      exact ⟨_, h1, ⟨true, by rw [hflt]⟩, h2, h3⟩
    · -- in the queue, not the head
      have hT := hc.tcbs
      have haf := hc.aff t ht
      have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
      have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
      have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
      have hq1 := (hc.released t ht).2 htR
      have hhd : L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.RELEASE_HEAD) ≠ t := by
        have := hrel.head; rw [hR] at this; rw [show L.mem s (L.nodeAt s (L.mem s (affA t)) layout.node.RELEASE_HEAD) =
          (L.relQ s (L.mem s (affA t))).head from rfl, this]; exact ha
      have hhd' : σ.releaseQueue.head? ≠ some t.bv := by
        rw [hs.rel, hR]; simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
        exact fun e => ha (eq_of_bv e)
      have hW : ∀ w ∈ R, w ∈ T := hc.release.mem
      have h1 := sched.release_remove.rel s t R hT ht hN hrel (fun _ => htR)
      have h2 := sched.release_remove.foot s t R hT ht hN hN' hrel (fun _ => htR)
      have h3 := release_remove_norepr s t R hT ht hN hN' hrel hq1 htR hhd
      refine WP.spec_mono (WP.spec_and h1 (WP.spec_and h2 h3)) ?_
      rintro s' ⟨hRc, ⟨hw, hinq⟩, hrp⟩
      rw [if_pos hq1] at hRc hinq
      rw [haf] at hRc hw hrp
      have hnd := hc.release.nodup
      have hflt : (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) = (R.erase t).map UScalar.bv := by
        rw [hs.rel, List.filter_map, List.Nodup.erase_eq_filter hnd]
        congr 1
        apply List.filter_congr
        intro y _
        by_cases e : y = t
        · subst e; simp
        · have : t.bv ≠ y.bv := fun h => e (eq_of_bv h).symm
          simp [e, this]
      refine ⟨_, tcbReleaseRemove_mid hhd', ⟨σ.reprogramTimer, rfl⟩, qfoot_footEq hS hc ht hW hw, ?_⟩
      have := hS.rstep hc hs ht (W := R) (R' := R.erase t) (tIn := False) (fun w hw => Or.inr hw)
        (fun _ hm => hc.excl t ht hm htR) hw hRc
        (fun y => by
          rw [List.Nodup.mem_erase_iff hnd]
          constructor
          · rintro ⟨hne, hy⟩; exact Or.inr ⟨hne, hy⟩
          · rintro (⟨-, h⟩ | ⟨hne, hy⟩)
            · exact h.elim
            · exact ⟨hne, hy⟩)
        (by rw [hinq, andn_qr_qr]; simp) (by rw [hinq, andn_qr_qq]) (fun h => h.elim)
      have e1 : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM := hrp
      rw [e1, ← hS.repr, ← hflt] at this
      exact this
  · have hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra h; exact htR ((hc.released t ht).1 h)
    have htR' : t.bv ∉ σ.releaseQueue := by rw [hs.rel, mem_map_bv]; exact htR
    unfold sched.release_remove
    step with sched.in_release_queue.spec as ⟨b, hb⟩
    have hb' : b = false := by rw [hb]; exact decide_eq_false (not_not.2 hr0)
    simp only [hb', Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, tcbReleaseRemove_not htR', ⟨σ.reprogramTimer, ?_⟩, FootEq.rfl', hS⟩
    rw [List.filter_eq_self.2 fun a ha => by
      have : t.bv ≠ a := fun e => htR' (e ▸ ha)
      simpa using this]
    rfl

theorem obj.Sc.set_badge.spec2 (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_badge st sc s v ⦃ s' => s' = L.wr s (scW sc 48#u64) v ⦄ := by
  unfold obj.Sc.set_badge; step*; simp_all [scW, layout.sc.BADGE]
theorem obj.Sc.set_sporadic.spec2 (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_sporadic st sc s v ⦃ s' => s' = L.wr s (scW sc 64#u64) v ⦄ := by
  unfold obj.Sc.set_sporadic; step*; simp_all [scW, layout.sc.SPORADIC]
theorem obj.Sc.set_cpu.spec2 (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_cpu st sc s v ⦃ s' => s' = L.wr s (scW sc 16#u64) v ⦄ := by
  unfold obj.Sc.set_cpu; step*; simp_all [scW, layout.sc.CORE]

/-- Writing an SC's badge word. -/
theorem SchedRel.set_sc_badge {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scW sc 48#u64) v) (updSc σ sc.bv { x with scBadge := v.bv } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scW sc 48#u64) v)) ∧
      KView σ (updSc σ sc.bv { x with scBadge := v.bv } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 48#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 48#u64) v) sc { x with scBadge := v.bv } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hv],
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.sporadic, by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx',
    scin_footEq hS hsc hwr, KView.of_sc hk⟩

/-- Writing an SC's sporadic word. -/
theorem SchedRel.set_sc_sporadic {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (v : U64) :
    SchedRel st N T C c (L.wr s (scW sc 64#u64) v)
        (updSc σ sc.bv { x with scSporadic := decide (v ≠ 0#u64) } n) ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (scW sc 64#u64) v)) ∧
      KView σ (updSc σ sc.bv { x with scSporadic := decide (v ≠ 0#u64) } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨hW', ep, em, hrs, hw, hv, hwr⟩ := hx.wr_hdr (K := 64#u64) (by simp [HdrK]) v
  have hx' : ScRel1 st (L.wr s (scW sc 64#u64) v) sc { x with scSporadic := decide (v ≠ 0#u64) } n :=
    ⟨hW', by rw [ep]; exact hx.period, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.consumed,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.tcb, by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.ntfn,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.badge,
      by rw [hw _ (by simp) (by simp) (by decide)]; exact hx.yieldFrom,
      by rw [hv], by rw [em]; exact hx.max,
      by rw [hrs]; exact hx.refills⟩
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hw _ (by simp) (by simp) (by decide)) _ hx',
    scin_footEq hS hsc hwr, KView.of_sc hk⟩

/-- **FL4's `refill_new`**: writes inside the object, keeps the header words
other than the period, the ring size and the ring indices, and leaves the
ring `newL`. -/
theorem refill_new_fl4 {s : S} {sc : U64} {n : Nat} (hW : RefillsWF st s sc n) (m b p : U64)
    (hm2 : 2 ≤ m.val) (hmx : m.val ≤ absMax n)
    (hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ ¬ ScObj sc n (L.nodeA s layout.node.CUR_TIME)) :
    sporadic.refill_new st s sc m b p ⦃ s' => WritesIn st s s' (ScObj sc n) ∧ RefillsWF st s' sc n ∧
      L.rperiod s' sc = p ∧ L.rmax s' sc = m ∧ L.refills s' sc = newL (L.curTime s) b p ∧
      ∀ K : U64, K.val < 96 → K.val % 8 = 0 → K.val ≠ 0 → K.val ≠ 72 → K.val ≠ 80 → K.val ≠ 88 →
        L.mem s' (scW sc K) = L.mem s (scW sc K) ⦄ := by
  have hP := hW.placed
  obtain ⟨h8, hb, hfit⟩ := hP.bounds hm2 hmx
  obtain ⟨-, hpA, hmA, hhA, htA, -⟩ := hW.inside
  let RW : U64 → Prop := fun a => ScObj sc n a ∧ ¬ ∃ K : U64, K.val < 96 ∧ K.val % 8 = 0 ∧ K.val ≠ 0 ∧
    K.val ≠ 72 ∧ K.val ≠ 80 ∧ K.val ≠ 88 ∧ a = scW sc K
  have hRW : ∀ a : U64, sc.val ≤ a.val → a.val < sc.val + 96 + 16 * m.val →
      (a.val = sc.val ∨ a.val = sc.val + 72 ∨ a.val = sc.val + 80 ∨ a.val = sc.val + 88 ∨ sc.val + 96 ≤ a.val) →
      RW a := by
    intro a h1 h2 h3
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rintro ⟨K, hK, -, h0, h72, h80, h88, rfl⟩
    rw [scW_val (by omega)] at h3; omega
  have wH : ∀ {s0 : S} {a v : U64}, (a = periodA sc ∨ a = maxA sc ∨ a = headA sc ∨ a = tailA sc) →
      WritesIn st s0 (L.wr s0 a v) RW := by
    intro s0 a v ha
    have hv : a.val = sc.val ∨ a.val = sc.val + 72 ∨ a.val = sc.val + 80 ∨ a.val = sc.val + 88 := by
      rcases ha with rfl | rfl | rfl | rfl <;> omega
    have hal : Aligned a := by unfold Aligned; rcases hv with h | h | h | h <;> rw [h] <;> omega
    refine (writesIn_wr hal).mono fun b' hb' => ?_
    subst hb'; exact hRW _ (by omega) (by omega) (by omega)
  have wR : ∀ {s0 s1 : S} {k : Nat}, L.rmax s0 sc = m → RingAt st s0 s1 sc k → WritesIn st s0 s1 RW := by
    intro s0 s1 k hm h
    refine h.w.mono fun b' hb' => ?_
    rcases hb' with rfl | rfl | ⟨h1, h2⟩
    · exact hRW _ (by omega) (by omega) (by omega)
    · exact hRW _ (by omega) (by omega) (by omega)
    · rw [hm] at h2; exact hRW _ (by omega) h2 (by omega)
  have hfin : ∀ {s' : S}, WritesIn st s s' RW → WritesIn st s s' (ScObj sc n) ∧
      ∀ K : U64, K.val < 96 → K.val % 8 = 0 → K.val ≠ 0 → K.val ≠ 72 → K.val ≠ 80 → K.val ≠ 88 →
        L.mem s' (scW sc K) = L.mem s (scW sc K) := by
    intro s' hw
    refine ⟨hw.mono fun _ h => h.1, fun K h1 h2 h3 h4 h5 h6 => hw.mem_eq ?_ fun h => h.2 ⟨K, h1, h2, h3, h4, h5, h6, rfl⟩⟩
    unfold Aligned; rw [scW_val (by omega)]; omega
  have hctRW : ¬ RW (L.nodeA s layout.node.CUR_TIME) := fun h => hct.2 h.1
  unfold sporadic.refill_new
  step with obj.Sc.set_period.spec as ⟨s1, s1_post⟩
  step with obj.Sc.set_refill_head.spec as ⟨s2, s2_post⟩
  step with obj.Sc.set_refill_tail.spec as ⟨s3, s3_post⟩
  step with obj.Sc.set_refill_max.spec as ⟨s4, s4_post⟩
  have hW4 : RefillsWF st s4 sc n := by subst s4_post s3_post s2_post; exact RefillsWF.reset hP (by simpa using hm2) hmx
  have hh4 : L.rhead s4 sc = 0#u64 := by
    subst s4_post s3_post s2_post; rw [rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8]
  have hm4 : L.rmax s4 sc = m := by subst s4_post; rw [rmax_wr_max h8]
  have hp4 : L.rperiod s4 sc = p := by
    subst s4_post s3_post s2_post s1_post; rw [rperiod_wr_max h8, rperiod_wr_tail h8, rperiod_wr_head h8,
      rperiod_wr_period h8]
  have hs4 : L.size s4 sc = 1 := by
    subst s4_post s3_post s2_post
    simp only [LawfulStore.size, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8,
      rtail_wr_max h8, rtail_wr_tail h8]; simp [ringN]
  have hw4 : WritesIn st s s4 RW := by
    have w1 : WritesIn st s s1 RW := by rw [s1_post]; exact wH (Or.inl rfl)
    have w2 : WritesIn st s1 s2 RW := by rw [s2_post]; exact wH (Or.inr (Or.inr (Or.inl rfl)))
    have w3 : WritesIn st s2 s3 RW := by rw [s3_post]; exact wH (Or.inr (Or.inr (Or.inr rfl)))
    have w4 : WritesIn st s3 s4 RW := by rw [s4_post]; exact wH (Or.inr (Or.inl rfl))
    exact wIn_trans (wIn_trans (wIn_trans w1 w2) w3) w4
  have hct4 : L.curTime s4 = L.curTime s := by
    simp only [LawfulStore.curTime]
    rw [show L.nodeA s4 layout.node.CUR_TIME = L.nodeA s layout.node.CUR_TIME by
      simp only [LawfulStore.nodeA, LawfulStore.nodeAt, hw4.1, hw4.2.1]]
    exact hw4.mem_eq hct.1 hctRW
  step with sporadic.cur_time.spec as ⟨now, now_post⟩
  rw [hct4] at now_post
  subst now_post
  have h0 : (0#u64).val < (L.rmax s4 sc).val := by rw [hm4]; simp; omega
  step with sporadic.put.spec as ⟨s5, s5_post⟩
  subst s5_post
  set s5 := L.putS s4 sc 0#u64 ⟨L.curTime s, b⟩ with hs5d
  have h5 : RingAt st s4 s5 sc n := (RingAt.refl hW4).putS h0 _
  have hm5 : L.rmax s5 sc = m := h5.mx.trans hm4
  have hrs5 : L.refills s5 sc = [⟨L.curTime s, b⟩] := by
    have hsz : L.size s5 sc = 1 := by rw [hs5d, hW4.size_putS h0, hs4]
    unfold LawfulStore.refills; rw [hsz]
    simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [LawfulStore.rf, h5.wf.ix_zero, hs5d, rhead_putS h8 (by simp; omega), hh4, refill_putS_same h8]
  have alP : Aligned (scW sc 0#u64) := by unfold Aligned; rw [scW_val (by simp; omega)]; simp; omega
  have per : ∀ {s' : S}, RingAt st s4 s' sc n → L.rperiod s' sc = p := by
    intro s' h'
    have := h'.hdr (K := 0#u64) (by simp) (by simp) alP
    simp only [LawfulStore.rperiod, periodA_eq] at hp4 ⊢; rw [this]; exact hp4
  unfold sporadic.maybe_add_empty_tail
  step with sporadic.is_round_robin.spec as ⟨rr, rr_post⟩
  rw [per h5] at rr_post
  split
  · rename_i hrr
    have hp0 : p = 0#u64 := by rw [rr_post] at hrr; simpa using hrr
    step with sporadic.head.spec as ⟨r, r_post⟩
    have er : r = ⟨L.curTime s, b⟩ := by rw [r_post, head_eq' h5.wf, hrs5]; rfl
    have hsz5 : L.size s5 sc = 1 := by rw [← refills_length, hrs5]; rfl
    refine WP.spec_mono (add_tail_ring h5 (by rw [hsz5, h5.mx, hm4]; omega) _) ?_
    rintro s' ⟨h', e'⟩
    obtain ⟨hw, hK⟩ := hfin (wIn_trans hw4 (wR hm4 h'))
    refine ⟨hw, h'.wf, per h', h'.mx.trans hm4, ?_, hK⟩
    rw [e', hrs5, er]; unfold newL; rw [if_pos hp0]; rfl
  · rename_i hrr
    have hp0 : ¬ p = 0#u64 := by rw [rr_post] at hrr; simpa using hrr
    rw [WP.spec_ok]
    obtain ⟨hw, hK⟩ := hfin (wIn_trans hw4 (wR hm4 h5))
    refine ⟨hw, h5.wf, per h5, hm5, ?_, hK⟩
    rw [hrs5]; unfold newL; rw [if_neg hp0]

theorem newL_map (now b p : U64) : (newL now b p).map toRefill = newRefills now.bv b.bv p.bv := by
  unfold newL newRefills
  by_cases e : p = 0#u64
  · have e' : p.bv = 0 := by rw [e]; rfl
    rw [if_pos e, if_pos e']; rfl
  · have e' : ¬ p.bv = 0 := fun h => e (eq_of_bv (by rw [h]; rfl))
    rw [if_neg e, if_neg e']; rfl

/-- **`refill_new` refines `refill_new`.** -/
theorem refill_new_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (m b p : U64) (hm2 : 2 ≤ m.val) (hmx : m.val ≤ absMax n) :
    sporadic.refill_new st s sc m b p ⦃ s' => ∃ σ', Fl4Spec.refillNew (Z := Unit) sc.bv m.val b.bv p.bv σ =
      ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧
      σ' = updSc σ sc.bv (newSC x σ.curTime m.val b.bv p.bv) n ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  have hN := hc.node
  have hnA : L.nodeA s layout.node.CUR_TIME = L.nodeAt s c layout.node.CUR_TIME := by
    simp only [LawfulStore.nodeA, hc.cur]
  have h48 : layout.node.CUR_TIME.val = 48 := by simp [layout.node.CUR_TIME]
  have hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ ¬ ScObj sc n (L.nodeA s layout.node.CUR_TIME) := by
    rw [hnA]
    refine ⟨nodeAt_aligned hN (by omega) (by omega), fun hin => ?_⟩
    have := (hS.scOut sc hsc x n hk _ hin).2.1
    rw [nodeAt_val hN (by omega)] at this; omega
  refine WP.spec_mono (refill_new_fl4 hx.wf m b p hm2 hmx hct) ?_
  rintro s' ⟨hw, hW', hp', hm', hr', hK⟩
  have htm : σ.curTime = (L.curTime s).bv := by rw [hs.curTime, curTime_eq hc]
  have e := fun K : U64 => hK K
  have hx' : ScRel1 st s' sc (newSC x σ.curTime m.val b.bv p.bv) n :=
    ⟨hW', by rw [hp']; rfl, by rw [e 8#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.consumed,
      by rw [e 24#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.tcb,
      by rw [e 40#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.ntfn,
      by rw [e 48#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.badge,
      by rw [e 56#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.yieldFrom,
      by rw [e 64#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hx.sporadic,
      by rw [hm']; rfl, by
        show newRefills σ.curTime b.bv p.bv = _
        rw [hr', newL_map, htm]⟩
  have h32 : L.mem s' (scW sc 32#u64) = L.mem s (scW sc 32#u64) :=
    e 32#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  refine ⟨updSc σ sc.bv (newSC x σ.curTime m.val b.bv p.bv) n, refillNew_eq hk _ _ _, ?_,
    scobj_footEq hS hsc hk hw, KView.of_sc hk, rfl,
    WritesIn.kfoot_of_scobj hsc hk hw (by rw [scReplyA_eq']; exact h32)⟩
  exact hS.sc_update hsc hk hw (e 16#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) _ hx'



/-- **`configure_flags`' refill step** refines `invoke_sched_control_configure_flags`'
(`cfgRefill`), keeping `Inv` except `rd` for the bound thread `u0`; the new
SC is active and, unless its thread is runnable, released. -/
theorem cfg_refill_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) {u0 : Fl4Spec.ObjRef} (hI : InvBut σ u0)
    {p : U64} (hp : p ∈ C) {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n))
    (hown : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p.bv → u = u0) (hnq : NotQueued σ u0)
    {i : U64} (hi : y.scTcb = optRef i) (hiT : i ≠ 0#u64 → i ∈ T)
    (cpu budget period mr : U64) (hcpu : cpu = c) (hm2 : 2 ≤ mr.val) (hmx : mr.val ≤ absMax n)
    (hb : Fl4Spec.MIN_BUDGET ≤ budget.bv) (hbp : budget.val ≤ period.val) (hmx2 : 2 ≤ absMax n) :
    (if budget = period then sporadic.refill_new st s p sporadic.MIN_REFILLS budget 0#u64
      else do
        let i1 ← obj.Sc.cpu st p s
        if cpu = i1 then
          let b1 ← sporadic.sc_active st s p
          if b1 then
            if decide (i = 0#u64) then sporadic.refill_new st s p mr budget period
            else
              let b2 ← sched.is_runnable st s i
              if b2 then sporadic.refill_update st s p period budget mr
              else sporadic.refill_new st s p mr budget period
          else sporadic.refill_new st s p mr budget period
        else sporadic.refill_new st s p mr budget period) ⦃ s' => ∃ σ' y',
      cfgRefill p.bv y.scTcb budget.bv period.bv mr.val σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ InvBut σ' u0 ∧
      σ' = updSc σ p.bv y' n ∧ y'.scTcb = y.scTcb ∧ Fl4Spec.scActive y' = true ∧
      (∀ t xt, y.scTcb = some t → σ.kheap t = some (.tcb xt) → Fl4Spec.runnable xt.tcbState = false →
        released σ' y') ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs p hp
  rw [hk] at hk'; cases hk'
  -- `refill_new` with any arguments
  have NEW : ∀ (m b0 per0 : U64), 2 ≤ m.val → m.val ≤ absMax n → Fl4Spec.MIN_BUDGET ≤ b0.bv →
      sporadic.refill_new st s p m b0 per0 ⦃ s' => ∃ σ' y', Fl4Spec.refillNew (Z := Unit) p.bv m.val b0.bv per0.bv σ =
        ({((), σ')}, False) ∧ SchedRel st N T C c s' σ' ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧
        InvBut σ' u0 ∧ σ' = updSc σ p.bv y' n ∧ y'.scTcb = y.scTcb ∧ Fl4Spec.scActive y' = true ∧
        (∀ t xt, y.scTcb = some t → σ.kheap t = some (.tcb xt) → Fl4Spec.runnable xt.tcbState = false →
          released σ' y') ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
    intro m b0 per0 h2 hx2 hb0
    refine WP.spec_mono (refill_new_refines s σ hS hp hk m b0 per0 h2 hx2) ?_
    rintro s' ⟨σ', h1, h2', h3, h4, rfl, hw⟩
    have hact : Fl4Spec.scActive (newSC y σ.curTime m.val b0.bv per0.bv) = true := by
      show decide (0 < m.val) = true; simp; omega
    obtain ⟨ok1, ok2⟩ := newSC_ok y σ.curTime m.val per0.bv hb0
    refine ⟨_, _, h1, h2', h3, h4, hI.scReconf hk rfl (by unfold newSC newRefills; split <;> simp)
      (fun _ hp => ok1 hp) (fun _ hp => ok2 hp) hown hnq, rfl, rfl, hact, fun _ _ _ _ _ => ?_, hw⟩
    exact newSC_released (σ := updSc σ p.bv _ n) y m.val per0.bv hb0
  have hmin : (sporadic.MIN_REFILLS).val = 2 := by unfold sporadic.MIN_REFILLS; rfl
  by_cases hbe : budget = period
  · rw [if_pos hbe]
    refine WP.spec_mono (NEW sporadic.MIN_REFILLS budget 0#u64 (by rw [hmin]) (by rw [hmin]; exact hmx2) hb) ?_
    rintro s' ⟨σ', y', h1, rest⟩
    refine ⟨σ', y', ?_, rest⟩
    unfold cfgRefill; rw [if_pos (by rw [hbe])]
    rw [hmin] at h1; exact h1
  · rw [if_neg hbe]
    have hbe' : ¬ period.bv = budget.bv := fun e => hbe (eq_of_bv e).symm
    step with obj.Sc.cpu.spec as ⟨i1, hi1⟩
    have hc1 : i1 = c := by
      rw [hi1, show scCoreA p = scW p 16#u64 by unfold scCoreA scW layout.sc.CORE; rfl]; exact hS.core p hp
    subst hc1 hcpu
    simp only [↓reduceIte]
    step with sc_active_spec as ⟨b1, hb1⟩
    have hab : b1 = Fl4Spec.scActive y := by
      rw [hb1]; show _ = decide (0 < y.scRefillMax)
      apply decide_eq_decide.2; rw [← hx.max]; rfl
    subst hab
    have hspec : ∀ (σ' : Fl4Spec.State Unit), (if Fl4Spec.scActive y = true ∧ y.scTcb ≠ none then (do
          let tcbPtr ← Fl4Spec.NonDet.assertOpt y.scTcb
          let st ← Fl4Spec.getThreadState tcbPtr
          if Fl4Spec.runnable st = true then Fl4Spec.refillUpdate p.bv period.bv budget.bv mr.val
          else Fl4Spec.refillNew p.bv mr.val budget.bv period.bv)
        else Fl4Spec.refillNew p.bv mr.val budget.bv period.bv) σ = ({((), σ')}, False) →
        cfgRefill p.bv y.scTcb budget.bv period.bv mr.val σ = ({((), σ')}, False) := by
      intro σ' h; unfold cfgRefill; rw [if_neg hbe', nd_bind_one (getScActive_eq hk)]; exact h
    have hnew := NEW mr budget period hm2 hmx hb
    by_cases hact : Fl4Spec.scActive y = true
    · simp only [hact, ↓reduceIte]
      by_cases hi0 : i = 0#u64
      · simp only [hi0, decide_true, ↓reduceIte]
        have hnone : y.scTcb = none := by rw [hi, hi0, optRef_zero]
        refine WP.spec_mono hnew ?_
        rintro s' ⟨σ', y', h1, rest⟩
        exact ⟨σ', y', hspec σ' (by rw [if_neg (by rw [hnone]; simp)]; exact h1), rest⟩
      · simp only [hi0, decide_false, Bool.false_eq_true, ↓reduceIte]
        have hiT' := hiT hi0
        obtain ⟨xt, hkt, -, -, -, -⟩ := hs.tcb i hiT'
        have hsome : y.scTcb = some i.bv := by rw [hi, optRef_ne hi0]
        step with is_runnable_spec as ⟨b2, hb2⟩
        have hb2' : b2 = Fl4Spec.runnable xt.tcbState := by
          rw [hb2, Bool.eq_iff_iff, decide_eq_true_iff]; exact runnable_iff (hR.at_tcb hiT' hkt).st
        subst hb2'
        have hpre : ∀ (m : Fl4Spec.SMonad Unit Unit) (σ' : Fl4Spec.State Unit),
            (if Fl4Spec.runnable xt.tcbState = true then Fl4Spec.refillUpdate p.bv period.bv budget.bv mr.val
              else Fl4Spec.refillNew p.bv mr.val budget.bv period.bv) σ = ({((), σ')}, False) →
            cfgRefill p.bv y.scTcb budget.bv period.bv mr.val σ = ({((), σ')}, False) := by
          intro _ σ' h
          refine hspec σ' ?_
          rw [if_pos ⟨hact, by rw [hsome]; simp⟩, hsome,
            nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some i.bv) σ = ({(i.bv, σ)}, False)
              from rfl), nd_bind_one (getThreadState_eq hkt)]
          exact h
        by_cases hrun : Fl4Spec.runnable xt.tcbState = true
        · simp only [hrun, ↓reduceIte]
          refine WP.spec_mono (refill_update_refines s σ hS hp hk period budget mr hm2 hmx) ?_
          rintro s' ⟨σ', h1, h2, h3, h4, hw⟩
          have hupd := refillUpdate_eq hk period.bv budget.bv mr.val
          rw [hupd] at h1
          have e1 := pair_eq h1
          subst e1
          have hm0 := min_budget_pos; rw [BitVec.lt_def] at hm0
          have hbv : Fl4Spec.MIN_BUDGET.toNat ≤ budget.val := by rw [BitVec.le_def] at hb; exact hb
          have hnp : period.bv ≠ 0 := fun e => by
            have : period.val = 0 := by have := congrArg BitVec.toNat e; simpa using this
            omega
          have hH := hI.headMin hk hact
          have hok := rUpd_ok y (H := Fl4Spec.refillHd y) σ.curTime (np := period.bv) (nb := budget.bv) mr.val hH hb hnp
          have hne' : (rUpdX y σ.curTime period.bv budget.bv mr.val).scRefills ≠ [] := by
            unfold rUpdX rUpdY rUpdS rUpdL'; split <;> (try split) <;> simp
          refine ⟨_, rUpdX y σ.curTime period.bv budget.bv mr.val, hpre (pure ()) _ (by rw [if_pos hrun]; exact hupd),
            h2, h3, h4, hI.scReconf hk rfl hne' (fun _ _ => hok) (fun _ hp0 => absurd hp0 hnp) hown hnq, rfl, rfl,
            by show decide (0 < mr.val) = true; simp; omega, fun t xt' ht hkt' hr => ?_, hw⟩
          rw [hsome] at ht; cases ht; rw [hkt] at hkt'; cases hkt'; rw [hrun] at hr; cases hr
        · simp only [hrun, Bool.false_eq_true, ↓reduceIte]
          refine WP.spec_mono hnew ?_
          rintro s' ⟨σ', y', h1, rest⟩
          exact ⟨σ', y', hpre (pure ()) σ' (by rw [if_neg hrun]; exact h1), rest⟩
    · have hact' : Fl4Spec.scActive y = false := by simpa using hact
      simp only [hact', Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono hnew ?_
      rintro s' ⟨σ', y', h1, rest⟩
      exact ⟨σ', y', hspec σ' (by rw [if_neg (fun h => hact h.1)]; exact h1), rest⟩

/-- A thread is only in the ready queue of its domain and priority. -/
theorem ready_only {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {d : Fl4Spec.Domain} {q : Fl4Spec.Priority}
    (hm : t.bv ∈ σ.readyQueues d q) : d = x.tcbDomain ∧ q = x.tcbPriority := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', hk', hd, -, -, hpr⟩ := hs.tcb t ht
  rw [hk] at hk'; cases hk'
  by_cases e : d = 0
  · subst e
    obtain ⟨p', hp', rfl⟩ := prio_of_spec q
    rw [hs.rq p' hp', mem_map_bv] at hm
    have := hc.inQ p' hp' t hm
    refine ⟨hd.symm, ?_⟩
    rw [← this]; exact specPrio_eq hpr
  · rw [hs.rqDom d q e] at hm; cases hm

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`remote_tcb_stall` of a thread of the core does nothing** (single core:
every thread of `T` has the current core's affinity). -/
theorem remote_tcb_stall_id {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit} (a : A)
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    smp.remote_tcb_stall st ar s a t ⦃ r => r = (s, a) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold smp.remote_tcb_stall
  step with obj.Tcb.affinity.spec as ⟨cpu, hcpu⟩
  step with LawfulStore.cur_cpu_spec as ⟨i, hi⟩
  rw [hc.aff t ht] at hcpu
  rw [hc.cur] at hi
  subst hcpu hi
  simp

/-- What `configure_flags`' first step keeps. -/
def PreKeep (σ σ1 : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (x : Fl4Spec.SchedContext) (n : Nat) : Prop :=
  (∀ q, q ≠ p → σ1.kheap q = σ.kheap q) ∧
  (∃ y1, σ1.kheap p = some (.schedContext y1 n) ∧ y1.scTcb = x.scTcb ∧ y1.scRefillMax = x.scRefillMax) ∧
  σ1.curThread = σ.curThread ∧ σ1.idleThread = σ.idleThread ∧ σ1.curTime = σ.curTime ∧
  σ1.schedulerAction = σ.schedulerAction ∧ ∀ u ∈ σ1.releaseQueue, u ∈ σ.releaseQueue

/-- **`configure_flags`' first step, for a bound thread `t`**: it leaves the
release queue and its ready queue, and the time is committed if the SC is
the current one. -/
theorem cfg_pre_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) {p : U64} (hp : p ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext x n)) {t : U64} (ht : t ∈ T) (hxt : x.scTcb = some t.bv)
    (hT : TimeAgree ar) :
    (do
      let (s2, a2) ← smp.remote_tcb_stall st ar s a t
      let s3 ← sched.release_remove st s2 t
      let s4 ← sched.dequeue st s3 t
      let s5 ← sched.cur_sc st s4
      let b1 ← obj.Sc.Insts.CoreCmpPartialEqSc.eq s5 p
      let r ← if b1 then sched.commit_time st ar s4 a2 else ok s4
      ok (r, a2)) ⦃ r => ∃ σ1, cfgPre p.bv x.scTcb σ = ({((), σ1)}, False) ∧
        SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ NSC N C σ1 ∧ InvBut σ1 t.bv ∧
        NotQueued σ1 t.bv ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ∧ PreKeep σ σ1 p.bv x n ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -⟩ := hs.tcb t ht
  have hP := hS.placed
  refine WP.spec_bind (remote_tcb_stall_id a hS ht) ?_
  rintro ⟨s2, a2⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hS2 := hS
  have hR2 := hR
  refine WP.spec_bind (WP.spec_and (release_remove_refines s2 σ hS2 ht) (release_remove_sfoot hS2 ht)) ?_
  rintro s3 ⟨⟨σa, hra, ⟨bb, hσa⟩, hf3, hS3⟩, hw3⟩
  subst hσa
  have hR3 : NtfnStateRel N T (L.mem s3) (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb) :=
    hR2.frame hP hf3 (KView.of_kheap rfl)
  have hkta : (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb).kheap t.bv = some (.tcb xt) := hkt
  refine WP.spec_bind (WP.spec_and (dequeue_refines s3 _ hS3 t ht) (dequeue_sfoot hS3 ht)) ?_
  rintro s4 ⟨⟨σb, hdq, hkb, hrb, hf4, hS4⟩, hw4⟩
  have hw34 := WritesIn.kfoot_sfoot (WritesIn.kfoot_of_sfoot (N := N) (C := C) (σ := σ) hw3) hw4
  have e4 := pair_eq (hdq.symm.trans (tcbSchedAction_gen hkta _))
  subst e4
  have hN4 : NSC N C (setQ (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb) xt.tcbDomain
      xt.tcbPriority (Fl4Spec.tcbSchedDequeue t.bv
        ((setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb).readyQueues xt.tcbDomain xt.tcbPriority))) := hN
  set σb := setQ (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb) xt.tcbDomain
      xt.tcbPriority (Fl4Spec.tcbSchedDequeue t.bv
        ((setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb).readyQueues xt.tcbDomain xt.tcbPriority))
    with hσb
  have hqb : QChange (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb) σb := qchange_dequeue hkta
  have hR4 : NtfnStateRel N T (L.mem s4) σb := hR3.frame hP hf4 (KView.of_kheap rfl)
  have hIb' : InvBut σb t.bv := (hI.relRemove t.bv bb).qchange hqb
  have hNQb : NotQueued σb t.bv := by
    refine ⟨fun d q hm => ?_, fun hm => ?_⟩
    · simp only [σb, setQ] at hm
      split at hm
      · exact (by simpa using List.mem_filter.1 hm : False)
      · rename_i hne
        exact hne (ready_only hS ht hkt hm)
    · simp only [σb, setQ, setRel, List.mem_filter] at hm; simp at hm
  -- the spec up to the commit
  have hsp : ∀ σc, Fl4Spec.NonDet.when (σb.curSc = p.bv) Fl4Spec.commitTime σb = ({((), σc)}, False) →
      cfgPre p.bv x.scTcb σ = ({((), σc)}, False) := by
    intro σc hc'
    unfold cfgPre; rw [hxt]
    unfold Fl4Spec.NonDet.when
    rw [if_pos (by simp), nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some t.bv) σ =
      ({(t.bv, σ)}, False) from rfl), nd_bind_one hra, nd_bind_one hdq, nd_gets_bind]
    exact hc'
  obtain ⟨Q4, R4, hc4, hs4⟩ := hS4.lists
  step with sched.cur_sc.spec' as ⟨v, hv⟩
  rw [hc4.cur] at hv
  subst hv
  unfold obj.Sc.Insts.CoreCmpPartialEqSc.eq
  simp only [bind_ok]
  have hcs4 : (nodeW st s4 c layout.node.CUR_SC).bv = σ.curSc := hs4.curSc.symm
  by_cases hcs : nodeW st s4 c layout.node.CUR_SC = p
  · simp only [hcs, decide_true, ↓reduceIte]
    -- the SC is the current one: its thread is the current thread, not released
    have hcp : σ.curSc = p.bv := by rw [← hcs4, hcs]
    obtain ⟨xc, hkc, hxc, -⟩ := hC.tcb
    obtain ⟨y0, m0, hy0, hyt0⟩ := hI.back _ xc _ hkc hxc
    rw [hcp, hk] at hy0; cases hy0
    have htc : t.bv = σ.curThread := Option.some.inj (hxt.symm.trans hyt0)
    have htR : t.bv ∉ σ.releaseQueue := by rw [htc]; exact hC.notRel
    have hflt : (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) = σ.releaseQueue :=
      List.filter_eq_self.2 fun a ha => by
        have : t.bv ≠ a := fun e => htR (e ▸ ha)
        simpa using this
    have hIa : Inv (setRel σ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)) bb) := hI.congr rfl rfl hflt rfl
    have hIb : Inv σb := hIa.qchange hqb
    have hkb : σb.kheap = σ.kheap := rfl
    refine WP.spec_bind (commit_time_refines s4 a2 σb hS4 hR4 hN4 hIb (by rw [hcs]; exact hp) (u0 := t.bv)
      (fun y m hy => by rw [hcs, hkb, hk] at hy; cases hy; exact hxt) hS4.idle
      (by show t.bv ∉ (σ.releaseQueue.filter fun x => decide (t.bv ≠ x)); rw [hflt]; exact htR)
      (OffOK.of_eq hO rfl rfl rfl rfl) (hT.mrt a2) (hT.mb a2)) ?_
    rintro s5 ⟨σc, hcm, hS5, hR5, hN5, hI5, hK6, -, hwc⟩
    rw [WP.spec_ok]
    rw [hcs] at hK6
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hK6
    refine ⟨σc, hsp σc (by unfold Fl4Spec.NonDet.when; rw [if_pos (show σb.curSc = p.bv from hcp)]; exact hcm),
      hS5, hR5, hN5, hI5,
      ⟨fun d q => by rw [k7]; exact hNQb.1 d q, by rw [k3]; exact hNQb.2⟩,
      WritesIn.kfoot_trans hw34 (SzKeepC.of (SzKeep.of_kheap rfl)) hwc, fun q hq => by rw [k8 q hq]; rfl,
      ?_, k2, k6, k5, k4, fun u hu => by rw [k3] at hu; exact (List.mem_filter.1 hu).1⟩
    obtain ⟨y1, h1, h2, h3⟩ := k9 x n hk
    exact ⟨y1, h1, h2, h3⟩
  · simp only [hcs, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    rw [WP.spec_ok]
    have hcp : ¬ σb.curSc = p.bv := fun e => hcs (eq_of_bv (by rw [hcs4]; exact e))
    refine ⟨σb, hsp σb (by unfold Fl4Spec.NonDet.when; rw [if_neg hcp]; rfl), hS4, hR4, hN4, hIb', hNQb, hw34,
      fun q _ => rfl, ⟨x, hk, rfl, rfl⟩, rfl, rfl, rfl, rfl, fun u hu => (List.mem_filter.1 hu).1⟩

theorem tcb_ne_eq (a b : obj.Tcb) :
    core.cmp.PartialEq.ne.trait_default obj.Tcb.Insts.CoreCmpPartialEqTcb a b = ok (decide (a ≠ b)) := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]
  exact ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

/-- **`configure_flags`' resume step, for a bound thread `t`**: the TCB moves
to the core (a no-op on one core), `sched_context_resume` restores `Inv`,
then the thread is switched to, or the current thread rescheduled. -/
theorem cfg_resume_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ)
    {p t : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) (ht : t ∈ T) (hI : InvBut σ t.bv) (hnq : NotQueued σ t.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n)) (hyt : y.scTcb = some t.bv)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxp : xt.tcbSchedContext = some p.bv)
    (ha : Fl4Spec.scActive y = true) (hr : Fl4Spec.runnable xt.tcbState = false → released σ y)
    (cpu : U64) (hcpu : cpu = c)
    (hT : TimeAgree ar) :
    (do
      let (s5, a3) ← smp.migrate_tcb st ar s a t cpu
      let (s6, a4) ← schedcontext.resume st ar s5 a3 p
      let i1 ← st.cur_cpu s6
      let (s7, a5) ←
        if cpu = i1
        then
          do
          let b1 ← sched.is_runnable st s6 t
          let t2 ←
            if b1
            then
              do
              let t1 ← sched.cur_thread st s6
              let b2 ← core.cmp.PartialEq.ne.trait_default obj.Tcb.Insts.CoreCmpPartialEqTcb t t1
              if b2
              then sched.possible_switch_to st s6 t
              else ok s6
            else ok s6
          ok (t2, a4)
        else
          do
          let b1 ← sched.is_schedulable st s6 t
          if b1
          then
            let s8 ← sched.enqueue st s6 t
            smp.remote_reschedule st ar s8 a4 cpu
          else
            let s8 ← sched.set_reprogram_on st s6 cpu
            smp.remote_reschedule st ar s8 a4 cpu
      let t1 ← sched.cur_thread st s7
      let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t t1
      let t3 ← if b1 then sched.reschedule_required st s7 else ok s7
      ok (t3, a5)) ⦃ r => ∃ σ', cfgResume p.bv (some t.bv) σ = ({((), σ')}, False) ∧
        SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        σ'.kheap = σ.kheap ∧
        (σ.schedulerAction = .resumeCurThread → IdleOK σ → t.bv ≠ σ.idleThread → ActIdle σ') ∧
        WritesIn st s r.1 (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hP := hS.placed
  -- `migrate_tcb` to the TCB's own core
  subst cpu
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨i, i_post⟩
  have hi : i = c := by rw [i_post]; exact hc.aff t ht
  subst hi
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step as ⟨s4, s4_post⟩
  subst s4_post
  obtain ⟨hS3, hf3⟩ := hS.wr_same (field_aligned (hc.tcbs t ht) (K := 3520#u64) (by simp) (by simp)) (hc.aff t ht)
  have hR3 : NtfnStateRel N T (L.mem (L.wr s (affA t) i)) σ := hR.frame hP hf3 (KView.refl σ)
  have hw4 : WritesIn st s (L.wr s (affA t) i) (SFoot st T i s) :=
    writesIn_tcb (K := 3520#u64) hc.tcbs ht (by unfold SOff; decide) (by simp) i
  -- `resume`
  have hRel : RelOK σ :=
    ⟨fun u hu => by obtain ⟨x, p, -, -, h1, h2, -⟩ := hI.rel u hu; exact ⟨x, p, h1, h2⟩, hI.sorted⟩
  have hkp' : ∃ y' n', σ.kheap p.bv = some (.schedContext y' n') := ⟨y, n, hk⟩
  refine WP.spec_bind (resume_refines (L.wr s (affA t) i) a σ hR3 hS3 hRel (hT.mb a) hp hp0 ht (word24_of hS3 hp hk hyt)
    (scA_of hS3 ht hkt hxp) (fun x hx => by rw [hkt] at hx; cases hx; exact hnq.1 _ _)) ?_
  rintro ⟨s6, a4⟩ ⟨rfl, σr, hrs, hkr, har, htr, -, -, hf6, hw6, hS6⟩
  have hw46 := WritesIn.sfoot_trans hw4 hw6
  have hR6 : NtfnStateRel N T (L.mem s6) σr := hR3.frame hP hf6 (KView.of_kheap hkr)
  have hN6 : NSC N C σr := fun m hm x q hx hq => hN m hm x q (by rw [← hkr]; exact hx) hq
  have hIr : Inv σr := hI.resume hk hyt hkt hxp hnq (fun hrun _ _ => hr hrun) hrs
  have hkeep := resume_keep hI hk hyt hkt hxp hnq hrs
  have hAr : σ.schedulerAction = .resumeCurThread → IdleOK σ → t.bv ≠ σ.idleThread →
      ActIdle σr ∧ σr.schedulerAction = .resumeCurThread := fun ha0 hid hti =>
    ⟨ActIdle.of_noswitch (IdleOK.of hid hkeep.1.2.2.2.2.2.1 (by rw [hkr])
      (fun hm => (hkeep.2.2 _ hm).resolve_left (fun e => hti e.symm)))
      (fun u => by rw [hkeep.2.1, ha0]; simp), by rw [hkeep.2.1, ha0]⟩
  obtain ⟨Q6, R6, hc6, hs6⟩ := hS6.lists
  step with LawfulStore.cur_cpu_spec as ⟨i1, hi1⟩
  rw [hc6.cur] at hi1
  subst hi1
  rw [if_pos rfl]
  have hkt6 : σr.kheap t.bv = some (.tcb xt) := by rw [hkr]; exact hkt
  have hkp6 : σr.kheap p.bv = some (.schedContext y n) := by rw [hkr]; exact hk
  step with is_runnable_spec as ⟨b1, hb1⟩
  have hb1' : b1 = Fl4Spec.runnable xt.tcbState := by
    rw [hb1, Bool.eq_iff_iff, decide_eq_true_iff]; exact runnable_iff (hR6.at_tcb ht hkt6).st
  subst hb1'
  have hct6 := hs6.curThread.symm
  -- the spec
  have hsp : ∀ σ', (if t.bv = σr.curThread then Fl4Spec.rescheduleRequired
      else Fl4Spec.NonDet.when (Fl4Spec.runnable xt.tcbState = true) (Fl4Spec.possibleSwitchTo t.bv)) σr =
      ({((), σ')}, False) → cfgResume p.bv (some t.bv) σ = ({((), σ')}, False) := by
    intro σ' h
    unfold cfgResume Fl4Spec.NonDet.when
    rw [if_pos (by simp), nd_bind_one hrs, nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit)
      (some t.bv) σr = ({(t.bv, σr)}, False) from rfl), nd_bind_one (getThreadState_eq hkt6), nd_gets_bind]
    exact h
  have hctne : ∀ u : U64, (decide (t ≠ u) = true ↔ t.bv ≠ u.bv) := fun u => by
    simp only [decide_eq_true_eq, ne_eq]; exact ⟨fun h e => h (eq_of_bv e), fun h e => h (e ▸ rfl)⟩
  -- the `reschedule_required` tail, when `t` is the current thread
  have hresched : ∀ (s7 : S) (σ7 : Fl4Spec.State Unit), NtfnStateRel N T (L.mem s7) σ7 →
      SchedRel st N T C i1 s7 σ7 → Inv σ7 → σ7.kheap = σ.kheap →
      sched.reschedule_required st s7 ⦃ s' => ∃ σ', Fl4Spec.rescheduleRequired (Z := Unit) σ7 = ({((), σ')}, False) ∧
        SchedRel st N T C i1 s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
        σ'.kheap = σ.kheap ∧ (σ7.schedulerAction = .resumeCurThread → IdleOK σ7 → ActIdle σ') ∧
        WritesIn st s7 s' (SFoot st T i1 s7) ⦄ := by
    intro s7 σ7 hR7 hS7 hI7 hk7
    refine WP.spec_mono (WP.spec_and (reschedule_required_refines s7 σ7 hR7 hS7 hI7.actReady)
      (reschedule_required_sfoot hS7)) ?_
    rintro s8 ⟨⟨σ8, he8, hk8, -, hf8, hS8⟩, hw8⟩
    obtain ⟨σ9, he9, hq9⟩ := rescheduleRequired_qchange hI7.actReady
    rw [he9] at he8
    have e : σ9 = σ8 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he8))).2
    subst e
    refine ⟨σ9, he9, hS8, hR7.frame hS7.placed hf8 (KView.of_kheap hk8), ?_, hI7.qchange hq9, hk8.trans hk7,
      fun ha hid => ?_, hw8⟩
    · intro m hm x q hx hq; rw [hk8, hk7] at hx; exact hN m hm x q hx hq
    · have e := rescheduleRequired_noswitch (σ := σ7) (fun t h => by rw [ha] at h; cases h)
      rw [he9] at e
      rw [← pair_eq e]
      exact ActIdle.of_noswitch hid (fun _ h => by cases h)
  by_cases hrun : Fl4Spec.runnable xt.tcbState = true
  · rw [if_pos hrun]
    step with sched.cur_thread.spec' as ⟨ct, hct⟩
    rw [hc6.cur] at hct
    subst hct
    rw [tcb_ne_eq]
    simp only [bind_ok]
    by_cases he : t.bv = σr.curThread
    · have hb : decide (t ≠ nodeW st s6 i1 layout.node.CUR_THREAD) = false := by
        rw [Bool.eq_false_iff]; intro h; exact (hctne _).1 h (by rw [hct6]; exact he)
      rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
      step with sched.cur_thread.spec' as ⟨ct, hct⟩
      rw [hc6.cur] at hct
      subst hct
      have hb2 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t (nodeW st s6 i1 layout.node.CUR_THREAD) = ok true := by
        unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq; simp only [ok.injEq, decide_eq_true_eq]
        exact eq_of_bv (by rw [hct6]; exact he)
      rw [hb2]; simp only [↓reduceIte, bind_ok]
      refine WP.spec_bind (hresched s6 σr hR6 hS6 hIr hkr) ?_
      rintro s8 ⟨σ8, he8, hS8, hR8, hN8, hI8, hk8, hA8, hw8⟩
      rw [WP.spec_ok]
      exact ⟨σ8, hsp σ8 (by rw [if_pos he]; exact he8), hS8, hR8, hN8, hI8, hk8,
        fun ha0 hid hti => hA8 (hAr ha0 hid hti).2 (hAr ha0 hid hti).1.2, WritesIn.sfoot_trans hw46 hw8⟩
    · have hb : decide (t ≠ nodeW st s6 i1 layout.node.CUR_THREAD) = true :=
        (hctne _).2 (by rw [hct6]; exact he)
      rw [hb]; simp only [↓reduceIte]
      refine WP.spec_bind (WP.spec_and (possible_switch_to_refines s6 σr hR6 hS6 hIr.actReady t ht)
        (possible_switch_to_sfoot hR6 hS6 hIr.actReady ht)) ?_
      rintro s7 ⟨⟨σ7, he7, hk7, hf7, hS7⟩, hw7⟩
      obtain ⟨hI7, -, hct7⟩ := hIr.psw hkt6 hxp hrun hkp6 ha he7
      obtain ⟨Q7, R7, hc7, hs7⟩ := hS7.lists
      step with sched.cur_thread.spec' as ⟨ct, hct⟩
      rw [hc7.cur] at hct
      subst hct
      have hb2 : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq t (nodeW st s7 i1 layout.node.CUR_THREAD) = ok false := by
        unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq; simp only [ok.injEq, decide_eq_false_iff_not]
        intro e; apply he; rw [← hct7, hs7.curThread, ← e]
      rw [hb2]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨σ7, hsp σ7 (by rw [if_neg he]; unfold Fl4Spec.NonDet.when; rw [if_pos hrun]; exact he7), hS7,
        hR6.frame hS6.placed hf7 (KView.of_kheap hk7), ?_, hI7, hk7.trans hkr,
        fun ha0 hid hti => (hAr ha0 hid hti).1.psw hIr hkt6 hxp hrun hkp6 ha he7, WritesIn.sfoot_trans hw46 hw7⟩
      intro m hm x q hx hq; rw [hk7, hkr] at hx; exact hN m hm x q hx hq
  · rw [if_neg hrun]
    simp only [bind_ok]
    step with sched.cur_thread.spec' as ⟨ct, hct⟩
    rw [hc6.cur] at hct
    subst hct
    unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
    simp only [bind_ok]
    by_cases he : t.bv = σr.curThread
    · have hb2 : decide (t = nodeW st s6 i1 layout.node.CUR_THREAD) = true :=
        decide_eq_true (eq_of_bv (by rw [hct6]; exact he))
      rw [hb2]; simp only [↓reduceIte]
      refine WP.spec_bind (hresched s6 σr hR6 hS6 hIr hkr) ?_
      rintro s8 ⟨σ8, he8, hS8, hR8, hN8, hI8, hk8, hA8, hw8⟩
      rw [WP.spec_ok]
      exact ⟨σ8, hsp σ8 (by rw [if_pos he]; exact he8), hS8, hR8, hN8, hI8, hk8,
        fun ha0 hid hti => hA8 (hAr ha0 hid hti).2 (hAr ha0 hid hti).1.2, WritesIn.sfoot_trans hw46 hw8⟩
    · have hb2 : decide (t = nodeW st s6 i1 layout.node.CUR_THREAD) = false :=
        decide_eq_false (fun e => he (by rw [← hct6, ← e]))
      rw [hb2]; simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
      refine ⟨σr, hsp σr (by rw [if_neg he]; unfold Fl4Spec.NonDet.when; rw [if_neg hrun]; rfl), hS6, hR6, hN6,
        hIr, hkr, fun ha0 hid hti => (hAr ha0 hid hti).1, hw46⟩

/-- FL4's `flags & SPORADIC != 0` is the spec's `test_bit flags sc_sporadic_flag`. -/
theorem sporadic_bit (flags : U64) :
    (flags &&& fl4_abi.consts.sc_flag.SPORADIC != 0#u64) = Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag := by
  have h1 : (flags.bv &&& 1#64).toNat = flags.bv.toNat % 2 := by
    rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
  have h2 : ((flags.bv &&& 1#64) ≠ 0#64) ↔ flags.bv.toNat % 2 = 1 := by
    rw [ne_eq, BitVec.toNat_eq, h1]; simp
  have h3 : (flags &&& fl4_abi.consts.sc_flag.SPORADIC != 0#u64) = decide ((flags.bv &&& 1#64) ≠ 0#64) := by
    unfold fl4_abi.consts.sc_flag.SPORADIC
    rw [bne, decide_not]; congr 1
  rw [h3, Fl4Spec.testBit, Fl4Spec.scSporadicFlag, BitVec.getLsbD, Nat.testBit_zero]
  simp only [h2]

/-- Replacing an SC keeps `NSC`. -/
theorem NSC.updSc {N C : Set U64} {σ : Fl4Spec.State Unit} (h : NSC N C σ) {p : Fl4Spec.ObjRef}
    {y : Fl4Spec.SchedContext} {n : Nat} : NSC N C (updSc σ p y n) := by
  intro m hm x q hx hq
  by_cases e : m.bv = p
  · subst e; simp [updK] at hx
  · simp only [updSc, updK_kheap, Function.update_of_ne e] at hx; exact h m hm x q hx hq

/-- **`configure_flags`' badge and sporadic-flag writes.** -/
theorem cfg_tail_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) {y : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p.bv = some (.schedContext y n))
    (badge flags : U64) :
    (do
      let s5 ← obj.Sc.set_badge st p s badge
      let i1 ← lift (flags &&& fl4_abi.consts.sc_flag.SPORADIC)
      if i1 != 0#u64 then
        let s6 ← obj.Sc.set_sporadic st p s5 1#u64
        ok (s6, a)
      else
        let s6 ← obj.Sc.set_sporadic st p s5 0#u64
        ok (s6, a)) ⦃ r => ∃ σ4 σ5,
      Fl4Spec.setScObjRef (Z := Unit) Fl4Spec.scBadgeUpdate p.bv badge.bv σ = ({((), σ4)}, False) ∧
      Fl4Spec.setScObjRef (Z := Unit) Fl4Spec.scSporadicUpdate p.bv
        (Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag) σ4 = ({((), σ5)}, False) ∧
      SchedRel st N T C c r.1 σ5 ∧ NtfnStateRel N T (L.mem r.1) σ5 ∧ NSC N C σ5 ∧ Inv σ5 ∧
      (ActIdle σ → ActIdle σ5) ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  have hP := hS.placed
  have hal : ∀ K : U64, K.val < 96 → K.val % 8 = 0 → Aligned (scW p K) := fun K h1 h2 => by
    obtain ⟨Q0, R0, -, hs0⟩ := hS.lists
    obtain ⟨x0, n0, -, hx0⟩ := hs0.scs p hp; exact (hx0.hdr h1 h2).1
  step with obj.Sc.set_badge.spec2 as ⟨s5, hs5⟩
  subst hs5
  obtain ⟨hS5, hf5, hK6⟩ := hS.set_sc_badge hp hk badge
  have hR5 := hR.frame hP hf5 hK6
  have h4 : Fl4Spec.setScObjRef (Z := Unit) Fl4Spec.scBadgeUpdate p.bv badge.bv σ =
      ({((), updSc σ p.bv { y with scBadge := badge.bv } n)}, False) := updateSchedContext_eq hk _
  have hk5 : (updSc σ p.bv { y with scBadge := badge.bv } n).kheap p.bv =
      some (.schedContext { y with scBadge := badge.bv } n) := by simp [updK]
  have hI5 : Inv (updSc σ p.bv { y with scBadge := badge.bv } n) := hI.scFields hk rfl rfl rfl rfl
  simp only [lift, bind_ok]
  rw [sporadic_bit]
  -- the sporadic word `v`
  have fin : ∀ v : U64, v = (if Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag then 1#u64 else 0#u64) →
      (do
        let s6 ← obj.Sc.set_sporadic st p (L.wr s (scW p 48#u64) badge) v
        ok (s6, a)) ⦃ r => ∃ σ4 σ5,
      Fl4Spec.setScObjRef (Z := Unit) Fl4Spec.scBadgeUpdate p.bv badge.bv σ = ({((), σ4)}, False) ∧
      Fl4Spec.setScObjRef (Z := Unit) Fl4Spec.scSporadicUpdate p.bv
        (Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag) σ4 = ({((), σ5)}, False) ∧
      SchedRel st N T C c r.1 σ5 ∧ NtfnStateRel N T (L.mem r.1) σ5 ∧ NSC N C σ5 ∧ Inv σ5 ∧
      (ActIdle σ → ActIdle σ5) ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
    intro v hv
    step with obj.Sc.set_sporadic.spec2 as ⟨s6, hs6⟩
    subst hs6
    obtain ⟨hS6, hf6, hK6⟩ := hS5.set_sc_sporadic hp hk5 v
    have hbit : decide (v ≠ 0#u64) = Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag := by
      rw [hv]; split <;> simp_all
    rw [hbit] at hS6 hK6
    refine ⟨_, _, h4, updateSchedContext_eq hk5 _, hS6, hR5.frame hS5.placed hf6 hK6, hN.updSc.updSc,
      hI5.scFields hk5 rfl rfl rfl rfl, fun hA => ?_,
      ((writesIn_wr (st := st) (s := s) (v := badge) (hal 48#u64 (by simp) (by simp))).trans
        (writesIn_wr (st := st) (s := L.wr s (scW p 48#u64) badge) (v := v) (hal 64#u64 (by simp) (by simp)))).mono
        fun b hb => by
          rcases hb with rfl | rfl
          · exact KFoot.of_sw (sw_hdr hS hp (by simp) (by simp) (by decide))
          · exact KFoot.of_sw (sw_hdr hS hp (by simp) (by simp) (by decide))⟩
    have hA5 : ActIdle (updSc σ p.bv { y with scBadge := badge.bv } n) :=
      hA.keepE (E := fun _ => False) (TKeepE.updSc _ hk rfl) (fun u hu => Or.inl hu) (Or.inl rfl) rfl
        (fun _ _ h => h) id
    exact hA5.keepE (E := fun _ => False) (TKeepE.updSc _ hk5 rfl) (fun u hu => Or.inl hu) (Or.inl rfl) rfl
      (fun _ _ h => h) id
  by_cases hb : Fl4Spec.testBit flags.bv Fl4Spec.scSporadicFlag = true
  · rw [if_pos hb]; exact fin _ (by rw [if_pos hb])
  · rw [if_neg hb]; exact fin _ (by rw [if_neg hb])

/-- **`configure_flags` refines `invoke_sched_control_configure_flags`**,
keeping `Inv`. On one core the TCB stall and the migration do nothing.
Hypotheses: the SC's bound TCB (if any) is one of `T` and points back at
the SC (l4v `sym_refs`); the core argument is the current core; and the
decoder's checks: `2 ≤ max_refills ≤ refill_absolute_max`, `MIN_BUDGET ≤
budget ≤ period`. -/
theorem configure_flags_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext x n))
    (hbnd : ∀ t : U64, x.scTcb = some t.bv →
      t ∈ T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    (cpu budget period mr badge flags : U64) (hcpu : cpu = c) (hm2 : 2 ≤ mr.val) (hmx : mr.val ≤ absMax n)
    (hb : Fl4Spec.MIN_BUDGET ≤ budget.bv) (hbp : budget.val ≤ period.val)
    (hT : TimeAgree ar) :
    schedcontext.configure_flags st ar s a p cpu budget period mr badge flags ⦃ r => ∃ σ',
      Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit)
        (.invokeSchedControlConfigureFlags p.bv budget.bv period.bv mr.val badge.bv flags.bv) σ =
        ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ.schedulerAction = .resumeCurThread → IdleOK σ → p.bv ≠ Fl4Spec.idleScPtr → ActIdle σ') ∧
      WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs p hp
  rw [hk] at hk'; cases hk'
  have hP := hS.placed
  have hmx2 : 2 ≤ absMax n := by omega
  have hTA : scTcbA p = scW p 24#u64 := by unfold scTcbA scW layout.sc.TCB; rfl
  have hal : Aligned (scW p 16#u64) := (hx.hdr (K := 16#u64) (by simp) (by simp)).1
  have hidp : IdleOK σ → σ.idleThread ≠ p.bv := fun hId e => by
    obtain ⟨xi, h1, -⟩ := hId; rw [e, hk] at h1; cases h1
  unfold schedcontext.configure_flags
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [hTA] at hi
  step with obj.Tcb.is_null.spec as ⟨b, hb0⟩
  subst hb0
  by_cases hi0 : i = 0#u64
  · -- an unbound SC
    have hnone : x.scTcb = none := by rw [hx.tcb, ← hi, hi0, optRef_zero]
    have hown : ∀ u xu, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext = some p.bv → u = p.bv := by
      intro u xu hu hxu
      obtain ⟨y', n', hy', hyu⟩ := hI.back u xu p.bv hu hxu
      rw [hk] at hy'; cases hy'; rw [hnone] at hyu; cases hyu
    have hnq : NotQueued σ p.bv := by
      refine ⟨fun d q hm => ?_, fun hm => ?_⟩
      · obtain ⟨_, _, _, _, h1, -⟩ := hI.rq d q _ hm; rw [hk] at h1; cases h1
      · obtain ⟨_, _, _, _, h1, -⟩ := hI.rel _ hm; rw [hk] at h1; cases h1
    have hRef := cfg_refill_refines s σ hS hR (hI.toBut p.bv) hp hk hown hnq (i := i) (by rw [hx.tcb, ← hi])
      (fun h => absurd hi0 h) cpu budget period mr hcpu hm2 hmx hb hbp hmx2
    simp only [hi0, decide_true, ↓reduceIte, bind_ok] at hRef ⊢
    refine WP.spec_bind hRef ?_
    rintro s2 ⟨σ2, y2, hrf, hS2, hf2, hK2, hI2, rfl, hy2t, -, -, hw2⟩
    refine WP.spec_bind (obj.Sc.set_cpu.spec2 s2 p cpu) ?_
    rintro s3 rfl
    obtain ⟨hS3, hf3⟩ := hS2.wr_same (v := cpu) hal (by rw [hS2.core p hp, hcpu])
    have hR3 := (hR.frame hP hf2 hK2).frame hS2.placed hf3 (KView.refl _)
    have hk2 : (updSc σ p.bv y2 n).kheap p.bv = some (.schedContext y2 n) := by simp [updK]
    have hw3 : WritesIn st s (L.wr s2 (scW p 16#u64) cpu) (KFoot st T N C c s σ) :=
      WritesIn.kfoot_sw hw2 ((writesIn_wr hal).mono fun b hb => hb ▸ sw_hdr hS hp (by simp) (by simp) (by decide))
    have hz3 : SzKeep σ (updSc σ p.bv y2 n) :=
      SzKeep.of_sc (fun q hq => by simp [updK, hq]) hk hk2
    have hI2' : Inv (updSc σ p.bv y2 n) := hI2.inv fun xu hxu => by rw [hk2] at hxu; cases hxu
    refine WP.spec_mono (cfg_tail_refines _ a _ hS3 hR3 hN.updSc hI2' hp hk2 badge flags) ?_
    rintro r ⟨σ4, σ5, h4, h5, hS5, hR5, hN5, hI5, hA5, hw5⟩
    refine ⟨σ5, cfg_spec hk (σ1 := σ) (by unfold cfgPre Fl4Spec.NonDet.when; rw [if_neg (by simp [hnone])]; rfl)
      hk (fun t ht => by rw [hnone] at ht; cases ht) hrf
      (by unfold cfgResume Fl4Spec.NonDet.when; rw [if_neg (by simp [hnone])]; rfl) h4 h5, hS5, hR5, hN5, hI5,
      fun ha0 hId _ => hA5 (ActIdle.of_noswitch (IdleOK.of hId rfl
        (by simp only [updSc, updK_kheap, Function.update_of_ne (hidp hId)]) id)
        (fun u => by show σ.schedulerAction ≠ _; rw [ha0]; simp)),
      WritesIn.kfoot_trans hw3 (SzKeepC.of hz3) hw5⟩
  · -- a bound SC: its TCB `i`
    have hxt : x.scTcb = some i.bv := by rw [hx.tcb, ← hi, optRef_ne hi0]
    obtain ⟨hiT, xt, hkt, hxp⟩ := hbnd i hxt
    have hip : i.bv ≠ p.bv := fun e => by rw [e, hk] at hkt; cases hkt
    simp only [hi0, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (cfg_pre_refines s a σ hS hR hN hI hC hO hp hk hiT hxt hT) ?_
    rintro ⟨s1, a1⟩ ⟨σ1, hpre, hS1, hR1, hN1, hI1, hnq1, hw1, hq1, ⟨y1, hk1, hy1t, -⟩, -, hid1, -, hact1, hrq1⟩
    have hkt1 : σ1.kheap i.bv = some (.tcb xt) := by rw [hq1 _ hip]; exact hkt
    have hown1 : ∀ u xu, σ1.kheap u = some (.tcb xu) → xu.tcbSchedContext = some p.bv → u = i.bv := by
      intro u xu hu hxu
      obtain ⟨y', n', hy', hyu⟩ := hI1.back u xu p.bv hu hxu
      rw [hk1] at hy'; cases hy'; rw [hy1t, hxt] at hyu; exact (Option.some.inj hyu).symm
    have hRef := cfg_refill_refines s1 σ1 hS1 hR1 hI1 hp hk1 hown1 hnq1 (i := i)
      (by rw [hy1t, hxt, optRef_ne hi0]) (fun _ => hiT) cpu budget period mr hcpu hm2 hmx hb hbp hmx2
    simp only [hi0, decide_false, Bool.false_eq_true, ↓reduceIte] at hRef
    refine WP.spec_bind hRef ?_
    rintro s2 ⟨σ2, y2, hrf, hS2, hf2, hK2, hI2, rfl, hy2t, ha2, hrel2, hw2⟩
    refine WP.spec_bind (obj.Sc.set_cpu.spec2 s2 p cpu) ?_
    rintro s3 rfl
    obtain ⟨hS3, hf3⟩ := hS2.wr_same (v := cpu) hal (by rw [hS2.core p hp, hcpu])
    have hR3 := (hR1.frame hS1.placed hf2 hK2).frame hS2.placed hf3 (KView.refl _)
    have hk2 : (updSc σ1 p.bv y2 n).kheap p.bv = some (.schedContext y2 n) := by simp [updK]
    have hw3 : WritesIn st s1 (L.wr s2 (scW p 16#u64) cpu) (KFoot st T N C c s1 σ1) :=
      WritesIn.kfoot_sw hw2 ((writesIn_wr hal).mono fun b hb => hb ▸ sw_hdr hS1 hp (by simp) (by simp) (by decide))
    have hz1 : SzKeep σ σ1 := SzKeep.of_sc hq1 hk hk1
    have hz2 : SzKeep σ1 (updSc σ1 p.bv y2 n) := SzKeep.of_sc (fun q hq => by simp [updK, hq]) hk1 hk2
    have hkt2 : (updSc σ1 p.bv y2 n).kheap i.bv = some (.tcb xt) := by
      simp only [updSc, updK_kheap, Function.update_of_ne hip]; exact hkt1
    refine WP.spec_bind (cfg_resume_refines _ a1 _ hS3 hR3 hN1.updSc hp hp0 hiT hI2 hnq1 hk2
      (by rw [hy2t, hy1t, hxt]) hkt2 hxp ha2 (fun h => hrel2 i.bv xt (by rw [hy1t, hxt]) hkt1 h) cpu hcpu hT) ?_
    rintro ⟨s4, a2⟩ ⟨σ3, hres, hS4, hR4, hN4, hI4, hk4, hA4, hw4⟩
    have hw34 := WritesIn.kfoot_sfoot hw3 hw4
    have hk3 : σ3.kheap p.bv = some (.schedContext y2 n) := by rw [hk4]; exact hk2
    refine WP.spec_mono (cfg_tail_refines s4 a2 σ3 hS4 hR4 hN4 hI4 hp hk3 badge flags) ?_
    rintro r ⟨σ4, σ5, h4, h5, hS5, hR5, hN5, hI5, hA5, hw5⟩
    refine ⟨σ5, cfg_spec hk hpre hk1 (fun t ht => by rw [hxt] at ht; cases ht; exact ⟨xt, hkt1⟩)
      (by rw [← hy1t]; exact hrf) (by rw [hxt]; exact hres) h4 h5, hS5, hR5, hN5, hI5, fun ha0 hId hpi => hA5 ?_,
      WritesIn.kfoot_trans hw1 (SzKeepC.of hz1)
        (WritesIn.kfoot_trans hw34 (SzKeepC.of (hz2.trans (SzKeep.of_kheap hk4))) hw5)⟩
    have hip1 : σ1.idleThread ≠ p.bv := by rw [hid1]; exact hidp hId
    have hId1 : IdleOK σ1 := IdleOK.of hId hid1 (hq1 _ (hidp hId)) (hrq1 _)
    have hId2 : IdleOK (updSc σ1 p.bv y2 n) :=
      IdleOK.of hId1 rfl (by simp only [updSc, updK_kheap, Function.update_of_ne hip1]) id
    have hti : i.bv ≠ σ1.idleThread := fun e => by
      obtain ⟨xi, h1, h2, -⟩ := hId
      rw [← hid1, ← e, hkt] at h1
      cases h1
      exact hpi (Option.some.inj (hxp.symm.trans h2))
    exact hA4 (by show σ1.schedulerAction = _; rw [hact1, ha0]) hId2 hti

end

end

end Fl4Proofs.P3.Sched
