/-
P3 (DESIGN.md §9), invariant line G1 (rd8s): **`VE` across `invoke_sched_control_configure`**
(KENTRY-PLAN rd8q handoff 1(c); spec side only, outside the JAtZ cone).

`refill_new` / `refill_update` may make the configured SC `p` active, so every TCB bound to `p`
may become schedulable. By sb2's `ScBackS` (carried `ScInv`) the only such TCB is the SC's own
`scTcb` `u` (read at the start), so the exception set `E ∪ {v | scTcb = some v}` covers it:

* **`ve_ro`**: `VE E'` across a write of the SC `p` only (sb2's `RO`, queues / ct / action fixed:
  `QRC`) when every TCB bound to `p` is in `E'`; `bu_br` carries the bound-TCB fact along sb2's
  binding frame `BR`; `hk_refillNew` / `hk_refillUpdate` (sb2's inner `RO` proofs, stated),
  `qrc_refillNew` / `qrc_refillUpdate`, `ht_refill`.
* **`ht_invokeSchedControlConfigureFlags`**: `VE E ∧ ScInv → VE E` (`u` is dequeued and
  release-removed first, exempt through the refill, and leaves by the final
  `possible_switch_to` / as ct / as a thread that is not runnable).
-/
import Fl4Proofs.P3.SpecInvRd8sC
import Fl4Proofs.P3.SpecInvSbW
open Classical

namespace Fl4Proofs.P3.SInvR.B8s
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8q

noncomputable section

set_option maxHeartbeats 1000000

variable {E : ObjRef → Prop}

/-! ## Refills write only the SC -/

open Fl4Proofs.P3.SInvB in
theorem hk_refillNew (p : ObjRef) (mr : Nat) (budget period : Ticks) (k : KHeap) :
    SInvB.HK (SInvB.ROs p k) (SInvB.RN p k) (refillNew (Z := Unit) p mr budget period) := by
  unfold refillNew
  refine SInvB.hk_bind (SInvB.hk_of_ik (ik_gets _)) fun ct => ?_
  refine SInvB.hk_bind (SInvB.hk_of_ik (SInvB.ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine SInvB.hk_bind (SInvB.hk_of_ik (SInvB.ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine SInvB.hk_bind (SInvB.hk_of_ik (SInvB.ik_ro_upd fun _ => rfl)) fun _ => ?_
  refine SInvB.hk_bind (SInvB.hk_of_ik (ik_pure _)) fun _ => ?_
  exact SInvB.hk_bind (SInvB.hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ =>
    SInvB.hk_of_ik (SInvB.ik_rn_maybeAddEmptyTail p k)

open Fl4Proofs.P3.SInvB in
theorem hk_refillUpdate (p : ObjRef) (np nb : Ticks) (nm : Nat) (k : KHeap) :
    SInvB.HK (SInvB.ROs p k) (SInvB.RN p k) (refillUpdate (Z := Unit) p np nb nm) := by
  unfold refillUpdate
  refine SInvB.hk_bind (SInvB.hk_ne_upd (fun _ => rfl) (fun _ => List.cons_ne_nil _ _)) fun _ => SInvB.hk_of_ik ?_
  refine ik_bind (SInvB.ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (SInvB.ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (SInvB.ik_rn_upd (fun _ => rfl) fun _ h => h) fun _ => ?_
  refine ik_bind (by unfold getScRefillReady; rd_auto) fun _ => ?_
  refine ik_bind ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · refine ik_bind (ik_gets _) fun _ => ?_
      unfold updateRefillHd
      exact SInvB.ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)
    · exact ik_pure _
  refine ik_bind (by unfold getRefillHead; rd_auto) fun _ => ?_
  split
  · unfold updateRefillHd
    exact ik_bind (SInvB.ik_rn_upd (fun _ => rfl) (fun _ _ => List.cons_ne_nil _ _)) fun _ =>
      SInvB.ik_rn_maybeAddEmptyTail p k
  · refine ik_pure_bind (ik_pure_bind ?_)
    unfold refillAddTail
    exact SInvB.ik_rn_upd (fun _ => rfl) (fun _ _ => by simp [scRefillsUpdate])

/-- Ready queues, release queue, ct and action fixed. -/
abbrev QRC (Q : Domain → Priority → ReadyQueue) (R : ReleaseQueue) (C : ObjRef) (A : SchedulerAction)
    (s : State Unit) : Prop :=
  s.readyQueues = Q ∧ s.releaseQueue = R ∧ s.curThread = C ∧ s.schedulerAction = A

theorem qrc_refillNew (p : ObjRef) (mr : Nat) (budget period : Ticks) (Q : Domain → Priority → ReadyQueue)
    (R : ReleaseQueue) (C : ObjRef) (A : SchedulerAction) : IK (QRC Q R C A) (refillNew (Z := Unit) p mr budget period) := by
  unfold refillNew; repeat' (first | ik_step0 | ik_unfold)

theorem qrc_refillUpdate (p : ObjRef) (np nb : Ticks) (nm : Nat) (Q : Domain → Priority → ReadyQueue)
    (R : ReleaseQueue) (C : ObjRef) (A : SchedulerAction) : IK (QRC Q R C A) (refillUpdate (Z := Unit) p np nb nm) := by
  unfold refillUpdate; repeat' (first | ik_step0 | ik_unfold)

/-- **`VE E'` across a write of the SC `p` alone**, when every TCB bound to `p` is exempt. -/
theorem ve_ro {E' : ObjRef → Prop} {p : ObjRef} {σ s : State Unit} (h : VE E' σ)
    (hb : ∀ v x, σ.kheap v = some (.tcb x) → x.tcbSchedContext = some p → E' v)
    (hr : SInvB.RO p σ.kheap s.kheap) (hq : QRC σ.readyQueues σ.releaseQueue σ.curThread σ.schedulerAction s) :
    VE E' s := by
  obtain ⟨e1, e2, e3, e4⟩ := hq
  refine ve_of h e3 e4 (fun d q u _ hu => by rw [e1]; exact hu) (fun v hv hs => ?_)
  obtain ⟨x, scp, y, n, hx, hsc, hrn, hy, ha, hq⟩ := Sched.schedulable_inv hs
  have hx' : σ.kheap v = some (.tcb x) := by
    by_cases ev : v = p
    · subst ev
      rcases hr.2 with e | ⟨y0, n0, y', h1, h2, -⟩
      · rw [← e]; exact hx
      · rw [h2] at hx; cases hx
    · rw [← hr.1 v ev]; exact hx
  have es : scp ≠ p := fun es => hv (hb v x hx' (by rw [hsc, es]))
  exact Sched.schedulable_of hx' hsc hrn (by rw [← hr.1 scp es]; exact hy) ha (by rw [← e2]; exact hq)

/-- The bound-TCB fact along sb2's binding frame. -/
theorem bu_br {E' : ObjRef → Prop} {p : ObjRef} {k k' : KHeap}
    (hb : ∀ v x, k v = some (.tcb x) → x.tcbSchedContext = some p → E' v) (h : SInvB.BR k k') :
    ∀ v x, k' v = some (.tcb x) → x.tcbSchedContext = some p → E' v := by
  intro v x hx hsc
  obtain ⟨x0, hx0⟩ := h.tcb' v x hx
  obtain ⟨x1, hx1, e⟩ := h.tcb v x0 hx0
  rw [hx] at hx1
  injection hx1 with hx1
  injection hx1 with hx1
  subst hx1
  exact hb v x0 hx0 (by rw [← e]; exact hsc)

theorem ht_refill {E' : ObjRef → Prop} {k0 : KHeap} {p : ObjRef}
    (hb : ∀ v x, k0 v = some (.tcb x) → x.tcbSchedContext = some p → E' v) {α : Type} {m : NonDet (State Unit) α}
    (hro : ∀ k, SInvB.HK (SInvB.ROs p k) (SInvB.RN p k) m) (hq : ∀ Q R C A, IK (QRC Q R C A) m) :
    HT (fun s => VE E' s ∧ SInvB.BRs k0 s) (VE E') m := by
  intro σ ⟨h1, h2⟩ x hx
  exact ve_ro h1 (bu_br hb h2) (hro σ.kheap σ (SInvB.RO.refl _ _) x hx).1 (hq _ _ _ _ σ ⟨rfl, rfl, rfl, rfl⟩ x hx)

theorem ht_p1 {E' : ObjRef → Prop} {k0 : KHeap} {α : Type} {m : NonDet (State Unit) α}
    (hv : HT (VE E') (VE E') m) (hs : SInvB.SBK k0 m) :
    HT (fun s => VE E' s ∧ SInvB.BRs k0 s) (fun s => VE E' s ∧ SInvB.BRs k0 s) m :=
  fun σ h x hx => ⟨hv σ h.1 x hx, hs σ h.2 x hx⟩

theorem ht_in {E' : ObjRef → Prop} {u : ObjRef} (hu : E' u) {α : Type} {m : NonDet (State Unit) α}
    (h : HT (VE E') (VE (Ins E' u)) m) : HT (VE E') (VE E') m :=
  ht_conseq (fun _ h => h) (fun _ h => ve_mono (fun v hv => hv.elim id fun e => by subst e; exact hu) h) h

theorem ht_assertOpt_bind {P Q : State Unit → Prop} {α β : Type} {o : Option α} {g : α → NonDet (State Unit) β}
    (h : ∀ u, o = some u → HT P Q (g u)) : HT P Q (NonDet.assertOpt o >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e1, e2⟩ := SInvB.mem_assertOpt' hy
  rw [e2] at hx
  exact h y.1 e1 σ hσ x hx

/-! ## Configure -/

/-- **`invoke_sched_control_configure` keeps `VE E`** (from carried `ScInv`). -/
theorem ht_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) :
    HT (fun s => VE E s ∧ SInvB.ScInv s) (VE E) (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  rcases iv with ⟨p, budget, period, mr, badge, flag⟩
  unfold invokeSchedControlConfigureFlags
  intro σ ⟨hv, hsi⟩ x ⟨y, hy, hx⟩
  obtain ⟨ey, n, hk⟩ := SInvB.mem_getSchedContext' hy
  obtain ⟨sc, σ1⟩ := y
  dsimp only at ey hk hx
  subst ey
  have hbk : ∀ v x, σ1.kheap v = some (.tcb x) → x.tcbSchedContext = some p → sc.scTcb = some v := by
    intro v x hx hsc
    obtain ⟨y', k', h1, h2, -⟩ := SInvB.ScInv.back hsi v x p hx hsc
    rw [hk] at h1
    injection h1 with h1
    injection h1 with h1 h1'
    rw [h1]; exact h2
  refine ht_apply (P := fun s => VE (fun v => E v ∨ sc.scTcb = some v) s ∧ SInvB.BRs σ1.kheap s) ?_
    ⟨ve_mono (fun _ h => Or.inl h) hv, SInvB.BR.refl _⟩ hx
  refine ht_bind (R := fun s => VE (fun v => E v ∨ sc.scTcb = some v) s ∧ SInvB.BRs σ1.kheap s) ?_ fun _ => ?_
  · unfold NonDet.when
    split
    · refine ht_assertOpt_bind fun u hu => ?_
      refine ht_bind (ht_p1 (ht_in (Or.inr hu) (ht_tcbReleaseRemove u)) (SInvB.sb_tcbReleaseRemove u)) fun _ => ?_
      refine ht_bind (ht_p1 (ht_in (Or.inr hu) (ht_dequeue u)) (SInvB.sb_tcbSchedAction _ _)) fun _ => ?_
      refine ht_bind (ht_ik (by ro_auto)) fun _ => ?_
      exact ht_ik (ik_and (by ve_auto) (by sb_auto))
    · exact ht_ik (ik_pure _)
  have hb' : ∀ v x, σ1.kheap v = some (.tcb x) → x.tcbSchedContext = some p → (fun v => E v ∨ sc.scTcb = some v) v :=
    fun v x hx hsc => Or.inr (hbk v x hx hsc)
  split
  rotate_left
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  split
  refine ht_bind (ht_ik (by ro_auto)) fun _ => ht_bind (ht_ik (by ro_auto)) fun _ => ?_
  split
  all_goals
    first
      | refine ht_bind (ht_refill hb' (hk_refillNew p _ _ _) (qrc_refillNew p _ _ _)) fun _ => ?_
      | refine ht_bind (ht_refill hb' (hk_refillUpdate p _ _ _) (qrc_refillUpdate p _ _ _)) fun _ => ?_
  all_goals
    refine ht_bind (R := VE E) ?_ fun _ => ?_
    · unfold NonDet.when
      split
      · refine ht_bind (ht_ik (by ve_auto)) fun _ => ?_
        refine ht_assertOpt_bind fun u hu => ?_
        refine ht_conseq (P := VE (Ins E u))
          (fun _ h => ve_mono (fun v hv => hv.elim Or.inl fun e => Or.inr (Option.some.inj (hu.symm.trans e)).symm) h)
          (fun _ h => h) ?_
        intro s hs x ⟨y, hy, hx⟩
        obtain ⟨x0, hk0, rfl⟩ := SInvQ.q1_mem_threadGet (by exact hy)
        obtain ⟨y2, hy2, hx⟩ := hx
        rw [Set.mem_singleton_iff.1 hy2] at hx
        try dsimp only at hx
        split at hx
        · rename_i hc
          have h1 := ve_rescheduleRequired (E := Ins E u) s hs x hx
          have h2 : x.2.curThread = s.curThread :=
            (by ct_auto : SInv.CTK s.curThread (rescheduleRequired (Z := Unit))) s rfl x hx
          exact ve_drop_ct h1 (h2.trans hc.symm)
        · try unfold NonDet.when at hx
          split at hx
          · exact ht_possibleSwitchTo u s hs x hx
          · rename_i hnr
            rw [Set.mem_singleton_iff.1 hx]
            refine ve_drop hs fun hsch => absurd ?_ hnr
            obtain ⟨x1, -, -, -, hx1, -, hrn, -⟩ := Sched.schedulable_inv hsch
            rw [hk0] at hx1
            injection hx1 with hx1
            injection hx1 with hx1
            subst hx1
            exact hrn
      · rename_i hn
        have hn' : sc.scTcb = none := not_not.1 hn
        intro s hs x hx
        rw [Set.mem_singleton_iff.1 hx]
        exact ve_mono (fun v hv => hv.elim id fun e => by rw [hn'] at e; cases e) hs
    exact ht_bind (ht_ik (by ve_auto)) fun _ => ht_ik (by ve_auto)

/-! ## Remaining cancel-cone / invocation leaves -/

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_finaliseCap _ _)

theorem ve_invokeIrqHandler (iv : IrqHandlerInvocation) : VEK E (invokeIrqHandler (Z := Unit) iv) := by
  unfold invokeIrqHandler; ve_auto

theorem ve_invokeSchedContext (iv : SchedContextInvocation) : VEK E (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ve_auto

theorem ve_domainSetStart (i : Nat) : VEK E (domainSetStart (Z := Unit) i) := by
  unfold domainSetStart; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeIrqHandler _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeSchedContext _)
macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_domainSetStart _)

theorem ve_invokeDomain (iv : DomainInvocation) : VEK E (invokeDomain (Z := Unit) iv) := by
  unfold invokeDomain; ve_auto

macro_rules | `(tactic| ve_leaf) => `(tactic| with_reducible exact ve_invokeDomain _)

end

end Fl4Proofs.P3.SInvR.B8s
