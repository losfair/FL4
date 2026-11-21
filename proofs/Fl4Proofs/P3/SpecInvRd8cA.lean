/-
P3 (DESIGN.md §9), invariant line G1 (rd8c): **`Rdy` across
`invoke_sched_control_configure_flags`** (spec side only, outside the JAtZ
cone; KENTRY-PLAN rd8b handoff 1).

* The front (`tcb_release_remove`, `tcb_sched_dequeue` of the SC's thread)
  keeps the heap and every `cfS` scalar (`trr_out`, `deq_out`), so `OffReady`
  and `Suff` reach `commit_time` (rd's `rdy_commitTime`, when the SC is
  `cur_sc`); the dequeued thread is in no ready queue by `T1` (`deq_out`).
  `FrontOut`: what the front leaves.
* The middle is rd8b's `rd_refillNew` (both arms) or `rd_refillUpdate`, whose
  `Excl` comes from `ScBackS` (the only TCB bound to the SC is its `sc_tcb`,
  just dequeued), `Simple` (no switch target) and the branch guard (runnable,
  so not `BlkR`): `excl_front`.
* **`rd_possibleSwitchTo_r`**: rd6's `possible_switch_to` lemma with the
  release-queue test of its guard: the target needs `RdyT` only when bound and
  not released-queued.
* The tail (`rd_cfgTail`): `sched_context_resume` (rd7's
  `sr_schedContextResume`: afterwards the thread, when schedulable, is
  `RdyT`), `reschedule_required` or, for a runnable thread, `possible_switch_to`
  (the SC is active since `MIN_REFILLS ≤ refill max`, so bound + runnable +
  not released-queued is `schedulable`), then the badge / sporadic updates.
* **`rd_configure`**.
-/
import Fl4Proofs.P3.SpecInvRd8bC
open Classical

namespace Fl4Proofs.P3.SInvR.B8c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The front -/

/-- **`tcb_release_remove t`**: heap, queues, scalars and action kept, `t` out of the release queue. -/
theorem trr_out {t : ObjRef} {σ : State Unit} {r : Unit × State Unit}
    (hr : r ∈ (tcbReleaseRemove (Z := Unit) t σ).1) :
    r.2.kheap = σ.kheap ∧ r.2.readyQueues = σ.readyQueues ∧ cfS r.2 = cfS σ ∧
      r.2.schedulerAction = σ.schedulerAction ∧ t ∉ r.2.releaseQueue := by
  unfold tcbReleaseRemove setReleaseQueue at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hz
  obtain ⟨w, hw, hr⟩ := hr
  obtain ⟨v, hv, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hv
  obtain rfl := Set.mem_singleton_iff.1 hr
  have hn : t ∉ tcbSchedDequeue t σ.releaseQueue := by simp [tcbSchedDequeue]
  unfold NonDet.when at hw
  split at hw
  · obtain rfl := Set.mem_singleton_iff.1 hw
    exact ⟨rfl, rfl, rfl, rfl, hn⟩
  · obtain rfl := Set.mem_singleton_iff.1 hw
    exact ⟨rfl, rfl, rfl, rfl, hn⟩

/-- **`tcb_sched_dequeue t`**: only the queues change, and with `T1` `t` is in none of them. -/
theorem deq_out {t : ObjRef} {σ : State Unit} (h1 : SInvQ.T1 σ) {r : Unit × State Unit}
    (hr : r ∈ (tcbSchedAction (Z := Unit) tcbSchedDequeue t σ).1) :
    r.2.kheap = σ.kheap ∧ cfS r.2 = cfS σ ∧ r.2.schedulerAction = σ.schedulerAction ∧
      ∀ d q, t ∉ r.2.readyQueues d q := by
  obtain ⟨x, hx, e⟩ := SInvQ.q1_tsa_out hr
  rw [e]
  refine ⟨rfl, rfl, rfl, fun d q hm => ?_⟩
  dsimp only at hm
  split at hm
  · simp [tcbSchedDequeue] at hm
  · rename_i hdq
    obtain ⟨x', hx', h1d, h1p⟩ := h1 d q t hm
    rw [hx] at hx'; cases hx'
    exact hdq ⟨h1d.symm, h1p.symm⟩

theorem offReady_congr {σ σ' : State Unit} (h : Sched.OffReady σ) (hk : σ'.kheap = σ.kheap)
    (hc : cfS σ' = cfS σ) : Sched.OffReady σ' := by
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨e1, e2, -, -, -, e6⟩ := hc
  intro y n hy
  rw [hk, e2] at hy
  rw [e1, e6]; exact h y n hy

theorem suff_congr {σ σ' : State Unit} (h : Suff σ) (hk : σ'.kheap = σ.kheap)
    (hc : cfS σ' = cfS σ) : Suff σ' := by
  simp only [cfS, Prod.mk.injEq] at hc
  obtain ⟨e1, e2, -, -, e5, -⟩ := hc
  intro y n hy ha hi
  rw [hk, e2] at hy
  rw [e1]; exact h y n hy ha (by rw [← e2, ← e5]; exact hi)

/-- What the front of configure leaves: `Rdy`, the action and the time kept, every
object but the SC kept, the SC's thread, max and non-empty refills kept, and the SC's
thread in no ready queue. -/
def FrontOut (σ : State Unit) (p : ObjRef) (sc : SchedContext) (n : Nat) (s : State Unit) : Prop :=
  Rdy s ∧ s.schedulerAction = σ.schedulerAction ∧ s.curTime = σ.curTime ∧
    (∀ q, q ≠ p → s.kheap q = σ.kheap q) ∧
    (∃ y, s.kheap p = some (.schedContext y n) ∧ y.scTcb = sc.scTcb ∧ y.scRefillMax = sc.scRefillMax ∧
      (scActive y = true → y.scRefills ≠ [])) ∧
    (∀ t, sc.scTcb = some t → ∀ d q, t ∉ s.readyQueues d q)

theorem frontOut_refl {σ : State Unit} {p : ObjRef} {sc : SchedContext} {n : Nat} (hR : Rdy σ)
    (hk : σ.kheap p = some (.schedContext sc n)) (hN : SInvB.RNE σ) (hn : sc.scTcb = none) :
    FrontOut σ p sc n σ :=
  ⟨hR, rfl, rfl, fun _ _ => rfl, ⟨sc, hk, rfl, rfl, fun ha => hN p sc n hk (Or.inr ha)⟩,
    fun t ht => by rw [hn] at ht; cases ht⟩

/-- **The front** (`sc_tcb = some t`). -/
theorem cfg_front (p t : ObjRef) (sc : SchedContext) (n : Nat) (σ : State Unit) (hR : Rdy σ)
    (hO : Sched.OffReady σ) (hS : Suff σ) (hN : SInvB.RNE σ) (h1 : SInvQ.T1 σ)
    (hk : σ.kheap p = some (.schedContext sc n)) (ht : sc.scTcb = some t) {r : Unit × State Unit}
    (hr : r ∈ ((do
      tcbReleaseRemove (Z := Unit) t
      tcbSchedAction tcbSchedDequeue t
      let curSc ← NonDet.gets fun s : State Unit => s.curSc
      NonDet.when (curSc = p) commitTime) σ).1) : FrontOut σ p sc n r.2 := by
  obtain ⟨w1, hw1, hr⟩ := hr
  obtain ⟨a1, a2, a3, a4, -⟩ := trr_out hw1
  have hR1 := rd_tcbReleaseRemove t σ hR w1 hw1
  obtain ⟨w2, hw2, hr⟩ := hr
  obtain ⟨b1, b2, b3, b4⟩ := deq_out (fun d q u hm => by
    rw [a2] at hm; obtain ⟨x, hx, e1, e2⟩ := h1 d q u hm; exact ⟨x, by rw [a1]; exact hx, e1, e2⟩) hw2
  have hR2 := rd_dequeue t w1.2 hR1 w2 hw2
  have k2 : w2.2.kheap = σ.kheap := b1.trans a1
  have c2 : cfS w2.2 = cfS σ := b2.trans a3
  have act2 : w2.2.schedulerAction = σ.schedulerAction := b3.trans a4
  have tm2 : w2.2.curTime = σ.curTime := by
    have := c2; simp only [cfS, Prod.mk.injEq] at this; exact this.2.2.2.2.2
  obtain ⟨w3, hw3, hr⟩ := hr
  obtain rfl := Set.mem_singleton_iff.1 hw3
  dsimp only at hr
  have hne : scActive sc = true → sc.scRefills ≠ [] := fun ha => hN p sc n hk (Or.inr ha)
  unfold NonDet.when at hr
  split at hr
  · rename_i hcp
    have hkc : w2.2.kheap w2.2.curSc = some (.schedContext sc n) := by rw [hcp, k2]; exact hk
    obtain ⟨hRr, -, y, ey, e1, e2, -, -, e6, -⟩ := rdy_commitTime hR2 hkc (offReady_congr hO k2 c2)
      (suff_congr hS k2 c2) hne hr
    rw [ey] at hRr ⊢
    refine ⟨hRr, act2, tm2, fun q hq => ?_, ⟨y, ?_, e1, e2, fun ha => e6 (hne (by
      simp only [scActive] at ha ⊢; rw [← e2]; exact ha))⟩, fun u hu d q => ?_⟩
    · show (Function.update w2.2.kheap w2.2.curSc _) q = _
      rw [hcp, Function.update_of_ne hq, k2]
    · show (Function.update w2.2.kheap w2.2.curSc _) p = _
      rw [hcp, Function.update_self]
    · rw [ht] at hu; cases hu; exact b4 d q
  · obtain rfl := Set.mem_singleton_iff.1 hr
    exact ⟨hR2, act2, tm2, fun q _ => by rw [k2], ⟨sc, by rw [k2]; exact hk, rfl, rfl, hne⟩,
      fun u hu d q => by rw [ht] at hu; cases hu; exact b4 d q⟩

/-- A runnable state is not `BlkR`. -/
theorem not_blkR {ts : ThreadState} {f : Option Fault} (h : runnable ts = true) : ¬ BlkR ts f := by
  rintro (⟨_, rfl⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, rfl⟩) <;> simp [runnable] at h

/-- **`Excl` after the front** for a runnable SC thread. -/
theorem excl_front {σ s : State Unit} {p t : ObjRef} {sc : SchedContext} {n : Nat}
    (hF : FrontOut σ p sc n s) (hB : SInvB.ScBackS σ) (hA : SInvQ.Simple σ)
    (hk : σ.kheap p = some (.schedContext sc n)) (ht : sc.scTcb = some t)
    {xt : Tcb} (hxt : s.kheap t = some (.tcb xt)) (hrun : runnable xt.tcbState = true) : Excl s p := by
  obtain ⟨-, hact, -, hko, ⟨y, hy, -⟩, hq⟩ := hF
  intro u x hx hc
  have hup : u ≠ p := by rintro rfl; rw [hy] at hx; cases hx
  rw [hko u hup] at hx
  obtain ⟨y', k', hy', hyt, -⟩ := hB u x p hx hc
  rw [hk] at hy'; cases hy'
  rw [ht] at hyt; cases hyt
  rw [hko t hup] at hxt
  rw [hx] at hxt; cases hxt
  exact ⟨hq t ht, by rw [hact]; exact hA t, not_blkR hrun⟩

/-! ## `possible_switch_to` with the release-queue test -/

/-- **`possible_switch_to t`**, `t` `RdyT` when bound and not in the release queue. -/
theorem rd_possibleSwitchTo_r (t : ObjRef) (σ : State Unit)
    (hR : ∀ x c, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some c → t ∉ σ.releaseQueue → RdyT σ t) :
    IKp Rdy σ (possibleSwitchTo (Z := Unit) t) := by
  by_cases hb : ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c ∧ t ∉ σ.releaseQueue
  · obtain ⟨x, c, hx, hc, hq⟩ := hb
    exact rd_possibleSwitchTo_p t σ (hR x c hx hc hq)
  · unfold possibleSwitchTo getTcbObjRef
    refine SInvQ.ikp_threadGet_bind fun x hx => ?_
    refine ikp_gets_bind ?_
    refine SInvQ.ikp_when _ fun hc => ?_
    obtain ⟨c, hc'⟩ := Option.ne_none_iff_exists'.mp hc.1
    have hq : t ∉ σ.releaseQueue := fun hm => hc.2 (by simp [inReleaseQueue, hm])
    exact absurd ⟨x, c, hx, hc', hq⟩ hb

/-! ## The tail -/

/-- The facts the tail reads: the SC, if bound to `t`, still is, `t` bound back, and the SC active. -/
def TailOK (p : ObjRef) (sc : SchedContext) (s : State Unit) : Prop :=
  ∀ t, sc.scTcb = some t →
    (∃ y n, s.kheap p = some (.schedContext y n) ∧ y.scTcb = some t ∧ MIN_REFILLS ≤ y.scRefillMax) ∧
      ∃ x, s.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some p

/-- **The tail of configure** keeps `Rdy`. -/
theorem rd_cfgTail (p : ObjRef) (sc : SchedContext) (badge : Badge) (flag : Data) (s : State Unit)
    (hR : Rdy s) (hT : TailOK p sc s) {y : Unit × State Unit}
    (hy : y ∈ ((do
      NonDet.when (sc.scTcb ≠ none) <| do
        schedContextResume (Z := Unit) p
        let tcbPtr ← NonDet.assertOpt sc.scTcb
        let st ← getThreadState tcbPtr
        let ct ← NonDet.gets fun s : State Unit => s.curThread
        if tcbPtr = ct then rescheduleRequired
        else NonDet.when (runnable st) <| possibleSwitchTo tcbPtr
      setScObjRef scBadgeUpdate p badge
      setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag)) s).1) : Rdy y.2 := by
  obtain ⟨w, hw, hy⟩ := hy
  have hRw : Rdy w.2 := by
    unfold NonDet.when at hw
    split at hw
    · rename_i hc
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hc
      obtain ⟨⟨y0, n0, hk0, hyt, hym⟩, x0, hx0, hx0p⟩ := hT t ht
      have hb : ∀ x, s.kheap t = some (.tcb x) → x.tcbSchedContext = some p := by
        intro x hx; rw [hx0] at hx; cases hx; exact hx0p
      have hp : ∀ y n, s.kheap p = some (.schedContext y n) → y.scTcb = some t := by
        intro y n hy; rw [hk0] at hy; cases hy; exact hyt
      obtain ⟨r, hr, hw⟩ := hw
      have hRr : Rdy r.2 := rd_schedContextResume p s hR r hr
      have hSV : SVK.SVS s r.2 := sv_schedContextResume' p s r hr
      have hSR : SR t r.2 := sr_schedContextResume p t s hp hb hr
      obtain ⟨a, ha, hw⟩ := hw
      obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
      obtain ⟨u, a2⟩ := a
      simp only at ha1 ha2; subst a2
      rw [ht] at ha1; cases ha1
      obtain ⟨v, hv, hw⟩ := hw
      obtain ⟨xt, hxt, rfl⟩ := SInvQ.q1_mem_threadGet hv
      obtain ⟨v2, hv2, hw⟩ := hw
      obtain rfl := Set.mem_singleton_iff.1 hv2
      dsimp only at hw
      split at hw
      · exact rd_rescheduleRequired r.2 hRr w hw
      · split at hw
        · rename_i hrun
          refine rd_possibleSwitchTo_r t r.2 (fun x c hx hc hq => hSR ?_) hRr w hw
          rw [hxt] at hx; cases hx
          -- the binding and the SC's activity along `SVS`
          have e2 := hSV.1 p; rw [hk0] at e2
          obtain ⟨y', hy', -, hm', -⟩ := SVK.sv_sc (o := r.2.kheap p) e2
          have e1 := hSV.1 t; rw [hx0] at e1
          obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := r.2.kheap t) e1
          rw [hxt] at hx'; cases hx'
          have hcp : xt.tcbSchedContext = some p := hxs.trans hx0p
          refine Sched.schedulable_of hxt hcp hrun hy' ?_ hq
          exact active_of_min (hm' ▸ hym)
        · obtain rfl := Set.mem_singleton_iff.1 hw
          exact hRr
    · obtain rfl := Set.mem_singleton_iff.1 hw
      exact hR
  obtain ⟨w2, hw2, hy⟩ := hy
  have hR2 := rd_updateSchedContext p (scBadgeUpdate fun _ => badge) (fun _ => ⟨rfl, rfl, rfl⟩) w.2 hRw w2 hw2
  exact rd_updateSchedContext p (scSporadicUpdate fun _ => testBit flag scSporadicFlag) (fun _ => ⟨rfl, rfl, rfl⟩)
    w2.2 hR2 y hy

/-- After a refill writer at the SC: `TailOK`. -/
theorem tailOK_mid {σ s s2 : State Unit} {p : ObjRef} {sc z : SchedContext} {n : Nat}
    (hF : FrontOut σ p sc n s) (hFw : SInvB.ScFwd σ) (hk : σ.kheap p = some (.schedContext sc n))
    (e : s2 = Sched.updSc s p z n) (hzt : z.scTcb = sc.scTcb) (hzm : MIN_REFILLS ≤ z.scRefillMax) :
    TailOK p sc s2 := by
  obtain ⟨-, -, -, hko, -, -⟩ := hF
  intro t ht
  obtain ⟨x, hx, hxp⟩ := hFw p sc n t hk ht
  have htp : t ≠ p := by rintro rfl; rw [hk] at hx; cases hx
  subst e
  refine ⟨⟨z, n, SInvE.updSc_kheap_self _ _ _ _, hzt.trans ht, hzm⟩, x, ?_, hxp⟩
  rw [updSc_other s p z n t htp, hko t htp, hx]

/-! ## The wrapper -/

/-- **`invoke_sched_control_configure_flags`** keeps `Rdy` (rd8b handoff 1): `OffReady ∧ Suff`
(rd7's `OS` first disjunct at a perform), sb2's `ScSym` / `RNE`, ctq's `T1` / `Simple`, and the
decode's `MIN_BUDGET ≤ budget` (epq2's `CfgDec`) and `MIN_REFILLS ≤ refills`. -/
theorem rd_configure (p : ObjRef) (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data) (σ : State Unit)
    (hO : Sched.OffReady σ) (hS : Suff σ) (hSy : SInvB.ScSym σ) (hN : SInvB.RNE σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hb : MIN_BUDGET ≤ b) (hm : MIN_REFILLS ≤ mr) :
    IKp Rdy σ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per mr badge flag)) := by
  intro hR y hy
  unfold invokeSchedControlConfigureFlags at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨e, n, hk⟩ := SInvQ.cq5_mem_getSc hz
  obtain ⟨sc, z2⟩ := z
  simp only at e hk; subst z2
  obtain ⟨w, hw, hy⟩ := hy
  have hF : FrontOut σ p sc n w.2 := by
    unfold NonDet.when at hw
    split at hw
    · rename_i hc
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hc
      obtain ⟨a, ha, hw⟩ := hw
      obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
      obtain ⟨u, a2⟩ := a
      simp only at ha1 ha2; subst a2
      rw [ht] at ha1; cases ha1
      exact cfg_front p t sc n σ hR hO hS hN h1 hk ht hw
    · rename_i hc
      obtain rfl := Set.mem_singleton_iff.1 hw
      exact frontOut_refl hR hk hN (not_not.mp hc)
  obtain ⟨hR1, -, -, -, ⟨y1, hk1, hy1t, hy1m, hy1n⟩, -⟩ := id hF
  have hFw : SInvB.ScFwd σ := hSy.2
  dsimp only at hy
  -- every refill writer, then the tail
  have mid_new : ∀ (mr' : Nat) (per' : Ticks), MIN_REFILLS ≤ mr' →
      ∀ y ∈ ((refillNew (Z := Unit) p mr' b per' >>= fun _ => (do
        NonDet.when (sc.scTcb ≠ none) <| do
          schedContextResume (Z := Unit) p
          let tcbPtr ← NonDet.assertOpt sc.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired
          else NonDet.when (runnable st) <| possibleSwitchTo tcbPtr
        setScObjRef scBadgeUpdate p badge
        setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag))) w.2).1, Rdy y.2 := by
    intro mr' per' hm' y hy
    obtain ⟨v, hv, hy⟩ := hy
    have hRv := rd_refillNew p mr' b per' w.2 hR1 hk1 hm' hb hv
    obtain ⟨z, ez, hzt, hzm, -⟩ := refillNew_out hk1 mr' b per' hv
    exact rd_cfgTail p sc badge flag v.2 hRv
      (tailOK_mid hF hFw hk ez (hzt.trans hy1t) (hzm ▸ hm')) hy
  split at hy
  · exact mid_new MIN_REFILLS 0 le_rfl y hy
  · rw [Notif.nd_bind_one (Sched.getScActive_eq hk1)] at hy
    try dsimp only at hy
    split at hy
    · rename_i hc
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hc.2
      obtain ⟨a, ha, hy⟩ := hy
      obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
      obtain ⟨u, a2⟩ := a
      simp only at ha1 ha2; subst a2
      rw [ht] at ha1; cases ha1
      obtain ⟨v, hv, hy⟩ := hy
      obtain ⟨xt, hxt, rfl⟩ := SInvQ.q1_mem_threadGet hv
      dsimp only at hy
      split at hy
      · rename_i hrun
        have hX : Excl w.2 p := excl_front hF hSy.1 hA hk ht hxt hrun
        obtain ⟨v, hv, hy⟩ := hy
        have hya : scActive y1 = true := hc.1
        have hne : y1.scRefills ≠ [] := hy1n hya
        have hRv := rd_refillUpdate p per b mr w.2 hR1 hk1 hne hya hm hb hX hv
        obtain ⟨z, ez, hzt, hzm, -⟩ := refillUpdate_out hk1 hne per b mr hv
        exact rd_cfgTail p sc badge flag v.2 hRv
          (tailOK_mid hF hFw hk ez (hzt.trans hy1t) (hzm ▸ hm)) hy
      · exact mid_new mr per hm y hy
    · exact mid_new mr per hm y hy

end

end Fl4Proofs.P3.SInvR.B8c
