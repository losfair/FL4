/-
P3 (DESIGN.md §9), invariant line G1 (rd8c): **the donation of a released SC**
(spec side only, outside the JAtZ cone; KENTRY-PLAN rd8b handoff 3).

`send_ipc` / `receive_ipc` / `reply_push` donate the caller's SC to a thread
that is (still) receive-blocked and unbound. rd7's `rd_schedContextDonate_free`
covers an SC bound to no thread and a non-blocked receiver; here the SC may
have a holder (dequeued, released-removed and unbound by `sched_context_donate`
itself; `Simple`: it is not the switch target; `T1`: the dequeue empties every
queue of it; `ScFwd`: the holder is bound back, so it is neither the SC nor the
receiver) and the receiver may be `BlkR`, which needs the SC released
(active with a ready head: at a syscall the caller's SC is `cur_sc`, active by
rd7's `CAx`, its head ready by `OffReady`).

* `kt_testReschedule`: heap and time kept.
* **`rd_schedContextDonate_rel`**.
-/
import Fl4Proofs.P3.SpecInvRd8cA
open Classical

namespace Fl4Proofs.P3.SInvR.B8c
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8

noncomputable section

set_option maxHeartbeats 1000000

theorem kt_testReschedule (K : ObjRef → Option KernelObject) (T : Time) (u : ObjRef) :
    IK (KT K T) (testReschedule (Z := Unit) u) := by
  unfold testReschedule
  repeat' (first | exact kt_rescheduleRequired K T | ik_step0 | ik_unfold | (unfold NonDet.when))

/-- **`sched_context_donate p t`** of a released SC to an unbound thread (module docstring):
`Rdy` kept, and afterwards `p` and `t` are bound to each other. -/
theorem rd_schedContextDonate_rel (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none)
    (hrel : ∀ y n, σ.kheap p = some (.schedContext y n) →
      scActive y = true ∧ refillReady σ.curTime (refillHd y) = true)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) :
    Rdy r.2 ∧ (∀ y n, r.2.kheap p = some (.schedContext y n) → y.scTcb = some t) ∧
      (∀ x', r.2.kheap t = some (.tcb x') → x'.tcbSchedContext = some p) := by
  unfold schedContextDonate at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨e, sc, n, hk, hv⟩ := SInvQ.cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  obtain ⟨w, hw, hr⟩ := hr
  have hW : Rdy w.2 ∧ w.2.kheap p = some (.schedContext sc n) ∧ w.2.kheap t = some (.tcb x) ∧
      w.2.curTime = σ.curTime := by
    unfold NonDet.when at hw
    split at hw
    · obtain ⟨a, ha, hw⟩ := hw
      obtain ⟨ha1, ha2⟩ := SInvQ.cq5_mem_assertOpt ha
      obtain ⟨u, a2⟩ := a
      simp only at ha1 ha2; subst a2
      have hsu : sc.scTcb = some u := hv.symm.trans ha1
      obtain ⟨xu, hxu, hxup⟩ := hF p sc n u hk hsu
      have hup : u ≠ p := by rintro rfl; rw [hk] at hxu; cases hxu
      have hut : u ≠ t := by rintro rfl; rw [hx] at hxu; cases hxu; rw [hn] at hxup; cases hxup
      obtain ⟨v, hv1, hw⟩ := hw
      have v1 := rd_dequeue u σ hR v hv1
      obtain ⟨-, v3⟩ := SInvQ.q1_dequeue_hk u σ h1 v hv1
      obtain ⟨xv, -, ev⟩ := SInvQ.q1_tsa_out hv1
      obtain ⟨u', hu', hw⟩ := hw
      have u1 := rd_tcbReleaseRemove u v.2 v1 u' hu'
      obtain ⟨-, eq, ea⟩ :=
        kqa_tcbReleaseRemove v.2.kheap v.2.readyQueues v.2.schedulerAction u v.2 ⟨rfl, rfl, rfl⟩ u' hu'
      obtain ⟨ek, et, -, er⟩ := mem_tcbReleaseRemove hu'
      obtain ⟨s, hs, hw⟩ := hw
      have s1 := rd_threadSet_unbind u u'.2 (fun d q hm => v3 d q (by rw [eq] at hm; exact hm))
        (by rw [ea, ev]; exact hA u) (by rw [er]; intro hm; simp [tcbSchedDequeue] at hm) u1 s hs
      obtain ⟨xs, -, es⟩ := SInv.mem_threadSet hs
      have hkw := kt_testReschedule s.2.kheap s.2.curTime u s.2 ⟨rfl, rfl⟩ w hw
      refine ⟨rd_testReschedule u s.2 s1 w hw, ?_, ?_, ?_⟩
      · rw [hkw.1, es]
        show Function.update u'.2.kheap u _ p = _
        rw [Function.update_of_ne (Ne.symm hup), ek, ev]; exact hk
      · rw [hkw.1, es]
        show Function.update u'.2.kheap u _ t = _
        rw [Function.update_of_ne (Ne.symm hut), ek, ev]; exact hx
      · rw [hkw.2, es]
        show u'.2.curTime = _
        rw [et, ev]
    · obtain rfl := Set.mem_singleton_iff.1 hw
      exact ⟨hR, hk, hx, rfl⟩
  obtain ⟨hRw, hkw, hxw, htw⟩ := hW
  obtain ⟨w2, hw2, hr⟩ := hr
  have hR2 : Rdy w2.2 :=
    rd_updateSchedContext p (scTcbUpdate fun _ => some t) (fun _ => ⟨rfl, rfl, rfl⟩) w.2 hRw w2 hw2
  obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext hw2
  rw [hkw] at hk2; cases hk2
  have hpt : p ≠ t := fun e => by rw [e, hx] at hk; cases hk
  have hx2 : w2.2.kheap t = some (.tcb x) := by rw [e2]; simp [Function.update_of_ne (Ne.symm hpt), hxw]
  have hkp2 : w2.2.kheap p = some (.schedContext (scTcbUpdate (fun _ => some t) sc) n) := by rw [e2]; simp
  have ht2 : w2.2.curTime = σ.curTime := by rw [e2]; exact htw
  obtain ⟨x3, hx3, e3⟩ := SInv.mem_threadSet hr
  rw [hx2] at hx3; cases hx3
  obtain ⟨hq, ha, hrq⟩ := free_of_rdy hR2 hx2 hn
  obtain ⟨hya, hyr⟩ := hrel sc n hk
  refine ⟨?_, fun y m hy => ?_, fun x' hx' => ?_⟩
  · rw [e3]
    refine rdy_upd_bind' hR2 t x _ hx2 (fun _ c hc => ?_) hq ha hrq
    obtain rfl : p = c := Option.some.inj hc
    exact ⟨_, n, hkp2, hya, by rw [ht2]; exact hyr⟩
  · rw [e3] at hy; dsimp only at hy
    rw [Function.update_of_ne hpt, hkp2] at hy; cases hy; rfl
  · rw [e3] at hx'; dsimp only at hx'
    rw [Function.update_self] at hx'; cases hx'; rfl

end

end Fl4Proofs.P3.SInvR.B8c
