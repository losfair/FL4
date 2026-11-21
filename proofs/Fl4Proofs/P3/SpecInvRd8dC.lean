/-
P3 (DESIGN.md §9), invariant line G1 (rd8d): **`reply_remove`'s donation**
(spec side only, outside the JAtZ cone; KENTRY-PLAN rd8c handoff 1, the
`do_reply_transfer` part).

`reply_remove caller r` gives the SC whose reply stack starts with `r` back to
the caller when the caller is unbound. The caller is `BlockedOnReply` (not
`BlkR`), so the SC need not be released: rd8c's donation with the release
asked only for a `BlkR` receiver (`rd_schedContextDonate_g`; its holder is
dequeued / release-removed / unbound by the donation itself).

* `tv_replyUnlinkSc` (rd8d's TV family): the unlink writes SCs and replies only.
* **`rd_schedContextDonate_g`**: rd8c's `rd_schedContextDonate_rel` with
  `hrel` under `BlkR` of the receiver.
* **`rd_replyRemove`**: from `Rdy`, `T1`, `Simple`, `ScFwd` and the caller not
  `BlkR` (at do_reply_transfer: read `BlockedOnReply r` just before).
-/
import Fl4Proofs.P3.SpecInvRd8dB
open Classical

namespace Fl4Proofs.P3.SInvR.B8d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c

noncomputable section

set_option maxHeartbeats 1000000

theorem tv_replyUnlinkSc {V : ObjRef → Option (ThreadState × Option Fault × Option ObjRef)} (scPtr replyPtr : ObjRef) :
    TVK V (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; tv_auto

/-- **`sched_context_donate p t`** to an unbound thread; the SC released only if
`t` is `BlkR` (rd8c's `rd_schedContextDonate_rel`, generalised). -/
theorem rd_schedContextDonate_g (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none)
    (hrel : BlkR x.tcbState x.tcbFault → ∀ y n, σ.kheap p = some (.schedContext y n) →
      scActive y = true ∧ refillReady σ.curTime (refillHd y) = true)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) : Rdy r.2 := by
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
  rw [e3]
  refine rdy_upd_bind' hR2 t x _ hx2 (fun hB c hc => ?_) hq ha hrq
  obtain rfl : p = c := Option.some.inj hc
  obtain ⟨hya, hyr⟩ := hrel hB sc n hk
  exact ⟨_, n, hkp2, hya, by rw [ht2]; exact hyr⟩

/-- **`reply_remove caller r`** keeps `Rdy`, with the donation back to an
unbound caller that is not `BlkR`. -/
theorem rd_replyRemove (caller r : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ)
    (hst : ∀ x, σ.kheap caller = some (.tcb x) → ¬ BlkR x.tcbState x.tcbFault)
    {y : Unit × State Unit} (hy : y ∈ (replyRemove (Z := Unit) caller r σ).1) : Rdy y.2 := by
  unfold replyRemove at hy
  obtain ⟨⟨a1, s1⟩, hz1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  obtain ⟨⟨a2, s2⟩, hz2, hy⟩ := hy
  have e2 : s2 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz2
  subst s2
  obtain ⟨z3, hz3, hy⟩ := hy
  obtain rfl := Set.mem_singleton_iff.1 hz3
  dsimp only at hy
  rcases hw : scWithReply r σ with _ | scPtr
  · simp only [hw] at hy
    first
    | exact rd_replyUnlinkTcb caller r σ hR y hy
    | (obtain ⟨z, hz, hy⟩ := hy
       obtain rfl := Set.mem_singleton_iff.1 hz
       exact rd_replyUnlinkTcb caller r _ hR y hy)
  · simp only [hw] at hy
    obtain ⟨⟨a4, s4⟩, hz4, hy⟩ := hy
    have e4 : s4 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz4
    subst s4
    obtain ⟨z5, hz5, hy⟩ := hy
    obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    have e6 : Rdy z6.2 := rd_replyUnlinkSc scPtr r σ hR z6 hz6
    have v6 : SVK.SVS σ z6.2 := SVK.sv_replyUnlinkSc' scPtr r σ z6 hz6
    have q6 : SInvQ.T1 z6.2 := SInvQ.q1_replyUnlinkSc scPtr r σ h1 z6 hz6
    have t6 : TV (TVv σ) z6.2 := tv_replyUnlinkSc scPtr r σ rfl z6 hz6
    obtain ⟨z7, hz7, hy⟩ := hy
    have e7 : Rdy z7.2 := by
      unfold NonDet.when at hz7
      split at hz7
      · rename_i hg
        have ev := congrFun t6 caller
        unfold TVv at ev
        rw [hx5] at ev
        cases hk : z6.2.kheap caller with
        | none => rw [hk] at ev; simp [B8c.tcbV] at ev
        | some o =>
          rw [hk] at ev
          cases o with
          | tcb x6 =>
            simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
            obtain ⟨es, ef, ec⟩ := ev
            refine rd_schedContextDonate_g scPtr caller z6.2 e6 q6 (simple_svs hA v6) (fwd_svs hF v6) hk
              (ec.trans hg.2) (fun hB => absurd (by rw [← es, ← ef]; exact hB) (hst x5 hx5)) hz7
          | _ => simp [B8c.tcbV] at ev
      · obtain rfl := Set.mem_singleton_iff.1 hz7
        exact e6
    exact rd_replyUnlinkTcb caller r z7.2 e7 y hy

end

end Fl4Proofs.P3.SInvR.B8d
