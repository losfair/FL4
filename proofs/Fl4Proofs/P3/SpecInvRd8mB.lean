/-
P3 (DESIGN.md §9), invariant line G1 (rd8m, KENTRY-PLAN rd14a FINDING): **the
donation chain without `Simple`** (spec side only, outside the JAtZ cone).

rd14a found `Simple` (no switch target) FALSE at reachable first-phase outcomes
of ReplyRecv / NBSendRecv / NBSendWait (the send half's possible_switch_to under
resume_cur_thread). rd8c's `rd_schedContextDonate_rel` reads `Simple` only for
"the donated SC's current holder is not the switch target". Here that is the
hypothesis:

* `NSwP p s` (no TCB bound to `p` is the switch target), `NSwT t s` (`NSwP` of
  `t`'s SC), `nswP_svs` / `nswT_svs` (along rd8d's SVS steps), **`nswT_of`**
  (sb2's `ScBackS` makes the holder unique: `NSw t ∧ ScInv ⇒ NSwT t`; at
  handle_recv `NSw ct` is ctq's `NP ct`), `nswT_upd` (a write of `t` keeping
  its SC).
* `rd_schedContextDonate_relN` / `_relTN`, `rd_replyPush_dN`, `rd_sendArm_dN`,
  **`rd_sendIpc_dN`** (rd8c / rd8d / rd8m-A's lemmas, `Simple` ↦ `NSwT`).
* `HBN t := Rdy ∧ RT t ∧ T1 ∧ NSwT t ∧ ScInv`, `rd_sendFaultIpcN`,
  **`rd_hfN`** (`handle_fault` for a possibly unbound thread, no `Simple`).
-/
import Fl4Proofs.P3.SpecInvRd8mA
open Classical

namespace Fl4Proofs.P3.SInvR.B8m

noncomputable section

set_option maxHeartbeats 1000000

section N
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d

/-- No TCB bound to `p` is the switch target. -/
def NSwP (p : ObjRef) (s : State Unit) : Prop :=
  ∀ u xu, s.kheap u = some (.tcb xu) → xu.tcbSchedContext = some p → s.schedulerAction ≠ .switchThread u

/-- `NSwP` of `t`'s SC (if bound). -/
def NSwT (t : ObjRef) (s : State Unit) : Prop :=
  ∀ x c, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c → NSwP c s

theorem nswP_svs {s s' : State Unit} {p : ObjRef} (h : NSwP p s) (hS : SVK.SVS s s') : NSwP p s' := by
  intro u xu' hxu' hc e
  have e1 := hS.1 u
  rw [hxu'] at e1
  obtain ⟨y, hy, hyc⟩ := SVK.sv_tcb (o := s.kheap u) e1.symm
  rcases hS.2.2 with e' | e' <;> rw [e'] at e
  · exact h u y hy (hyc.trans hc) e
  · cases e

theorem nswT_svs {s s' : State Unit} {t : ObjRef} (h : NSwT t s) (hS : SVK.SVS s s') : NSwT t s' := by
  intro x' c hx' hc
  have e1 := hS.1 t
  rw [hx'] at e1
  obtain ⟨y, hy, hyc⟩ := SVK.sv_tcb (o := s.kheap t) e1.symm
  exact nswP_svs (h y c hy (hyc.trans hc)) hS

/-- **`NSw t ∧ ScInv ⇒ NSwT t`**: the holder of `t`'s SC is `t` (sb2's `ScBackS`). -/
theorem nswT_of {s : State Unit} {t : ObjRef} (hI : SInvB.ScInv s) (hN : s.schedulerAction ≠ .switchThread t) :
    NSwT t s := by
  intro x c hx hc u xu hxu hxuc
  obtain ⟨y0, k0, hy0, hyT, -⟩ := hI.back t x c hx hc
  obtain ⟨y1, k1, hy1, hyU, -⟩ := hI.back u xu c hxu hxuc
  rw [hy0] at hy1; cases hy1
  obtain rfl : u = t := Option.some.inj (hyU.symm.trans hyT)
  exact hN

/-- `NSwT t` across a write of `t`'s TCB keeping its SC and the action. -/
theorem nswT_upd {s s' : State Unit} {t : ObjRef} {x x' : Tcb} (hx : s.kheap t = some (.tcb x))
    (hk' : s'.kheap = Function.update s.kheap t (some (.tcb x'))) (ha : s'.schedulerAction = s.schedulerAction)
    (hsc : x'.tcbSchedContext = x.tcbSchedContext) (h : NSwT t s) : NSwT t s' := by
  have hk : ∀ q, q ≠ t → s'.kheap q = s.kheap q := fun q hq => by rw [hk']; exact Function.update_of_ne hq _ _
  have ht : s'.kheap t = some (.tcb x') := by rw [hk']; exact Function.update_self _ _ _
  intro x'' c hx'' hc u xu hxu hxuc
  rw [ht] at hx''; cases hx''
  have hc0 : x.tcbSchedContext = some c := hsc.symm.trans hc
  rw [ha]
  by_cases e : u = t
  · subst e; exact h x c hx hc0 u x hx hc0
  · exact h x c hx hc0 u xu (by rw [← hk u e]; exact hxu) hxuc

theorem rd_schedContextDonate_relN (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : NSwP p σ) (hF : SInvB.ScFwd σ) {x : Tcb} (hx : σ.kheap t = some (.tcb x))
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
        (by rw [ea, ev]; exact hA u xu hxu hxup) (by rw [er]; intro hm; simp [tcbSchedDequeue] at hm) u1 s hs
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


theorem rd_schedContextDonate_relTN (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : NSwP p σ) (hF : SInvB.ScFwd σ) {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none)
    (hrel : ∀ y n, σ.kheap p = some (.schedContext y n) →
      scActive y = true ∧ refillReady σ.curTime (refillHd y) = true)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) :
    Rdy r.2 ∧ RdyT r.2 t := by
  refine ⟨(rd_schedContextDonate_relN p t σ hR h1 hA hF hx hn hrel hr).1, ?_⟩
  unfold schedContextDonate at hr
  obtain ⟨z, hz, hr⟩ := hr
  obtain ⟨e, sc, n, hk, hv⟩ := SInvQ.cq5_mem_getScObjRef hz
  obtain ⟨z1, z2⟩ := z
  simp only at e hv; subst z2
  obtain ⟨w, hw, hr⟩ := hr
  have hW : w.2.kheap p = some (.schedContext sc n) ∧ w.2.kheap t = some (.tcb x) ∧
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
      obtain ⟨xv, -, ev⟩ := SInvQ.q1_tsa_out hv1
      obtain ⟨u', hu', hw⟩ := hw
      obtain ⟨ek, et, -, er⟩ := mem_tcbReleaseRemove hu'
      obtain ⟨s, hs, hw⟩ := hw
      obtain ⟨xs, -, es⟩ := SInv.mem_threadSet hs
      have hkw := kt_testReschedule s.2.kheap s.2.curTime u s.2 ⟨rfl, rfl⟩ w hw
      refine ⟨?_, ?_, ?_⟩
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
      exact ⟨hk, hx, rfl⟩
  obtain ⟨hkw, hxw, htw⟩ := hW
  obtain ⟨w2, hw2, hr⟩ := hr
  obtain ⟨y2, n2, hk2, e2⟩ := SInvB.mem_updateSchedContext hw2
  rw [hkw] at hk2; cases hk2
  have hpt : p ≠ t := fun e => by rw [e, hx] at hk; cases hk
  have hx2 : w2.2.kheap t = some (.tcb x) := by rw [e2]; simp [Function.update_of_ne (Ne.symm hpt), hxw]
  have hkp2 : w2.2.kheap p = some (.schedContext (scTcbUpdate (fun _ => some t) sc) n) := by rw [e2]; simp
  have ht2 : w2.2.curTime = σ.curTime := by rw [e2]; exact htw
  obtain ⟨x3, hx3, e3⟩ := SInv.mem_threadSet hr
  rw [hx2] at hx3; cases hx3
  obtain ⟨hya, hyr⟩ := hrel sc n hk
  rw [e3]
  refine ⟨_, p, scTcbUpdate (fun _ => some t) sc, n, Function.update_self .., rfl, ?_, hya, ?_⟩
  · show Function.update w2.2.kheap t _ p = _
    rw [Function.update_of_ne hpt, hkp2]
  · show refillReady w2.2.curTime _ = true
    rw [ht2]; exact hyr


theorem rd_replyPush_dN (caller callee rp : ObjRef) (cd : Bool) (s : State Unit) (hR : Rdy s)
    (h1 : SInvQ.T1 s) (hA : NSwT caller s) (hF : SInvB.ScFwd s) (hc : cd = true → B8d.RT s caller)
    {y : Unit × State Unit} (hy : y ∈ (replyPush (Z := Unit) caller callee rp cd s).1) :
    Rdy y.2 ∧ (B8d.RT s callee → B8d.RT y.2 callee) := by
  unfold replyPush at hy
  obtain ⟨z1, hz1, hy⟩ := hy
  obtain ⟨xc, hxc, rfl⟩ := SInvQ.q1_mem_threadGet hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  obtain ⟨xe, hxe, rfl⟩ := SInvQ.q1_mem_threadGet hz2
  dsimp only at hy
  obtain ⟨z3, hz3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_setReplyObjRef' _ _ _ s hR z3 hz3
  have v3 : SVK.SVS s z3.2 := sv_setReplyObjRef' _ _ _ s z3 hz3
  have q3 : SInvQ.T1 z3.2 := q1_setReplyObjRef' _ _ _ s h1 z3 hz3
  obtain ⟨z4, hz4, hy⟩ := hy
  have e4 : Rdy z4.2 := rd_setThreadState caller (.blockedOnReply rp) trivial z3.2 e3 z4 hz4
  have v4 : SVK.SVS s z4.2 := v3.trans (SVK.sv_setThreadState' caller _ z3.2 z4 hz4)
  have q4 : SInvQ.T1 z4.2 := SInvQ.q1_setThreadState caller _ z3.2 q3 z4 hz4
  unfold NonDet.when at hy
  split at hy
  · rename_i hg
    obtain ⟨c, hcc⟩ := Option.ne_none_iff_exists'.mp hg.1
    rw [hcc] at hy
    obtain ⟨z5, hz5, hy⟩ := hy
    have e5 : Rdy z5.2 := rd_bindScReply c rp z4.2 e4 z5 hz5
    have v5 : SVK.SVS s z5.2 := v4.trans (SVK.sv_bindScReply' c rp z4.2 z5 hz5)
    have q5 : SInvQ.T1 z5.2 := SInvQ.q1_bindScReply c rp z4.2 q4 z5 hz5
    have hxe5 := v5.1 callee
    rw [hxe] at hxe5
    obtain ⟨xe5, hk5, hb5⟩ := SVK.sv_tcb (o := z5.2.kheap callee) hxe5
    have hxc5 := v5.1 caller
    rw [hxc] at hxc5
    obtain ⟨xc5, hkc5, hbc5⟩ := SVK.sv_tcb (o := z5.2.kheap caller) hxc5
    obtain ⟨r1, r2⟩ := rd_schedContextDonate_relTN c callee z5.2 e5 q5 (nswP_svs (hA xc c hxc hcc) v5) (fwd_svs hF v5)
      hk5 (hb5.trans hg.2.1) (rel_of_rdyT (rdyT_svs (hc hg.2.2 xc c hxc hcc) v5) hkc5 (hbc5.trans hcc)) hy
    exact ⟨r1, fun _ => rT_of_rdyT r2⟩
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨e4, fun hT => rT_svs hT v4⟩


theorem rd_sendArm_dN (call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr dest : ObjRef)
    (reply : Option ObjRef) (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : NSwT thread s)
    (hF : SInvB.ScFwd s) (hct : B8d.RT s thread) (hcd : cd = true → RdyT s thread) (hRT : B8d.RT s dest)
    (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) thread (some epptr) badge cg dest
      NonDet.maybeM (replyUnlinkTcb (Z := Unit) dest) reply
      let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      let fault ← threadGet (Z := Unit) Tcb.tcbFault thread
      if call ∨ fault ≠ none then
        if (cg ∨ cgr) ∧ reply ≠ none then
          replyPush (Z := Unit) thread dest (the reply) cd
        else
          setThreadState (Z := Unit) thread .inactive
      else NonDet.when (cd ∧ scOpt = none) <| do
        let threadSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext thread
        schedContextDonate (Z := Unit) (the threadSc) dest
      setThreadState (Z := Unit) dest .running
      let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
      ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
      possibleSwitchTo (Z := Unit) dest) s).1) : Rdy y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer thread (some epptr) badge cg dest s hs z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' thread (some epptr) badge cg dest s z3 h3
  have q3 : SInvQ.T1 z3.2 := SInvQ.q1_doIpcTransfer thread (some epptr) badge cg dest s h1 z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have e4 : Rdy z4.2 := (ik_maybeM (fun r => rd_replyUnlinkTcb dest r) reply) z3.2 e3 z4 h4
  have v4 : SVK.SVS s z4.2 :=
    v3.trans (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb dest r) reply z3.2 z4 h4)
  have q4 : SInvQ.T1 z4.2 := (ik_maybeM (fun r => SInvQ.q1_replyUnlinkTcb dest r) reply) z3.2 q3 z4 h4
  have hA4 := nswT_svs hA v4
  have hF4 := fwd_svs hF v4
  have hc4 := B8d.rT_svs hct v4
  have hd4 : cd = true → RdyT z4.2 thread := fun h => rdyT_svs (hcd h) v4
  have hT4 := B8d.rT_svs hRT v4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨e7, t7⟩ := rd_replyPush_dN thread dest _ cd z4.2 e4 q4 hA4 hF4 (fun _ => hc4) h7
      exact rd_sendTail dest z7.2 e7 (t7 hT4) y hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact rd_sendTail dest z7.2 (rd_setThreadState thread .inactive trivial z4.2 e4 z7 h7)
        (B8d.rT_svs hT4 (SVK.sv_setThreadState' thread .inactive z4.2 z7 h7)) y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    unfold NonDet.when at h7
    split at h7
    · rename_i hg
      obtain ⟨z8, h8, h7⟩ := h7
      obtain ⟨x8, hx8, rfl⟩ := SInvQ.q1_mem_threadGet h8
      have hc4' := hd4 hg.1
      obtain ⟨xt, c, yc, nc, hxt, hcc, -, -, -⟩ := id hc4'
      rw [hxt] at hx8
      cases hx8
      dsimp only at h7
      rw [hcc] at h7
      obtain ⟨r1, r2⟩ := rd_schedContextDonate_relTN c dest z4.2 e4 q4 (hA4 _ c hxt hcc) hF4 hx5 hg.2
        (rel_of_rdyT hc4' hxt hcc) h7
      exact rd_sendTail dest z7.2 r1 (B8d.rT_of_rdyT r2) y hy
    · obtain rfl := Set.mem_singleton_iff.1 h7
      exact rd_sendTail dest z4.2 e4 hT4 y hy

/-- **`send_ipc` from an `RT` sender**, `RdyT` only when `canDonate`. -/
theorem rd_sendIpc_dN (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hct : B8d.RT σ thread) (hcd : cd = true → RdyT σ thread) (h1 : SInvQ.T1 σ)
    (hA : NSwT thread σ) (hF : SInvB.ScFwd σ) :
    IKp Rdy σ (sendIpc (Z := Unit) block call badge cg cgr cd thread epptr) := by
  unfold sendIpc
  intro hσ y ⟨z, hz, hy⟩
  obtain ⟨hk, ez⟩ := SInvI.mem_getSimpleKo hz
  obtain ⟨ep, z2⟩ := z
  simp only at hk ez; subst z2
  revert hy
  refine (show IKp Rdy σ _ from ?_) hσ y
  cases ep with
  | idleEP =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · unfold sendIpcBlocked
      exact ikp_bind (B8e.rd_setThreadState_rt thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
  | sendEP q =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · unfold sendIpcBlocked
      exact ikp_bind (B8e.rd_setThreadState_rt thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact ikp_of_ik ik_fail σ
    | cons dest q =>
      cases block
      all_goals
        intro h0 y hy
        obtain ⟨⟨z1a, z1⟩, h1', hy⟩ := hy
        have e1 : Rdy z1 := rd_tcbEpDequeue dest epptr σ h0 _ h1'
        have v1 : SVK.SVS σ z1 := sv_tcbEpDequeue dest epptr σ _ h1'
        have q1 : SInvQ.T1 z1 := SInvQ.q1_tcbEpDequeue dest epptr σ h1 _ h1'
        obtain ⟨z2, h2, hy⟩ := hy
        obtain ⟨x, hx, rfl⟩ := SInvQ.q1_mem_threadGet h2
        dsimp only at hy
        revert hy
        cases hxs : x.tcbState with
        | blockedOnReceive e r d =>
          intro hy
          dsimp only at hy
          obtain ⟨z3, h3, hy⟩ := hy
          rw [Set.mem_singleton_iff.1 h3] at hy
          exact rd_sendArm_dN call badge cg cgr cd thread epptr dest r z1 e1 q1 (nswT_svs hA v1)
            (fwd_svs hF v1) (B8d.rT_svs hct v1) (fun h => rdyT_svs (hcd h) v1)
            (fun x' c hx' hc => by
              rw [hx] at hx'; cases hx'
              exact e1.2.2.1 dest x c hx (Or.inr (Or.inr ⟨e, r, d, hxs⟩)) hc) y hy
        | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)


end N

section H
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8h

/-- The faulting thread's bundle without `Simple` (`t` possibly unbound). -/
def HBN (t : ObjRef) (s : State Unit) : Prop :=
  Rdy s ∧ B8d.RT s t ∧ T1 s ∧ NSwT t s ∧ SInvB.ScInv s

/-- **`send_fault_ipc`** from `HBN t`, `RdyT t` when donating. -/
theorem rd_sendFaultIpcN (t : ObjRef) (cap : Cap) (ex : Fault) (cd : Bool) (s : State Unit) (h : HBN t s)
    (hcd : cd = true → RdyT s t) :
    ∀ y ∈ (sendFaultIpc (Z := Unit) t cap ex cd s).1, Rdy y.2 := by
  intro y hy
  unfold sendFaultIpc at hy
  cases cap
  case endpointCap r b rs =>
    obtain ⟨w1, hw1, hy⟩ := hy
    have r1 : Rdy w1.2 := rd_threadSet_rt (fun tcb => { tcb with tcbFault := some ex }) t s (fun _ => rfl)
      (fun _ => rfl) h.2.1 h.1 w1 hw1
    obtain ⟨x, hx, e⟩ := SInv.mem_threadSet hw1
    obtain ⟨f1, f2, f3⟩ := fh_factsT hx (x' := { x with tcbFault := some ex }) (s' := w1.2) (by rw [e])
      (by rw [e]) (by rw [e]) rfl rfl rfl h.2.1 h.2.2.1 h.2.2.2.2.1.2
    have hd1 : cd = true → RdyT w1.2 t := fun hc =>
      (fh_facts hx (x' := { x with tcbFault := some ex }) (s' := w1.2) (by rw [e])
        (by rw [e]) (by rw [e]) rfl rfl rfl (hcd hc) h.2.2.1 h.2.2.2.2.1.2).1
    have hA : NSwT t w1.2 := nswT_upd hx (x' := { x with tcbFault := some ex }) (by rw [e]) (by rw [e]) rfl
      h.2.2.2.1
    obtain ⟨w2, hw2, hy⟩ := hy
    have r2 := rd_sendIpc_dN true false _ _ _ cd t _ w1.2 f1 hd1 f2 hA f3 r1 w2 hw2
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact r2
  case nullCap => rw [Set.mem_singleton_iff.1 hy]; exact h.1
  all_goals exact hy.elim

/-- **`handle_fault t ex`** from `HBN t` (`t` possibly unbound, no `Simple`). -/
theorem rd_hfN (t : ObjRef) (ex : Fault) (s : State Unit) (h : HBN t s) :
    ∀ z ∈ (handleFault (Z := Unit) t ex s).1, Rdy z.2 := by
  intro z hz
  unfold handleFault at hz
  obtain ⟨w0, hw0, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hw0
  obtain ⟨⟨cap, s1⟩, hw1, hz⟩ := hz
  obtain ⟨e1, -⟩ := SInvU.getCap_capAt hw1
  simp only at e1; subst e1
  obtain ⟨w2, hw2, hz⟩ := hz
  obtain ⟨xt, hxt, rfl⟩ := q1_mem_threadGet hw2
  obtain ⟨⟨b, s3⟩, hw3, hz⟩ := hz
  have hcd : decide (xt.tcbSchedContext ≠ none) = true → RdyT s1 t := by
    intro hd
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (of_decide_eq_true hd)
    exact h.2.1 xt c hxt hc
  have r3 : Rdy s3 := rd_sendFaultIpcN t cap ex _ s1 h hcd _ hw3
  obtain ⟨w4, hw4, hz⟩ := hz
  obtain rfl := Set.mem_singleton_iff.1 hz
  unfold NonDet.unless at hw4
  split_ifs at hw4
  · rw [Set.mem_singleton_iff.1 hw4]; exact r3
  · unfold handleNoFault at hw4
    exact rd_setThreadState t .inactive trivial s3 r3 w4 hw4

end H

end

end Fl4Proofs.P3.SInvR.B8m
