/-
P3 (DESIGN.md §9), invariant line G1 (rd8d): **`send_ipc` with donation**
(spec side only, outside the JAtZ cone; KENTRY-PLAN rd8c handoff 1).

rd6's `rd_sendIpc_nd` covers `canDonate = false` from a sender holding a
timeout fault. Here any `canDonate`, from a sender that is `RdyT` (at a
perform the sender is ct, `Restart`, so rd8b's `CtRdy` gives it). The donation
arms (`sched_context_donate` of the sender's SC in the non-call branch,
`reply_push`'s in the call / fault branch) run rd8c's
`rd_schedContextDonate_rel` at a state reached from the dequeue state by
`do_ipc_transfer` / `reply_unlink_tcb` / `reply_push`'s head, all `SVS` steps
with `T1` frames, so `T1`, `Simple`, `ScFwd` and "the sender's SC is
released" travel along.

* `RT s t`: `t` is `RdyT` if bound; `rT_svs`, `rT_of_rdyT`, `simple_svs`,
  `rel_of_rdyT`.
* `rd_sendTail`: `set_thread_state dest Running ; the unblock check ;
  possible_switch_to dest` keeps `Rdy` from `RT dest`.
* **`rd_schedContextDonate_relT`**: rd8c's donation lemma with `RdyT t`
  afterwards.
* **`rd_replyPush_d`**: `reply_push` with any `canDonate`.
* `rd_sendArm_d`, **`rd_sendIpc_d`**.
-/
import Fl4Proofs.P3.SpecInvRd8cE
open Classical

namespace Fl4Proofs.P3.SInvR.B8d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c

noncomputable section

set_option maxHeartbeats 1000000

/-- `t` is `RdyT` if it is a TCB bound to an SC. -/
def RT (s : State Unit) (t : ObjRef) : Prop :=
  ∀ x c, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c → RdyT s t

theorem rT_of_rdyT {s : State Unit} {t : ObjRef} (h : RdyT s t) : RT s t := fun _ _ _ _ => h

theorem rT_svs {s s' : State Unit} {t : ObjRef} (h : RT s t) (hS : SVK.SVS s s') : RT s' t := by
  intro x' c hx' hc
  have e := hS.1 t
  rw [hx'] at e
  obtain ⟨y, hy, hyc⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  exact rdyT_svs (h y c hy (hyc.trans hc)) hS

theorem simple_svs {s s' : State Unit} (h : SInvQ.Simple s) (hS : SVK.SVS s s') : SInvQ.Simple s' := by
  intro t e
  rcases hS.2.2 with e' | e' <;> rw [e'] at e
  · exact h t e
  · cases e

theorem rel_of_rdyT {s : State Unit} {t c : ObjRef} {x : Tcb} (h : RdyT s t) (hx : s.kheap t = some (.tcb x))
    (hc : x.tcbSchedContext = some c) :
    ∀ y n, s.kheap c = some (.schedContext y n) → scActive y = true ∧ refillReady s.curTime (refillHd y) = true := by
  obtain ⟨x', c', y', n', hx', hc', hy', ha, hr⟩ := h
  rw [hx] at hx'
  cases hx'
  rw [hc] at hc'
  cases hc'
  intro y n hy
  rw [hy'] at hy
  cases hy
  exact ⟨ha, hr⟩

/-- The common tail of the transfer to a receiver. -/
theorem rd_sendTail (dest : ObjRef) (s7 : State Unit) (e7 : Rdy s7) (hT : RT s7 dest) (y' : Unit × State Unit)
    (hy' : y' ∈ ((do
        setThreadState (Z := Unit) dest .running
        let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
        ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
        possibleSwitchTo (Z := Unit) dest) s7).1) : Rdy y'.2 := by
  obtain ⟨z8, h8, hy'⟩ := hy'
  have e8 : Rdy z8.2 := rd_setThreadState dest .running trivial s7 e7 z8 h8
  have v8 : SVK.SVS s7 z8.2 := SVK.sv_setThreadState' dest .running s7 z8 h8
  obtain ⟨z9, h9, hy'⟩ := hy'
  obtain ⟨x9, -, rfl⟩ := SInvQ.q1_mem_threadGet h9
  obtain ⟨z10, h10, hy'⟩ := hy'
  obtain ⟨e10, r10, k10⟩ := rd_ifCond x9.tcbSchedContext (some false) (some false) z8.2 e8 h10
  refine rd_possibleSwitchTo_q dest z10.2 (fun x' c hx' hc => ?_) e10 y' hy'
  exact r10 dest (rT_svs hT v8 x' c (k10 dest x' hx') hc)

/-- **`sched_context_donate p t`** of a released SC to an unbound thread (rd8c's
`rd_schedContextDonate_rel`), with `t` `RdyT` afterwards. -/
theorem rd_schedContextDonate_relT (p t : ObjRef) (σ : State Unit) (hR : Rdy σ) (h1 : SInvQ.T1 σ)
    (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (hn : x.tcbSchedContext = none)
    (hrel : ∀ y n, σ.kheap p = some (.schedContext y n) →
      scActive y = true ∧ refillReady σ.curTime (refillHd y) = true)
    {r : Unit × State Unit} (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) :
    Rdy r.2 ∧ RdyT r.2 t := by
  refine ⟨(rd_schedContextDonate_rel p t σ hR h1 hA hF hx hn hrel hr).1, ?_⟩
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

theorem rd_setReplyObjRef' (u : (Option ObjRef → Option ObjRef) → Reply → Reply) (r : ObjRef) (v : Option ObjRef) :
    RdK (setReplyObjRef (Z := Unit) u r v) := rd_updateSkObjRef KernelObject.reply u r v

theorem sv_setReplyObjRef' (u : (Option ObjRef → Option ObjRef) → Reply → Reply) (r : ObjRef) (v : Option ObjRef) :
    SVK.SVM (setReplyObjRef (Z := Unit) u r v) := SVK.sv_updateSkObjRef' KernelObject.reply u r v (fun _ => SVK.so_reply _)

theorem q1_setReplyObjRef' (u : (Option ObjRef → Option ObjRef) → Reply → Reply) (r : ObjRef) (v : Option ObjRef) :
    SInvQ.Q1K (setReplyObjRef (Z := Unit) u r v) := SInvQ.q1_updateSkObjRef KernelObject.reply u r v

/-- **`reply_push caller callee r cd`** (any `cd`): `Rdy` kept and the callee
`RdyT` if bound afterwards. The donation (guard: the caller bound, the callee
not) gives the caller's SC, released by `RT caller`, to the callee. -/
theorem rd_replyPush_d (caller callee rp : ObjRef) (cd : Bool) (s : State Unit) (hR : Rdy s)
    (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s) (hF : SInvB.ScFwd s) (hc : cd = true → RT s caller)
    {y : Unit × State Unit} (hy : y ∈ (replyPush (Z := Unit) caller callee rp cd s).1) :
    Rdy y.2 ∧ (RT s callee → RT y.2 callee) := by
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
    obtain ⟨r1, r2⟩ := rd_schedContextDonate_relT c callee z5.2 e5 q5 (simple_svs hA v5) (fwd_svs hF v5)
      hk5 (hb5.trans hg.2.1) (rel_of_rdyT (rdyT_svs (hc hg.2.2 xc c hxc hcc) v5) hkc5 (hbc5.trans hcc)) hy
    exact ⟨r1, fun _ => rT_of_rdyT r2⟩
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨e4, fun hT => rT_svs hT v4⟩

/-- **The transfer to a waiting receiver**, any `canDonate`, from the dequeue
state `s`: the sender `RdyT`, the receiver `RT`, `T1`, `Simple`, `ScFwd`. -/
theorem rd_sendArm_d (call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr dest : ObjRef)
    (reply : Option ObjRef) (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s)
    (hF : SInvB.ScFwd s) (hct : RdyT s thread) (hRT : RT s dest) (y : Unit × State Unit)
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
  have hA4 := simple_svs hA v4
  have hF4 := fwd_svs hF v4
  have hc4 := rdyT_svs hct v4
  have hT4 := rT_svs hRT v4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨e7, t7⟩ := rd_replyPush_d thread dest _ cd z4.2 e4 q4 hA4 hF4 (fun _ => rT_of_rdyT hc4) h7
      exact rd_sendTail dest z7.2 e7 (t7 hT4) y hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact rd_sendTail dest z7.2 (rd_setThreadState thread .inactive trivial z4.2 e4 z7 h7)
        (rT_svs hT4 (SVK.sv_setThreadState' thread .inactive z4.2 z7 h7)) y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    unfold NonDet.when at h7
    split at h7
    · rename_i hg
      obtain ⟨z8, h8, h7⟩ := h7
      obtain ⟨x8, hx8, rfl⟩ := SInvQ.q1_mem_threadGet h8
      obtain ⟨xt, c, yc, nc, hxt, hcc, -, -, -⟩ := id hc4
      rw [hxt] at hx8
      cases hx8
      dsimp only at h7
      rw [hcc] at h7
      obtain ⟨r1, r2⟩ := rd_schedContextDonate_relT c dest z4.2 e4 q4 hA4 hF4 hx5 hg.2
        (rel_of_rdyT hc4 hxt hcc) h7
      exact rd_sendTail dest z7.2 r1 (rT_of_rdyT r2) y hy
    · obtain rfl := Set.mem_singleton_iff.1 h7
      exact rd_sendTail dest z4.2 e4 hT4 y hy

/-- **`send_ipc`, any `canDonate`**, from a sender `RdyT` at the start (at a
perform: ct, `Restart`, rd8b's `CtRdy`) with ctq's `T1` / `Simple` and sb2's
`ScFwd`. -/
theorem rd_sendIpc_d (block call : Bool) (badge : Badge) (cg cgr cd : Bool) (thread epptr : ObjRef)
    (σ : State Unit) (hct : RdyT σ thread) (h1 : SInvQ.T1 σ) (hA : SInvQ.Simple σ) (hF : SInvB.ScFwd σ) :
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
      exact ikp_bind (rd_setThreadState_r thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
  | sendEP q =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · unfold sendIpcBlocked
      exact ikp_bind (rd_setThreadState_r thread _ σ hct) fun _ => rd_tcbEpAppend _ _ _
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
          exact rd_sendArm_d call badge cg cgr cd thread epptr dest r z1 e1 q1 (simple_svs hA v1)
            (fwd_svs hF v1) (rdyT_svs hct v1)
            (fun x' c hx' hc => by
              rw [hx] at hx'; cases hx'
              exact e1.2.2.1 dest x c hx (Or.inr (Or.inr ⟨e, r, d, hxs⟩)) hc) y hy
        | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)

end

end Fl4Proofs.P3.SInvR.B8d
