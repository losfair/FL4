/-
P3 (DESIGN.md §9), invariant line G1 (rd12a, KENTRY-PLAN rd11a handoff 1-2):
**`complete_signal` and `receive_ipc`'s sender arm** under rd11a's pinned
body frame `KP` (spec side only).

* `B0 σ0` (σ0's ct a TCB bound to cur_sc: BS's `ct` / `cs`);
  **`nores_of_unbound`**: under `KP σ0 s`, ct an unbound TCB at `s` rules out
  resume (RS would give σ0's binding); `kp_nores`.
* `kp_ruc` / **`kp_ifCondA`** (the assert-form sporadic unblock check: it
  runs only on `scp ≠ cur_sc`, and rewrites one SC, never ct's TCB);
  **`kp_replyPush`** (callee = ct: no donation under resume; otherwise
  rd11b's CP), **`kp_recvSender`** (KP across the whole sender arm).
* `CX t s` (t a TCB unbound or bound to cur_sc) and its frames;
  **`cx_replyPush`**, **`ce_recvSender`** (rd8d's `rd_recvSender` walk: the
  receiver keeps `CX`, or reply_push donated the sender's SC and the
  receiver is `RT`).
* **`ke_completeSignal`** (rd11a handoff 1): A2's active arm plus the
  sporadic test, whose inner `scp ≠ cur_sc` test fails.
-/
import Fl4Proofs.P3.SpecInvRd11A2
import Fl4Proofs.P3.SpecInvRd11bA
import Fl4Proofs.P3.SpecInvRd8eB
open Classical

namespace Fl4Proofs.P3.SInvR.A12a
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.A11

noncomputable section

set_option maxHeartbeats 1000000

/-! ## No resume once ct is unbound -/

/-- σ0's current thread is a TCB bound to cur_sc. -/
abbrev B0 (σ0 : State Unit) : Prop :=
  ∃ x, σ0.kheap σ0.curThread = some (.tcb x) ∧ x.tcbSchedContext = some σ0.curSc

theorem b0_of_bs {σ0 : State Unit} (h : A10.BS σ0) : B0 σ0 := by
  obtain ⟨xt, hct, -⟩ := h.ct
  exact ⟨xt, hct, h.cs xt hct⟩

theorem nores_of_unbound {σ0 s : State Unit} (h0 : B0 σ0) (hK : KP σ0 s) {x : Tcb}
    (hx : s.kheap σ0.curThread = some (.tcb x)) (hn : x.tcbSchedContext = none) :
    s.schedulerAction ≠ .resumeCurThread := by
  intro hr
  obtain ⟨x0, hx0, hb0⟩ := h0
  have e := (hK.2.2 hr).1
  rw [hx, hx0] at e
  simp only [SVK.sv, hn, hb0, Prod.mk.injEq] at e
  exact absurd e.2.1 (by simp)

theorem kp_nores {σ0 s s' : State Unit} (h : KP σ0 s) (hr : s.schedulerAction ≠ .resumeCurThread)
    (hc : cfS s' = cfS s) (hw : A8.CW s.curSc s s') : KP σ0 s' :=
  kp_step h hc hw fun e => absurd (hw.2 e) hr

/-! ## The assert-form unblock check -/

theorem kp_ruc {σ0 s : State Unit} (h0 : B0 σ0) (hK : KP σ0 s) {p : ObjRef} (hp : p ≠ σ0.curSc)
    {y0 : SchedContext} {n : Nat} (hk : s.kheap p = some (.schedContext y0 n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p s).1) : KP σ0 r.2 := by
  have hc : cfS r.2 = cfS s := cfk_refillUnblockCheck' p s r hr
  have hw : A8.CW s.curSc s r.2 :=
    (A8.cp_refillUnblockCheck_ne p (c := s.curSc) (by rw [kp_curSc hK]; exact hp) s s
      ⟨rfl, A8.CW.refl _ _⟩ r hr).2
  refine kp_step hK hc hw fun hres => ?_
  have hres0 := hw.2 hres
  rcases ruc_out hk (ruc_ne hk hr) hr with e | ⟨-, z, e, -⟩
  · rw [e]; exact ⟨rfl, rfl⟩
  · have hkq : ∀ q, q ≠ p → r.2.kheap q = s.kheap q := fun q hq => by
      rw [e]; simp [Notif.updK, hq]
    have hct : σ0.curThread ≠ p := by
      intro ep
      obtain ⟨x0, hx0, -⟩ := h0
      have e1 := (hK.2.2 hres0).1
      rw [ep, hk, ← ep, hx0] at e1
      simp [SVK.sv] at e1
    exact ⟨by rw [hkq _ hct], by rw [hkq _ (Ne.symm hp)]⟩

/-- **`if_sporadic_cur_sc_assert_refill_unblock_check`** keeps `KP`. -/
theorem kp_ifCondA (o : Option ObjRef) {σ0 : State Unit} (h0 : B0 σ0) :
    IK (KP σ0) (ifCondRefillUnblockCheck (Z := Unit) o (some false) (some true)) := by
  intro s hs y hy
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hy
  cases o with
  | none =>
    obtain rfl : y = ((), s) := hy
    exact hs
  | some p =>
    dsimp only at hy
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hy
    subst w2
    rw [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hy
    unfold NonDet.when at hy
    split_ifs at hy with h1 h2
    · have h2' : p ≠ s.curSc := by first | exact h2 rfl | exact h2
      exact kp_ruc h0 hs (fun e => h2' (e.trans (kp_curSc hs).symm)) hk hy
    all_goals (obtain rfl : y = ((), _) := hy; exact hs)

/-! ## `reply_push` to the current thread -/

/-- **`reply_push caller ct`**: under resume ct is bound (no donation, two SVS
writes); otherwise rd11b's CP with no resume to keep. -/
theorem kp_replyPush {σ0 : State Unit} (h0 : B0 σ0) (a r : ObjRef) (d : Bool) (s : State Unit)
    (hK : KP σ0 s) {y : Unit × State Unit} (hy : y ∈ (replyPush (Z := Unit) a σ0.curThread r d s).1) :
    KP σ0 y.2 := by
  have hc := cfk_replyPush' a σ0.curThread r d s y hy
  by_cases hr : s.schedulerAction = .resumeCurThread
  · unfold replyPush at hy
    obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨xc, hxc, rfl⟩ := SInvQ.q1_mem_threadGet hz1
    obtain ⟨z2, hz2, hy⟩ := hy
    obtain ⟨xe, hxe, rfl⟩ := SInvQ.q1_mem_threadGet hz2
    dsimp only at hy
    obtain ⟨z3, hz3, hy⟩ := hy
    have v3 : SVK.SVS s z3.2 := B8d.sv_setReplyObjRef' _ _ _ s z3 hz3
    obtain ⟨z4, hz4, hy⟩ := hy
    have v4 : SVK.SVS s z4.2 := v3.trans (SVK.sv_setThreadState' a _ z3.2 z4 hz4)
    unfold NonDet.when at hy
    rw [if_neg (fun hg => nores_of_unbound h0 hK hxe hg.2.1 hr)] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact kp_step hK hc (A8.cw_of_svs v4) fun _ => ⟨v4.1 _, v4.1 _⟩
  · exact kp_nores hK hr hc (cw_of_cp (A11b.cp_replyPush a σ0.curThread r d) hy)

/-- **`KP` across `receive_ipc`'s sender arm** (receiver = ct). -/
theorem kp_recvSender {σ0 : State Unit} (h0 : B0 σ0) (sender epptr : ObjRef) (reply : Option ObjRef)
    (data : SenderPayload) (s : State Unit) (hK : KP σ0 s) (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) sender (some epptr) data.senderBadge data.senderCanGrant σ0.curThread
      let scPtr ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scPtr
      let fault ← threadGet (Z := Unit) Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush (Z := Unit) sender σ0.curThread (the reply) donate
        else setThreadState (Z := Unit) sender .inactive
      else do
        setThreadState (Z := Unit) sender .running
        possibleSwitchTo (Z := Unit) sender) s).1) : KP σ0 y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have k3 : KP σ0 z3.2 := ik_kp (SVK.sv_doIpcTransfer' _ _ _ _ _) (cfk_doIpcTransfer' _ _ _ _ _) σ0 s hK z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain ⟨x4, -, rfl⟩ := SInvQ.q1_mem_threadGet h4
  obtain ⟨z5, h5, hy⟩ := hy
  have k5 : KP σ0 z5.2 := kp_ifCondA _ h0 z3.2 k3 z5 h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, -, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      exact kp_replyPush h0 _ _ _ z5.2 k5 hy
    · exact ik_kp (SVK.sv_setThreadState' _ _) (cfk_setThreadState' _ _) σ0 z5.2 k5 y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    have k7 : KP σ0 z7.2 := ik_kp (SVK.sv_setThreadState' _ _) (cfk_setThreadState' _ _) σ0 z5.2 k5 z7 h7
    exact kp_possibleSwitchTo _ σ0 z7.2 k7 y hy

/-! ## The receiver's binding -/

/-- `t` a TCB, unbound or bound to cur_sc. -/
abbrev CX (t : ObjRef) (s : State Unit) : Prop :=
  ∃ x, s.kheap t = some (.tcb x) ∧ (x.tcbSchedContext = none ∨ x.tcbSchedContext = some s.curSc)

theorem cx_svcf {t : ObjRef} {s s' : State Unit} (h : CX t s) (hS : SVK.SVS s s') (hc : cfS s' = cfS s) :
    CX t s' := by
  obtain ⟨x, hx, hb⟩ := h
  have e := hS.1 t
  rw [hx] at e
  obtain ⟨x', hx', hb'⟩ := SVK.sv_tcb (o := s'.kheap t) e
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  exact ⟨x', hx', by rw [hb', ec]; exact hb⟩

theorem cx_tcb {t : ObjRef} {s s' : State Unit} (h : CX t s)
    (hk : ∀ q x, s.kheap q = some (.tcb x) → s'.kheap q = some (.tcb x)) (hc : cfS s' = cfS s) : CX t s' := by
  obtain ⟨x, hx, hb⟩ := h
  have ec : s'.curSc = s.curSc := congrArg (fun p => p.2.1) hc
  exact ⟨x, hk t x hx, by rw [ec]; exact hb⟩

/-- **`reply_push caller callee`** from `CX callee`: kept (a bound callee gets
nothing), or the unbound callee got the caller's released SC (`RT`). -/
theorem cx_replyPush (caller callee rp : ObjRef) (cd : Bool) (s : State Unit) (hR : Rdy s)
    (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s) (hF : SInvB.ScFwd s) (hc : cd = true → B8d.RT s caller)
    (hC : CX callee s) {y : Unit × State Unit} (hy : y ∈ (replyPush (Z := Unit) caller callee rp cd s).1) :
    CX callee y.2 ∨ B8d.RT y.2 callee := by
  obtain ⟨x, hx, hb | hb⟩ := hC
  · right
    refine (B8d.rd_replyPush_d caller callee rp cd s hR h1 hA hF hc hy).2 fun x' c hx' hc' => ?_
    rw [hx] at hx'; cases hx'; rw [hb] at hc'; cases hc'
  · left
    have hcf := cfk_replyPush' caller callee rp cd s y hy
    unfold replyPush at hy
    obtain ⟨z1, hz1, hy⟩ := hy
    obtain ⟨xc, hxc, rfl⟩ := SInvQ.q1_mem_threadGet hz1
    obtain ⟨z2, hz2, hy⟩ := hy
    obtain ⟨xe, hxe, rfl⟩ := SInvQ.q1_mem_threadGet hz2
    dsimp only at hy
    obtain ⟨z3, hz3, hy⟩ := hy
    have v3 : SVK.SVS s z3.2 := B8d.sv_setReplyObjRef' _ _ _ s z3 hz3
    obtain ⟨z4, hz4, hy⟩ := hy
    have v4 : SVK.SVS s z4.2 := v3.trans (SVK.sv_setThreadState' caller _ z3.2 z4 hz4)
    rw [hx] at hxe; cases hxe
    unfold NonDet.when at hy
    rw [if_neg (fun hg => by rw [hb] at hg; exact absurd hg.2.1 (by simp))] at hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact cx_svcf ⟨x, hx, Or.inr hb⟩ v4 hcf

/-- **`receive_ipc`'s sender arm** (rd8d's `rd_recvSender` walk) from the
dequeue state: the receiver keeps `CX`, or ends `RT`. -/
theorem ce_recvSender (sender thread epptr e : ObjRef) (reply : Option ObjRef) (data : SenderPayload)
    (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s) (hF : SInvB.ScFwd s)
    {x : Tcb} (hx : s.kheap sender = some (.tcb x)) (hxs : x.tcbState = .blockedOnSend e data)
    (hC : CX thread s) (y : Unit × State Unit)
    (hy : y ∈ ((do
      doIpcTransfer (Z := Unit) sender (some epptr) data.senderBadge data.senderCanGrant thread
      let scPtr ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) scPtr
      let fault ← threadGet (Z := Unit) Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush (Z := Unit) sender thread (the reply) donate
        else setThreadState (Z := Unit) sender .inactive
      else do
        setThreadState (Z := Unit) sender .running
        possibleSwitchTo (Z := Unit) sender) s).1) : CX thread y.2 ∨ B8d.RT y.2 thread := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer sender (some epptr) _ _ thread s hs z3 h3
  have q3 : SInvQ.T1 z3.2 := SInvQ.q1_doIpcTransfer sender (some epptr) _ _ thread s h1 z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' sender (some epptr) _ _ thread s z3 h3
  have t3 : B8d.TV (B8d.TVv s) z3.2 := B8d.tv_doIpcTransfer sender (some epptr) _ _ thread s rfl z3 h3
  have C3 : CX thread z3.2 := cx_svcf hC v3 (cfk_doIpcTransfer' _ _ _ _ _ s z3 h3)
  have hx3 : ∃ x3, z3.2.kheap sender = some (.tcb x3) ∧ x3.tcbState = .blockedOnSend e data := by
    have ev := congrFun t3 sender
    unfold B8d.TVv at ev
    rw [hx] at ev
    cases hk : z3.2.kheap sender with
    | none => rw [hk] at ev; simp [B8c.tcbV] at ev
    | some o =>
      rw [hk] at ev
      cases o with
      | tcb x3 =>
        simp only [B8c.tcbV, Option.some.injEq, Prod.mk.injEq] at ev
        exact ⟨x3, rfl, ev.1.trans hxs⟩
      | _ => simp [B8c.tcbV] at ev
  obtain ⟨x3, hx3, hxs3⟩ := hx3
  obtain ⟨z4, h4, hy⟩ := hy
  obtain ⟨x4, -, rfl⟩ := SInvQ.q1_mem_threadGet h4
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨e5, -, -⟩ := rd_ifCond x4.tcbSchedContext (some false) (some true) z3.2 e3 h5
  have f5 := B8d.sf_ifCond x4.tcbSchedContext (some false) (some true) z3.2 h5
  have q5 : SInvQ.T1 z5.2 := SInvQ.q1_ifCondRefillUnblockCheck _ _ _ z3.2 q3 z5 h5
  have hA5 := f5.1 (B8d.simple_svs hA v3)
  have hF5 := f5.2.1 (fwd_svs hF v3)
  have hx5 := f5.2.2 sender x3 hx3
  have C5 : CX thread z5.2 := cx_tcb C3 f5.2.2 (cfk_ifCondRefillUnblockCheck' _ _ _ z3.2 z5 h5)
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
  rw [hx5] at hx6
  cases hx6
  dsimp only at hy
  have hRT : (∀ b, x3.tcbFault ≠ some (.timeout b)) → B8d.RT z5.2 sender := fun hnt x' c hx' hc => by
    rw [hx5] at hx'; cases hx'
    exact e5.2.2.1 sender x3 c hx5 (Or.inr (Or.inl ⟨e, data, hxs3, hnt⟩)) hc
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      refine cx_replyPush sender thread _ _ z5.2 e5 q5 hA5 hF5 (fun hd => hRT fun b hb => ?_) C5 hy
      have hd' := of_decide_eq_true hd
      apply hd'.2
      rw [hb]; rfl
    · left
      exact cx_svcf C5 (SVK.sv_setThreadState' sender .inactive z5.2 y hy)
        (cfk_setThreadState' sender .inactive z5.2 y hy)
  · left
    obtain ⟨z7, h7, hy⟩ := hy
    have C7 := cx_svcf C5 (SVK.sv_setThreadState' sender .running z5.2 z7 h7)
      (cfk_setThreadState' sender .running z5.2 z7 h7)
    have ek := (ktc_possibleSwitchTo z7.2.kheap z7.2.curTime z7.2.releaseQueue z7.2.curThread sender z7.2
      ⟨rfl, rfl, rfl, rfl⟩ y hy).1
    exact cx_tcb C7 (fun q x' hq => by rw [ek]; exact hq) (cfk_possibleSwitchTo' sender z7.2 y hy)

/-! ## `complete_signal` -/

/-- **`complete_signal` of the current thread bound to cur_sc** (rd11a handoff 1). -/
theorem ke_completeSignal (σ0 : State Unit) (ntfnptr : ObjRef) (s : State Unit) (hK : KP σ0 s)
    (hb : ∀ x, s.kheap s.curThread = some (.tcb x) → x.tcbSchedContext = some s.curSc)
    {y : Unit × State Unit} (hy : y ∈ (completeSignal (Z := Unit) ntfnptr σ0.curThread s).1) : KE σ0 y.2 := by
  have ect := kp_curThread hK
  unfold completeSignal at hy
  obtain ⟨⟨nt, s1⟩, h1, hy⟩ := hy
  have e1 : s1 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  dsimp only at hy
  cases hob : nt.ntfnObj with
  | activeNtfn bdg =>
    simp only [hob] at hy
    obtain ⟨z3, h3, hy⟩ := hy
    obtain ⟨z4, h4, hy⟩ := hy
    obtain ⟨z5, h5, hy⟩ := hy
    have v3 := SVK.sv_asUser' _ _ s z3 h3
    have c3 : cfS z3.2 = cfS s := cfk_asUser' _ _ s z3 h3
    have v4 : SVK.SVS z3.2 z4.2 := by refine (?_ : SVK.SVM _) z3.2 z4 h4; sv_auto
    have c4 : cfS z4.2 = cfS z3.2 := by refine (?_ : CFK _) z3.2 z4 h4; cfk_auto
    have v34 := v3.trans v4
    have c34 := c4.trans c3
    have hb4 := (A8.keep_svcf v34 c34).2.2 hb
    have et4 : z4.2.curThread = σ0.curThread := (congrArg (fun p => p.2.2.1) c34).trans ect
    rw [← et4] at h5
    have e5 : z5.2 = z4.2 := md_ro (fun x hx => by rw [hb4 x hx]; simp) h5
    rw [e5] at hy
    obtain ⟨z6, h6, hy⟩ := hy
    obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
    rw [← et4] at hx6
    rw [hb4 x6 hx6] at hy
    have hend : KE σ0 z4.2 := ke_svs hK hb v34 c34
    simp only [NonDet.maybeM] at hy
    obtain ⟨⟨sc, s7⟩, h7, hy⟩ := hy
    obtain ⟨-, e7⟩ := SInvI.mem_getSchedContext_vi h7
    simp only at e7
    subst e7
    beta_reduce at hy
    unfold NonDet.when at hy
    split at hy
    · obtain ⟨⟨np, s8⟩, h8, hy⟩ := hy
      have e8 : s8 = z4.2 := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h8
      subst e8
      beta_reduce at hy
      rw [Notif.nd_gets_bind] at hy
      split at hy
      · rename_i hg
        exact absurd rfl hg.2
      · obtain rfl := Set.mem_singleton_iff.1 hy; exact hend
    · obtain rfl := Set.mem_singleton_iff.1 hy; exact hend
  | _ =>
    simp only [hob] at hy
    first | exact (hy : False).elim | (obtain ⟨_, h, -⟩ := hy; exact h.elim) | simp [NonDet.fail] at hy

end

end Fl4Proofs.P3.SInvR.A12a
