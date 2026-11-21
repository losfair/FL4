/-
P3 (DESIGN.md §9), invariant line G1 (rd8e): **`do_reply_transfer` keeps
`Rdy`** (spec side only, outside the JAtZ cone; KENTRY-PLAN rd8d handoff 2).

The tail `when (sc ≠ none ∧ runnable)` calls `possible_switch_to receiver`
after testing only `refill_ready ∧ refill_sufficient 0` of the head, or else
`postpone`s the SC: both need the receiver's SC ACTIVE. No carried `Rdy`
clause gives it (the receiver was `BlockedOnReply`, which `R3` does not
cover), and "an inactive SC has no refills" would not help: `refillHd [] =
the none = undefined` (Classical.choice), so the guard is undetermined on an
empty list. What gives it is l4v's `active_reply_scs` /
`active_if_bound_sc_tcb_at` for blocked threads, already stated in ScInv.lean
as **`Sched.BlockedScActive`** (an SC bound to an ipc-queued TCB — send,
receive, notification AND reply blocked — is active; an SC with a non-empty
reply stack is active). It is carried today only inside the J layer
(`JAtZ.bsa`); here it is an entry hypothesis at the state where
`do_reply_transfer` starts (a carried fact, not a premise: see the rd8e
section of KENTRY-PLAN for its spec-side carry, handed off).

From it: before `reply_remove` the receiver, if bound, is bound to an active
SC (`BlockedScActive.tcb` with sb2's `ScBackS`); `reply_remove` either leaves
that binding or donates the SC whose stack starts with the reply
(`BlockedScActive.replies`; `ab_schedContextDonate`). So afterwards
`ABo receiver` (bound ⇒ `ActB`), carried by SVK's `SVS` and the unblock
check to the tail, where the guard's readiness makes it `RdyT`
(`rd_replyTail`).

* `ABo`, `abo_svs`, `abo_ifCond`, `PA`, **`ab_schedContextDonate`**,
  `inact_replyUnlinkTcb`, **`abo_replyRemove`**, `nsw_replyRemove`,
  `rdy_setTwice`, **`rd_replyTail`**, **`rd_doReplyTransfer`**.
-/
import Fl4Proofs.P3.SpecInvRd8eB
import Fl4Proofs.P3.ScRemoveKeep
import Fl4Proofs.P3.SpecInvRd8A2
open Classical

namespace Fl4Proofs.P3.SInvR.B8e
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d

noncomputable section

set_option maxHeartbeats 1000000

/-- **`BlockedScActive` at boot** (non-vacuity of the entry hypothesis): the
idle thread is the only TCB (state `IdleThreadState`, not ipc-queued) and the
idle SC the only SC (empty reply stack). -/
theorem boot_bsa : Sched.BlockedScActive (initASt (Z := Unit)) := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · have hx' : initKheap t = some (.tcb x) := hx
    rw [init_tcbSt hx'] at hq
    cases hq
  · have hy' : initKheap p = some (.schedContext y n) := hp
    by_cases e : p = idleScPtr
    · subst e
      rw [SInvV.initKheap_idleSc] at hy'
      cases hy'
      exact absurd rfl hr
    · exfalso
      unfold initKheap at hy'
      simp only [Function.update_apply, e, if_false] at hy'
      split_ifs at hy' <;> cases hy'

/-- `t`, if bound, is bound to an active SC. -/
def ABo (t : ObjRef) (s : State Unit) : Prop :=
  ∀ x c, s.kheap t = some (.tcb x) → x.tcbSchedContext = some c → ActB s t

theorem abo_svs {s s' : State Unit} {t : ObjRef} (h : ABo t s) (hS : SVK.SVS s s') : ABo t s' := by
  intro x' c hx' hc
  have e := hS.1 t
  rw [hx'] at e
  obtain ⟨x, hx, hxc⟩ := SVK.sv_tcb (o := s.kheap t) e.symm
  exact A8.actB_svs (h x c hx (hxc.trans hc)) hS

theorem abo_ifCond (o : Option ObjRef) (a b : Option Bool) (t : ObjRef) (s : State Unit) (hR : Rdy s)
    (h : ABo t s) {r : Unit × State Unit} (hr : r ∈ (ifCondRefillUnblockCheck (Z := Unit) o a b s).1) :
    ABo t r.2 := by
  intro x' c hx' hc
  obtain ⟨-, -, k⟩ := rd_ifCond o a b s hR hr
  exact A8.ab_ifCond o a b t s (h x' c (k t x' hx') hc) r hr

/-- The SC at `p` is an active SC. -/
def PA (p : ObjRef) (s : State Unit) : Prop := ∃ y n, s.kheap p = some (.schedContext y n) ∧ scActive y = true

/-- **`sched_context_donate p t`** of an active SC: `t` is bound to an active SC afterwards. -/
theorem ab_schedContextDonate (p t : ObjRef) (σ : State Unit) (hp : PA p σ) {r : Unit × State Unit}
    (hr : r ∈ (schedContextDonate (Z := Unit) p t σ).1) : ActB r.2 t := by
  unfold schedContextDonate at hr
  obtain ⟨⟨fo, s1⟩, h1, hr⟩ := hr
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h1
  subst s1
  obtain ⟨z2, h2, hr⟩ := hr
  have p2 : PA p z2.2 := by
    unfold NonDet.when at h2
    split at h2
    · obtain ⟨⟨ft, s3⟩, h3, h2⟩ := h2
      have e3 : s3 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h3
      subst s3
      obtain ⟨z4, h4, h2⟩ := h2
      obtain ⟨x4, -, e4⟩ := SInvQ.q1_tsa_out h4
      obtain ⟨z5, h5, h2⟩ := h2
      have k5 := (kt_tcbReleaseRemove _ _ ft z4.2 ⟨rfl, rfl⟩ z5 h5).1
      obtain ⟨z6, h6, h2⟩ := h2
      obtain ⟨x6, hx6, e6⟩ := SInv.mem_threadSet h6
      have k7 := (kt_testReschedule _ _ ft z6.2 ⟨rfl, rfl⟩ z2 h2).1
      obtain ⟨y0, n0, hk0, ha0⟩ := hp
      have hk5 : z5.2.kheap = σ.kheap := by rw [k5, e4]
      have hfp : ft ≠ p := fun h => by rw [h, hk5, hk0] at hx6; cases hx6
      refine ⟨y0, n0, ?_, ha0⟩
      rw [k7, e6]
      simp only [Function.update_of_ne (Ne.symm hfp)]
      rw [hk5]; exact hk0
    · obtain rfl := Set.mem_singleton_iff.1 h2
      exact hp
  obtain ⟨z7, h7, hr⟩ := hr
  obtain ⟨y7, n7, hk7, e7⟩ := SInvB.mem_updateSchedContext h7
  obtain ⟨x8, hx8, e8⟩ := SInv.mem_threadSet hr
  obtain ⟨y2, n2, hk2, ha2⟩ := p2
  rw [hk2] at hk7; cases hk7
  have htp : t ≠ p := fun h => by rw [h, e7] at hx8; simp at hx8
  rw [e8]
  refine ⟨tcbSchedContextUpdate (fun _ => some p) x8, p, scTcbUpdate (fun _ => some t) y7, n7, by simp, rfl, ?_, ha2⟩
  simp only [Function.update_of_ne (Ne.symm htp)]
  rw [e7]; simp

/-- `reply_unlink_tcb t r` leaves `t` an `Inactive` TCB. -/
theorem inact_replyUnlinkTcb {t r : ObjRef} {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (replyUnlinkTcb (Z := Unit) t r σ).1) :
    ∃ x', y.2.kheap t = some (.tcb x') ∧ x'.tcbState = .inactive := by
  unfold replyUnlinkTcb at hy
  obtain ⟨⟨a1, s1⟩, h1, hy⟩ := hy
  obtain ⟨⟨a2, s2⟩, h2, hy⟩ := hy
  obtain ⟨⟨a3, s3⟩, h3, hy⟩ := hy
  obtain ⟨⟨a4, s4⟩, h4, hy⟩ := hy
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, e6⟩ := SInv.mem_threadSet h6
  have k := SInv.kh_setThreadStateAct t z6.2.kheap z6.2 rfl y hy
  exact ⟨{ x6 with tcbState := .inactive }, by rw [k, e6]; simp, rfl⟩

theorem not_blkR_reply (r : ObjRef) (f : Option Fault) : ¬ BlkR (.blockedOnReply r) f := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩) <;> cases h

/-- **`reply_remove caller r`** of a `BlockedOnReply` caller, from
`BlockedScActive` and `ScBackS`: the caller is `Inactive` afterwards and, if
bound, bound to an active SC. -/
theorem abo_replyRemove (caller r : ObjRef) (σ : State Unit) (hB : Sched.BlockedScActive σ)
    (hBk : SInvB.ScBackS σ) {x : Tcb} (hx : σ.kheap caller = some (.tcb x))
    (hst : ipcQueuedThreadState x.tcbState = true) {y : Unit × State Unit}
    (hy : y ∈ (replyRemove (Z := Unit) caller r σ).1) :
    ABo caller y.2 ∧ ∃ x', y.2.kheap caller = some (.tcb x') ∧ x'.tcbState = .inactive := by
  have hab0 : ABo caller σ := fun x' c hx' hc => by
    rw [hx] at hx'; cases hx'
    obtain ⟨yc, k, hk, hyt, -⟩ := hBk caller x c hx hc
    exact ⟨x, c, yc, k, hx, hc, hk, hB.tcb c yc k caller x hk hyt hx hst⟩
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
    | exact ⟨abo_svs hab0 (SVK.sv_replyUnlinkTcb caller r σ y hy), inact_replyUnlinkTcb hy⟩
    | (obtain ⟨z, hz, hy⟩ := hy
       obtain rfl := Set.mem_singleton_iff.1 hz
       exact ⟨abo_svs hab0 (SVK.sv_replyUnlinkTcb caller r _ y hy), inact_replyUnlinkTcb hy⟩)
  · simp only [hw] at hy
    obtain ⟨⟨a4, s4⟩, hz4, hy⟩ := hy
    have e4 : s4 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz4
    subst s4
    obtain ⟨z5, hz5, hy⟩ := hy
    obtain ⟨x5, hx5, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    have v6 : SVK.SVS σ z6.2 := SVK.sv_replyUnlinkSc' scPtr r σ z6 hz6
    obtain ⟨z7, hz7, hy⟩ := hy
    have ab7 : ABo caller z7.2 := by
      unfold NonDet.when at hz7
      split at hz7
      · obtain ⟨ys, ns, hks, hrm⟩ := Sched.scWithReply_mem' hw
        have ha := hB.replies scPtr ys ns hks (List.ne_nil_of_mem hrm)
        have e := v6.1 scPtr
        rw [hks] at e
        obtain ⟨y', hy', -, hm', -⟩ := SVK.sv_sc (o := z6.2.kheap scPtr) e
        have hpa : PA scPtr z6.2 := ⟨y', ns, hy', by show activeSc _ = true; rw [hm']; exact ha⟩
        exact fun _ _ _ _ => ab_schedContextDonate scPtr caller z6.2 hpa hz7
      · obtain rfl := Set.mem_singleton_iff.1 hz7
        exact abo_svs hab0 v6
    exact ⟨abo_svs ab7 (SVK.sv_replyUnlinkTcb caller r z7.2 y hy), inact_replyUnlinkTcb hy⟩

theorem nsw_replyRemove (t c r : ObjRef) : IK (SInvQ.P12.NSw t) (replyRemove (Z := Unit) c r) := by
  unfold replyRemove; p12_nsw_auto

/-- Two writes of one TCB keeping its SC, the second to a non-`BlkR` TCB. -/
theorem rdy_setTwice {σ : State Unit} (hR : Rdy σ) {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x))
    (x1 y : Tcb) (hy : y.tcbSchedContext = x.tcbSchedContext) (hb : ¬ BlkR y.tcbState y.tcbFault) :
    Rdy { σ with kheap := Function.update (Function.update σ.kheap t (some (.tcb x1))) t (some (.tcb y)) } := by
  rw [Function.update_idem]
  refine rdy_upd hR t _ ⟨fun x0 h => ?_, fun x' h hb' _ => ?_, by rw [hx]; rfl⟩
  · rw [hx] at h; cases h; exact ⟨y, rfl, hy⟩
  · cases h; exact absurd hb' hb

/-- **`do_reply_transfer`'s tail** from `Rdy`, `ScFwd` and `ABo receiver`. -/
theorem rd_replyTail (receiver : ObjRef) (fault : Option Fault) (s : State Unit) (hR : Rdy s)
    (hF : SInvB.ScFwd s) (hab : ABo receiver s) {y : Unit × State Unit}
    (hy : y ∈ ((do
        let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext receiver
        let state ← getThreadState (Z := Unit) receiver
        NonDet.when (scOpt ≠ none ∧ runnable state) <| do
          let scPtr ← NonDet.assertOpt scOpt
          let sc ← getSchedContext (Z := Unit) scPtr
          let curtime ← NonDet.gets fun s : State Unit => s.curTime
          if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
          then possibleSwitchTo (Z := Unit) receiver
          else do
            let tcb ← NonDet.getsThe (getTcb (Z := Unit) receiver)
            if isEpCap tcb.tcbTimeoutHandler ∧
               ¬(fault.elim false isTimeoutFault = true)
            then handleTimeout (Z := Unit) receiver (.timeout sc.scBadge)
            else postpone (Z := Unit) scPtr) s).1) : Rdy y.2 := by
  obtain ⟨z1, h1, hy⟩ := hy
  obtain ⟨x1, hx1, rfl⟩ := SInvQ.q1_mem_threadGet h1
  obtain ⟨z2, h2, hy⟩ := hy
  unfold getThreadState at h2
  obtain ⟨x2, -, rfl⟩ := SInvQ.q1_mem_threadGet h2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    cases hsc : x1.tcbSchedContext with
    | none => exact absurd hsc hc.1
    | some c =>
      rw [hsc] at hy
      obtain ⟨⟨c', s3⟩, h3, hy⟩ := hy
      obtain ⟨e3a, e3b⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
      subst c'
      subst s3
      obtain ⟨⟨sc, s4⟩, h4, hy⟩ := hy
      obtain ⟨⟨n4, hk4⟩, e4⟩ := SInvI.mem_getSchedContext_vi h4
      simp only at e4 hk4
      subst s4
      obtain ⟨⟨ct, s5⟩, h5, hy⟩ := hy
      obtain ⟨e5a, e5b⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h5)
      subst ct
      subst s5
      have hact : scActive sc = true := by
        obtain ⟨x', c'', y', n', hx', hc', hy', ha'⟩ := hab x1 c hx1 hsc
        rw [hx1] at hx'; cases hx'
        rw [hsc] at hc'; cases hc'
        rw [hk4] at hy'; cases hy'
        exact ha'
      dsimp only at hy
      split_ifs at hy with hg
      · refine rd_possibleSwitchTo_q receiver s (fun x c0 hx hc0 => ?_) hR y hy
        exact ⟨x1, c, sc, n4, hx1, hsc, hk4, hact, hg.1⟩
      · obtain ⟨⟨tb, s6⟩, h6, hy⟩ := hy
        have e6 : s6 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h6
        subst s6
        dsimp only at hy
        split_ifs at hy
        · exact rd_handleTimeout_p receiver _ s hR y hy
        · refine rd_postpone_fwd c s hF (fun y' n' hk' => ?_) hR y hy
          rw [hk4] at hk'; cases hk'; exact hact
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hR

/-- **`do_reply_transfer sender reply grant`** keeps `Rdy`, from `T1` / `Simple`
(ctq), `ScInv` (sb2) and `BlockedScActive` at its start. -/
theorem rd_doReplyTransfer (sender reply : ObjRef) (grant : Bool) (σ : State Unit) (hR : Rdy σ)
    (h1 : SInvQ.T1 σ) (hA : SInvQ.Simple σ) (hI : SInvB.ScInv σ) (hB : Sched.BlockedScActive σ)
    {y : Unit × State Unit} (hy : y ∈ (doReplyTransfer (Z := Unit) sender reply grant σ).1) : Rdy y.2 := by
  unfold doReplyTransfer at hy
  obtain ⟨⟨recvOpt, s1⟩, hz1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  cases recvOpt with
  | none =>
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hR
  | some receiver =>
    dsimp only [NonDet.maybeM] at hy
    obtain ⟨⟨st, s2⟩, hz2, hy⟩ := hy
    unfold getThreadState at hz2
    obtain ⟨x, hx, e2⟩ := SInvQ.q1_mem_threadGet hz2
    obtain ⟨rfl, e2'⟩ := Prod.mk.inj e2
    subst s2
    cases hst : x.tcbState
    all_goals first
      | (rw [hst] at hy; dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hR)
      | skip
    rename_i r
    rw [hst] at hy
    dsimp only at hy
    obtain ⟨⟨u3, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    obtain ⟨z4, hz4, hy⟩ := hy
    have e4 : Rdy z4.2 := rd_replyRemove receiver reply σ hR h1 hA hI.fwd
      (fun x' hx' => by rw [hx] at hx'; cases hx'; rw [hst]; exact not_blkR_reply r _) hz4
    have i4 : SInvB.ScInv z4.2 := SInvB.sik_replyRemove receiver reply σ hI z4 hz4
    obtain ⟨ab4, x4, hx4, hs4⟩ := abo_replyRemove receiver reply σ hB hI.back hx (by rw [hst]; rfl) hz4
    obtain ⟨z5, hz5, hy⟩ := hy
    obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    obtain ⟨e6, -, k6⟩ := rd_ifCond _ _ _ z4.2 e4 hz6
    have f6 := sf_ifCond _ _ _ z4.2 hz6
    have F6 : SInvB.ScFwd z6.2 := f6.2.1 i4.fwd
    have ab6 : ABo receiver z6.2 := abo_ifCond _ _ _ receiver z4.2 e4 ab4 hz6
    obtain ⟨z7, hz7, hy⟩ := hy
    obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet hz7
    cases hf : x7.tcbFault with
    | none =>
      rw [hf] at hy
      dsimp only at hy
      obtain ⟨z8, hz8, hy⟩ := hy
      have e8 : Rdy z8.2 := rd_doIpcTransfer sender none 0 grant receiver z6.2 e6 z8 hz8
      have v8 : SVK.SVS z6.2 z8.2 := SVK.sv_doIpcTransfer' sender none 0 grant receiver z6.2 z8 hz8
      obtain ⟨z9, hz9, hy⟩ := hy
      have e9 : Rdy z9.2 := rd_setThreadState receiver .running trivial z8.2 e8 z9 hz9
      have v9 : SVK.SVS z8.2 z9.2 := SVK.sv_setThreadState' receiver .running z8.2 z9 hz9
      exact rd_replyTail receiver none z9.2 e9 (fwd_svs F6 (v8.trans v9)) (abo_svs ab6 (v8.trans v9)) hy
    | some f =>
      rw [hf] at hy
      dsimp only at hy
      obtain ⟨z8, hz8, hy⟩ := hy
      have e8 : Rdy z8.2 := rd_getMessageInfo sender z6.2 e6 z8 hz8
      have v8 : SVK.SVS z6.2 z8.2 := SVK.sv_getMessageInfo' sender z6.2 z8 hz8
      obtain ⟨z9, hz9, hy⟩ := hy
      have e9 : Rdy z9.2 := rd_lookupIpcBuffer false sender z8.2 e8 z9 hz9
      have v9 : SVK.SVS z8.2 z9.2 := SVK.sv_lookupIpcBuffer' false sender z8.2 z9 hz9
      obtain ⟨z10, hz10, hy⟩ := hy
      have e10 : Rdy z10.2 := rd_getMrs sender _ _ z9.2 e9 z10 hz10
      have v10 : SVK.SVS z9.2 z10.2 := SVK.sv_getMrs' sender _ _ z9.2 z10 hz10
      obtain ⟨z11, hz11, hy⟩ := hy
      have e11 : Rdy z11.2 := rd_handleFaultReply f receiver _ _ z10.2 e10 z11 hz11
      have v11 : SVK.SVS z10.2 z11.2 := SVK.sv_handleFaultReply' f receiver _ _ z10.2 z11 hz11
      obtain ⟨z12, hz12, hy⟩ := hy
      obtain ⟨x12, hx12, e12⟩ := SInv.mem_threadSet hz12
      have v12 : SVK.SVS z11.2 z12.2 :=
        SVK.sv_threadSet' (fun tcb => { tcb with tcbFault := none }) (fun _ => rfl) receiver z11.2 z12 hz12
      obtain ⟨z13, hz13, hy⟩ := hy
      obtain ⟨z14, hz14, hz13'⟩ := hz13
      obtain ⟨x14, hx14, e14⟩ := SInv.mem_threadSet hz14
      have v13 : SVK.SVS z12.2 z13.2 := SVK.sv_setThreadState' receiver _ z12.2 z13 ⟨z14, hz14, hz13'⟩
      have hx14' : x14 = { x12 with tcbFault := none } := by
        rw [e12] at hx14; simp at hx14; exact hx14.symm
      subst hx14'
      have e14' : Rdy z14.2 := by
        rw [e14, e12]
        refine rdy_setTwice e11 hx12 _ _ rfl ?_
        split_ifs <;>
          rintro (⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩) <;> cases h
      have e13 : Rdy z13.2 := rd_setThreadStateAct receiver z14.2 e14' z13 hz13'
      have V : SVK.SVS z6.2 z13.2 := v8.trans (v9.trans (v10.trans (v11.trans (v12.trans v13))))
      exact rd_replyTail receiver (some f) z13.2 e13 (fwd_svs F6 V) (abo_svs ab6 V) hy

end

end Fl4Proofs.P3.SInvR.B8e
