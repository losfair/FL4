/-
P3 (DESIGN.md §9), invariant line G1 (rd8k): **`Sched.BlockedScActive`
across `do_reply_transfer` and `handle_recv`** (spec side only, outside the
JAtZ cone; KENTRY-PLAN rd8i handoff 1-2).

* `abo_ifCond'`: rd8e's `ABo t` across `if_cond_refill_unblock_check`
  WITHOUT `Rdy`, from the write's shape (rd8d's `sf_ifCond`: every TCB kept;
  rd8's `A8.ab_ifCond`: `ActB t` kept), given `t` a TCB.
* **`ba_replyTail`** (ScFwd + `ABo receiver`: the `handle_timeout` arm gets
  `TA receiver` by rd8i's `ta_of_fwd`), **`ba_doReplyTransfer sender reply
  grant σ (hI : ScInv σ)`** (rd8e's `rd_doReplyTransfer` walk; `ABo receiver`
  after `reply_remove` by rd8e's `abo_replyRemove` from BlockedScActive and
  ScBackS).
* `RK C s := BSA s ∧ ScInv s ∧ NotQ C s ∧ CBa C s ∧ ct = C`, `rk_asUser`,
  `rk_lookupReply`, **`ba_handleRecv C blk cr : HK (RK C) BSA (handle_recv
  blk cr)`** (rd8h's `rd_handleRecv` skeleton: endpoint → rd8i's
  `ba_receiveIpc_p`, notification → `ba_receiveSignal_p`, lookup fault →
  `ba_handleFault_p`; `TA C` = `ta_of_fwd ScFwd (CBa C)`).
-/
import Fl4Proofs.P3.SpecInvRd8iD
import Fl4Proofs.P3.SpecInvRd8hR
open Classical

namespace Fl4Proofs.P3.SInvR.B8k
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvQ Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c
  Fl4Proofs.P3.SInvR.B8d Fl4Proofs.P3.SInvR.B8e Fl4Proofs.P3.SInvR.B8g Fl4Proofs.P3.SInvR.B8i

noncomputable section

set_option maxHeartbeats 1000000

/-! ## `do_reply_transfer` -/

/-- rd8e's `ABo t` across the unblock check, from its write shape (no `Rdy`). -/
theorem abo_ifCond' (o : Option ObjRef) (a b : Option Bool) (t : ObjRef) (s : State Unit)
    {x : Tcb} (hx : s.kheap t = some (.tcb x)) (h : ABo t s) {r : Unit × State Unit}
    (hr : r ∈ (ifCondRefillUnblockCheck (Z := Unit) o a b s).1) : ABo t r.2 := by
  intro x' c hx' hc
  have k := (sf_ifCond o a b s hr).2.2 t x hx
  rw [k] at hx'; cases hx'
  exact A8.ab_ifCond o a b t s (h x c hx hc) r hr

theorem cba_of_abo {t : ObjRef} {s : State Unit} (h : ABo t s) : CBa t s := by
  intro x c hx hc
  exact cba_of_actB (h x c hx hc) x c hx hc

/-- **`do_reply_transfer`'s tail** from `ScFwd` and `ABo receiver`. -/
theorem ba_replyTail (receiver : ObjRef) (fault : Option Fault) (s : State Unit)
    (hF : SInvB.ScFwd s) (hab : ABo receiver s) (hb : BSA s) {y : Unit × State Unit}
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
            else postpone (Z := Unit) scPtr) s).1) : BSA y.2 := by
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
      dsimp only at hy
      split_ifs at hy with hg
      · exact ba_possibleSwitchTo receiver s hb y hy
      · obtain ⟨⟨tb, s6⟩, h6, hy⟩ := hy
        have e6 : s6 = s := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) h6
        subst s6
        dsimp only at hy
        split_ifs at hy
        · exact ba_handleTimeout_p receiver _ s (ta_of_fwd hF (cba_of_abo hab)) hb y hy
        · exact ba_postpone c s hb y hy
  · obtain rfl := Set.mem_singleton_iff.1 hy
    exact hb

/-- **`do_reply_transfer sender reply grant`** keeps `BlockedScActive`, from
sb2's `ScInv` at its start. -/
theorem ba_doReplyTransfer (sender reply : ObjRef) (grant : Bool) (σ : State Unit) (hI : SInvB.ScInv σ) :
    IKp BSA σ (doReplyTransfer (Z := Unit) sender reply grant) := by
  intro hB y hy
  unfold doReplyTransfer at hy
  obtain ⟨⟨recvOpt, s1⟩, hz1, hy⟩ := hy
  have e1 : s1 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz1
  subst s1
  cases recvOpt with
  | none =>
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact hB
  | some receiver =>
    dsimp only [NonDet.maybeM] at hy
    obtain ⟨⟨st, s2⟩, hz2, hy⟩ := hy
    unfold getThreadState at hz2
    obtain ⟨x, hx, e2⟩ := SInvQ.q1_mem_threadGet hz2
    obtain ⟨rfl, e2'⟩ := Prod.mk.inj e2
    subst s2
    cases hst : x.tcbState
    all_goals first
      | (rw [hst] at hy; dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hB)
      | skip
    rename_i r
    rw [hst] at hy
    dsimp only at hy
    obtain ⟨⟨u3, s3⟩, hz3, hy⟩ := hy
    have e3 : s3 = σ := SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz3
    subst s3
    obtain ⟨z4, hz4, hy⟩ := hy
    have b4 : BSA z4.2 := ba_replyRemove receiver reply σ hB z4 hz4
    have i4 : SInvB.ScInv z4.2 := SInvB.sik_replyRemove receiver reply σ hI z4 hz4
    obtain ⟨ab4, x4, hx4, -⟩ := abo_replyRemove receiver reply σ hB hI.back hx (by rw [hst]; rfl) hz4
    obtain ⟨z5, hz5, hy⟩ := hy
    obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet hz5
    obtain ⟨z6, hz6, hy⟩ := hy
    have b6 : BSA z6.2 := ba_ifCondRefillUnblockCheck _ _ _ z4.2 b4 z6 hz6
    have f6 := sf_ifCond _ _ _ z4.2 hz6
    have F6 : SInvB.ScFwd z6.2 := f6.2.1 i4.fwd
    have ab6 : ABo receiver z6.2 := abo_ifCond' _ _ _ receiver z4.2 hx4 ab4 hz6
    obtain ⟨z7, hz7, hy⟩ := hy
    obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet hz7
    cases hf : x7.tcbFault with
    | none =>
      rw [hf] at hy
      dsimp only at hy
      obtain ⟨z8, hz8, hy⟩ := hy
      have b8 : BSA z8.2 := ba_doIpcTransfer sender none 0 grant receiver z6.2 b6 z8 hz8
      have v8 : SVK.SVS z6.2 z8.2 := SVK.sv_doIpcTransfer' sender none 0 grant receiver z6.2 z8 hz8
      obtain ⟨z9, hz9, hy⟩ := hy
      have b9 : BSA z9.2 := ba_setThreadState receiver .running rfl z8.2 b8 z9 hz9
      have v9 : SVK.SVS z8.2 z9.2 := SVK.sv_setThreadState' receiver .running z8.2 z9 hz9
      exact ba_replyTail receiver none z9.2 (fwd_svs F6 (v8.trans v9)) (abo_svs ab6 (v8.trans v9)) b9 hy
    | some f =>
      rw [hf] at hy
      dsimp only at hy
      obtain ⟨z8, hz8, hy⟩ := hy
      have b8 : BSA z8.2 := ba_getMessageInfo sender z6.2 b6 z8 hz8
      have v8 : SVK.SVS z6.2 z8.2 := SVK.sv_getMessageInfo' sender z6.2 z8 hz8
      obtain ⟨z9, hz9, hy⟩ := hy
      have b9 : BSA z9.2 := ba_lookupIpcBuffer false sender z8.2 b8 z9 hz9
      have v9 : SVK.SVS z8.2 z9.2 := SVK.sv_lookupIpcBuffer' false sender z8.2 z9 hz9
      obtain ⟨z10, hz10, hy⟩ := hy
      have b10 : BSA z10.2 := ba_getMrs sender _ _ z9.2 b9 z10 hz10
      have v10 : SVK.SVS z9.2 z10.2 := SVK.sv_getMrs' sender _ _ z9.2 z10 hz10
      obtain ⟨z11, hz11, hy⟩ := hy
      have b11 : BSA z11.2 := ba_handleFaultReply f receiver _ _ z10.2 b10 z11 hz11
      have v11 : SVK.SVS z10.2 z11.2 := SVK.sv_handleFaultReply' f receiver _ _ z10.2 z11 hz11
      obtain ⟨z12, hz12, hy⟩ := hy
      have b12 : BSA z12.2 :=
        ba_threadSet (fun tcb => { tcb with tcbFault := none }) receiver (fun _ => rfl) z11.2 b11 z12 hz12
      have v12 : SVK.SVS z11.2 z12.2 :=
        SVK.sv_threadSet' (fun tcb => { tcb with tcbFault := none }) (fun _ => rfl) receiver z11.2 z12 hz12
      obtain ⟨z13, hz13, hy⟩ := hy
      have v13 : SVK.SVS z12.2 z13.2 := SVK.sv_setThreadState' receiver _ z12.2 z13 hz13
      have b13 : BSA z13.2 := ba_setThreadState receiver _ (by split <;> rfl) z12.2 b12 z13 hz13
      have V : SVK.SVS z6.2 z13.2 := v8.trans (v9.trans (v10.trans (v11.trans (v12.trans v13))))
      exact ba_replyTail receiver (some f) z13.2 (fwd_svs F6 V) (abo_svs ab6 V) b13 hy

/-! ## `handle_recv` -/

/-- The receiver's facts at a state of `handle_recv`. -/
def RK (C : ObjRef) (s : State Unit) : Prop :=
  BSA s ∧ SInvB.ScInv s ∧ NotQ C s ∧ CBa C s ∧ s.curThread = C

theorem rk_asUser (C t : ObjRef) (r : Register) : IK (RK C) (asUser (Z := Unit) t (getRegister r)) := by
  intro s hs z hz
  obtain ⟨hb, hI, hN, hC, hc⟩ := hs
  have v := SVK.sv_asUser' t _ s z hz
  have hc' : z.2.curThread = C :=
    (show IK (fun s : State Unit => s.curThread = C) (asUser (Z := Unit) t (getRegister r)) by
      unfold asUser; repeat' (first | ik_step0 | ik_unfold)) s hc z hz
  exact ⟨ba_asUser t _ s hb z hz, SInvB.sik_of_sbk (fun _ => SInvB.sb_asUser _ _) s hI z hz,
    nq_asUser C t _ s hN z hz, cba_sv hC v, hc'⟩

theorem rk_lookupReply (C : ObjRef) : IKE (RK C) (lookupReply (Z := Unit)) := by
  unfold lookupReply
  repeat' (first | (with_reducible exact rk_asUser _ _ _) |
    (with_reducible exact SInvQ.pk_capFaultLookupCap _ _ _ _) | ik_step0 | ik_unfold)

/-- **`handle_recv` keeps `BlockedScActive`** from `RK C` at its start. -/
theorem ba_handleRecv (C : ObjRef) (blk canReply : Bool) :
    SInv.HK (RK C) BSA (handleRecv (Z := Unit) blk canReply) := by
  have hro : ∀ {α : Type} {m : NonDet (State Unit) α}, (∀ σ0 : State Unit, IK (fun s => s = σ0) m) →
      IK (RK C) m := fun h => SInvQ.ik_of_ro h
  have hRIP : ∀ cp rc, SInv.HK (RK C) BSA (receiveIpc (Z := Unit) C cp blk rc) :=
    fun cp rc s hs y hy => ba_receiveIpc_p C cp blk rc s hs.2.1 hs.2.2.1
      (ta_of_fwd hs.2.1.fwd hs.2.2.2.1) hs.1 y hy
  have hRS : ∀ cp, SInv.HK (RK C) BSA (receiveSignal (Z := Unit) C cp blk) :=
    fun cp s hs y hy => ba_receiveSignal_p C cp blk s hs.2.2.1 (ta_of_fwd hs.2.1.fwd hs.2.2.2.1) hs.1 y hy
  unfold handleRecv
  intro σ hσ y ⟨y1, h1, hy⟩
  rw [mem_gets h1] at hy
  have hc : σ.curThread = C := hσ.2.2.2.2
  (try dsimp only at hy)
  rw [hc] at hy
  obtain ⟨y2, h2, hy⟩ := hy
  have hb2 : RK C y2.2 := (?_ : IK (RK C) _) σ hσ y2 h2
  · refine hk_catch (I := RK C) (Q0 := BSA) ?_ (fun e => ?_) y2.2 hb2 y hy
    · refine hkr_bind (SInvQ.pk_capFaultLookupCap _ _ _ _) (fun epCap => ?_)
      split
      · (try dsimp only)
        split
        · (try dsimp only)
          split
          · refine hkr_bind (rk_lookupReply C) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
          · refine hkr_bind (ike_returnOk _) (fun rc => ?_)
            exact hkr_liftE (hRIP _ rc)
        · exact hkr_throw _
      · (try dsimp only)
        split
        · refine hkr_bind (hro fun _ => by repeat' (first | ik_step0 | ik_unfold)) (fun bt => ?_)
          split
          · exact hkr_liftE (hRS _)
          · exact hkr_throw _
        · exact hkr_throw _
      · exact hkr_throw _
    · intro s hs z hz
      obtain ⟨hb, hI, -, hC, -⟩ := hs
      exact ba_handleFault_p C e s (ta_of_fwd hI.fwd hC) hC hb z hz
  · repeat' (first | exact rk_asUser C _ _ | ik_step0)

end

end Fl4Proofs.P3.SInvR.B8k
