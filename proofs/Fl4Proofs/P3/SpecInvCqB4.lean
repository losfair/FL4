/-
P3 (DESIGN.md §9), invariant line G1 (ctq10): **`do_reply_transfer` keeps
`EB true`** (KENTRY-PLAN ctq9 handoff 1; spec side only, outside the JAtZ
cone). ReplyRecv runs `handle_recv` after it, so the strong form is needed.

* At its start (`D0 C`): `EB true`, the current thread `C`, nq3's `NQ [C]`,
  sb2's `ScInv`, and `C` a runnable TCB. In the perform `C` is the sender:
  `fl4HandleInvocationR` writes `set_thread_state ct Restart` right before
  `perform_invocation`, so the last fact is local (no `EntryJ`, no ∀-state
  premise).
* The receiver `r` is read `BlockedOnReply`, so `r ≠ C` (`C` runnable) and
  `NQ [r, C]` (nq3's `nq_consR`).
* `reply_remove r` keeps `DR r C := EB true ∧ ct = C ∧ NQ [r, C] ∧ ScInv`
  (generated tq/sa/q4/rb leaves; its donation's `test_reschedule` only
  reschedules) and ends with `r` Inactive (`post_replyRemove`), so `NPQ r`
  by SchedQ (`npq_nr`): `DN r C := DR r C ∧ NPQ r` from there on.
* The refill check, `do_ipc_transfer`, the fault-reply reads and
  `handle_fault_reply` keep `DN` (one lemma each from the generated leaves: EB from
  tq/sa/q4/rb, `NPQ` and ct from ctq7's FX frame, NQ from nq3, ScInv from sb2's SBK); `set_thread_state r _` keeps it
  (`dn_setThreadState`: `NPQ r` before the write).
* The tail (`dn_tail`): `possible_switch_to r` (`r` read runnable, `r ≠ ct`),
  `handle_timeout r` (`NPQ r`, `NQ [r, C]` with ct ∈), `postpone scPtr`
  (sb2's `ScBackS`: `r`'s SC is `scPtr`, so its `sc_tcb` is `r`; `r`
  runnable, `≠ ct`, not the switch target by `NPQ r`).
* **`eb_doReplyTransfer C : HK (D0 C) (EB true) (do_reply_transfer s r g)`**,
  `eb_doReplyTransfer_ct`.
-/
import Fl4Proofs.P3.SpecInvCqB3
import Fl4Proofs.P3.SpecInvSbG4
open Classical

namespace Fl4Proofs.P3.SInvQ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Posts and frames -/

theorem post_sts (t : ObjRef) (ts : ThreadState) :
    PostK (fun s => ∃ x, s.kheap t = some (.tcb x) ∧ x.tcbState = ts) (setThreadState (Z := Unit) t ts) :=
  fun _ y hy => by obtain ⟨x, -, e⟩ := q3_setThreadState_out hy; exact ⟨_, e, rfl⟩

/-- `reply_remove caller r` leaves `caller` Inactive (its last step is
`reply_unlink_tcb`). -/
theorem post_replyRemove (caller r : ObjRef) :
    PostK (fun s => ∃ x, s.kheap caller = some (.tcb x) ∧ x.tcbState = .inactive)
      (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove replyUnlinkTcb
  dsimp only
  repeat' (first | (with_reducible exact post_sts _ _) | (with_reducible refine post_bind fun _ => ?_) | split)

theorem npq_setThreadState (u t : ObjRef) (ts : ThreadState) : IK (NPQ u) (setThreadState (Z := Unit) t ts) :=
  fun σ h y hy => ((show IK (NC u σ.curThread) (setThreadState (Z := Unit) t ts) by
    unfold setThreadState; nc_auto) σ ⟨h, rfl⟩ y hy).1

/-! ## The carried facts -/

/-- At `do_reply_transfer`'s start. -/
abbrev D0 (C : ObjRef) (s : State Unit) : Prop :=
  EB true s ∧ CTh C s ∧ NQ [C] s ∧ SInvB.ScInv s ∧ RnH C s.kheap

/-- Across `reply_remove r`. -/
abbrev DR (r C : ObjRef) (s : State Unit) : Prop := EB true s ∧ CTh C s ∧ NQ [r, C] s ∧ SInvB.ScInv s

/-- After `reply_remove r`. -/
abbrev DN (r C : ObjRef) (s : State Unit) : Prop := DR r C s ∧ NPQ r s

theorem dn_of_fx {r C : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h1 : EBK true m)
    (h2 : ∀ A R Q C, FXK A R Q C m) (h3 : NQK [r, C] m) (h4 : SInvB.SIK m) : IK (DN r C) m := by
  intro σ h y hy
  have e := nc_of_fx h2 r C σ ⟨h.2, h.1.2.1⟩ y hy
  exact ⟨⟨h1 σ h.1.1 y hy, e.2, h3 σ h.1.2.2.1 y hy, h4 σ h.1.2.2.2 y hy⟩, e.1⟩

theorem dn_refill (r C : ObjRef) (o : Option ObjRef) (a b : Option Bool) :
    IK (DN r C) (ifCondRefillUnblockCheck (Z := Unit) o a b) :=
  dn_of_fx (eb_of (tq_ifCondRefillUnblockCheck _ _ _) (sa_ifCondRefillUnblockCheck _ _ _)
      (q4_ifCondRefillUnblockCheck _ _ _) (rb_ifCondRefillUnblockCheck _ _ _))
    (fun _ _ _ _ => by unfold ifCondRefillUnblockCheck; fx_auto) (nq_ifCondRefillUnblockCheck _ _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_ifCondRefillUnblockCheck _ _ _)

theorem dn_doIpcTransfer (r C sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (rcv : ObjRef) :
    IK (DN r C) (doIpcTransfer (Z := Unit) sender ep badge grant rcv) :=
  dn_of_fx (eb_of (tq_doIpcTransfer _ _ _ _ _) (sa_doIpcTransfer _ _ _ _ _) (q4_doIpcTransfer _ _ _ _ _)
      (rb_doIpcTransfer _ _ _ _ _))
    (fun _ _ _ _ => fx_doIpcTransfer _ _ _ _ _) (nq_doIpcTransfer _ _ _ _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_doIpcTransfer _ _ _ _ _)

theorem dn_getMessageInfo (r C t : ObjRef) : IK (DN r C) (getMessageInfo (Z := Unit) t) :=
  dn_of_fx (eb_of (tq_getMessageInfo _) (sa_getMessageInfo _) (q4_getMessageInfo _) (rb_getMessageInfo _))
    (fun _ _ _ _ => fx_getMessageInfo _) (nq_getMessageInfo _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_getMessageInfo _)

theorem dn_lookupIpcBuffer (r C : ObjRef) (b : Bool) (t : ObjRef) : IK (DN r C) (lookupIpcBuffer (Z := Unit) b t) :=
  dn_of_fx (eb_of (tq_lookupIpcBuffer _ _) (sa_lookupIpcBuffer _ _) (q4_lookupIpcBuffer _ _) (rb_lookupIpcBuffer _ _))
    (fun _ _ _ _ => fx_lookupIpcBuffer _ _) (nq_lookupIpcBuffer _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_lookupIpcBuffer _ _)

theorem dn_getMrs (r C t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : IK (DN r C) (getMrs (Z := Unit) t b mi) :=
  dn_of_fx (eb_of (tq_getMrs _ _ _) (sa_getMrs _ _ _) (q4_getMrs _ _ _) (rb_getMrs _ _ _))
    (fun _ _ _ _ => by unfold getMrs; fx_auto) (nq_getMrs _ _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_getMrs _ _ _)

theorem dn_handleFaultReply (r C : ObjRef) (f : Fault) (t : ObjRef) (l : Data) (ms : List Data) :
    IK (DN r C) (handleFaultReply (Z := Unit) f t l ms) :=
  dn_of_fx (eb_of (tq_handleFaultReply _ _ _ _) (sa_handleFaultReply _ _ _ _) (q4_handleFaultReply _ _ _ _)
      (rb_handleFaultReply _ _ _ _))
    (fun _ _ _ _ => by cases f <;> (unfold handleFaultReply; fx_auto)) (nq_handleFaultReply _ _ _ _)
    (SInvB.sik_of_sbk fun _ => SInvB.sb_handleFaultReply _ _ _ _)

theorem dr_replyRemove (r C reply : ObjRef) : IK (DR r C) (replyRemove (Z := Unit) r reply) := by
  intro σ h y hy
  refine ⟨(show EBK true (replyRemove (Z := Unit) r reply) by eb_auto) σ h.1 y hy, ?_,
    nq_replyRemove (Kq := [r, C]) r reply (by simp) σ h.2.2.1 y hy, SInvB.sik_replyRemove r reply σ h.2.2.2 y hy⟩
  exact (show IK (CTh C) (replyRemove (Z := Unit) r reply) by
    unfold replyRemove
    repeat' (first | (with_reducible exact ct_schedContextDonate _ _ _) | (with_reducible exact ct_setThreadState _ _ _) | ik_step0 | ik_unfold | (unfold NonDet.when))) σ h.2.1 y hy

theorem dn_setThreadState (r C : ObjRef) (ts : ThreadState) (hts : ¬ isBoN ts) :
    HK (DN r C) (DN r C) (setThreadState (Z := Unit) r ts) := by
  intro s h y hy
  exact ⟨⟨eb_setThreadState_p r ts s (Or.inr h.2) h.1.1 y hy, ct_setThreadState C r ts s h.1.2.1 y hy,
    nq_setThreadState r ts (by simp) hts s h.1.2.2.1 y hy,
    (show SInvB.SIK (setThreadState (Z := Unit) r ts) by si_auto) s h.1.2.2.2 y hy⟩,
    npq_setThreadState r r ts s h.2 y hy⟩

theorem dn_threadSetFault (r C : ObjRef) :
    IK (DN r C) (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := none }) r) :=
  dn_of_fx (eb_threadSet _ r (fun _ => by exact ⟨rfl, rfl, rfl⟩) (fun _ h => by exact h))
    (fun _ _ _ _ => by unfold threadSet; fx_auto) (nq_threadSet _ r (fun _ => by rfl)) (by si_auto)

/-! ## The tail -/

/-- **The tail of `do_reply_transfer`**: wake, time out, or postpone the
receiver. -/
theorem dn_tail (r C : ObjRef) (hne : r ≠ C) (fault : Option Fault) :
    HK (DN r C) (EB true) (do
        let scOpt ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext r
        let state ← getThreadState r
        NonDet.when (scOpt ≠ none ∧ runnable state) <| do
          let scPtr ← NonDet.assertOpt scOpt
          let sc ← getSchedContext scPtr
          let curtime ← NonDet.gets fun s : State Unit => s.curTime
          if refillReady curtime (refillHd sc) ∧ refillSufficient 0 (refillHd sc)
          then possibleSwitchTo r
          else do
            let tcb ← NonDet.getsThe (getTcb r)
            if isEpCap tcb.tcbTimeoutHandler ∧ ¬(fault.elim false isTimeoutFault = true)
            then handleTimeout r (.timeout sc.scBadge)
            else postpone scPtr) := by
  intro s hs y hy
  obtain ⟨z1, hz1, hy⟩ := hy
  unfold getTcbObjRef at hz1
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz1
  obtain ⟨z2, hz2, hy⟩ := hy
  unfold getThreadState at hz2
  obtain ⟨x2, hx2, rfl⟩ := q1_mem_threadGet hz2
  rw [hx] at hx2; cases hx2
  dsimp only at hy
  unfold NonDet.when at hy
  split at hy
  · rename_i hc
    obtain ⟨-, hrun⟩ := hc
    obtain ⟨z3, hz3, hy⟩ := hy
    obtain ⟨e3, e3'⟩ := cq5_mem_assertOpt hz3
    have e3 : x.tcbSchedContext = some z3.1 := e3
    rw [e3'] at hy
    obtain ⟨z4, hz4, hy⟩ := hy
    rw [cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz4] at hy
    obtain ⟨z5, hz5, hy⟩ := hy
    rw [mem_gets hz5] at hy
    dsimp only at hy
    split at hy
    · exact eb_possibleSwitchTo_p r s ⟨x, hx, hrun⟩ (fun _ => by rw [hs.1.2.1]; exact hne) hs.1.1 y hy
    · obtain ⟨z6, hz6, hy⟩ := hy
      rw [cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hz6] at hy
      dsimp only at hy
      split at hy
      · exact eb_handleTimeout_p r _ s hs.2 hs.1.2.2.1 (by rw [hs.1.2.1]; simp) hs.1.1 y hy
      · refine eb_postpone_p _ s (fun y' n t hk ht => ?_) hs.1.1 y hy
        have hSy := SInvB.ScInv.sym hs.1.2.2.2
        unfold SInvB.ScSym at hSy
        have hB := hSy.1
        unfold SInvB.ScBackS at hB
        obtain ⟨y0, k0, hk0, ht0, -⟩ := hB r x z3.1 hx e3
        rw [hk0] at hk; cases hk
        rw [ht0] at ht; cases ht
        exact ⟨⟨x, hx, hrun⟩, fun _ => by rw [hs.1.2.1]; exact hne, hs.2.1.1⟩
  · rw [Set.mem_singleton_iff.1 hy]; exact hs.1.1

/-! ## `do_reply_transfer` -/

theorem hk_gts {P Q : State Unit → Prop} {β : Type} {t : ObjRef} {k : ThreadState → NonDet (State Unit) β}
    (h : ∀ ts, HK (fun s => P s ∧ ∃ x, s.kheap t = some (.tcb x) ∧ x.tcbState = ts) Q (k ts)) :
    HK P Q (getThreadState (Z := Unit) t >>= k) := by
  intro s hs y ⟨z, hz, hy⟩
  unfold getThreadState at hz
  obtain ⟨x, hx, rfl⟩ := q1_mem_threadGet hz
  exact h x.tcbState s ⟨hs, x, hx, rfl⟩ y hy

set_option maxHeartbeats 4000000 in
/-- **`do_reply_transfer` keeps `EB true`** from `D0 C` (the current thread
`C` runnable, nq3's `NQ [C]`, sb2's `ScInv`). -/
theorem eb_doReplyTransfer (C sender reply : ObjRef) (grant : Bool) :
    HK (D0 C) (EB true) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer
  refine hk_bind (hk_of_ik (ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun ro => ?_
  cases ro with
  | none => exact fun σ h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h.1
  | some receiver =>
    show HK _ _ (getThreadState (Z := Unit) receiver >>= _)
    refine hk_gts fun ts => ?_
    cases ts
    case blockedOnReply r' =>
      dsimp only
      by_cases hne : receiver = C
      · intro s ⟨⟨_, _, _, _, x0, hx0, hr0⟩, x, hx, hxs⟩
        subst hne
        rw [hx] at hx0; cases hx0
        rw [hxs] at hr0
        exact absurd hr0 (by simp [runnable])
      refine hk_bind (hk_of_ik (ik_assert _)) fun _ => ?_
      refine hk_bind (R := DN receiver C) ?_ fun _ => ?_
      · intro s ⟨⟨h1, h2, h3, h4, _⟩, x, hx, hxs⟩ y hy
        have hq : NQ [receiver, C] s := nq_consR h3 hx (by rw [hxs]; exact fun h => h) (by rw [hxs]; rfl)
        have hD : DR receiver C y.2 := dr_replyRemove receiver C reply s ⟨h1, h2, hq, h4⟩ y hy
        obtain ⟨x', hx', hs'⟩ := post_replyRemove receiver reply s y hy
        exact ⟨hD, npq_nr hD.1.1 hx' (by rw [hs']; rfl)⟩
      refine hk_bind (hk_of_ik (ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun scOpt => ?_
      refine hk_bind (hk_of_ik (dn_refill _ _ _ _ _)) fun _ => ?_
      refine hk_bind (hk_of_ik (ik_of_ro fun _ => by repeat' (first | ik_step0 | ik_unfold))) fun fault => ?_
      (try dsimp only)
      cases fault with
      | none =>
        refine hk_bind (hk_of_ik (dn_doIpcTransfer _ _ _ _ _ _ _)) fun _ => ?_
        refine hk_bind (dn_setThreadState receiver C .running (fun h => h)) fun _ => ?_
        exact dn_tail receiver C hne none
      | some f =>
        refine hk_bind (hk_of_ik (dn_getMessageInfo _ _ _)) fun _ => hk_bind (hk_of_ik (dn_lookupIpcBuffer _ _ _ _)) fun _ =>
          hk_bind (hk_of_ik (dn_getMrs _ _ _ _ _)) fun _ => hk_bind (hk_of_ik (dn_handleFaultReply _ _ _ _ _ _)) fun rs => ?_
        refine hk_bind (hk_of_ik (dn_threadSetFault receiver C)) fun _ => ?_
        refine hk_bind (dn_setThreadState receiver C _ (by cases rs <;> exact fun h => h)) fun _ => ?_
        exact dn_tail receiver C hne (some f)
    all_goals
      dsimp only
      exact fun s h y hy => by rw [Set.mem_singleton_iff.1 hy]; exact h.1.1

/-- `do_reply_transfer` from the current thread's facts. -/
theorem eb_doReplyTransfer_ct (sender reply : ObjRef) (grant : Bool) (σ : State Unit) (hσ : EB true σ)
    (hN : NQ [σ.curThread] σ) (hS : SInvB.ScInv σ) (hR : RnH σ.curThread σ.kheap) :
    ∀ y ∈ (doReplyTransfer (Z := Unit) sender reply grant σ).1, EB true y.2 :=
  eb_doReplyTransfer σ.curThread sender reply grant σ ⟨hσ, rfl, hN, hS, hR⟩

end

end Fl4Proofs.P3.SInvQ
