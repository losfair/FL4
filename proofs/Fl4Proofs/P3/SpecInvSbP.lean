/-
P3 (DESIGN.md §9), invariant line G1 (sb1): **the SC donations** (spec side
only; imports SpecInvSbW).

Every `sched_context_donate` of the syscall entry is guarded by a read of the
receiving TCB's `tcb_sched_context` (`= None`), and every step between the read
and the donation keeps the binding view (`SBK`). So the donation's precondition
holds and `ScInv` is kept with no premise:

* `sik_replyPush` (`reply_push`: `sc_callee = None`),
* `sik_replyRemove` (`reply_remove`: `caller_sc = None`),
* `sik_maybeDonateSc` (`maybe_donate_sc`: the TCB's SC and the notification
  SC's TCB both `None`),
* `sik_sendIpc` (`send_ipc`: the non-call donation, `sc_opt = None`; a call
  goes through `reply_push`).
-/
import Fl4Proofs.P3.SpecInvSbW
open Classical

namespace Fl4Proofs.P3.SInvB
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 2000000

theorem sik_fin {α : Type} {m : NonDet (State Unit) α} (hm : ∀ h0, SBK h0 m) {σ : State Unit}
    (hσ : ScInv σ) {x : α × State Unit} (hx : x ∈ (m σ).1) : ScInv x.2 :=
  scInv_of_br hσ (br_mem_of_sbk hm hx)

theorem sik_replyPush (caller callee r : ObjRef) (d : Bool) : SIK (replyPush (Z := Unit) caller callee r d) := by
  intro σ hσ x hx
  unfold replyPush at hx
  obtain ⟨⟨a, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, -⟩ := mem_getTcbSc hy1
  (try simp only at e1); subst s1
  obtain ⟨⟨b, s2⟩, hy2, hx⟩ := hx
  obtain ⟨e2, xc, hxc, hb⟩ := mem_getTcbSc hy2
  simp only at e2 hb; subst s2
  obtain ⟨y3, hb3, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y4, hb4, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  have hb34 := BR.trans hb3 hb4
  have hI4 := scInv_of_br hσ hb34
  try dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hc
    obtain ⟨y5, hb5, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
    refine sikp_schedContextDonate _ callee y5.2 (Or.inl ?_) (scInv_of_br hI4 hb5) x hx
    rw [bv_of_br hb5, bv_of_br hb34]; exact bv_t.2 ⟨xc, hxc, by rw [hb]; exact hc.2.1⟩
  · rw [Set.mem_singleton_iff.1 hx]; exact hI4

theorem sik_replyRemove (caller r : ObjRef) : SIK (replyRemove (Z := Unit) caller r) := by
  intro σ hσ x hx
  unfold replyRemove at hx
  obtain ⟨y1, hb1, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y2, hb2, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨⟨rs, s3⟩, hy3, hx⟩ := hx
  have e3 := (Prod.mk.inj (mem_gets' hy3)).2
  (try simp only at e3); subst s3
  have hI2 := scInv_of_br hσ (BR.trans hb1 hb2)
  try dsimp only at hx
  cases rs with
  | none => exact sik_fin (fun _ => by sb_auto) hI2 hx
  | some sp =>
    try dsimp only at hx
    obtain ⟨y4, hb4, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
    obtain ⟨⟨cs, s5⟩, hy5, hx⟩ := hx
    obtain ⟨e5, xc, hxc, hcs⟩ := mem_getTcbSc hy5
    simp only at e5 hcs; subst s5
    obtain ⟨y6, hb6, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
    obtain ⟨⟨u7, s7⟩, hy7, hx⟩ := hx
    have hI6 : ScInv y6.2 := scInv_of_br hI2 (BR.trans hb4 hb6)
    have hI7 : ScInv s7 := by
      try dsimp only at hy7
      unfold NonDet.when at hy7
      split at hy7
      · rename_i hc
        refine sikp_schedContextDonate sp caller y6.2 (Or.inl ?_) hI6 _ hy7
        rw [bv_of_br hb6]; exact bv_t.2 ⟨xc, hxc, by rw [hcs]; exact hc.2⟩
      · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hy7)).2]; exact hI6
    exact sik_fin (fun _ => by sb_auto) hI7 hx

theorem sik_maybeDonateSc (t ntfn : ObjRef) : SIK (maybeDonateSc (Z := Unit) t ntfn) := by
  intro σ hσ x hx
  unfold maybeDonateSc at hx
  obtain ⟨⟨so, s1⟩, hy1, hx⟩ := hx
  obtain ⟨e1, xt, hxt, hso⟩ := mem_getTcbSc hy1
  simp only at e1 hso; subst s1
  try dsimp only at hx
  unfold NonDet.when at hx
  split at hx
  · rename_i hc
    obtain ⟨⟨no, s2⟩, hy2, hx⟩ := hx
    have e2 : s2 = σ := (show IK (fun s => s = σ) (getNtfnObjRef (Z := Unit) Notification.ntfnSc ntfn) by
      rd_auto) σ rfl _ hy2
    subst s2
    try dsimp only at hx
    cases no with
    | none => rw [Set.mem_singleton_iff.1 hx]; exact hσ
    | some sp =>
      try dsimp only at hx
      obtain ⟨⟨st, s3⟩, hy3, hx⟩ := hx
      obtain ⟨e3, -⟩ := mem_getScTcb hy3
      (try simp only at e3); subst s3
      try dsimp only at hx
      split at hx
      · obtain ⟨y4, hy4, hx⟩ := hx
        have hI4 := sikp_schedContextDonate sp t σ (Or.inl (bv_t.2 ⟨xt, hxt, by rw [hso]; exact hc⟩)) hσ y4 hy4
        exact sik_fin (fun _ => by sb_auto) hI4 hx
      · rw [Set.mem_singleton_iff.1 hx]; exact hσ
  · rw [Set.mem_singleton_iff.1 hx]; exact hσ

theorem sik_sendIpc (block call : Bool) (badge : Badge) (g gr d : Bool) (thread epptr : ObjRef) :
    SIK (sendIpc (Z := Unit) block call badge g gr d thread epptr) := by
  intro σ hσ x hx
  unfold sendIpc at hx
  obtain ⟨⟨ep, s1⟩, hy1, hx⟩ := hx
  have e1 : s1 = σ := (show IK (fun s => s = σ) (getEndpoint (Z := Unit) epptr) by rd_auto) σ rfl _ hy1
  subst s1
  try dsimp only at hx
  cases ep with
  | idleEP => cases block <;> (try dsimp only at hx) <;> exact sik_fin (fun _ => by sb_auto) hσ hx
  | sendEP q => cases block <;> (try dsimp only at hx) <;> exact sik_fin (fun _ => by sb_auto) hσ hx
  | recvEP q =>
    cases q with
    | nil => (try dsimp only at hx); exact sik_fin (fun _ => by sb_auto) hσ hx
    | cons dest q =>
      try dsimp only at hx
      obtain ⟨y2, hb2, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      obtain ⟨⟨ts, s3⟩, hy3, hx⟩ := hx
      have hb3 : BR y2.2.kheap s3.kheap := br_mem_of_sbk (fun _ => by sb_auto) hy3
      cases ts
      all_goals first | ((try dsimp only at hx); obtain ⟨_, h, -⟩ := hx; exact h.elim) | skip
      rename_i ep0 reply dat
      try dsimp only at hx
      obtain ⟨y4, hb4, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      obtain ⟨y5, hb5, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      obtain ⟨y6, hb6, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      obtain ⟨⟨so, s7⟩, hy7, hx⟩ := hx
      obtain ⟨e7, xd, hxd, hso⟩ := mem_getTcbSc hy7
      simp only at e7 hso; subst s7
      obtain ⟨y8, hb8, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      have hI6 : ScInv y6.2 :=
        scInv_of_br hσ (BR.trans hb2 (BR.trans hb3 (BR.trans hb4 (BR.trans hb5 hb6))))
      have hI8 : ScInv y8.2 := scInv_of_br hI6 hb8
      try dsimp only at hx
      split at hx
      · split at hx
        · obtain ⟨y9, hy9, hx⟩ := hx
          exact sik_fin (fun _ => by sb_auto) (sik_replyPush _ _ _ _ _ hI8 _ hy9) hx
        · exact sik_fin (fun _ => by sb_auto) hI8 hx
      · obtain ⟨⟨u9, s9⟩, hy9, hx⟩ := hx
        have hI9 : ScInv s9 := by
          try dsimp only at hy9
          unfold NonDet.when at hy9
          split at hy9
          · rename_i hc
            obtain ⟨⟨ts, s10⟩, hy10, hy9⟩ := hy9
            obtain ⟨e10, -⟩ := mem_getTcbSc hy10
            (try simp only at e10); subst s10
            refine sikp_schedContextDonate _ dest y8.2 (Or.inl ?_) hI8 _ hy9
            rw [bv_of_br hb8]; exact bv_t.2 ⟨xd, hxd, by rw [hso]; exact hc.2⟩
          · rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hy9)).2]; exact hI8
        exact sik_fin (fun _ => by sb_auto) hI9 hx

theorem sik_receiveIpc_send (thread epptr : ObjRef) (reply : Option ObjRef) (q : List ObjRef) :
    SIK (do
      NonDet.assert (q ≠ [])
      let sender ← pure (the q.head?)
      tcbEpDequeue (Z := Unit) sender epptr
      let senderState ← getThreadState sender
      let data ← match senderState with
        | .blockedOnSend _ref data => pure data
        | _ => NonDet.fail
      doIpcTransfer sender (some epptr) data.senderBadge data.senderCanGrant thread
      let scPtr ← getTcbObjRef Tcb.tcbSchedContext sender
      ifSporadicCurScAssertRefillUnblockCheck scPtr
      let fault ← threadGet Tcb.tcbFault sender
      if data.senderIsCall ∨ fault ≠ none
      then
        if (data.senderCanGrant ∨ data.senderCanGrantReply) ∧ reply ≠ none
        then do
          let senderSc ← getTcbObjRef Tcb.tcbSchedContext sender
          let donate ← pure (decide (senderSc ≠ none ∧ ¬(fault.elim false isTimeoutFault = true)))
          replyPush sender thread (the reply) donate
        else setThreadState sender .inactive
      else do
        setThreadState sender .running
        possibleSwitchTo sender) := by
  intro σ hσ x hx
  obtain ⟨y1, hb1, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y2, hb2, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y3, hb3, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨⟨st, s4⟩, hy4, hx⟩ := hx
  have hb4 := br_mem_of_sbk (fun _ => by sb_auto) hy4
  have hI4 : ScInv s4 := scInv_of_br hσ (BR.trans hb1 (BR.trans hb2 (BR.trans hb3 hb4)))
  cases st
  all_goals first | ((try dsimp only at hx); obtain ⟨_, h, -⟩ := hx; exact h.elim) | skip
  try dsimp only at hx
  obtain ⟨y5, hb5, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y6, hb6, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y7, hb7, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y8, hb8, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  obtain ⟨y9, hb9, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
  have hI9 : ScInv y9.2 := scInv_of_br hI4 (BR.trans hb5 (BR.trans hb6 (BR.trans hb7 (BR.trans hb8 hb9))))
  try dsimp only at hx
  split at hx
  · split at hx
    · obtain ⟨y10, hb10, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      obtain ⟨y11, hb11, hx⟩ := mem_bind_sbk (fun _ => by sb_auto) hx
      exact sik_replyPush _ _ _ _ _ (scInv_of_br hI9 (BR.trans hb10 hb11)) _ hx
    · exact sik_fin (fun _ => by sb_auto) hI9 hx
  · exact sik_fin (fun _ => by sb_auto) hI9 hx


end

end Fl4Proofs.P3.SInvB
