/-
P3 (DESIGN.md §9), invariant line G1 (rd8d): **`receive_ipc`'s sender arm with
donation** (spec side only, outside the JAtZ cone; KENTRY-PLAN rd8c handoff 1).

After the dequeue of a send-blocked sender, `do_ipc_transfer` (TV: every TCB
keeps state, fault, SC) and the sporadic unblock check (`sf_ifCond`: it writes
one SC's refills, keeping `scTcb`, the action and every TCB), the sender is
still `BlockedOnSend`; its fault is read there. When `reply_push` donates
(`senderSc ≠ none ∧ ¬ timeout fault`) or the sender is woken (`fault = none`),
the sender is `BlkR` at that state, so R3 makes it `RdyT`: the donated SC is
released (rd8c's `rd_schedContextDonate_rel` through `rd_replyPush_d`), and
`possible_switch_to sender` enqueues an `RdyT` thread. A sender holding a
timeout fault (R3-exempt) never donates (the spec's guard) and is never woken
here (`fault ≠ none` takes the call arm).

* `fwd_upd`, `sf_ruc`, **`sf_ifCond`**: `Simple`, `ScFwd` and every TCB kept
  across `if_cond_refill_unblock_check`.
* **`rd_recvSender`**.
-/
import Fl4Proofs.P3.SpecInvRd8dA
import Fl4Proofs.P3.SpecInvRd8dT
open Classical

namespace Fl4Proofs.P3.SInvR.B8d
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvR Fl4Proofs.P3.SInvR.B8 Fl4Proofs.P3.SInvR.B8c

noncomputable section

set_option maxHeartbeats 1000000

/-- `ScFwd` across a write of an SC keeping its TCB. -/
theorem fwd_upd {σ σ' : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat} (hF : SInvB.ScFwd σ)
    (hk : σ.kheap p = some (.schedContext y n)) (e1 : z.scTcb = y.scTcb)
    (hkq : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q) (hkp : σ'.kheap p = some (.schedContext z n)) :
    SInvB.ScFwd σ' := by
  intro q y' m u hy hu
  have hfw : ∀ y0 m0, σ.kheap q = some (.schedContext y0 m0) → y0.scTcb = some u →
      ∃ x0, σ'.kheap u = some (.tcb x0) ∧ x0.tcbSchedContext = some q := by
    intro y0 m0 hy0 hu0
    obtain ⟨x0, hx0, hc0⟩ := hF q y0 m0 u hy0 hu0
    have hun : u ≠ p := fun e => by rw [e, hk] at hx0; cases hx0
    exact ⟨x0, by rw [hkq u hun]; exact hx0, hc0⟩
  by_cases e : q = p
  · subst e
    rw [hkp] at hy; cases hy
    exact hfw y n hk (by rw [← e1]; exact hu)
  · rw [hkq q e] at hy
    exact hfw y' m hy hu

/-- What the unblock check keeps for the donation. -/
def SF (σ σ' : State Unit) : Prop :=
  (SInvQ.Simple σ → SInvQ.Simple σ') ∧ (SInvB.ScFwd σ → SInvB.ScFwd σ') ∧
    ∀ q x, σ.kheap q = some (.tcb x) → σ'.kheap q = some (.tcb x)

theorem SF.refl (σ : State Unit) : SF σ σ := ⟨id, id, fun _ _ h => h⟩

theorem sf_ruc {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p σ).1) : SF σ r.2 := by
  rcases ruc_out hk (ruc_ne hk hr) hr with e | ⟨-, z, e, -, -, ez, -⟩
  · rw [e]; exact SF.refl σ
  · rw [e]
    have hkq : ∀ q, q ≠ p → (Sched.updSc { σ with reprogramTimer := true } p z n).kheap q = σ.kheap q :=
      fun q hq => by simp [Notif.updK, hq]
    have hkp : (Sched.updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) :=
      kh_upd _ _ _ _
    refine ⟨fun hA => hA, fun hF => fwd_upd hF hk ez hkq hkp, fun q x hx => ?_⟩
    have hq : q ≠ p := fun e => by rw [e, hk] at hx; cases hx
    rw [hkq q hq]; exact hx

/-- **`if_cond_refill_unblock_check`** keeps `Simple`, `ScFwd` and every TCB. -/
theorem sf_ifCond (scOpt : Option ObjRef) (a b : Option Bool) (σ : State Unit)
    {r : Unit × State Unit} (hr : r ∈ (ifCondRefillUnblockCheck (Z := Unit) scOpt a b σ).1) : SF σ r.2 := by
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hr
  cases scOpt with
  | none =>
    obtain rfl : r = ((), σ) := hr
    exact SF.refl σ
  | some p =>
    dsimp only at hr
    obtain ⟨w, hw, hr⟩ := hr
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hr
    subst w2
    rw [Notif.nd_gets_bind, Notif.nd_pure_bind'] at hr
    unfold NonDet.when at hr
    split_ifs at hr
    · exact sf_ruc hk hr
    all_goals (obtain rfl : r = ((), _) := hr; exact SF.refl _)

/-- **`receive_ipc`'s sender arm** from the dequeue state `s` (the sender a TCB
`BlockedOnSend` there): `Rdy` kept, with any donation. -/
theorem rd_recvSender (sender thread epptr e : ObjRef) (reply : Option ObjRef) (data : SenderPayload)
    (s : State Unit) (hs : Rdy s) (h1 : SInvQ.T1 s) (hA : SInvQ.Simple s) (hF : SInvB.ScFwd s)
    {x : Tcb} (hx : s.kheap sender = some (.tcb x)) (hxs : x.tcbState = .blockedOnSend e data)
    (y : Unit × State Unit)
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
        possibleSwitchTo (Z := Unit) sender) s).1) : Rdy y.2 := by
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer sender (some epptr) _ _ thread s hs z3 h3
  have q3 : SInvQ.T1 z3.2 := SInvQ.q1_doIpcTransfer sender (some epptr) _ _ thread s h1 z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' sender (some epptr) _ _ thread s z3 h3
  have t3 : TV (TVv s) z3.2 := tv_doIpcTransfer sender (some epptr) _ _ thread s rfl z3 h3
  -- the sender is still a TCB BlockedOnSend after the transfer
  have hx3 : ∃ x3, z3.2.kheap sender = some (.tcb x3) ∧ x3.tcbState = .blockedOnSend e data := by
    have ev := congrFun t3 sender
    unfold TVv at ev
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
  have f5 := sf_ifCond x4.tcbSchedContext (some false) (some true) z3.2 h5
  have q5 : SInvQ.T1 z5.2 := SInvQ.q1_ifCondRefillUnblockCheck _ _ _ z3.2 q3 z5 h5
  have hA5 := f5.1 (simple_svs hA v3)
  have hF5 := f5.2.1 (fwd_svs hF v3)
  have hx5 := f5.2.2 sender x3 hx3
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, hx6, rfl⟩ := SInvQ.q1_mem_threadGet h6
  rw [hx5] at hx6
  cases hx6
  dsimp only at hy
  -- the sender is BlkR at z5 unless it holds a timeout fault
  have hRT : (∀ b, x3.tcbFault ≠ some (.timeout b)) → RT z5.2 sender := fun hnt x' c hx' hc => by
    rw [hx5] at hx'; cases hx'
    exact e5.2.2.1 sender x3 c hx5 (Or.inr (Or.inl ⟨e, data, hxs3, hnt⟩)) hc
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      obtain ⟨x7, hx7, rfl⟩ := SInvQ.q1_mem_threadGet h7
      obtain ⟨z8, h8, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 h8
      dsimp only at hy
      refine (rd_replyPush_d sender thread _ _ z5.2 e5 q5 hA5 hF5 (fun hd => hRT fun b hb => ?_) hy).1
      have hd' := of_decide_eq_true hd
      apply hd'.2
      rw [hb]; rfl
    · exact rd_setThreadState sender .inactive trivial z5.2 e5 y hy
  · rename_i hn
    have hf : x3.tcbFault = none := by
      by_contra hc; exact hn (Or.inr hc)
    obtain ⟨z7, h7, hy⟩ := hy
    have e7 : Rdy z7.2 := rd_setThreadState sender .running trivial z5.2 e5 z7 h7
    have v7 : SVK.SVS z5.2 z7.2 := SVK.sv_setThreadState' sender .running z5.2 z7 h7
    have hT7 := rT_svs (hRT fun b hb => by rw [hf] at hb; cases hb) v7
    exact rd_possibleSwitchTo_q sender z7.2 hT7 e7 y hy

end

end Fl4Proofs.P3.SInvR.B8d
