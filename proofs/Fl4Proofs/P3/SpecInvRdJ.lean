/-
P3 (DESIGN.md §9), invariant line G1 (INV-PLAN §4, rd6): **`handle_timeout`:
the timeout fault and the non-donating send** (spec side only, outside the
`JAtZ` cone; KENTRY-PLAN rd5 handoff 2, end_timeslice's timeout arm).

* `ruc_ne`: an outcome of `refill_unblock_check p` reads `p`'s refills non-empty.
* **`rd_refillUnblockCheck`** / **`rd_ifCond`**: `refill_unblock_check` (and
  every `if_cond_refill_unblock_check` guard) keeps `Rdy`, keeps every `RdyT`
  thread `RdyT` and writes no TCB: when it changes the SC, the head is at the
  current time (ready), the refill max and period are kept (`ruc_out` records
  `period ≠ 0`: round robin is skipped), the sum is kept and the head amount
  does not drop (`UI`), so `rdy_frame1` applies without `Excl`.
* `rdyT_svs`: `RdyT` along SVK's `SVS` (bindings, SC refills / max, time).
* `rd_possibleSwitchTo_q`: `possible_switch_to t` with `t` `RdyT` if bound
  (an unbound `t` is not enqueued).
* `rd_threadSet_tmo`: setting a timeout fault keeps `Rdy` (a `BlkR` state with
  a timeout fault is a notification or receive wait, `BlkR` before).
* `rd_sendIpcBlocked_tmo`: the sender, holding a timeout fault, blocks on send:
  exempt from `R3` (l4v `released_ipc_queues`' timeout-fault exemption).
* `rd_replyPush_nd` / `sv_replyPush_nd`: `reply_push` without donation.
* **`rd_sendArm_nd`**: the transfer to a waiting receiver with `canDonate =
  false`: the receiver was `BlkR` at the dequeue state, so `RdyT` if bound
  (`R3`); `SVS` carries it to the unblock check (`rd_ifCond`), and
  `possible_switch_to` enqueues an `RdyT` thread.
* **`rd_sendIpc_nd`**, **`rd_handleTimeout_p`**: `send_ipc` with
  `canDonate = false` from a state where the sender holds a timeout fault, and
  `handle_timeout t (timeout b)` from any `Rdy` state. This discharges
  `rd_endTimeslice_p`'s `hTO` (`rd_endTimeslice`, `rd_cbTail'`).
-/
import Fl4Proofs.P3.SpecInvRdI
open Classical

namespace Fl4Proofs.P3.SInvR
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.Notif Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The sporadic unblock check -/

theorem ruc_ne {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p σ).1) : y.scRefills ≠ [] := by
  intro hne
  unfold refillUnblockCheck at hr
  rw [nd_bind_one (isRoundRobin_eq hk)] at hr
  beta_reduce at hr
  obtain ⟨w, hw, -⟩ := hr
  have e : readScRefillReady (Z := Unit) p σ = none := by
    show Option.bind (readRefillHead p σ) (fun h => Option.bind (Lookup.asks (fun s : State Unit => s.curTime) σ)
      (fun ct => Lookup.oreturn (refillReady ct h) σ)) = _
    rw [readRefillHead_nil hk hne]; rfl
  change w ∈ (NonDet.assertOpt (readScRefillReady (Z := Unit) p σ) σ).1 at hw
  rw [e] at hw; exact hw

/-- What the unblock checks keep. -/
def UK (σ σ' : State Unit) : Prop :=
  Rdy σ' ∧ (∀ t, RdyT σ t → RdyT σ' t) ∧ (∀ q x, σ'.kheap q = some (.tcb x) → σ.kheap q = some (.tcb x))

theorem uk_refl {σ : State Unit} (h : Rdy σ) : UK σ σ := ⟨h, fun _ h => h, fun _ _ h => h⟩

/-- **`refill_unblock_check`** (module docstring). -/
theorem rd_refillUnblockCheck {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat} (h : Rdy σ)
    (hk : σ.kheap p = some (.schedContext y n)) {r : Unit × State Unit}
    (hr : r ∈ (refillUnblockCheck (Z := Unit) p σ).1) : UK σ r.2 := by
  have hne := ruc_ne hk hr
  rcases ruc_out hk hne hr with e | ⟨hp0, z, e, hz1, hz2, hz3, hz4, hz5, hz6, hz9⟩
  · rw [e]; exact uk_refl h
  · rw [e]
    have h1 : Rdy ({ σ with reprogramTimer := true } : State Unit) := rdy_congr h rfl rfl rfl rfl rfl fun _ h => h
    have hk1 : ({ σ with reprogramTimer := true } : State Unit).kheap p = some (.schedContext y n) := hk
    have hkq : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z n).kheap q =
        ({ σ with reprogramTimer := true } : State Unit).kheap q := fun q hq => by simp [Notif.updK, hq]
    have hkp : (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) := kh_upd _ _ _ _
    have hay : scActive z = scActive y := by simp only [scActive, hz4]
    have hrdz : refillReady σ.curTime (refillHd z) = true := ready_of_nat (by rw [hz2]; try exact le_refl _)
    have hp : ∀ y0 n0, ({ σ with reprogramTimer := true } : State Unit).kheap p = some (.schedContext y0 n0) →
        scActive y0 = true → refillReady σ.curTime (refillHd y0) = true →
        ∃ z0, (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z0 n0) ∧
          scActive z0 = true ∧ refillReady σ.curTime (refillHd z0) = true := by
      intro y0 n0 hy0 ha0 _
      rw [hk1] at hy0; cases hy0
      exact ⟨z, hkp, by rw [hay]; exact ha0, hrdz⟩
    have hpt : ∀ x, ({ σ with reprogramTimer := true } : State Unit).kheap p ≠ some (.tcb x) :=
      fun x hx => by rw [hk1] at hx; cases hx
    refine ⟨rdy_frame1 h1 hkq rfl rfl rfl hp hpt (fun x hx => by rw [hkp] at hx; cases hx)
      (fun z0 m hz0 ha0 => ?_) rfl
      (fun y0 n0 hy0 ha0 => ⟨z, n, hkp, by rw [hk1] at hy0; cases hy0; rw [hay]; exact ha0⟩) rfl
      (fun _ z0 m hz0 => ?_), fun t ht => rdyT_frame hkq rfl hp hpt (rdy_congr_t ht), fun q x hx => ?_⟩
    · rw [hkp] at hz0; cases hz0
      rw [hay] at ha0
      obtain ⟨v1, v2, v3, -⟩ := h.2.2.2.1 p y n hk ha0
      obtain ⟨w1, w2⟩ := hz9 v3
      exact ⟨by rw [hz4]; exact v1, by rw [BitVec.le_def] at v2 ⊢; omega, by rw [w1]; exact v3,
        fun h0 => absurd (by rw [← hz6]; exact h0) hp0⟩
    · rw [hkp] at hz0; cases hz0
      exact ⟨hz1, by rw [hz2]; try exact le_refl _⟩
    · by_cases e : q = p
      · subst e; rw [hkp] at hx; cases hx
      · rw [hkq q e] at hx; exact hx
where
  rdy_congr_t {t : ObjRef} (ht : RdyT σ t) : RdyT ({ σ with reprogramTimer := true } : State Unit) t := ht

/-- **`if_cond_refill_unblock_check`** under any guard (module docstring). -/
theorem rd_ifCond (scOpt : Option ObjRef) (a b : Option Bool) (σ : State Unit) (h : Rdy σ)
    {r : Unit × State Unit} (hr : r ∈ (ifCondRefillUnblockCheck (Z := Unit) scOpt a b σ).1) : UK σ r.2 := by
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hr
  cases scOpt with
  | none =>
    obtain rfl : r = ((), σ) := hr
    exact uk_refl h
  | some p =>
    dsimp only at hr
    obtain ⟨w, hw, hr⟩ := hr
    obtain ⟨⟨n, hk⟩, e1⟩ := SInvI.mem_getSchedContext_vi hw
    obtain ⟨w1, w2⟩ := w
    simp only at e1 hk hr
    subst w2
    rw [nd_gets_bind, nd_pure_bind'] at hr
    unfold NonDet.when at hr
    split_ifs at hr
    · exact rd_refillUnblockCheck h hk hr
    all_goals (obtain rfl : r = ((), _) := hr; exact uk_refl h)

/-! ## The view carry and `possible_switch_to` -/

theorem rdyT_svs {σ σ' : State Unit} {t : ObjRef} (h : RdyT σ t) (hS : SVK.SVS σ σ') : RdyT σ' t := by
  obtain ⟨x, c, y, n, hx, hc, hy, h1, h2⟩ := h
  have e1 := hS.1 t; rw [hx] at e1
  obtain ⟨x', hx', hxs⟩ := SVK.sv_tcb (o := σ'.kheap t) e1
  have e2 := hS.1 c; rw [hy] at e2
  obtain ⟨y', hy', hr, hm, -⟩ := SVK.sv_sc (o := σ'.kheap c) e2
  refine ⟨x', c, y', n, hx', hxs.trans hc, hy', ?_, ?_⟩
  · show activeSc y'.scRefillMax = true
    rw [hm]; exact h1
  · rw [hS.2.1]; unfold refillHd; rw [hr]; exact h2

/-- **`possible_switch_to t`**, `t` `RdyT` when bound. -/
theorem rd_possibleSwitchTo_q (t : ObjRef) (σ : State Unit)
    (hR : ∀ x c, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some c → RdyT σ t) :
    IKp Rdy σ (possibleSwitchTo (Z := Unit) t) := by
  by_cases hb : ∃ x c, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some c
  · obtain ⟨x, c, hx, hc⟩ := hb
    exact rd_possibleSwitchTo_p t σ (hR x c hx hc)
  · unfold possibleSwitchTo getTcbObjRef
    refine SInvQ.ikp_threadGet_bind fun x hx => ?_
    refine ikp_gets_bind ?_
    refine SInvQ.ikp_when _ fun hc => ?_
    obtain ⟨c, hc'⟩ := Option.ne_none_iff_exists'.mp hc.1
    exact absurd ⟨x, c, hx, hc'⟩ hb

/-! ## The timeout fault, the blocked send, the reply push -/

theorem blk_tmo {ts : ThreadState} {b : Data} {f : Option Fault} (h : BlkR ts (some (.timeout b))) : BlkR ts f := by
  rcases h with h | ⟨e, d, _, hf⟩ | h
  · exact Or.inl h
  · exact absurd rfl (hf b)
  · exact Or.inr (Or.inr h)

/-- Setting a timeout fault keeps `Rdy`. -/
theorem rd_threadSet_tmo (b : Data) (t : ObjRef) :
    IK Rdy (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some (.timeout b) }) t) := by
  unfold threadSet
  refine ik_getsThe_bind fun x σ hx => rd_setObject_p _ _ σ ?_
  rw [getTcb_kheap hx]
  refine ⟨fun x0 e => ?_, fun x' e hb _ => ?_, rfl⟩
  · cases e; exact ⟨_, rfl, rfl⟩
  · cases e; exact ⟨x, rfl, rfl, blk_tmo hb⟩

/-- After setting the fault, the thread holds a timeout fault. -/
theorem tmo_threadSet {b : Data} {t : ObjRef} {σ : State Unit} {z : Unit × State Unit}
    (hz : z ∈ (threadSet (Z := Unit) (fun tcb => { tcb with tcbFault := some (.timeout b) }) t σ).1) :
    ∀ x, z.2.kheap t = some (.tcb x) → ∃ b', x.tcbFault = some (.timeout b') := by
  intro x hx
  cases e : σ.kheap t with
  | none =>
    exfalso
    unfold threadSet NonDet.getsThe at hz
    obtain ⟨w, hw, -⟩ := hz
    have : getTcb t σ = none := by unfold getTcb readObject; simp [e]
    change w ∈ (NonDet.assertOpt (getTcb t σ) σ).1 at hw
    rw [this] at hw; exact hw
  | some o =>
    cases o with
    | tcb x0 =>
      rw [threadSet_eq _ e] at hz
      obtain rfl := Set.mem_singleton_iff.1 hz
      have : (updK σ t (.tcb { x0 with tcbFault := some (.timeout b) })).kheap t =
          some (.tcb { x0 with tcbFault := some (.timeout b) }) := by simp [updK]
      rw [this] at hx; cases hx
      exact ⟨b, rfl⟩
    | _ =>
      exfalso
      unfold threadSet NonDet.getsThe at hz
      obtain ⟨w, hw, -⟩ := hz
      have : getTcb t σ = none := by unfold getTcb readObject; simp [e]
      change w ∈ (NonDet.assertOpt (getTcb t σ) σ).1 at hw
      rw [this] at hw; exact hw

/-- **Blocking on send with a timeout fault** (module docstring). -/
theorem rd_setThreadState_tmo (t : ObjRef) (e : ObjRef) (d : SenderPayload) (σ : State Unit)
    (hf : ∀ x, σ.kheap t = some (.tcb x) → ∃ b, x.tcbFault = some (.timeout b)) :
    IKp Rdy σ (setThreadState (Z := Unit) t (.blockedOnSend e d)) := by
  unfold setThreadState
  refine ikp_bind ?_ fun _ => rd_setThreadStateAct t
  unfold threadSet
  intro hσ r ⟨z, hz, hr⟩
  unfold NonDet.getsThe at hz
  cases eg : getTcb t σ with
  | none => rw [eg] at hz; exact hz.elim
  | some x =>
    rw [eg] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    obtain ⟨b, hb⟩ := hf x (getTcb_kheap eg)
    refine rd_setObject_p _ _ σ ?_ hσ r hr
    rw [getTcb_kheap eg]
    refine ⟨fun x0 e0 => ?_, fun x' e0 hB _ => ?_, rfl⟩
    · cases e0; exact ⟨_, rfl, rfl⟩
    · cases e0
      exfalso
      rcases hB with ⟨_, h⟩ | ⟨_, _, h, hn⟩ | ⟨_, _, _, h⟩
      · cases h
      · exact hn b hb
      · cases h

theorem rd_sendIpcBlocked_tmo (t ep : ObjRef) (badge : Badge) (cg cgr call : Bool) (σ : State Unit)
    (hf : ∀ x, σ.kheap t = some (.tcb x) → ∃ b, x.tcbFault = some (.timeout b)) :
    IKp Rdy σ (sendIpcBlocked (Z := Unit) t ep badge cg cgr call) := by
  unfold sendIpcBlocked
  exact ikp_bind (rd_setThreadState_tmo t ep _ σ hf) fun _ => rd_tcbEpAppend _ _ _

theorem rd_replyUnlinkTcb (t r : ObjRef) : IK Rdy (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; rd_auto

theorem rd_replyPush_nd (caller callee r : ObjRef) : IK Rdy (replyPush (Z := Unit) caller callee r false) := by
  unfold replyPush
  simp only [Bool.false_eq_true, and_false, NonDet.when, ↓reduceIte]
  rd_auto

theorem sv_replyPush_nd (caller callee r : ObjRef) : SVK.SVM (replyPush (Z := Unit) caller callee r false) := by
  unfold replyPush
  simp only [Bool.false_eq_true, and_false, NonDet.when, ↓reduceIte]
  sv_auto

/-! ## The send -/

/-- **The transfer to a waiting receiver, no donation** (module docstring). -/
theorem rd_sendArm_nd (call : Bool) (badge : Badge) (cg cgr cd : Bool) (hcd : cd = false) (thread epptr dest : ObjRef)
    (reply : Option ObjRef) (s : State Unit) (hs : Rdy s) {x : Tcb} (hx : s.kheap dest = some (.tcb x))
    (hRT : ∀ c, x.tcbSchedContext = some c → RdyT s dest) (y : Unit × State Unit)
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
  subst hcd
  obtain ⟨z3, h3, hy⟩ := hy
  have e3 : Rdy z3.2 := rd_doIpcTransfer thread (some epptr) badge cg dest s hs z3 h3
  have v3 : SVK.SVS s z3.2 := SVK.sv_doIpcTransfer' thread (some epptr) badge cg dest s z3 h3
  obtain ⟨z4, h4, hy⟩ := hy
  have e4 : Rdy z4.2 := (ik_maybeM (fun r => rd_replyUnlinkTcb dest r) reply) z3.2 e3 z4 h4
  have v4 : SVK.SVS s z4.2 :=
    v3.trans (SVK.sv_maybeM (fun r => SVK.sv_replyUnlinkTcb dest r) reply z3.2 z4 h4)
  obtain ⟨z5, h5, hy⟩ := hy
  obtain ⟨x5, -, rfl⟩ := SInvQ.q1_mem_threadGet h5
  obtain ⟨z6, h6, hy⟩ := hy
  obtain ⟨x6, -, rfl⟩ := SInvQ.q1_mem_threadGet h6
  dsimp only at hy
  have hw : ∀ s7 : State Unit, Rdy s7 → SVK.SVS s s7 → ∀ y' : Unit × State Unit,
      y' ∈ ((do
        setThreadState (Z := Unit) dest .running
        let destSc ← getTcbObjRef (Z := Unit) Tcb.tcbSchedContext dest
        ifSporadicCurScTestRefillUnblockCheck (Z := Unit) destSc
        possibleSwitchTo (Z := Unit) dest) s7).1 → Rdy y'.2 := by
    intro s7 e7 v7 y' hy'
    obtain ⟨z8, h8, hy'⟩ := hy'
    have e8 : Rdy z8.2 := rd_setThreadState dest .running trivial s7 e7 z8 h8
    have v8 : SVK.SVS s z8.2 := v7.trans (SVK.sv_setThreadState' dest .running s7 z8 h8)
    obtain ⟨z9, h9, hy'⟩ := hy'
    obtain ⟨x9, -, rfl⟩ := SInvQ.q1_mem_threadGet h9
    obtain ⟨z10, h10, hy'⟩ := hy'
    obtain ⟨e10, r10, k10⟩ := rd_ifCond x9.tcbSchedContext (some false) (some false) z8.2 e8 h10
    refine rd_possibleSwitchTo_q dest z10.2 (fun x' c hx' hc => ?_) e10 y' hy'
    have hx8 := k10 dest x' hx'
    have hsv := v8.1 dest
    rw [hx8, hx] at hsv
    have hb : x.tcbSchedContext = some c := by
      have : x'.tcbSchedContext = x.tcbSchedContext := by simpa [SVK.sv] using hsv
      rw [← this]; exact hc
    exact r10 dest (rdyT_svs (hRT c hb) v8)
  split at hy
  · split at hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact hw z7.2 (rd_replyPush_nd thread dest _ z4.2 e4 z7 h7)
        (v4.trans (sv_replyPush_nd thread dest _ z4.2 z7 h7)) y hy
    · obtain ⟨z7, h7, hy⟩ := hy
      exact hw z7.2 (rd_setThreadState thread .inactive trivial z4.2 e4 z7 h7)
        (v4.trans (SVK.sv_setThreadState' thread .inactive z4.2 z7 h7)) y hy
  · obtain ⟨z7, h7, hy⟩ := hy
    rw [NonDet.when, if_neg (by simp)] at h7
    obtain rfl : z7 = ((), z4.2) := h7
    exact hw z4.2 e4 v4 y hy

/-- **`send_ipc` without donation** from a sender holding a timeout fault. -/
theorem rd_sendIpc_nd (block call : Bool) (badge : Badge) (cg cgr : Bool) (thread epptr : ObjRef) (σ : State Unit)
    (hf : ∀ x, σ.kheap thread = some (.tcb x) → ∃ b, x.tcbFault = some (.timeout b)) :
    IKp Rdy σ (sendIpc (Z := Unit) block call badge cg cgr false thread epptr) := by
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
    · exact rd_sendIpcBlocked_tmo _ _ _ _ _ _ σ hf
  | sendEP q =>
    cases block
    · exact ikp_of_ik (ik_pure _) σ
    · exact rd_sendIpcBlocked_tmo _ _ _ _ _ _ σ hf
  | recvEP q =>
    cases q with
    | nil => cases block <;> exact ikp_of_ik ik_fail σ
    | cons dest q =>
      cases block
      all_goals
        intro h0 y hy
        obtain ⟨⟨z1a, z1⟩, h1, hy⟩ := hy
        have e1 : Rdy z1 := rd_tcbEpDequeue dest epptr σ h0 _ h1
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
          exact rd_sendArm_nd call badge cg cgr false rfl thread epptr dest r z1 e1 hx
            (fun c hc => e1.2.2.1 dest x c hx (Or.inr (Or.inr ⟨e, r, d, hxs⟩)) hc) y hy
        | _ => intro hy; first | exact hy.elim | (obtain ⟨_, h, _⟩ := hy; exact h.elim)

/-- **`handle_timeout t (timeout b)`** keeps `Rdy`. -/
theorem rd_handleTimeout_p (t : ObjRef) (b : Data) (σ : State Unit) :
    IKp Rdy σ (handleTimeout (Z := Unit) t (.timeout b)) := by
  unfold handleTimeout
  refine ikp_keep (fun y hy => SInvQ.cq5_ro (fun _ => by unfold isValidTimeoutHandler; repeat' (first | ik_step0 | ik_unfold)) hy) fun v => ?_
  refine ikp_keep (fun y hy => SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun _ => ?_
  refine ikp_pure_bind ?_
  refine ikp_keep (fun y hy => SInvQ.cq5_ro (fun _ => by repeat' (first | ik_step0 | ik_unfold)) hy) fun cap => ?_
  refine ikp_bind ?_ fun _ => ik_pure _
  unfold sendFaultIpc
  split
  · intro hσ y ⟨z, hz, hy⟩
    have e1 : Rdy z.2 := rd_threadSet_tmo b t σ hσ z hz
    have hf := tmo_threadSet hz
    obtain ⟨w, hw, hy⟩ := hy
    have e2 := rd_sendIpc_nd true false _ _ _ t _ z.2 hf e1 w hw
    rw [Set.mem_singleton_iff.1 hy]; exact e2
  · exact ikp_of_ik (ik_pure _) σ
  · exact ikp_of_ik ik_fail σ

/-! ## `end_timeslice`, `charge_budget`'s tail, without `hTO` -/

theorem rd_endTimeslice (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb}
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hF : SInvB.ScFwd s) : IKp Rdy s (endTimeslice (Z := Unit) c) :=
  rd_endTimeslice_p c s hk ha hct hb hF fun b => rd_handleTimeout_p _ b s

theorem rd_cbTail' (c : Bool) (s : State Unit) {z : SchedContext} {n : Nat} {xt : Tcb} (hR : Rdy s)
    (hk : s.kheap s.curSc = some (.schedContext z n)) (ha : scActive z = true)
    (hct : s.kheap s.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some s.curSc)
    (hF : SInvB.ScFwd s) {r : Unit × State Unit} (hr : r ∈ (cbTail c s).1) :
    Rdy r.2 ∧ (schedulable s.curThread s = true → r.2.schedulerAction = .chooseNewThread) :=
  rd_cbTail c s hR hk ha hct hb hF (fun b => rd_handleTimeout_p _ b s) hr

/-! ## `charge_budget` -/

/-- `ScFwd` across `charge_budget`'s charge (the SC keeps its bound TCB). -/
theorem fwd_chargeOut {σ : State Unit} {x : SchedContext} {n : Nat} (hF : SInvB.ScFwd σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) {z : SchedContext} (e1 : z.scTcb = x.scTcb) :
    SInvB.ScFwd ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit) := by
  have hkq : ∀ q, q ≠ σ.curSc → ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit).kheap q =
      σ.kheap q := fun q hq => by simp [Notif.updK, hq]
  have hkp : ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit).kheap σ.curSc =
      some (.schedContext z n) := kh_upd _ _ _ _
  intro p y m u hy hu
  have hfw : ∀ y0 m0, σ.kheap p = some (.schedContext y0 m0) → y0.scTcb = some u →
      ∃ x0, ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit).kheap u = some (.tcb x0) ∧
        x0.tcbSchedContext = some p := by
    intro y0 m0 hy0 hu0
    obtain ⟨x0, hx0, hc0⟩ := hF p y0 m0 u hy0 hu0
    have hun : u ≠ σ.curSc := fun e => by rw [e, hk] at hx0; cases hx0
    exact ⟨x0, by rw [hkq u hun]; exact hx0, hc0⟩
  by_cases e : p = σ.curSc
  · subst e
    rw [hkp] at hy; cases hy
    exact hfw x n hk (by rw [← e1]; exact hu)
  · rw [hkq p e] at hy
    exact hfw y m hy hu

/-- **`charge_budget`** (charge and tail) from facts at its start: `Rdy`, the
current SC an active SC with refills (`Excl` when sporadic and not idle), the
current thread a TCB bound to it (ctq5's `kentry_curScT`), sb2's `ScFwd`.
Afterwards `Rdy`, and when the tail ran (`schedulable ct` after the charge)
the action is `choose_new_thread`. -/
theorem rd_chargeBudget {σ : State Unit} {x : SchedContext} {n : Nat} {xt : Tcb} (h : Rdy σ)
    (hk : σ.kheap σ.curSc = some (.schedContext x n)) (ha : scActive x = true) (hne : x.scRefills ≠ [])
    (hX : σ.curSc ≠ σ.idleSc → x.scPeriod ≠ 0 → Excl σ σ.curSc)
    (hct : σ.kheap σ.curThread = some (.tcb xt)) (hb : xt.tcbSchedContext = some σ.curSc)
    (hF : SInvB.ScFwd σ) (u : Ticks) (c : Bool) {r : Unit × State Unit}
    (hr : r ∈ (chargeBudget (Z := Unit) u c σ).1) :
    Rdy r.2 ∧ ∃ s1, ChargeOut σ x n s1 ∧
      (schedulable s1.curThread s1 = true → r.2.schedulerAction = .chooseNewThread) := by
  obtain ⟨s1, hR1, hO, hr⟩ := rd_chargeBudget_head h hk (fun hi => ⟨ha, hne, hX hi⟩) u c hr
  obtain ⟨z, e, e1, e2, e3, e4, e5, e6⟩ := hO
  subst e
  have hk1 : ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit).kheap σ.curSc =
      some (.schedContext z n) := kh_upd _ _ _ _
  have ha1 : scActive z = true := by simp only [scActive, e2]; exact ha
  have hcs : σ.curThread ≠ σ.curSc := fun e => by rw [e, hk] at hct; cases hct
  have hct1 : ({ updSc σ σ.curSc z n with consumedTime := 0 } : State Unit).kheap σ.curThread =
      some (.tcb xt) := by simp [Notif.updK, hcs, hct]
  obtain ⟨hR, hA⟩ := rd_cbTail' c _ hR1 hk1 ha1 hct1 hb (fwd_chargeOut hF hk e1) hr
  exact ⟨hR, _, ⟨z, rfl, e1, e2, e3, e4, e5, e6⟩, hA⟩

end

end Fl4Proofs.P3.SInvR
