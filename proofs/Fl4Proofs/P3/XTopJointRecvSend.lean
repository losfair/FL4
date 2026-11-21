/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` from a waiting sender at `J`**
(XTopJointRecvIpcLink's `JRecvSendHyp`, KENTRY-PLAN.md item 6 (d)).

* `unblockHole`: FL4's `unblock_sporadic` of a thread at a state that is
  only `IRel` (the sender dequeued but not yet woken: no `JAtZ` holds there)
  against the spec's `specSporadicAssert`, with its footprint `KFoot`, P1's
  invariants for any hole set `X` and P1's footprint, and the spec's
  outcome explicitly (unchanged, or the sender's SC `p ≠ curSc` refilled with
  `reprogramTimer` set: ScInvU's `unblock_result`).
* `receiveIpc_send_eqB`, `receiveIpc_sendCall_eq` (spec), `receive_ipc_preN`
  (FL4): the receive's prefix with a bound notification that is not active,
  polling or not lending its SC (`maybe_return_sc` a no-op on both sides).
* `JAtZ.recvSendJ0`: the receive from the head sender of an endpoint, the
  sender not faulted and either not calling (`Running`, then
  `possible_switch_to`) or calling without a reply pushed (neither grant
  right or no reply cap: `Inactive`), the receiver with no bound notification
  or one as above: FL4's dequeue, transfer (XTopJointXferG's `xferStepGJ`,
  sender to receiver, any grant), `unblockHole`, the sender `Running` on
  `IRel`; the spec frame IpcRecvSendFr's `RSFr` from the transfer's base
  `σy`; `Inv` at the end by `InvBut.ik` at the state without the SC refill
  and `Inv.scRef` across it; back to `JAtZ` by `JAtZ.bufRebaseX` and
  XTopJointRecvSendStep's `JAtZ.rsfrStep`; then `JAtZ.sendSwitchJ` for
  `possible_switch_to`; the spec's outcome EpRecvSend's `receiveIpc_send_eq`.
-/
import Fl4Proofs.P3.XTopJointRecvSendStep
import Fl4Proofs.P3.XTopJointSendRecv
import Fl4Proofs.P3.EpRecvSend
import Fl4Proofs.P3.XTopJointRecvIpc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecC
open Fl4Spec

theorem flags_grantReply (d : SenderPayload) :
    ((Endp.flagsOf d &&& endpoint.FLAG_GRANT_REPLY) != 0#u64) = d.senderCanGrantReply := by
  unfold Endp.flagsOf endpoint.FLAG_GRANT_REPLY
  cases d.senderCanGrant <;> cases d.senderCanGrantReply <;> cases d.senderIsCall <;> decide

/-- The spec's `receive_ipc` from a waiting sender `sd` calling or faulted
(after the transfer, `hcf`) without a reply pushed (neither grant right, or no reply cap),
the receiver's bound notification as in `receiveIpc_send_eqB`: the sender
`Inactive`. -/
theorem receiveIpc_sendCall_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt))
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hno : ¬ ((dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ reply ≠ none)) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hcf : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ =
      ({((), stsAct (updK σ3 sd (.tcb { xs3 with tcbState := .inactive })) sd)}, False) := by
  have hks1 : (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))).kheap sd = some (.tcb xs) := by
    simp [hse, hks]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    rcases hbN with hb | ⟨n, xn, hb, hkn, hna, hnr⟩
    on_goal 1 =>
      simp only [hb]
      rw [nd_pure_bind']
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [nd_when_false_bind (by simp [hb])]
    on_goal 2 =>
      have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
          (NonDet.when (xt.tcbBoundNotification ≠ none ∧ blk = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ =
            f () σ := by
        intro f
        cases blk with
        | false => exact nd_when_false_bind (by simp) _ _ _
        | true =>
          unfold NonDet.when
          rw [if_pos (by simp [hb]), show the (some n) = n from rfl,
            nd_bind_one (Ipc.maybeReturnSc_noop hkn hkt (hnr rfl))]
      simp only [hb]
      rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals
      rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
      rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
        nd_bind_one (getThreadState_eq hks1), hst]
      dsimp only
      rw [nd_pure_bind', nd_bind_one hT, Endp.nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3)]
      rw [if_pos hcf, if_neg (by simp)]
      rw [Notif.setThreadState_eq _ hks3]
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    rcases hbN with hb | ⟨n, xn, hb, hkn, hna, hnr⟩
    on_goal 1 =>
      simp only [hb]
      rw [nd_pure_bind']
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [nd_when_false_bind (by simp [hb])]
    on_goal 2 =>
      have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
          (NonDet.when (xt.tcbBoundNotification ≠ none ∧ blk = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ =
            f () σ := by
        intro f
        cases blk with
        | false => exact nd_when_false_bind (by simp) _ _ _
        | true =>
          unfold NonDet.when
          rw [if_pos (by simp [hb]), show the (some n) = n from rfl,
            nd_bind_one (Ipc.maybeReturnSc_noop hkn hkt (hnr rfl))]
      simp only [hb]
      rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals
      rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
      rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
        nd_bind_one (getThreadState_eq hks1), hst]
      dsimp only
      rw [nd_pure_bind', nd_bind_one hT, Endp.nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3)]
      rw [if_pos hcf, if_neg hno]
      rw [Notif.setThreadState_eq _ hks3]

/-- EpRecvSend's `receiveIpc_send_eq` (a non-calling sender without a
fault: `Running`, then `possible_switch_to`) with a bound notification that
is not active, the receive polling or the notification not lending its SC to
the thread (`maybe_return_sc` a no-op). -/
theorem receiveIpc_send_eqB {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt))
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hcall : dd.senderIsCall = false) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hf3 : xs3.tcbFault = none) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ =
      possibleSwitchTo sd (stsAct (updK σ3 sd (.tcb { xs3 with tcbState := .running })) sd) := by
  have hks1 : (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))).kheap sd = some (.tcb xs) := by
    simp [hse, hks]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    rcases hbN with hb | ⟨n, xn, hb, hkn, hna, hnr⟩
    on_goal 1 =>
      simp only [hb]
      rw [nd_pure_bind']
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [nd_when_false_bind (by simp [hb])]
    on_goal 2 =>
      have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
          (NonDet.when (xt.tcbBoundNotification ≠ none ∧ blk = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ =
            f () σ := by
        intro f
        cases blk with
        | false => exact nd_when_false_bind (by simp) _ _ _
        | true =>
          unfold NonDet.when
          rw [if_pos (by simp [hb]), show the (some n) = n from rfl,
            nd_bind_one (Ipc.maybeReturnSc_noop hkn hkt (hnr rfl))]
      simp only [hb]
      rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals
      rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
      rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
        nd_bind_one (getThreadState_eq hks1), hst]
      dsimp only
      rw [nd_pure_bind', nd_bind_one hT, Endp.nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3), hf3, hcall]
      simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
      rw [nd_bind_one (Notif.setThreadState_eq _ hks3), hf3]
  · dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr)]
    simp only [hr]
    rw [nd_when_false_bind (by simp [hr])]
    rw [nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt)]
    rcases hbN with hb | ⟨n, xn, hb, hkn, hna, hnr⟩
    on_goal 1 =>
      simp only [hb]
      rw [nd_pure_bind']
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      rw [nd_when_false_bind (by simp [hb])]
    on_goal 2 =>
      have tail : ∀ (f : Unit → NonDet (State Unit) Unit),
          (NonDet.when (xt.tcbBoundNotification ≠ none ∧ blk = true) (maybeReturnSc (Z := Unit) (the (some n)) t) >>= f) σ =
            f () σ := by
        intro f
        cases blk with
        | false => exact nd_when_false_bind (by simp) _ _ _
        | true =>
          unfold NonDet.when
          rw [if_pos (by simp [hb]), show the (some n) = n from rfl,
            nd_bind_one (Ipc.maybeReturnSc_noop hkn hkt (hnr rfl))]
      simp only [hb]
      rw [nd_bind_one (getNotification_eq hkn), if_neg (by simp [hna]), tail]
    all_goals
      rw [nd_bind_one (assert_true (by simp) σ), nd_pure_bind']
      rw [show the (sd :: q).head? = sd from rfl, nd_bind_one (tcbEpDequeue_eq hk (by simp [Endpoint.epQueue])),
        nd_bind_one (getThreadState_eq hks1), hst]
      dsimp only
      rw [nd_pure_bind', nd_bind_one hT, Endp.nd_bind_assoc, nd_bind_one (show (getTcbObjRef Tcb.tcbSchedContext sd >>= ifSporadicCurScAssertRefillUnblockCheck) σ2 = _ from hA), nd_bind_one (threadGet_eq _ hks3), hf3, hcall]
      simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
      rw [nd_bind_one (Notif.setThreadState_eq _ hks3), hf3]

end SpecC

/-- The sender's wake as `Inactive` in an `RSFr` frame. -/
theorem Sched.RSFr.stsInact {t r : Fl4Spec.ObjRef} {σ : Fl4Spec.State Unit} {y : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb y)) (hrb : KbIn y.tcbState) :
    RSFr t r σ (Notif.stsAct (Notif.updK σ t (.tcb { y with tcbState := .inactive })) t) :=
  (RSFr.upd hk (Or.inl ⟨y, .inactive, y.tcbArch, rfl, rfl, Or.inl rfl, Or.inr ⟨rfl, hrb, Or.inl rfl⟩⟩)).trans
    (RSFr.sts _ _ _ _)

section Hole
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- The spec's outcome of the sporadic check of a thread with TCB `xt`. -/
def UnblockOut (xt : Fl4Spec.Tcb) (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ' = σ ∨ ∃ p y z n, xt.tcbSchedContext = some p ∧ σ.kheap p = some (.schedContext y n) ∧
    y.scRefills ≠ [] ∧ p ≠ σ.curSc ∧ σ' = updSc { σ with reprogramTimer := true } p z n ∧
    (RefOK y → RefOK z) ∧ (Fl4Spec.refillHd z).rTime = σ.curTime ∧ z = { y with scRefills := z.scRefills } ∧
    z.scRefills ≠ [] ∧ y.scPeriod ≠ 0

set_option maxHeartbeats 16000000 in
/-- **`unblock_sporadic` at a hole** (module docstring). -/
theorem unblockHole (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb xt))
    (hne : ∀ p y n, σ.kheap p = some (.schedContext y n) → Fl4Spec.scActive y = true → y.scRefills ≠ [])
    {Hp : P1.Heap} {Cs Ac X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (h : P1.SchedQueuesInvX st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) Hp X s Q Rq)
    (hB : P1.BoundInv st (P1.Heap.tcbs Hp) Ac s)
    (hXi : P1.XInv st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.replies Hp)
      (P1.Heap.scs Hp) (P1.Heap.ntfns Hp) (P1.Heap.scBits Hp) s)
    (hSc : P1.SCsOK st (P1.Heap.tcbs Hp) (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.scs Hp)
      (P1.Heap.scBits Hp) Ac s)
    (hSg : P1.SgOK st (P1.Heap.omega Hp) (P1.Heap.frame Hp) s) (htH : t ∈ P1.Heap.tcbs Hp) :
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ σ', Endp.specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ P1.WritesIn st s s' (KFoot st T N C c s σ) ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) Hp X s' Q Rq ∧
      P1.BoundInv st (P1.Heap.tcbs Hp) Ac s' ∧
      P1.XInv st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.replies Hp)
        (P1.Heap.scs Hp) (P1.Heap.ntfns Hp) (P1.Heap.scBits Hp) s' ∧
      P1.SCsOK st (P1.Heap.tcbs Hp) (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.scs Hp)
        (P1.Heap.scBits Hp) Ac s' ∧
      P1.SgOK st (P1.Heap.omega Hp) (P1.Heap.frame Hp) s' ∧
      (∀ y ∈ P1.Heap.tcbs Hp, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      P1.Foot st (P1.Heap.tcbs Hp) Cs (P1.Heap.frame Hp) (P1.Heap.scs Hp) (P1.Heap.scBits Hp) (P1.EH Hp) s s' ∧
      UnblockOut xt σ σ' ⦄ := by
  have hS := hX.2.2.1
  obtain ⟨Q0, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt', hkt, -, -, hsct, -⟩ := hs.tcb t ht
  rw [hk] at hkt; cases hkt
  have hspec0 : Endp.specSporadicAssert t.bv σ = (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit)
      (optRef (L.mem s (scA t)))) σ := by
    rw [Ipc.specSporadicAssert_eq]
    unfold specUnblock Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hk), hsct]
  have skip : (Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t)))) σ =
      ({((), σ)}, False) → ∃ σ', Endp.specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s σ' ∧ P1.WritesIn st s s (KFoot st T N C c s σ) ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) Hp X s Q Rq ∧
      P1.BoundInv st (P1.Heap.tcbs Hp) Ac s ∧
      P1.XInv st (P1.Heap.tcbs Hp) Cs (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.replies Hp)
        (P1.Heap.scs Hp) (P1.Heap.ntfns Hp) (P1.Heap.scBits Hp) s ∧
      P1.SCsOK st (P1.Heap.tcbs Hp) (P1.Heap.omega Hp) (P1.Heap.frame Hp) (P1.Heap.scs Hp)
        (P1.Heap.scBits Hp) Ac s ∧
      P1.SgOK st (P1.Heap.omega Hp) (P1.Heap.frame Hp) s ∧
      (∀ y ∈ P1.Heap.tcbs Hp, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      P1.Foot st (P1.Heap.tcbs Hp) Cs (P1.Heap.frame Hp) (P1.Heap.scs Hp) (P1.Heap.scBits Hp) (P1.EH Hp) s s ∧
      UnblockOut xt σ σ' :=
    fun h0 => ⟨σ, by rw [hspec0, h0], hX, P1.WritesIn.refl _ _, h, hB, hXi, hSc, hSg, fun _ _ _ _ _ => rfl,
      P1.Foot.refl _, Or.inl rfl⟩
  unfold endpoint.unblock_sporadic
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i2, hi2⟩
  step with sporadic.sc_sporadic.spec' as ⟨b, b_post⟩
  subst hi2
  by_cases h0 : L.mem s (scA t) = 0#u64
  · have hb : b = false := by rw [b_post]; simp [h0]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (skip (by rw [h0, optRef_zero]; rfl))
  have hscC := hs.scMem t ht h0
  obtain ⟨y, n, hky, hy⟩ := hs.scs _ hscC
  have hsp : (y.scSporadic = true) ↔ L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64 := by
    rw [hy.sporadic]; simp
  have hif : Fl4Spec.ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (optRef (L.mem s (scA t))) σ =
      (if y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc then
        Fl4Spec.refillUnblockCheck (L.mem s (scA t)).bv σ else ({((), σ)}, False)) := by
    rw [Notif.optRef_ne h0]
    unfold Fl4Spec.ifSporadicCurScTestRefillUnblockCheck Fl4Spec.ifCondRefillUnblockCheck
    simp only [Fl4Spec.NonDet.maybeM]
    rw [nd_bind_one (getSchedContext_eq hky), nd_gets_bind, nd_pure_bind']
    simp only [Fl4Spec.NonDet.when]
    by_cases e : y.scSporadic = true ∧ (L.mem s (scA t)).bv ≠ σ.curSc
    · simp only [e, ne_eq, not_false_eq_true, forall_const, and_self, ↓reduceIte, Option.some.injEq,
        Bool.false_eq_true, IsEmpty.forall_iff]
    · simp only [ne_eq, forall_const, ↓reduceIte, Option.some.injEq]
      rw [ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e),
        ite_f (c := y.scSporadic = true ∧ ¬ (L.mem s (scA t)).bv = σ.curSc) (by simpa only [ne_eq] using e)]
      rfl
  by_cases hsp' : L.mem s (scW (L.mem s (scA t)) 64#u64) ≠ 0#u64
  swap
  · have hb : b = false := by rw [b_post]; simp [h0]; simpa using hsp'
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (skip (by rw [hif, ite_f (fun h => hsp' (hsp.1 h.1))]))
  have hb : b = true := by rw [b_post]; simp [h0, hsp']
  simp only [hb, ↓reduceIte]
  step with sched.cur_sc.spec' as ⟨s1, s1_post⟩
  rw [sc_ne_eq]
  simp only [bind_ok]
  rw [s1_post, hc.cur]
  by_cases e : L.mem s (scA t) = nodeW st s c layout.node.CUR_SC
  · simp only [e, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 (skip (by rw [hif, ite_f]; rw [e, ← hs.curSc]; simp))
  · simp only [e, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    have hpc : (L.mem s (scA t)).bv ≠ σ.curSc := by rw [hs.curSc]; exact bv_ne e
    have hxsc : xt.tcbSchedContext = some (L.mem s (scA t)).bv := by rw [hsct, Notif.optRef_ne h0]
    have hmx : (L.rmax s (L.mem s (scA t))).val ≠ 0 := hy.spor hsp'
    have hya : Fl4Spec.scActive y = true := hy.active_of_rmax hmx
    obtain ⟨hiS, -, -⟩ := hXi.2.2.bound t htH h0
    have hiA : L.mem s (scA t) ∈ Ac := (hSc.act _ hiS).2 (fun e0 => hmx (by rw [e0]; rfl))
    refine WP.spec_mono (WP.spec_and (WP.spec_and (WP.spec_and (unblock_check_refines s σ hS hscC hmx)
      (WP.spec_and (unblock_check_scw hS hscC hmx) (unblock_check_kfoot hS hscC hmx)))
      (Fl4Proofs.P1.sporadic.unblock_check.all s t _ h hB hXi hSc hSg htH rfl h0 hiA))
      (Fl4Proofs.P1.sporadic.unblock_check.kw (Es := P1.EH Hp) s t _ h hB hXi hSc hSg htH rfl h0 hiA)) ?_
    rintro s' ⟨⟨⟨⟨σ', he, -, -, hS'⟩, hW, hwK⟩, h2, hB2, hX2, hS2, hSg2, -, -, -, hT2, -⟩, hfoot⟩
    have hK := Ipc.nks_refillUnblockCheck _ σ ((), σ') (by rw [he]; rfl)
    have mem : ((), σ') ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) (L.mem s (scA t)).bv σ).1 := by
      rw [he]; exact Set.mem_singleton _
    have hne' := hne _ y n hky hya
    refine ⟨σ', by rw [hspec0, hif, ite_t ⟨hsp.2 hsp', hpc⟩, he], sc_step_lift hP0 hX (hW.mono fun _ h => Or.inl h) hK hS',
      hwK, h2, hB2, hX2, hS2, hSg2, hT2, hfoot, ?_⟩
    rcases unblock_result hky hne' mem with ⟨rfl, -⟩ | ⟨z, rfl, hz1, hz2, hz3, -, hz5, hz6⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, y, z, n, hxsc, hky, hne', hpc, rfl, hz1, hz2, hz3, hz5, hz6⟩

end Hole

/-- `RSFr` from a state with other user memory. -/
theorem RSFr.ofUm {t r : Fl4Spec.ObjRef} {σ0 σ' : Fl4Spec.State Unit} (F : RSFr t r σ0 σ')
    (um : Fl4Spec.Word → Fl4Spec.Word8) : RSFr t r (Endp.setUm σ0 um) σ' :=
  ⟨⟨F.sk.ct, F.sk.idle, F.sk.cons, F.sk.tm, F.sk.csc, F.sk.rel, F.sk.cdt, F.sk.orig, F.sk.arch, F.sk.dt, F.sk.isc⟩,
    F.kh⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- FL4's `receive_ipc` up to the endpoint's state with a bound notification
that is not active, the receive polling or the notification's SC not the
thread's (`maybe_return_sched_context` a no-op): XTopJointRecvIpc's
`receive_ipc_pollN_pre` and XTopJointRecvIpcBound's `receive_ipc_blockN_red`
for any endpoint state. -/
theorem receive_ipc_preN {R : Set U64} {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 blk : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) {n : U64}
    (hbound : L.mem s (tBoundA t) = n) (hn0 : n ≠ 0#u64) (hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE)
    (hwn : blk = false ∨ L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (P1.scA t))
    {P : S × A → Prop}
    (h : (do
      let st1 ← obj.Ep.state st e s
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ P ⦄ := by
  cases blk with
  | false => exact receive_ipc_pollN_pre hrc hbound hn0 hstN h
  | true =>
    have hwn' := hwn.resolve_left (by decide)
    have key : (do
        let (s2, a2) ← (do
          let t' ← notification.maybe_return_sched_context st s n t
          ok (t', a))
        let st1 ← obj.Ep.state st e s2
        if st1 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s2 t e true rv
          ok (s3, a2)
        else if st1 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s2 t e true rv
          ok (s3, a2)
        else endpoint.receive_from_sender st arI s2 a2 t e rv) ⦃ P ⦄ := by
      have hm : (do
          let t' ← notification.maybe_return_sched_context st s n t
          ok (t', a)) ⦃ r => r = (s, a) ⦄ :=
        WP.spec_bind (Sched.maybe_return_noop hwn') fun s' h' => by rw [h']; exact (WP.spec_ok _).2 rfl
      refine WP.spec_bind hm ?_
      rintro ⟨s2, a2⟩ hq
      rw [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
      exact h
    unfold endpoint.receive_ipc
    simp only [capability.Cap.ptr, bind_tc_ok]
    rcases hrc with ⟨rfl, -, rfl⟩ | ⟨b, r', rfl, -, -, h0⟩
    · simp only [endpoint.take_reply, bind_tc_ok]
      step with Endp.obj.Tcb.bound_ntfn.spec as ⟨i, hi⟩
      simp only [hi, hbound]
      rw [if_pos (by simpa using hn0)]
      refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
      rintro v rfl
      rw [epState_eq, if_neg hstN]
      simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, bind_tc_ok, bind_ok, Bind.bind]
      simpa only [bind_tc_ok, bind_ok, Bind.bind] using key
    · simp only [endpoint.take_reply]
      step with Endp.obj.Reply.tcb.spec as ⟨i, hi⟩
      step with P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
      simp only [hb, hi, h0, decide_true, ↓reduceIte, bind_tc_ok]
      step with Endp.obj.Tcb.bound_ntfn.spec as ⟨j, hj⟩
      simp only [hj, hbound]
      rw [if_pos (by simpa using hn0)]
      refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
      rintro v rfl
      rw [epState_eq, if_neg hstN]
      simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, bind_tc_ok, bind_ok, Bind.bind]
      simpa only [bind_tc_ok, bind_ok, Bind.bind] using key

set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from the head sender at `J`**, for any FL4 program `m`
reducing to the endpoint-state switch (`hm`; `JAtZ.recvSendJ0`, and after
`maybe_return_sched_context` XTopJointRecvSendRet's `JAtZ.recvSendRetJ`). -/
theorem JAtZ.recvSendJG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false ∨
      ((dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null)) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    {m : Result (S × A)} (hm : ∀ {P : S × A → Prop}, (do
            let st1 ← obj.Ep.state st e s
            if st1 = obj.EP_IDLE then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else if st1 = obj.EP_RECV then do
              let s3 ← endpoint.wait_for_sender st s t e blk rv
              ok (s3, a)
            else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄ → m ⦃ P ⦄) :
    m ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hsr := replyArg_spec hP hR hrc
  obtain ⟨hst1, xs0, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : sd' = sd := eq_of_bv hd'.symm
  subst hdd
  have hsT : sd' ∈ Z.T := hQ.mem sd' (by simp)
  have hsa := hP.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  have hsb : L.mem s (tBlockA sd') = e := (hB sd' (by simp)).2
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  have he' : e' = e.bv := by
    have := hxs.blk e' (by rw [hstd]; rfl); rw [hsb] at this; exact this.symm
  subst he'
  obtain ⟨hbadge, hflags⟩ := hxs.send _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    constructor
    · intro h0; obtain ⟨_, _, _, h1⟩ := tsCode_three h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
    · intro h0; obtain ⟨_, _, h1⟩ := tsCode_four h0; rw [h1] at hrun; simp [Fl4Spec.runnable] at hrun
  have hts : t ≠ sd' := by intro h; subst h; exact hnb.2 (hxt.st.symm.trans hs4)
  have hse : sd'.bv ≠ e.bv := kheap_ne hks hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have hst' : sd'.bv ≠ t.bv := bv_ne (Ne.symm hts)
  have hsc : sd'.bv ≠ σ.curThread := by rw [hct]; exact hst'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hsH : sd' ∈ P1.Heap.tcbs H := J.zH.1 sd' hsT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hsta := hTP sd' hsH
  have hss : L.mem s (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [stA_tStA, tsVals.2.2.2.1]; exact UScalar.eq_of_val_eq hs4
  have hbe : L.mem s (P1.blockA sd') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hsb
  have hdq := P1.endpoint.ep_dequeue.inv s sd' Q0 R0 h0 hsH (by simp) (Or.inl hss)
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : sd' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 sd' hsH (by simp) (Or.inl hss); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e sd' (EQ0 e) hTP hE0 hq0' hdm
  apply hm
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst1]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.2]; decide)]
  unfold endpoint.receive_from_sender
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = sd' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := sd')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he sd' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, cc1, nc1⟩, w1⟩
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (sd' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, -, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  -- the badge and the flags
  have hbw : L.mem s1 (tBadgeA sd') = L.mem s (tBadgeA sd') := hA1 _ (a_badge hsa).1 ⟨sd', hsT, (a_badge hsa).2⟩
  have hfw : L.mem s1 (tFlagsA sd') = L.mem s (tFlagsA sd') := hA1 _ (a_flags hsa).1 ⟨sd', hsT, (a_flags hsa).2⟩
  refine WP.spec_bind (Endp.obj.Tcb.block_badge.spec s1 sd') ?_
  rintro bdg hbdg
  refine WP.spec_bind (Endp.obj.Tcb.block_flags.spec s1 sd') ?_
  rintro fl hfl
  step as ⟨i, hi, hi'⟩
  step as ⟨i1, hi1, hi1'⟩
  step as ⟨i2, hi2, hi2'⟩
  have hg : (i != 0#u64) = dd.senderCanGrant := by
    rw [← flags_grant dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi
  have hgr : (i1 != 0#u64) = dd.senderCanGrantReply := by
    rw [← flags_grantReply dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi1
  have hc : (i2 != 0#u64) = dd.senderIsCall := by
    rw [← flags_call dd, ← hflags, ← hfw, ← hfl]
    congr 1
    exact UScalar.eq_of_val_eq hi2
  have hbb : bdg.bv = dd.senderBadge := by rw [hbdg, hbw]; exact hbadge
  -- the transfer
  refine WP.spec_bind (J.xferStepGJ hk (epDeq (.sendEP (sd'.bv :: q)) sd'.bv) hR1 hS1 hW1 F1 hsT ht (Ne.symm hts)
    hks hkt hfs bdg (i != 0#u64) h1 hB1 hX1 hS1' hSg1) ?_
  rintro s2 ⟨x2, um2, y, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksb, hKy, -, hyk⟩
  have hncn : ∀ {q' : Fl4Spec.ObjRef} {o' : Fl4Spec.KernelObject}, σ.kheap q' = some o' →
      (∀ r cs, o' ≠ .cnode r cs) → σy.kheap q' = some o' :=
    fun hq ho => (hyk _ fun r cs h0 => ho r cs (by rw [hq] at h0; exact Option.some.inj h0)).trans hq
  have hky : σy.kheap e.bv = some (.endpoint (.sendEP (sd'.bv :: q))) := hncn hk (fun _ _ h0 => by cases h0)
  have hksy : σy.kheap sd'.bv = some (.tcb xs) := hncn hks (fun _ _ h0 => by cases h0)
  have hkty : σy.kheap t.bv = some (.tcb xt) := hncn hkt (fun _ _ h0 => by cases h0)
  have hcty : σy.curThread = σ.curThread := hKy.2.2.2.2
  set σ1y := Notif.updK σy e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1y
  have hkt1y : σ1y.kheap t.bv = some (.tcb xt) := by simp [σ1y, hte, hkty]
  have hks1y : σ1y.kheap sd'.bv = some (.tcb xs) := by simp [σ1y, hse, hksy]
  have hk1ey : σ1y.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by simp [σ1y]
  set σ2 := Notif.updK (Endp.setUm σ1y um2) t.bv (.tcb x2) with hσ2
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1y]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, Ne.symm hte, hk1ey]
  -- the spec frame from `σy`
  have Fr1y : RSFr sd'.bv t.bv σy σ1y := RSFr.upd hky (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv (Endp.setUm σ1y um2) σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := Endp.setUm σ1y um2) hkt1y x2.tcbArch
    rw [← hx2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σy σ2 := (Fr1y.trans (RSFr.um _ _ σ1y um2)).trans Fr2c
  have IK1y : IK sd'.bv σy σ1y := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hky
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1y : Ipc.SKeep σy σ1y := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σy σ2 := IK1y.trans ((IK.um _ σ1y um2).trans
    (IK.updTcb (σ := Endp.setUm σ1y um2) hkt1y (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2])))
  have SK2 : Ipc.SKeep σy σ2 := SK1y.trans ((Fl4Proofs.P3.SKeep.um σ1y um2).trans (Ipc.SKeep.updK (σ := Endp.setUm σ1y um2) (p := t.bv)
    (o := .tcb x2) (fun y' h => ⟨xt, hkt1y, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h)))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => Jy.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
  refine WP.spec_bind (unblockHole hP0 (IpcRel.ofSRN hR2 hS2') hsT hks2 hne2 h2 hB2 hX2 hS2'' hSg2 hsH) ?_
  rintro s3 ⟨σ3, hA, hIR3, hW3, h3, hB3, hX3, hS3', hSg3, hT3, fu3, hU3⟩
  have hk3 : ∀ q' o', σ2.kheap q' = some o' → (∀ y' n, o' ≠ .schedContext y' n) → σ3.kheap q' = some o' := by
    intro q' o' hq ho
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, -, rfl, -⟩
    · exact hq
    · have hqp : q' ≠ p := fun h => by subst h; rw [hkp] at hq; cases hq; exact ho _ _ rfl
      simp [Notif.updK, hqp, hq]
  have hks3 : σ3.kheap sd'.bv = some (.tcb xs) := hk3 _ _ hks2 (fun _ _ h => by cases h)
  have hk3e := hk3 _ _ hk2e (fun _ _ h => by cases h)
  have ct3 : σ3.curThread = σ2.curThread := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have act3 : σ3.schedulerAction = σ2.schedulerAction := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]
    · rw [h]; rfl
  have hR3 := hIR3.1.toE
  have hS3 := IpcRel.toSRN hIR3.1 hIR3.2
  have hxs3 := hR3.at_tcb hsT hks3
  refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 sd') ?_
  rintro ft hft
  have hft0 : ft = fl4_abi.consts.fault.NullFault := by
    rw [hft, hxs3.fault0.2 hfs]; unfold fl4_abi.consts.fault.NullFault; rfl
  -- the sender is in no queue
  have eW : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → 3328 ≤ K.val → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s3 (core.num.U64.wrapping_add sd' K) = L.mem s (core.num.U64.wrapping_add sd' K) := by
    intro K k1 k2 k3 k4 k5
    rw [hT3 sd' hsH K k1 k2, f2 sd' hsH K k3 k1 k2, f1 sd' hsH K k1 k2 k4 k5]
  have hb3 : L.mem s3 (tBlockA sd') = e := by
    rw [← blockA_tBlockA, P1.blockA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.blockA_eq]
    exact hbe
  have hst3 : L.mem s3 (P1.stA sd') = sched.TS_BLOCKED_ON_SEND := by
    rw [P1.stA_eq, eW _ (by simp) (by simp) (by simp) (by simp) (by simp), ← P1.stA_eq]
    exact hss
  have hq3 := dequeued_not_queued hR3 he hb3 hk3e (epDeq_not_mem _)
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ sd' :=
    hX3.noref hsta (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide)
      (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide)
  cases hcl : dd.senderIsCall with
  | false =>
      simp only [hc, hcl, hft0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      -- the sender runs
      refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 hsT hks3 hq3
          (by rw [hstd]; simp [tsCode]) .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
          (set_thread_state_sfoot hIR3.2.2.1 hsT sched.TS_RUNNING))
        (WP.spec_and (P1.sts_all s3 sd' _ Q0 R0 h3 hB3 hX3 hS3' hSg3 hsH P1.not_blocked_running P1.running_ne
            (Or.inl (Or.inr rfl)) hnr3
            ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
          (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s3 sd' sched.TS_RUNNING h3 hsH))) ?_
      rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
      set x5 : Fl4Spec.Tcb := { xs with tcbState := .running } with hx5
      have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
        show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σy.curThread; rw [hcty]; exact hsc
      set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
      -- the footprints from the transfer's base
      have hks2b : L.ksb s2 = L.ksb y := hW2.1
      have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
      have hks3b : L.ksb s3 = L.ksb y := hW3'.1
      have hW5' : P1.WritesIn st y s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
        hW3'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3b).1 hb)))))
      have hfoot := footW_trans (footW_trans F2 (footW_of fu3)) (footW_of fu5)
      have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
      have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
          (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
        ⟨⟨Q0, R0, h5.congrX (P1.excT_congr hXc)⟩, hB5, hX5, hS5', hSg5⟩
      -- the frame
      have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
        rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
        · exact RSFr.refl _ _ _
        · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
            (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
      have Fr5 : RSFr sd'.bv t.bv σy σ5 := Fr2.trans (Fr3.trans (RSFr.stsRun hks3 (Or.inl ⟨_, _, hstd⟩)))
      -- `Inv` at the end
      have hnqD : NotQueued σy sd'.bv := by
        refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
          rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
          rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
      set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
      have IK5' : IK sd'.bv σy σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
      have SK5' : Ipc.SKeep σy σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
        (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
      have hrib : RelIfBound σ5' sd'.bv :=
        Ipc.RelIfBound.of_keep (Jy.inv.rd sd'.bv xs hksy (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
          fun b' h => by rw [hfs] at h; cases h⟩)))) SK5'
      have I5' : Inv σ5' := ((Jy.inv.toBut sd'.bv).ik hnqD IK5').1.inv fun _ _ _ => hrib
      have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
      have I5 : Inv σ5 := by
        rcases hU3 with e3 | ⟨p, y', z, n, hxp, hkp, hne', hpc, e3, hz1, hz2, hz3, hz5, hz6⟩
        · rw [hσ5, stsAct_ne hsc3, e3]; exact I5'
        · have hpsd : p ≠ sd'.bv := fun h => by rw [h, hks2] at hkp; cases hkp
          have hkp' : σ5'.kheap p = some (.schedContext y' n) := by simp [σ5', hpsd, hkp]
          have e5 : σ5 = updSc { σ5' with reprogramTimer := true } p z n := by
            rw [hσ5, stsAct_ne hsc3, e3, hσ5']
            rw [show ({ Notif.updK σ2 sd'.bv (.tcb x5) with reprogramTimer := true } : Fl4Spec.State Unit) =
              Notif.updK { σ2 with reprogramTimer := true } sd'.bv (.tcb x5) from rfl, updSc_updK_comm _ hpsd]
          rw [e5]
          refine I5'.scRef hkp' hne' hz1 hz2 hz3 hz5 hz6 (fun u hu x hx hxu => ?_)
          obtain ⟨y1, n1, hk1, ht1⟩ := I5'.back u x p hx hxu
          obtain ⟨y2, n2, hk2, ht2⟩ := I5'.back sd'.bv x5 p hk5' hxp
          rw [hk1] at hk2; cases hk2
          have hu' : u = sd'.bv := Option.some.inj (ht1.symm.trans ht2)
          subst hu'
          exact hnqD.2 (by rw [← SK5'.1]; exact hu)
      have act5 : σ5.schedulerAction = σy.schedulerAction := by
        rw [hσ5, stsAct_ne hsc3]; exact act3
      -- back to `JAtZ`
      have hth : Z.th t = some .tcb := by
        obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
        exact Ipc.RelTopB.tcbT hB0' hkt
      obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs)
        Jy ht hth hkty hW5' hfoot
      have hIu := Ju.xtop.irelK Ju.ks Ju.buf
      have htD := Ju.not_dead_of_st hsT hksy (by rw [hstd]; simp [tsCode])
      have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
      have hIR5 := IpcRel.ofSRN hR5 hS5
      obtain ⟨V', J5⟩ := Ju.rsfrStep (by rw [← hKy.2.1] at hIR5; exact hIR5) hF hWu hblk hFu (RSFr.ofUm Fr5 umu) I5
        (Or.inl act5) htD
      -- `possible_switch_to`
      have hk5 : σ5.kheap sd'.bv = some (.tcb x5) := by rw [hσ5, stsAct_kheap]; simp
      have hnr5 : sd'.bv ∉ σ5.releaseQueue := by rw [Fr5.sk.rel]; exact hnqD.2
      have hact5 : ∀ p y' n, x5.tcbSchedContext = some p → σ5.kheap p = some (.schedContext y' n) →
          Fl4Spec.scActive y' = true := by
        intro p y' n hp hy
        obtain ⟨y0, hy0, hyy, -⟩ := Fr5.scB hy
        obtain ⟨y1, n1, hky1, hyt⟩ := Jy.inv.back _ _ _ hksy hp
        rw [hy0] at hky1; cases hky1
        have h0 := Jy.bsa.tcb p y0 n sd'.bv xs hy0 hyt hksy (by rw [hstd]; rfl)
        have em : y'.scRefillMax = y0.scRefillMax := by rw [hyy]
        simp only [Fl4Spec.scActive] at h0 ⊢; rw [em]; exact h0
      have hti5 : sd'.bv ≠ σ5.idleThread := by
        rw [Fr5.sk.idle]
        intro h
        obtain ⟨x, hkx, -, hxs', -⟩ := Jy.act.2
        rw [← h, hksy] at hkx; cases hkx; rw [hstd] at hxs'; cases hxs'
      have htc5 : sd'.bv ≠ σ5.curThread := by rw [Fr5.sk.ct, hcty]; exact hsc
      have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
          (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
        rw [← hbb, ← hg]; exact e2
      have hspec := receiveIpc_send_eqB b rights blk hsr hkt hbN hk hks hse hstd hcl e2' hA hks3 hfs
      refine WP.spec_bind (J5.sendSwitchJ hsT hk5 rfl hnr5 hact5 hti5 htc5) ?_
      rintro s7 ⟨σ7, h7, Lst7, J7⟩
      refine (WP.spec_ok _).2 ⟨((), σ7), ?_, J7.xtop.relTop, _, _, _, _, _, _, J7⟩
      rw [hspec, h7]; exact Set.mem_singleton _

  | true =>
      have hno := (hcall _ _ hstd).resolve_left (fun h => by rw [hcl] at h; cases h)
      have hnoS : ¬ ((dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none) := by
        rintro ⟨hgg, hrn⟩
        rcases hno with ⟨hg0, hgr0⟩ | hnull
        · rcases hgg with h | h
          · rw [hg0] at h; cases h
          · rw [hgr0] at h; cases h
        · rcases hrc with ⟨-, -, hrv⟩ | ⟨_, _, hr, -⟩
          · exact hrn (by rw [hrv, optRef_zero])
          · rw [hnull] at hr; cases hr
      suffices H : (do
          let s4 ← sched.set_thread_state st s3 sd' sched.TS_INACTIVE
          ok (s4, a)) ⦃ r => ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
        rcases hno with ⟨hg0, hgr0⟩ | hnull
        · simp only [hc, hcl, hg, hg0, hgr, hgr0, Bool.false_eq_true, ↓reduceIte]
          exact H
        · have hrv : rv = 0#u64 := by
            rcases hrc with ⟨-, -, hrv⟩ | ⟨_, _, hr, -⟩
            · exact hrv
            · rw [hnull] at hr; cases hr
          subst hrv
          simp only [hc, hcl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
          exact H
      -- the sender `Inactive`
      have hnqS : NotQueued σ sd'.bv := by
        refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
          rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
          rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
      obtain ⟨hqb, hrb'⟩ := J.curBits hsT hnqS.1 hnqS.2
      have hna3 : L.actionW s3 ≠ sd' := by
        refine actionW_ne_of hIR3.2.2.1 hsT (fun h => ?_)
        have hsw := Jy.act.1 sd'.bv (show σy.schedulerAction = _ from act3.symm.trans h)
        obtain ⟨x, -, -, -, hkx, -, hrx, -⟩ := schedulable_inv hsw
        rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
      refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 hsT hks3 hq3
          (by rw [hstd]; simp [tsCode]) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
          (set_thread_state_sfoot hIR3.2.2.1 hsT sched.TS_INACTIVE))
        (WP.spec_and (P1.sts_all s3 sd' _ Q0 R0 h3 hB3 hX3 hS3' hSg3 hsH P1.not_blocked_inactive P1.inactive_ne
            (Or.inl (Or.inr rfl)) hnr3
            ⟨fun c hc' p hp hm => absurd hm (h0.notQ hsH hqb hc' hp), fun c hc' hm => absurd hm (h0.notR hsH hrb' hc'),
              fun e0 => absurd e0 hna3⟩)
          (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s3 sd' sched.TS_INACTIVE h3 hsH))) ?_
      rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
      set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
      have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
        show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σy.curThread; rw [hcty]; exact hsc
      set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
      -- the footprints from the transfer's base
      have hks2b : L.ksb s2 = L.ksb y := hW2.1
      have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
      have hks3b : L.ksb s3 = L.ksb y := hW3'.1
      have hW5' : P1.WritesIn st y s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
        hW3'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3b).1 hb)))))
      have hfoot := footW_trans (footW_trans F2 (footW_of fu3)) (footW_of fu5)
      have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
      have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
          (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
        ⟨⟨Q0, R0, h5.congrX (P1.excT_congr hXc)⟩, hB5, hX5, hS5', hSg5⟩
      -- the frame
      have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
        rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
        · exact RSFr.refl _ _ _
        · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
            (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
      have Fr5 : RSFr sd'.bv t.bv σy σ5 := Fr2.trans (Fr3.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩)))
      -- `Inv` at the end
      have hnqD : NotQueued σy sd'.bv := by
        refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
          rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
        · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
          rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
      set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
      have IK5' : IK sd'.bv σy σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
      have SK5' : Ipc.SKeep σy σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
        (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
      have hrib : RelIfBound σ5' sd'.bv :=
        Ipc.RelIfBound.of_keep (Jy.inv.rd sd'.bv xs hksy (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
          fun b' h => by rw [hfs] at h; cases h⟩)))) SK5'
      have I5' : Inv σ5' := ((Jy.inv.toBut sd'.bv).ik hnqD IK5').1.inv fun _ _ _ => hrib
      have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
      have I5 : Inv σ5 := by
        rcases hU3 with e3 | ⟨p, y', z, n, hxp, hkp, hne', hpc, e3, hz1, hz2, hz3, hz5, hz6⟩
        · rw [hσ5, stsAct_ne hsc3, e3]; exact I5'
        · have hpsd : p ≠ sd'.bv := fun h => by rw [h, hks2] at hkp; cases hkp
          have hkp' : σ5'.kheap p = some (.schedContext y' n) := by simp [σ5', hpsd, hkp]
          have e5 : σ5 = updSc { σ5' with reprogramTimer := true } p z n := by
            rw [hσ5, stsAct_ne hsc3, e3, hσ5']
            rw [show ({ Notif.updK σ2 sd'.bv (.tcb x5) with reprogramTimer := true } : Fl4Spec.State Unit) =
              Notif.updK { σ2 with reprogramTimer := true } sd'.bv (.tcb x5) from rfl, updSc_updK_comm _ hpsd]
          rw [e5]
          refine I5'.scRef hkp' hne' hz1 hz2 hz3 hz5 hz6 (fun u hu x hx hxu => ?_)
          obtain ⟨y1, n1, hk1, ht1⟩ := I5'.back u x p hx hxu
          obtain ⟨y2, n2, hk2, ht2⟩ := I5'.back sd'.bv x5 p hk5' hxp
          rw [hk1] at hk2; cases hk2
          have hu' : u = sd'.bv := Option.some.inj (ht1.symm.trans ht2)
          subst hu'
          exact hnqD.2 (by rw [← SK5'.1]; exact hu)
      have act5 : σ5.schedulerAction = σy.schedulerAction := by
        rw [hσ5, stsAct_ne hsc3]; exact act3
      -- back to `JAtZ`
      have hth : Z.th t = some .tcb := by
        obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
        exact Ipc.RelTopB.tcbT hB0' hkt
      obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs)
        Jy ht hth hkty hW5' hfoot
      have hIu := Ju.xtop.irelK Ju.ks Ju.buf
      have htD := Ju.not_dead_of_st hsT hksy (by rw [hstd]; simp [tsCode])
      have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
      have hIR5 := IpcRel.ofSRN hR5 hS5
      obtain ⟨V', J5⟩ := Ju.rsfrStep (by rw [← hKy.2.1] at hIR5; exact hIR5) hF hWu hblk hFu (RSFr.ofUm Fr5 umu) I5
        (Or.inl act5) htD
      have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
          (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
        rw [← hbb, ← hg]; exact e2
      have hspec := receiveIpc_sendCall_eq b rights blk hsr hkt hbN hk hks hse hstd hnoS e2' hA hks3 (Or.inl hcl)
      refine (WP.spec_ok _).2 ⟨((), σ5), ?_, J5.xtop.relTop, _, _, _, _, _, _, J5⟩
      rw [hspec]; exact Set.mem_singleton _

set_option maxHeartbeats 4000000 in
/-- FL4's `receive_ipc` reduces to the endpoint-state switch when the
receiver (the current thread) has no bound notification or one not active,
polling or not lending its SC (`receive_ipc_pre`, `receive_ipc_preN`). -/
theorem JAtZ.recvPreN (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (e cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) {P : S × A → Prop} :
    (do
        let st1 ← obj.Ep.state st e s
        if st1 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s t e blk rv
          ok (s3, a)
        else if st1 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s t e blk rv
          ok (s3, a)
        else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄ →
      endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ P ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hxt := hI.1.toE.at_tcb ht hkt
  have hpre : ∀ {P : S × A → Prop}, (do
      let st1 ← obj.Ep.state st e s
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s t e blk rv
        ok (s3, a)
      else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄ →
      endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ P ⦄ := by
    intro P h
    rcases hbN with hbn | ⟨n0, xn, hbn, hkn, hna, hnr⟩
    · exact receive_ipc_pre s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc (optRef_none (hxt.bound.symm.trans hbn)) h
    · obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
      have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
      have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e0 => by rw [e0, optRef_zero] at hb1; cases hb1
      have hbound : L.mem s (tBoundA t) = n := by
        rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
      have hxn := hI.1.toN.at_ntfn hn hkn
      have hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE := by
        have ho := hxn.obj
        cases hxo : xn.ntfnObj with
        | activeNtfn b0 => simp [Fl4Spec.isActive, hxo] at hna
        | idleNtfn => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
        | waitingNtfn q => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
      have hwn : blk = false ∨ L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (P1.scA t) := by
        cases hblk : blk with
        | false => exact Or.inl rfl
        | true =>
          right
          have hnr' := hnr hblk
          have hsN : xn.ntfnSc = optRef (L.mem s (nScA n)) := hxn.sc
          obtain ⟨Q0', R0', -, hs0⟩ := J.xtop.fin.1.1.1.lists
          obtain ⟨xt0, hkt0, -, -, hsct, -⟩ := hs0.tcb t ht
          rw [hkt] at hkt0; cases hkt0
          by_cases h0 : L.mem s (nScA n) = 0#u64
          · exact Or.inl h0
          · refine Or.inr fun he' => hnr' ⟨?_, ?_⟩
            · rw [hsN, he']; exact hsct.symm
            · rw [hsN, Notif.optRef_ne h0]; simp
      exact receive_ipc_preN hrc hbound (by rw [← hbound]; exact hbz) hstN hwn h
  exact hpre

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` from the head sender at `J`**, the sender neither calling
nor faulted, the receiver (the current thread) without a bound notification
(module docstring). -/
theorem JAtZ.recvSendJ0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcall : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false ∨
      ((dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null)) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  exact J.recvSendJG ht hkt hrun hbN hct he hk hks hfs cb c1 c2 c3 c4 hrc hcall b rights
    (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

end

end

end Fl4Proofs.P3
