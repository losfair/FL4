/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` at `J`** (KENTRY-PLAN.md item 6,
toward XTopJointDispatch's `JRecvIpcHyp`).

* `JAtZ.recvIpcPollJ`: a polling receive (`blocking = false`) of a thread
  with no bound notification, on an endpoint with no waiting sender, with a
  null reply cap or one whose reply object is not linked to a thread
  (EpRecv's `ReplyArg`): the badge register := 0 (the spec's
  `doNbrecvFailedTransfer`, EpRecv's `receiveIpc_noSend`), one register write
  at `J` (`JAtZ.recvIpcPollJR`: `JAtZ.regWrJ`, `badge_wr_irel`, given the
  reductions); FL4's side by EpRecv's `receive_ipc_pre` and
  `receive_ipc_poll_cont` (`receive_ipc_poll_eq`). `JAtZ.recvIpcPollNJ`: the
  same with a bound notification that is not active (no `maybe_return` when
  polling: `receive_ipc_pollN_pre`, XTopJointRecvIpcBound's
  `receiveIpc_boundNA`).
* The case predicates (`RecvIpcPollCase`, `RecvIpcActCase`, `RecvIpcBlockCase`,
  `RecvIpcBoundCase`), `JAtZ.replyArg_of`, `JAtZ.recvCov_of`, used by
  XTopJointRecvIpcLink's case split for `JRecvIpcHyp` (which superseded the
  former `JRecvIpcRestHyp` / `jRecvIpcHyp_of` / `dispatch_recvJR`).
-/
import Fl4Proofs.P3.XTopJointRecvIpcRet
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- FL4's polling wait on an idle or receiving endpoint (the part of
`receive_ipc` after the bound notification): the badge register := 0. -/
theorem receive_ipc_poll_cont {s : S} {a : A} {t e rv : U64}
    (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64) :
    (do
      let st1 ← obj.Ep.state st e s
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s t e false rv
        ok (s3, a)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s t e false rv
        ok (s3, a)
      else endpoint.receive_from_sender st arI s a t e rv) ⦃ r =>
      r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄ := by
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e false rv
      ok (s3, a)) ⦃ r => r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE 0#u64) ?_
    rintro s1 rfl
    rw [WP.spec_ok, regIdx_badge]
  refine WP.spec_bind (P1.obj.Ep.state.spec s e) ?_
  rintro v rfl
  rw [epState_eq]
  rcases hst with h | h
  · rw [h, if_pos ep_state_vals.1.symm]
    exact key
  · rw [h, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key

/-- FL4's polling `receive_ipc` with no bound notification on an idle or
receiving endpoint, the reply cap as in `ReplyArg`: the badge register := 0. -/
theorem receive_ipc_poll_eq {R : Set U64} {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv)
    (hbound : L.mem s (tBoundA t) = 0#u64) (hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄ :=
  receive_ipc_pre s a t e cb c1 c2 c3 c4 false rc rc' rv hrc hbound (receive_ipc_poll_cont hst)

/-- FL4's polling `receive_ipc` with a bound notification that is not
active (no `maybe_return_sched_context` when polling), reduced to the wait. -/
theorem receive_ipc_pollN_pre {R : Set U64} {s : S} {a : A} {t e cb : U64} {c1 c2 c3 c4 : Bool}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg R (L.mem s) rc rc' rv) {n : U64}
    (hbound : L.mem s (tBoundA t) = n) (hn0 : n ≠ 0#u64) (hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE)
    {P : S × A → Prop}
    (h : (do
      let st1 ← obj.Ep.state st e s
      if st1 = obj.EP_IDLE then do
        let s3 ← endpoint.wait_for_sender st s t e false rv
        ok (s3, a)
      else if st1 = obj.EP_RECV then do
        let s3 ← endpoint.wait_for_sender st s t e false rv
        ok (s3, a)
      else endpoint.receive_from_sender st arI s a t e rv) ⦃ P ⦄) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ P ⦄ := by
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
    simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, Bool.false_eq_true, bind_tc_ok,
      bind_ok, Bind.bind]
    exact h
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
    simp only [show (n != 0#u64) = true by simpa using hn0, ↓reduceIte, Bool.false_eq_true, bind_tc_ok,
      bind_ok, Bind.bind]
    exact h

set_option maxHeartbeats 8000000 in
/-- **A polling receive at `J`, given the reductions**: FL4's `receive_ipc`
writes 0 to the badge register (`hpoll`), the spec's is the polling
`receiveIpcBlocked` (`hsp`). -/
theorem JAtZ.recvIpcPollJR {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) {e : U64} (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap}
    (hpoll : endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      r = (L.wr s (regA t (regIdx Fl4Spec.badge_register)) 0#u64, a) ⦄)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) {reply : Option Fl4Spec.ObjRef}
    (hsp : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ =
      Fl4Spec.receiveIpcBlocked false t.bv e.bv reply σ) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  refine WP.spec_mono hpoll ?_
  rintro r rfl
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register (0#u64 : U64).bv)))}, False) := by
    rw [hsp]
    unfold Fl4Spec.receiveIpcBlocked Fl4Spec.doNbrecvFailedTransfer
    rw [if_neg (by simp), nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have hXb := badge_wr_irel J.ip hI ht hkt 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register 0#u64 hXb
  rw [hspec]
  exact ⟨_, Set.mem_singleton _, J1.xtop.relTop, _, _, _, _, _, _, J1⟩

/-- **A polling receive at `J`** (module docstring). -/
theorem JAtZ.recvIpcPollJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hns : ∀ q, x ≠ .sendEP q) (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => exact absurd rfl (hns q)
  exact J.recvIpcPollJR ht hkt cb c1 c2 c3 c4 (receive_ipc_poll_eq hrc hbound hst) b rights
    (receiveIpc_noSend b rights false (replyArg_spec J.ip.e hR hrc) hkt hbn hk hns)

/-- **A polling receive with a bound notification that is not active at
`J`**: as `JAtZ.recvIpcPollJ` (no `maybe_return` when polling, on either
side). -/
theorem JAtZ.recvIpcPollNJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hns : ∀ q, x ≠ .sendEP q) (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hst : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => exact absurd rfl (hns q)
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have hxn := hI.1.toN.at_ntfn hn hkn
  have hstN : stOf (L.mem s) n ≠ obj.NTFN_ACTIVE := by
    have ho := hxn.obj
    cases hxo : xn.ntfnObj with
    | activeNtfn b0 => simp [Fl4Spec.isActive, hxo] at hna
    | idleNtfn => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
    | waitingNtfn q => rw [hxo] at ho; rw [ho.1, ntfn_consts.2.2]; decide
  exact J.recvIpcPollJR ht hkt cb c1 c2 c3 c4
    (receive_ipc_pollN_pre hrc hbound (by rw [← hbound]; exact hbz) hstN (receive_ipc_poll_cont hst)) b rights
    (receiveIpc_boundNA b rights false (replyArg_spec J.ip.e hR hrc) hkt hbn hk hns hkn hna (fun h => by cases h))

/-- The case `JAtZ.recvIpcPollJ`/`JAtZ.recvIpcPollNJ` prove: polling, no bound
notification or one not active, no waiting sender, the reply cap null or naming a reply object not linked to a
thread. -/
def RecvIpcPollCase (ct : U64) (blocking : Bool) (s : S) (σ : Fl4Spec.State Unit) (p : U64)
    (rc : capability.Cap) : Prop :=
  blocking = false ∧ (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none ∨
      ∃ n xn, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
        Fl4Spec.isActive xn = false) ∧
    (∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q) ∧
    (rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64)

/-- The case `JAtZ.recvIpcActJ` proves: the current thread's bound
notification active, the reply cap null or naming a reply object not linked
to a thread. -/
def RecvIpcActCase (ct : U64) (s : S) (σ : Fl4Spec.State Unit) (rc : capability.Cap) : Prop :=
  (∃ xt n x b0, σ.kheap ct.bv = some (.tcb xt) ∧ xt.tcbBoundNotification = some n ∧
    σ.kheap n = some (.notification x) ∧ x.ntfnObj = .activeNtfn b0) ∧
    (rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64)

/-- The case `JAtZ.recvIpcBlockJ` proves: blocking, no bound notification,
no waiting sender, the reply cap null or naming a reply object not linked to
a thread. -/
def RecvIpcBlockCase (ct : U64) (blocking : Bool) (s : S) (σ : Fl4Spec.State Unit) (p : U64)
    (rc : capability.Cap) : Prop :=
  blocking = true ∧ (∀ xt, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = none) ∧
    (∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q) ∧
    (rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64)

/-- The case `JAtZ.recvIpcBlockNJ` (the notification's SC not the thread's)
and `JAtZ.recvIpcRetJ` (the thread's) prove: blocking, a bound notification
not active, no waiting sender, the reply cap null or naming a reply object
not linked to a thread. -/
def RecvIpcBoundCase (ct : U64) (blocking : Bool) (s : S) (σ : Fl4Spec.State Unit) (p : U64)
    (rc : capability.Cap) : Prop :=
  blocking = true ∧ (∃ xt n xn, σ.kheap ct.bv = some (.tcb xt) ∧ xt.tcbBoundNotification = some n ∧
    σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false) ∧
    (∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q) ∧
    (rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64)

/-- The reply cap of a receive as in `ReplyArg`, when null or naming a reply
object not linked to a thread. -/
theorem JAtZ.replyArg_of {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {rc : capability.Cap} {rc' : Fl4Spec.Cap}
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hrr : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) :
    ∃ rv, ReplyArg Z.R (L.mem s) rc rc' rv := by
  rcases hrc with ⟨rfl, rfl⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
  · exact ⟨0#u64, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have hrc' : rc' = absCap (.Reply q g') := hcr.abs
    subst hrc'
    obtain ⟨r, hr, h⟩ := J.obj.reply _ xr hkr
    rw [Sched.bv_inj h] at hr
    have h0 : L.mem s (rTcbA q) = 0#u64 := by
      rcases hrr with h | ⟨q', g'', h, h0⟩
      · cases h
      · cases h; exact h0
    exact ⟨q, Or.inr ⟨g', _, rfl, rfl, hr, h0⟩⟩

/-- The objects of a blocking receive's caps are covered (both caps held,
`J.cover_cap`). -/
theorem JAtZ.recvCov_of {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p b : U64} {sd g gr : Bool} (he : p ∈ Z.E)
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr)) {rc : capability.Cap}
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc) {rc' : Fl4Spec.Cap} {rv : U64}
    (hra : ReplyArg Z.R (L.mem s) rc rc' rv) :
    ((∀ k, Z.th p = some k → Sched.Covered (L.mem s) Z.G p.val (p.val + max (objSize k) 1)) ∧
      (∀ k, H p = some k → Sched.Covered (L.mem s) Z.G p.val (p.val + 2 ^ k.bits))) ∧
    (rv ≠ 0#u64 →
      (∀ k, Z.th rv = some k → Sched.Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Sched.Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits))) :=
  J.recvCov_ofW (P1.WritesIn.refl s _) he hHd hHr hra

end

end

end Fl4Proofs.P3
