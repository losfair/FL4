/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` from a waiting sender that pushes a
reply at `J`** (XTopJointRecvIpcLink's `JRecvSendHyp`, KENTRY-PLAN.md item 6
(d3); l4v `receive_ipc`'s `send_ep` branch with `reply_push`): the head
sender calls or is faulted, has the grant or grant-reply right, and the
receiver passes a reply object. At a resumed entry the receiver (the current
thread) has the current SC (`CurInv`), so `reply_push` never donates: the
reply is bound to the sender, which blocks on it. `hAct` of `JAtZ.recvSendFPJG` /
`JAtZ.recvSendPJG` also admits a pending reschedule with the receiver out of
the release queue and a sender without an SC (no donation either; after
`maybe_return_sc`, XTopJointRecvSendRP).

* `replyPush_don_irrel`, `receiveIpc_sendPush_eq`: the spec's `reply_push`
  from a caller without an SC or to a callee with an SC is the same for every `can_donate`; the spec's
  receive ending in the push.
* `updK3_eq`: two writes of one object around another collapse.
* `JAtZ.undeadC`: an object covered at the state leaves the dead set
  (XTopJointRestart's `JAtZ.undead` from cover facts).
* `JAtZ.deadP_rsfrC`, `JAtZ.rsfr_postGR`: XTopJointSendPush's
  `JAtZ.wake_postGR` with IpcRecvSendFr's `RSFr` as the first frame (its
  replies are kept, so no reply fact is needed) and a step `σa → σ'` (here
  IpcEpSteps' `pushSt`).
* `JAtZ.recvSendFPJG`: XTopJointRecvSendF's `JAtZ.recvSendFJG` (a faulted
  sender, a timeout only without an SC) with the push instead of `Inactive`:
  IpcPushCore's `reply_push_iC` on `IRel`, P1's `ipc.reply_push.ipc` /
  `ipc.reply_push.nd` from the hole of the dequeue, `JAtZ` by `rsfr_postGR`
  at `pushSt` of the state where the sender is `Inactive` (`Inv` there as in
  `recvSendFJG`, `ps_inv`); the reply leaves the dead set first (it is
  covered: `hcovR`).
* `JAtZ.recvSendPJG`: the same for a calling sender without a fault, after
  XTopJointRecvSend's `JAtZ.recvSendJG` transfer (`xferStepGJ`, its `JAtZ`
  at `σy`).
* `PushOK`, `JAtZ.recvSendP0X`: the two cases, the receiver not lending its
  SC (`JAtZ.recvPreN`). A receiver whose bound notification lends it its SC
  has none after `maybe_return_sc`, so a push from a sender with an SC
  donates: not covered here (a sender without one: XTopJointRecvSendRP).
-/
import Fl4Proofs.P3.XTopJointRecvSendF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecP
open Fl4Spec

/-- The spec's `reply_push` from a caller without an SC, or to a callee with
an SC, does not depend on `can_donate`. -/
theorem replyPush_don_irrel {σ : State Unit} {t d r : ObjRef} {xt xd : Tcb} (hkt : σ.kheap t = some (.tcb xt))
    (hkd : σ.kheap d = some (.tcb xd)) (hsc : xt.tcbSchedContext = none ∨ xd.tcbSchedContext ≠ none)
    (b1 b2 : Bool) :
    replyPush (Z := Unit) t d r b1 σ = replyPush (Z := Unit) t d r b2 σ := by
  have hn : ∀ b : Bool, ¬ (xt.tcbSchedContext ≠ none ∧ xd.tcbSchedContext = none ∧ b = true) := by
    intro b h; rcases hsc with h' | h'
    · exact h.1 h'
    · exact h' h.2.1
  unfold replyPush
  simp only [nd_bind_one (getTcbObjRef_eq _ hkt), nd_bind_one (getTcbObjRef_eq _ hkd),
    nd_when_false (hn b1), nd_when_false (hn b2)]

/-- Two writes of `p` around a write of `q ≠ p`. -/
theorem updK3_eq (σ0 : State Unit) (p q : ObjRef) (o1 o2 o3 : KernelObject) (hpq : p ≠ q) :
    Notif.updK (Notif.updK (Notif.updK σ0 p o1) q o2) p o3 = Notif.updK (Notif.updK σ0 q o2) p o3 := by
  simp only [Notif.updK]
  congr 1
  rw [Function.update_comm hpq, Function.update_idem]

/-- The spec's `receive_ipc` from a waiting sender `sd` calling or faulted
(after the transfer, `hcf`) with the grant or grant-reply right and a reply
cap (`hyes`), the receiver's bound notification as in `receiveIpc_send_eqB`:
the push (`hP`, for any `can_donate`). -/
theorem receiveIpc_sendPush_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) {xt : Tcb}
    (hkt : σ.kheap t = some (.tcb xt))
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))) {q : List ObjRef}
    (hk : σ.kheap e = some (.endpoint (.sendEP (sd :: q)))) {xs : Tcb} (hks : σ.kheap sd = some (.tcb xs))
    (hse : sd ≠ e) {dd : SenderPayload} (hst : xs.tcbState = .blockedOnSend e dd)
    (hyes : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ reply ≠ none) {σ2 σ3 : State Unit}
    (hT : doIpcTransfer (Z := Unit) sd (some e) dd.senderBadge dd.senderCanGrant t
      (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))) = ({((), σ2)}, False))
    (hA : specSporadicAssert sd σ2 = ({((), σ3)}, False))
    {xs3 : Tcb} (hks3 : σ3.kheap sd = some (.tcb xs3)) (hcf : dd.senderIsCall = true ∨ xs3.tcbFault ≠ none)
    {σ' : State Unit} (hP : ∀ r, reply = some r → ∀ bd, replyPush (Z := Unit) sd t r bd σ3 = ({((), σ')}, False)) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) blk rc' σ = ({((), σ')}, False) := by
  have hks1 : (updK σ e (.endpoint (epDeq (.sendEP (sd :: q)) sd))).kheap sd = some (.tcb xs) := by
    simp [hse, hks]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · exact absurd rfl hyes.2
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
      rw [if_pos hcf, if_pos hyes]
      rw [nd_bind_one (getTcbObjRef_eq _ hks3), nd_pure_bind']
      exact hP r rfl _

end SpecP

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **An object covered at the state leaves the dead set** (XTopJointRestart's
`JAtZ.undead` from the cover facts). -/
theorem JAtZ.undeadC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {e : U64}
    (hth : ∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1))
    (hH : ∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits))
    (hez : Z.th e ≠ some .tcb) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst (D \ {e}) s a σ := by
  have hw : P1.WritesIn st s s (TFoot st Z.T Z.N Z.C Z.c s σ) := P1.WritesIn.refl _ _
  have hK : ScTKw (fun _ => False) σ σ := ScTKw.refl _ σ
  exact { J with
    jcov := J.jcov.undead hth hH
    kern := J.sc_kern hw hK (FK.refl σ) J.xtop rfl Set.sdiff_subset
    zD := fun q hq => ⟨J.zD q hq, fun (eq : q = e) => hez (eq ▸ J.ztcb_tcb hq)⟩ }

/-- The reply argument of a receive is no TCB of the typed heap (null: `H 0`
is empty; a reply: `H` holds a reply there). -/
theorem JAtZ.replyArg_ntcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {m : U64 → U64}
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R m rc rc' rv) :
    Z.th rv ≠ some .tcb := fun h => by
  have hT := J.zH.1 rv (J.thT rv h)
  rcases hrc with ⟨-, -, rfl⟩ | ⟨b, r', -, -, hr, -⟩
  · rw [J.kern.h0] at hT; cases hT
  · rw [J.zH.2.2.1 rv hr] at hT; cases hT

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an `RSFr` step and a step keeping them**
(`JAtZ.deadP_rsfr` with the dead objects of the state after kept from the
middle state, `hkq`, as XTopJointSendCall's `JAtZ.deadP_dfrCI`). -/
theorem JAtZ.deadP_rsfrC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t r : Fl4Spec.ObjRef} {s3 : S}
    {σa σ3 : Fl4Spec.State Unit} (F : RSFr t r σ σa) (hkq : ∀ q ∈ D, σ3.kheap q.bv = σa.kheap q.bv)
    (hidl : σ3.idleThread = σ.idleThread) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_)
    (fun x hx => by rw [hkq q hq]; exact ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => by rw [hkq q hq]; exact ⟨x, F.replyF hx, rfl⟩)
    (fun x n hx => by
      rw [hkq q hq]; obtain ⟨rf, h1, -⟩ := F.scF hx; exact ⟨_, h1, Or.inl rfl, Or.inl rfl⟩)
    (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK) hidl hAS hY3 (hYK.dk q.bv) hd
  · rw [hkq q hq]
    obtain ⟨st', ar, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
    show st' = x.tcbState
    rcases hs.2 with e | ⟨e, -⟩
    · exact e
    · exact absurd e (ht q hq)
  · rw [hkq q hq]
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | ⟨-, hm⟩
    · exact hy
    · exfalso
      obtain ⟨e', he', e⟩ := J.obj.ep q.bv x hx
      have heq : e' = q := P1.eq_of_bv e
      subst heq
      have d2 := hd.2.1 (J.zH.2.1 e' he')
      obtain ⟨x', hk', hO⟩ := J.xtop.ipc.toE.ep e' he'
      rw [hx] at hk'; cases hk'
      rw [epState_eq] at d2
      cases x with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hm
      | sendEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
      | recvEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)

set_option maxHeartbeats 8000000 in
/-- **XTopJointSendPush's `JAtZ.wake_postGR` with an `RSFr` frame first**
(module docstring): the frame `σ → σa` by `RSFr` (replies kept), then a step
`σa → σ'` that may bind a free reply. -/
theorem JAtZ.rsfr_postGR (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σa σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : RSFr n t σ σa) (G : SkD σa σ') (hks1 : KSub σa σ') (hsz1 : SzKeep σa σ') (hyk1 : YKeep σa σ')
    (hmk1 : McpKeep σa σ')
    (hbk1 : ∀ p x, σa.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer)
    (hrb1 : ∀ d ∈ Z.R, RecvB σ' d → RecvB σa d) (hkz1 : KSz σa σ') (hkb1 : KBack σa σ') (hfk1 : IpcFrKeep σa σ')
    (hck1 : (∀ q y n, σa.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σa.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σa.kheap p = some (.schedContext x0 n)))
    (hfree1 : ∀ d ∈ Z.R, Free σ' d → Free σa d)
    (hao1 : ∀ q ao, σa.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao))
    (hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv)
    (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') (hrun3 : CurRunM σ')
    (hown3 : CurOwnW Z.T Z.C σ') (hoff3 : OffOK σ') (hnsc3 : NSC Z.N Z.C σ') (hiso3 : IpcSorted σ')
    (ht : ∀ q ∈ D, q.bv ≠ n) :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig)
    (F.ksub.trans hks1) hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck0 := F.callKeep
  have ck : (∀ q y n, σ.kheap q = some (.schedContext y n) → ∃ y', σ'.kheap q = some (.schedContext y' n) ∧
      y'.scReplies = y.scReplies) ∧
      (∀ q x, σ.kheap q = some (.reply x) → ∃ x', σ'.kheap q = some (.reply x') ∧ x'.replySc = x.replySc) ∧
      (∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)) := by
    refine ⟨fun q y n hq => ?_, fun q x hq => ?_, fun p x n hp => ?_⟩
    · obtain ⟨y', h1, h2⟩ := ck0.1 q y n hq
      obtain ⟨y'', h1', h2'⟩ := hck1.1 q y' n h1
      exact ⟨y'', h1', h2'.trans h2⟩
    · obtain ⟨x', h1, h2⟩ := ck0.2.1 q x hq
      obtain ⟨x'', h1', h2'⟩ := hck1.2.1 q x' h1
      exact ⟨x'', h1', h2'.trans h2⟩
    · obtain ⟨x0, h0⟩ := hck1.2.2 p x n hp
      exact ck0.2.2 p x0 n h0
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy', hyt⟩ := hfree1 d hd hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy', hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hidl0 : σ'.idleThread = σ.idleThread := G.idle.trans F.sk.idle
  have hisc0 : σ'.idleSc = σ.idleSc := G.isc.trans F.sk.isc
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q :=
    J.deadP_rsfrC F hkq hidl0 hS3 hIR.1 hw k3 hAI3.1
      (J.yld.frame k2 (F.ykeep.trans hyk1)) (F.ykeep.trans hyk1) ht
  have hsz : SzKeep σ σ' := fun p y n hp => by
    obtain ⟨y0, hy0⟩ := hsz1 p y n hp
    exact F.szKeep p y0 n hy0
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hsz q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 hidl0 hisc0).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 (G.ct.trans F.sk.ct) (G.csc.trans F.sk.csc)
    (fun sl h => Or.inl (by rw [← F.sk.orig, ← G.orig]; exact h))
    (by rw [G.arch, F.sk.arch])
    (fun q ao h => hao1 q ao (F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)))
    hDbg (D' := D)
  have hRR' : RRecv (L.mem s') Z.R σ' := fun d hd hr => by
    obtain ⟨h1, h2⟩ := J.rrecv d hd (F.khrb.recvB (hrb1 d hd hr))
    exact ⟨(k4 d hd).2.trans h1, (k4 d hd).1.trans h2⟩
  have hbuf : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer :=
    fun p x hp => by
      obtain ⟨y, hy, e⟩ := F.bufKeep p x hp
      obtain ⟨z, hz, e'⟩ := hbk1 p y hy
      exact ⟨z, hz, e'.trans e⟩
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 (F.ykeep.trans hyk1),
      J.mcp.frame k1 (F.mcpKeep.trans hmk1), J.buf.frame kb hbuf, hRP',
      J.apart.sc_frame hks hsz, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hidl0 hisc0), hkern,
      J.cnW_utc hw hF.1 (G.cdt.trans F.sk.cdt) (G.orig.trans F.sk.orig) (G.arch.trans F.sk.arch) hDbg,
      hnsc3, I3, hcur3, hown3, hoff3, hAI3, B3, hiso3, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 (F.ksz.trans hkz1)
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) (G.arch.trans F.sk.arch)
    (fun q ao h => hao1 q ao (F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)))
    hsz hF.1 (F.kback.trans' hkb1) (F.ipcFr.trans hfk1) hC R hKd (G.orig.trans F.sk.orig) (J.idleW_keep hS3 hidl0 hisc0).1 J.zD⟩

set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a faulted head sender pushing a reply at `J`**
(module docstring): the sender holds a fault (a timeout only without an SC),
has the grant or grant-reply right, the receiver passes a reply object
(covered, `hcovR`), at a resumed entry; for any FL4 program `m` reducing to
the endpoint-state switch. -/
theorem JAtZ.recvSendFPJG (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) {f : Fl4Spec.Fault}
    (hft : xs.tcbFault = some f) (hto : ∀ b, f = .timeout b → xs.tcbSchedContext = none)
    (hAct : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue ∧ xs.tcbSchedContext = none))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hyes : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hrn : rc ≠ .Null)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
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
  have J := J.undeadC hcovR.1 hcovR.2 (J.replyArg_ntcb hrc)
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
  -- the transfer: the fault (XTopJointXferF's `xferFaultStepGJ`, on `IRel`)
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hks1 : σ1.kheap sd'.bv = some (.tcb xs) := by simp [σ1, hse, hks]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by simp [σ1]
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  have hth : Z.th t = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkt
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hUt := J.rbufU ht hth hkt
  have hok : FaultOK (L := L) s1 sd' xs f := by
    cases f with
    | timeout b0 =>
      have hsc := hto b0 rfl
      obtain ⟨Q, R0, -, hsp⟩ := hS1.1.1.2.1.lists
      obtain ⟨x, hk', -, -, hscw, -⟩ := hsp.tcb sd' hsT
      rw [hks1] at hk'; cases hk'
      exact ⟨hsc, optRef_none (hscw.symm.trans hsc)⟩
    | _ => trivial
  refine WP.spec_bind (xferFaultStepGJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) hsT ht (Ne.symm hts) hks1 hkt1 hft hok e bdg (i != 0#u64)
    hTP htH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUt b hb).1.ksb hW1.1, (hUt b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) t.bv (.tcb x2) with hσ2
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by simp [σ2]
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by simp [σ2, hst', hks1]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    simp [σ2, Ne.symm hte, hk1e]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 ht hA2 (fun p hp => by simp [σ2, hp]) hkt1 hkt2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xt b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  -- the spec frame from `σ`
  have Fr1 : RSFr sd'.bv t.bv σ σ1 := RSFr.upd hk (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv (Endp.setUm σ1 um2) σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := Endp.setUm σ1 um2) hkt1 x2.tcbArch
    rw [← hx2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σ σ2 := (Fr1.trans (RSFr.um _ _ σ1 um2)).trans Fr2c
  have IK1 : IK sd'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hk
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σ σ1 := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans
    (IK.updTcb (σ := Endp.setUm σ1 um2) hkt1 (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2])))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((Fl4Proofs.P3.SKeep.um σ1 um2).trans (Ipc.SKeep.updK (σ := Endp.setUm σ1 um2) (p := t.bv)
    (o := .tcb x2) (fun y' h => ⟨xt, hkt1, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h)))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => J.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
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
  rintro ft hft'
  have hftB : (ft != fl4_abi.consts.fault.NullFault) = true := by
    rw [hft']
    have hne : L.mem s3 (tFaultA sd') ≠ fl4_abi.consts.fault.NullFault := fun e => by
      have := hxs3.fault0.1 (by rw [e]; unfold fl4_abi.consts.fault.NullFault; rfl); rw [hft] at this; cases this
    simpa using hne
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
      (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide)  -- the sender is in no ready or release queue
  have hnqS : NotQueued σ sd'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  -- the receiver: current, with the current SC (so no donation)
  have hA0 := hAct
  have hCI : σ.schedulerAction = .resumeCurThread → CurInv σ := fun hres =>
    J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnd : xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none := by
    rcases hA0 with hres | ⟨-, -, h⟩
    · obtain ⟨xc, hkc, hcs, -⟩ := (hCI hres).tcb
      rw [hct, hkt] at hkc; cases hkc; exact Or.inr (by rw [hcs]; simp)
    · exact Or.inl h
  have hnrT : t.bv ∉ σ.releaseQueue := by
    rcases hA0 with hres | ⟨-, h, -⟩
    · rw [← hct]; exact (hCI hres).notRel
    · exact h
  have hsw : ∀ u, σ.schedulerAction ≠ .switchThread u := fun u h => by
    rcases hA0 with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
  have hnqT : ∀ dm p, t.bv ∉ σ.readyQueues dm p := by rw [← hct]; exact hnq
  -- the frames to `σ3`
  have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
    · exact RSFr.refl _ _ _
    · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
        (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
  have Fr23 : RSFr sd'.bv t.bv σ σ3 := Fr2.trans Fr3
  have hrq3 : σ3.readyQueues = σ.readyQueues := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]; exact IK2.2.1
    · rw [h]; exact IK2.2.1
  -- the reply
  have hgg := hyes _ _ hstd
  obtain ⟨wb, r', hrcw, hrc'w, hwR, hw0s⟩ : ∃ b r', rc = .Reply rv b ∧ rc' = .replyCap rv.bv r' ∧ rv ∈ Z.R ∧
      L.mem s (Endp.rTcbA rv) = 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | h
    · exact absurd h1 hrn
    · exact h
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hwR
  have hxr0 : xr.replyTcb = none := by rw [hxr, hw0s, optRef_zero]
  have hkr3 : σ3.kheap rv.bv = some (.reply xr) := Fr23.replyF hkr
  have hkt3 : σ3.kheap t.bv = some (.tcb x2) := hk3 _ _ hkt2 (fun _ _ h => by cases h)
  have hsc2 : x2.tcbSchedContext = xt.tcbSchedContext := by rw [hx2]
  have hws : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  -- P1's facts at `s3`
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hIR3.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have bits3 : ∀ u ∈ Z.T, (∀ dm p, u.bv ∉ σ.readyQueues dm p) → u.bv ∉ σ.releaseQueue →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hq hr
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hq 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [← hrq3, hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hr
      rw [← Fr23.sk.rel, hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbS, hrbS⟩ := bits3 sd' hsT hnqS.1 hnqS.2
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT hnrT
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu =>
    actionW_ne_of hSR3 hu (fun h => hsw _ (act3.symm.trans h))
  have hidl3 : σ3.idleThread = σ.idleThread := Fr23.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hni
  have his : sd'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hks] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA sd') ≠ 0#u64 → L.mem s3 (P1.scA sd') ∈ Ac := fun h0 =>
    hB3.sact sd' hsH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hst3))))))) h0
  have hcold : L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide,
      by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide⟩
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hwH : rv ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : rv ≠ 0#u64 := (J.rp.align rv hwR).2.1
  have hz3 : L.mem s3 (P1.rTcbA rv) = 0#u64 := by
    obtain ⟨xr', hkr', hrl⟩ := hR3.reply rv hwR
    rw [hkr3] at hkr'; cases hkr'
    exact optRef_none (hrl.symm.trans hxr0)
  have hns3 : tsCode xs.tcbState ≠ 6 := by rw [hstd]; simp [tsCode]
  have hSM := ScRelM.of hIR3.1
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM t ht
  rw [hkt3] at hkd3'; cases hkd3'
  obtain ⟨xs3', hks3', hssc⟩ := hSM sd' hsT
  rw [hks3] at hks3'; cases hks3'
  have hscw : L.mem s3 (P1.scA sd') = 0#u64 ∨ L.mem s3 (P1.scA t) ≠ 0#u64 := by
    rcases hnd with h | h
    · exact Or.inl (optRef_none (hssc.symm.trans h))
    · exact Or.inr fun h0 => h (by rw [← hsc2, hdsc, h0, optRef_zero])
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA rv) sd') (fun b => b.val = rv.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 sd'
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
  -- the push on `IRel`, at P1
  have hPush : ∀ cd : Bool, (cd = false ∨ L.mem s3 (P1.scA t) ≠ 0#u64) → ipc.reply_push st arI s3 a sd' t rv cd ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv rv.bv cd σ3 = ({((), pushSt σ3 sd'.bv rv.bv xr xs)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 sd'.bv rv.bv xr xs) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 sd'.bv rv.bv xr xs) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA rv) sd') sd' rv = ok r.1 ⦄ := by
    intro cd hcd
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := cd) (P := fun s' σ' => σ' = pushSt σ3 sd'.bv rv.bv xr xs ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 hns3 hwR hkr3 (fun _ => ht)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hd _ _ _ _ _ _ _ h9 => hcd.elim (fun e => by rw [e] at hd; cases hd)
          (fun h => (h (by rw [hdsc] at h9; exact optRef_none h9)).elim)))
      (P1.ipc.reply_push.ipc hAT s3 a sd' t rv cd Q0 R0 h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hqbT hrbT (hna3 t ht)
        (hiw3 t ht hit) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a sd' t rv cd h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hcA hcd)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, -, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hf, hsb⟩
  have hrv0 : (rv != 0#u64) = true := by simpa using hw00
  suffices HH : ∀ cd : Bool, (cd = false ∨ L.mem s3 (P1.scA t) ≠ 0#u64) → ipc.reply_push st arI s3 a sd' t rv cd ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    have HH' : (do
        let i3 ← obj.Tcb.sc st sd' s3
        let can_donate ← if i3 != 0#u64 then ok (ft != fl4_abi.consts.fault.Timeout) else ok false
        ipc.reply_push st arI s3 a sd' t rv can_donate) ⦃ r =>
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s3 sd') ?_
      rintro i3 hi3
      by_cases h3' : (i3 != 0#u64) = true
      · rw [if_pos h3']
        refine ok_bind_spec _ _ (HH _ (hscw.elim (fun h => ?_) Or.inr))
        rw [← hi3] at h; simp [h] at h3'
      · rw [if_neg h3']; exact ok_bind_spec _ _ (HH _ (Or.inl rfl))
    rcases Bool.eq_false_or_eq_true dd.senderCanGrant with hG | hG
    · by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hrv0, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
    · have hGR : dd.senderCanGrantReply = true := hgg.resolve_left (by rw [hG]; decide)
      by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
  intro cd hcd
  refine WP.spec_mono (hPush cd hcd) ?_
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, hblk, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 hblk fu4 hsb4 ⊢
  subst ha4
  -- the footprints
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 hsT hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hks2b : L.ksb s2 = L.ksb s := hW2.1
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
  have hks3b : L.ksb s3 = L.ksb s := hW3'.1
  have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3b (SzKeepC.of Fr23.szKeep) hb))
  have hfoot := footW_trans (footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)) (footW_of fu4)
  -- the sender `Inactive` (a spec state only): `Inv` there, as in `recvSendFJG`
  set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
  have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σ.curThread; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  have Fr5 : RSFr sd'.bv t.bv σ σ5 := Fr23.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩))
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σ σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σ σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : RelIfBound σ5' sd'.bv := by
    by_cases htf : ∃ b0, f = .timeout b0
    · obtain ⟨b0, rfl⟩ := htf
      intro y scp z n hy hscp
      rw [hk5'] at hy
      simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hy
      subst hy
      rw [hx5] at hscp
      simp [hto b0 rfl] at hscp
    · have hnt : ∀ b', xs.tcbFault ≠ some (.timeout b') := fun b' h =>
        htf ⟨b', Option.some.inj (hft.symm.trans h)⟩
      exact Ipc.RelIfBound.of_keep (J.inv.rd sd'.bv xs hks (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
        fun b' h => hnt b' h⟩)))) SK5'
  have I5' : Inv σ5' := ((J.inv.toBut sd'.bv).ik hnqS IK5').1.inv fun _ _ _ => hrib
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
      exact hnqS.2 (by rw [← SK5'.1]; exact hu)
  have act5 : σ5.schedulerAction = σ.schedulerAction := by
    rw [hσ5, stsAct_ne hsc3]; exact act3
  -- the push from `σ5`
  have e5 : σ5 = Notif.updK σ3 sd'.bv (.tcb x5) := stsAct_ne hsc3
  have hkta : σ5.kheap sd'.bv = some (.tcb x5) := by rw [e5]; simp [Notif.updK]
  have hkwa : σ5.kheap rv.bv = some (.reply xr) := by rw [e5]; simp [Notif.updK, hws, hkr3]
  have heqP : pushSt σ3 sd'.bv rv.bv xr xs = pushSt σ5 sd'.bv rv.bv xr x5 := by
    rw [e5]; unfold pushSt; rw [updK3_eq σ3 sd'.bv rv.bv _ _ _ (Ne.symm hws)]; try rfl
  set σ' := pushSt σ5 sd'.bv rv.bv xr x5 with hσ'
  have G' := (ps_skD (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5))
  have hnqSa : ∀ dm p, sd'.bv ∉ σ5.readyQueues dm p := by
    rw [e5]; show ∀ dm p, sd'.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqS.1
  have hnrSa : sd'.bv ∉ σ5.releaseQueue := by rw [Fr5.sk.rel]; exact hnqS.2
  have I6 : Inv σ' := ps_inv hkta hkwa hws I5 hnqSa hnrSa
  have hscA : ∀ p y n, σ5.kheap p = some (.schedContext y n) → y.scTcb = some sd'.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨y0, hy0, ey, -⟩ := Fr5.scB hp
    rw [ey]
    exact J.bsa.tcb p y0 n sd'.bv xs hy0 (by rw [ey] at hyt; exact hyt) hks (by rw [hstd]; rfl)
  have B6 : BlockedScActive σ' := ps_bsa hkta hkwa hws hscA (Fr5.bsa J.bsa)
  have hcne1 : σ5.curThread ≠ sd'.bv := by rw [Fr5.sk.ct, hct]; exact Ne.symm hst'
  have hcne2 : σ5.curThread ≠ rv.bv := by rw [Fr5.sk.ct, hct]; exact Ne.symm hwt
  have hactP : σ'.schedulerAction = σ.schedulerAction := by
    show (pushSt σ5 sd'.bv rv.bv xr x5).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (by show sd'.bv ≠ σ5.curThread; exact Ne.symm hcne1)]
    exact act5
  have hidT : σ5.idleThread ≠ sd'.bv := by rw [Fr5.sk.idle]; exact fun e0 => his e0.symm
  have hAI6 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hactP] at hu; exact absurd hu (hsw u)), ps_idleOK hkta hkwa hws hidT (Fr5.idleOK J.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases hA0 with hres | ⟨hcn, -⟩
    swap
    · exact Or.inl (hactP.trans hcn)
    have hCIa : CurInv σ5 := Fr5.curInv (hCI hres)
    refine Or.inr ?_
    obtain ⟨⟨xc, hkc, hcs, hnb'⟩, ⟨y0, n0, hky0⟩, hact0, hnr0⟩ := hCIa
    have hsne1 : σ5.curSc ≠ sd'.bv := kheap_ne hky0 hkta (fun _ h1 h2 => by subst h1; cases h2)
    have hsne2 : σ5.curSc ≠ rv.bv := kheap_ne hky0 hkwa (fun _ h1 h2 => by subst h1; cases h2)
    refine ⟨⟨xc, ?_, ?_, hnb'⟩, ⟨y0, n0, ?_⟩, ?_, ?_⟩
    · rw [G'.ct, ps_ko hcne1 hcne2]; exact hkc
    · rw [G'.csc]; exact hcs
    · rw [G'.csc, ps_ko hsne1 hsne2]; exact hky0
    · intro hne x n hx
      rw [G'.csc, ps_ko hsne1 hsne2] at hx
      rw [G'.csc, G'.isc] at hne
      exact hact0 hne x n hx
    · rw [G'.ct, ps_rel]; exact hnr0
  have hrun6 : CurRunM σ' := by
    rcases hA0 with hres | ⟨hcn, -⟩
    swap
    · exact Or.inl (by rw [hactP, hcn]; intro h; cases h)
    have hrun5 : CurRunW σ5 := Fr5.curRunW (J.curRun.resolve_left fun e0 => e0 hres)
    exact Or.inr (by
      rcases hrun5 with h | h
      · refine Or.inl fun y hy => h y ?_
        rw [G'.ct, ps_ko hcne1 hcne2] at hy; exact hy
      · exact Or.inr (by rw [G'.ct, G'.idle]; exact h))
  -- back to `JAtZ`
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX ht hth hkt hW4' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hsT hks (by rw [hstd]; simp [tsCode])
  have hF : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have hIR4 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s4 σ' := by
    rw [← heqP]; exact IpcRel.ofSRN hR4 hS4
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σ5.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hws h1 h2
  have hkq : ∀ q ∈ D \ {rv}, σ'.kheap q.bv = σ5.kheap q.bv := fun q hq =>
    ps_ko (htD q hq) (fun e0 => hq.2 (P1.eq_of_bv e0))
  obtain ⟨V', J6⟩ := Ju.rsfr_postGR hIR4 hF hWu hblk hFu (RSFr.ofUm Fr5 umu) ps_skD
    (ps_ksub hkta hkwa hws) (ps_szKeep hkta hkwa hws) (ps_ykeep hkta hkwa hws) (ps_mcpKeep hkta hkwa hws)
    (ps_bufKeep hkta hkwa hws) (fun d _ h => ps_recvB hkta hkwa hws h) (ps_ksz hkta hkwa hws)
    (ps_kback hkta hkwa hws) (ps_ipcFr hkta hkwa hws) (ps_ck hkta hkwa hws) (fun d _ h => ps_free hkta hkwa hws h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I6 B6 hAI6 hcur6 hrun6 (ps_own hkta hkwa hws (Fr5.own J.own))
    (ps_off hkta hkwa hws (Fr5.off J.off)) (ps_nsc hkta hkwa hws (Fr5.nsc J.nsc))
    (ps_isorted hkta hkwa hws (Fr5.isorted J.isorted)) htD
  -- the spec's outcome
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hyesS : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none :=
    ⟨by rcases hgg with h | h <;> simp [h], by rw [Notif.optRef_ne hw00]; simp⟩
  have hPS : ∀ r, optRef rv = some r → ∀ bd, Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv r bd σ3 =
      ({((), σ')}, False) := by
    intro r hr bd
    rw [Notif.optRef_ne hw00] at hr
    cases hr
    rw [replyPush_don_irrel hks3 hkt3 (hnd.imp id fun h => by rw [hsc2]; exact h) bd cd, hpush, heqP]
  have hspec := receiveIpc_sendPush_eq b rights blk hsr hkt hbN hk hks hse hstd hyesS e2' hA hks3
    (Or.inr (by rw [hft]; simp)) hPS
  exact ⟨((), σ'), by rw [hspec]; exact Set.mem_singleton _, J6.xtop.relTop, _, _, _, _, _, _, J6⟩


set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a calling head sender (no fault) pushing a reply at
`J`** (module docstring; XTopJointRecvSend's `JAtZ.recvSendJG` up to the
transfer, its intermediate `JAtZ` `Jy` at `σy`): the grant or grant-reply
right, a reply object (covered, `hcovR`), at a resumed entry. -/
theorem JAtZ.recvSendPJG (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hAct : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue ∧ xs.tcbSchedContext = none))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hcl0 : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true)
    (hyes : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) (hrn : rc ≠ .Null)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
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
  have J := J.undeadC hcovR.1 hcovR.2 (J.replyArg_ntcb hrc)
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
  rintro s2 ⟨x2, um2, y, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksb, hKy, hCnKy, hyk⟩
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
  have hcl : dd.senderIsCall = true := hcl0 _ _ hstd
  have hsay : σy.schedulerAction = σ.schedulerAction := by
    have e := congrArg Fl4Spec.AbstractState.schedulerAction hCnKy.1; exact e
  have hidy : σy.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hCnKy.1; exact e
  have hrqy : σy.readyQueues = σ.readyQueues := by
    have e := congrArg Fl4Spec.AbstractState.readyQueues hCnKy.1; exact e
  -- the sender is in no ready or release queue
  have hnqS : NotQueued σy sd'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rq dm p _ hm
      rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := Jy.inv.rel _ hm
      rw [hksy] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  -- the receiver: current, with the current SC (so no donation)
  have hA0 : σy.schedulerAction = .resumeCurThread ∨
      (σy.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue ∧ xs.tcbSchedContext = none) := by
    rw [hsay]; exact hAct
  have hcty' : σy.curThread = t.bv := hcty.trans hct
  have hCI : σy.schedulerAction = .resumeCurThread → CurInv σy := fun hres =>
    Jy.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hrly : σy.releaseQueue = σ.releaseQueue := by
    have e := congrArg Fl4Spec.AbstractState.releaseQueue hCnKy.1; exact e
  have hnd : xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none := by
    rcases hA0 with hres | ⟨-, -, h⟩
    · obtain ⟨xc, hkc, hcs, -⟩ := (hCI hres).tcb
      rw [hcty', hkty] at hkc; cases hkc; exact Or.inr (by rw [hcs]; simp)
    · exact Or.inl h
  have hnrT : t.bv ∉ σy.releaseQueue := by
    rcases hA0 with hres | ⟨-, h, -⟩
    · rw [← hcty']; exact (hCI hres).notRel
    · rw [hrly]; exact h
  have hsw : ∀ u, σy.schedulerAction ≠ .switchThread u := fun u h => by
    rcases hA0 with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
  have hnqT : ∀ dm p, t.bv ∉ σy.readyQueues dm p := by rw [hrqy, ← hct]; exact hnq
  -- the frames to `σ3`
  have Fr3 : RSFr sd'.bv t.bv σ2 σ3 := by
    rcases hU3 with rfl | ⟨p, y', z, n, -, hkp, -, hpc, rfl, -, -, hz, -⟩
    · exact RSFr.refl _ _ _
    · exact (RSFr.reprog _ _ σ2).trans (RSFr.upd (σ := { σ2 with reprogramTimer := true }) hkp
        (Or.inr (Or.inl ⟨y', n, z.scRefills, rfl, by rw [← hz], hpc⟩)))
  have Fr23 : RSFr sd'.bv t.bv σy σ3 := Fr2.trans Fr3
  have hrq3 : σ3.readyQueues = σy.readyQueues := by
    rcases hU3 with h | ⟨_, _, _, _, -, -, -, -, h, -⟩
    · rw [h]; exact IK2.2.1
    · rw [h]; exact IK2.2.1
  -- the reply
  have hgg := hyes _ _ hstd
  obtain ⟨wb, r', hrcw, hrc'w, hwR, hw0s⟩ : ∃ b r', rc = .Reply rv b ∧ rc' = .replyCap rv.bv r' ∧ rv ∈ Z.R ∧
      L.mem s (Endp.rTcbA rv) = 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | h
    · exact absurd h1 hrn
    · exact h
  obtain ⟨xr, hkr, hxr⟩ := hR.reply rv hwR
  have hxr0 : xr.replyTcb = none := by rw [hxr, hw0s, optRef_zero]
  have hkry : σy.kheap rv.bv = some (.reply xr) := hncn hkr (fun _ _ h0 => by cases h0)
  have hkr3 : σ3.kheap rv.bv = some (.reply xr) := Fr23.replyF hkry
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by simp [σ2]
  have hkt3 : σ3.kheap t.bv = some (.tcb x2) := hk3 _ _ hkt2 (fun _ _ h => by cases h)
  have hsc2 : x2.tcbSchedContext = xt.tcbSchedContext := by rw [hx2]
  have hws : rv.bv ≠ sd'.bv := kheap_ne hkr hks (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : rv.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  -- P1's facts at `s3`
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hIR3.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have bits3 : ∀ u ∈ Z.T, (∀ dm p, u.bv ∉ σy.readyQueues dm p) → u.bv ∉ σy.releaseQueue →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hq hr
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hq 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [← hrq3, hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hr
      rw [← Fr23.sk.rel, hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbS, hrbS⟩ := bits3 sd' hsT hnqS.1 hnqS.2
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT hnrT
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu =>
    actionW_ne_of hSR3 hu (fun h => hsw _ (act3.symm.trans h))
  have hidl3 : σ3.idleThread = σy.idleThread := Fr23.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σy.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σy.idleThread := by rw [hidy, ← hct]; exact hni
  have his : sd'.bv ≠ σy.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := Jy.act.2
    rw [← h, hksy] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA sd') ≠ 0#u64 → L.mem s3 (P1.scA sd') ∈ Ac := fun h0 =>
    hB3.sact sd' hsH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hst3))))))) h0
  have hcold : L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (P1.stA sd') ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4]; unfold sched.TS_BLOCKED_ON_REPLY; decide,
      by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide⟩
  have hRe : Z.R = P1.Heap.replies H := Jy.tcbs_eq.2
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hwH : rv ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : rv ≠ 0#u64 := (Jy.rp.align rv hwR).2.1
  have hz3 : L.mem s3 (P1.rTcbA rv) = 0#u64 := by
    obtain ⟨xr', hkr', hrl⟩ := hR3.reply rv hwR
    rw [hkr3] at hkr'; cases hkr'
    exact optRef_none (hrl.symm.trans hxr0)
  have hns3 : tsCode xs.tcbState ≠ 6 := by rw [hstd]; simp [tsCode]
  have hSM := ScRelM.of hIR3.1
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM t ht
  rw [hkt3] at hkd3'; cases hkd3'
  obtain ⟨xs3', hks3', hssc⟩ := hSM sd' hsT
  rw [hks3] at hks3'; cases hks3'
  have hscw : L.mem s3 (P1.scA sd') = 0#u64 ∨ L.mem s3 (P1.scA t) ≠ 0#u64 := by
    rcases hnd with h | h
    · exact Or.inl (optRef_none (hssc.symm.trans h))
    · exact Or.inr fun h0 => h (by rw [← hsc2, hdsc, h0, optRef_zero])
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA rv) sd') (fun b => b.val = rv.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 sd'
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hXc : P1.ExcT {y' | y' ∈ (∅ : Set U64) ∨ y' = sd'} sd' := fun y' hy' => by simpa using hy'
  -- the push on `IRel`, at P1
  have hPush : ∀ cd : Bool, (cd = false ∨ L.mem s3 (P1.scA t) ≠ 0#u64) → ipc.reply_push st arI s3 a sd' t rv cd ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv rv.bv cd σ3 = ({((), pushSt σ3 sd'.bv rv.bv xr xs)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 sd'.bv rv.bv xr xs) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 sd'.bv rv.bv xr xs) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA rv) sd') sd' rv = ok r.1 ⦄ := by
    intro cd hcd
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := cd) (P := fun s' σ' => σ' = pushSt σ3 sd'.bv rv.bv xr xs ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 hsT hks3 hkt3 hq3 hns3 hwR hkr3 (fun _ => ht)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hd _ _ _ _ _ _ _ h9 => hcd.elim (fun e => by rw [e] at hd; cases hd)
          (fun h => (h (by rw [hdsc] at h9; exact optRef_none h9)).elim)))
      (P1.ipc.reply_push.ipc hAT s3 a sd' t rv cd Q0 R0 h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hqbT hrbT (hna3 t ht)
        (hiw3 t ht hit) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a sd' t rv cd h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hcA hcd)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, -, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hf, hsb⟩
  have hrv0 : (rv != 0#u64) = true := by simpa using hw00
  suffices HH : ∀ cd : Bool, (cd = false ∨ L.mem s3 (P1.scA t) ≠ 0#u64) → ipc.reply_push st arI s3 a sd' t rv cd ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    have HH' : (do
        let i3 ← obj.Tcb.sc st sd' s3
        let can_donate ← if i3 != 0#u64 then ok (ft != fl4_abi.consts.fault.Timeout) else ok false
        ipc.reply_push st arI s3 a sd' t rv can_donate) ⦃ r =>
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s3 sd') ?_
      rintro i3 hi3
      by_cases h3' : (i3 != 0#u64) = true
      · rw [if_pos h3']
        refine ok_bind_spec _ _ (HH _ (hscw.elim (fun h => ?_) Or.inr))
        rw [← hi3] at h; simp [h] at h3'
      · rw [if_neg h3']; exact ok_bind_spec _ _ (HH _ (Or.inl rfl))
    rcases Bool.eq_false_or_eq_true dd.senderCanGrant with hG | hG
    · simp only [hc, hcl, hg, hG, hrv0, ↓reduceIte]; exact HH'
    · have hGR : dd.senderCanGrantReply = true := hgg.resolve_left (by rw [hG]; decide)
      simp only [hc, hcl, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
  intro cd hcd
  refine WP.spec_mono (hPush cd hcd) ?_
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, hblk, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 hblk fu4 hsb4 ⊢
  subst ha4
  -- the footprints
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 hsT hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hks2b : L.ksb s2 = L.ksb y := hW2.1
  have hW3' : P1.WritesIn st y s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
  have hks3b : L.ksb s3 = L.ksb y := hW3'.1
  have hW4' : P1.WritesIn st y s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c y σy b ∨ RcvBufW xt b) :=
    hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3b (SzKeepC.of Fr23.szKeep) hb))
  have hfoot := footW_trans (footW_trans F2 (footW_of fu3)) (footW_of fu4)
  -- the sender `Inactive` (a spec state only): `Inv` there, as in `recvSendFJG`
  set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
  have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σy.curThread; rw [hcty]; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  have Fr5 : RSFr sd'.bv t.bv σy σ5 := Fr23.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩))
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σy σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σy σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : RelIfBound σ5' sd'.bv :=
    Ipc.RelIfBound.of_keep (Jy.inv.rd sd'.bv xs hksy (Or.inr (Or.inr (Or.inl ⟨_, _, hstd,
      fun b' h => by rw [hfs] at h; cases h⟩)))) SK5'
  have I5' : Inv σ5' := ((Jy.inv.toBut sd'.bv).ik hnqS IK5').1.inv fun _ _ _ => hrib
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
      exact hnqS.2 (by rw [← SK5'.1]; exact hu)
  have act5 : σ5.schedulerAction = σy.schedulerAction := by
    rw [hσ5, stsAct_ne hsc3]; exact act3
  -- the push from `σ5`
  have e5 : σ5 = Notif.updK σ3 sd'.bv (.tcb x5) := stsAct_ne hsc3
  have hkta : σ5.kheap sd'.bv = some (.tcb x5) := by rw [e5]; simp [Notif.updK]
  have hkwa : σ5.kheap rv.bv = some (.reply xr) := by rw [e5]; simp [Notif.updK, hws, hkr3]
  have heqP : pushSt σ3 sd'.bv rv.bv xr xs = pushSt σ5 sd'.bv rv.bv xr x5 := by
    rw [e5]; unfold pushSt; rw [updK3_eq σ3 sd'.bv rv.bv _ _ _ (Ne.symm hws)]; try rfl
  set σ' := pushSt σ5 sd'.bv rv.bv xr x5 with hσ'
  have G' := (ps_skD (σ := σ5) (t := sd'.bv) (w := rv.bv) (xr := xr) (xt := x5))
  have hnqSa : ∀ dm p, sd'.bv ∉ σ5.readyQueues dm p := by
    rw [e5]; show ∀ dm p, sd'.bv ∉ σ3.readyQueues dm p; rw [hrq3]; exact hnqS.1
  have hnrSa : sd'.bv ∉ σ5.releaseQueue := by rw [Fr5.sk.rel]; exact hnqS.2
  have I6 : Inv σ' := ps_inv hkta hkwa hws I5 hnqSa hnrSa
  have hscA : ∀ p y n, σ5.kheap p = some (.schedContext y n) → y.scTcb = some sd'.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨y0, hy0, ey, -⟩ := Fr5.scB hp
    rw [ey]
    exact Jy.bsa.tcb p y0 n sd'.bv xs hy0 (by rw [ey] at hyt; exact hyt) hksy (by rw [hstd]; rfl)
  have B6 : BlockedScActive σ' := ps_bsa hkta hkwa hws hscA (Fr5.bsa Jy.bsa)
  have hcne1 : σ5.curThread ≠ sd'.bv := by rw [Fr5.sk.ct, hcty']; exact Ne.symm hst'
  have hcne2 : σ5.curThread ≠ rv.bv := by rw [Fr5.sk.ct, hcty']; exact Ne.symm hwt
  have hactP : σ'.schedulerAction = σy.schedulerAction := by
    show (pushSt σ5 sd'.bv rv.bv xr x5).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (by show sd'.bv ≠ σ5.curThread; exact Ne.symm hcne1)]
    exact act5
  have hidT : σ5.idleThread ≠ sd'.bv := by rw [Fr5.sk.idle]; exact fun e0 => his e0.symm
  have hAI6 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hactP] at hu; exact absurd hu (hsw u)), ps_idleOK hkta hkwa hws hidT (Fr5.idleOK Jy.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    rcases hA0 with hres | ⟨hcn, -⟩
    swap
    · exact Or.inl (hactP.trans hcn)
    have hCIa : CurInv σ5 := Fr5.curInv (hCI hres)
    refine Or.inr ?_
    obtain ⟨⟨xc, hkc, hcs, hnb'⟩, ⟨y0, n0, hky0⟩, hact0, hnr0⟩ := hCIa
    have hsne1 : σ5.curSc ≠ sd'.bv := kheap_ne hky0 hkta (fun _ h1 h2 => by subst h1; cases h2)
    have hsne2 : σ5.curSc ≠ rv.bv := kheap_ne hky0 hkwa (fun _ h1 h2 => by subst h1; cases h2)
    refine ⟨⟨xc, ?_, ?_, hnb'⟩, ⟨y0, n0, ?_⟩, ?_, ?_⟩
    · rw [G'.ct, ps_ko hcne1 hcne2]; exact hkc
    · rw [G'.csc]; exact hcs
    · rw [G'.csc, ps_ko hsne1 hsne2]; exact hky0
    · intro hne x n hx
      rw [G'.csc, ps_ko hsne1 hsne2] at hx
      rw [G'.csc, G'.isc] at hne
      exact hact0 hne x n hx
    · rw [G'.ct, ps_rel]; exact hnr0
  have hrun6 : CurRunM σ' := by
    rcases hA0 with hres | ⟨hcn, -⟩
    swap
    · exact Or.inl (by rw [hactP, hcn]; intro h; cases h)
    have hrun5 : CurRunW σ5 := Fr5.curRunW (Jy.curRun.resolve_left fun e0 => e0 hres)
    exact Or.inr (by
      rcases hrun5 with h | h
      · refine Or.inl fun y hy => h y ?_
        rw [G'.ct, ps_ko hcne1 hcne2] at hy; exact hy
      · exact Or.inr (by rw [G'.ct, G'.idle]; exact h))
  -- back to `JAtZ`
  have hth : Z.th t = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkt
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs)
    Jy ht hth hkty hW4' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hsT hksy (by rw [hstd]; simp [tsCode])
  have hF : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have hIR4 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s4 σ' := by
    rw [← heqP]; exact IpcRel.ofSRN hR4 hS4
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σ5.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hws h1 h2
  have hkq : ∀ q ∈ D \ {rv}, σ'.kheap q.bv = σ5.kheap q.bv := fun q hq =>
    ps_ko (htD q hq) (fun e0 => hq.2 (P1.eq_of_bv e0))
  obtain ⟨V', J6⟩ := Ju.rsfr_postGR (by rw [← hKy.2.1] at hIR4; exact hIR4) hF hWu hblk hFu (RSFr.ofUm Fr5 umu) ps_skD
    (ps_ksub hkta hkwa hws) (ps_szKeep hkta hkwa hws) (ps_ykeep hkta hkwa hws) (ps_mcpKeep hkta hkwa hws)
    (ps_bufKeep hkta hkwa hws) (fun d _ h => ps_recvB hkta hkwa hws h) (ps_ksz hkta hkwa hws)
    (ps_kback hkta hkwa hws) (ps_ipcFr hkta hkwa hws) (ps_ck hkta hkwa hws) (fun d _ h => ps_free hkta hkwa hws h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I6 B6 hAI6 hcur6 hrun6 (ps_own hkta hkwa hws (Fr5.own Jy.own))
    (ps_off hkta hkwa hws (Fr5.off Jy.off)) (ps_nsc hkta hkwa hws (Fr5.nsc Jy.nsc))
    (ps_isorted hkta hkwa hws (Fr5.isorted Jy.isorted)) htD
  -- the spec's outcome
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hyesS : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none :=
    ⟨by rcases hgg with h | h <;> simp [h], by rw [Notif.optRef_ne hw00]; simp⟩
  have hPS : ∀ r, optRef rv = some r → ∀ bd, Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv r bd σ3 =
      ({((), σ')}, False) := by
    intro r hr bd
    rw [Notif.optRef_ne hw00] at hr
    cases hr
    rw [replyPush_don_irrel hks3 hkt3 (hnd.imp id fun h => by rw [hsc2]; exact h) bd cd, hpush, heqP]
  have hspec := receiveIpc_sendPush_eq b rights blk hsr hkt hbN hk hks hse hstd hyesS e2' hA hks3
    (Or.inl hcl) hPS
  exact ⟨((), σ'), by rw [hspec]; exact Set.mem_singleton _, J6.xtop.relTop, _, _, _, _, _, _, J6⟩


/-- The head senders whose push is proved at `J`: a reply cap, the grant or
grant-reply right, and either calling without a fault (`JAtZ.recvSendPJG`)
or faulted (a timeout only without an SC, `JAtZ.recvSendFPJG`). -/
def PushOK (xs : Fl4Spec.Tcb) (rc : capability.Cap) : Prop :=
  rc ≠ .Null ∧ (∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) ∧
    ((xs.tcbFault = none ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = true) ∨
      ∃ f, xs.tcbFault = some f ∧ ∀ b, f = .timeout b → xs.tcbSchedContext = none)

/-- **`receive_ipc` from the head sender pushing a reply at `J`**, the cases
of `PushOK`, the receiver without a bound notification or with one not
active, polling or not lending its SC (XTopJointRecvSend's `JAtZ.recvPreN`). -/
theorem JAtZ.recvSendP0X (hAT : P0.ArchTotal arI)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : Entered σ) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hok : PushOK xs rc) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
  · exact J.recvSendPJG hAT ht hkt hrun hbN hct hni.1 hnq he hk hks hfs (Or.inl hni.2) cb c1 c2 c3 c4 hrc hcovR hcl hyes hrn
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFPJG hAT ht hkt hrun hbN hct hni.1 hnq he hk hks hft hto (Or.inl hni.2) cb c1 c2 c3 c4 hrc hcovR hyes hrn
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
end

end

end Fl4Proofs.P3
