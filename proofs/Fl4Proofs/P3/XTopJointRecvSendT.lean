/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` from a waiting sender with a
timeout fault and an SC at `J`** (the last case of XTopJointRecvIpcLink's
former `JRecvSendHyp`, KENTRY-PLAN.md (R2); l4v `receive_ipc`'s `send_ep`
branch for a sender that `handle_timeout` blocked on its timeout handler's
endpoint).

FL4's `do_ipc_transfer` of a timeout fault from a thread with an SC first
runs `update_consumed` (the SC's `CONSUMED` word to 0, spec
`schedContextUpdateConsumed`), then writes two message registers; FL4's
`can_donate` is false for a timeout fault, so a reply push never donates.

* `JAtZ.tmoRecvBaseJ`: the base `J` state after the SC step
  (ScJointConsumed's `JAtZ.updConsumedJ`, the state by
  `update_consumed_irel`), as XTopJointFaultTmo's `JAtZ.tmoBaseJ` without
  `set_fault` (the fault is already there).
* `JAtZ.recvSendFTJ` (no reply pushed, the sender `Inactive`) and
  `JAtZ.recvSendFPTJ` (a reply pushed, no donation): XTopJointRecvSendF's
  `JAtZ.recvSendFJG` / XTopJointRecvSendP's `JAtZ.recvSendFPJG` with the
  transfer XTopJointFaultTmo's `xferTmoStepJ`, the spec frame `RSFr` read
  from the base `σb` (the dequeue commutes with the SC update,
  `updSc_updK_comm`), `Inv` from the base's (the sender ends `Inactive`, out
  of `inClassR`, so no `RelIfBound` is needed for it), FL4's footprints
  rebased onto the base by `writesIn_rebase`; the push's spec outcome
  `receiveIpc_sendPushT_eq` (the spec's `can_donate` false too).
* `TmoOK`, `sendOK_split` (every blocked sender is `SendOK`, `PushOK` or
  `TmoOK`), `noPush_of`, `JAtZ.head_sendT` (the head of a send queue is a TCB
  blocked on send); wrappers `JAtZ.recvSendT0X` (receiver not lending,
  `JAtZ.recvPreN`) and `JAtZ.recvSendRetTJ` (lending: XTopJointRecvSendRP's
  route after `maybe_return_sc`).
-/
import Fl4Proofs.P3.XTopJointRecvSendRP
import Fl4Proofs.P3.XTopJointFaultTmo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecT
open Fl4Spec

/-- `receiveIpc_sendPush_eq` for a sender with a timeout fault: the spec's
`can_donate` is `false` (`hP` only for it). -/
theorem receiveIpc_sendPushT_eq {σ : State Unit} {t e sd : ObjRef} (b : Badge) (rights : CapRights) (blk : Bool)
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
    (hto3 : xs3.tcbFault.elim false isTimeoutFault = true)
    {σ' : State Unit} (hP : ∀ r, reply = some r → replyPush (Z := Unit) sd t r false σ3 = ({((), σ')}, False)) :
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
      have hd : decide (xs3.tcbSchedContext ≠ none ∧ ¬(xs3.tcbFault.elim false isTimeoutFault = true)) = false :=
        decide_eq_false (fun h => h.2 hto3)
      rw [hd]; exact hP r rfl

/-- The head senders left by `SendOK` / `PushOK`: a timeout fault and an SC. -/
def TmoOK (xs : Fl4Spec.Tcb) : Prop :=
  (∃ bb, xs.tcbFault = some (.timeout bb)) ∧ xs.tcbSchedContext ≠ none

/-- **Every sender blocked on send is `SendOK`, `PushOK` or `TmoOK`.** -/
theorem sendOK_split {xs : Fl4Spec.Tcb} (rc : capability.Cap) {e' : ObjRef} {dd : SenderPayload}
    (hst : xs.tcbState = .blockedOnSend e' dd) : SendOK xs rc ∨ PushOK xs rc ∨ TmoOK xs := by
  by_cases htm : TmoOK xs
  · exact Or.inr (Or.inr htm)
  have hto : ∀ f, xs.tcbFault = some f → ∀ b, f = .timeout b → xs.tcbSchedContext = none := by
    intro f hf b hb
    subst hb
    by_contra hn
    exact htm ⟨⟨b, hf⟩, hn⟩
  have hd : ∀ e1 d1, xs.tcbState = .blockedOnSend e1 d1 → d1 = dd := fun e1 d1 h => by
    rw [hst] at h; cases h; rfl
  by_cases hp : rc ≠ .Null ∧ (dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)
  · rcases hf : xs.tcbFault with _ | f
    · by_cases hcall : dd.senderIsCall = true
      · exact Or.inr (Or.inl ⟨hp.1, fun e1 d1 h => by rw [hd e1 d1 h]; exact hp.2,
          Or.inl ⟨hf, fun e1 d1 h => by rw [hd e1 d1 h]; exact hcall⟩⟩)
      · exact Or.inl (Or.inl ⟨hf, fun e1 d1 h => Or.inl (by rw [hd e1 d1 h]; simpa using hcall)⟩)
    · exact Or.inr (Or.inl ⟨hp.1, fun e1 d1 h => by rw [hd e1 d1 h]; exact hp.2, Or.inr ⟨f, hf, hto f hf⟩⟩)
  · have hnp : ∀ e1 d1, xs.tcbState = .blockedOnSend e1 d1 →
        (d1.senderCanGrant = false ∧ d1.senderCanGrantReply = false) ∨ rc = .Null := fun e1 d1 h => by
      rw [hd e1 d1 h]
      by_cases hn : rc = .Null
      · exact Or.inr hn
      · left
        have hg : ¬ (dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) := fun hg => hp ⟨hn, hg⟩
        simp only [not_or, Bool.not_eq_true] at hg
        exact hg
    rcases hf : xs.tcbFault with _ | f
    · exact Or.inl (Or.inl ⟨hf, fun e1 d1 h => Or.inr (hnp e1 d1 h)⟩)
    · exact Or.inl (Or.inr ⟨⟨f, hf, hto f hf⟩, hnp⟩)

/-- No reply pushed: neither grant right, or a null reply cap. -/
theorem noPush_of {xs : Fl4Spec.Tcb} {rc : capability.Cap}
    (hp : ¬ (rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true)) :
    ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      (dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null := by
  intro e' dd hst
  by_cases hn : rc = .Null
  · exact Or.inr hn
  · left
    have hg : ¬ (dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true) := fun hg =>
      hp ⟨hn, fun e1 d1 h1 => by rw [hst] at h1; cases h1; exact hg⟩
    simp only [not_or, Bool.not_eq_true] at hg
    exact hg

end SpecT

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The head of a send queue at `J`**: a TCB blocked on send. -/
theorem JAtZ.head_sendT (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {e : U64} (he : e ∈ Z.E)
    {l : List Fl4Spec.ObjRef} (hk : σ.kheap e.bv = some (.endpoint (.sendEP l))) :
    ∃ sd0 q xs e' dd, l = sd0 :: q ∧ σ.kheap sd0 = some (.tcb xs) ∧ xs.tcbState = .blockedOnSend e' dd := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  obtain ⟨-, xs0, hxs0, hq, hQ, hB⟩ := hR.at_ep he hk
  obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  have hsT : sd' ∈ Z.T := hQ.mem sd' (by simp)
  obtain ⟨xs, hks, -⟩ := hI.1.tcb sd' hsT
  have hxs := hR.at_tcb hsT hks
  have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
  obtain ⟨e', dd, hstd⟩ := tsCode_four (hxs.st.symm.trans hs4)
  exact ⟨sd'.bv, xs'.map UScalar.bv, xs, e', dd, by rw [hq]; rfl, hks, hstd⟩

set_option maxHeartbeats 8000000 in
/-- **The base `J` state of a receive from a timeout-faulted sender**
(module docstring): the SC `sc`'s consumed time cleared. -/
theorem JAtZ.tmoRecvBaseJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t : U64} (ht : t ∈ Z.T) {sc : U64} (hsc : sc ∈ Z.C)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n)) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (tmoS st s sc) a (Ipc.tmoSt σ sc y n) := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨r, -, ⟨σ2, c2, he2, V2, J2⟩, hs2, -, he2', -⟩ := spec_exists (WP.spec_and
    (J.updConsumedJ hAT hmax htu hsc ht) (update_consumed_irel (ar := arI) J.ip _ a _ hI hsc hky hmax htu))
  have eσ : σ2 = Ipc.tmoSt σ sc y n := by
    have e := (Prod.mk.inj (he2.symm.trans he2')).1
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e)
  rw [eσ, hs2] at J2
  exact ⟨V2, J2⟩

set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a head sender with a timeout fault and an SC at
`J`**, no reply pushed (module docstring), for any FL4 program `m` reducing
to the endpoint-state switch. -/
theorem JAtZ.recvSendFTJ (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) {bb : Fl4Spec.Word}
    (hft : xs.tcbFault = some (.timeout bb)) (hsn : xs.tcbSchedContext ≠ none)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hnp : ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      (dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null)
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
  -- the sender's SC and the base `J` state (its consumed time cleared, XTopJointFaultTmo's `tmoBaseJ`)
  obtain ⟨sc0, hsc0⟩ := Option.ne_none_iff_exists'.1 hsn
  obtain ⟨ys0, ns0, hky, -⟩ := J.inv.back sd'.bv xs sc0 hks hsc0
  obtain ⟨sc, hscC, rfl⟩ := J.obj.sc _ ys0 ns0 hky
  obtain ⟨Vb, Jb⟩ := J.tmoRecvBaseJ hAT hmax htu hsT hscC hky
  set σb := Ipc.tmoSt σ sc ys0 ns0 with hσb
  have hscE : sc.bv ≠ e.bv := kheap_ne hky hk (fun _ h1 h2 => by subst h1; cases h2)
  have hstS : sd'.bv ≠ sc.bv := kheap_ne hks hky (fun _ h1 h2 => by subst h1; cases h2)
  have htS : t.bv ≠ sc.bv := kheap_ne hkt hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkb : ∀ q', q' ≠ sc.bv → σb.kheap q' = σ.kheap q' := fun q' hq' => by
    simp [σb, Ipc.tmoSt, Sched.updSc, Notif.updK, hq']
  have hkbsc : σb.kheap sc.bv = some (.schedContext { ys0 with scConsumed := (0#u64 : U64).bv } ns0) := by
    simp [σb, Ipc.tmoSt, Sched.updSc, Notif.updK]
  have hksb : σb.kheap sd'.bv = some (.tcb xs) := by rw [hkb _ hstS]; exact hks
  have hkbe : σb.kheap e.bv = some (.endpoint (.sendEP (sd'.bv :: q))) := by rw [hkb _ (Ne.symm hscE)]; exact hk
  have hktb : σb.kheap t.bv = some (.tcb xt) := by rw [hkb _ htS]; exact hkt
  have hzb : SzKeep σ σb := fun p y0 m hp => by
    by_cases hps : p = sc.bv
    · subst hps; rw [hkbsc] at hp; cases hp; exact ⟨_, hky⟩
    · exact ⟨y0, by rw [← hkb _ hps]; exact hp⟩
  have hz0 : SzKeepC Z.C σb σ := by
    intro p _ y0 m hp
    by_cases hps : p.bv = sc.bv
    · rw [hps] at hp ⊢; rw [hky] at hp; cases hp; exact ⟨_, hkbsc⟩
    · exact ⟨y0, by rw [hkb _ hps]; exact hp⟩
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
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hky1 : σ1.kheap sc.bv = some (.schedContext ys0 ns0) := by simp [σ1, hscE, hky]
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc sc ys0 ns0 (J.c0 sc hscC) hky).2⟩
  -- the transfer: the timeout fault (XTopJointFaultTmo's `xferTmoStepJ`, on `IRel`)
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) hsT ht (Ne.symm hts) hks1 hkt1 hft hsc0 hky1 e bdg (i != 0#u64)
    hTP htH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2', hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc ys0 ns0) t.bv (.tcb x2) with hσ2
  set σ1b := Notif.updK σb e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1b
  have eσ2 : σ2 = Notif.updK σ1b t.bv (.tcb x2) := by
    rw [hσ2, hσ1b, hσ1, hσb]; simp only [Ipc.tmoSt]; rw [updSc_updK_comm _ hscE]
  have hkt1b : σ1b.kheap t.bv = some (.tcb xt) := by simp [σ1b, hte, hktb]
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by rw [eσ2]; simp
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by rw [eσ2]; simp [σ1b, hst', hse, hksb]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    rw [eσ2]; simp [σ1b, Ne.symm hte]
  have hscw8 : SW Z.C σ (scW sc 8#u64) := sw_hdr hI.2.2.1 hscC (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ False) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩))))
      · exact Or.inl (Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
  -- the spec frame from the base `σb`
  have Fr1 : RSFr sd'.bv t.bv σb σ1b := RSFr.upd hkbe (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv σ1b σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := σ1b) hkt1b x2.tcbArch
    rw [← hx2, ← eσ2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σb σ2 := Fr1.trans Fr2c
  have hz2 : SzKeepC Z.C σ σ2 := SzKeepC.of (fun p y m hp => by
    obtain ⟨y1, h⟩ := Fr2.szKeep p y m hp; exact hzb p y1 m h)
  have IK1 : IK sd'.bv σb σ1b := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hkbe
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σb σ1b := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σb σ2 := by
    rw [eσ2]; exact IK1.trans (IK.updTcb (σ := σ1b) hkt1b (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2]))
  have SK2 : Ipc.SKeep σb σ2 := by
    rw [eσ2]; exact SK1.trans (Ipc.SKeep.updK (σ := σ1b) (p := t.bv)
      (o := .tcb x2) (fun y' h => ⟨xt, hkt1b, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => Jb.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
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
      (by obtain ⟨-, -, r3, r4, -⟩ := P1.ts_vals; rw [hst3, r4, r3]; decide)
  have hno := hnp _ _ hstd
  have hnoS : ¬ ((dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none) := by
    rintro ⟨hgg, hrn⟩
    rcases hno with ⟨hg0, hgr0⟩ | hnull
    · rcases hgg with h | h
      · rw [hg0] at h; cases h
      · rw [hgr0] at h; cases h
    · rcases hrc with ⟨-, -, hrv⟩ | ⟨_, _, hr, -⟩
      · exact hrn (by rw [hrv, optRef_zero])
      · rw [hnull] at hr; cases hr
  suffices HH : (do
      let s4 ← sched.set_thread_state st s3 sd' sched.TS_INACTIVE
      ok (s4, a)) ⦃ r => ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    rcases hno with ⟨hg0, hgr0⟩ | hnull
    · by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hg0, hgr, hgr0, Bool.false_eq_true, ↓reduceIte]
        exact HH
      · simp only [hci, hftB, hg, hg0, hgr, hgr0, Bool.false_eq_true, ↓reduceIte]
        exact HH
    · have hrv : rv = 0#u64 := by
        rcases hrc with ⟨-, -, hrv⟩ | ⟨_, _, hr, -⟩
        · exact hrv
        · rw [hnull] at hr; cases hr
      subst hrv
      by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
        exact HH
      · simp only [hci, hftB, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ite_self]
        exact HH
  -- the sender `Inactive`
  have hnqS : NotQueued σ sd'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hnqSb : NotQueued σb sd'.bv := hnqS
  obtain ⟨hqb, hrb'⟩ := J.curBits hsT hnqS.1 hnqS.2
  have hna3 : L.actionW s3 ≠ sd' := by
    refine actionW_ne_of hIR3.2.2.1 hsT (fun h => ?_)
    have hsw := J.act.1 sd'.bv (show σ.schedulerAction = _ from act3.symm.trans h)
    obtain ⟨x, -, -, -, hkx, -, hrx, -⟩ := schedulable_inv hsw
    rw [hks] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
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
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σ.curThread; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  -- the footprints
  have hks2b : L.ksb s2 = L.ksb s := hW2.1
  have hW3' : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW2.trans1 (hW3.mono fun b hb => cnW_back hks2b hz2 (Or.inl (Or.inl hb)))
  have hks3b : L.ksb s3 = L.ksb s := hW3'.1
  have hW5' : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW3'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3b).1 hb))))
  have hfoot := footW_trans (footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)) (footW_of fu5)
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
  have Fr5 : RSFr sd'.bv t.bv σb σ5 := Fr2.trans (Fr3.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩)))
  -- `Inv` at the end
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σb σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σb σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : ∀ x, σ5'.kheap sd'.bv = some (.tcb x) → inClassR x.tcbState x.tcbFault → RelIfBound σ5' sd'.bv := by
    intro x hx hc
    rw [hk5'] at hx; cases hx
    exfalso
    rcases hc with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩ <;> simp [hx5, Fl4Spec.runnable] at h
  have I5' : Inv σ5' := ((Jb.inv.toBut sd'.bv).ik hnqSb IK5').1.inv hrib
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
      exact hnqSb.2 (by rw [← SK5'.1]; exact hu)
  have act5 : σ5.schedulerAction = σ.schedulerAction := by
    rw [hσ5, stsAct_ne hsc3]; exact act3
  -- the footprints rebased onto the base (XTopJointFaultTmo's `writesIn_rebase`)
  have hSσ := J.xtop.fin.1.1.1
  obtain ⟨Qs, Rs, hcs, hsps⟩ := hSσ.lists
  obtain ⟨ysb, nsb, hkys, hys⟩ := hsps.scs sc hscC
  rw [hky] at hkys; cases hkys
  have hal8 : P1.Aligned (scW sc 8#u64) := (hys.hdr (K := 8#u64) (by simp) (by simp)).1
  have hw0 : P1.WritesIn st s (tmoS st s sc) (fun b => b = scW sc 8#u64) := writesIn_wr hal8
  have hWb : P1.WritesIn st (tmoS st s sc) s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c (tmoS st s sc) σb) :=
    (writesIn_rebase hW5' hw0 (fun b0 hb0 => by subst hb0; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8))))).mono
      fun b0 hb0 => CnW.back (s := tmoS st s sc) (s' := s) hw0.1.symm hz0 hb0
  have hfootb : P1.WritesIn st (tmoS st s sc) s5 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) (tmoS st s sc)) :=
    (writesIn_rebase hfoot hw0 (fun b0 hb0 => by
      subst hb0; exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc1, scW8_inSC J.blk hsc1⟩)))))).mono
      fun b0 hb0 => hb0.elim (P1.KW.ksb hw0.1.symm) False.elim
  have hIb := Jb.xtop.irelK Jb.ks Jb.buf
  have hF : IFrame (L := L) Z.th (tmoS st s sc) s5 := IRel.iframe_of hIb hWb fun b0 hb0 => CnW.oobj hIb.2.2.1 hb0
  have htD := Jb.not_dead_of_st hsT hksb (by rw [hstd]; simp [tsCode])
  have hIR5 := IpcRel.ofSRN hR5 hS5
  obtain ⟨V', J5⟩ := Jb.rsfrStep hIR5 hF hWb hblk hfootb Fr5 I5 (Or.inl act5) htD
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hspec := receiveIpc_sendCall_eq b rights blk hsr hkt hbN hk hks hse hstd hnoS e2' hA hks3
    (Or.inr (by rw [hft]; simp))
  refine (WP.spec_ok _).2 ⟨((), σ5), ?_, J5.xtop.relTop, _, _, _, _, _, _, J5⟩
  rw [hspec]; exact Set.mem_singleton _


set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a head sender with a timeout fault and an SC pushing
a reply at `J`** (module docstring; no donation),
has the grant or grant-reply right, the receiver passes a reply object
(covered, `hcovR`), at a resumed entry; for any FL4 program `m` reducing to
the endpoint-state switch. -/
theorem JAtZ.recvSendFPTJ (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) {bb : Fl4Spec.Word}
    (hft : xs.tcbFault = some (.timeout bb)) (hsn : xs.tcbSchedContext ≠ none)
    (hAct : σ.schedulerAction = .resumeCurThread ∨
      (σ.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue))
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
  -- the sender's SC and the base `J` state (its consumed time cleared, XTopJointFaultTmo's `tmoBaseJ`)
  obtain ⟨sc0, hsc0⟩ := Option.ne_none_iff_exists'.1 hsn
  obtain ⟨ys0, ns0, hky, -⟩ := J.inv.back sd'.bv xs sc0 hks hsc0
  obtain ⟨sc, hscC, rfl⟩ := J.obj.sc _ ys0 ns0 hky
  obtain ⟨Vb, Jb⟩ := J.tmoRecvBaseJ hAT hmax htu hsT hscC hky
  set σb := Ipc.tmoSt σ sc ys0 ns0 with hσb
  have hscE : sc.bv ≠ e.bv := kheap_ne hky hk (fun _ h1 h2 => by subst h1; cases h2)
  have hstS : sd'.bv ≠ sc.bv := kheap_ne hks hky (fun _ h1 h2 => by subst h1; cases h2)
  have htS : t.bv ≠ sc.bv := kheap_ne hkt hky (fun _ h1 h2 => by subst h1; cases h2)
  have hkb : ∀ q', q' ≠ sc.bv → σb.kheap q' = σ.kheap q' := fun q' hq' => by
    simp [σb, Ipc.tmoSt, Sched.updSc, Notif.updK, hq']
  have hkbsc : σb.kheap sc.bv = some (.schedContext { ys0 with scConsumed := (0#u64 : U64).bv } ns0) := by
    simp [σb, Ipc.tmoSt, Sched.updSc, Notif.updK]
  have hksb : σb.kheap sd'.bv = some (.tcb xs) := by rw [hkb _ hstS]; exact hks
  have hkbe : σb.kheap e.bv = some (.endpoint (.sendEP (sd'.bv :: q))) := by rw [hkb _ (Ne.symm hscE)]; exact hk
  have hktb : σb.kheap t.bv = some (.tcb xt) := by rw [hkb _ htS]; exact hkt
  have hzb : SzKeep σ σb := fun p y0 m hp => by
    by_cases hps : p = sc.bv
    · subst hps; rw [hkbsc] at hp; cases hp; exact ⟨_, hky⟩
    · exact ⟨y0, by rw [← hkb _ hps]; exact hp⟩
  have hz0 : SzKeepC Z.C σb σ := by
    intro p _ y0 m hp
    by_cases hps : p.bv = sc.bv
    · rw [hps] at hp ⊢; rw [hky] at hp; cases hp; exact ⟨_, hkbsc⟩
    · exact ⟨y0, by rw [hkb _ hps]; exact hp⟩
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
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hky1 : σ1.kheap sc.bv = some (.schedContext ys0 ns0) := by simp [σ1, hscE, hky]
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc sc ys0 ns0 (J.c0 sc hscC) hky).2⟩
  -- the transfer: the timeout fault (XTopJointFaultTmo's `xferTmoStepJ`, on `IRel`)
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) hsT ht (Ne.symm hts) hks1 hkt1 hft hsc0 hky1 e bdg (i != 0#u64)
    hTP htH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2', hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc ys0 ns0) t.bv (.tcb x2) with hσ2
  set σ1b := Notif.updK σb e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) with hσ1b
  have eσ2 : σ2 = Notif.updK σ1b t.bv (.tcb x2) := by
    rw [hσ2, hσ1b, hσ1, hσb]; simp only [Ipc.tmoSt]; rw [updSc_updK_comm _ hscE]
  have hkt1b : σ1b.kheap t.bv = some (.tcb xt) := by simp [σ1b, hte, hktb]
  have hkt2 : σ2.kheap t.bv = some (.tcb x2) := by rw [eσ2]; simp
  have hks2 : σ2.kheap sd'.bv = some (.tcb xs) := by rw [eσ2]; simp [σ1b, hst', hse, hksb]
  have hk2e : σ2.kheap e.bv = some (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) := by
    rw [eσ2]; simp [σ1b, Ne.symm hte]
  have hscw8 : SW Z.C σ (scW sc 8#u64) := sw_hdr hI.2.2.1 hscC (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ False) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩))))
      · exact Or.inl (Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
  -- the spec frame from the base `σb`
  have Fr1 : RSFr sd'.bv t.bv σb σ1b := RSFr.upd hkbe (Or.inr (Or.inr ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩))
  have Fr2c : RSFr sd'.bv t.bv σ1b σ2 := by
    have h := RSFr.arch (t := sd'.bv) (σ := σ1b) hkt1b x2.tcbArch
    rw [← hx2, ← eσ2] at h; exact h
  have Fr2 : RSFr sd'.bv t.bv σb σ2 := Fr1.trans Fr2c
  have hz2 : SzKeepC Z.C σ σ2 := SzKeepC.of (fun p y m hp => by
    obtain ⟨y1, h⟩ := Fr2.szKeep p y m hp; exact hzb p y1 m h)
  have IK1 : IK sd'.bv σb σ1b := IK.updOther (o' := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv)) hkbe
    (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : Ipc.SKeep σb σ1b := Ipc.SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have IK2 : IK sd'.bv σb σ2 := by
    rw [eσ2]; exact IK1.trans (IK.updTcb (σ := σ1b) hkt1b (by rw [hx2]) (by rw [hx2]) (fun _ => by rw [hx2]))
  have SK2 : Ipc.SKeep σb σ2 := by
    rw [eσ2]; exact SK1.trans (Ipc.SKeep.updK (σ := σ1b) (p := t.bv)
      (o := .tcb x2) (fun y' h => ⟨xt, hkt1b, by cases h; rw [hx2]⟩) (fun _ _ h => by cases h))
  -- the sender's sporadic check, at the hole
  have hne2 : ∀ p y' n, σ2.kheap p = some (.schedContext y' n) → Fl4Spec.scActive y' = true → y'.scRefills ≠ [] :=
    fun p y' n hp ha => Jb.inv.ne p y' n (SK2.2.2.2 p y' n hp) ha
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
  have hty3 : L.mem s3 (tFaultA sd') = 5#u64 := by
    have hfr := hxs3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; exact hfr.1
  have hcdF : (ft != fl4_abi.consts.fault.Timeout) = false := by
    rw [hft', hty3]; unfold fl4_abi.consts.fault.Timeout; decide
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
  have hnqSb : NotQueued σb sd'.bv := hnqS
  -- the receiver: no donation (the sender's timeout fault)
  have hA0 := hAct
  have hCI : σ.schedulerAction = .resumeCurThread → CurInv σb := fun hres =>
    Jb.cur.resolve_left (fun h => by
      have h' : σ.schedulerAction = .chooseNewThread := h
      rw [hres] at h'; cases h')
  have hnrT : t.bv ∉ σ.releaseQueue := by
    rcases hA0 with hres | ⟨-, h⟩
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
  have Fr23 : RSFr sd'.bv t.bv σb σ3 := Fr2.trans Fr3
  have hz23 : SzKeepC Z.C σ σ3 := SzKeepC.of (fun p y m hp => by
    obtain ⟨y1, h⟩ := Fr23.szKeep p y m hp; exact hzb p y1 m h)
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
  have hkrb : σb.kheap rv.bv = some (.reply xr) := by
    rw [hkb _ (kheap_ne hkr hky (fun _ h1 h2 => by subst h1; cases h2))]; exact hkr
  have hkr3 : σ3.kheap rv.bv = some (.reply xr) := Fr23.replyF hkrb
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
      show u.bv ∈ σb.releaseQueue
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
  suffices HH : ipc.reply_push st arI s3 a sd' t rv false ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ by
    have HH' : (do
        let i3 ← obj.Tcb.sc st sd' s3
        let can_donate ← if i3 != 0#u64 then ok (ft != fl4_abi.consts.fault.Timeout) else ok false
        ipc.reply_push st arI s3 a sd' t rv can_donate) ⦃ r =>
          ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
            RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
      refine WP.spec_bind (Fl4Proofs.P1.obj.Tcb.sc.spec s3 sd') ?_
      rintro i3 -
      by_cases h3' : (i3 != 0#u64) = true
      · rw [if_pos h3', hcdF]; exact ok_bind_spec _ _ HH
      · rw [if_neg h3']; exact ok_bind_spec _ _ HH
    rcases Bool.eq_false_or_eq_true dd.senderCanGrant with hG | hG
    · by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hrv0, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
    · have hGR : dd.senderCanGrantReply = true := hgg.resolve_left (by rw [hG]; decide)
      by_cases hci : (i2 != 0#u64) = true
      · simp only [hci, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
      · simp only [hci, hftB, hg, hG, hgr, hGR, hrv0, Bool.false_eq_true, ↓reduceIte]; exact HH'
  refine WP.spec_mono (hPush false (Or.inl rfl)) ?_
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, hblk, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 hblk fu4 hsb4 ⊢
  subst ha4
  -- the footprints
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 hsT hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hks2b : L.ksb s2 = L.ksb s := hW2.1
  have hW3' : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW2.trans1 (hW3.mono fun b hb => cnW_back hks2b hz2 (Or.inl (Or.inl hb)))
  have hks3b : L.ksb s3 = L.ksb s := hW3'.1
  have hW4' : P1.WritesIn st s s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW3'.trans1 (hW4.mono fun b hb => cnW_back hks3b hz23 hb)
  have hfoot := footW_trans (footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)) (footW_of fu4)
  -- the sender `Inactive` (a spec state only): `Inv` there, as in `recvSendFJG`
  set x5 : Fl4Spec.Tcb := { xs with tcbState := .inactive } with hx5
  have hsc3 : sd'.bv ≠ (Notif.updK σ3 sd'.bv (.tcb x5)).curThread := by
    show sd'.bv ≠ σ3.curThread; rw [ct3]; show sd'.bv ≠ σ.curThread; exact hsc
  set σ5 := Notif.stsAct (Notif.updK σ3 sd'.bv (.tcb x5)) sd'.bv with hσ5
  have Fr5 : RSFr sd'.bv t.bv σb σ5 := Fr23.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩))
  set σ5' := Notif.updK σ2 sd'.bv (.tcb x5) with hσ5'
  have IK5' : IK sd'.bv σb σ5' := IK2.trans (IK.updSelf (y := x5) hks2 rfl)
  have SK5' : Ipc.SKeep σb σ5' := SK2.trans (Ipc.SKeep.updK (p := sd'.bv) (o := .tcb x5)
    (fun y' h => ⟨xs, hks2, by cases h; rfl⟩) (fun _ _ h => by cases h))
  have hk5' : σ5'.kheap sd'.bv = some (.tcb x5) := by simp [σ5']
  have hrib : ∀ x, σ5'.kheap sd'.bv = some (.tcb x) → inClassR x.tcbState x.tcbFault → RelIfBound σ5' sd'.bv := by
    intro x hx hc
    rw [hk5'] at hx; cases hx
    exfalso
    rcases hc with h | ⟨_, h⟩ | ⟨_, _, h, -⟩ | ⟨_, _, _, h⟩ <;> simp [hx5, Fl4Spec.runnable] at h
  have I5' : Inv σ5' := ((Jb.inv.toBut sd'.bv).ik hnqSb IK5').1.inv hrib
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
      exact hnqSb.2 (by rw [← SK5'.1]; exact hu)
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
    exact Jb.bsa.tcb p y0 n sd'.bv xs hy0 (by rw [ey] at hyt; exact hyt) hksb (by rw [hstd]; rfl)
  have B6 : BlockedScActive σ' := ps_bsa hkta hkwa hws hscA (Fr5.bsa Jb.bsa)
  have hcne1 : σ5.curThread ≠ sd'.bv := by rw [Fr5.sk.ct]; show σ.curThread ≠ _; rw [hct]; exact Ne.symm hst'
  have hcne2 : σ5.curThread ≠ rv.bv := by rw [Fr5.sk.ct]; show σ.curThread ≠ _; rw [hct]; exact Ne.symm hwt
  have hactP : σ'.schedulerAction = σ.schedulerAction := by
    show (pushSt σ5 sd'.bv rv.bv xr x5).schedulerAction = _
    unfold pushSt
    rw [stsAct_ne (by show sd'.bv ≠ σ5.curThread; exact Ne.symm hcne1)]
    exact act5
  have hidT : σ5.idleThread ≠ sd'.bv := by rw [Fr5.sk.idle]; exact fun e0 => his e0.symm
  have hAI6 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hactP] at hu; exact absurd hu (hsw u)), ps_idleOK hkta hkwa hws hidT (Fr5.idleOK Jb.act.2)⟩
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
    have hrun5 : CurRunW σ5 := Fr5.curRunW (Jb.curRun.resolve_left fun e0 => e0 hres)
    exact Or.inr (by
      rcases hrun5 with h | h
      · refine Or.inl fun y hy => h y ?_
        rw [G'.ct, ps_ko hcne1 hcne2] at hy; exact hy
      · exact Or.inr (by rw [G'.ct, G'.idle]; exact h))
  -- the footprints rebased onto the base (XTopJointFaultTmo's `writesIn_rebase`)
  have hSσ := J.xtop.fin.1.1.1
  obtain ⟨Qs, Rs, hcs, hsps⟩ := hSσ.lists
  obtain ⟨ysb, nsb, hkys, hys⟩ := hsps.scs sc hscC
  rw [hky] at hkys; cases hkys
  have hal8 : P1.Aligned (scW sc 8#u64) := (hys.hdr (K := 8#u64) (by simp) (by simp)).1
  have hw0 : P1.WritesIn st s (tmoS st s sc) (fun b => b = scW sc 8#u64) := writesIn_wr hal8
  have hWb : P1.WritesIn st (tmoS st s sc) s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c (tmoS st s sc) σb) :=
    (writesIn_rebase hW4' hw0 (fun b0 hb0 => by subst hb0; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8))))).mono
      fun b0 hb0 => CnW.back (s := tmoS st s sc) (s' := s) hw0.1.symm hz0 hb0
  have hfootb : P1.WritesIn st (tmoS st s sc) s4 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) (tmoS st s sc)) :=
    (writesIn_rebase hfoot hw0 (fun b0 hb0 => by
      subst hb0; exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc1, scW8_inSC J.blk hsc1⟩)))))).mono
      fun b0 hb0 => hb0.elim (P1.KW.ksb hw0.1.symm) False.elim
  have hIb := Jb.xtop.irelK Jb.ks Jb.buf
  have hF : IFrame (L := L) Z.th (tmoS st s sc) s4 := IRel.iframe_of hIb hWb fun b0 hb0 => CnW.oobj hIb.2.2.1 hb0
  have htD := Jb.not_dead_of_st hsT hksb (by rw [hstd]; simp [tsCode])
  have hIR4 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s4 σ' := by
    rw [← heqP]; exact IpcRel.ofSRN hR4 hS4
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σ5.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hws h1 h2
  have hkq : ∀ q ∈ D \ {rv}, σ'.kheap q.bv = σ5.kheap q.bv := fun q hq =>
    ps_ko (htD q hq) (fun e0 => hq.2 (P1.eq_of_bv e0))
  obtain ⟨V', J6⟩ := Jb.rsfr_postGR hIR4 hF hWb hblk hfootb Fr5 ps_skD
    (ps_ksub hkta hkwa hws) (ps_szKeep hkta hkwa hws) (ps_ykeep hkta hkwa hws) (ps_mcpKeep hkta hkwa hws)
    (ps_bufKeep hkta hkwa hws) (fun d _ h => ps_recvB hkta hkwa hws h) (ps_ksz hkta hkwa hws)
    (ps_kback hkta hkwa hws) (ps_ipcFr hkta hkwa hws) (ps_ck hkta hkwa hws) (fun d _ h => ps_free hkta hkwa hws h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I6 B6 hAI6 hcur6 hrun6 (ps_own hkta hkwa hws (Fr5.own Jb.own))
    (ps_off hkta hkwa hws (Fr5.off Jb.off)) (ps_nsc hkta hkwa hws (Fr5.nsc Jb.nsc))
    (ps_isorted hkta hkwa hws (Fr5.isorted Jb.isorted)) htD
  -- the spec's outcome
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hyesS : (dd.senderCanGrant ∨ dd.senderCanGrantReply) ∧ optRef rv ≠ none :=
    ⟨by rcases hgg with h | h <;> simp [h], by rw [Notif.optRef_ne hw00]; simp⟩
  have hPS : ∀ r, optRef rv = some r → Fl4Spec.replyPush (Z := Unit) sd'.bv t.bv r false σ3 =
      ({((), σ')}, False) := by
    intro r hr
    rw [Notif.optRef_ne hw00] at hr
    cases hr
    rw [hpush, heqP]
  have hspec := receiveIpc_sendPushT_eq b rights blk hsr hkt hbN hk hks hse hstd hyesS e2' hA hks3
    (Or.inr (by rw [hft]; simp)) (by rw [hft]; rfl) hPS
  exact ⟨((), σ'), by rw [hspec]; exact Set.mem_singleton _, J6.xtop.relTop, _, _, _, _, _, _, J6⟩



/-- **`receive_ipc` from a head sender with a timeout fault and an SC at
`J`**, the receiver without a bound notification or with one not active,
polling or not lending its SC (XTopJointRecvSend's `JAtZ.recvPreN`): a reply
pushed (`JAtZ.recvSendFPTJ`) or not (`JAtZ.recvSendFTJ`). -/
theorem JAtZ.recvSendT0X (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
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
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (hok : TmoOK xs) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨⟨bb, hft⟩, hsn⟩ := hok
  by_cases hp : rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
  · have hrv0 : rv ≠ 0#u64 := by
      rcases hrc with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hp.1
      · exact (J.rp.align rv hr).2.1
    exact J.recvSendFPTJ hAT hmax htu ht hkt hrun hbN hct hni.1 hnq he hk hks hft hsn (Or.inl hni.2) cb c1 c2 c3 c4
      hrc (hcovR hrv0) hp.2 hp.1 b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFTJ hAT hmax htu ht hkt hrun hbN hct he hk hks hft hsn cb c1 c2 c3 c4 hrc (noPush_of hp)
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a head sender with a timeout fault and an
SC, the receiver's bound notification lending it its SC, at `J`** (module
docstring): XTopJointRecvSendRP's route, then `JAtZ.recvSendFPTJ` (a reply
pushed) or `JAtZ.recvSendFTJ` at the state after `maybe_return_sc`. -/
theorem JAtZ.recvSendRetTJ (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : TmoOK xs)
    {g gr : Bool} (hHd : JHeld (L := L) Z.th s (.Endpoint e cb c1 true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hC : CurInv σ := J.curInv (by rw [hni.2]; intro e; cases e)
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := (J.curRun.run hni) xt (by rw [hcur]; exact hkt)
  -- the sender is not the receiver
  have hxt := hR.at_tcb ht hkt
  have hts : sd ≠ t := by
    rintro rfl
    obtain ⟨-, xs0, hxs0, hq, hQ, hB⟩ := hR.at_ep he hk
    obtain ⟨sd', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    have hdd : sd' = sd := eq_of_bv hq.1.symm
    subst hdd
    have hs4 : (L.mem s (tStA sd')).val = 4 := (hB sd' (by simp)).1
    obtain ⟨_, _, h1⟩ := tsCode_four (hxt.st.symm.trans hs4)
    rw [h1] at hr; simp [Fl4Spec.runnable] at hr
  -- the SC `i` lent by the notification, the thread's
  obtain ⟨hl1, hl2⟩ := hlend
  obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hl2
  have hxs0 : xt.tcbSchedContext = some i0 := hl1.symm.trans hi0
  obtain ⟨y, m, hky, -⟩ := J.inv.back t.bv xt i0 hkt hxs0
  obtain ⟨i, hiC, rfl⟩ := J.obj.sc _ y m hky
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, hnrl⟩
  obtain ⟨σ2, he2, kt, -, ko, ct, -, -, -, idl, -, rel, act, -, rq⟩ := maybeReturn_shape J.inv hkn hkt hky hxs0 hi0 hnqT
  -- FL4's bound-notification words
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
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
  rintro s' ⟨hW, σ', he', Ac', Lst', J2⟩
  rw [the_result he2 he'] at J2
  have hI2 := J2.xtop.irelK J2.ks J2.buf
  -- the objects kept by `maybe_return_sc`
  have hte : e.bv ≠ t.bv := fun h => by rw [h, hkt] at hk; cases hk
  have hie : e.bv ≠ i.bv := fun h => by rw [h, hky] at hk; cases hk
  have hk2 : σ2.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))) := by rw [ko _ hte hie]; exact hk
  have hnt : n.bv ≠ t.bv := fun h => by rw [h, hkt] at hkn; cases hkn
  have hni' : n.bv ≠ i.bv := fun h => by rw [h, hky] at hkn; cases hkn
  have hkn2 : σ2.kheap n.bv = some (.notification xn) := by rw [ko _ hnt hni']; exact hkn
  have hst' : sd.bv ≠ t.bv := bv_ne hts
  have hsi : sd.bv ≠ i.bv := fun h => by rw [h, hky] at hks; cases hks
  have hks2 : σ2.kheap sd.bv = some (.tcb xs) := by rw [ko _ hst' hsi]; exact hks
  have hcur2 : σ2.curThread = t.bv := ct.trans hcur
  -- the reply cap at the state after
  have hrc2 : ReplyArg Z.R (L.mem s') rc rc' rv := by
    rcases hrc with h | ⟨bb, r', h1, h2, hrR, h0⟩
    · exact Or.inl h
    refine Or.inr ⟨bb, r', h1, h2, hrR, ?_⟩
    obtain ⟨xr, hkr, hxr⟩ := hI.1.toE.reply rv hrR
    obtain ⟨xr2, hkr2, hxr2⟩ := hI2.1.toE.reply rv hrR
    have hrt : rv.bv ≠ t.bv := fun h => by rw [h, hkt] at hkr; cases hkr
    have hri : rv.bv ≠ i.bv := fun h => by rw [h, hky] at hkr; cases hkr
    rw [ko _ hrt hri, hkr] at hkr2; cases hkr2
    rw [h0, optRef_zero] at hxr
    exact optRef_none (hxr2.symm.trans hxr)
  have hnr2 : ¬ (xn.ntfnSc = (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbSchedContext ∧
      xn.ntfnSc ≠ none) := fun h => h.2 h.1
  have hsp := receiveIpc_lend_eq b rights (replyArg_spec J.ip.e hI.1.toE hrc)
    (replyArg_spec J2.ip.e hI2.1.toE hrc2) hkt kt hbn hbn hk hk2 hkn hkn2 hna he2 hnr2
  -- the reply's covers at the state after
  obtain ⟨-, hcovR⟩ := J.recvCov_ofW hW he hHd hHr hrc
  have hni2 : σ2.curThread ≠ σ2.idleThread := by rw [ct, idl]; exact hni.1
  have hnq2 : ∀ dm p, σ2.curThread ∉ σ2.readyQueues dm p := by rw [hcur2]; exact rq
  have hA2 : σ2.schedulerAction = .resumeCurThread ∨ (σ2.schedulerAction = .chooseNewThread ∧
      t.bv ∉ σ2.releaseQueue) :=
    Or.inr ⟨act hcur.symm, fun h => hnrl (rel _ h)⟩
  have hbN2 : (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = none ∨
      ∃ n' xn', (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = some n' ∧
        σ2.kheap n' = some (.notification xn') ∧ Fl4Spec.isActive xn' = false ∧
        (true = true → ¬ (xn'.ntfnSc = (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbSchedContext ∧
          xn'.ntfnSc ≠ none)) :=
    Or.inr ⟨n.bv, xn, hbn, hkn2, hna, fun _ => hnr2⟩
  rw [hsp]
  obtain ⟨⟨bb, hft⟩, hsn⟩ := hok
  by_cases hp : rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
  · have hrv0 : rv ≠ 0#u64 := by
      rcases hrc with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hp.1
      · exact (J.rp.align rv hr).2.1
    exact J2.recvSendFPTJ hAT hmax htu ht kt hr hbN2 hcur2 hni2 hnq2 he hk2 hks2 hft hsn hA2 cb c1 true g gr hrc2
      (hcovR hrv0) hp.2 hp.1 b rights (m := Endp.recvTail st arI s' a t e rv)
      (fun h => by unfold Endp.recvTail; exact h)
  · exact J2.recvSendFTJ hAT hmax htu ht kt hr hbN2 hcur2 he hk2 hks2 hft hsn cb c1 true g gr hrc2
      (noPush_of hp) b rights (m := Endp.recvTail st arI s' a t e rv)
      (fun h => by unfold Endp.recvTail; exact h)

end

end

end Fl4Proofs.P3
