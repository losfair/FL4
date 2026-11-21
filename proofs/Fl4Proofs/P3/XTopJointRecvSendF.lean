/-
P3 (DESIGN.md §9), IPC: **`receive_ipc` from a waiting faulted sender at
`J`** (XTopJointRecvIpcLink's `JRecvSendHyp`, KENTRY-PLAN.md item 6 (d4),
(d4'); l4v `receive_ipc`'s `send_ep` branch with `fault ≠ None`), any fault
but a timeout fault of a sender with an SC.

* `JAtZ.recvSendFJG`: the head sender holds a fault (a timeout only without
  an SC) and no reply is
  pushed (neither grant right, or no reply cap): XTopJointRecvSend's
  `JAtZ.recvSendJG` with the transfer XTopJointXferF's `xferFaultStepGJ`
  (on `IRel`, sender to receiver, back to `JAtZ` across the receive buffer by
  `JAtZ.bufRebaseX` as XTopJointFaultRecv's `JAtZ.sendFaultIJ`), the spec
  frame IpcRecvSendFr's `RSFr` from `σ`, `unblockHole`, FL4's fault word
  non-null (so the call-or-fault branch), the sender `Inactive`; the spec's
  outcome `receiveIpc_sendCall_eq` with the fault disjunct.
* `SendOK`, `JAtZ.recvSendJX`: the head sender cases proved (unfaulted as in
  `JAtZ.recvSendJG`, or faulted as above), for any FL4 program reducing to
  the endpoint-state switch; `JAtZ.recvSendJ0X` with XTopJointRecvSend's
  `JAtZ.recvPreN`.
-/
import Fl4Proofs.P3.XTopJointRecvSend
import Fl4Proofs.P3.XTopJointXferF
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- The head senders whose receive is proved at `J`: not faulted and either
not calling or calling without a reply pushed (`JAtZ.recvSendJG`), or with a
fault (a timeout only without an SC) and no reply pushed (`JAtZ.recvSendFJG`). -/
def SendOK (xs : Fl4Spec.Tcb) (rc : capability.Cap) : Prop :=
  (xs.tcbFault = none ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd → dd.senderIsCall = false ∨
      ((dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null)) ∨
    ((∃ f, xs.tcbFault = some f ∧ ∀ b, f = .timeout b → xs.tcbSchedContext = none) ∧
      ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      (dd.senderCanGrant = false ∧ dd.senderCanGrantReply = false) ∨ rc = .Null)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a faulted head sender at `J`** (a timeout fault only
without an SC), no reply pushed
(module docstring), for any FL4 program `m` reducing to the endpoint-state
switch. -/
theorem JAtZ.recvSendFJG (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) {f : Fl4Spec.Fault}
    (hft : xs.tcbFault = some f) (hto : ∀ b, f = .timeout b → xs.tcbSchedContext = none)
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
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2b (SzKeepC.of Fr2.szKeep) (Or.inl (Or.inl hb))))
  have hks3b : L.ksb s3 = L.ksb s := hW3'.1
  have hW5' : P1.WritesIn st s s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xt b) :=
    hW3'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3b).1 hb)))))
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
  have Fr5 : RSFr sd'.bv t.bv σ σ5 := Fr2.trans (Fr3.trans (Sched.RSFr.stsInact hks3 (Or.inl ⟨_, _, hstd⟩)))
  -- `Inv` at the end
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
  -- back to `JAtZ`
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX ht hth hkt hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hsT hks (by rw [hstd]; simp [tsCode])
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have hIR5 := IpcRel.ofSRN hR5 hS5
  obtain ⟨V', J5⟩ := Ju.rsfrStep hIR5 hF hWu hblk hFu (RSFr.ofUm Fr5 umu) I5 (Or.inl act5) htD
  have e2' : Fl4Spec.doIpcTransfer (Z := Unit) sd'.bv (some e.bv) dd.senderBadge dd.senderCanGrant t.bv
      (Notif.updK σ e.bv (.endpoint (epDeq (.sendEP (sd'.bv :: q)) sd'.bv))) = ({((), σ2)}, False) := by
    rw [← hbb, ← hg]; exact e2
  have hspec := receiveIpc_sendCall_eq b rights blk hsr hkt hbN hk hks hse hstd hnoS e2' hA hks3
    (Or.inr (by rw [hft]; simp))
  refine (WP.spec_ok _).2 ⟨((), σ5), ?_, J5.xtop.relTop, _, _, _, _, _, _, J5⟩
  rw [hspec]; exact Set.mem_singleton _

/-- **`receive_ipc` from the head sender at `J`**, the cases of `SendOK`, for
any FL4 program `m` reducing to the endpoint-state switch. -/
theorem JAtZ.recvSendJX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : SendOK xs rc)
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
  rcases hok with ⟨hfs, hcall⟩ | ⟨⟨f, hft, hto⟩, hnp⟩
  · exact J.recvSendJG ht hkt hrun hbN hct he hk hks hfs cb c1 c2 c3 c4 hrc hcall b rights hm
  · exact J.recvSendFJG ht hkt hrun hbN hct he hk hks hft hto cb c1 c2 c3 c4 hrc hnp b rights hm

/-- **`receive_ipc` from the head sender at `J`**, the cases of `SendOK`, the
receiver without a bound notification or with one not active, polling or not
lending its SC (XTopJointRecvSend's `JAtZ.recvPreN`). -/
theorem JAtZ.recvSendJ0X (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : SendOK xs rc)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.recvSendJX ht hkt hrun hbN hct he hk hks cb c1 c2 c3 c4 hrc hok b rights
    (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

end

end

end Fl4Proofs.P3
