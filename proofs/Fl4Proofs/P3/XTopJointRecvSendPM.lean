/-
P3 (DESIGN.md §9), IPC (KENTRY-PLAN sch17 item 2): **`receive_ipc` from a
head sender pushing a reply at a switch mid state.** The resumed copies
(XTopJointRecvSendP's `JAtZ.recvSendFPJG` / `JAtZ.recvSendPJG`,
XTopJointRecvSendT's `JAtZ.recvSendFPTJ`) take `hAct`: the action resumes the
current thread, or a reschedule is pending. Here the action is
`switchThread u` with `u ≠ ct` (a mid state of `handle_recv` after a first
phase that woke `u`; l4v `scheduler_act_sane`). The reply push binds the
reply to the sender, which blocks on it (no `possibleSwitchTo`), so the
changes are local:

* `CurInv` by `J.curInv` (the action is not `chooseNewThread`), so the
  receiver has the current SC (no donation, `hnd`) and is not released;
* the P1 push's "the action word names neither thread" (`hna3`) from
  `u ≠ ct` and `u ≠ sender` (the switch target is schedulable, `ActSched`,
  the sender is blocked on send), `hswT`;
* `ActIdle` after: the switch target `u` stays schedulable (`RSFr.sched`
  through the transfer and the sender's `Inactive`, `ps_schedM` through the
  push: `u` is neither the sender nor the reply);
* `CurRunM` by its first disjunct (the action is not resume); `CurInv` after
  as in the resumed case, so the post is `JAtZ`.

* `ps_schedM`, `JAtZ.recvSendFPJGM`, `JAtZ.recvSendPJGM`, `JAtZ.recvSendFPTJM`
  (copies with the changes above), wrappers `JAtZ.recvSendP0XM` (`PushOK`)
  and `JAtZ.recvSendT0XM` (`TmoOK`; without a push XTopJointRecvSendT's
  `JAtZ.recvSendFTJ`, which reads no action).
-/
import Fl4Proofs.P3.XTopJointRecvSendT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- A thread other than the pushing sender and the reply stays schedulable
through the push. -/
theorem ps_schedM {σ : Fl4Spec.State Unit} {t w : Fl4Spec.ObjRef} {xr : Fl4Spec.Reply} {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hkw : σ.kheap w = some (.reply xr)) {u : Fl4Spec.ObjRef}
    (hut : u ≠ t) (huw : u ≠ w) (hs : Fl4Spec.schedulable u σ = true) :
    Fl4Spec.schedulable u (pushSt σ t w xr xt) = true := by
  obtain ⟨x, scp, y, n, hk, hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hs
  have h1 : scp ≠ t := fun e => by rw [e, hkt] at hky; cases hky
  have h2 : scp ≠ w := fun e => by rw [e, hkw] at hky; cases hky
  exact schedulable_of (by rw [ps_ko hut huw]; exact hk) hsc hrun (by rw [ps_ko h1 h2]; exact hky) hact
    (by rw [ps_rel]; exact hnr)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a faulted head sender pushing a reply at `J`**
(module docstring): the sender holds a fault (a timeout only without an SC),
has the grant or grant-reply right, the receiver passes a reply object
(covered, `hcovR`), at a resumed entry; for any FL4 program `m` reducing to
the endpoint-state switch. -/
theorem JAtZ.recvSendFPJGM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
    (hAct : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv)
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
  have hCI : CurInv σ := J.curInv (by obtain ⟨u0, hu0, -⟩ := hAct; rw [hu0]; intro h; cases h)
  have hnd : xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none := by
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hct, hkt] at hkc; cases hkc; exact Or.inr (by rw [hcs]; simp)
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  have hswT : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv ∧ u ≠ sd'.bv := fun u hu => by
    obtain ⟨u0, hu0, hne⟩ := hAct
    rw [hu0] at hu; cases hu
    refine ⟨hne, fun e0 => ?_⟩
    obtain ⟨x0, -, -, -, hk0, -, hr0, -, -, -⟩ := schedulable_inv (J.act.1 _ hu0)
    rw [e0, hks] at hk0; cases hk0; rw [hstd] at hr0; cases hr0
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
  have hna3 : ∀ u ∈ Z.T, (u = sd' ∨ u = t) → L.actionW s3 ≠ u := fun u hu hut =>
    actionW_ne_of hSR3 hu (fun h => by
      obtain ⟨h1, h2⟩ := hswT _ (act3.symm.trans h)
      rcases hut with rfl | rfl
      · exact h2 rfl
      · exact h1 rfl)
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
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hqbT hrbT (hna3 t ht (Or.inr rfl))
        (hiw3 t ht hit) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a sd' t rv cd h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hcA hcd)) ?_
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
    ⟨fun u hu => by
      rw [hactP] at hu
      have hs5 := Fr5.sched (J.act.1 u hu)
      have hur : u ≠ rv.bv := fun e0 => by
        obtain ⟨x0, -, -, -, hk0, -⟩ := schedulable_inv hs5
        rw [e0, hkwa] at hk0; cases hk0
      exact ps_schedM hkta hkwa (hswT u hu).2 hur hs5, ps_idleOK hkta hkwa hws hidT (Fr5.idleOK J.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    have hCIa : CurInv σ5 := Fr5.curInv hCI
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
  have hrun6 : CurRunM σ' := Or.inl (by
    rw [hactP]; obtain ⟨u0, hu0, -⟩ := hAct; rw [hu0]; intro h; cases h)
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
theorem JAtZ.recvSendPJGM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs)) (hfs : xs.tcbFault = none)
    (hAct : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv)
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
  have hAy : ∃ u, σy.schedulerAction = .switchThread u ∧ u ≠ t.bv := by rw [hsay]; exact hAct
  have hcty' : σy.curThread = t.bv := hcty.trans hct
  have hCI : CurInv σy := Jy.curInv (by obtain ⟨u0, hu0, -⟩ := hAy; rw [hu0]; intro h; cases h)
  have hrly : σy.releaseQueue = σ.releaseQueue := by
    have e := congrArg Fl4Spec.AbstractState.releaseQueue hCnKy.1; exact e
  have hnd : xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none := by
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hcty', hkty] at hkc; cases hkc; exact Or.inr (by rw [hcs]; simp)
  have hnrT : t.bv ∉ σy.releaseQueue := by rw [← hcty']; exact hCI.notRel
  have hswT : ∀ u, σy.schedulerAction = .switchThread u → u ≠ t.bv ∧ u ≠ sd'.bv := fun u hu => by
    obtain ⟨u0, hu0, hne⟩ := hAy
    rw [hu0] at hu; cases hu
    refine ⟨hne, fun e0 => ?_⟩
    obtain ⟨x0, -, -, -, hk0, -, hr0, -, -, -⟩ := schedulable_inv (Jy.act.1 _ hu0)
    rw [e0, hksy] at hk0; cases hk0; rw [hstd] at hr0; cases hr0
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
  have hna3 : ∀ u ∈ Z.T, (u = sd' ∨ u = t) → L.actionW s3 ≠ u := fun u hu hut =>
    actionW_ne_of hSR3 hu (fun h => by
      obtain ⟨h1, h2⟩ := hswT _ (act3.symm.trans h)
      rcases hut with rfl | rfl
      · exact h2 rfl
      · exact h1 rfl)
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
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hqbT hrbT (hna3 t ht (Or.inr rfl))
        (hiw3 t ht hit) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a sd' t rv cd h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hcA hcd)) ?_
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
    ⟨fun u hu => by
      rw [hactP] at hu
      have hs5 := Fr5.sched (Jy.act.1 u hu)
      have hur : u ≠ rv.bv := fun e0 => by
        obtain ⟨x0, -, -, -, hk0, -⟩ := schedulable_inv hs5
        rw [e0, hkwa] at hk0; cases hk0
      exact ps_schedM hkta hkwa (hswT u hu).2 hur hs5, ps_idleOK hkta hkwa hws hidT (Fr5.idleOK Jy.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    have hCIa : CurInv σ5 := Fr5.curInv hCI
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
  have hrun6 : CurRunM σ' := Or.inl (by
    rw [hactP]; obtain ⟨u0, hu0, -⟩ := hAy; rw [hu0]; intro h; cases h)
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



set_option maxHeartbeats 64000000 in
/-- **`receive_ipc` from a head sender with a timeout fault and an SC pushing
a reply at `J`** (module docstring; no donation),
has the grant or grant-reply right, the receiver passes a reply object
(covered, `hcovR`), at a resumed entry; for any FL4 program `m` reducing to
the endpoint-state switch. -/
theorem JAtZ.recvSendFPTJM (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
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
    (hAct : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv)
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
  have hCI : CurInv σb := Jb.cur.resolve_left (fun h => by
      have h' : σ.schedulerAction = .chooseNewThread := h
      obtain ⟨u0, hu0, -⟩ := hAct
      rw [hu0] at h'; cases h')
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  have hswT : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv ∧ u ≠ sd'.bv := fun u hu => by
    obtain ⟨u0, hu0, hne⟩ := hAct
    rw [hu0] at hu; cases hu
    refine ⟨hne, fun e0 => ?_⟩
    obtain ⟨x0, -, -, -, hk0, -, hr0, -, -, -⟩ := schedulable_inv (J.act.1 _ hu0)
    rw [e0, hks] at hk0; cases hk0; rw [hstd] at hr0; cases hr0
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
  have hna3 : ∀ u ∈ Z.T, (u = sd' ∨ u = t) → L.actionW s3 ≠ u := fun u hu hut =>
    actionW_ne_of hSR3 hu (fun h => by
      obtain ⟨h1, h2⟩ := hswT _ (act3.symm.trans h)
      rcases hut with rfl | rfl
      · exact h2 rfl
      · exact h1 rfl)
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
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hqbT hrbT (hna3 t ht (Or.inr rfl))
        (hiw3 t ht hit) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a sd' t rv cd h3 hXc (Or.inl (Or.inr rfl)) hB3 hX3 hS3' hSg3 hsH
        hqbS hrbS (hna3 sd' hsT (Or.inl rfl)) (hiw3 sd' hsT his) hcold hwH hw00 hz3 htH hts hcA hcd)) ?_
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
    ⟨fun u hu => by
      rw [hactP] at hu
      have hs5 := Fr5.sched (Jb.act.1 u (show σb.schedulerAction = _ from hu))
      have hur : u ≠ rv.bv := fun e0 => by
        obtain ⟨x0, -, -, -, hk0, -⟩ := schedulable_inv hs5
        rw [e0, hkwa] at hk0; cases hk0
      exact ps_schedM hkta hkwa (hswT u hu).2 hur hs5, ps_idleOK hkta hkwa hws hidT (Fr5.idleOK Jb.act.2)⟩
  have hcur6 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := by
    have hCIa : CurInv σ5 := Fr5.curInv hCI
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
  have hrun6 : CurRunM σ' := Or.inl (by
    rw [hactP]; obtain ⟨u0, hu0, -⟩ := hAct; rw [hu0]; intro h; cases h)
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

/-- **`receive_ipc` from the head sender pushing a reply at a switch mid
state** (`PushOK`; module docstring), the receiver as in
XTopJointRecvSendP's `JAtZ.recvSendP0X`. -/
theorem JAtZ.recvSendP0XM (hAT : P0.ArchTotal arI)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    (hAct : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv)
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
  · exact J.recvSendPJGM hAT ht hkt hrun hbN hct hni hnq he hk hks hfs hAct cb c1 c2 c3 c4 hrc hcovR hcl hyes hrn
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFPJGM hAT ht hkt hrun hbN hct hni hnq he hk hks hft hto hAct cb c1 c2 c3 c4 hrc hcovR hyes hrn
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

/-- **`receive_ipc` from a head sender with a timeout fault and an SC at a
switch mid state** (`TmoOK`; module docstring): XTopJointRecvSendT's
`JAtZ.recvSendT0X` with `JAtZ.recvSendFPTJM` for the push. -/
theorem JAtZ.recvSendT0XM (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    (hAct : ∃ u, σ.schedulerAction = .switchThread u ∧ u ≠ t.bv)
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
    exact J.recvSendFPTJM hAT hmax htu ht hkt hrun hbN hct hni hnq he hk hks hft hsn hAct cb c1 c2 c3 c4
      hrc (hcovR hrv0) hp.2 hp.1 b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFTJ hAT hmax htu ht hkt hrun hbN hct he hk hks hft hsn cb c1 c2 c3 c4 hrc (noPush_of hp)
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

end

end

end Fl4Proofs.P3
