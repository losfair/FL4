/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch21 (a)): **the
endpoint receive at a `chooseNewThread` mid state where `CurInv` holds**
(`MidC`, XTopJointRecvSigC), every case with a null or free reply.
Scripted copies (sch21gen/gen.py `c`, untracked) of the switch-mid endpoint
leaves (XTopJointKEntry11M / XTopJointRecvIpcBlockM / XTopJointRecvRetM)
and dispatchers (XTopJointKEntry11M/13M/14M/15M) with `MidC` for `MidE`:
`J.curInv hni.ncn` → `MidC`'s `CurInv`, `canBlockCurM` → `canBlockCurMC`,
the "switch target is not ct" steps closed by the action being
`chooseNewThread` (`set_thread_state_act` changes only `resumeCurThread`,
`maybe_return_sc`'s `reschedule_required` from `chooseNewThread` enqueues
nothing, `JAtZ.maybeReturnJQ` asks only that no switch to ct is pending).

* `JAtZ.recvIpcActJC`, `JAtZ.recvIpcBlockJGC/JC/NJGC`, `JAtZ.recvIpcRetJC`,
  `JAtZ.recvSendRetJC/RetPJC/RetPDJC/RetTJC` (copies);
* `JAtZ.recvSendP0XC` / `JAtZ.recvSendT0XC` (hand-written, the switch-mid
  `…0XM` wrappers): the reply-pushing head senders by XTopJointRecvSendPC's
  `recvSendPJGC` / `recvSendFPJGC` (the receiver has the current SC, so the
  push does not donate) and the timeout-fault sender with an SC by
  XTopJointRecvSendT's resumed `recvSendFPTJ`, whose `hAct` already admits
  `chooseNewThread` with the receiver out of the release queue;
* `jRecvIpcDoneC`, `jRecvIpcDoneC2`, `jRecvIpcDoneC3`, `jRecvIpcUC`: every
  `receive_ipc` at a `MidC` state with a null or free reply
  (`ipcDoneM3_of`'s case split is state-only, reused).

Not here: a reply object linked to another thread. Its `cancel_ipc` may
return an SC that thread donated to ct (`reply_remove`), after which ct has no
SC and `CurInv` fails, so the state after is not `MidC`; that case stays in
the premise (`IpcLinked`, XTopJointKEntry20M).
-/
import Fl4Proofs.P3.XTopJointRecvSendPC
import Fl4Proofs.P3.XTopJointRecvSigC
import Fl4Proofs.P3.XTopJointKEntry15M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}


set_option maxHeartbeats 16000000 in
/-- **`receive_ipc` with an active bound notification at `J`** (module
docstring): the current thread at a mid state (`MidC`: a reschedule pending with `CurInv`; was `MidE`: resumed or a switch
to another thread pending), as `JAtZ.recvSigActiveJM`. -/
theorem JAtZ.recvIpcActJC (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidC σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt0 : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hbn : xt.tcbBoundNotification = some n.bv) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) {e : U64} {xe : Fl4Spec.Endpoint} (hke : σ.kheap e.bv = some (.endpoint xe))
    (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := hni.2.2.2
  have hkt := hkt0
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  obtain ⟨ys, ms, hks⟩ := hC.sc
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurMC ht hcur hkt hrn hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  -- the badge register
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hXb := badge_wr_irel J.ip hI ht hkt (L.mem s (nBadgeA n))
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register _ hXb
  rw [hb0] at J1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))).kheap n.bv = some (.notification x) := by
    simp [updK, hnt, hk]
  -- the notification's state
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI J1.ip hI1.1 hn hk1 hact
  have hSch2 := hI1.2.2.1.stable hW2 hS2
  obtain ⟨Q, R, hc, hs⟩ := hSch2.lists
  obtain ⟨xt2, hkt2, -, -, hsct2, -⟩ := hs.tcb t ht
  have hkt2' : (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv =
      some (.tcb (setReg xt Fl4Spec.badge_register b0)) := by
    simp [updK, hnt.symm]
  rw [hkt2'] at hkt2; cases hkt2
  have hsw : optRef (L.mem (recvActS st s t n) (P1.scA t)) = some σ.curSc := hsct2.symm.trans hscc
  have h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hsw; cases hsw
  have hcw : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC := by
    apply P1.eq_of_bv
    rw [Notif.optRef_ne h0] at hsw
    rw [Option.some.inj hsw]
    exact hs.curSc.trans (congrArg (fun q => (Sched.nodeW st (recvActS st s t n) q layout.node.CUR_SC).bv) hc.cur).symm
  have heq := spec_eq_ok (receive_signal_active_eq (arI := arI) (a := a) blk hst h0 hcw)
  -- P1's `BlkOK` after
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.receive_signal.ipc hAT s a t n blk Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) (by rw [epState_eq, hst, ntfn_consts.2.2]; decide)
  rw [heq, WP.spec_ok] at p1
  simp only [WP.uncurry'_pair] at p1
  -- the notification write at `J`
  have hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := fun l h => by rw [hact] at h; cases h
  obtain ⟨σ', V', hsp', -, J2⟩ := J1.signal_badge_post hn hk1 hxw
    (y := Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) (fun l h => by cases h) rfl rfl rfl
    ⟨_, rfl, hR2, hS2, hW2, NoBlock.ntfnUpd _ _ _⟩ p1
  obtain rfl := (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hsp').1))
  -- the spec's outcome and FL4's
  have hct : σ.curSc ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  have hcn : σ.curSc ≠ n.bv := fun e => by rw [e, hk] at hks; cases hks
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have ht0 : t ≠ 0#u64 := fun e => by
    obtain ⟨Q1, R1, hc1, -⟩ := J.xtop.fin.1.1.1.lists
    exact (hc1.tcbs t ht).ne0 (by rw [e]; rfl)
  have heqI := spec_eq_ok (receive_ipc_preA (ar := arI) s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
    (by rw [← hbound]; exact hbz) hst (complete_signal_cur_eq (arI := arI) (a := a) ht0 hst h0 hcw))
  have hspecI := receiveIpc_active b rights blk (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hke hk hact
  rw [hspecI, completeSignal_cur hkt hk hact hscc hks hct hcn hnt, heqI, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩

set_option maxHeartbeats 16000000 in
set_option maxHeartbeats 16000000 in
/-- **The blocking receive at `J` under a pending reschedule (with `CurInv`)** (`MidC`, action not
resumed; `JAtZ.recvIpcBlockJG`'s changes as XTopJointRecvSigM's
`recvSigBlockJM`), ending in `JAtZR`: the current thread
`t` blocks receiving on the idle or receiving endpoint `e`, covered by a cap
(`hcov`), with a null reply cap or one naming a reply object linked to no
thread, covered by the cap (`hcovR`); `hred`, `hsp`: FL4's and the spec's
`receive_ipc` reduce to the wait (no bound notification: `receive_ipc_block_red`,
`receiveIpc_noSend`; a bound idle or waiting one: XTopJointRecvIpcBound), stated
for any FL4 program `m` reducing to the wait. -/
theorem JAtZ.recvIpcBlockJGC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    {m : Result (S × A)} (hred : ∀ {P : S × A → Prop}, (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ P ⦄ → m ⦃ P ⦄)
    (hsp : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
      Fl4Spec.receiveIpcBlocked true t.bv e.bv (optRef rv) σ) :
    m ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := hni.2.2.2
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hnb3 : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    rcases runnable_code hr with h | h | h <;> rw [h] <;> decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [h] at hr; cases hr
  have htq : t.bv ∉ x.epQueue := Endp.not_queued hI.1.toE ht hkt hnb3 e he x hk
  have hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.epQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, -, hsrt, -, hactK⟩ :=
    recvIpcBlock_eqM hkt hk hc htq hq hr (J.isorted.1 _ _ hk) b rights (replyArg_spec J.ip.e hI.1.toE hrc) hsp
  -- the reply object (if any): in `R`, linked to no thread
  have hrv : rv ≠ 0#u64 → rv ∈ Z.R ∧ L.mem s (Endp.rTcbA rv) = 0#u64 := fun h0 => replyArg_ne J.ip.e hrc h0
  have hact' : σ'.schedulerAction = σ.schedulerAction := hactK hsw
  -- P1's `BlkOK` after and footprint
  have hcb := J.canBlockCurMC ht hcur hkt hr hti hnrl hni hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hx := hI.1.toE.at_ep he hk
  have hst2 : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => simp [Endp.CanBlock] at hc
  have hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 2#u64 := by rw [epState_eq]; exact hst2
  have hrH : rv ≠ 0#u64 → rv ∈ P1.Heap.replies H := fun h => J.zH.2.2.1 rv (hrv h).1
  have p1b := spec_lift_ok (P1.endpoint.wait_for_sender.inv s t e true rv Q0 R0 h0 hB0 hX0 hS0 hSg0
    (J.zH.1 t ht) (fun _ => hcb) hHe hst0 (fun h => ⟨hrH h, Or.inl (hrv h).2⟩)) a
  have p1f := spec_lift_ok (P1.endpoint.wait_for_sender.footR (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
    (Z := P1.Heap.scBits H) s t e rv h0 hcb hHe
    (fun h => ⟨hSg0.sub _ (hX0.1.tcbW (hrH h)), hX0.1.tcbW (hrH h)⟩)) a
  apply hred
  refine WP.spec_mono (WP.spec_and (WP.spec_and (wait_for_sender_blockF J.ip s a σ hI ht hkt hnb3 hnn he hk hc
    (J.qsortedE e he) b rights hrc hsp) p1b) p1f) ?_
  rintro ⟨s', a'⟩ ⟨⟨⟨ea, σ0, h0eq, hIR, hW⟩, hbk⟩, hfoot⟩
  simp only at ea hbk hfoot hIR hW
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := ⟨⟨Q0, R0, hbk.1⟩, hbk.2⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  -- the assembly (as XTopJointSendBlock's `JAtZ.sendBlockJ`)
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hW
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB_free hy hyt, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := by
    refine J.act.keepE (E := fun p => p = t.bv) ⟨fun p x0 hp hx => ?_, fun p y m hp => ⟨y, F.scF hp, rfl⟩⟩
      (fun u hu => Or.inl (by rw [F.sk.rel] at hu; exact hu)) (Or.inl hact') F.sk.idle (fun u hu => ?_)
      (fun h => hti (hcur.trans h.symm)) F.sk.isc
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      rcases hs' with e1 | ⟨e1, -⟩
      · rw [hk3, e1]
      · exact absurd e1 hp
    · rw [hni.2.2.1] at hu; cases hu
  have hcur3 : CurInvR σ' := fun h => absurd (hact'.symm.trans h) hsw
  have hrun3 : CurRunM σ' := Or.inl (by rw [hact']; exact hsw)
  -- the dead: the thread is not dead (runnable); the endpoint and the reply leave the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rcases runnable_code hr with h | h | h <;> rw [h] <;> decide)
  set D' : Set U64 := if rv = 0#u64 then D \ {e} else (D \ {e}) \ {rv} with hD'
  have hD'D : ∀ q ∈ D', q ∈ D \ {e} ∧ Notif.optRef rv ≠ some q.bv := by
    intro q hq
    by_cases h0 : rv = 0#u64
    · rw [hD', if_pos h0] at hq
      exact ⟨hq, by rw [h0, optRef_zero]; intro h; cases h⟩
    · rw [hD', if_neg h0] at hq
      refine ⟨hq.1, fun h => hq.2 ?_⟩
      rw [Notif.optRef_ne h0] at h
      exact (P1.eq_of_bv (Option.some.inj h)).symm
  have hdead : ∀ q ∈ D', DeadP (L := L) H s' q := fun q hq' => by
    obtain ⟨hq, hqr⟩ := hD'D q hq'
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqe : q.bv ≠ e.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => ?_)
      (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, F.replyF' hx hqr, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1
      (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.epF hx
      rcases hc' with rfl | e1
      · exact hy
      · exact absurd e1 hqe
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D')
  -- no reply names the runnable thread (`SchedValid.replyTcb`)
  have hnt : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb ≠ some t.bv := by
    intro d _ xr hkr hrt
    obtain ⟨x', hk', hs'⟩ := J.sv.replyTcb _ xr _ hkr hrt
    rw [hkt] at hk'; cases hk'
    rcases hs' with hs' | ⟨ep, dd, hs'⟩ <;> rw [hs'] at hr <;> cases hr
  -- the reply (if any) was free, so it has null links
  have hrq : ∀ d ∈ Z.R, Notif.optRef rv = some d.bv → L.mem s' (rNextA d) = 0#u64 ∧ L.mem s' (rPrevA d) = 0#u64 := by
    intro d hd hdr
    have h0 : rv ≠ 0#u64 := fun h => by rw [h, optRef_zero] at hdr; cases hdr
    rw [Notif.optRef_ne h0] at hdr
    obtain rfl : rv = d := P1.eq_of_bv (Option.some.inj hdr)
    obtain ⟨xr, hkr, hxr⟩ := hI.1.toE.reply rv hd
    obtain ⟨-, h2, h3⟩ := J.rfree rv hd ⟨xr, hkr, by rw [hxr, (hrv h0).2, optRef_zero]⟩
    obtain ⟨e1, e2⟩ := k4 rv hd
    exact ⟨by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hRR' := J.rrecv.frameR k4 F hnt hrq
  have hjcov : JCovD (L := L) Z.th H Z.G D' Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    have hcv : JCovD (L := L) Z.th H Z.G D' Cs s := by
      by_cases h0 : rv = 0#u64
      · rw [hD', if_pos h0]; exact J.jcov.undead hcov.1 hcov.2
      · rw [hD', if_neg h0]; exact (J.jcov.undead hcov.1 hcov.2).undead (hcovR h0).1 (hcovR h0).2
    exact hcv.same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from a runnable state)
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, hnrl⟩
  obtain ⟨hIB, -⟩ := (J.inv.toBut t.bv).ik hnqT hik
  have hrib : RelIfBound σ' t.bv := Ipc.RelIfBound.of_keep (J.inv.rd t.bv xt hkt (Or.inl hr)) F.skeep
  have I3 : Inv σ' := hIB.inv fun _ _ _ => hrib
  -- `BlockedScActive`: the thread's SC is the current SC, active
  have hscA : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp).2⟩
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := Option.some.inj (hscc.symm.trans hxs)
    rw [← e1] at hp
    exact hC.active (J.curSc_ne_idle hC hti) y n hp
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D' s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J3 := J.toR.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R hKd F.sk.orig hidl.1 (fun p hp => by
      have h1 := J.zD_diffE he p hp
      have hT : H p = some .tcb := J.zH.1 p (J.thT p (J.ztcb_tcb hp))
      rw [hD']
      split_ifs with h0
      · exact h1
      · exact ⟨h1, fun e' => by rw [Set.mem_singleton_iff.1 e', J.zH.2.2.1 rv (hrv h0).1] at hT; cases hT⟩)
  rw [heq]
  exact ⟨_, Set.mem_singleton _, J3.xtop.relTop, _, _, _, _, _, _, J3⟩

/-- **The blocking receive at `J` under a pending reschedule (with `CurInv`)**, no bound
notification: `JAtZ.recvIpcBlockJGC`. -/
theorem JAtZ.recvIpcBlockJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights)
    (hred : ∀ {P : S × A → Prop}, (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ P ⦄ → endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ P ⦄)
    (hsp : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
      Fl4Spec.receiveIpcBlocked true t.bv e.bv (optRef rv) σ) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  J.recvIpcBlockJGC ht hcur hni hsw hnq hkt he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights hred hsp

set_option maxHeartbeats 4000000 in
/-- **The blocking receive with a bound idle or waiting notification at `J`**
(module docstring): the notification's SC is not the thread's (`hnr`); at a
mid state with a pending reschedule (with `CurInv`) (`MidC`, as `JAtZ.recvIpcBlockJGC`). -/
theorem JAtZ.recvIpcBlockNJGC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hnr : ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none))
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x)
    (hcov : (∀ k, Z.th e = some k → Covered (L.mem s) Z.G e.val (e.val + max (objSize k) 1)) ∧
      (∀ k, H e = some k → Covered (L.mem s) Z.G e.val (e.val + 2 ^ k.bits)))
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (hcovR : rv ≠ 0#u64 → (∀ k, Z.th rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + max (objSize k) 1)) ∧
      (∀ k, H rv = some k → Covered (L.mem s) Z.G rv.val (rv.val + 2 ^ k.bits)))
    (cb : U64) (c1 c2 c3 c4 : Bool) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  have hx := hI.1.toE.at_ep he hk
  have hst2 : stOf (L.mem s) e = 0#u64 ∨ stOf (L.mem s) e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx.1
    | recvEP q => exact Or.inr hx.1
    | sendEP q => exact absurd rfl (hns q)
  have hxt := hI.1.toE.at_tcb ht hkt
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
  have hwn : L.mem s (nScA n) = 0#u64 ∨ L.mem s (nScA n) ≠ L.mem s (P1.scA t) := by
    have hsN : xn.ntfnSc = optRef (L.mem s (nScA n)) := hxn.sc
    obtain ⟨Q0, R0, -, hs0⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨xt0, hkt0, -, -, hsct, -⟩ := hs0.tcb t ht
    rw [hkt] at hkt0; cases hkt0
    by_cases h0 : L.mem s (nScA n) = 0#u64
    · exact Or.inl h0
    · refine Or.inr fun he' => hnr ⟨?_, ?_⟩
      · rw [hsN, he']; exact hsct.symm
      · rw [hsN, Notif.optRef_ne h0]; simp
  exact J.recvIpcBlockJGC ht hcur hni hsw hnq hkt he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights
    (fun h => receive_ipc_blockN_red hrc hbound (by rw [← hbound]; exact hbz) hstN hwn hst2 h)
    (receiveIpc_boundNA b rights true (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna (fun _ => hnr))

set_option maxHeartbeats 8000000 in
/-- **The blocking receive with a bound notification lending the thread its
SC at `J`** (module docstring). -/
theorem JAtZ.recvIpcRetJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e : U64} (he : e ∈ Z.E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : Endp.CanBlock true x) {cb : U64} {sd g gr : Bool}
    (hHd : JHeld (L := L) Z.th s (.Endpoint e cb sd true g gr)) {rc : capability.Cap}
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := hni.2.2.2
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  -- the SC `i` lent by the notification, the thread's
  obtain ⟨hl1, hl2⟩ := hlend
  obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hl2
  have hxs0 : xt.tcbSchedContext = some i0 := hl1.symm.trans hi0
  obtain ⟨y, m, hky, -⟩ := J.inv.back t.bv xt i0 hkt hxs0
  obtain ⟨i, hiC, rfl⟩ := J.obj.sc _ y m hky
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, hnrl⟩
  obtain ⟨σ2, he2, kt, -, ko, ct, -, -, -, hidl, -, rq, a1, -, hrq2⟩ :=
    maybeReturn_shape J.inv hkn hkt hky hxs0 hi0 hnqT
  -- FL4's bound-notification words
  have hxt := hI.1.toE.at_tcb ht hkt
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
  have hcb := J.canBlockCurMC ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  have hsp1 := receiveIpc_boundR b rights (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna he2
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2.2.1] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
  rintro s' ⟨hW, σ', he', Ac', Lst', J2⟩
  rw [the_result he2 he'] at J2
  have hI2 := J2.xtop.irelK J2.ks J2.buf
  -- the objects kept by `maybe_return_sc`
  have hte : e.bv ≠ t.bv := fun h => by rw [h, hkt] at hk; cases hk
  have hie : e.bv ≠ i.bv := fun h => by rw [h, hky] at hk; cases hk
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by rw [ko _ hte hie]; exact hk
  have hnt : n.bv ≠ t.bv := fun h => by rw [h, hkt] at hkn; cases hkn
  have hni' : n.bv ≠ i.bv := fun h => by rw [h, hky] at hkn; cases hkn
  have hkn2 : σ2.kheap n.bv = some (.notification xn) := by rw [ko _ hnt hni']; exact hkn
  have hcur2 : σ2.curThread = t.bv := ct.trans hcur
  have hti2 : σ2.curThread ≠ σ2.idleThread := by rw [ct, hidl]; exact hni.1
  have hnq2 : ∀ d p, σ2.curThread ∉ σ2.readyQueues d p := by rw [hcur2]; exact hrq2
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
  obtain ⟨hcov, hcovR⟩ := J.recvCov_ofW hW he hHd hHr hrc
  have hx2 := hI2.1.toE.at_ep he hk2
  have hst2 : stOf (L.mem s') e = 0#u64 ∨ stOf (L.mem s') e = 2#u64 := by
    cases x with
    | idleEP => exact Or.inl hx2.1
    | recvEP q => exact Or.inr hx2.1
    | sendEP q => exact absurd rfl (hns q)
  have hsp2 := receiveIpc_boundNA b rights true (replyArg_spec J2.ip.e hI2.1.toE hrc2) kt hbn hk2 hns hkn2 hna
    (fun _ h => h.2 h.1)
  have key := J2.recvIpcBlockJG ht hcur2 hti2 hnq2 (fun h => hnrl (rq _ h)) kt hr (Or.inr ⟨a1 hcur.symm, rfl⟩) he
    hk2 hc hcov hrc2 hcovR cb sd true g gr b rights (m := recvTail st arI s' a t e rv)
    (fun h => recvTail_wait hst2 h) hsp2
  rw [hsp1, ← hsp2]
  exact key

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender with a bound notification
lending the receiver its SC at `J`** (module docstring), the sender as in
XTopJointRecvSendF's `SendOK`. -/
theorem JAtZ.recvSendRetJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : SendOK xs rc)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hC : CurInv σ := hni.2.2.2
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
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
  obtain ⟨σ2, he2, kt, -, ko, ct, -⟩ := maybeReturn_shape J.inv hkn hkt hky hxs0 hi0 hnqT
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
  have hcb := J.canBlockCurMC ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2.2.1] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
  rintro s' ⟨-, σ', he', Ac', Lst', J2⟩
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
  have key := J2.recvSendJX ht kt hr (Or.inr ⟨n.bv, xn, hbn, hkn2, hna, fun _ => hnr2⟩) hcur2 he hk2 hks2
    cb c1 c2 c3 c4 hrc2 hok b rights (m := Endp.recvTail st arI s' a t e rv) (fun h => by unfold Endp.recvTail; exact h)
  rw [hsp]
  exact key

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender without an SC pushing a
reply, the receiver's bound notification lending it its SC, at `J`** (module
docstring): XTopJointRecvSendRet's route, then XTopJointRecvSendP's
`JAtZ.recvSendPJG` / `JAtZ.recvSendFPJG` at the state after
`maybe_return_sc` (a reschedule pending, the receiver without an SC). -/
theorem JAtZ.recvSendRetPJC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : PushOK xs rc) (hsn : xs.tcbSchedContext = none)
    {g gr : Bool} (hHd : JHeld (L := L) Z.th s (.Endpoint e cb c1 true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hC : CurInv σ := hni.2.2.2
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
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
  have hcb := J.canBlockCurMC ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2.2.1] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
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
  have hrv0 : rv ≠ 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
    · exact absurd h1 hok.1
    · exact (J.rp.align rv hr).2.1
  obtain ⟨-, hcovR⟩ := J.recvCov_ofW hW he hHd hHr hrc
  have hni2 : σ2.curThread ≠ σ2.idleThread := by rw [ct, idl]; exact hni.1
  have hnq2 : ∀ dm p, σ2.curThread ∉ σ2.readyQueues dm p := by rw [hcur2]; exact rq
  have hA2 : σ2.schedulerAction = .resumeCurThread ∨ (σ2.schedulerAction = .chooseNewThread ∧
      t.bv ∉ σ2.releaseQueue ∧ xs.tcbSchedContext = none) :=
    Or.inr ⟨act hcur.symm, fun h => hnrl (rel _ h), hsn⟩
  have hbN2 : (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = none ∨
      ∃ n' xn', (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = some n' ∧
        σ2.kheap n' = some (.notification xn') ∧ Fl4Spec.isActive xn' = false ∧
        (true = true → ¬ (xn'.ntfnSc = (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbSchedContext ∧
          xn'.ntfnSc ≠ none)) :=
    Or.inr ⟨n.bv, xn, hbn, hkn2, hna, fun _ => hnr2⟩
  rw [hsp]
  obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
  · exact J2.recvSendPJG hAT ht kt hr hbN2 hcur2 hni2 hnq2 he hk2 hks2 hfs hA2 cb c1 true g gr hrc2
      (hcovR hrv0) hcl hyes hrn b rights (m := Endp.recvTail st arI s' a t e rv)
      (fun h => by unfold Endp.recvTail; exact h)
  · exact J2.recvSendFPJG hAT ht kt hr hbN2 hcur2 hni2 hnq2 he hk2 hks2 hft hto hA2 cb c1 true g gr hrc2
      (hcovR hrv0) hyes hrn b rights (m := Endp.recvTail st arI s' a t e rv)
      (fun h => by unfold Endp.recvTail; exact h)

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender with an SC pushing a reply,
the receiver's bound notification lending it its SC, at `J`** (the
passive-server call; module docstring): XTopJointRecvSendRP's route, then
`JAtZ.recvSendPDJ` / `JAtZ.recvSendFPDJ` at the state after
`maybe_return_sc` (a reschedule pending, the receiver without an SC, the
current SC the notification's, now bound to no thread): the push donates the
sender's SC to the receiver. -/
theorem JAtZ.recvSendRetPDJC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) (hbn : xt.tcbBoundNotification = some n.bv)
    {xn : Fl4Spec.Notification} (hkn : σ.kheap n.bv = some (.notification xn))
    (hna : Fl4Spec.isActive xn = false) (hlend : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)
    {e sd : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.sendEP (sd.bv :: q))))
    {xs : Fl4Spec.Tcb} (hks : σ.kheap sd.bv = some (.tcb xs))
    (cb : U64) (c1 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : PushOK xs rc) (hsn : xs.tcbSchedContext ≠ none)
    {g gr : Bool} (hHd : JHeld (L := L) Z.th s (.Endpoint e cb c1 true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hR := hI.1.toE
  have hC : CurInv σ := hni.2.2.2
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
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
  obtain ⟨σ2, he2, kt, ki, ko, ct, cs, -, -, idl, -, rel, act, -, rq⟩ := maybeReturn_shape J.inv hkn hkt hky hxs0 hi0 hnqT
  -- the current SC: the notification's (`CurInv`), bound to no thread after `maybe_return_sc`
  have hcsI : σ.curSc = i.bv := by
    obtain ⟨xc, hkc, hcs, -⟩ := hC.tcb
    rw [hcur, hkt] at hkc; cases hkc
    exact Option.some.inj (hcs.symm.trans hxs0)
  -- the sender's SC
  obtain ⟨p0, hp0⟩ := Option.ne_none_iff_exists'.1 hsn
  obtain ⟨yp, mp, hkyp, -⟩ := J.inv.back sd.bv xs p0 hks hp0
  obtain ⟨p, hpC, rfl⟩ := J.obj.sc _ yp mp hkyp
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
  have hcb := J.canBlockCurMC ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2.2.1] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
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
  have hrv0 : rv ≠ 0#u64 := by
    rcases hrc with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
    · exact absurd h1 hok.1
    · exact (J.rp.align rv hr).2.1
  obtain ⟨-, hcovR⟩ := J.recvCov_ofW hW he hHd hHr hrc
  have hni2 : σ2.curThread ≠ σ2.idleThread := by rw [ct, idl]; exact hni.1
  have hnq2 : ∀ dm p, σ2.curThread ∉ σ2.readyQueues dm p := by rw [hcur2]; exact rq
  have hk02 : σ2.kheap σ2.curSc = some (.schedContext (Fl4Spec.scTcbUpdate (fun _ => none) y) m) := by
    rw [cs, hcsI]; exact ki
  have hcsC2 : ∃ c0 ∈ Z.C, c0.bv = σ2.curSc := ⟨i, hiC, by rw [cs, hcsI]⟩
  have hbN2 : (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = none ∨
      ∃ n' xn', (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbBoundNotification = some n' ∧
        σ2.kheap n' = some (.notification xn') ∧ Fl4Spec.isActive xn' = false ∧
        (true = true → ¬ (xn'.ntfnSc = (Fl4Spec.tcbSchedContextUpdate (fun _ => none) xt).tcbSchedContext ∧
          xn'.ntfnSc ≠ none)) :=
    Or.inr ⟨n.bv, xn, hbn, hkn2, hna, fun _ => hnr2⟩
  rw [hsp]
  obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
  · exact J2.recvSendPDJ hAT ht kt hr hbN2 hcur2 hni2 hnq2 he hk2 hks2 hfs hpC hp0 rfl (act hcur.symm)
      (fun h => hnrl (rel _ h)) hcsC2 hk02 rfl cb c1 true g gr hrc2 (hcovR hrv0) hcl hyes hrn b rights
      (m := Endp.recvTail st arI s' a t e rv) (fun h => by unfold Endp.recvTail; exact h)
  · exact J2.recvSendFPDJ hAT ht kt hr hbN2 hcur2 hni2 hnq2 he hk2 hks2 hft (fun b0 e0 => hsn (hto b0 e0))
      hpC hp0 rfl (act hcur.symm) (fun h => hnrl (rel _ h)) hcsC2 hk02 rfl cb c1 true g gr hrc2 (hcovR hrv0)
      hyes hrn b rights (m := Endp.recvTail st arI s' a t e rv) (fun h => by unfold Endp.recvTail; exact h)

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a head sender with a timeout fault and an
SC, the receiver's bound notification lending it its SC, at `J`** (module
docstring): XTopJointRecvSendRP's route, then `JAtZ.recvSendFPTJ` (a reply
pushed) or `JAtZ.recvSendFTJ` at the state after `maybe_return_sc`. -/
theorem JAtZ.recvSendRetTJC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidC σ)
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
  have hC : CurInv σ := hni.2.2.2
  have hnrl : t.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
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
  have hcb := J.canBlockCurMC ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2.2.1] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
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

/-- **`receive_ipc` from the head sender pushing a reply under a pending
reschedule, the receiver with an SC** (`PushOK`; module docstring). -/
theorem JAtZ.recvSendP0XC (hAT : P0.ArchTotal arI)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    (hAct : σ.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue ∧ xt.tcbSchedContext ≠ none)
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
  obtain ⟨hcn, hnr, hsc⟩ := hAct
  obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
  · exact J.recvSendPJGC hAT ht hkt hrun hbN hct hni hnq he hk hks hfs (Or.inr ⟨hcn, hnr, Or.inr hsc⟩)
      cb c1 c2 c3 c4 hrc hcovR hcl hyes hrn b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFPJGC hAT ht hkt hrun hbN hct hni hnq he hk hks hft hto (Or.inr ⟨hcn, hnr, Or.inr hsc⟩)
      cb c1 c2 c3 c4 hrc hcovR hyes hrn b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

/-- **`receive_ipc` from a head sender with a timeout fault and an SC under
a pending reschedule** (`TmoOK`; module docstring): XTopJointRecvSendT's
resumed `JAtZ.recvSendFPTJ` for the push. -/
theorem JAtZ.recvSendT0XC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrun : Fl4Spec.runnable xt.tcbState = true) {blk : Bool}
    (hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
      σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
      (blk = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)))
    (hct : σ.curThread = t.bv) (hni : σ.curThread ≠ σ.idleThread) (hnq : ∀ dm p, σ.curThread ∉ σ.readyQueues dm p)
    (hAct : σ.schedulerAction = .chooseNewThread ∧ t.bv ∉ σ.releaseQueue ∧ xt.tcbSchedContext ≠ none)
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
  obtain ⟨hcn, hnr, -⟩ := hAct
  obtain ⟨⟨bb, hft⟩, hsn⟩ := hok
  by_cases hp : rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
      dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
  · have hrv0 : rv ≠ 0#u64 := by
      rcases hrc with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hp.1
      · exact (J.rp.align rv hr).2.1
    exact J.recvSendFPTJ hAT hmax htu ht hkt hrun hbN hct hni hnq he hk hks hft hsn (Or.inr ⟨hcn, hnr⟩)
      cb c1 c2 c3 c4 hrc (hcovR hrv0) hp.2 hp.1 b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)
  · exact J.recvSendFTJ hAT hmax htu ht hkt hrun hbN hct he hk hks hft hsn cb c1 c2 c3 c4 hrc (noPush_of hp)
      b rights (J.recvPreN ht hkt hbN e cb c1 c2 c3 c4 hrc)

set_option maxHeartbeats 4000000 in
/-- **`IpcDoneM`'s receives at a reschedule mid state (`MidC`)** (module docstring). -/
theorem jRecvIpcDoneC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidC σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM (L := L) ct s σ p rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  rcases hD with hca | hcb | ⟨hcn, hnr0⟩ | ⟨hun, hcs, hnr0⟩
  · obtain ⟨⟨xt, n0, x, b0, hkt, hbn, hkn, hact⟩, hrr⟩ := hca
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    exact WP.spec_mono (J.recvIpcActJC hAT ht hcur hni hnq hkt hn hkn hbn hact true hke b sd true g gr hra b.bv
      (rightsOf sd true g gr)) fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ =>
        ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · obtain ⟨-, hbn, hns, hrr⟩ := hcb
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hx := hI.1.toE.at_ep he hke
    have hst2 : stOf (L.mem s) p = 0#u64 ∨ stOf (L.mem s) p = 2#u64 := by
      cases xe with
      | idleEP => exact Or.inl hx.1
      | recvEP q => exact Or.inr hx.1
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hbound : L.mem s (tBoundA ct) = 0#u64 :=
      optRef_none ((hI.1.toE.at_tcb ht hkt).bound.symm.trans (hbn xt hkt))
    exact J.recvIpcBlockJC ht hcur hni hsw hnq hkt he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr) (fun h => receive_ipc_block_red hra hbound hst2 h)
      (receiveIpc_noSend b.bv (rightsOf sd true g gr) true (replyArg_spec J.ip.e hI.1.toE hra) hkt (hbn xt hkt) hke
        (hns xe hke))
  · obtain ⟨-, ⟨xt, n0, xn, hkt, hbn, hkn, hna⟩, hns, hrr⟩ := hcn
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact J.recvIpcBlockNJGC ht hcur hni hsw hnq hkt hn hbn hkn hna (hnr0 xt _ xn hkt hbn hkn) he hke hcB hcov hra
      hcovR b sd true g gr b.bv (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := hni.run xt (by rw [hcur]; exact hkt)
    have hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
        (true = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) := by
      rcases hbn xt hkt with hb0 | ⟨n0, xn, hbn0, hkn, hna⟩
      · exact Or.inl hb0
      · exact Or.inr ⟨n0, xn, hbn0, hkn, hna, fun _ => hnr0 xt n0 xn hkt hbn0 hkn⟩
    exact WP.spec_mono (J.recvSendJ0X ht hkt hrun hbN hcur he hke' hks b sd true g gr hra hok b.bv
      (rightsOf sd true g gr)) fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ =>
        ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩

set_option maxHeartbeats 4000000 in
/-- **`IpcDoneM2`'s receives at a reschedule mid state (`MidC`)** (module docstring). -/
theorem jRecvIpcDoneC2 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidC σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM2 (L := L) ct s σ p rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  rcases hD with hD | ⟨hun, hcp | hcT⟩
  · exact jRecvIpcDoneC hAT J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr hD
  all_goals
    obtain ⟨xe, hke⟩ := hpE
    obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
    rw [Sched.bv_inj h] at he
    have hA : ∀ {x : Fl4Spec.Tcb}, σ.kheap ct.bv = some (.tcb x) →
        σ.schedulerAction = .chooseNewThread ∧ ct.bv ∉ σ.releaseQueue ∧ x.tcbSchedContext ≠ none :=
      fun {x} hx => by
        obtain ⟨⟨xc, hkc, hcs, -⟩, -, -, hnr⟩ := hni.2.2.2
        rw [hcur, hx] at hkc; cases hkc
        exact ⟨hni.2.2.1, by rw [← hcur]; exact hnr, by rw [hcs]; simp⟩
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := hni.run xt (by rw [hcur]; exact hkt)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcp
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hrv0 : rv ≠ 0#u64 := by
      rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hok.1
      · exact (J.rp.align rv hr).2.1
    obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact WP.spec_mono (J.recvSendP0XC hAT ht hkt hrun (hbn xt hkt) hcur hni.1 hnq (hA hkt) he hke' hks b sd true g gr hra
      (hcovR hrv0) hok b.bv (rightsOf sd true g gr)) fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ =>
        ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcT
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    exact WP.spec_mono (J.recvSendT0XC hAT hmax htu ht hkt hrun (hbn xt hkt) hcur hni.1 hnq (hA hkt) he hke' hks
      b sd true g gr hra (J.recvCov_of he hHd hHr hra).2 hok b.bv (rightsOf sd true g gr))
      fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩

set_option maxHeartbeats 4000000 in
/-- **`IpcDoneM3`'s receives at a reschedule mid state (`MidC`)** (module docstring). -/
theorem jRecvIpcDoneC3 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidC σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM3 (L := L) ct s σ p rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  rcases hD with hD | hD
  · exact jRecvIpcDoneC2 hAT hmax htu J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr hD
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  have hI := J.xtop.irelK J.ks J.buf
  suffices hRJ : endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ from
    WP.spec_mono hRJ fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  rcases hD with ⟨⟨-, ⟨xt, n0, xn, hkt, hbn, hkn, hna⟩, hns, hrr⟩, hL⟩ | ⟨hun, ⟨hcs, hL⟩ | hcr | ⟨hL, hcT⟩⟩
  · obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    exact J.recvIpcRetJC ht hcur hni hnq hkt hn hbn hkn hna (hL.at hkt hbn hkn) he hke hcB hHd hHr hra b.bv
      (rightsOf sd true g gr)
  · obtain ⟨-, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨n0, xn, hbn0, hkn, hna, hl1, hl2⟩ := hL xt hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    exact J.recvSendRetJC ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd true g gr hra hok b.bv
      (rightsOf sd true g gr)
  · obtain ⟨-, hbn, sd0, q, xs, hke', hks, hok⟩ := hcr
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨n0, xn, hbn0, hkn, hna, hl1, hl2⟩ := hbn xt hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    by_cases hsn : xs.tcbSchedContext = none
    · exact J.recvSendRetPJC hAT ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd hra hok hsn
        hHd hHr b.bv (rightsOf sd true g gr)
    · exact J.recvSendRetPDJC hAT ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd hra hok hsn
        hHd hHr b.bv (rightsOf sd true g gr)
  · obtain ⟨sd0, q, xs, hke', hks, hok⟩ := hcT
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨n0, xn, hbn0, hkn, hna, hl1, hl2⟩ := hL xt hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    exact J.recvSendRetTJC hAT hmax htu ht hcur hni hnq hkt hn hbn0 hkn hna ⟨hl1, hl2⟩ he hke' hks b sd hra hok
      hHd hHr b.bv (rightsOf sd true g gr)

/-- **`receive_ipc` with a null or free reply at a reschedule mid state (`MidC`)**
(module docstring). -/
theorem jRecvIpcUC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidC σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  jRecvIpcDoneC3 hAT hmax htu J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr (ipcDoneM3_of J ht hpE hun)

end

end

end Fl4Proofs.P3
