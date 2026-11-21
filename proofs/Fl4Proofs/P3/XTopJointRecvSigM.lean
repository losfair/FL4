/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch15): **the
blocking notification receive under a pending switch**, the first receive
leaf ending in `JAtZR` from a mid state whose action is `switchThread u`
(u ≠ ct; `MidE`). The template for the other blocking leaves under a switch:

* `Sched.recvSigBlock_act`: the spec's blocking receive keeps a non-resume
  action (`set_thread_state_act` turns only `resumeCurThread` into
  `chooseNewThread`).
* `JAtZ.recvSigBlockJM`: `JAtZ.recvSigBlockJ` (XTopJointRecvSigBlock) from
  `MidE` + action ≠ resume instead of `Entered`. Changes: `CurInv` from
  `J.curInv hni.ncn`; `CanBlock` by `canBlockCurM` (switch case);
  `ActIdle` after by `ActIdle.keepE` with `E = {ct}` (the switch target is
  not ct, its TCB and the release queue are kept); `CurInvR` after is vacuous
  (the action stays `switchThread u`), `CurRunM` by its first disjunct; the
  post is `JAtZR` via `JAtZR.cs_frameI` with a `JRestR`.
* `RJR` (`RelTopM ∧ JAtZR`), `jRecvSigHypM_of`: the notification receive at
  a switch mid state for every notification but a non-active one whose SC is
  the current SC (the SC-return case, `recvSigRetJ`'s, left to the premise):
  active by `JAtZ.recvSigActiveJM`, the rest by `recvSigBlockJM`.
-/
import Fl4Proofs.P3.XTopJointKEntry9M
import Fl4Proofs.P3.XTopJointRecvMid
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- The spec's blocking notification receive keeps a non-resume action. -/
theorem recvSigBlock_act {σ : State Unit} {t n : ObjRef} {xt : Tcb} {x : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hk : σ.kheap n = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (htq : t ∉ ntfnQueueOf x) (hq : ∀ y ∈ ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z))
    (hnr : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none)) (cb : Badge) (rt : CapRights)
    {σ' : State Unit} (he : receiveSignal (Z := Unit) t (.notificationCap n cb rt) true σ = ({((), σ')}, False))
    (hsw : σ.schedulerAction ≠ .resumeCurThread) : σ'.schedulerAction = σ.schedulerAction := by
  let x1 : Tcb := { xt with tcbState := .blockedOnNotification n }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  let q' := Notif.specIns (ntfnQueueOf x) (Sched.prioOf σ2) x1.tcbPriority t
  let y : Notification := { x with ntfnObj := .waitingNtfn q' }
  have htn : t ≠ n := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap n = some (.notification x) := by simp [σ2, stsAct_kheap, Ne.symm htn, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hq2 : ∀ y ∈ ntfnQueueOf x, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σ2 y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σ2.kheap y = some (.tcb z) := by simp [σ2, stsAct_kheap, hyt, hz]
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have heq : receiveSignal (Z := Unit) t (.notificationCap n cb rt) true σ =
      ({((), updK σ2 n (.notification y))}, False) := by
    rw [receiveSignal_notActive hk hna]
    unfold receiveSignalBlocked
    simp only [↓reduceIte]
    rw [nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one (tcbNtfnAppend_eq hk2 hkt2 (Sched.prioOf σ2) hq2)]
    exact Ipc.maybeReturnSc_noop (xn := y) (xt := x1)
      (by show (updK σ2 n (.notification y)).kheap n = _; rw [updK_kheap, Function.update_self])
      (by simp [updK, htn, hkt2]) hnr
  rw [heq] at he
  have e1 := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj he).1)
  simp only at e1
  subst e1
  show (stsAct _ t).schedulerAction = _
  unfold stsAct
  rw [if_neg (fun h => hsw h.2.1)]
  rfl

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The relation a receive at a mid state ends in: `RelTopM` and `JAtZR`. -/
abbrev RJR (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RelTopM (L := L) s σ ∧ ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
/-- **The blocking notification receive at `J` under a pending switch**
(module docstring): `JAtZ.recvSigBlockJ` from `MidE` with a non-resume
action, ending in `JAtZR`. -/
theorem JAtZ.recvSigBlockJM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (hnr : x.ntfnSc ≠ some σ.curSc)
    (hcov : (∀ k, Z.th n = some k → Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits)))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hC : CurInv σ := J.curInv hni.ncn
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hnr' : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none) := fun h => hnr (h.1.trans hscc)
  have hnb3 : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by
    rcases runnable_code hr with h | h | h <;> rw [h] <;> decide
  have hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m := fun m h => by rw [h] at hr; cases hr
  have hqE : ∀ e ∈ Z.E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue :=
    fun e he z hz => Endp.not_queued hI.1.toE ht hkt hnb3 e he z hz
  have hnqN : t.bv ∉ Fl4Spec.ntfnQueueOf x := not_member hI.1.toN ht hkt hnn n hn x hk
  have hq : ∀ y ∈ Fl4Spec.ntfnQueueOf x, ∃ z, σ.kheap y = some (.tcb z) := fun y hy => by
    obtain ⟨z, hz, -⟩ := (J.sv.ntfnQ _ _ hk).2 y hy
    exact ⟨z, hz⟩
  obtain ⟨σ', heq, F, hik, -, hcn, hsrt⟩ := recvSigBlock_eq hkt hk hna hnqN hq hr (J.isorted.2 _ _ hk) hnr' cb rt
  have hact' : σ'.schedulerAction = σ.schedulerAction :=
    recvSigBlock_act hkt hk hna hnqN hq hnr' cb rt heq hsw
  -- P1's `BlkOK` after
  have hcb := J.canBlockCurM ht hcur hkt hr hti (by rw [← hcur]; exact hC.notRel) (hni.sa (x := xt) hcur) hnq
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have hx := hI.1.toN.at_ntfn hn hk
  have hst0 : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := Z.T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := Z.T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  have h3 : L.epState s n ≠ 3#u64 := by
    rw [epState_eq]
    rcases hst0 with h | h
    · rw [h, ntfn_consts.1]; decide
    · rw [h, ntfn_consts.2.1]; decide
  have p1 := P1.notification.receive_signal.ipc hAT s a t n true Q0 R0 h0 hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) h3
  refine WP.spec_mono (WP.spec_and (receive_signal_blockF (ar := arI) J.ip s a σ hI ht hkt hnn hqE hn hk hna
    (J.qsortedN n hn) hnr' cb rt) p1) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, σ0, h0eq, hIR, hRB⟩, hbk⟩
  simp only [WP.uncurry'_pair] at ea hbk hIR hRB
  subst a'
  obtain rfl : σ' = σ0 := by
    have e1 := (Prod.mk.inj (h0eq.symm.trans heq)).1
    exact (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 e1)).symm
  have hblk := hbk
  have hW : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hRB.mono fun b hb => RBW.cnW hS hb
  have hDbg := J.rbw_dbg hRB
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
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
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
    · rcases hni.2.2 with e | ⟨u0, e, hu0⟩
      · exact absurd e hsw
      · rw [hu] at e; cases e; rw [← hcur]; exact hu0
  have hcur3 : CurInvR σ' := fun h => absurd (hact'.symm.trans h) hsw
  have hrun3 : CurRunM σ' := Or.inl (by rw [hact']; exact hsw)
  -- the dead: the thread is not dead (runnable); the notification leaves the dead set
  have htD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rcases runnable_code hr with h | h | h <;> rw [h] <;> decide)
  have hdead : ∀ q ∈ D \ {n}, DeadP (L := L) H s' q := fun q hq => by
    have hd := J.jcov.dead q hq.1
    have hqt : q.bv ≠ t.bv := htD q hq.1
    have hqn : q.bv ≠ n.bv := fun h => hq.2 (P1.eq_of_bv h)
    refine J.deadP_keep hS3 hIR.1 (fun x hx h0 => ?_) (fun x hx => F.epF hx) (fun x hx => ?_)
      (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
      (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hW hz hqC hK8 hK) F.sk.idle hAI3.1 (J.yld.frame k2 F.ykeep) (F.ykeep.dk q.bv) hd
    · obtain ⟨st', hk3, hs'⟩ := F.tcbF hx
      refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
      show st' = x.tcbState
      rcases hs' with e1 | ⟨e1, -⟩
      · exact e1
      · exact absurd e1 hqt
    · obtain ⟨y, hy, hc'⟩ := F.ntfnF hx
      rcases hc' with rfl | ⟨e1, -⟩
      · exact ⟨_, hy, Or.inl rfl, rfl, Or.inl rfl⟩
      · exact absurd e1 hqn
  have hidl := J.idleW_keep hS3 F.sk.idle F.sk.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hW) hidl.2⟩
  have hkern := J.kern_keep hks hW.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D \ {n})
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjcov : JCovD (L := L) Z.th H Z.G (D \ {n}) Cs s' := by
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
    exact (J.jcov.undead hcov.1 hcov.2).same (fun y hy _ _ => ⟨hy, hF.1.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
      (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩) hidl hks
      (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hF.1.capV (hsl x hx)]; exact hc⟩)
  -- `Inv` (`InvBut.ik`; the thread's `RelIfBound` from a runnable state)
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, by rw [← hcur]; exact hC.notRel⟩
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
  have R : JRestR (L := L) arI (Z.mv Z.G V') H Cs Ac Lst (D \ {n}) s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, hjcov, hkern,
      J.cnW_utc hW hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa hscA, F.isorted J.isorted hsrt, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hCs : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have J3 := J.toR.cs_frameI hks hX3 hW (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hCs R
    (J.rbw_dbgKeep hRB) F.sk.orig (XTopAt.idleW_eqS J.xtop hX3 F.sk.idle) (J.zD_diffN hn)
  rw [heq]
  exact ⟨_, Set.mem_singleton _, J3.xtop.relTop, _, _, _, _, _, _, J3⟩


set_option maxHeartbeats 4000000 in
/-- **The blocking notification receive at a switch mid state** (module
docstring): every case but the SC return (`hret`: a non-active notification
whose SC is the current SC). -/
theorem jRecvSigHypM_of (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidE σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p : U64) (b : U64) (w rd : Bool) (ac : Fl4Spec.Cap) (hcr : CapRel (.Notification p b w rd) ac)
    (hex : ∃ x, σ.kheap p.bv = some (.notification x)) (hHd : JHeld (L := L) Z.th s (.Notification p b w rd))
    (hret : ¬ ∃ x, σ.kheap p.bv = some (.notification x) ∧ (∀ b', x.ntfnObj ≠ .activeNtfn b') ∧
      x.ntfnSc = some σ.curSc) :
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨x, hk⟩ := hex
  obtain ⟨y, hy, hcv⟩ := hHd
  have hac : ac = absCap (.Notification p b w rd) := hcr.abs
  subst hac
  obtain ⟨n, hn, h⟩ := J.obj.ntfn _ x hk
  rw [Sched.bv_inj h] at hn
  cases hact : x.ntfnObj with
  | activeNtfn b0 =>
    exact WP.spec_mono (J.recvSigActiveJM hAT ht hcur hni hnq hn hk hact true b.bv (rightsOf w rd false false))
      fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  | _ =>
    have hna : ∀ b', x.ntfnObj ≠ .activeNtfn b' := fun b' h => by rw [hact] at h; cases h
    have hHn : H p = some .ntfn := J.zH.2.2.2 p hn
    have hfit := J.kern.heap.fits p _ hHn
    simp only [P1.HKind.bits] at hfit
    have hcov := J.cover_cap (P1.WritesIn.refl s _) hy (by rw [capAt_capV, hcv]) (fun h => by cases h)
      (ok_inj (phys_eq _).symm) rfl (range_ntfn p b w rd hfit) fun k hk' => by
        rw [hHn] at hk'; cases hk'
        exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
    have hsc : x.ntfnSc ≠ some σ.curSc := fun e => hret ⟨x, hk, hna, e⟩
    exact J.recvSigBlockJM hAT ht hcur hni hsw hnq hn hk hna hsc hcov b.bv (rightsOf w rd false false)

end

end

end Fl4Proofs.P3
