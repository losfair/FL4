/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch23b (c2)): **the
notification receive at a `chooseNewThread` mid state where ct has no SC**
(`MidN`, XTopJointMidN), every case but the SC donation (`SigDon`).

* `JAtZ.recvSigBlockJN` (scripted, sch23bgen/gens.py, from XTopJointRecvSigC's
  `recvSigBlockJC`): ct blocks; the SC-return condition (the notification's
  SC is ct's SC, not `none`) is false for an SC-less ct, so no
  `maybe_return_sched_context` case arises; ct out of the release queue by
  `Sched.Inv.notRel_of_noSc`, `BlockedScActive` vacuous for ct.
* `JAtZ.recvSigActiveJN` (hand-adapted from `recvSigActiveJC`): an active
  notification whose SC is `none` or bound to a thread: FL4's
  `maybe_donate_sched_context` and the spec's `maybeDonateSc` do nothing
  (ScDonate's `maybe_donate_nodonate`, from `NoDon` at the words:
  `NoDon.wordsR`), then ct's SC word is `0`: FL4 `sc_sporadic(0)` is false
  (`receive_signal_active_eqN`), the spec's `ifSporadicCurScTestRefillUnblockCheck none`
  is nothing (`specRecvTail_noSc`).
* `SigDon σ p`: `p` an active notification whose SC is bound to no thread:
  the receiving SC-less ct is given that SC (`maybeDonateSc`:
  `schedContextDonate` + `schedContextResume`). Not proved here.
* `jRecvSigHypN_of`: every `receive_signal` at a `MidN` state outside `SigDon`.
-/
import Fl4Proofs.P3.XTopJointMidN
import Fl4Proofs.P3.XTopJointRecvSigC
import Fl4Proofs.P3.IpcSignalWake
import Fl4Proofs.P3.ScDonate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The notification receive donates an SC** (module docstring): `p` is an
active notification whose SC is bound to no thread. -/
def SigDon (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) : Prop :=
  ∃ x, σ.kheap p = some (.notification x) ∧ (∃ b, x.ntfnObj = .activeNtfn b) ∧
    ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb = none

/-- The spec's tail of `receive_signal` (active) for a thread with no SC when
`maybeDonateSc` does nothing: nothing. -/
theorem specRecvTail_noSc {σ : Fl4Spec.State Unit} {t n : Fl4Spec.ObjRef} {xt : Fl4Spec.Tcb}
    (hkt : σ.kheap t = some (.tcb xt)) (hsc : xt.tcbSchedContext = none)
    (hnd : Fl4Spec.maybeDonateSc (Z := Unit) t n σ = ({((), σ)}, False)) :
    specRecvTail t n σ = ({((), σ)}, False) := by
  unfold specRecvTail
  rw [nd_bind_one hnd]
  unfold Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hkt), hsc]
  exact ifSporadic_none _

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `NoDon` at FL4's words from the notification and scheduler relations
(IpcSignalWake's `NoDon.words` without the whole `IRel`). -/
theorem NoDon.wordsR {s : S} {σ : Fl4Spec.State Unit} {N T C : Set U64} {c : U64}
    (hN : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) {t n : U64}
    (ht : t ∈ T) (hn : n ∈ N) (h : NoDon C σ t.bv n.bv) :
    L.mem s (scA t) ≠ 0#u64 ∨ L.mem s (nScA n) = 0#u64 ∨
      (L.mem s (nScA n) ∈ C ∧ L.mem s (scW (L.mem s (nScA n)) 24#u64) ≠ 0#u64) := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  obtain ⟨xn, hkn, hxn⟩ := hN.ntfn n hn
  rcases h xt xn hkt hkn with h1 | h2 | ⟨cq, hcq, h3, y, k, hky, hyt⟩
  · left; intro e; rw [hsct, e, Notif.optRef_zero] at h1; exact h1 rfl
  · right; left
    by_contra e
    rw [hxn.sc, Notif.optRef_ne e] at h2; cases h2
  · right; right
    rw [hxn.sc] at h3
    obtain ⟨-, e⟩ := Notif.optRef_some h3
    have e' : L.mem s (nScA n) = cq := P1.eq_of_bv e
    rw [e']
    refine ⟨hcq, fun e0 => hyt ?_⟩
    obtain ⟨y', k', hky', hy'⟩ := hs.scs cq hcq
    rw [hky] at hky'; cases hky'
    rw [hy'.tcb, e0, Notif.optRef_zero]

/-- FL4's `receive_signal` on an active notification for a thread with no SC
when `maybe_donate_sched_context` does nothing: the two writes
(`sc_sporadic` of the null SC is false). -/
theorem receive_signal_active_eqN {s : S} {a : A} {t n : U64} (blk : Bool)
    (hst : stOf (L.mem s) n = obj.NTFN_ACTIVE)
    (h0 : L.mem (recvActS st s t n) (P1.scA t) = 0#u64)
    (hnd : notification.maybe_donate_sched_context st arI (recvActS st s t n) a t n = ok (recvActS st s t n, a)) :
    notification.receive_signal st arI s a t n blk ⦃ r => r = (recvActS st s t n, a) ⦄ := by
  unfold recvActS at h0 hnd ⊢
  rw [regIdx_badge] at h0 hnd ⊢
  unfold notification.receive_signal
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq, hst, if_neg (by rw [ntfn_consts.1, ntfn_consts.2.2]; decide),
    if_neg (by rw [ntfn_consts.2.1, ntfn_consts.2.2]; decide)]
  refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
  rintro b rfl
  refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Ntfn.set_state.spec _ n obj.NTFN_IDLE) ?_
  rintro s2 rfl
  rw [hnd, bind_ok]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec _ t) ?_
  rintro i rfl
  refine WP.spec_bind (Sched.sched.cur_sc.spec' _) ?_
  rintro c rfl
  rw [Sched.sc_ne_eq, bind_ok, h0]
  have hsp : ∀ s' : S, sporadic.sc_sporadic st s' (0#u64 : U64) = ok false := fun s' => by
    unfold sporadic.sc_sporadic obj.Sc.is_null; simp
  split
  · rw [hsp, bind_ok]; simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  · simp only [WP.spec_ok]

set_option maxHeartbeats 16000000 in
/-- **Receiving from an active notification at a `MidN` state without a
donation** (module docstring). -/
theorem JAtZ.recvSigActiveJN (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (hnd : x.ntfnSc = none ∨ ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb ≠ none)
    (blk : Bool) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n blk ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  have hsc0 : xt.tcbSchedContext = none := hni.2.2.2 xt (by rw [hcur]; exact hkt)
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurMN ht hcur hkt hrn hni.1 (J.inv.notRel_of_noSc hkt hsc0) hni hnq
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
  have h0 : L.mem (recvActS st s t n) (P1.scA t) = 0#u64 := optRef_none (hsct2.symm.trans hsc0)
  -- no donation, at the spec and at FL4's words
  have hND : NoDon Z.C (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) t.bv n.bv := by
    intro xt' xn' _ hxn'
    have hk2n : (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap n.bv =
        some (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x)) := by simp [updK]
    rw [hk2n] at hxn'; cases hxn'
    right
    rcases hnd with h | ⟨q, y, k, hq, hky, hyt⟩
    · left; exact h
    · right
      obtain ⟨cq, hcq, rfl⟩ := J.obj.sc q y k hky
      have hqt : cq.bv ≠ t.bv := fun e => by rw [e, hkt] at hky; cases hky
      have hqn : cq.bv ≠ n.bv := fun e => by rw [e, hk] at hky; cases hky
      exact ⟨cq, hcq, hq, y, k, by simp [updK, hqt, hqn, hky], hyt⟩
  obtain ⟨rd, hrd, hrd1, hsd⟩ := spec_exists (maybe_donate_nodonate (ar := arI) (recvActS st s t n) a _ hR2.toN
    hSch2 t n ht hn (NoDon.wordsR hR2.toN hSch2 ht hn hND))
  subst hrd1
  have heq := spec_eq_ok (receive_signal_active_eqN (arI := arI) (a := a) blk hst h0 hrd)
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
  -- the spec's outcome
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) blk σ =
      specRecvTail t.bv n.bv (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
        (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))) := by
    rw [receiveSignal_cap hk]
    simp only [hact]
    rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1)]
  rw [hspec, specRecvTail_noSc hkt2' hsc0 hsd, heq, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩

set_option maxHeartbeats 16000000 in
/-- **The blocking notification receive at `J` under a pending reschedule (ct SC-less)**
(module docstring): `JAtZ.recvSigBlockJ` from `MidE` with a non-resume
action, ending in `JAtZR`. -/
theorem JAtZ.recvSigBlockJN (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b)
    (hcov : (∀ k, Z.th n = some k → Covered (L.mem s) Z.G n.val (n.val + max (objSize k) 1)) ∧
      (∀ k, H n = some k → Covered (L.mem s) Z.G n.val (n.val + 2 ^ k.bits)))
    (cb : Fl4Spec.Badge) (rt : Fl4Spec.CapRights) :
    notification.receive_signal st arI s a t n true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb rt) true σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  obtain ⟨xt, hkt, -⟩ := hI.1.tcb t ht
  have hsc0 : xt.tcbSchedContext = none := hni.2.2.2 xt (by rw [hcur]; exact hkt)
  have hr : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hnr' : ¬ (x.ntfnSc = xt.tcbSchedContext ∧ x.ntfnSc ≠ none) := fun h => h.2 (h.1.trans hsc0)
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
  have hcb := J.canBlockCurMN ht hcur hkt hr hti (J.inv.notRel_of_noSc hkt hsc0) hni hnq
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
    · rw [hni.2.2.1] at hu; cases hu
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
  have hnqT : NotQueued σ t.bv := ⟨by rw [← hcur]; exact hnq, J.inv.notRel_of_noSc hkt hsc0⟩
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
    rw [hsc0] at hxs; cases hxs
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
/-- **The notification receive at a `MidN` state outside `SigDon`** (module
docstring). -/
theorem jRecvSigHypN_of (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {ct : U64} (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p : U64) (b : U64) (w rd : Bool) (ac : Fl4Spec.Cap) (hcr : CapRel (.Notification p b w rd) ac)
    (hex : ∃ x, σ.kheap p.bv = some (.notification x)) (hHd : JHeld (L := L) Z.th s (.Notification p b w rd))
    (hdon : ¬ SigDon σ p.bv) :
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
    have hnd : x.ntfnSc = none ∨
        ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb ≠ none := by
      cases hq : x.ntfnSc with
      | none => exact Or.inl rfl
      | some q =>
        obtain ⟨y0, m0, hky, -⟩ := J.ntfn_link hn x q hk hq
        exact Or.inr ⟨q, y0, m0, rfl, hky, fun h0 => hdon ⟨x, hk, ⟨b0, hact⟩, q, y0, m0, hq, hky, h0⟩⟩
    exact WP.spec_mono (J.recvSigActiveJN hAT ht hcur hni hnq hn hk hact hnd true b.bv (rightsOf w rd false false))
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
    exact J.recvSigBlockJN hAT ht hcur hni hsw hnq hn hk hna hcov b.bv (rightsOf w rd false false)

end

end

end Fl4Proofs.P3
