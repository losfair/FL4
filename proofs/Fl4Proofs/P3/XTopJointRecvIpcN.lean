/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch23b (c2)): **the
endpoint receive at a `chooseNewThread` mid state where ct has no SC**
(`MidN`, XTopJointMidN), with a null or free reply, every case but the two
SC donations to ct.

* `JAtZ.recvIpcActJN` (sch23bgen, from XTopJointRecvIpcAct's `recvIpcActJ`):
  an active bound notification whose SC is `none` or bound to a thread:
  `complete_signal`'s `maybe_donate_sched_context` / `maybeDonateSc` do
  nothing (`maybe_donate_nodonate`, XTopJointRecvSigN's `NoDon.wordsR`),
  ct's SC word `0`: FL4 `sc_sporadic(0)` false (`complete_signal_eqN`), the
  spec's `maybeM` over `none` nothing (`completeSignal_noSc`).
* The blocking receives (no bound notification, a bound idle / waiting one)
  are the resumed `recvIpcBlockJG` / `recvIpcBlockNJG` with their `hsa`
  second disjunct (a reschedule pending, ct SC-less); the non-pushing head
  sender `recvSendJ0X` (generic); the reply-pushing sender WITHOUT an SC
  XTopJointRecvSendPC's `recvSendPJGC` / `recvSendFPJGC` (`hAct`'s
  `xs.tcbSchedContext = none` disjunct: no donation); the timeout-fault sender
  with an SC the resumed `recvSendFPTJ` / `recvSendFTJ` (`hAct`:
  `chooseNewThread` with ct out of the release queue); the SC-return
  (`LendM`) cases are vacuous: the notification's SC would be ct's, `none`.
* `IpcActDon σ`: ct's bound notification active with an SC bound to no thread
  (ct is given that SC); `IpcPushDon σ p rc`: the head sender pushes a reply
  and has an SC (`PushOK`; the passive receiver is given the caller's SC).
  Not proved here.
* `jRecvIpcUN`: every `receive_ipc` at a `MidN` state with a null or free reply
  outside `IpcActDon` and `IpcPushDon`.
-/
import Fl4Proofs.P3.XTopJointRecvSigN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **ct's bound notification donates an SC to ct** (module docstring). -/
def IpcActDon (σ : Fl4Spec.State Unit) : Prop :=
  ∃ xt n x, σ.kheap σ.curThread = some (.tcb xt) ∧ xt.tcbBoundNotification = some n ∧
    σ.kheap n = some (.notification x) ∧ (∃ b, x.ntfnObj = .activeNtfn b) ∧
    ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb = none

/-- **The head sender pushes a reply and donates its SC** (module docstring). -/
def IpcPushDon (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (rc : capability.Cap) : Prop :=
  ∃ sd q xs, σ.kheap p = some (.endpoint (.sendEP (sd :: q))) ∧ σ.kheap sd = some (.tcb xs) ∧
    xs.tcbSchedContext ≠ none ∧ PushOK xs rc

section Spec
open Fl4Spec

/-- **The spec's `complete_signal` for a thread with no SC, no donation**: the
badge register, the notification idle. -/
theorem completeSignal_noSc {σ : State Unit} {t n : ObjRef} {xt : Tcb} {x : Notification} {b0 : Badge}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification x))
    (hact : x.ntfnObj = .activeNtfn b0) (hsc : xt.tcbSchedContext = none) (hnt : n ≠ t)
    (hnd : maybeDonateSc (Z := Unit) t n (updK (updK σ t (.tcb (setReg xt badge_register b0))) n
      (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x))) =
      ({((), updK (updK σ t (.tcb (setReg xt badge_register b0))) n
        (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x)))}, False)) :
    completeSignal (Z := Unit) n t σ = ({((), updK (updK σ t (.tcb (setReg xt badge_register b0))) n
      (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x)))}, False) := by
  have hk1 : (updK σ t (.tcb (setReg xt badge_register b0))).kheap n = some (.notification x) := by
    simp [updK, hnt, hkn]
  have hkt2 : (updK (updK σ t (.tcb (setReg xt badge_register b0))) n
      (.notification (ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t =
      some (.tcb (setReg xt badge_register b0)) := by simp [updK, Ne.symm hnt]
  have hsc2 : (setReg xt badge_register b0).tcbSchedContext = none := hsc
  unfold completeSignal
  rw [nd_bind_one (getNotification_eq hkn)]
  simp only [hact]
  rw [nd_bind_one (asUser_setRegister_eq _ _ hkt), nd_bind_one (setNotification_eq _ hk1), nd_bind_one hnd]
  unfold getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hkt2), hsc2]
  rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- FL4's `complete_signal` on an active notification for a thread with no SC
when `maybe_donate_sched_context` does nothing: the two writes of `recvActS`. -/
theorem complete_signal_eqN {s : S} {a : A} {t n : U64} (ht0 : t ≠ 0#u64)
    (hst : stOf (L.mem s) n = obj.NTFN_ACTIVE)
    (h0 : L.mem (recvActS st s t n) (P1.scA t) = 0#u64)
    (hnd : notification.maybe_donate_sched_context st arI (recvActS st s t n) a t n = ok (recvActS st s t n, a)) :
    notification.complete_signal st arI s a n t ⦃ r => r = (recvActS st s t n, a) ⦄ := by
  unfold recvActS at h0 hnd ⊢
  rw [regIdx_badge] at h0 hnd ⊢
  unfold notification.complete_signal
  step with P1.obj.Tcb.is_null.spec as ⟨b, hb⟩
  simp only [hb, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (P1.obj.Ntfn.state.spec s n) ?_
  rintro v rfl
  rw [epState_eq, hst]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (obj.Ntfn.badge.spec s n) ?_
  rintro b rfl
  refine WP.spec_bind (obj.Tcb.set_reg.spec s t layout.reg.BADGE _) ?_
  rintro s1 rfl
  refine WP.spec_bind (obj.Ntfn.set_state.spec _ n obj.NTFN_IDLE) ?_
  rintro s2 rfl
  rw [hnd, bind_ok]
  refine WP.spec_bind (P1.obj.Tcb.sc.spec _ t) ?_
  rintro i rfl
  rw [h0]
  have hsp : ∀ s' : S, sporadic.sc_sporadic st s' (0#u64 : U64) = ok false := fun s' => by
    unfold sporadic.sc_sporadic obj.Sc.is_null; simp
  rw [hsp, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]

set_option maxHeartbeats 16000000 in
/-- **`receive_ipc` with an active bound notification at a `MidN` state
without a donation** (module docstring). -/
theorem JAtZ.recvIpcActJN (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt0 : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hbn : xt.tcbBoundNotification = some n.bv) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (hnd : x.ntfnSc = none ∨ ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb ≠ none)
    (blk : Bool) {e : U64} {xe : Fl4Spec.Endpoint} (hke : σ.kheap e.bv = some (.endpoint xe))
    (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hkt := hkt0
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
  -- the spec's outcome and FL4's
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have ht0 : t ≠ 0#u64 := fun e => by
    obtain ⟨Q1, R1, hc1, -⟩ := J.xtop.fin.1.1.1.lists
    exact (hc1.tcbs t ht).ne0 (by rw [e]; rfl)
  have heqI := spec_eq_ok (receive_ipc_preA (ar := arI) s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
    (by rw [← hbound]; exact hbz) hst (complete_signal_eqN (arI := arI) (a := a) ht0 hst h0 hrd))
  have hspecI := receiveIpc_active b rights blk (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hke hk hact
  rw [hspecI, completeSignal_noSc hkt hk hact hsc0 hnt hsd, heqI, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` with a null or free reply at a `MidN` state outside the
two donations** (module docstring). -/
theorem jRecvIpcUN (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64)
    (hAD : ¬ IpcActDon σ) (hPD : ¬ IpcPushDon σ p.bv rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hD := ipcDoneM3_of J ht hpE hun
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  have hI := J.xtop.irelK J.ks J.buf
  have hS0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → x.tcbSchedContext = none := fun x hx =>
    hni.2.2.2 x (by rw [hcur]; exact hx)
  have hR0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → ct.bv ∉ σ.releaseQueue := fun x hx =>
    J.inv.notRel_of_noSc hx (hS0 x hx)
  have hU0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := fun x hx =>
    hni.run x (by rw [hcur]; exact hx)
  have hnl : ¬ LendM ct σ := fun hL => by
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨n, xn, -, -, -, h1, h2⟩ := hL xt hkt
    exact h2 (h1.trans (hS0 xt hkt))
  suffices hRJ : endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ from
    WP.spec_mono hRJ fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  rcases hD with ((hca | hcb | ⟨hcn, hnr0⟩ | ⟨hun', hcs, hnr0⟩) | ⟨hun', hcp | hcT⟩) | hR
  · obtain ⟨⟨xt, n0, x, b0, hkt, hbn, hkn, hact⟩, hrr⟩ := hca
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hnd : x.ntfnSc = none ∨
        ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb ≠ none := by
      cases hq : x.ntfnSc with
      | none => exact Or.inl rfl
      | some q =>
        obtain ⟨y0, m0, hky, -⟩ := J.ntfn_link hn x q hkn hq
        exact Or.inr ⟨q, y0, m0, rfl, hky, fun h0 =>
          hAD ⟨xt, n.bv, x, by rw [hcur]; exact hkt, hbn, hkn, ⟨b0, hact⟩, q, y0, m0, hq, hky, h0⟩⟩
    exact J.recvIpcActJN hAT ht hcur hni hnq hkt hn hkn hbn hact hnd true hke b sd true g gr hra b.bv
      (rightsOf sd true g gr)
  · obtain ⟨-, hbn, hns, hrr⟩ := hcb
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
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
    exact J.recvIpcBlockJG ht hcur hni.1 hnq (hR0 xt hkt) hkt (hU0 xt hkt) (Or.inr ⟨hni.2.2.1, hS0 xt hkt⟩)
      he hke hcB hcov hra hcovR b sd true g gr b.bv (rightsOf sd true g gr)
      (fun h => receive_ipc_block_red hra hbound hst2 h)
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
    exact J.recvIpcBlockNJG ht hcur hni.1 hnq (hR0 xt hkt) hkt (hU0 xt hkt) (Or.inr ⟨hni.2.2.1, hS0 xt hkt⟩)
      hn hbn hkn hna (hnr0 xt _ xn hkt hbn hkn) he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
        (true = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) := by
      rcases hbn xt hkt with hb0 | ⟨n0, xn, hbn0, hkn, hna⟩
      · exact Or.inl hb0
      · exact Or.inr ⟨n0, xn, hbn0, hkn, hna, fun _ => hnr0 xt n0 xn hkt hbn0 hkn⟩
    exact J.recvSendJ0X ht hkt (hU0 xt hkt) hbN hcur he hke' hks b sd true g gr hra hok b.bv
      (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcp
    by_cases hxs : xs.tcbSchedContext = none
    swap
    · exact absurd ⟨sd0, q, xs, hke', hks, hxs, hok⟩ hPD
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hrv0 : rv ≠ 0#u64 := by
      rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hok.1
      · exact (J.rp.align rv hr).2.1
    obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
    have hbN := hbn xt hkt
    have hA : σ.schedulerAction = .resumeCurThread ∨ (σ.schedulerAction = .chooseNewThread ∧
        ct.bv ∉ σ.releaseQueue ∧ (xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none)) :=
      Or.inr ⟨hni.2.2.1, hR0 xt hkt, Or.inl hxs⟩
    obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
    · exact J.recvSendPJGC hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hfs hA
        b sd true g gr hra (hcovR hrv0) hcl hyes hrn b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
    · exact J.recvSendFPJGC hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hft hto hA
        b sd true g gr hra (hcovR hrv0) hyes hrn b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcT
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hbN := hbn xt hkt
    have hcovR := (J.recvCov_of he hHd hHr hra).2
    obtain ⟨⟨bb, hft⟩, hsn⟩ := hok
    by_cases hp : rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
        dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
    · have hrv0 : rv ≠ 0#u64 := by
        rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
        · exact absurd h1 hp.1
        · exact (J.rp.align rv hr).2.1
      exact J.recvSendFPTJ hAT hmax htu ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hft hsn
        (Or.inr ⟨hni.2.2.1, hR0 xt hkt⟩) b sd true g gr hra (hcovR hrv0) hp.2 hp.1 b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
    · exact J.recvSendFTJ hAT hmax htu ht hkt (hU0 xt hkt) hbN hcur he hke' hks hft hsn b sd true g gr hra
        (noPush_of hp) b.bv (rightsOf sd true g gr) (J.recvPreN ht hkt hbN p b sd true g gr hra)
  · exfalso
    rcases hR with ⟨-, hL⟩ | ⟨-, ⟨-, hL⟩ | ⟨-, hL, -⟩ | ⟨hL, -⟩⟩
    · exact hnl hL
    · exact hnl hL
    · exact hnl hL
    · exact hnl hL

end

end

end Fl4Proofs.P3
