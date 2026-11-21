/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch16, item 1): **the
blocking endpoint receive under a pending switch**, XTopJointRecvSigM's
template applied to XTopJointRecvIpcBlock / XTopJointRecvIpcBound: from a mid
state whose action is `switchThread u` (u ≠ ct; `MidE` with action ≠ resume)
the current thread blocks receiving on an idle or receiving endpoint, ending
in `JAtZR`.

* `Sched.recvIpcBlock_eqM`: `recvIpcBlock_eq` with a non-resume action kept
  (`set_thread_state_act` turns only `resumeCurThread` into
  `chooseNewThread`).
* `JAtZ.recvIpcBlockJGM`: `JAtZ.recvIpcBlockJG` from `MidE` + action ≠
  resume (no `hsa`). Changes: `CurInv` from `J.curInv hni.ncn` (runnable,
  not in the release queue, the SC active); `CanBlock` by `canBlockCurM`;
  `ActIdle` after by `ActIdle.keepE (E := {ct})`; `CurInvR` after vacuous,
  `CurRunM` by its first disjunct; `JRestR` and `J.toR.cs_frameI`.
* `JAtZ.recvIpcBlockJM` (no bound notification), `JAtZ.recvIpcBlockNJGM`
  (a bound idle or waiting notification whose SC is not the thread's).
-/
import Fl4Proofs.P3.XTopJointRecvSigM
import Fl4Proofs.P3.XTopJointRecvIpcLink
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec Classical

/-- **`recvIpcBlock_eq` with the action kept when not resumed** (module docstring), the reply
cap null or naming an unlinked reply (`Endp.SpecReplyArg`). -/
theorem recvIpcBlock_eqM {σ : State Unit} {t e : ObjRef} {xt : Tcb} {x : Endpoint}
    (hkt : σ.kheap t = some (.tcb xt))
    (hk : σ.kheap e = some (.endpoint x)) (hc : Endp.CanBlock true x)
    (htq : t ∉ x.epQueue) (hq : ∀ y ∈ x.epQueue, ∃ z, σ.kheap y = some (.tcb z)) (hr : runnable xt.tcbState = true)
    (hS : SortedQ σ x.epQueue) (b : Badge) (rights : CapRights) {rc' : Cap} {r : Option ObjRef}
    (hrc : Endp.SpecReplyArg σ rc' r)
    (hsp0 : receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ = receiveIpcBlocked true t e r σ) :
    ∃ σ', receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ = ({((), σ')}, False) ∧
      BFrR t e r σ σ' ∧ IK t σ σ' ∧ σ'.readyQueues = σ.readyQueues ∧
      (t = σ.curThread → σ.schedulerAction = .resumeCurThread → σ'.schedulerAction = .chooseNewThread) ∧
      (∀ y, σ'.kheap e = some (.endpoint y) → SortedQ σ y.epQueue) ∧
      (σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread) ∧
      (σ.schedulerAction ≠ .resumeCurThread → σ'.schedulerAction = σ.schedulerAction) := by
  let x1 : Tcb := { xt with tcbState := .blockedOnReceive e r { receiverCanGrant := false } }
  let σ2 := stsAct (updK σ t (.tcb x1)) t
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [Endp.CanBlock] at hc
  have hte : t ≠ e := by rintro rfl; rw [hkt] at hk; cases hk
  have hk2 : σ2.kheap e = some (.endpoint x) := by simp [σ2, stsAct_kheap, Ne.symm hte, hk]
  have hkt2 : σ2.kheap t = some (.tcb x1) := by simp [σ2, stsAct_kheap]
  have hk2o : ∀ p, p ≠ t → σ2.kheap p = σ.kheap p := fun p hp => by simp [σ2, stsAct_kheap, hp]
  -- the reply step
  obtain ⟨σr, hrep, hσr, hkr, hrq⟩ : ∃ σr, NonDet.maybeM (fun q => setReplyObjRef (Z := Unit) replyTcbUpdate q (some t))
      r σ2 = ({((), σr)}, False) ∧ (∃ kh, σr = { σ2 with kheap := kh }) ∧
      (∀ p, σr.kheap p = σ2.kheap p ∨ ∃ xr, r = some p ∧ σ.kheap p = some (.reply xr) ∧
        σr.kheap p = some (.reply { xr with replyTcb := some t })) ∧
      (∀ q, r = some q → ∃ xr, σ.kheap q = some (.reply xr) ∧
        σr.kheap q = some (.reply { xr with replyTcb := some t })) := by
    rcases hrc with ⟨-, rfl⟩ | ⟨q, rr, xr, -, rfl, hkr, -⟩
    · exact ⟨σ2, rfl, ⟨_, rfl⟩, fun p => Or.inl rfl, fun q h => by cases h⟩
    · have hqt : q ≠ t := by rintro rfl; rw [hkt] at hkr; cases hkr
      have hkr2 : σ2.kheap q = some (.reply xr) := by rw [hk2o q hqt]; exact hkr
      refine ⟨_, Endp.setReplyTcb_eq _ hkr2, ⟨_, rfl⟩, fun p => ?_, fun q' h => ?_⟩
      · by_cases hp : p = q
        · subst hp; exact Or.inr ⟨xr, rfl, hkr, by simp [updK]⟩
        · exact Or.inl (by simp [updK, hp])
      · cases h; exact ⟨xr, hkr, by simp [updK]⟩
  obtain ⟨kh, hσr⟩ := hσr
  have hkrT : ∀ p o, σ2.kheap p = some o → (∀ y, o ≠ .reply y) → σr.kheap p = some o := by
    intro p o hp ho
    rcases hkr p with h | ⟨xr, hr', h1, -⟩
    · rw [h, hp]
    · have hpt : p ≠ t := by rintro rfl; rw [hkt] at h1; cases h1
      rw [hk2o p hpt, h1] at hp; cases hp; exact absurd rfl (ho xr)
  have hkr2 : σr.kheap e = some (.endpoint x) := hkrT e _ hk2 fun _ h => by cases h
  have hktr : σr.kheap t = some (.tcb x1) := hkrT t _ hkt2 fun _ h => by cases h
  have hprr : ∀ u, Sched.prioOf σr u = Sched.prioOf σ2 u := by
    intro u
    unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq]
    rcases hkr u with h | ⟨xr, -, h1, h2⟩
    · rw [h]
    · have hut : u ≠ t := by rintro rfl; rw [hkt] at h1; cases h1
      rw [h2, hk2o u hut, h1]
  let q' := Notif.specIns x.epQueue (Sched.prioOf σr) x1.tcbPriority t
  let σ' := updK σr e (.endpoint (updateEpQueue x q' true))
  have hq2 : ∀ y ∈ x.epQueue, ∃ z, σr.kheap y = some (.tcb z) ∧ z.tcbPriority = Sched.prioOf σr y := by
    intro y hy
    obtain ⟨z, hz⟩ := hq y hy
    have hyt : y ≠ t := fun h => htq (h ▸ hy)
    have hz2 : σr.kheap y = some (.tcb z) := hkrT y _ (by rw [hk2o y hyt]; exact hz) fun _ h => by cases h
    exact ⟨z, hz2, (prioOf_eq hz2).symm⟩
  have hblk : receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ =
      ((setThreadState t (.blockedOnReceive e r { receiverCanGrant := false }) >>= fun _ =>
        NonDet.maybeM (fun q => setReplyObjRef (Z := Unit) replyTcbUpdate q (some t)) r >>= fun _ =>
          tcbEpAppend t e true) σ) := by
    rw [hsp0]
    unfold receiveIpcBlocked
    rw [if_pos rfl]
  have heq : receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ = ({((), σ')}, False) := by
    rw [hblk, nd_bind_one (Notif.setThreadState_eq _ hkt), nd_bind_one hrep]
    exact Endp.tcbEpAppend_eq hkr2 hktr (Sched.prioOf σr) hq2 true
  have hsk2 : Sk σ σ2 := by
    show Sk σ (stsAct _ t)
    unfold stsAct; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hskr : Sk σ2 σr := by rw [hσr]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsk : Sk σ σ' := (hsk2.trans hskr).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hkh' : ∀ p, p ≠ e → σ'.kheap p = σr.kheap p := fun p hp => by simp [σ', updK, hp]
  have hpr2 : ∀ u, Sched.prioOf σ2 u = Sched.prioOf σ u := by
    intro u
    by_cases hut : u = t
    · subst hut; exact (prioOf_eq hkt2).trans (prioOf_eq hkt).symm
    · unfold Sched.prioOf; rw [tcbsOf_eq, tcbsOf_eq, hk2o u hut]
  have hrq' : σ'.readyQueues = σ.readyQueues := by
    show σr.readyQueues = _
    rw [hσr]
    show (stsAct _ t).readyQueues = _
    unfold stsAct; split <;> rfl
  have F : BFrR t e r σ σ' := by
    refine ⟨hsk, fun p => ?_, fun q hq0 => ?_⟩
    · by_cases hpe : p = e
      · subst hpe
        exact Or.inr ⟨.endpoint x, .endpoint (updateEpQueue x q' true), hk, by simp [σ', updK],
          Or.inr (Or.inl ⟨x, _, rfl, rfl, rfl⟩)⟩
      rw [hkh' p hpe]
      rcases hkr p with h | ⟨xr, hr', h1, h2⟩
      · rw [h]
        by_cases hpt : p = t
        · subst hpt
          exact Or.inr ⟨.tcb xt, .tcb x1, hkt, hkt2, Or.inl ⟨xt, e, _, rfl, rfl, rfl, hr⟩⟩
        · exact Or.inl (hk2o p hpt)
      · exact Or.inr ⟨_, _, h1, h2, Or.inr (Or.inr ⟨xr, rfl, rfl, hr'⟩)⟩
    · obtain ⟨xr, h1, h2⟩ := hrq q hq0
      have hqe : q ≠ e := by rintro rfl; rw [hk] at h1; cases h1
      exact ⟨xr, h1, by rw [hkh' q hqe]; exact h2⟩
  refine ⟨σ', heq, F, F.ik hrq', hrq', fun hct hres => ?_, fun y hy => ?_, fun hcn0 => ?_, fun hsw => ?_⟩
  · have hns' : ¬ schedulable t (updK σ t (.tcb x1)) = true := by
      intro hs
      obtain ⟨y, -, -, -, hy, -, hrun, -⟩ := schedulable_inv hs
      rw [updK_kheap, Function.update_self] at hy
      cases hy
      simp [x1, runnable] at hrun
    show σr.schedulerAction = _
    rw [hσr]
    show (stsAct _ t).schedulerAction = _
    unfold stsAct
    rw [if_pos ⟨hct, hres, hns'⟩]
  · have : σ'.kheap e = some (.endpoint (updateEpQueue x q' true)) := by simp [σ', updK]
    rw [this] at hy
    cases hy
    rw [epQueue_update]
    have hpr : ∀ u, Sched.prioOf σr u = Sched.prioOf σ u := fun u => (hprr u).trans (hpr2 u)
    exact (sortedQ_specIns (hS.congr fun u _ => hpr u) t (prioOf_eq hktr)).congr fun u _ => (hpr u).symm
  · show σr.schedulerAction = _
    rw [hσr]
    show (stsAct _ t).schedulerAction = _
    unfold stsAct
    split
    · rfl
    · exact hcn0
  · show σr.schedulerAction = _
    rw [hσr]
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
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 16000000 in
set_option maxHeartbeats 16000000 in
/-- **The blocking receive at `J` under a pending switch** (`MidE`, action not
resumed; `JAtZ.recvIpcBlockJG`'s changes as XTopJointRecvSigM's
`recvSigBlockJM`), ending in `JAtZR`: the current thread
`t` blocks receiving on the idle or receiving endpoint `e`, covered by a cap
(`hcov`), with a null reply cap or one naming a reply object linked to no
thread, covered by the cap (`hcovR`); `hred`, `hsp`: FL4's and the spec's
`receive_ipc` reduce to the wait (no bound notification: `receive_ipc_block_red`,
`receiveIpc_noSend`; a bound idle or waiting one: XTopJointRecvIpcBound), stated
for any FL4 program `m` reducing to the wait. -/
theorem JAtZ.recvIpcBlockJGM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hti hnrl (hni.sa (x := xt) hcur) hnq
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
    · rcases hni.2.2 with e | ⟨u0, e, hu0⟩
      · exact absurd e hsw
      · rw [hu] at e; cases e; rw [← hcur]; exact hu0
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

/-- **The blocking receive at `J` under a pending switch**, no bound
notification: `JAtZ.recvIpcBlockJGM`. -/
theorem JAtZ.recvIpcBlockJM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  J.recvIpcBlockJGM ht hcur hni hsw hnq hkt he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights hred hsp

set_option maxHeartbeats 4000000 in
/-- **The blocking receive with a bound idle or waiting notification at `J`**
(module docstring): the notification's SC is not the thread's (`hnr`); at a
mid state with a pending switch (`MidE`, as `JAtZ.recvIpcBlockJGM`). -/
theorem JAtZ.recvIpcBlockNJGM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  exact J.recvIpcBlockJGM ht hcur hni hsw hnq hkt he hk hc hcov hrc hcovR cb c1 c2 c3 c4 b rights
    (fun h => receive_ipc_blockN_red hrc hbound (by rw [← hbound]; exact hbz) hstN hwn hst2 h)
    (receiveIpc_boundNA b rights true (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna (fun _ => hnr))

end

end

end Fl4Proofs.P3
