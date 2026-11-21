/-
P3 (DESIGN.md §9), IPC: **a blocking `receive_ipc` from a waiting sender
whose bound notification lends the receiver its SC, at `J`**
(XTopJointRecvIpcLink's `JRecvSendHyp`, KENTRY-PLAN.md item 6 (d5); l4v
`receive_ipc`'s `maybe_return_sc` for a passive server, then the `send_ep`
branch).

* `receiveIpc_lend_eq` (spec): the blocking receive with a bound
  notification lending the thread its SC (not active) is the same receive at
  the state after `maybe_return_sc`, where the notification's SC is not the
  thread's any more (`maybe_return_sc` a no-op there).
* `JAtZ.recvSendRetJ`: XTopJointRecvSigRet's `JAtZ.maybeReturnJQ` (the
  running current thread, in no queue) to a `JAtZ` after it, as
  XTopJointRecvIpcRet's `JAtZ.recvIpcRetJ`; then XTopJointRecvSend's
  `JAtZ.recvSendJX` (XTopJointRecvSendF) there for FL4's `recvTail` (the endpoint-state switch
  after `maybe_return_sched_context`, XTopJointRecvIpcRet's
  `receive_ipc_blockR_red`), the receiver's bound notification not lending.
-/
import Fl4Proofs.P3.XTopJointRecvSendF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section SpecC
open Fl4Spec

/-- **The spec's blocking receive with a bound notification lending the
thread its SC** (not active), any endpoint: the same receive at the state
`σ2` after `maybe_return_sc` (`hm`), where the notification's SC is not the
thread's (`hnr2`). -/
theorem receiveIpc_lend_eq {σ σ2 : State Unit} {t e n : ObjRef} (b : Badge) (rights : CapRights)
    {rc' : Cap} {reply : Option ObjRef} (hrc : SpecReplyArg σ rc' reply) (hrc2 : SpecReplyArg σ2 rc' reply)
    {xt xt2 : Tcb} (hkt : σ.kheap t = some (.tcb xt)) (hkt2 : σ2.kheap t = some (.tcb xt2))
    (hb : xt.tcbBoundNotification = some n) (hb2 : xt2.tcbBoundNotification = some n) {x : Endpoint}
    (hk : σ.kheap e = some (.endpoint x)) (hk2 : σ2.kheap e = some (.endpoint x)) {xn : Notification}
    (hkn : σ.kheap n = some (.notification xn)) (hkn2 : σ2.kheap n = some (.notification xn))
    (hna : isActive xn = false) (hm : maybeReturnSc (Z := Unit) n t σ = ({((), σ2)}, False))
    (hnr2 : ¬ (xn.ntfnSc = xt2.tcbSchedContext ∧ xn.ntfnSc ≠ none)) :
    receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ =
      receiveIpc (Z := Unit) t (.endpointCap e b rights) true rc' σ2 := by
  have tail : ∀ (c : Prop) [Decidable c] (o : ObjRef) (f : Unit → NonDet (State Unit) Unit), c → o = n →
      (NonDet.when c (maybeReturnSc (Z := Unit) o t) >>= f) σ = f () σ2 := by
    intro c _ o f hc ho
    subst ho
    unfold NonDet.when
    rw [if_pos hc, nd_bind_one hm]
  have tail2 : ∀ (c : Prop) [Decidable c] (o : ObjRef) (f : Unit → NonDet (State Unit) Unit), c → o = n →
      (NonDet.when c (maybeReturnSc (Z := Unit) o t) >>= f) σ2 = f () σ2 := by
    intro c _ o f hc ho
    subst ho
    unfold NonDet.when
    rw [if_pos hc, nd_bind_one (Ipc.maybeReturnSc_noop hkn2 hkt2 hnr2)]
  unfold receiveIpc
  dsimp only
  rw [nd_pure_bind', nd_pure_bind']
  rcases hrc with ⟨rfl, rfl⟩ | ⟨r, rr, xr, rfl, rfl, hkr, hr⟩
  · dsimp only
    rw [nd_pure_bind', nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt),
      nd_bind_one (getEndpoint_eq hk2), nd_bind_one (getTcbObjRef_eq _ hkt2)]
    simp only [hb, hb2]
    rw [nd_bind_one (getNotification_eq hkn), nd_bind_one (getNotification_eq hkn2), if_neg (by simp [hna]),
      if_neg (by simp [hna]), tail (xt.tcbBoundNotification ≠ none ∧ true = true) (the (some n)) _ (by simp [hb]) rfl,
      tail2 (xt2.tcbBoundNotification ≠ none ∧ true = true) (the (some n)) _ (by simp [hb2]) rfl]
  · obtain ⟨r2, rr2, xr2, h1, h2, hkr2, hr2⟩ := hrc2.resolve_left (fun h => by cases h.1)
    cases h1
    cases h2
    dsimp only
    rw [nd_bind_one (getReplyTcb_eq hkr), nd_bind_one (getReplyTcb_eq hkr2)]
    simp only [hr, hr2]
    rw [nd_when_false_bind (by simp [hr]), nd_when_false_bind (by simp [hr2])]
    rw [nd_pure_bind', nd_pure_bind', nd_bind_one (getEndpoint_eq hk), nd_bind_one (getTcbObjRef_eq _ hkt),
      nd_bind_one (getEndpoint_eq hk2), nd_bind_one (getTcbObjRef_eq _ hkt2)]
    simp only [hb, hb2]
    rw [nd_bind_one (getNotification_eq hkn), nd_bind_one (getNotification_eq hkn2), if_neg (by simp [hna]),
      if_neg (by simp [hna]), tail (xt.tcbBoundNotification ≠ none ∧ true = true) (the (some n)) _ (by simp [hb]) rfl,
      tail2 (xt2.tcbBoundNotification ≠ none ∧ true = true) (the (some n)) _ (by simp [hb2]) rfl]

end SpecC

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender with a bound notification
lending the receiver its SC at `J`** (module docstring), the sender as in
XTopJointRecvSendF's `SendOK`. -/
theorem JAtZ.recvSendRetJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : Entered σ)
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
  have hcb := J.canBlockCur ht hcur hkt hr hni hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (fun u hu => by rw [hni.2] at hu; cases hu) (by rw [← hcur]; exact hni.1)) ?_
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

end

end

end Fl4Proofs.P3
