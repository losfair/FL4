/-
P3 (DESIGN.md §9), IPC: **a blocking `receive_ipc` from a waiting sender
without an SC that pushes a reply, the receiver's bound notification lending
it its SC, at `J`** (XTopJointRecvIpcLink's `JRecvSendHyp` (R1), sender
without an SC; l4v `receive_ipc`'s `maybe_return_sc`, then the `send_ep`
branch with `reply_push` not donating since the sender has no SC).

* `JAtZ.recvSendRetPJ`: XTopJointRecvSendRet's route (`JAtZ.maybeReturnJQ`,
  `receiveIpc_lend_eq`), the reply's covers at the state after by
  XTopJointRecvIpcRet's `JAtZ.recvCov_ofW`, then XTopJointRecvSendP's
  `JAtZ.recvSendPJG` / `JAtZ.recvSendFPJG` there, whose `hAct` takes a pending
  reschedule (`maybe_return_sc` of the current thread) when the sender has
  no SC.
-/
import Fl4Proofs.P3.XTopJointRecvSendRet
import Fl4Proofs.P3.XTopJointRecvSendP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender without an SC pushing a
reply, the receiver's bound notification lending it its SC, at `J`** (module
docstring): XTopJointRecvSendRet's route, then XTopJointRecvSendP's
`JAtZ.recvSendPJG` / `JAtZ.recvSendFPJG` at the state after
`maybe_return_sc` (a reschedule pending, the receiver without an SC). -/
theorem JAtZ.recvSendRetPJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
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
    (hrc : ReplyArg Z.R (L.mem s) rc rc' rv) (hok : PushOK xs rc) (hsn : xs.tcbSchedContext = none)
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

end

end

end Fl4Proofs.P3
