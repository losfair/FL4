/-
P3 (DESIGN.md §9), IPC (KENTRY-PLAN sch17 item 3): **the bound SC return
before an endpoint receive at a switch mid state.** A blocking receive whose
bound notification lends the receiver (the current thread) its SC first runs
`maybe_return_sc`: the SC goes back and, the thread being current,
`rescheduleRequired` (under a pending `switchThread u` it enqueues `u`;
the spec's `maybeReturn_shape` / `whenResched_fields` and FL4's
`maybe_return_refines` read the action generically) sets `chooseNewThread`.
XTopJointRecvSigRet's `JAtZ.maybeReturnJQ` asks only that the switch target is
not the thread, so the resumed proofs carry over to a switch mid state
(`MidE`) unchanged after the return (the action is then `chooseNewThread`, the
case their tails already cover). The copies differ only in the entry facts:
`CurInv` by `J.curInv hni.ncn`, `CurRun` by `hni.run`, `CanBlock` by
`canBlockCurM`, the switch target `≠ ct` by `MidE.swNe`.

* `MidE.swNe`;
* `JAtZ.recvIpcRetJM` (XTopJointRecvIpcRet), `JAtZ.recvSendRetJM`
  (XTopJointRecvSendRet), `JAtZ.recvSendRetPJM` (XTopJointRecvSendRP),
  `JAtZ.recvSendRetPDJM` (XTopJointRecvSendRD), `JAtZ.recvSendRetTJM`
  (XTopJointRecvSendT).
-/
import Fl4Proofs.P3.XTopJointRecvSigM
import Fl4Proofs.P3.XTopJointRecvIpcLink
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- At a mid state the switch target is not the current thread. -/
theorem MidE.swNe {σ : Fl4Spec.State Unit} {t : U64} (h : MidE σ) (hcur : σ.curThread = t.bv) :
    ∀ u, σ.schedulerAction = .switchThread u → u ≠ t.bv := fun u hu => by
  rcases h.2.2 with e | ⟨v, e, hv⟩
  · rw [e] at hu; cases hu
  · rw [e] at hu; cases hu; rw [← hcur]; exact hv

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The blocking receive with a bound notification lending the thread its
SC at `J`** (module docstring). -/
theorem JAtZ.recvIpcRetJM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa hcur) hnq
  have hsp1 := receiveIpc_boundR b rights (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hk hns hkn hna he2
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (hni.swNe hcur) (by rw [← hcur]; exact hni.1)) ?_
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



end

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **The blocking receive from a waiting sender with a bound notification
lending the receiver its SC at `J`** (module docstring), the sender as in
XTopJointRecvSendF's `SendOK`. -/
theorem JAtZ.recvSendRetJM (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa hcur) hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (hni.swNe hcur) (by rw [← hcur]; exact hni.1)) ?_
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
theorem JAtZ.recvSendRetPJM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa hcur) hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (hni.swNe hcur) (by rw [← hcur]; exact hni.1)) ?_
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
theorem JAtZ.recvSendRetPDJM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa hcur) hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (hni.swNe hcur) (by rw [← hcur]; exact hni.1)) ?_
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
theorem JAtZ.recvSendRetTJM (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv) (hni : MidE σ)
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
  have hC : CurInv σ := J.curInv hni.ncn
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
  have hcb := J.canBlockCurM ht hcur hkt hr hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa hcur) hnq
  refine receive_ipc_blockR_red hrc hbound (by rw [← hbound]; exact hbz) hstN ?_
  refine WP.spec_mono (J.maybeReturnJQ ht hn hiC hkt hkn hxs0 hi0 hnqT ⟨hcb.nq, hcb.nr, hcb.na⟩
    (hni.swNe hcur) (by rw [← hcur]; exact hni.1)) ?_
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
