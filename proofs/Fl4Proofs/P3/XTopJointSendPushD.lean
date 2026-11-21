/-
P3 (DESIGN.md §9), IPC: **a call to a waiting receiver at `J` that pushes a
reply and donates the caller's SC** (toward `JSendRecvHyp`): a call with the
grant or grant-reply right and `can_donate` to a receiver with a reply object
and no SC. FL4 (and l4v `send_ipc`/`reply_push`) links the receiver's
(unlinked) reply to the caller, blocks the caller on it, pushes the reply on
the caller's SC's call stack and donates the SC to the receiver
(`bind_sc_reply`, `sched_context_donate`), then the receiver runs.

* `JAtZ.sendCallPDJ`: as XTopJointSendPush's `JAtZ.sendCallPJ` up to the
  reply unlink; then IpcPushCore's `reply_push_iC` (its donation step given the
  block's outcome), `JAtZ` after the block by `JAtZ.wake_postGR`, the donation
  by XTopJointPushDon's `JAtZ.pushDonJ`, the receiver `Running` by
  `JAtZ.stsIJ`, the tail `JAtZ.sendTailJ`; the spec's outcome
  `sendIpc_call_eq` (`replyPush_don_eq`, `pd_eq`).
* `SendRecvCPD`, `jSendRest_of` / `sendLeafJ2` (moved here from
  XTopJointSendPush): the five cases cover every send to a waiting
  receiver, any grant, so `JSendRestHyp` holds (the former `JSendRecvHyp`
  [W] is gone).
-/
import Fl4Proofs.P3.XTopJointPushDon
import Fl4Proofs.P3.BufJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **A call to a waiting receiver at `J` that pushes a reply and donates
the caller's SC** (module docstring): the caller has the grant or grant-reply
right (`hg`), the receiver a reply object (`hrepn`) and no SC (`hxdn`), the
call donates; as `JAtZ.sendCallPJ` up to the reply unlink, then `reply_push`
(`reply_push_iC`): the link and block on `IRel` and P1 (`set_blocked_on_reply`),
`JAtZ` there by `JAtZ.wake_postGR` at `pushSt`, the donation by
XTopJointPushDon's `JAtZ.pushDonJ`; the receiver `Running` by XTopJointStsI's
`JAtZ.stsIJ` (released: the caller's SC, `Inv.rd`), the tail
`JAtZ.sendTailJ`; the spec's outcome `sendIpc_call_eq` with
`replyPush_don_eq`/`pd_eq`. -/
theorem JAtZ.sendCallPDJ (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrs : xt.tcbState = .restart) (hft : xt.tcbFault = none) (hct : σ.curThread = t.bv)
    (hres : σ.schedulerAction = .resumeCurThread) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hxdn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext = none) :
    endpoint.send_ipc st arI s a blk true badge g gr true t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk true badge.bv g gr true t.bv e.bv σ).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hP0 := J.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J.tcbs_eq.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  obtain ⟨hst2, xs, hxs0, hq, hQ, hB⟩ := hx
  obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
  simp only [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hd', hq'⟩ := hq
  have hdd : d' = d := eq_of_bv hd'.symm
  subst hdd
  have hdT : d' ∈ Z.T := hQ.mem d' (by simp)
  have hda := hP.tcb d' hdT
  obtain ⟨xd, hkd, -⟩ := hI.1.tcb d' hdT
  have hxd := hR.at_tcb hdT hkd
  have hd3 : (L.mem s (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by rw [hrs]; decide
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := kheap_ne hkt hk (fun _ h1 h2 => by subst h1; cases h2)
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdc : d'.bv ≠ σ.curThread := by rw [hct]; exact Ne.symm htd'
  -- P1's facts at the start
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := J.blk
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hHe : H e = some .ep := J.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s e) ?_
  rintro _ rfl
  have hhead : (L.epQ s e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s σ hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σ e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
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
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have Fr1 : CFr e.bv d'.bv σ σ1 := CFr.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ σ1 := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hk (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (J.xferStepGJ hk (epDeq (.recvEP (d'.bv :: q)) d'.bv) hR1 hS1 hW1 F1 ht hdT htd hkt hkd hft
    badge g h1 hB1 hX1 hS1' hSg1) ?_
  rintro s2 ⟨x2, um2, yb, σy, Gy, Jy, e2, hx2, hR2, hS2', hA2, hW2, F2, h2, hB2, hX2, hS2'', hSg2, f2, hksy, hKy, hCnKy, hyk⟩
  have hncn : ∀ {q' : Fl4Spec.ObjRef} {o' : Fl4Spec.KernelObject}, σ.kheap q' = some o' →
      (∀ r cs, o' ≠ .cnode r cs) → σy.kheap q' = some o' :=
    fun hq ho => (hyk _ fun r cs h0 => ho r cs (by rw [hq] at h0; exact Option.some.inj h0)).trans hq
  have hky : σy.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := hncn hk (fun _ _ h0 => by cases h0)
  have hkdy : σy.kheap d'.bv = some (.tcb xd) := hncn hkd (fun _ _ h0 => by cases h0)
  have hkty : σy.kheap t.bv = some (.tcb xt) := hncn hkt (fun _ _ h0 => by cases h0)
  have hcty : σy.curThread = σ.curThread := hKy.2.2.2.2
  have hsay : σy.schedulerAction = σ.schedulerAction := by
    have e := congrArg Fl4Spec.AbstractState.schedulerAction hCnKy.1; exact e
  have hidy : σy.idleThread = σ.idleThread := by
    have e := congrArg Fl4Spec.AbstractState.idleThread hCnKy.1; exact e
  have hrqy : σy.readyQueues = σ.readyQueues := by
    have e := congrArg Fl4Spec.AbstractState.readyQueues hCnKy.1; exact e
  have hrly : σy.releaseQueue = σ.releaseQueue := by
    have e := congrArg Fl4Spec.AbstractState.releaseQueue hCnKy.1; exact e
  set σ1y := Notif.updK σy e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1y
  have hkt1y : σ1y.kheap t.bv = some (.tcb xt) := by simp [σ1y, hte, hkty]
  have hkd1y : σ1y.kheap d'.bv = some (.tcb xd) := by simp [σ1y, hde, hkdy]
  have hk1ey : σ1y.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1y]
  have Fr1y : CFr e.bv d'.bv σy σ1y := CFr.upd hky (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
    by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
    by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1y : IK d'.bv σy σ1y := IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hky (fun o0 h => by
    rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1y : SKeep σy σ1y := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv))
    (fun y h => by cases h) (fun _ _ h => by cases h)
  have hq1y : ∀ e'' ∈ Z.E, ∀ z, σ1y.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    refine hq1 e'' he'' z ?_
    by_cases hee : e''.bv = e.bv
    · rw [hee] at hz ⊢; rw [hk1ey] at hz; rw [hk1e]; exact hz
    · simp only [σ1y, Notif.updK_kheap, Function.update_of_ne hee] at hz
      simp only [σ1, Notif.updK_kheap, Function.update_of_ne hee]
      exact keepC_back hKy.1 hz (fun _ _ h0 => by cases h0)
  set σ2 := Notif.updK (Endp.setUm σ1y um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1y]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1ey]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1y e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨⟨d', hdT, (a_reply hda).2⟩, ?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have Fr2 : CFr e.bv d'.bv σy σ2 := (Fr1y.trans (CFr.um _ _ σ1y um2)).trans (CFr.upd (σ := Endp.setUm σ1y um2) hkd1y
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σy σ2 := IK1y.trans ((IK.um _ σ1y um2).trans (IK.updSelf (σ := Endp.setUm σ1y um2) hkd1y hxsc))
  have SK2 : SKeep σy σ2 := SK1y.trans ((SKeep.um σ1y um2).trans (SKeep.updK (σ := Endp.setUm σ1y um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1y, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb yb := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkd _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
    simp [σ2, σ1y, hwe, hwd, hncn hkr (fun _ _ h0 => by cases h0)]
  have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd]) hkr
  have hX2' := IpcRel.ofSRN hR2 hS2'
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
      hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
    (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
        (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
      (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
  rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩

  have J0 := J
  have hk0 := hk
  have hkd0 := hkd
  have hkt0 := hkt
  have J := Jy
  have hkd : σy.kheap d'.bv = some (.tcb xd) := hkdy
  have hkt : σy.kheap t.bv = some (.tcb xt) := hkty
  have hk : σy.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := hky
  have hres : σy.schedulerAction = .resumeCurThread := hsay.trans hres
  have hti : σy.curThread ≠ σy.idleThread := by rw [hcty, hidy]; exact hti
  have hct : σy.curThread = t.bv := hcty.trans hct
  have hnq : ∀ dm q', t.bv ∉ σy.readyQueues dm q' := by rw [hrqy]; exact hnq
  have hdc : d'.bv ≠ σy.curThread := by rw [hcty]; exact hdc
  have hrepn : ∀ xd, σy.kheap d'.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none :=
    fun xd h => hrepn xd (by rw [hkdy] at h; rw [hkd0]; exact h)
  have hxdn : ∀ xd, σy.kheap d'.bv = some (.tcb xd) → xd.tcbSchedContext = none :=
    fun xd h => hxdn xd (by rw [hkdy] at h; rw [hkd0]; exact h)
  have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
    intro r hr er
    obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
    rw [er, hrA] at b2; rw [← b2]; exact z3
  set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
  set xr3 : Fl4Spec.Reply := { xr with replyTcb := none } with hxr3
  set σ3a := Notif.updK σ2 w.bv (.reply xr3) with hσ3a
  have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
  have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
  have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
    stsAct_ne hct3a
  set σ3 := Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv with hσ3
  have hU : Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) (some w.bv) σ2 =
      ({((), σ3)}, False) := e3
  have hW3' : P1.WritesIn st yb s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
    hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  have Fr3 : CFr e.bv d'.bv σy σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σy σ3 := by
    have IK3a : IK d'.bv σy σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σy (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : SKeep σy σ3 :=
    ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σy.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σy.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans F2 (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hks3 : L.ksb s3 = L.ksb yb := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hCI : CurInv σy := J.cur.resolve_left (by rw [hres]; intro h; cases h)
  have hnrT : t.bv ∉ σy.releaseQueue := by rw [← hct]; exact hCI.notRel
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = 2 := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st, hrs]; rfl
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (Or.inr (Or.inl hw3))
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σy d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [IK3.2.1]; exact hnq, by rw [IK3.2.2.1]; exact hnrT⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [IK3.2.1]; exact hnqD.1, by rw [IK3.2.2.1]; exact hnqD.2⟩
  have bits3 : ∀ u ∈ Z.T, NotQueued σ3 u.bv →
      (L.mem s3 (P1.inqA u) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s3 (P1.inqA u) &&& sched.Q_RELEASE) = 0#u64 := by
    intro u hu hnu
    refine ⟨Classical.byContradiction fun h => ?_, Classical.byContradiction fun h => ?_⟩
    · have hm := (hcq3.queued u hu).1 h
      apply hnu.1 0 (specPrio (L.mem s3 (P1.prioA u)))
      rw [hs3.rq _ (hcq3.prio u hu)]
      exact List.mem_map_of_mem hm
    · have hm := (hcq3.released u hu).1 h
      apply hnu.2
      rw [hs3.rel]
      exact List.mem_map_of_mem hm
  obtain ⟨hqbT, hrbT⟩ := bits3 t ht hnqT3
  obtain ⟨hqbD, hrbD⟩ := bits3 d' hdT hnqD3
  have ha0 : L.actionW s3 = 0#u64 := by
    have h := hSR3.act
    rw [hact3, hres] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha0] at h'; exact (hcq3.tcbs u hu).ne0 (by rw [← h']; rfl)
  have hcw3 : L.curW s3 = t := by
    have h : (nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σy.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σy.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σy.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σy.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h0 =>
    hB3.sact t htH (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0, hcw3⟩))))) h0
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the caller's SC, donated
  obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
  rw [hct, hkt] at hkc; cases hkc
  obtain ⟨y, n, hky0⟩ := hCI.sc
  have hya : Fl4Spec.scActive y = true := hCI.active (J.curSc_ne_idle hCI hti) y n hky0
  obtain ⟨sc, hsC, esc⟩ := J.obj.sc _ y n hky0
  rw [← esc] at hky0 hcs
  obtain ⟨y1, n1, hky1, hyt⟩ := J.inv.back _ _ _ hkt hcs
  rw [hky0] at hky1; cases hky1
  have hrelσ : Fl4Spec.scActive y = true → released σy y := fun ha =>
    J.inv.rd t.bv xt hkt (Or.inl (by rw [hrs]; rfl)) xt sc.bv y n hkt hcs hky0 ha hnrT
  have hse : sc.bv ≠ e.bv := kheap_ne hky0 hk (fun _ h1 h2 => by subst h1; cases h2)
  have hsd : sc.bv ≠ d'.bv := kheap_ne hky0 hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hsw : sc.bv ≠ w.bv := kheap_ne hky0 (hncn hkr (fun _ _ h0 => by cases h0)) (fun _ h1 h2 => by subst h1; cases h2)
  have hst : sc.bv ≠ t.bv := kheap_ne hky0 hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hky2 : σ2.kheap sc.bv = some (.schedContext y n) := by simp [σ2, σ1y, hsd, hse, hky0]
  have hky3 : σ3.kheap sc.bv = some (.schedContext y n) := by rw [stsAct_kheap]; simp [σ3a, hsd, hsw, hky2]
  have hsw3 : L.mem s3 (P1.scA t) = sc := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs3.tcb t ht
    rw [hkt3] at hk'; cases hk'
    exact optRef_some_eq (hscw.symm.trans hcs)
  have hxdn3 : x3.tcbSchedContext = none := by rw [hsc3]; exact hxdn xd hkd
  -- the J state after the block
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by rw [hrs]; simp [tsCode])
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J0.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σy.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem yb (rNextA q') = 0#u64 ∧ L.mem yb (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D yb _ σy J q' hq'' xr d'.bv xd hx' hxt' hkd
      (by rw [hstd]; rfl)
  have hrib3 : RelIfBound σ3 d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK3
  have I3 : Inv σ3 := ((J.inv.toBut d'.bv).ik hnqD IK3).1.inv fun _ _ _ => hrib3
  have hscA3 : ∀ p y n, σ3.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σy.kheap p = some (.schedContext y n) := SK3.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    have e1 : σy.curSc = q.bv := by rw [← esc]; exact Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp0
    exact hCI.active (J.curSc_ne_idle hCI hti) y n hp0
  set xtP : Fl4Spec.Tcb := { xt with tcbState := .blockedOnReply w.bv } with hxtP
  set xwP : Fl4Spec.Reply := { xr3 with replyTcb := some t.bv } with hxwP
  set σP := pushSt σ3 t.bv w.bv xr3 xt with hσP
  set σD := pdSt σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n with hσD
  have hktP : σP.kheap t.bv = some (.tcb xtP) := ps_kt
  have hkwP : σP.kheap w.bv = some (.reply xwP) := ps_kw hwt
  have hkdP : σP.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hkyP : σP.kheap sc.bv = some (.schedContext y n) := by rw [ps_ko hst hsw]; exact hky3
  have hcnP : σP.schedulerAction = .chooseNewThread := ps_act (by rw [hct3, hct]) (by rw [hact3, hres])
  have hnsw : ∀ u, σP.schedulerAction ≠ .switchThread u := fun u e0 => by rw [hcnP] at e0; cases e0
  have hctP : σP.curThread = t.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct.trans (hct3.trans hct)
  have hcscP : σP.curSc = sc.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).csc.trans (Fr3.sk.csc.trans esc.symm)
  have hnqtP : NotQueued σP t.bv := ⟨by rw [ps_rq]; exact hnqT3.1, by rw [ps_rel]; exact hnqT3.2⟩
  have hnqdP : NotQueued σP d'.bv := ⟨by rw [ps_rq]; exact hnqD3.1, by rw [ps_rel]; exact hnqD3.2⟩
  have hhP := J.stackHead hsC hky0 (hRR w hwR xr (hncn hkr (fun _ _ h0 => by cases h0)) hb').1
  have hhP' : ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σP.kheap h = some (.reply x) := by
    intro h l hr
    obtain ⟨h1, h2, x, hx⟩ := hhP h l hr
    refine ⟨h1, h2, x, ?_⟩
    have ht' : h ≠ t.bv := fun e0 => by rw [e0, hkt] at hx; cases hx
    have hd' : h ≠ d'.bv := fun e0 => by rw [e0, hkd] at hx; cases hx
    have he' : h ≠ e.bv := fun e0 => by rw [e0, hk] at hx; cases hx
    rw [ps_ko ht' h2, stsAct_kheap]
    simp [σ3a, hd', h2, σ2, σ1y, he', hx]
  have hpdE := pd_eq hktP hkdP hkyP hkwP (Ne.symm hsw) hhP' hyt htd' hst hsd hwt hwd
    hctP.symm hnqtP hnsw
  have hpushE : Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σD)}, False) := by
    rw [replyPush_don_eq hkt3 hkd3 hkr3 hwt hcs hxdn3]; exact hpdE
  have hns3 : tsCode xt.tcbState ≠ 6 := by rw [hrs]; decide
  -- the push: link and block (`J` again), then the donation at `J`
  have hPush : ipc.reply_push st arI s3 a t d' w true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σ')}, False) ∧
      (σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR ((Z.mv Gy Z.vs).mv (Z.mv Gy Z.vs).G V) H Cs Ac Lst' D r.1 a σ') ⦄ := by
    refine reply_push_iC (don := true) (P := fun s' σ' => σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR ((Z.mv Gy Z.vs).mv (Z.mv Gy Z.vs).G V) H Cs Ac Lst' D s' a σ')
      hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT) (fun s' _ _ e0 => ?_) ?_
    · exfalso
      have h1 : σD.kheap t.bv = some (.tcb xtP) := by rw [← e0]; exact hktP
      have h2 : σD.kheap t.bv = some (.tcb { xtP with tcbSchedContext := none }) :=
        @dn_kt (bdSt σP sc.bv w.bv y n xwP) t.bv d'.bv sc.bv xtP x3 { y with scReplies := w.bv :: y.scReplies } n
          htd' hst
      rw [h2] at h1
      have h3 : ({ xtP with tcbSchedContext := none } : Fl4Spec.Tcb) = xtP := by
        injection h1 with h1; injection h1
      have h4 : (none : Option Fl4Spec.ObjRef) = some sc.bv := (congrArg Fl4Spec.Tcb.tcbSchedContext h3).trans hcs
      cases h4
    · intro _ s4 hsb hR4 hS4 _ _ _ _
      rw [hsw3]
      have hsb' : sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok s4 := hsb
      -- FL4's words and P1 at the block
      have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
        obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
        exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
      have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
        have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
        rw [hsb', WP.spec_ok] at h; exact h
      have hW4' : P1.WritesIn st yb s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c yb σy b ∨ RcvBufW xd b) :=
        hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3 (SzKeepC.of Fr3.szKeep) hb))
      have hb4 := P1.sched.set_blocked_on_reply.ipc s3 t w Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 hcA
      rw [hsb', WP.spec_ok] at hb4
      obtain ⟨h4, hB4, hX4, hS4', hSg4, -, -, -, -, -, -⟩ := hb4
      have hO3 := hX3.1
      obtain ⟨hrΩ3, -⟩ := P1.objs_omega hO3 hSg3.sub
      have f1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H)
          s3 (L.wr s3 (P1.rTcbA w) t) :=
        P1.foot_wr (h3.omega _ (hrΩ3 w hwH).1).1 (P1.kw_sg (hO3.tcbW hwH))
      have q1 := (P1.omega_wr (v := t) h3 (hrΩ3 w hwH).1).1
      have f4 := P1.sched.set_blocked_on_reply.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H)
        (Z := P1.Heap.scBits H) (Es := P1.EH H) _ t w q1 htH
      rw [hsb', WP.spec_ok] at f4
      have hfoot4 : P1.WritesIn st yb s4 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
          (P1.Heap.scBits H) (P1.EH H) yb b ∨ RcvBufW xd b) :=
        footW_trans (footW_trans F3 (footW_of f1)) (footW_of f4)
      have hIR4 := IpcRel.ofSRN hR4 hS4
      obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := JAtZ.bufRebaseX (Z := Z.mv Gy Z.vs) J hdT hdth hkd hW4' hfoot4
      have hIu := Ju.xtop.irelK Ju.ks Ju.buf
      have hRRu : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σy umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
          Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
        fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D su _ (Endp.setUm σy umu) Ju q' hq'' xr d'.bv xd hx'
          hxt' hkd (by rw [hstd]; rfl)
      have hF4 : IFrame (L := L) Z.th su s4 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
      have hblk4 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
          (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s4 := ⟨⟨Q0, R0, h4⟩, hB4, hX4, hS4', hSg4⟩
      have I4 : Inv σP := ps_inv hkt3 hkr3 hwt I3 hnqT3.1 hnqT3.2
      have B4 : BlockedScActive σP := ps_bsa hkt3 hkr3 hwt hscA3 (Fr3.bsa J.bsa)
      have hidT3 : σ3.idleThread ≠ t.bv := by rw [Fr3.sk.idle, ← hct]; exact fun e0 => hti e0.symm
      have hAI4 : ActIdle σP :=
        ⟨fun u hu => (by rw [hcnP] at hu; cases hu), ps_idleOK hkt3 hkr3 hwt hidT3 (Fr3.idleOK J.act.2)⟩
      have hkq : ∀ q ∈ D, σP.kheap q.bv = σ3.kheap q.bv := fun q hq => ps_ko (hcD q hq) (hwD q hq)
      have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
          (σP.kheap q = some o ↔ σ3.kheap q = some o) := fun h1 h2 => ps_oth hkt3 hkr3 hwt h1 h2
      obtain ⟨V', J4⟩ := Ju.wake_postGR (by rw [← hKy.2.1] at hIR4; exact hIR4) hF4 hWu hblk4 hFu (DWFr.ofUm (DWFr.ofCFr Fr3) umu) ps_skD
        (ps_ksub hkt3 hkr3 hwt) (ps_szKeep hkt3 hkr3 hwt) (ps_ykeep hkt3 hkr3 hwt) (ps_mcpKeep hkt3 hkr3 hwt)
        (ps_bufKeep hkt3 hkr3 hwt) (fun d _ h => ps_recvB hkt3 hkr3 hwt h) (ps_ksz hkt3 hkr3 hwt)
        (ps_kback hkt3 hkr3 hwt) (ps_ipcFr hkt3 hkr3 hwt) (ps_ck hkt3 hkr3 hwt) (fun d _ h => ps_free hkt3 hkr3 hwt h)
        (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
        I4 B4 hAI4 (Or.inl hcnP) (Or.inl (by rw [hcnP]; intro h; cases h))
        (ps_own hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).own ⟨d', hdT, rfl⟩ J.own))
        (ps_off hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).off J.off)) (ps_nsc hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).nsc J.nsc))
        (ps_isorted hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).isorted J.isorted)) hRRu htD
      -- the reply's links at the block
      obtain ⟨hdet, hn0, hp0⟩ := hRRu w hwR xr (hncn hkr (fun _ _ h0 => by cases h0)) hb'
      obtain ⟨-, -, -, -, k4⟩ := Ju.cnW_keeps hWu
      refine WP.spec_mono (J4.pushDonJ hAT ht hdT hwR hsC htd hktP hkdP hkwP hkyP rfl hcs hyt hxdn3 rfl rfl
        hctP hcscP hcnP hnqtP hnqdP hya hdet (by rw [(k4 w hwR).2]; exact hn0) (by rw [(k4 w hwR).1]; exact hp0)
        htD) ?_
      rintro ⟨s5, a5⟩ ⟨ha5, hsp5, Lst5, J5⟩
      simp only at ha5
      subst a5
      exact ⟨rfl, _, hsp5, fun _ => ⟨V', Lst5, J5⟩⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σ')}, False) ∧
      (σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR ((Z.mv Gy Z.vs).mv (Z.mv Gy Z.vs).G V) H Cs Ac Lst' D r.1 a σ'))
    ?_ ?_
  · rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s5, a5⟩ ⟨ha5, σ5', hpush, hPσ⟩
  simp only at ha5 hpush hPσ ⊢
  subst a5
  try dsimp only
  have e5 : σ5' = σD := by
    have h := hpush.symm.trans hpushE
    exact congrArg Prod.snd (Set.singleton_injective (congrArg Prod.fst h))
  obtain ⟨V5, Lst5, J5⟩ := hPσ e5
  subst e5
  -- the receiver runs (`Inactive` with the donated SC)
  set x4 : Fl4Spec.Tcb := { x3 with tcbSchedContext := some sc.bv } with hx4
  have hk5 : σD.kheap d'.bv = some (.tcb x4) := @pd_kd σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n
  have hst5 : L.mem s5 (P1.stA d') = sched.TS_INACTIVE := by
    have h := ((J5.xtop.irelK J5.ks J5.buf).1.toN.at_tcb hdT hk5).st
    rw [stA_tStA, P1.ts_inactive]
    exact UScalar.eq_of_val_eq (by rw [h]; rfl)
  have htmD : σD.curTime = σy.curTime := (@pd_tm σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
    ((ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).tm.trans SK3.2.1)
  have hkpD : σD.kheap sc.bv = some (.schedContext { { y with scReplies := w.bv :: y.scReplies } with
      scTcb := some d'.bv } n) :=
    @dn_kp (bdSt σP sc.bv w.bv y n xwP) t.bv d'.bv sc.bv xtP x3 { y with scReplies := w.bv :: y.scReplies } n hsd
  have hrelD : RelIfBound σD d'.bv := by
    intro x' scp y' n' hx' hsc' hky' ha' _
    rw [hk5] at hx'; cases hx'
    simp only [x4, Option.some.injEq] at hsc'
    subst hsc'
    rw [hkpD] at hky'
    cases hky'
    have := hrelσ hya
    unfold released at this ⊢
    rw [htmD]; exact this
  refine WP.spec_bind (J5.stsIJ hdT (fun h => htD d' h rfl) hk5 rfl .running (by simp [tsCode]) sched.TS_RUNNING
    (by unfold sched.TS_RUNNING; rfl) (fun _ => hrelD)
    (P1.sched.set_thread_state.running_blkI (Es := P1.EH H) s5 d' J5.blk hdH hst5)) ?_
  rintro s6 ⟨Lst6, J6⟩
  set x6 : Fl4Spec.Tcb := { x4 with tcbState := .running } with hx6
  have hdcD : d'.bv ≠ σD.curThread := by
    rw [show σD.curThread = t.bv from (@pd_ct σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans hctP]
    exact Ne.symm htd'
  have e6 : stsAct (updK σD d'.bv (.tcb x6)) d'.bv = updK σD d'.bv (.tcb x6) := stsAct_ne hdcD
  have hk6 : (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).kheap d'.bv = some (.tcb x6) := by
    rw [e6]; simp [updK]
  have hnr6 : d'.bv ∉ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).releaseQueue := by
    rw [e6]
    show d'.bv ∉ σD.releaseQueue
    rw [show σD.releaseQueue = σy.releaseQueue from (@pd_rel σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
      ((@ps_rel σ3 t.bv w.bv xr3 xt).trans SK3.1)]
    exact hnqD.2
  have hact6 : ∀ p y' n', x6.tcbSchedContext = some p →
      (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).kheap p = some (.schedContext y' n') → Fl4Spec.scActive y' = true := by
    intro p y' n' hp hy'
    simp only [x6, x4, Option.some.injEq] at hp
    subst hp
    rw [e6] at hy'
    simp only [updK_kheap, Function.update_of_ne hsd] at hy'
    rw [hkpD] at hy'
    cases hy'
    exact hya
  have hti6 : d'.bv ≠ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).idleThread := by
    rw [e6]
    show d'.bv ≠ σD.idleThread
    rw [show σD.idleThread = σy.idleThread from (@pd_idle σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
      ((ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle.trans Fr3.sk.idle)]
    exact hid
  have htc6 : d'.bv ≠ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).curThread := by
    rw [e6]; exact hdcD
  have hspec := sendIpc_call_eq (don := true) hk0 hkd0 hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpushE hk5
    (t := t.bv)
  refine WP.spec_mono (J6.sendTailJ hdT hk6 rfl hnr6 hact6 hti6 htc6) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec, h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

/-- **The calls to a waiting receiver `JAtZ.sendCallPDJ` covers**: a call
with `can_donate` from a sender without a fault, any grant, the head
receiver with a reply object and without an SC, the grant or
grant-reply right. -/
def SendRecvCPD (σ : Fl4Spec.State Unit) (call g gr don : Bool) (t e : Fl4Spec.ObjRef) : Prop :=
  call = true ∧ don = true ∧ ∃ xt d q, σ.kheap t = some (.tcb xt) ∧ xt.tcbFault = none ∧
    σ.kheap e = some (.endpoint (.recvEP (d :: q))) ∧
    (g = true ∨ gr = true) ∧
    (∀ xd, σ.kheap d = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) ∧
    (∀ xd, σ.kheap d = some (.tcb xd) → xd.tcbSchedContext = none)

set_option maxHeartbeats 4000000 in
/-- **`JSendRestHyp` holds** at the caller's restart state (a send to an
endpoint with receivers, the caller without a fault): the five cases cover
every such send, any grant (XTopJointXferG's `JAtZ.xferStepGJ`):
`JAtZ.sendRecvJ0` for `SendRecvBasic`, `JAtZ.sendCallIJ` for `SendRecvCI`,
`JAtZ.sendDonJ` for `SendRecvDon`, `JAtZ.sendCallPJ` for `SendRecvCP`,
`JAtZ.sendCallPDJ` for `SendRecvCPD`. -/
theorem jSendRest_of (hAT : P0.ArchTotal arI) {s1 : S} {ar : A} {σ1 : Fl4Spec.State Unit}
    (J1 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 ar σ1) {ct p : U64} (hct : ct ∈ Z.T) (hp : p ∈ Z.E)
    {xt : Fl4Spec.Tcb} (hkt : σ1.kheap ct.bv = some (.tcb xt)) (hrs : xt.tcbState = .restart)
    (hft0 : xt.tcbFault = none) (hcur : σ1.curThread = ct.bv) (hres : σ1.schedulerAction = .resumeCurThread)
    (hti : σ1.curThread ≠ σ1.idleThread) (hnq : ∀ dm q, ct.bv ∉ σ1.readyQueues dm q)
    (blk call : Bool) (b : U64) (g gr don : Bool) :
    JSendRestHyp (L := L) arI AR s1 ar σ1 blk call b g gr don ct p := by
  intro x hk hc
  by_cases hb : SendRecvBasic σ1 call don ct.bv p.bv
  · obtain ⟨rfl, xt', dv, q, hkt', hft, hk', hdon⟩ := hb
    rw [hkt] at hkt'; cases hkt'
    have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk'
    obtain ⟨-, xs, hxs0, hq, -, -⟩ := hx
    obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    obtain ⟨hd, -⟩ := hq
    obtain rfl : dv = d.bv := by first | exact hd | exact hd.symm
    exact J1.sendRecvJ0 hct hkt hrs hft hcur hp hk' blk b g gr don hdon
  by_cases hci : SendRecvCI σ1 call g gr ct.bv p.bv
  · obtain ⟨rfl, xt', dv, q, hkt', hft, hk', hno⟩ := hci
    rw [hkt] at hkt'; cases hkt'
    have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk'
    obtain ⟨-, xs, hxs0, hq, -, -⟩ := hx
    obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    obtain ⟨hd, -⟩ := hq
    obtain rfl : dv = d.bv := by first | exact hd | exact hd.symm
    exact J1.sendCallIJ hct hkt hrs hft hcur hres hti hnq hp hk' blk b g gr don hno
  by_cases hdo : SendRecvDon σ1 call don ct.bv p.bv
  · obtain ⟨rfl, rfl, xt', dv, q, hkt', hft, hk', hsn⟩ := hdo
    rw [hkt] at hkt'; cases hkt'
    have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk'
    obtain ⟨-, xs, hxs0, hq, -, -⟩ := hx
    obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    obtain ⟨hd, -⟩ := hq
    obtain rfl : dv = d.bv := by first | exact hd | exact hd.symm
    exact J1.sendDonJ hAT hct hkt hrs hft hcur hres hti hnq hp hk' blk b g gr hsn
  by_cases hcp : SendRecvCP σ1 call g gr don ct.bv p.bv
  · obtain ⟨rfl, xt', dv, q, hkt', hft, hk', hg, hrepn, hnd⟩ := hcp
    rw [hkt] at hkt'; cases hkt'
    have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk'
    obtain ⟨-, xs, hxs0, hq, -, -⟩ := hx
    obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    obtain ⟨hd, -⟩ := hq
    obtain rfl : dv = d.bv := by first | exact hd | exact hd.symm
    exact J1.sendCallPJ hAT hct hkt hrs hft hcur hres hti hnq hp hk' blk b g gr don hg hrepn hnd
  by_cases hcpd : SendRecvCPD σ1 call g gr don ct.bv p.bv
  · obtain ⟨rfl, rfl, xt', dv, q, hkt', hft, hk', hg, hrepn, hxdn⟩ := hcpd
    rw [hkt] at hkt'; cases hkt'
    have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk'
    obtain ⟨-, xs, hxs0, hq, -, -⟩ := hx
    obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons, List.cons.injEq] at hq
    obtain ⟨hd, -⟩ := hq
    obtain rfl : dv = d.bv := by first | exact hd | exact hd.symm
    exact J1.sendCallPDJ hAT hct hkt hrs hft hcur hres hti hnq hp hk' blk b g gr hg hrepn hxdn
  · -- every send to a waiting receiver is one of the five cases
    exfalso
    cases x with
    | idleEP => exact hc trivial
    | sendEP l => exact hc rfl
    | recvEP l =>
      have hx := (J1.xtop.irelK J1.ks J1.buf).1.toE.at_ep hp hk
      obtain ⟨-, xs, hxs0, hq, hQ, -⟩ := hx
      obtain ⟨d, xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
      have hk2 : ∃ q', σ1.kheap p.bv = some (.endpoint (.recvEP (d.bv :: q'))) := by
        first
          | (rw [← hq] at hk; exact ⟨_, hk⟩)
          | (rw [hq] at hk; exact ⟨_, hk⟩)
      obtain ⟨q', hk2⟩ := hk2
      cases call with
      | false =>
        by_cases hsc : don = false ∨ ∀ xd, σ1.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none
        · exact hb ⟨rfl, xt, d.bv, q', hkt, hft0, hk2, hsc⟩
        · have hdon : don = true := by
            cases don
            · exact absurd (Or.inl rfl) hsc
            · rfl
          refine hdo ⟨rfl, hdon, xt, d.bv, q', hkt, hft0, hk2, fun xd h' => ?_⟩
          by_contra hne
          exact hsc (Or.inr fun xd' h'' => by rw [h'] at h''; cases h''; exact hne)
      | true =>
        by_cases hggr : g = true ∨ gr = true
        · by_cases hrep : ∀ xd, σ1.kheap d.bv = some (.tcb xd) → ∀ e' rep dd,
              xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
          · by_cases hsc : don = false ∨ ∀ xd, σ1.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none
            · exact hcp ⟨rfl, xt, d.bv, q', hkt, hft0, hk2, hggr, hrep, hsc⟩
            · have hdon : don = true := by
                cases don
                · exact absurd (Or.inl rfl) hsc
                · rfl
              refine hcpd ⟨rfl, hdon, xt, d.bv, q', hkt, hft0, hk2, hggr, hrep, fun xd h' => ?_⟩
              by_contra hne
              exact hsc (Or.inr fun xd' h'' => by rw [h'] at h''; cases h''; exact hne)
          · refine hci ⟨rfl, xt, d.bv, q', hkt, hft0, hk2, Or.inr fun xd h' e' rep dd hst => ?_⟩
            by_contra hne
            exact hrep fun xd' h'' e'' rep' dd' hst' => by
              rw [h'] at h''; cases h''; rw [hst] at hst'; cases hst'; exact hne
        · refine hci ⟨rfl, xt, d.bv, q', hkt, hft0, hk2, Or.inl ⟨?_, ?_⟩⟩
          · cases g
            · rfl
            · exact absurd (Or.inl rfl) hggr
          · cases gr
            · rfl
            · exact absurd (Or.inr rfl) hggr

set_option maxHeartbeats 4000000 in
/-- **The endpoint cap's leaf at `J`** (XTopJointIpcJ's `sendLeafJ` with
`jSendRest_of` at the restart state). -/
theorem sendLeafJ2 (hAT : P0.ArchTotal arI) {s : S} {ar : A} {σ σ1 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (hni : Entered σ) (hnq : ∀ d q, σ.curThread ∉ σ.readyQueues d q)
    (hnf : ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbFault = none) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    {sl : Fl4Spec.CslotPtr} (hA : AbsSlot Z.th sl) {p b : U64} {x1 x2 x3 x4 : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Endpoint p b x1 x2 x3 x4))
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False))
    (blk call : Bool) (g gr don : Bool) :
    XLeaf (L := L) (JAt (L := L) arI AR) s ar σ (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let (s2, a1) ← endpoint.send_ipc st arI s1 ar blk call b g gr don ct p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1))
      (Fl4Spec.sendIpc (Z := Unit) blk call b.bv g gr don σ1.curThread p.bv σ1) := by
  have hpE := J.slotE hA hc
  obtain ⟨-, xr0, hkr, hrun0⟩ := J.curRunnable hni hct
  obtain ⟨s1, σ1', x, -, hst1, hkx, hcur, eσ1, -, hidl, hcur1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  obtain rfl := restart_out_eq hst1 hst
  have hrun : Fl4Spec.runnable x.tcbState = true := by rw [hkx] at hkr; cases hkr; exact hrun0
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hcq, -⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hcq.curT
  have hkt1 : σ1'.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [eσ1, (stsAct_fields _ _).1]; simp [Notif.updK]
  have hc1 : σ1'.curThread = ct.bv := hcur1.trans hcur
  -- still resumed (the current thread stays schedulable), not idle, in no ready queue (`sendLeafJ`)
  set xr : Fl4Spec.Tcb := { x with tcbState := .restart }
  have hsch : Fl4Spec.schedulable ct.bv σ = true := by
    have h := ct_schedulable (J.curInv (by rw [hni.2]; simp)) J.act J.inv (hcur ▸ hkx) hrun
    rw [hcur] at h; exact h
  have hsch1 : Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb xr)) = true := by
    rw [schedulable_updK_tcb (y := xr) (y' := x) (by rw [hrun]; rfl) rfl]
    exact (schedulable_heap (σ := σ) (σ' := Notif.updK σ ct.bv (.tcb x))
      (by simp only [Notif.updK_kheap]; exact Function.update_eq_self_iff.2 hkx.symm) rfl ct.bv).trans hsch
  have hres1 : σ1'.schedulerAction = .resumeCurThread := by
    rw [eσ1]; unfold Notif.stsAct
    rw [if_neg (fun h => by simp [hsch1] at h)]
    exact hni.2
  have hti1 : σ1'.curThread ≠ σ1'.idleThread := by rw [hcur1, hidl]; exact hni.1
  have hrq1 : σ1'.readyQueues = σ.readyQueues := by
    rw [eσ1]; unfold Notif.stsAct; split <;> rfl
  have hnq1 : ∀ d q, ct.bv ∉ σ1'.readyQueues d q := by
    rw [hrq1, ← hcur]; exact hnq
  refine sendLeafJ J hni hnq hct hA hc hst blk call g gr don fun s1' σ1'' h1 h2 => ?_
  have e1 : s1' = s1 := eq_of_ok_eq (h1.symm.trans hs1)
  subst e1
  obtain rfl := restart_out_eq h2 hst
  exact jSendRest_of hAT J1 hctT hpE hkt1 rfl (hnf x (by rw [hcur]; exact hkx)) hc1 hres1 hti1 hnq1 blk call b g gr don

end

end

end Fl4Proofs.P3
