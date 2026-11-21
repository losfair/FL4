/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch21 (b)): **the cap
fault of `handle_recv` at a `chooseNewThread` mid state with `CurInv` whose
fault handler has a waiting receiver** (`FltRecv`, XTopJointFaultC).
Scripted copies (sch21gen/genf.py, untracked) of the RESUMED fault sends
(XTopJointFaultRecv's `JAtZ.sendFaultIJ` / `sendFaultPJ` / `sendFaultPDJ` /
`faultRecvJ`), not the switch-mid ones: a resumed entry turns into
`chooseNewThread` when the faulting ct blocks (`set_thread_state`), and from
then on the resumed proofs reason about a `chooseNewThread` state; at a `MidC`
state the action is `chooseNewThread` already and stays so. Changes:

* `hres` (resume) → `hcn0` (`chooseNewThread`) and `CurInv σ` as a premise
  (`JAtZ.cur` gives it only outside a pending reschedule);
* the action word: `1` (P1's `chooseNewThread` encoding, `hSR.act`) instead of
  `0`, below every TCB address (`P1.notT_small`), so it names no thread;
* ct's SC word in `Ac` by `JAtZ.curScAc` (sch18's FaultRecvM patch) instead of
  P1's `BoundInv.sact` resumed branch;
* the action after the block / push: `ciSt_actN` / `ps_actN` (a non-resume
  action is kept) instead of `ciSt_act` / `ps_act`. The donation
  (`sendFaultPDJC`) is the resumed one unchanged: `pd_eq` and `pushDonJ`
  already run under `chooseNewThread` (no switch: `test_reschedule`'s
  `reschedule_required` enqueues nothing);
* `JAtZ.faultRecvJC`: `faultRecvJ` from `MidC` (`canBlockCurMC`; `CurInv`
  after `set_fault`, which writes only ct's fault field);
* `JAtZ.faultHypJZC2`: `handle_fault` of a cap fault at every `MidC` state
  (sch18's `faultHypJZM2` split: no handler `noFaultJC`, idle / sending
  endpoint `faultBlockJC`, waiting receiver `faultRecvJC`).
-/
import Fl4Proofs.P3.XTopJointFaultC
import Fl4Proofs.P3.XTopJointFaultRecvM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 64000000 in
/-- **A cap-faulted sender's `send_ipc` to a waiting receiver at `J` where
the sender gets no reply** (XTopJointSendCall's `JAtZ.sendCallIJ` for
`call = false` and a sender with a cap fault, running or restarting: FL4 reads
the fault word where the call flag is false; the transfer is the fault
transfer `do_ipc_transfer_capFJ`).

Original docstring:
(module docstring): the receiver has no reply object, or the caller neither
the grant nor the grant-reply right (`hno`); as `JAtZ.sendRecvJ0` up to the
reply unlink, then the caller `Inactive` on `IRel` (its queue bits clear by
`JAtZ.curBits`: in no ready queue, `hnq`, l4v `ct_not_in_q`, and not in the
release queue, `CurInv.notRel`), the receiver `Running`, `JAtZ` by
`JAtZ.wake_postCI` (the spec's two state changes swapped, `ciSt_swap`), the
tail `JAtZ.sendTailJ`; the spec's outcome `sendIpc_callInactive_eq`. -/
theorem JAtZ.sendFaultIJC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hcn0 : σ.schedulerAction = .chooseNewThread) (hCI : CurInv σ) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hno : (g = false ∧ gr = false) ∨
      ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep = none) :
    endpoint.send_ipc st arI s a blk false badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ).1,
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
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
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
  have SK1 : Ipc.SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((SKeep.um σ1 um2).trans (SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]
  refine WP.spec_bind (Pₘ := fun s3 => ∃ σ3 x3 X3,
      Fl4Spec.NonDet.maybeM (Fl4Spec.replyUnlinkTcb (Z := Unit) d'.bv) rep σ2 = ({((), σ3)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem s3) σ3 ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s3 σ3 ∧
      σ3.kheap t.bv = some (.tcb xt) ∧ σ3.kheap d'.bv = some (.tcb x3) ∧ RbIn x3.tcbState ∧
      tsCode x3.tcbState ≠ 6 ∧ x3.tcbSchedContext = xd.tcbSchedContext ∧
      (∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue) ∧
      P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) ∧
      P1.WritesIn st s s3 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
        (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b) ∧
      CFr e.bv d'.bv σ σ3 ∧ IK d'.bv σ σ3 ∧ Ipc.SKeep σ σ3 ∧ σ3.curThread = σ.curThread ∧
      σ3.schedulerAction = σ.schedulerAction ∧
      P1.SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X3 s3 Q0 R0 ∧
      P1.BoundInv st (P1.Heap.tcbs H) Ac s3 ∧
      P1.XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s3 ∧
      P1.SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s3 ∧
      P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 ∧ P1.ExcT X3 d' ∧
      (d' ∈ X3 ∨ ¬ P1.Blocked (L.mem s3 (P1.stA d'))) ∧
      (∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d')) ?_ ?_
  · cases hrp : rep with
    | none =>
      rw [hrp] at hrep
      have h00 := optRef_none hrep
      simp only [h00, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hrA : L.mem s2 (P1.replyA d') = 0#u64 := by
        show L.mem s2 (tReplyA d') = 0#u64; rw [hrw]; exact h00
      exact ⟨σ2, x2, _, rfl, hR2, hS2', hkt2, hkd2, Or.inl ⟨_, _, _, hst2'⟩,
        by rw [hst2']; simp [tsCode], hxsc, hq2, hW2, footW_trans (footW_of F1) F2, Fr2, IK2, SK2, rfl, rfl, h2, hB2, hX2, hS2'',
        hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl), hX2.noref0 hdta hrA⟩
    | some r =>
      rw [hrp] at hrep hrepR hst2'
      obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
      have hwR := hrepR (by simp)
      have hne0 : (L.mem s (tReplyA d') != 0#u64) = true := by simp [hw0]
      simp only [hne0, ↓reduceIte]
      set w := L.mem s (tReplyA d') with hwdef
      subst hwr
      obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
      have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
      have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
      have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
      have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
      have hb' : xr.replyTcb = some d'.bv := hback_of J.sv hkd e.bv w.bv dd xr (by rw [hstd, hrp]) hkr
      have hX2' := IpcRel.ofSRN hR2 hS2'
      have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
      rw [hrA] at hiR hit
      refine WP.spec_mono (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2' hdT hkd2 hst2' hwR hkr2
          hb' hq2) (reply_unlink_cn hP0 hX2' hdT hwR hkr2))
        (WP.spec_and (P1.ipc.reply_unlink.inv s2 w d' Q0 R0 h2 hdH hX2.1 hsub hiR hit
            (by rw [hds2]; exact P1.blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
          (P1.ipc.reply_unlink.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
            (Es := P1.EH H) s2 w d' h2 hX2 hsub hiR hdH))) ?_
      rintro s3 ⟨⟨⟨e3, hR3, hS3⟩, hW3⟩, ⟨h3, e3', k3, z3⟩, fu3⟩
      have hclr : ∀ r ∈ P1.Heap.replies H, L.mem s2 (P1.rTcbA r) = d' → L.mem s3 (P1.rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, hrA] at b2; rw [← b2]; exact z3
      set x3 : Fl4Spec.Tcb := { x2 with tcbState := .inactive } with hx3
      set σ3a := Notif.updK σ2 w.bv (.reply { xr with replyTcb := none }) with hσ3a
      have hkd3a : σ3a.kheap d'.bv = some (.tcb (x2)) := by simp [σ3a, Ne.symm hwd, hkd2]
      have hct3a : d'.bv ≠ (Notif.updK σ3a d'.bv (.tcb x3)).curThread := hdc
      have e3s : Notif.stsAct (Notif.updK σ3a d'.bv (.tcb x3)) d'.bv = Notif.updK σ3a d'.bv (.tcb x3) :=
        stsAct_ne hct3a
      have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
        hW2.trans1 (hW3.mono fun b hb => Or.inl (cnW_back hks2 (SzKeepC.of Fr2.szKeep) hb))
      refine ⟨_, x3, _, e3, hR3, hS3, ?_, ?_, Or.inr rfl, by simp [x3, tsCode], by simp [x3, hxsc], ?_, hW3',
        footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3), ?_, ?_, ?_, ?_, ?_, h3,
        hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1),
        hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr, hS2''.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3']; exact P1.not_blocked_inactive),
        (hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr).noref hdta (by rw [e3']; exact P1.inactive_ne.1)
          (by rw [e3']; exact P1.inactive_ne.2)⟩
      · rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
      · rw [stsAct_kheap]; simp
      · intro e'' he'' z hz
        rw [stsAct_kheap] at hz
        have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
        have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
        exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
      · exact (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
          (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
      · have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply { xr with replyTcb := none }) hkr2 (fun o0 h => by
          rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
        have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
        exact IK3b.trans (IK.sts _ _ _)
      · exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply { xr with replyTcb := none }) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
          (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
      · rw [e3s]; rfl
      · rw [e3s]; rfl
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
  rintro s3 ⟨σ3, x3, X3, hU, hR3, hS3, hkt3, hkd3, hrb3, hns3, hsc3, hq3, hW3, F3, Fr3, IK3, SK3, hct3, hact3,
    h3, hB3, hX3, hS3', hSg3, hXc3, hx3, hnr3⟩
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3.1
  -- the caller's facts for its `Inactive`
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  obtain ⟨hqb, hrb'⟩ := J.curBits ht hnq hnrT
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := (IpcRel.ofSRN hR3 hS3).2.2.1
  have hna3 : L.actionW s3 ≠ t := by
    obtain ⟨Q, R', hcq, -⟩ := hSR3.lists
    have h := hSR3.act
    rw [hact3, hcn0] at h
    have ha1 : L.actionW s3 = 1#u64 := by unfold P1.LawfulStore.actionW; rw [hcq.cur]; exact h
    rw [ha1]; intro h'; exact P1.notT_small hcq.tcbs (by simp) (h' ▸ ht)
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  have hstsT := WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s3 σ3 hR3 hS3 ht hkt3 hqt3
      (by have := runnable_code hrn; omega) .inactive (by simp [tsCode]) sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl))
      (set_thread_state_sfoot hSR3 ht sched.TS_INACTIVE))
    (WP.spec_and (P1.sts_all s3 t _ Q0 R0 h3 hB3 hX3 hS3' hSg3 htH P1.not_blocked_inactive P1.inactive_ne
        (Or.inr hnbt3) (hX3.noref (hTP t htH) hnrp3 (fun e0 => hnbt3 (Or.inr (Or.inl e0))))
        ⟨fun c hc' p hp hm => absurd hm (h0.notQ htH hqb hc' hp), fun c hc' hm => absurd hm (h0.notR htH hrb' hc'),
          fun e0 => absurd e0 hna3⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s3 t sched.TS_INACTIVE h3 htH))
  -- FL4: no reply pushed, the caller `Inactive`
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧ sched.set_thread_state st s3 t sched.TS_INACTIVE = ok r.1)
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    by_cases hi : (L.mem s (tReplyA d') != 0#u64) = true
    · rw [if_pos hi]
      have hgg : g = false ∧ gr = false := by
        rcases hno with h | hn
        · exact h
        · exfalso
          have hr0 := hn xd hkd _ _ _ hstd
          rw [hr0] at hrep
          have h00 := optRef_none hrep
          rw [h00] at hi
          simp at hi
      obtain ⟨rfl, rfl⟩ := hgg
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
    · rw [if_neg hi]
      exact WP.spec_bind (spec_self hstsT) fun s4 h4 => (WP.spec_ok _).2 ⟨rfl, h4⟩
  rintro ⟨s4, a4⟩ ⟨ha4, hs4⟩
  simp only at ha4 hs4
  subst ha4
  try dsimp only
  have hpost := hstsT
  rw [hs4] at hpost
  obtain ⟨⟨⟨hR4, hS4⟩, hW4⟩, ⟨h4, hB4, hX4, hS4', hSg4, -, k4⟩, fu4⟩ := (WP.spec_ok _).1 hpost
  have hkd4 : (ciSt σ3 t.bv xt).kheap d'.bv = some (.tcb x3) := by rw [ciSt_kh (Ne.symm htd')]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, (ciSt σ3 t.bv xt).kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z (by rw [← ciSt_kh (ciSt_ne hz (fun _ h => by cases h))]; exact hz)
  have hx4 : d' ∈ {y | y ∈ X3 ∧ y ≠ t} ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := by
    rcases hx3 with h | h
    · exact Or.inl ⟨h, Ne.symm htd⟩
    · right
      have e0 : L.mem s4 (P1.stA d') = L.mem s3 (P1.stA d') := by
        rw [P1.stA_eq]
        exact k4.fld d' hdH _ (by simp) (by simp) (by simp) (by simp) (fun e1 => absurd e1 (Ne.symm htd))
      rw [e0]; exact h
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' := fun r hr => by
    rcases k4.rtcb r hr with e0 | ⟨-, e0⟩
    · rw [e0]; exact hnr3 r hr
    · rw [e0]; intro h0'; exact hdta.ne0 (by rw [← h0']; rfl)
  have hks4 : L.ksb s4 = L.ksb s := hW4.1.trans hks3
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4 hns3
      .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q0 R0 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK (ciSt σ3 t.bv xt) d'.bv (.tcb x5)) d'.bv = ciSt σa t.bv xt :=
    ciSt_swap htd' hdc3
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (ciSt σa t.bv xt) := by
    rw [← heq5]; exact hIR0
  have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW3.trans1 (hW4.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks3).1 hb)))))
  have hW5' : P1.WritesIn st s s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q0, R0, h5.congrX (P1.excT_congr (X := {y | y ∈ X3 ∧ y ≠ t}) (fun y hy => hXc3 y hy.1))⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have Fr5 : CFr e.bv d'.bv σ σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σ (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σ σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : Ipc.SKeep σ σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hnqD : NotQueued σ d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rq dm p _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
    · obtain ⟨x, -, -, -, hkx, -, hrx, -, -⟩ := J.inv.rel _ hm
      rw [hkd] at hkx; cases hkx; rw [hstd] at hrx; cases hrx
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σ.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the caller's `Inactive` after the wake (`ciSt_swap`)
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1]; exact hnrT
  have I5' : Inv (ciSt σa t.bv xt) := ciSt_inv hkta I5 hnqT hnrT'
  have B5' : BlockedScActive (ciSt σa t.bv xt) := ciSt_bsa (Fr5.bsa J.bsa)
  have hcn : (ciSt σa t.bv xt).schedulerAction = .chooseNewThread :=
    (ciSt_actN (by rw [act5, hcn0]; intro h; cases h)).trans (act5.trans hcn0)
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle (ciSt σa t.bv xt) :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ciSt_idleOK hidT (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM (ciSt σa t.bv xt) := Or.inl (by rw [hcn]; intro h; cases h)
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX hdT hdth hkd hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have htD := Ju.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D su _ (Endp.setUm σ umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  obtain ⟨V', J5⟩ := Ju.wake_postCI hkta hIR hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) I5' B5' hAI5
    (Or.inl hcn) hrun5 hRR htD hcD ⟨d', hdT, rfl⟩
  -- the tail
  have G := (ciSt_skD (σ := σa) (c := t.bv) (x := xt))
  have hk5 : (ciSt σa t.bv xt).kheap d'.bv = some (.tcb x5) := by
    rw [ciSt_kh (Ne.symm htd'), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ (ciSt σa t.bv xt).releaseQueue := by rw [ciSt_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → (ciSt σa t.bv xt).kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) := by
      rw [← ciSt_kh (ciSt_ne hy (fun _ h => by cases h))]; exact hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ (ciSt σa t.bv xt).idleThread := by
    rw [G.idle, Fr5.sk.idle]
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have htc5 : d'.bv ≠ (ciSt σa t.bv xt).curThread := by rw [G.ct, Fr5.sk.ct]; exact hdc
  have hcond : ¬ ((g = true ∨ gr = true) ∧ rep ≠ none) := by
    rintro ⟨hg, hr⟩
    rcases hno with ⟨rfl, rfl⟩ | hn
    · rcases hg with h | h <;> cases h
    · exact hr (hn xd hkd _ _ _ hstd)
  have hspec := sendIpc_faultInactive_eq (don := don) hk hkd hde htd' hstd blk badge.bv g gr hcond e2 hU hkt3 hkd3
    (by rw [hft]; simp) (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv (ciSt σa t.bv xt) := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

set_option maxHeartbeats 64000000 in
/-- **A cap-faulted sender's `send_ipc` to a waiting receiver at `J` that
pushes a reply without a donation** (XTopJointSendPush's `JAtZ.sendCallPJ`
for `call = false` and a sender with a cap fault, running or restarting;
the transfer `do_ipc_transfer_capFJ`). Original docstring: (module docstring): the caller has the grant or grant-reply right
(`hg`), the receiver a reply object (`hrepn`), and the call does not donate or
the receiver has an SC (`hnd`); as `JAtZ.sendCallIJ` up to the reply unlink,
then `reply_push` on `IRel` (`reply_push_iG`, no donation), P1's
`reply_push.ipc` and `reply_push.nd`, the receiver `Running`, `JAtZ` by
`JAtZ.wake_postGR` at `pushSt` (`ps_swap`), the tail `JAtZ.sendTailJ`; the
spec's outcome `sendIpc_call_eq`. -/
theorem JAtZ.sendFaultPJC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hcn0 : σ.schedulerAction = .chooseNewThread) (hCI : CurInv σ) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr don : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hnd : don = false ∨ ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none) :
    endpoint.send_ipc st arI s a blk false badge g gr don t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ).1,
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
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
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
  have SK1 : Ipc.SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((SKeep.um σ1 um2).trans (SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
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
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
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
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
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
  have Fr3 : CFr e.bv d'.bv σ σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ σ3 := by
    have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : Ipc.SKeep σ σ3 :=
    ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σ d'.bv := by
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
  have ha1 : L.actionW s3 = 1#u64 := by
    have h := hSR3.act
    rw [hact3, hcn0] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha1] at h'; exact P1.notT_small hcq3.tcbs (by simp) (h' ▸ hu)
  have hcw3 : L.curW s3 = t := by
    have h : (nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σ.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun _ => by
    obtain ⟨e1, hA⟩ := J.curScAc hCI hti
    obtain ⟨Q', R'', hcq0, hs0⟩ := J.xtop.fin.1.1.1.lists
    have hcw : L.curW s = t := by
      apply P1.eq_of_bv
      rw [← hct, hs0.curThread]
      unfold P1.LawfulStore.curW nodeW; rw [hcq0.cur]
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hct, hkt] at hkc; cases hkc
    have h0 : L.mem s3 (P1.scA t) = L.mem s (P1.scA t) := by
      obtain ⟨x', hk', -, -, hscw, -⟩ := hs0.tcb t ht
      obtain ⟨x'', hk'', -, -, hscw', -⟩ := hs3.tcb t ht
      rw [hkt] at hk'; cases hk'
      rw [hkt3] at hk''; cases hk''
      have e2 := hscw.symm.trans hcs
      have hv0 : L.mem s (P1.scA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at e2; cases e2
      exact optRef_some_eq ((hscw'.symm.trans hcs).trans (e2.symm.trans (Notif.optRef_ne hv0)))
    rw [h0, ← hcw, e1]; exact hA
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the receiver's SC: no donation
  have hndF : don = true → x3.tcbSchedContext = none → False := fun hdon hx0 => by
    rcases hnd with h | h
    · rw [h] at hdon; cases hdon
    · exact h xd hkd (by rw [← hsc3]; exact hx0)
  obtain ⟨xd3, hkd3', hdsc⟩ := hSM d' hdT
  rw [hkd3] at hkd3'; cases hkd3'
  have hnd1 : don = false ∨ L.mem s3 (P1.scA d') ≠ 0#u64 := by
    cases don
    · exact Or.inl rfl
    · right; intro h0; exact hndF rfl (by rw [hdsc, h0, optRef_zero])
  -- the push on `IRel`, at P1
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  have hPush : ipc.reply_push st arI s3 a t d' w don ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1 ⦄ := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := don) (P := fun s' σ' => σ' = pushSt σ3 t.bv w.bv xr3 xt ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hdon _ _ _ _ _ _ _ hx0 => (hndF hdon hx0).elim))
      (P1.ipc.reply_push.ipc hAT s3 a t d' w don Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hqbD hrbD (hna3 d' hdT) (hiw3 d' hdT hid) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a t d' w don h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        (hna3 t ht) (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J.zH.1 d' hdT)
        (Ne.symm htd) hcA hnd1)) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, hb2, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hb2, hf, hsb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv don σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1) ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    rcases hg with rfl | rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true]; exact hPush
    · cases g <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self_iff_true, if_true] <;> exact hPush
  rintro ⟨s4, a4⟩ ⟨ha4, hpush, hR4, hS4, ⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4', hSg4⟩, hst4, fu4, hsb4⟩
  simp only at ha4 hpush hR4 hS4 h4 hB4 hX4 hS4' hSg4 hst4 fu4 hsb4 ⊢
  subst ha4
  try dsimp only
  have hW4 : P1.WritesIn st s3 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s3 σ3) := by
    have h := set_blocked_on_reply_cn (N := Z.N) (C := Z.C) (E := Z.E) hP hSR3 ht hwR hw1
    rw [hsb4, WP.spec_ok] at h; exact h
  have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW3'.trans1 (hW4.mono fun b hb => Or.inl (cnW_back hks3 (SzKeepC.of Fr3.szKeep) hb))
  have hks4 : L.ksb s4 = L.ksb s := hW4'.1
  set σ4 := pushSt σ3 t.bv w.bv xr3 xt with hσ4
  have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z ((ps_oth hkt3 hkr3 hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hz)
  have hdH : d' ∈ P1.Heap.tcbs H := J.zH.1 d' hdT
  have hst4d : L.mem s4 (P1.stA d') = sched.TS_INACTIVE := by rw [hst4 d' hdH (Ne.symm htd)]; exact e3'
  have hx4 : d' ∈ (∅ : Set U64) ∨ ¬ P1.Blocked (L.mem s4 (P1.stA d')) := Or.inr (by rw [hst4d]; exact P1.not_blocked_inactive)
  have hnr4 : ∀ r ∈ P1.Heap.replies H, L.mem s4 (P1.rTcbA r) ≠ d' :=
    hX4.noref hdta (by rw [hst4d]; exact P1.inactive_ne.1) (by rw [hst4d]; exact P1.inactive_ne.2)
  -- the receiver runs
  refine WP.spec_bind (WP.spec_and (WP.spec_and (set_thread_state_c hH hP0 hP s4 _ hR4 hS4 hdT hkd4 hq4
      (by simp [x3, tsCode]) .running (by simp [tsCode]) sched.TS_RUNNING (by unfold sched.TS_RUNNING; rfl))
      (set_thread_state_sfoot (IpcRel.ofSRN hR4 hS4).2.2.1 hdT sched.TS_RUNNING))
    (WP.spec_and (P1.sts_all s4 d' _ Q4 R4 h4 hB4 hX4 hS4' hSg4 hdH P1.not_blocked_running P1.running_ne hx4 hnr4
        ⟨fun _ _ _ _ _ => P1.runnable_running, fun _ _ _ => P1.runnable_running, fun _ => P1.runnable_running⟩)
      (P1.sched.set_thread_state.kw (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H)
        (Es := P1.EH H) s4 d' sched.TS_RUNNING h4 hdH))) ?_
  rintro s5 ⟨⟨⟨hR5, hS5⟩, hW5⟩, ⟨h5, hB5, hX5, hS5', hSg5, -, -⟩, fu5⟩
  set x5 : Fl4Spec.Tcb := { x3 with tcbState := .running } with hx5
  set σa := Notif.stsAct (Notif.updK σ3 d'.bv (.tcb x5)) d'.bv with hσa
  have hdc3 : d'.bv ≠ σ3.curThread := by rw [hct3]; exact hdc
  have heq5 : Notif.stsAct (Notif.updK σ4 d'.bv (.tcb x5)) d'.bv = pushSt σa t.bv w.bv xr3 xt :=
    ps_swap htd' hwd hdc3
  have hIR0 := IpcRel.ofSRN hR5 hS5
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 (pushSt σa t.bv w.bv xr3 xt) := by
    rw [← heq5]; exact hIR0
  have hW5' : P1.WritesIn st s s5 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb)))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX P1.empty_congr⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have hrb3 : RbIn x3.tcbState := Or.inr rfl
  have Fr5 : CFr e.bv d'.bv σ σa := Fr3.trans (CFr.stsRun hkd3 hrb3)
  have IK5a : IK d'.bv σ (Notif.updK σ3 d'.bv (.tcb x5)) := IK3.trans (IK.updSelf (y := x5) hkd3 rfl)
  have IK5 : IK d'.bv σ σa := IK5a.trans (IK.sts _ _ _)
  have SK5 : Ipc.SKeep σ σa := (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3, by cases h; rfl⟩)
    (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hrib : RelIfBound σa d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σa := ((J.inv.toBut d'.bv).ik hnqD IK5).1.inv fun _ _ _ => hrib
  have act5 : σa.schedulerAction = σ.schedulerAction := by
    rw [hσa, stsAct_ne (by show d'.bv ≠ σ3.curThread; exact hdc3)]; exact hact3
  -- the push after the wake (`ps_swap`)
  have hkta : σa.kheap t.bv = some (.tcb xt) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, htd', hkt3]
  have hkwa : σa.kheap w.bv = some (.reply xr3) := by rw [hσa, stsAct_kheap]; simp [Notif.updK, hwd, hkr3]
  have hnqT : ∀ dm p, t.bv ∉ σa.readyQueues dm p := by rw [IK5.2.1]; exact hnq
  have hnrT' : t.bv ∉ σa.releaseQueue := by rw [IK5.2.2.1]; exact hnrT
  set σ' := pushSt σa t.bv w.bv xr3 xt with hσ'
  have I5' : Inv σ' := ps_inv hkta hkwa hwt I5 hnqT hnrT'
  -- an SC bound to the caller is the current SC, active
  have hscA : ∀ p y n, σa.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σ.kheap p = some (.schedContext y n) := SK5.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hct, hkt] at hkc; cases hkc
    have e1 : σ.curSc = q.bv := Option.some.inj (hcs.symm.trans hxs)
    rw [← e1] at hp0
    exact hCI.active (J.curSc_ne_idle hCI hti) y n hp0
  have B5' : BlockedScActive σ' := ps_bsa hkta hkwa hwt hscA (Fr5.bsa J.bsa)
  have hcn : σ'.schedulerAction = .chooseNewThread :=
    (ps_actN (by rw [act5, hcn0]; intro h; cases h)).trans (act5.trans hcn0)
  have hidT : σa.idleThread ≠ t.bv := by rw [Fr5.sk.idle, ← hct]; exact fun e0 => hti e0.symm
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => (by rw [hcn] at hu; cases hu), ps_idleOK hkta hkwa hwt hidT (Fr5.idleOK J.act.2)⟩
  have hrun5 : CurRunM σ' := Or.inl (by rw [hcn]; intro h; cases h)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hkq : ∀ q ∈ D, σ'.kheap q.bv = σa.kheap q.bv := fun q hq => ps_ko (hcD q hq) (hwD q hq)
  obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX hdT hdth hkd hW5' hfoot
  have hIu := Ju.xtop.irelK Ju.ks Ju.buf
  have hRR : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D su _ (Endp.setUm σ umu) Ju q' hq'' xr d'.bv xd hx'
      hxt' hkd (by rw [hstd]; rfl)
  have hF : IFrame (L := L) Z.th su s5 := IRel.iframe_of hIu hWu fun b hb => CnW.oobj hIu.2.2.1 hb
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σa.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hwt h1 h2
  obtain ⟨V', J5⟩ := Ju.wake_postGR hIR hF hWu hblk hFu (DWFr.ofUm (DWFr.ofCFr Fr5) umu) ps_skD
    (ps_ksub hkta hkwa hwt) (ps_szKeep hkta hkwa hwt) (ps_ykeep hkta hkwa hwt) (ps_mcpKeep hkta hkwa hwt)
    (ps_bufKeep hkta hkwa hwt) (fun d _ h => ps_recvB hkta hkwa hwt h) (ps_ksz hkta hkwa hwt)
    (ps_kback hkta hkwa hwt) (ps_ipcFr hkta hkwa hwt) (ps_ck hkta hkwa hwt) (fun d _ h => ps_free hkta hkwa hwt h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 (Or.inl hcn) hrun5 (ps_own hkta hkwa hwt ((DWFr.ofCFr Fr5).own ⟨d', hdT, rfl⟩ J.own))
    (ps_off hkta hkwa hwt ((DWFr.ofCFr Fr5).off J.off)) (ps_nsc hkta hkwa hwt ((DWFr.ofCFr Fr5).nsc J.nsc))
    (ps_isorted hkta hkwa hwt ((DWFr.ofCFr Fr5).isorted J.isorted)) hRR htD
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb x5) := by
    rw [ps_ko (Ne.symm htd') (Ne.symm hwd), hσa, stsAct_kheap]; simp
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [ps_rel, SK5.1]; exact hnqD.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ'.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya : σa.kheap p = some (.schedContext y n) :=
      (ho (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
    have hy0 := SK5.2.2.2 p y n hya
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J.inv.back _ _ _ hkd hp'
    rw [hy0] at hky'; cases hky'
    exact J.bsa.tcb p y n d'.bv xd hy0 hyt hkd (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle, Fr5.sk.idle]
    exact hid
  have htc5 : d'.bv ≠ σ'.curThread := by
    rw [(ps_skD (σ := σa) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct, Fr5.sk.ct]; exact hdc
  have hspec := sendIpc_faultPush_eq (don := don) hk hkd hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpush hkd4 (by rw [hft]; simp)
    (t := t.bv)
  have hspec' : Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr don t.bv e.bv σ =
      Endp.specWakeTailE d'.bv σ' := by
    rw [hspec]; exact congrArg _ heq5
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec', h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

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
theorem JAtZ.sendFaultPDJC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t : U64} (ht : t ∈ Z.T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hrn : Fl4Spec.runnable xt.tcbState = true) {cf : Fl4Spec.ObjRef} {rp : Bool} {lf : Fl4Spec.LookupFailure}
    (hft : xt.tcbFault = some (.capFault cf rp lf)) (hct : σ.curThread = t.bv)
    (hcn0 : σ.schedulerAction = .chooseNewThread) (hCI : CurInv σ) (hti : σ.curThread ≠ σ.idleThread)
    (hnq : ∀ dm p, t.bv ∉ σ.readyQueues dm p)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hk : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (blk : Bool) (badge : U64) (g gr : Bool)
    (hg : g = true ∨ gr = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none)
    (hxdn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext = none) :
    endpoint.send_ipc st arI s a blk false badge g gr true t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) blk false badge.bv g gr true t.bv e.bv σ).1,
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
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
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
  have SK1 : Ipc.SKeep σ σ1 := SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h) (fun _ _ h => by cases h)
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (J.xferH).1 (EpStep.ep hk)
  -- the transfer
  have hdth : Z.th d' = some .tcb := by
    obtain ⟨⟨⟨G0, hB0'⟩, -⟩, -⟩ := hS0.1.1
    exact Ipc.RelTopB.tcbT hB0' hkd
  have hUd := J.rbufU hdT hdth hkd
  refine WP.spec_bind (xferFaultStepJ hP0 hP (hH.epHyps hP0) s1 a σ1 hR1 hS1 hOK1
    (bufCover_epStep (J.xferH).2.1 (EpStep.ep hk)) ht hdT htd hkt1 hkd1 hft e badge g
    hTP hdH h1 hB1 hX1 hS1' hSg1 (fun b hb => ⟨(hUd b hb).1.ksb hW1.1, (hUd b hb).2⟩)) ?_
  rintro s2 ⟨x2, um2, e2, hx2, hR2, hS2, hA2, w2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Endp.setUm σ1 um2) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by simp [σ2, htd', hkt1]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hN2 := ntfn_lift_rcv hP0.toC hS1.2 hR2 hdT hA2 (fun p hp => by simp [σ2, hp])
    hkd1 hkd2 (by rw [hx2])
  have hS2' : SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
      (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s2 σ2 := ⟨hS2.1, hN2⟩
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    simp [σ2, Ne.symm hde, hk1e]
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    exact hq1 e'' he'' z (by simpa [σ2, Ne.symm hne] using hz)
  have hrw : L.mem s2 (tReplyA d') = L.mem s (tReplyA d') := by
    rw [hA2 _ (a_reply hda).1 ⟨?_, ?_⟩, hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
    · rintro ⟨r', hr'⟩
      rw [val_reply hda, regA_val hda (regIdx_lt r')] at hr'; have := regIdx_lt r'; omega
    · rintro ⟨wp, hwp, e'⟩
      have h1' := hP.bt wp hwp d' hdT
      have h2' := val_reply hda
      rw [← e'] at h1'; omega
  have hW2 : P1.WritesIn st s s2 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
    (hW1.mono fun b hb => Or.inl hb).trans1 (w2.mono fun b hb => by
    rcases hb with (⟨y, hy, K, h1', h2', -, eb⟩ | hb) | hb
    · have hyT : y ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inl (Or.inr ⟨y, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩))
      rw [eb]; exact tfield_val (hP.tcb y hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr hb)
  have F2 : P1.WritesIn st s1 s2 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1 b ∨ RcvBufW xd b) :=
    w2.mono fun b hb => by
      rcases hb with (⟨y, hy, K, h1', h2', h3', eb⟩ | hb) | hb
      · exact Or.inl (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, eb⟩)
      · exact absurd hb (Set.notMem_empty _)
      · exact Or.inr hb
  have Fr2 : CFr e.bv d'.bv σ σ2 := (Fr1.trans (CFr.um _ _ σ1 um2)).trans (CFr.upd (σ := Endp.setUm σ1 um2) hkd1
    (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl, by rw [hx2],
    Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ σ2 := IK1.trans ((IK.um _ σ1 um2).trans (IK.updSelf (σ := Endp.setUm σ1 um2) hkd1 hxsc))
  have SK2 : Ipc.SKeep σ σ2 := SK1.trans ((SKeep.um σ1 um2).trans (SKeep.updK (σ := Endp.setUm σ1 um2) (p := d'.bv)
    (o := .tcb x2) (fun y h => ⟨xd, hkd1, by cases h; exact hxsc.symm⟩) (fun _ _ h => by cases h)))
  have hks2 : L.ksb s2 = L.ksb s := hW2.1
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
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by simp [σ2, σ1, hwe, hwd, hkr]
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
  have hW3' : P1.WritesIn st s s3 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
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
  have Fr3 : CFr e.bv d'.bv σ σ3 := (Fr2.trans (CFr.upd hkr2 (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
    (CFr.stsIn hkd3a (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ σ3 := by
    have IK3a : IK d'.bv σ σ3a := IK2.trans (IK.updOther (o' := .reply xr3) hkr2 (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    have IK3b : IK d'.bv σ (Notif.updK σ3a d'.bv (.tcb x3)) := IK3a.trans (IK.updSelf (y := x3) hkd3a rfl)
    exact IK3b.trans (IK.sts _ _ _)
  have SK3 : Ipc.SKeep σ σ3 :=
    ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h) (fun _ _ h => by cases h))).trans
      (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3a, by cases h; rfl⟩) (fun _ _ h => by cases h))).trans
      (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have hnr3 : ∀ r ∈ P1.Heap.replies H, L.mem s3 (P1.rTcbA r) ≠ d' :=
    hX3.noref hdta (by rw [e3']; exact P1.inactive_ne.1) (by rw [e3']; exact P1.inactive_ne.2)
  have F3 := footW_trans (footW_trans (footW_of F1) F2) (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = fl4_abi.consts.fault.CapFault := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; rw [hfr.1]; unfold fl4_abi.consts.fault.CapFault; rfl
  have hks3 : L.ksb s3 = L.ksb s := hW3'.1
  -- the caller's and the receiver's words at `s3`
  have hnrT : t.bv ∉ σ.releaseQueue := by rw [← hct]; exact hCI.notRel
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD : NotQueued σ d'.bv := by
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
  have ha1 : L.actionW s3 = 1#u64 := by
    have h := hSR3.act
    rw [hact3, hcn0] at h
    unfold P1.LawfulStore.actionW; rw [hcq3.cur]; exact h
  have hna3 : ∀ u ∈ Z.T, L.actionW s3 ≠ u := fun u hu h' => by
    rw [ha1] at h'; exact P1.notT_small hcq3.tcbs (by simp) (h' ▸ hu)
  have hcw3 : L.curW s3 = t := by
    have h : (nodeW st s3 Z.c layout.node.CUR_THREAD).bv = t.bv := by rw [← hs3.curThread, hct3, hct]
    unfold P1.LawfulStore.curW; rw [hcq3.cur]; exact P1.eq_of_bv h
  have hidl3 : σ3.idleThread = σ.idleThread := Fr3.sk.idle
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := by rw [← hct]; exact hti
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x, hkx, -, hxs, -⟩ := J.act.2
    rw [← h, hkd] at hkx; cases hkx; rw [hstd] at hxs; cases hxs
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun _ => by
    obtain ⟨e1, hA⟩ := J.curScAc hCI hti
    obtain ⟨Q', R'', hcq0, hs0⟩ := J.xtop.fin.1.1.1.lists
    have hcw : L.curW s = t := by
      apply P1.eq_of_bv
      rw [← hct, hs0.curThread]
      unfold P1.LawfulStore.curW nodeW; rw [hcq0.cur]
    obtain ⟨xc, hkc, hcs, -⟩ := hCI.tcb
    rw [hct, hkt] at hkc; cases hkc
    have h0 : L.mem s3 (P1.scA t) = L.mem s (P1.scA t) := by
      obtain ⟨x', hk', -, -, hscw, -⟩ := hs0.tcb t ht
      obtain ⟨x'', hk'', -, -, hscw', -⟩ := hs3.tcb t ht
      rw [hkt] at hk'; cases hk'
      rw [hkt3] at hk''; cases hk''
      have e2 := hscw.symm.trans hcs
      have hv0 : L.mem s (P1.scA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at e2; cases e2
      exact optRef_some_eq ((hscw'.symm.trans hcs).trans (e2.symm.trans (Notif.optRef_ne hv0)))
    rw [h0, ← hcw, e1]; exact hA
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
  have hrelσ : Fl4Spec.scActive y = true → released σ y := fun ha =>
    J.inv.rd t.bv xt hkt (Or.inl hrn) xt sc.bv y n hkt hcs hky0 ha hnrT
  have hse : sc.bv ≠ e.bv := kheap_ne hky0 hk (fun _ h1 h2 => by subst h1; cases h2)
  have hsd : sc.bv ≠ d'.bv := kheap_ne hky0 hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hsw : sc.bv ≠ w.bv := kheap_ne hky0 hkr (fun _ h1 h2 => by subst h1; cases h2)
  have hst : sc.bv ≠ t.bv := kheap_ne hky0 hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hky2 : σ2.kheap sc.bv = some (.schedContext y n) := by simp [σ2, σ1, hsd, hse, hky0]
  have hky3 : σ3.kheap sc.bv = some (.schedContext y n) := by rw [stsAct_kheap]; simp [σ3a, hsd, hsw, hky2]
  have hsw3 : L.mem s3 (P1.scA t) = sc := by
    obtain ⟨x', hk', -, -, hscw, -⟩ := hs3.tcb t ht
    rw [hkt3] at hk'; cases hk'
    exact optRef_some_eq (hscw.symm.trans hcs)
  have hxdn3 : x3.tcbSchedContext = none := by rw [hsc3]; exact hxdn xd hkd
  -- the J state after the block
  have hcD : ∀ q ∈ D, q.bv ≠ t.bv := J.notDead ht hkt (by have := runnable_code hrn; omega)
  have htD := J.not_dead_of_st hdT hkd (by rw [hstd]; simp [tsCode])
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s (Endp.rTcbA w) = 0#u64 := (J.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := hR.reply w hwR
    rw [hkr] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s (rNextA q') = 0#u64 ∧ L.mem s (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D s _ σ J q' hq'' xr d'.bv xd hx' hxt' hkd
      (by rw [hstd]; rfl)
  have hrib3 : RelIfBound σ3 d'.bv :=
    Ipc.RelIfBound.of_keep (J.inv.rd d'.bv xd hkd (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK3
  have I3 : Inv σ3 := ((J.inv.toBut d'.bv).ik hnqD IK3).1.inv fun _ _ _ => hrib3
  have hscA3 : ∀ p y n, σ3.kheap p = some (.schedContext y n) → y.scTcb = some t.bv →
      Fl4Spec.scActive y = true := by
    intro p y n hp hyt
    have hp0 : σ.kheap p = some (.schedContext y n) := SK3.2.2.2 _ _ _ hp
    obtain ⟨q, hqC, eq⟩ := J.obj.sc p y n hp0
    subst eq
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hq0 := J.c0 q hqC
    have hqS : q ∈ P1.Heap.scs H := ⟨_, (hJ.sc q y n hq0 hp0).2⟩
    have hS := J.xtop.fin.1.1.1
    obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS J.blk.2.2.1 J.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
    rw [hkt] at hku; cases hku
    have e1 : σ.curSc = q.bv := by rw [← esc]; exact Option.some.inj (hcs.symm.trans hxs)
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
  have hcnP : σP.schedulerAction = .chooseNewThread := (ps_actN (by rw [hact3, hcn0]; intro h; cases h)).trans (hact3.trans hcn0)
  have hnsw : ∀ u, σP.schedulerAction ≠ .switchThread u := fun u e0 => by rw [hcnP] at e0; cases e0
  have hctP : σP.curThread = t.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).ct.trans (hct3.trans hct)
  have hcscP : σP.curSc = sc.bv :=
    (ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).csc.trans (Fr3.sk.csc.trans esc.symm)
  have hnqtP : NotQueued σP t.bv := ⟨by rw [ps_rq]; exact hnqT3.1, by rw [ps_rel]; exact hnqT3.2⟩
  have hnqdP : NotQueued σP d'.bv := ⟨by rw [ps_rq]; exact hnqD3.1, by rw [ps_rel]; exact hnqD3.2⟩
  have hhP := J.stackHead hsC hky0 (hRR w hwR xr hkr hb').1
  have hhP' : ∀ h l, y.scReplies = h :: l → h ≠ sc.bv ∧ h ≠ w.bv ∧ ∃ x, σP.kheap h = some (.reply x) := by
    intro h l hr
    obtain ⟨h1, h2, x, hx⟩ := hhP h l hr
    refine ⟨h1, h2, x, ?_⟩
    have ht' : h ≠ t.bv := fun e0 => by rw [e0, hkt] at hx; cases hx
    have hd' : h ≠ d'.bv := fun e0 => by rw [e0, hkd] at hx; cases hx
    have he' : h ≠ e.bv := fun e0 => by rw [e0, hk] at hx; cases hx
    rw [ps_ko ht' h2, stsAct_kheap]
    simp [σ3a, hd', h2, σ2, σ1, he', hx]
  have hpdE := pd_eq hktP hkdP hkyP hkwP (Ne.symm hsw) hhP' hyt htd' hst hsd hwt hwd
    hctP.symm hnqtP hnsw
  have hpushE : Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σD)}, False) := by
    rw [replyPush_don_eq hkt3 hkd3 hkr3 hwt hcs hxdn3]; exact hpdE
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  -- the push: link and block (`J` again), then the donation at `J`
  have hPush : ipc.reply_push st arI s3 a t d' w true ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv true σ3 = ({((), σ')}, False) ∧
      (σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D r.1 a σ') ⦄ := by
    refine reply_push_iC (don := true) (P := fun s' σ' => σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D s' a σ')
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
      have hW4' : P1.WritesIn st s s4 (fun b => CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ b ∨ RcvBufW xd b) :=
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
      have hfoot4 : P1.WritesIn st s s4 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
          (P1.Heap.scBits H) (P1.EH H) s b ∨ RcvBufW xd b) :=
        footW_trans (footW_trans F3 (footW_of f1)) (footW_of f4)
      have hIR4 := IpcRel.ofSRN hR4 hS4
      obtain ⟨su, umu, Ju, hWu, hFu, -, -⟩ := J.bufRebaseX hdT hdth hkd hW4' hfoot4
      have hIu := Ju.xtop.irelK Ju.ks Ju.buf
      have hRRu : ∀ q' ∈ Z.R, ∀ xr, (Endp.setUm σ umu).kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
          Detached Z.C Lst q' ∧ L.mem su (rNextA q') = 0#u64 ∧ L.mem su (rPrevA q') = 0#u64 :=
        fun q' hq'' xr hx' hxt' => recvReplyHyp_holds Z Ac Lst D su _ (Endp.setUm σ umu) Ju q' hq'' xr d'.bv xd hx'
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
      obtain ⟨V', J4⟩ := Ju.wake_postGR hIR4 hF4 hWu hblk4 hFu (DWFr.ofUm (DWFr.ofCFr Fr3) umu) ps_skD
        (ps_ksub hkt3 hkr3 hwt) (ps_szKeep hkt3 hkr3 hwt) (ps_ykeep hkt3 hkr3 hwt) (ps_mcpKeep hkt3 hkr3 hwt)
        (ps_bufKeep hkt3 hkr3 hwt) (fun d _ h => ps_recvB hkt3 hkr3 hwt h) (ps_ksz hkt3 hkr3 hwt)
        (ps_kback hkt3 hkr3 hwt) (ps_ipcFr hkt3 hkr3 hwt) (ps_ck hkt3 hkr3 hwt) (fun d _ h => ps_free hkt3 hkr3 hwt h)
        (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
        I4 B4 hAI4 (Or.inl hcnP) (Or.inl (by rw [hcnP]; intro h; cases h))
        (ps_own hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).own ⟨d', hdT, rfl⟩ J.own))
        (ps_off hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).off J.off)) (ps_nsc hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).nsc J.nsc))
        (ps_isorted hkt3 hkr3 hwt ((DWFr.ofCFr Fr3).isorted J.isorted)) hRRu htD
      -- the reply's links at the block
      obtain ⟨hdet, hn0, hp0⟩ := hRRu w hwR xr hkr hb'
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
      (σ' = σD → ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D r.1 a σ'))
    ?_ ?_
  · refine WP.spec_bind (Endp.obj.Tcb.fault_type.spec s3 t) ?_
    rintro i1 rfl
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.CapFault fl4_abi.consts.fault.NullFault; decide)]
    rcases hg with rfl | rfl
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
  have htmD : σD.curTime = σ.curTime := (@pd_tm σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
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
    rw [show σD.releaseQueue = σ.releaseQueue from (@pd_rel σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
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
    rw [show σD.idleThread = σ.idleThread from (@pd_idle σP t.bv d'.bv sc.bv w.bv xtP x3 xwP y n).trans
      ((ps_skD (σ := σ3) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xt)).idle.trans Fr3.sk.idle)]
    exact hid
  have htc6 : d'.bv ≠ (stsAct (updK σD d'.bv (.tcb x6)) d'.bv).curThread := by
    rw [e6]; exact hdcD
  have hspec := sendIpc_faultPush_eq (don := true) hk hkd hde hstd blk badge.bv g gr hg e2 hU hkt3 hkd3 hpushE hk5 (by rw [hft]; simp)
    (t := t.bv)
  refine WP.spec_mono (J6.sendTailJ hdT hk6 rfl hnr6 hact6 hti6 htc6) ?_
  rintro ⟨s7, a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  exact ⟨((), σ7), by rw [hspec, h7]; exact Set.mem_singleton _, ⟨_, _, _, _, _, _, J7⟩⟩

set_option maxHeartbeats 64000000 in
/-- **`handle_fault` with an endpoint handler and a waiting receiver at `J`,
with or without a receive buffer** (module docstring): XTopJointFaultEp's
`JAtZ.faultBlockJ` up to the handler cap, then `set_fault` at `J`
(`JAtZ.setFaultCapJ`) and the send to the receiver: `JAtZ.sendFaultIJ` (no
reply right or no reply object: the sender `Inactive`), `JAtZ.sendFaultPJ`
(the reply pushed, no donation: `can_donate` false or the receiver with an
SC), `JAtZ.sendFaultPDJ` (the reply pushed and the sender's SC donated). -/
theorem JAtZ.faultRecvJC (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hni : MidC σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {ptr bdg : U64} {sd rv g gr : Bool}
    (hep : capAt (L.mem s) (cslotAddr (ct.bv, Fl4Spec.tcbCnodeIndex 3)) = ok (.Endpoint ptr bdg sd rv g gr))
    {d : U64} {q : List Fl4Spec.ObjRef} (hkq : σ.kheap ptr.bv = some (.endpoint (.recvEP (d.bv :: q))))
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩ := hf
  obtain ⟨⟨lt, l0, l1⟩, he, -⟩ := spec_exists (encode_lfRel hlf)
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have hrn : Fl4Spec.runnable x.tcbState = true := hni.run x (by rw [hcur]; exact hk)
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := J.xtop.fin.1.1.1
  have hT : TcbPlaced Z.T := hP0.e.tcb
  have hTH : P1.TcbPlaced (P1.Heap.tcbs H) := by rw [← J.tcbs_eq.1]; exact hP0.e.tcb
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨Q, R, hcq, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hcq.cur] at h; exact h
  have ht : ct ∈ Z.T := by rw [hct']; exact hcq.curT
  have hta := hP0.e.tcb ct ht
  have htH : ct ∈ P1.Heap.tcbs H := J.zH.1 ct ht
  have htD : ct ∉ D := fun h => J.notDead ht hk (by have := runnable_code hrn; omega) ct h rfl
  have hnq' : ∀ d p, ct.bv ∉ σ.readyQueues d p := by rw [← hcur]; exact hnq
  have hC : CurInv σ := hni.2.2.2
  have hnr : ct.bv ∉ σ.releaseQueue := by rw [← hcur]; exact hC.notRel
  have hti : σ.curThread ≠ σ.idleThread := hni.1
  have hidt : σ.idleThread ≠ ct.bv := fun e => hti (by rw [hcur, e])
  -- the handler cap, its endpoint
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have e1 : c1 = .Endpoint ptr bdg sd rv g gr := by rw [hep] at hc1; simpa using hc1.symm
  subst e1
  have habs := hcr.2
  simp only [absCap] at habs
  have hfh : x.tcbFaultHandler = .endpointCap ptr.bv bdg.bv (rightsOf sd rv g gr) := habs.symm
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : ptr ∈ Z.E := J.slotE hAS hep
  obtain ⟨xe, hke, -⟩ := hI.1.ep ptr hpE
  have hpt : ptr.bv ≠ ct.bv := fun e => by rw [e, hk] at hke; cases hke
  have hHe : H ptr = some .ep := J.zH.2.1 ptr hpE
  have hfit := J.kern.heap.fits ptr _ hHe
  simp only [P1.HKind.bits] at hfit
  have hcov := J.cover_cap (P1.WritesIn.refl s _) hAS.isSlot hep (fun h => by cases h) (ok_inj (phys_eq _).symm) rfl
    (range_ep ptr bdg sd rv g gr hfit) fun k hk' => by
      rw [hHe] at hk'; cases hk'
      exact ⟨by simp only [P1.HKind.bits]; omega, fun z h => by cases h⟩
  have hcbP : P1.CanBlock st (P1.Heap.tcbs H) Ac s ct := J.canBlockCurMC ht hcur hk hrn hti hnr hni hnq
  -- the spec's donation flag is FL4's
  obtain ⟨xt6, hkt6, -, -, hsct6, -⟩ := hs.tcb ct ht
  rw [hk] at hkt6; cases hkt6
  have hdon : (L.mem s (scA ct) != 0#u64) = decide (x.tcbSchedContext ≠ none) := by
    rw [hsct6]
    by_cases h0 : L.mem s (scA ct) = 0#u64
    · simp [h0, Notif.optRef]
    · simp [h0, Notif.optRef]
  -- `handle_fault`: the handler cap
  unfold faults.handle_fault
  rw [tcb_slot_fault]
  apply ok_bind_spec
  rw [slot_cap_eq, hep]
  apply ok_bind_spec
  step with Fl4Proofs.P1.obj.Tcb.sc.spec as ⟨i, hi⟩
  subst hi
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => r.1 = true ∧
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault a0.bv rp lf') σ).1,
      RelTopM (L := L) r.2.1 z.2 ∧ JAt (L := L) arI AR r.2.1 r.2.2 z.2) ?_ ?_
  swap
  · rintro ⟨b0, s2, a2⟩ ⟨hb, hr0⟩
    simp only at hb hr0
    subst hb
    exact (WP.spec_ok _).2 hr0
  unfold faults.send_fault_ipc
  dsimp only
  -- `set_fault`
  set f' : Fl4Spec.Fault := .capFault a0.bv rp lf' with hf'
  set x2 : Fl4Spec.Tcb := { x with tcbFault := some f' } with hx2
  set σf := updK σ ct.bv (.tcb x2) with hσf
  -- `set_fault` at `J`
  refine WP.spec_bind (J.setFaultCapJ ht hk (fun e0 d0 h => by
      have := runnable_code hrn; rw [h] at this; simp [tsCode] at this) hcbP ⟨a0, rp, lf, lf', rfl, rfl, hlf⟩) ?_
  rintro s7 ⟨V, J7, -⟩
  have hkf : σf.kheap ct.bv = some (.tcb x2) := by simp [hσf, updK]
  have hkfp : ∀ q, q ≠ ct.bv → σf.kheap q = σ.kheap q := by
    intro q hq'; rw [hσf]; simp only [updK, Function.update_of_ne hq']
  have hkef : σf.kheap ptr.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkfp _ hpt]; exact hkq
  have hnb0 : tsCode x.tcbState ≠ 3 ∧ tsCode x.tcbState ≠ 4 := by
    have := runnable_code hrn; omega
  have htq : ct.bv ∉ (Fl4Spec.Endpoint.recvEP (d.bv :: q)).epQueue :=
    Endp.not_queued hI.1.toE ht hk hnb0 ptr hpE _ hkq
  have hdc : d.bv ≠ ct.bv := fun e0 => htq (by rw [← e0]; simp [Fl4Spec.Endpoint.epQueue])
  have hCf : CurInv σf := by
    obtain ⟨⟨xc, hkc, hcs, hnb⟩, ⟨y0, n0, hky⟩, hact, hnrl⟩ := hC
    rw [hcur, hk] at hkc; cases hkc
    have hsc : σ.curSc ≠ ct.bv := fun e => by rw [e, hk] at hky; cases hky
    exact ⟨⟨x2, by rw [show σf.curThread = ct.bv from hcur]; exact hkf, hcs, hnb⟩, ⟨y0, n0, (hkfp _ hsc).trans hky⟩,
      fun hne y n hy => hact hne y n ((hkfp _ hsc).symm.trans hy), hnrl⟩
  have hpost : ∀ don : Bool, endpoint.send_ipc st arI s7 a true false bdg g gr don ct ptr ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv g gr don ct.bv ptr.bv σf).1,
        JAt (L := L) arI AR r.1 r.2 z.2 ⦄ := by
    intro don
    by_cases hgg : g = true ∨ gr = true
    · by_cases hA : ∀ xd, σf.kheap d.bv = some (.tcb xd) → ∀ e' rep dd,
          xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none
      · by_cases hS : don = false ∨ ∀ xd, σf.kheap d.bv = some (.tcb xd) → xd.tcbSchedContext ≠ none
        · exact J7.sendFaultPJC hAT ht hkf hrn rfl hcur hni.2.2.1 hCf hti hnq' hpE hkef true bdg g gr don hgg hA hS
        · have hd1 : don = true := by
            cases don
            · exact absurd (Or.inl rfl) hS
            · rfl
          subst hd1
          refine J7.sendFaultPDJC hAT ht hkf hrn rfl hcur hni.2.2.1 hCf hti hnq' hpE hkef true bdg g gr hgg hA ?_
          intro xd hxd
          by_contra hne
          exact hS (Or.inr fun xd' hxd' => by rw [hxd] at hxd'; cases hxd'; exact hne)
      · refine J7.sendFaultIJC ht hkf hrn rfl hcur hni.2.2.1 hCf hti hnq' hpE hkef true bdg g gr don (Or.inr ?_)
        intro xd hxd e' rep dd hst
        by_contra hne
        apply hA
        intro xd' hxd' e'' rep' dd' hst'
        rw [hxd] at hxd'; cases hxd'
        rw [hst] at hst'; cases hst'; exact hne
    · exact J7.sendFaultIJC ht hkf hrn rfl hcur hni.2.2.1 hCf hti hnq' hpE hkef true bdg g gr don
        (Or.inl ⟨Bool.eq_false_iff.2 fun h => hgg (Or.inl h), Bool.eq_false_iff.2 fun h => hgg (Or.inr h)⟩)
  refine WP.spec_bind (hpost _) ?_
  rintro ⟨s', a'⟩ ⟨z, hz, hJ⟩
  apply (WP.spec_ok _).2
  refine ⟨rfl, ?_⟩
  have hz' : z ∈ (Fl4Spec.sendIpc (Z := Unit) true false bdg.bv
      (decide (Fl4Spec.Rights.allowGrant ∈ rightsOf sd rv g gr))
      (decide (Fl4Spec.Rights.allowGrantReply ∈ rightsOf sd rv g gr)) (decide (x.tcbSchedContext ≠ none)) ct.bv
      ptr.bv (updK σ ct.bv (.tcb { x with tcbFault := some f' }))).1 := by
    rw [rights_grant, rights_grantReply, ← hdon]; exact hz
  obtain ⟨Z', H', Cs', Ac', Lst', D', J'⟩ := hJ
  exact ⟨((), z.2), handleFault_ep_mem hk hfh _ hz',
    ⟨_, _, J'.xtop.rel.1, J'.xtop.rel.2.1, J'.xtop.rel.2.2.1, J'.xtop.rel.2.2.2.1, J'.xtop.rel.2.2.2.2.1⟩,
    ⟨_, _, _, _, _, _, J'⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`handle_fault` at a reschedule mid state with `CurInv`, every case** (module
docstring; `JAtZ.faultHypJZ`'s case split, the waiting receiver by
`JAtZ.faultRecvJC`). -/
theorem JAtZ.faultHypJZC2 (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : MidC σ)
    (hsw : σ.schedulerAction ≠ .resumeCurThread) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (hvfh : ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
    {f : error.Fault} {f' : Fl4Spec.Fault} (hf : CapFaultCorr f f') :
    faults.handle_fault st arI s a ct f ⦃ r => ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv f' σ).1,
      RelTopM (L := L) r.1 z.2 ∧ JAtR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨hcur, x, hk⟩ := J.curEq hct
  have htcb : Z.th ct = some .tcb := (J.xtop.curTcb hcur).1
  obtain ⟨x1, c1, hk1, hc1, hcr⟩ := fhCap_rel J.xtop.rel.2.1.1 htcb
  rw [hk] at hk1; cases hk1
  have hv : Fl4Spec.validFaultHandler (absCap c1) := by
    rw [hcr.2]; exact hvfh x (by rw [hcur]; exact hk)
  by_cases hn : c1 = .Null
  · subst hn
    exact J.noFaultJC hni hsw hct hnq hc1 f f'
  obtain ⟨p, b, sd, rv, g, gr, rfl⟩ := vfh_ep hv hn
  have hAS : AbsSlot Z.th (ct.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨ct, rfl, Or.inr ⟨htcb, 3, by decide, rfl⟩⟩
  have hpE : p ∈ Z.E := J.slotE hAS hc1
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xe, hke, -⟩ := hI.1.ep p hpE
  cases xe with
  | recvEP l =>
    obtain ⟨-, xs, hxs0, hq, -⟩ := hI.1.toE.at_ep hpE hke
    obtain ⟨d', xs', rfl⟩ := List.exists_cons_of_ne_nil hxs0
    simp only [List.map_cons] at hq
    subst hq
    refine WP.spec_mono (J.faultRecvJC hAT hni hct hnq hc1 hke hf) ?_
    rintro r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩
    exact ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  | idleEP =>
    exact J.faultBlockJC hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf
  | sendEP q =>
    exact J.faultBlockJC hni hsw hct hnq hc1 (fun xe h => by rw [hke] at h; cases h; trivial) hf

end

end

end Fl4Proofs.P3
