/-
P3 (DESIGN.md §9), scheduling contexts: **the current thread's own
timeout-fault send to a waiting receiver with a reply object, the reply
pushed** (KENTRY-PLAN kp17 (1)): XTopJointFaultTmo's `JAtZ.sendTmoRecvPJ`
(a scripted copy, as ScTmoCtRecvI's `JAtZ.sendTmoRecvCtIJ`) for `t` the
current thread: the base `J0` a parameter (ScTmoCtBase), the receiver not the
current thread by `t ≠ d`, the action resume or choose, the sender's queue
bits from `NotQueued` at the hole, and after the push (`pushSt`, whose
`set_thread_state` blocks the current thread on the reply) the action
`ChooseNewThread` (`stsAct_cur`).
-/
import Fl4Proofs.P3.ScTmoCtRecvI
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
/-- **The current thread's timeout-fault `send_ipc` to a waiting receiver,
the reply pushed** (module docstring): XTopJointFaultTmo's
`JAtZ.sendTmoRecvPJ` with `t` the current thread (Running/Restart at the send
`s7`, `σf`) and the base `J0` given (ScTmoCtBase's `JTH.tmoBaseCtJ`: the
thread `Inactive` with the fault, its SC's consumed time cleared, related to
the pre-state `σ` by `hk0`/`hk0t`/`hk0s`/`hsk0`); the sender's own
`reply_push` (its `set_thread_state`) sets `ChooseNewThread` (`stsAct`):
`ActIdle`, `CurRunM` and `cur` after from that. -/
theorem JAtZ.sendTmoRecvCtPJ {s0 : S} {σ0 : Fl4Spec.State Unit} (hAT : P0.ArchTotal arI)
    (J0 : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ0)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {t : U64} (ht : t ∈ Z.T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x))
    (htc : t.bv = σ.curThread)
    (hres : σ.schedulerAction = .resumeCurThread ∨ σ.schedulerAction = .chooseNewThread)
    (hnq : NotQueued σ t.bv) (hidt : σ.idleThread ≠ t.bv)
    {sc : U64} (hsc : sc ∈ Z.C) (hxsc : x.tcbSchedContext = some sc.bv)
    {y : Fl4Spec.SchedContext} {n : Nat} (hky : σ.kheap sc.bv = some (.schedContext y n))
    (b : U64)
    (hk0 : ∀ q, q ≠ t.bv → q ≠ sc.bv → σ0.kheap q = σ.kheap q)
    (hk0t : σ0.kheap t.bv = some (.tcb { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) }))
    (hk0s : σ0.kheap sc.bv = some (.schedContext { y with scConsumed := (0#u64 : U64).bv } n))
    (hsk0 : Sk σ σ0) (hrq0 : σ0.readyQueues = σ.readyQueues)
    (hwB : P1.WritesIn st s s0 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfB : P1.WritesIn st s s0 (fun b => P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s b ∨ False))
    {ts : Fl4Spec.ThreadState} (hrun : Fl4Spec.runnable ts = true) {s7 : S}
    (hI7 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s7
      (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) })))
    (hblk7 : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s7)
    (hW7 : P1.WritesIn st s s7 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hfoot7 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s s7)
    (hcb7 : P1.CanBlock st (P1.Heap.tcbs H) Ac s7 t)
    {e d : U64} (he : e ∈ Z.E) {q : List Fl4Spec.ObjRef}
    (hke : σ.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))))
    (badge : U64) (g gr : Bool)
    (hg : g = true ∨ gr = true) (htD : t ∉ D) (hya : Fl4Spec.scActive y = true)
    (hrepn : ∀ xd, σ.kheap d.bv = some (.tcb xd) → ∀ e' rep dd, xd.tcbState = .blockedOnReceive e' rep dd → rep ≠ none) :
    endpoint.send_ipc st arI s7 a true false badge g gr false t e ⦃ r =>
      ∃ z ∈ (Fl4Spec.sendIpc (Z := Unit) true false badge.bv g gr false t.bv e.bv
        (updK σ t.bv (.tcb { x with tcbState := ts, tcbFault := some (.timeout b.bv) }))).1,
        ∃ (V : XVs) (Lst' : U64 → List U64), JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst' D r.1 r.2 z.2 ⦄ := by
  set xt : Fl4Spec.Tcb := { x with tcbState := ts, tcbFault := some (.timeout b.bv) } with hxt
  set σf := updK σ t.bv (.tcb xt) with hσf
  set xT : Fl4Spec.Tcb := { x with tcbState := .inactive, tcbFault := some (.timeout b.bv) } with hxT
  set yS : Fl4Spec.SchedContext := { y with scConsumed := (0#u64 : U64).bv } with hyS
  have hst : t.bv ≠ sc.bv := fun e0 => by rw [e0, hky] at hk; cases hk
  have hkf : ∀ q, q ≠ t.bv → σf.kheap q = σ.kheap q := fun q h1 => by simp [hσf, updK, h1]
  have hkfr : ∀ p, (rhoT σf t.bv sc.bv xT yS n).kheap p = σ0.kheap p := fun p => by
    by_cases h1 : p = t.bv
    · subst h1; rw [rhoT_kt hst, hk0t]
    · by_cases h2 : p = sc.bv
      · subst h2; rw [rhoT_ksc, hk0s]
      · rw [rhoT_kh h1 h2, hk0 p h1 h2, hkf p h1]
  have skf : Sk σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨hsk0.ct.symm, hsk0.idle.symm, hsk0.cons.symm, hsk0.tm.symm, hsk0.csc.symm, hsk0.rel.symm, hsk0.cdt.symm,
      hsk0.orig.symm, hsk0.arch.symm, hsk0.dt.symm, hsk0.isc.symm⟩
  have Fr0 : CFr e.bv d.bv σ0 (rhoT σf t.bv sc.bv xT yS n) := ⟨skf, fun p => Or.inl (hkfr p)⟩
  have IK0 : IK d.bv σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨fun p => by rw [hkfr p]; exact OIK.refl _ _, hrq0.symm, hsk0.rel.symm, hsk0.tm.symm⟩
  have SK0 : SKeep σ0 (rhoT σf t.bv sc.bv xT yS n) :=
    ⟨hsk0.rel.symm, hsk0.tm.symm, fun p y' hy => ⟨y', by rw [← hkfr]; exact hy, rfl⟩,
      fun p y' n' hy => by rw [← hkfr]; exact hy⟩
  have hP0 := J0.ip
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP
  have hI := hI7
  have hR := hI.1.toE
  have hS0 := IpcRel.toSRN hI.1 hI.2
  have hTe : Z.T = P1.Heap.tcbs H := J0.tcbs_eq.1
  have hRe : Z.R = P1.Heap.replies H := J0.tcbs_eq.2
  have hte0 : t.bv ≠ e.bv := kheap_ne hk hke (fun _ h1 h2 => by subst h1; cases h2)
  have hse0 : sc.bv ≠ e.bv := kheap_ne hky hke (fun _ h1 h2 => by subst h1; cases h2)
  have hkx := hk
  have hk : σf.kheap e.bv = some (.endpoint (.recvEP (d.bv :: q))) := by rw [hkf _ (Ne.symm hte0)]; exact hke
  have hkt : σf.kheap t.bv = some (.tcb xt) := by simp [hσf, updK]
  have hrn : Fl4Spec.runnable xt.tcbState = true := hrun
  have hft : xt.tcbFault = some (.timeout b.bv) := rfl
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
  have hd3 : (L.mem s7 (tStA d')).val = 3 := (hB d' (by simp)).1
  have hdb : L.mem s7 (tBlockA d') = e := (hB d' (by simp)).2
  obtain ⟨e', rep, dd, hstd⟩ := tsCode_three (hxd.st.symm.trans hd3)
  have he' : e' = e.bv := by
    have := hxd.blk e' (by rw [hstd]; rfl); rw [hdb] at this; exact this.symm
  subst he'
  obtain ⟨hrep, hrepR⟩ := hxd.recv _ _ _ hstd
  have hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4 := by have := runnable_code hrn; omega
  have htd : t ≠ d' := by intro h; subst h; exact hnb.1 (hxt.st.symm.trans hd3)
  have hde : d'.bv ≠ e.bv := kheap_ne hkd hk (fun _ h1 h2 => by subst h1; cases h2)
  have hte : t.bv ≠ e.bv := hte0
  have htd' : t.bv ≠ d'.bv := bv_ne htd
  have hdsc : d'.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkd; cases hkd
  have hkdσ : σ.kheap d'.bv = some (.tcb xd) := by rw [← hkf _ (Ne.symm htd')]; exact hkd
  have hkd0 : σ0.kheap d'.bv = some (.tcb xd) := by rw [hk0 _ (Ne.symm htd') hdsc]; exact hkdσ
  have hke0 : σ0.kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hk0 _ (Ne.symm hte0) (Ne.symm hse0)]; exact hke
  have hdc : d'.bv ≠ σf.curThread := fun h => htd' (htc.trans h.symm)
  -- P1's facts at the send
  obtain ⟨⟨Q0, R0, h0⟩, hB0, hX0, hSc0, hSg0⟩ := hblk7
  have hdH : d' ∈ P1.Heap.tcbs H := J0.zH.1 d' hdT
  have hHe : H e = some .ep := J0.zH.2.1 e he
  have hTP : P1.TcbPlaced (P1.Heap.tcbs H) := h0.tcbs
  have hdta := hTP d' hdH
  have hsub := hSg0.sub
  have hds : L.mem s7 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_tStA, tsVals.2.2.1]; exact UScalar.eq_of_val_eq hd3
  have hbe : L.mem s7 (P1.blockA d') = e := by rw [P1.blockA_eq, ← tBlockA_eq]; exact hdb
  have hdq := P1.endpoint.ep_dequeue.inv s7 d' Q0 R0 h0 hdH (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h0.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hHe)
  obtain ⟨hE0, -, hq0'⟩ := hEW0.1 e heE0
  have hdm : d' ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 d' hdH (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  have pf := P1.endpoint.ep_dequeue.foot s7 e d' (EQ0 e) hTP hE0 hq0' hdm
  -- FL4: the endpoint's state and queue
  unfold endpoint.send_ipc
  refine WP.spec_bind (Fl4Proofs.P1.obj.Ep.state.spec s7 e) ?_
  rintro _ rfl
  rw [epState_eq, hst2]
  rw [if_neg (by rw [ep_state_vals.1]; decide), if_neg (by rw [ep_state_vals.2.1]; decide)]
  refine WP.spec_bind (Fl4Proofs.P1.endpoint.get_queue.spec s7 e) ?_
  rintro _ rfl
  have hhead : (L.epQ s7 e).head = d' := by rw [epQ_eq]; exact hQ.head
  rw [hhead]
  -- the dequeue
  refine WP.spec_bind (WP.spec_and (WP.spec_and (ep_dequeue_c hH hP0 hP s7 σf hR hS0 he hk (d := d')
      (by simp [Fl4Spec.Endpoint.epQueue])) (ep_dequeue_full hP s7 he d' _ hQ (by simp)))
    (WP.spec_and hdq pf)) ?_
  rintro s1 ⟨⟨⟨-, hR1, hS1, hA1⟩, -, -, hQA, hWE, -, -⟩, ⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  set σ1 := Notif.updK σf e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) with hσ1
  have hW1a : P1.WritesIn st s7 s1 (fun b => EW e b ∨ ∃ w ∈ (d' :: xs'), TL w b) :=
    ⟨hWE.1, hWE.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩⟩
  have hW1 : P1.WritesIn st s7 s1 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) := hW1a.mono fun b hb => by
    rcases hb with h | ⟨w, hw, h | h⟩
    · exact Or.inr (Or.inl ⟨e, he, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩)
    · exact Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩)
  have F1 : P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s7 s1 :=
    P1.Foot.of w1 fun b hb => hb.kw hq0'.mem (Or.inl hHe)
  obtain ⟨hB1, hX1, hS1', hSg1, ea1, -, -⟩ := P1.frame_bx h0 hB0 hX0 hSc0 hSg0 f1 o1 n1 k1
    (P1.TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg0.sub _ (hX0.1.ntB n' hn').2)⟩)
  have hkt1 : σ1.kheap t.bv = some (.tcb xt) := by simp [σ1, hte, hkt]
  have hkd1 : σ1.kheap d'.bv = some (.tcb xd) := by simp [σ1, hde, hkd]
  have hk1e : σ1.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by simp [σ1]
  have hky1 : σ1.kheap sc.bv = some (.schedContext y n) := by
    simp [σ1, hse0, hσf, updK, Ne.symm hst, hky]
  have hdb1 : L.mem s1 (tBlockA d') = e := by
    rw [hA1 _ (a_blk hda).1 ⟨d', hdT, (a_blk hda).2⟩, hdb]
  have hq1 := dequeued_not_queued hR1 he hdb1 hk1e (epDeq_not_mem _)
  have hke0f : (rhoT σf t.bv sc.bv xT yS n).kheap e.bv = some (.endpoint (.recvEP (d'.bv :: q))) := by
    rw [hkfr]; exact hke0
  -- the shadow frame from the base
  have eρ1 : rhoT σ1 t.bv sc.bv xT yS n = updK (rhoT σf t.bv sc.bv xT yS n) e.bv (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ1, rhoT_updK _ (Ne.symm hte) (Ne.symm hse0)]
  have Fr1 : CFr e.bv d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine Fr0.trans (CFr.upd hke0f ?_)
    exact (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl,
      by rw [epDeq_queue']; unfold Fl4Spec.removeAll; exact List.filter_sublist,
      by simp [Fl4Spec.Endpoint.epQueue]⟩)))
  have IK1 : IK d'.bv σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine IK0.trans (IK.updOther (o' := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) hke0f ?_)
    exact (fun o0 h => by
      rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩)
  have SK1 : SKeep σ0 (rhoT σ1 t.bv sc.bv xT yS n) := by
    rw [eρ1]
    refine SK0.trans ?_
    exact SKeep.updK (p := e.bv) (o := .endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) (fun y h => by cases h)
      (fun _ _ h => by cases h)
  have htbk : ∀ p y', σf.kheap p = some (.tcb y') → ∃ x0, σ0.kheap p = some (.tcb x0) ∧
      x0.tcbIpcframe = y'.tcbIpcframe ∧ x0.tcbIpcBuffer = y'.tcbIpcBuffer := fun p y' hp => by
    by_cases h1 : p = t.bv
    · subst h1; rw [hkt] at hp; cases hp; exact ⟨_, hk0t, rfl, rfl⟩
    · have h2 : p ≠ sc.bv := fun e0 => by rw [e0, hkf _ (Ne.symm hst), hky] at hp; cases hp
      exact ⟨y', by rw [hk0 p h1 h2, ← hkf p h1]; exact hp, rfl, rfl⟩
  have hafw : ∀ p ao, σ0.kheap p = some (.archObj ao) → σf.kheap p = some (.archObj ao) := fun p ao hp => by
    have h1 : p ≠ t.bv := fun e0 => by rw [e0, hk0t] at hp; cases hp
    have h2 : p ≠ sc.bv := fun e0 => by rw [e0, hk0s] at hp; cases hp
    rw [hkf p h1, ← hk0 p h1 h2]; exact hp
  have hOK1 : Endp.IpcBufCapOK σ1 := ipcBufCapOK_epStep (ipcBufCapOK_tr J0.xferH.1 htbk hafw) (EpStep.ep hk)
  have hBC1 : Endp.BufCover Z.T Z.B σ1 := bufCover_epStep (bufCover_tr J0.xferH.2.1 htbk) (EpStep.ep hk)
  have hsc1 : sc ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J0.jpl
    exact ⟨_, (hJ.sc sc _ n (J0.c0 sc hsc) hk0s).2⟩
  -- the transfer
  refine WP.spec_bind (xferTmoStepJ hP0 (hH.epHyps hP0) hmax s1 a σ1 htu hR1 hS1 hOK1 hBC1 ht hdT htd hkt1 hkd1 hft
    hxsc hky1 e badge g hTP hdH h1 hB1 hX1 hS1' hSg1 hsc1) ?_
  rintro s2 ⟨x2, e2, hx2, hR2, hS2, hA2, w2, ea2, h2, hB2, hX2, hS2'', hSg2, f2⟩
  set σ2 := Notif.updK (Ipc.tmoSt σ1 sc y n) d'.bv (.tcb x2) with hσ2
  have hkd2 : σ2.kheap d'.bv = some (.tcb x2) := by simp [σ2]
  have hkt2 : σ2.kheap t.bv = some (.tcb xt) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne htd', Function.update_of_ne hst]
    exact hkt1
  have hksc2 : σ2.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσ2, updK_kheap, Function.update_of_ne (Ne.symm hdsc)]
    show Function.update σ1.kheap sc.bv _ sc.bv = _
    rw [Function.update_self]
  have hst2' : x2.tcbState = .blockedOnReceive e.bv rep dd := by rw [hx2]; exact hstd
  have hxsc2 : x2.tcbSchedContext = xd.tcbSchedContext := by rw [hx2]
  have hk1e2 : σ2.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hde), Function.update_of_ne (Ne.symm hse0)]
    exact hk1e
  have hq2 : ∀ e'' ∈ Z.E, ∀ z, σ2.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h, hkd2] at hz; cases hz
    have hns' : sc.bv ≠ e''.bv := by intro h; rw [← h, hksc2] at hz; cases hz
    rw [hσ2] at hz
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne (Ne.symm hne),
      Function.update_of_ne (Ne.symm hns')] at hz
    exact hq1 e'' he'' z hz
  have hrw : L.mem s2 (tReplyA d') = L.mem s7 (tReplyA d') := by
    rw [show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl, f2 d' hdH _ (by simp) (by simp) (by simp),
      ← show tReplyA d' = core.num.U64.wrapping_add d' 3360#u64 from rfl,
      hA1 _ (a_reply hda).1 ⟨d', hdT, (a_reply hda).2⟩]
  have hscw8 : SW Z.C σf (scW sc 8#u64) := sw_hdr hI.2.2.1 hsc (K := 8#u64) (by simp) (by simp) (by decide)
  have hW2 : P1.WritesIn st s7 s2 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW1.trans1 (w2.mono fun b hb => by
    rcases hb with ⟨eb, -⟩ | (⟨y0, hy, K, h1', h2', -, eb⟩ | hb)
    · subst eb; exact Or.inl (Or.inl (Or.inr (Or.inr hscw8)))
    · have hyT : y0 ∈ Z.T := by rw [hTe]; exact hy
      refine Or.inl (Or.inr ⟨y0, hyT, K.val, h1', by omega, by omega, by omega, by omega, ?_⟩)
      rw [eb]; exact tfield_val (hP.tcb y0 hyT) (by omega)
    · exact absurd hb (Set.notMem_empty _))
  have F2 : P1.WritesIn st s1 s2 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s1) :=
    w2.mono fun b hb => by
      rcases hb with ⟨-, c0, hc0, hin⟩ | (⟨y0, hy, K, h1', h2', h3', eb⟩ | hb)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c0, hc0, hin⟩)))
      · exact Or.inl ⟨y0, hy, K, by omega, by omega, by omega, by omega, eb⟩
      · exact absurd hb (Set.notMem_empty _)
  have eρ2 : rhoT σ2 t.bv sc.bv xT yS n = updK (rhoT σ1 t.bv sc.bv xT yS n) d'.bv (.tcb x2) := by
    rw [hσ2, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updKsc _ hst]
  have hkd1ρ : (rhoT σ1 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb xd) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd1
  have Fr2 : CFr e.bv d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact Fr1.trans (CFr.upd hkd1ρ (Or.inl ⟨xd, xd.tcbState, xd.tcbBoundNotification, xd.tcbFault, x2.tcbArch, rfl,
      by rw [hx2], Or.inr ⟨Or.inl rfl, rfl, Or.inl ⟨_, _, _, hstd⟩, Or.inr (Or.inr rfl)⟩⟩))
  have IK2 : IK d'.bv σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]; exact IK1.trans (IK.updSelf hkd1ρ hxsc2)
  have SK2 : SKeep σ0 (rhoT σ2 t.bv sc.bv xT yS n) := by
    rw [eρ2]
    exact SK1.trans (SKeep.updK (p := d'.bv) (o := .tcb x2) (fun y h => ⟨xd, hkd1ρ, by cases h; exact hxsc2.symm⟩)
      (fun _ _ h => by cases h))
  have hks2 : L.ksb s2 = L.ksb s7 := hW2.1
  have Fst2 : L.mem s2 (P1.stA d') = L.mem s7 (P1.stA d') := by
    rw [P1.stA_eq]
    exact (f2 d' hdH _ (by simp) (by simp) (by simp)).trans (f1 d' hdH _ (by simp) (by simp) (by simp) (by simp))
  have hds2 : L.mem s2 (P1.stA d') = sched.TS_BLOCKED_ON_RECV := Fst2.trans hds
  -- the reply object
  obtain ⟨r, hrp⟩ := Option.ne_none_iff_exists'.1 (hrepn xd hkdσ _ _ _ hstd)
  subst hrp
  obtain ⟨hw0, hwr⟩ := Notif.optRef_some hrep
  have hwR := hrepR (by simp)
  refine WP.spec_bind (Endp.obj.Tcb.reply_obj.spec s2 d') ?_
  rintro _ rfl
  rw [hrw]
  have hne0 : (L.mem s7 (tReplyA d') != 0#u64) = true := by simp [hw0]
  simp only [hne0, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
  set w := L.mem s7 (tReplyA d') with hwdef
  subst hwr
  obtain ⟨xr, hkr, -⟩ := hR.reply w hwR
  have hwe : w.bv ≠ e.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hwd : w.bv ≠ d'.bv := kheap_ne hkr hkd (fun _ h1 h2 => by subst h1; cases h2)
  have hwt : w.bv ≠ t.bv := kheap_ne hkr hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hws : w.bv ≠ sc.bv := fun e0 => by
    have h1 : σf.kheap sc.bv = some (.schedContext y n) := by rw [hkf _ (Ne.symm hst)]; exact hky
    rw [e0, h1] at hkr; cases hkr
  have hkr2 : σ2.kheap w.bv = some (.reply xr) := by
    rw [hσ2]
    simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hwd, Function.update_of_ne hws]
    simp [σ1, hwe, hkr]
  have hkrσ : σ.kheap w.bv = some (.reply xr) := by rw [← hkf _ hwt]; exact hkr
  have hb' : xr.replyTcb = some d'.bv := hback_of J0.sv hkd0 e.bv w.bv dd xr (by rw [hstd]) (by rw [hk0 _ hwt hws]; exact hkrσ)
  have hX2' := IpcRel.ofSRN hR2 hS2
  have hrA : L.mem s2 (P1.replyA d') = w := by show L.mem s2 (tReplyA d') = w; rw [hrw]
  obtain ⟨hiR, hit⟩ := hX2.2.1.recv d' hdH hds2 (by rw [hrA]; exact hw0)
  rw [hrA] at hiR hit
  refine WP.spec_bind (WP.spec_and (WP.spec_and (reply_unlink_c hH hP0 hP s2 σ2 hR2 hS2 hdT hkd2 hst2' hwR hkr2
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
  have hW3' : P1.WritesIn st s7 s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW2.trans1 (hW3.mono fun b hb => cnW_back hks2 (SzKeepC.of (by
      intro p y0 m hp
      by_cases hps : p = sc.bv
      · subst hps; rw [hksc2] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
      · refine ⟨y0, ?_⟩
        rw [hσ2] at hp
        have hpd : p ≠ d'.bv := fun e0 => by rw [e0] at hp; simp at hp
        simp only [Ipc.tmoSt, Sched.updSc, updK_kheap, Function.update_of_ne hpd, Function.update_of_ne hps] at hp
        have hpe : p ≠ e.bv := fun e0 => by rw [e0] at hp; simp [σ1] at hp
        simpa [σ1, hpe] using hp)) hb)
  have hkt3 : σ3.kheap t.bv = some (.tcb xt) := by rw [stsAct_kheap]; simp [σ3a, htd', hwt.symm, hkt2]
  have hkd3 : σ3.kheap d'.bv = some (.tcb x3) := by rw [stsAct_kheap]; simp
  have hkr3 : σ3.kheap w.bv = some (.reply xr3) := by rw [stsAct_kheap]; simp [σ3a, hwd]
  have hksc3 : σ3.kheap sc.bv = some (.schedContext yS n) := by
    rw [stsAct_kheap]; simp [σ3a, Ne.symm hdsc, hws.symm, hksc2]
  have hq3 : ∀ e'' ∈ Z.E, ∀ z, σ3.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue := by
    intro e'' he'' z hz
    rw [stsAct_kheap] at hz
    have hne : d'.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp at hz
    have hne' : w.bv ≠ e''.bv := by intro h; rw [← h] at hz; simp [σ3a, hwd] at hz
    exact hq2 e'' he'' z (by simpa [σ3a, Ne.symm hne, Ne.symm hne'] using hz)
  -- the shadows
  have hkr2ρ : (rhoT σ2 t.bv sc.bv xT yS n).kheap w.bv = some (.reply xr) := by
    rw [rhoT_kh hwt hws]; exact hkr2
  have hkd3aρ : (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)).kheap d'.bv = some (.tcb x2) := by
    simp only [updK_kheap, Function.update_of_ne (Ne.symm hwd)]
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd2
  have eρ3 : rhoT σ3 t.bv sc.bv xT yS n =
      Notif.stsAct (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)) d'.bv (.tcb x3)) d'.bv := by
    rw [e3s, stsAct_ne (show d'.bv ≠ (Notif.updK (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv
      (.reply xr3)) d'.bv (.tcb x3)).curThread from hdc), hσ3a, rhoT_updK _ (Ne.symm htd') hdsc, rhoT_updK _ hwt hws]
  have Fr3 : CFr e.bv d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    exact (Fr2.trans (CFr.upd hkr2ρ (Or.inr (Or.inr (Or.inr ⟨xr, rfl, rfl, hb'⟩))))).trans
      (CFr.stsIn hkd3aρ (Or.inl ⟨_, _, _, hst2'⟩))
  have IK3 : IK d'.bv σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    have IK3a : IK d'.bv σ0 (Notif.updK (rhoT σ2 t.bv sc.bv xT yS n) w.bv (.reply xr3)) :=
      IK2.trans (IK.updOther (o' := .reply xr3) hkr2ρ (fun o0 h => by
        rcases h with rfl | rfl <;> exact ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩))
    exact (IK3a.trans (IK.updSelf (y := x3) hkd3aρ rfl)).trans (IK.sts _ _ _)
  have SK3 : SKeep σ0 (rhoT σ3 t.bv sc.bv xT yS n) := by
    rw [eρ3]
    exact ((SK2.trans (SKeep.updK (p := w.bv) (o := .reply xr3) (fun y h => by cases h)
      (fun _ _ h => by cases h))).trans (SKeep.updK (p := d'.bv) (o := .tcb x3) (fun y h => ⟨_, hkd3aρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hct3 : σ3.curThread = σ.curThread := by rw [e3s]; rfl
  have hact3 : σ3.schedulerAction = σ.schedulerAction := by rw [e3s]; rfl
  have hsc3 : x3.tcbSchedContext = xd.tcbSchedContext := by simp [x3, hxsc2]
  have hB3 := hB2.keepT h2 k3 (by rw [e3']; exact P1.not_blocked_inactive) (by rw [e3']; exact P1.inactive_ne.1)
  have hX3 := hX2.keepT k3 (by rw [e3']; exact P1.inactive_ne) hclr
  have hS3' := hS2''.keepT hX2 k3
  have hSg3 : P1.SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s3 :=
    ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩
  have F3 := footW_trans (footW_trans (footW_of (W := fun _ => False) F1) (F2.mono fun b hb => Or.inl hb))
    (footW_of fu3)
  have hxt3 := hR3.at_tcb ht hkt3
  have hty3 : L.mem s3 (tFaultA t) = 5#u64 := by
    have hfr := hxt3.faultR
    unfold FaultRel at hfr; rw [hft] at hfr; exact hfr.1
  have hks3 : L.ksb s3 = L.ksb s7 := hW3'.1
  -- the sender's and the receiver's words at `s3`
  have htH : t ∈ P1.Heap.tcbs H := J0.zH.1 t ht
  have hw3 : (L.mem s3 (P1.stA t)).val = tsCode xt.tcbState := by
    rw [P1.stA_eq, ← tStA_eq, hxt3.st]
  obtain ⟨hnbt3, hnrp3⟩ := P1.run_word (w := L.mem s3 (P1.stA t)) (by rw [hw3]; exact runnable_code hrn)
  have hX3' := IpcRel.ofSRN hR3 hS3
  have hSR3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hX3'.2.2.1
  obtain ⟨Q3, R3', hcq3, hs3⟩ := hSR3.lists
  have hSM := ScRelM.of hX3'.1
  have hnqD0 : NotQueued σ0 d'.bv := by
    refine ⟨fun dm p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rq dm p _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
    · obtain ⟨x0, -, -, -, hkx0, -, hrx, -, -⟩ := J0.inv.rel _ hm
      rw [hkd0] at hkx0; cases hkx0; rw [hstd] at hrx; cases hrx
  have hnqD : NotQueued σ d'.bv := ⟨by rw [← hrq0]; exact hnqD0.1, by rw [← hsk0.rel]; exact hnqD0.2⟩
  have hnqT : NotQueued σ t.bv := hnq
  have hqq3 : σ3.readyQueues = σ.readyQueues := IK3.2.1.trans hrq0
  have hrq3 : σ3.releaseQueue = σ.releaseQueue := IK3.2.2.1.trans hsk0.rel
  have hnqT3 : NotQueued σ3 t.bv := ⟨by rw [hqq3]; exact hnqT.1, by rw [hrq3]; exact hnqT.2⟩
  have hnqD3 : NotQueued σ3 d'.bv := ⟨by rw [hqq3]; exact hnqD.1, by rw [hrq3]; exact hnqD.2⟩
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
  have hna3t : L.actionW s3 ≠ t := actionW_ne_of hSR3 ht (by
    rw [hact3]; rcases hres with e0 | e0 <;> rw [e0] <;> intro e' <;> cases e')
  have hna3d : L.actionW s3 ≠ d' := actionW_ne_of hSR3 hdT (by
    rw [hact3]; rcases hres with e0 | e0 <;> rw [e0] <;> intro e' <;> cases e')
  have hidl3 : σ3.idleThread = σ.idleThread := by rw [e3s]; rfl
  have hiw3 : ∀ u ∈ Z.T, u.bv ≠ σ.idleThread → L.idleW s3 ≠ u := fun u hu hne h' => by
    apply hne
    rw [← hidl3, hs3.idleTh]
    unfold P1.LawfulStore.idleW at h'; rw [hcq3.cur] at h'
    exact congrArg _ (show nodeW st s3 Z.c layout.node.IDLE_THREAD = u from h').symm
  have hit : t.bv ≠ σ.idleThread := fun h => hidt h.symm
  have hid : d'.bv ≠ σ.idleThread := by
    intro h
    obtain ⟨x0, hkx0, -, hxs, -⟩ := J0.act.2
    rw [hsk0.idle, ← h, hkd0] at hkx0; cases hkx0; rw [hstd] at hxs; cases hxs
  have hsA3 : L.mem s3 (P1.scA t) = L.mem s7 (P1.scA t) := by
    rw [P1.scA_eq, k3.fld t htH _ (by simp) (by simp) (by simp) (by simp) (fun e0 => absurd e0 htd),
      f2 t htH _ (by simp) (by simp) (by simp), f1 t htH _ (by simp) (by simp) (by simp) (by simp)]
  have hcA : L.mem s3 (P1.scA t) ≠ 0#u64 → L.mem s3 (P1.scA t) ∈ Ac := fun h0' => by
    rw [hsA3] at h0' ⊢; exact hcb7.ac h0'
  have hwH : w ∈ P1.Heap.replies H := hRe ▸ hwR
  have hw00 : w ≠ 0#u64 := (J0.rp.align w hwR).2.1
  have hqt3 := Endp.not_queued hR3 ht hkt3 hnb
  -- the push on `IRel`, at P1
  have hw1 : P1.WritesIn st s3 (L.wr s3 (P1.rTcbA w) t) (fun b => b.val = w.val) := by
    obtain ⟨-, -, -, hA1⟩ := reply_write_rel (hH.epHyps hP0) hP s3 σ3 hR3 hS3.1 hwR hkr3 t
    exact ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => hA1 b hb hn⟩
  have hns3 : tsCode xt.tcbState ≠ 6 := by have := runnable_code hrn; omega
  have hPush : ipc.reply_push st arI s3 a t d' w false ⦃ r => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv false σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
      EpStateRel Z.T Z.E Z.R Z.B (L.mem r.1) (pushSt σ3 t.bv w.bv xr3 xt) ∧
      SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) r.1 (pushSt σ3 t.bv w.bv xr3 xt) ∧
      P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
        (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      (∀ y ∈ P1.Heap.tcbs H, y ≠ t → L.mem r.1 (P1.stA y) = L.mem s3 (P1.stA y)) ∧
      P1.Foot st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H) s3 r.1 ∧
      sched.set_blocked_on_reply st (L.wr s3 (P1.rTcbA w) t) t w = ok r.1 ⦄ := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and
      (reply_push_iC (don := false) (P := fun s' σ' => σ' = pushSt σ3 t.bv w.bv xr3 xt ∧
          EpStateRel Z.T Z.E Z.R Z.B (L.mem s') σ' ∧
          SRN st Z.N Z.T (SRS st Z.T (SRT st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
            (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s' σ')
        hH hP0 hP s3 a σ3 hR3 hS3 ht hkt3 hkd3 hqt3 hns3 hwR hkr3 (fun _ => hdT)
        (fun s' h1 h2 => ⟨rfl, h1, h2⟩) (fun hdon => by cases hdon))
      (P1.ipc.reply_push.ipc hAT s3 a t d' w false Q0 R0 h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        hna3t (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J0.zH.1 d' hdT)
        (Ne.symm htd) hqbD hrbD hna3d (hiw3 d' hdT hid) hcA))
      (P1.ipc.reply_push.nd (Es := P1.EH H) s3 a t d' w false h3 (fun y hy => by
          obtain ⟨hy1, hy2⟩ := hy
          rcases hy1 with hy1 | hy1
          · exact absurd hy1 (Set.notMem_empty _)
          · exact absurd hy1 hy2) (Or.inr hnbt3) hB3 hX3 hS3' hSg3 htH hqbT hrbT
        hna3t (hiw3 t ht hit) ⟨hnrp3, fun e0 => hnbt3 (Or.inr (Or.inl e0))⟩ hwH hw00 z3 (J0.zH.1 d' hdT)
        (Ne.symm htd) hcA (Or.inl rfl))) ?_
    rintro ⟨s4, a4⟩ ⟨⟨⟨ha, σ', hm, e4, hR4, hS4⟩, hb1, hb2, -⟩, -, hf, hsb⟩
    subst e4
    exact ⟨ha, hm, hR4, hS4, hb1, hb2, hf, hsb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.2 = a ∧
      Fl4Spec.replyPush (Z := Unit) t.bv d'.bv w.bv false σ3 = ({((), pushSt σ3 t.bv w.bv xr3 xt)}, False) ∧
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
    rw [hty3, if_pos (by unfold fl4_abi.consts.fault.NullFault; decide)]
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
  have hz3 : SzKeepC Z.C σf σ3 := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hksc3] at hp; cases hp; exact ⟨y, by rw [hkf _ (Ne.symm hst)]; exact hky⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkt3] at hp; cases hp
      have hpd : p.bv ≠ d'.bv := fun e0 => by rw [e0, hkd3] at hp; cases hp
      have hpw : p.bv ≠ w.bv := fun e0 => by rw [e0, hkr3] at hp; cases hp
      have hpe : p.bv ≠ e.bv := fun e0 => by
        have h1 : σ3.kheap e.bv = some (.endpoint (epDeq (.recvEP (d'.bv :: q)) d'.bv)) := by
          rw [stsAct_kheap]; simp [σ3a, updK, Ne.symm hde, Ne.symm hwe, hk1e2]
        rw [e0, h1] at hp; cases hp
      refine ⟨y0, ?_⟩
      rw [stsAct_kheap] at hp
      simp [σ3a, hσ2, updK, hpd, hpw, hps', σ1, hpe] at hp
      exact hp
  have hW4' : P1.WritesIn st s7 s4 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW3'.trans1 (hW4.mono fun b hb => cnW_back hks3 hz3 hb)
  have hks4 : L.ksb s4 = L.ksb s7 := hW4'.1
  set σ4 := pushSt σ3 t.bv w.bv xr3 xt with hσ4
  have hkd4 : σ4.kheap d'.bv = some (.tcb x3) := by rw [ps_ko (Ne.symm htd') (Ne.symm hwd)]; exact hkd3
  have hq4 : ∀ e'' ∈ Z.E, ∀ z, σ4.kheap e''.bv = some (.endpoint z) → d'.bv ∉ z.epQueue :=
    fun e'' he'' z hz => hq3 e'' he'' z ((ps_oth hkt3 hkr3 hwt (fun _ h => by cases h) (fun _ h => by cases h)).1 hz)
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
  have hW5' : P1.WritesIn st s7 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s7 σf) :=
    hW4'.trans1 (hW5.mono fun b hb => Or.inl (Or.inl (KFoot.of_sfoot ((SFoot.ksb hks4).1 hb))))
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s5 :=
    ⟨⟨Q4, R4, h5.congrX P1.empty_congr⟩, hB5, hX5, hS5', hSg5⟩
  have hfoot := footW_trans (footW_trans F3 (footW_of fu4)) (footW_of fu5)
  have hrb3 : RbIn x3.tcbState := Or.inr rfl
  -- the shadow of the state before the push
  have hdcρ : d'.bv ≠ (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)).curThread := by
    show d'.bv ≠ σ3.curThread; exact hdc3
  set σb := rhoT σa t.bv sc.bv xT yS n with hσb
  have eρa : σb = Notif.stsAct (Notif.updK (rhoT σ3 t.bv sc.bv xT yS n) d'.bv (.tcb x5)) d'.bv := by
    rw [hσb, hσa, stsAct_ne (show d'.bv ≠ (Notif.updK σ3 d'.bv (.tcb x5)).curThread from hdc3),
      rhoT_updK _ (Ne.symm htd') hdsc, stsAct_ne hdcρ]
  have hkd3ρ : (rhoT σ3 t.bv sc.bv xT yS n).kheap d'.bv = some (.tcb x3) := by
    rw [rhoT_kh (Ne.symm htd') hdsc]; exact hkd3
  have Fr5 : CFr e.bv d'.bv σ0 σb := by rw [eρa]; exact Fr3.trans (CFr.stsRun hkd3ρ hrb3)
  have IK5 : IK d'.bv σ0 σb := by
    rw [eρa]; exact (IK3.trans (IK.updSelf (y := x5) hkd3ρ rfl)).trans (IK.sts _ _ _)
  have SK5 : SKeep σ0 σb := by
    rw [eρa]
    exact (SK3.trans (SKeep.updK (p := d'.bv) (o := .tcb x5) (fun y h => ⟨x3, hkd3ρ, by cases h; rfl⟩)
      (fun _ _ h => by cases h))).trans (SKeep.stsAct _ _)
  have hkda : σa.kheap d'.bv = some (.tcb x5) := by rw [hσa, stsAct_kheap]; simp
  have hksca : σa.kheap sc.bv = some (.schedContext yS n) := by
    rw [hσa, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne (Ne.symm hdsc)]; exact hksc3
  have hkta : σb.kheap t.bv = some (.tcb xT) := rhoT_kt hst
  have hkwa : σb.kheap w.bv = some (.reply xr3) := by
    rw [hσb, rhoT_kh hwt hws, hσa, stsAct_kheap]; simp only [updK_kheap, Function.update_of_ne hwd]; exact hkr3
  -- the push from the shadow is the push from the state
  have hpb : pushSt σa t.bv w.bv xr3 xt = pushSt σb t.bv w.bv xr3 xT := by
    have e1 : σb = Notif.updK σa t.bv (.tcb xT) := by
      rw [hσb, rhoT_eq]
      show ({ σa with kheap := Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) sc.bv (some (Fl4Spec.KernelObject.schedContext yS n)) } : Fl4Spec.State Unit) = { σa with kheap := Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) }
      have e2 : Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) sc.bv
          (some (Fl4Spec.KernelObject.schedContext yS n)) = Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) := by
        have e3 : (some (Fl4Spec.KernelObject.schedContext yS n) : Option Fl4Spec.KernelObject) =
            Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT)) sc.bv := by
          rw [Function.update_of_ne (Ne.symm hst)]; exact hksca.symm
        rw [e3, Function.update_eq_self]
      rw [e2]
    rw [e1]
    unfold pushSt
    show Notif.stsAct ({ σa with kheap := Function.update (Function.update σa.kheap w.bv (some (Fl4Spec.KernelObject.reply { xr3 with replyTcb := some t.bv }))) t.bv (some (Fl4Spec.KernelObject.tcb { xt with tcbState := .blockedOnReply w.bv })) } : Fl4Spec.State Unit) t.bv = Notif.stsAct ({ σa with kheap := Function.update (Function.update (Function.update σa.kheap t.bv (some (Fl4Spec.KernelObject.tcb xT))) w.bv (some (Fl4Spec.KernelObject.reply { xr3 with replyTcb := some t.bv }))) t.bv (some (Fl4Spec.KernelObject.tcb { xT with tcbState := .blockedOnReply w.bv })) } : Fl4Spec.State Unit) t.bv
    rw [Function.update_comm (f := σa.kheap) (Ne.symm hwt), Function.update_idem]
    all_goals rfl
  have hIR0 := IpcRel.ofSRN hR5 hS5
  set σ' := pushSt σb t.bv w.bv xr3 xT with hσ'
  have hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σ' := by
    rw [← hpb, ← heq5]; exact hIR0
  -- the scheduler facts
  have hrib : RelIfBound σb d'.bv :=
    Ipc.RelIfBound.of_keep (J0.inv.rd d'.bv xd hkd0 (Or.inr (Or.inr (Or.inr ⟨_, _, _, hstd⟩)))) SK5
  have I5 : Inv σb := ((J0.inv.toBut d'.bv).ik hnqD0 IK5).1.inv fun _ _ _ => hrib
  have hnqTb : ∀ dm p, t.bv ∉ σb.readyQueues dm p := by rw [IK5.2.1, hrq0]; exact hnqT.1
  have hnrTb : t.bv ∉ σb.releaseQueue := by rw [IK5.2.2.1, hsk0.rel]; exact hnqT.2
  have I5' : Inv σ' := ps_inv hkta hkwa hwt I5 hnqTb hnrTb
  have hscA : ∀ p y0 n0, σb.kheap p = some (.schedContext y0 n0) → y0.scTcb = some t.bv →
      Fl4Spec.scActive y0 = true := by
    intro p y0 n0 hp hyt
    by_cases hps : p = sc.bv
    · subst hps; rw [hσb, rhoT_ksc] at hp; cases hp; exact hya
    · have hp0 : σ0.kheap p = some (.schedContext y0 n0) := SK5.2.2.2 _ _ _ hp
      obtain ⟨q0, hqC, eq⟩ := J0.obj.sc p y0 n0 hp0
      subst eq
      obtain ⟨Tr, Cq, hJ⟩ := J0.jpl
      have hq0 := J0.c0 q0 hqC
      have hqS : q0 ∈ P1.Heap.scs H := ⟨_, (hJ.sc q0 y0 n0 hq0 hp0).2⟩
      have hS0' := J0.xtop.fin.1.1.1
      obtain ⟨u, -, -, xu, hku, hxs⟩ := scBack_of hS0' J0.blk.2.2.1 J0.tcbs_eq.1.symm hqC hqS hq0 hp0 hyt
      have hkt0 : σ0.kheap t.bv = some (.tcb xT) := hk0t
      rw [hkt0] at hku; cases hku
      exact absurd (Option.some.inj (hxs.symm.trans hxsc)) hps
  have B5' : BlockedScActive σ' := ps_bsa hkta hkwa hwt hscA (Fr5.bsa J0.bsa)
  have hidT : σb.idleThread ≠ t.bv := by rw [Fr5.sk.idle, hsk0.idle]; exact fun e0 => hit e0.symm
  have hactb : σb.schedulerAction = σ.schedulerAction := by rw [eρa, stsAct_ne hdcρ]; exact hact3
  have hkP : (Notif.updK (Notif.updK σb w.bv (.reply { xr3 with replyTcb := some t.bv })) t.bv
      (.tcb { xT with tcbState := .blockedOnReply w.bv })).kheap t.bv =
      some (.tcb { xT with tcbState := .blockedOnReply w.bv }) := by simp [updK]
  have hschP : Fl4Spec.schedulable t.bv (Notif.updK (Notif.updK σb w.bv (.reply { xr3 with replyTcb := some t.bv }))
      t.bv (.tcb { xT with tcbState := .blockedOnReply w.bv })) = false :=
    Bool.eq_false_iff.2 fun h => by
      obtain ⟨x', -, -, -, h1', -, h3', -⟩ := schedulable_inv h
      rw [hkP] at h1'; cases h1'; simp [Fl4Spec.runnable] at h3'
  have act5 : σ'.schedulerAction = .chooseNewThread := by
    show (pushSt σb t.bv w.bv xr3 xT).schedulerAction = _
    unfold pushSt
    have hc := Fl4Proofs.P3.Sched.stsAct_cur (σ := Notif.updK (Notif.updK σb w.bv
      (.reply { xr3 with replyTcb := some t.bv })) t.bv (.tcb { xT with tcbState := .blockedOnReply w.bv }))
      (t := t.bv) (by show t.bv = σb.curThread; rw [Fr5.sk.ct, hsk0.ct]; exact htc) hschP
    have e1 : (Notif.updK (Notif.updK σb w.bv (.reply { xr3 with replyTcb := some t.bv })) t.bv
        (.tcb { xT with tcbState := .blockedOnReply w.bv })).schedulerAction = σ.schedulerAction := hactb
    rcases stsAct_action (Notif.updK (Notif.updK σb w.bv (.reply { xr3 with replyTcb := some t.bv })) t.bv
        (.tcb { xT with tcbState := .blockedOnReply w.bv })) t.bv with e0 | e0
    · exact e0
    · rcases hres with e' | e'
      · exact absurd (e0.trans (e1.trans e')) hc
      · exact e0.trans (e1.trans e')
  have hAI5 : ActIdle σ' :=
    ⟨fun u hu => (by rw [act5] at hu; cases hu), ps_idleOK hkta hkwa hwt hidT (Fr5.idleOK J0.act.2)⟩
  have hcur5 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := Or.inl act5
  have hrun5 : CurRunM σ' := Or.inl (by rw [act5]; intro e0; cases e0)
  -- the footprints from the base
  have hz7 : SzKeepC Z.C σ σf := SzKeepC.of (SzKeep.of_tcb (p := t.bv) (x' := xt) (fun q hq => hkf q hq) hkt)
  have hWs5 : P1.WritesIn st s s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    hW7.trans1 (hW5'.mono fun b hb => cnW_back hW7.1 hz7 hb)
  have hz0 : SzKeepC Z.C σ0 σ := by
    intro p _ y0 m hp
    by_cases hps : p = sc
    · subst hps; rw [hky] at hp; cases hp; exact ⟨yS, hk0s⟩
    · have hps' : p.bv ≠ sc.bv := fun e0 => hps (P1.eq_of_bv e0)
      have hpt : p.bv ≠ t.bv := fun e0 => by rw [e0, hkx] at hp; cases hp
      exact ⟨y0, by rw [hk0 _ hpt hps']; exact hp⟩
  have hW05 : P1.WritesIn st s0 s5 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s0 σ0) :=
    (writesIn_rebase hWs5 hwB (fun _ h => h)).mono fun b0 hb0 => CnW.back (s := s0) (s' := s) hwB.1.symm hz0 hb0
  have hfs5 := footW_trans (footW_of (W := fun _ => False) hfoot7) hfoot
  have hfoot05 : P1.WritesIn st s0 s5 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s0) :=
    (writesIn_rebase hfs5 hfB (fun _ h => h)).mono fun b0 hb0 => hb0.elim (P1.KW.ksb hfB.1.symm) False.elim
  have hI0 := J0.xtop.irelK J0.ks J0.buf
  have hF : IFrame (L := L) Z.th s0 s5 := IRel.iframe_of hI0 hW05 fun b0 hb0 => CnW.oobj hI0.2.2.1 hb0
  have htDd := J0.not_dead_of_st hdT hkd0 (by rw [hstd]; simp [tsCode])
  have hRR : ∀ q' ∈ Z.R, ∀ xr, σ0.kheap q'.bv = some (.reply xr) → xr.replyTcb = some d'.bv →
      Detached Z.C Lst q' ∧ L.mem s0 (rNextA q') = 0#u64 ∧ L.mem s0 (rPrevA q') = 0#u64 :=
    fun q' hq'' xr hx' hxt' => recvReplyHyp_holds _ Ac Lst D s0 _ σ0 J0 q' hq'' xr d'.bv xd hx'
      hxt' hkd0 (by rw [hstd]; rfl)
  have hcD : ∀ q0 ∈ D, q0.bv ≠ t.bv := fun q0 hq0 e0 => htD (by rw [← P1.eq_of_bv e0]; exact hq0)
  have hwD : ∀ q0 ∈ D, q0.bv ≠ w.bv := fun q0 hq0 e0 => by
    have hqw : q0 = w := P1.eq_of_bv e0
    rw [hqw] at hq0
    have d1 : L.mem s0 (Endp.rTcbA w) = 0#u64 := (J0.jcov.dead w hq0).2.2.2.1 hwH
    obtain ⟨xr', hkr', hxr'⟩ := J0.xtop.irelK J0.ks J0.buf |>.1.toE.reply w hwR
    rw [hk0 _ hwt hws, hkrσ] at hkr'; cases hkr'
    rw [hb', d1, optRef_zero] at hxr'
    cases hxr'
  have hkq : ∀ q0 ∈ D, σ'.kheap q0.bv = σb.kheap q0.bv := fun q0 hq0 => ps_ko (hcD q0 hq0) (hwD q0 hq0)
  have ho : ∀ {q : Fl4Spec.ObjRef} {o : Fl4Spec.KernelObject}, (∀ x, o ≠ .tcb x) → (∀ x, o ≠ .reply x) →
      (σ'.kheap q = some o ↔ σb.kheap q = some o) := fun h1 h2 => ps_oth hkta hkwa hwt h1 h2
  obtain ⟨V', J5⟩ := J0.wake_postGR (by rw [hsk0.arch]; exact hIR) hF hW05 hblk hfoot05 (DWFr.ofCFr Fr5) ps_skD
    (ps_ksub hkta hkwa hwt) (ps_szKeep hkta hkwa hwt) (ps_ykeep hkta hkwa hwt) (ps_mcpKeep hkta hkwa hwt)
    (ps_bufKeep hkta hkwa hwt) (fun d _ h => ps_recvB hkta hkwa hwt h) (ps_ksz hkta hkwa hwt)
    (ps_kback hkta hkwa hwt) (ps_ipcFr hkta hkwa hwt) (ps_ck hkta hkwa hwt) (fun d _ h => ps_free hkta hkwa hwt h)
    (fun q ao h => (ho (fun _ e => by cases e) (fun _ e => by cases e)).2 h) hkq
    I5' B5' hAI5 hcur5 hrun5 (ps_own hkta hkwa hwt ((DWFr.ofCFr Fr5).own ⟨d', hdT, rfl⟩ J0.own))
    (ps_off hkta hkwa hwt ((DWFr.ofCFr Fr5).off J0.off)) (ps_nsc hkta hkwa hwt ((DWFr.ofCFr Fr5).nsc J0.nsc))
    (ps_isorted hkta hkwa hwt ((DWFr.ofCFr Fr5).isorted J0.isorted)) hRR htDd
  -- the tail
  have hk5 : σ'.kheap d'.bv = some (.tcb x5) := by
    rw [ps_ko (Ne.symm htd') (Ne.symm hwd), hσb, rhoT_kh (Ne.symm htd') hdsc]; exact hkda
  have hnr5 : d'.bv ∉ σ'.releaseQueue := by rw [ps_rel, SK5.1]; exact hnqD0.2
  have hact5 : ∀ p y n, x5.tcbSchedContext = some p → σ'.kheap p = some (.schedContext y n) →
      Fl4Spec.scActive y = true := by
    intro p y n hp hy
    have hya' : σb.kheap p = some (.schedContext y n) :=
      (ho (fun _ h => by cases h) (fun _ h => by cases h)).1 hy
    have hy0 := SK5.2.2.2 p y n hya'
    have hp' : xd.tcbSchedContext = some p := by rw [← hsc3]; exact hp
    obtain ⟨y', n', hky', hyt⟩ := J0.inv.back _ _ _ hkd0 hp'
    rw [hy0] at hky'; cases hky'
    exact J0.bsa.tcb p y n d'.bv xd hy0 hyt hkd0 (by rw [hstd]; rfl)
  have hti5 : d'.bv ≠ σ'.idleThread := by
    rw [(ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT)).idle, Fr5.sk.idle, hsk0.idle]
    exact hid
  have htc5 : d'.bv ≠ σ'.curThread := by
    rw [(ps_skD (σ := σb) (t := t.bv) (w := w.bv) (xr := xr3) (xt := xT)).ct, Fr5.sk.ct, hsk0.ct]; exact hdc
  have hspec := sendIpc_faultPush_eq (don := false) hk hkd hde hstd true badge.bv g gr hg e2 hU hkt3 hkd3 hpush hkd4
    (by rw [hft]; simp) (t := t.bv)
  refine WP.spec_mono (J5.sendTailJ hdT hk5 rfl hnr5 hact5 hti5 htc5) ?_
  rintro ⟨s7', a7⟩ ⟨ha7, σ7, h7, Lst7, J7⟩
  simp only at ha7
  subst ha7
  refine ⟨((), σ7), ?_, V', Lst7, J7⟩
  rw [hspec, heq5, hpb]
  show ((), σ7) ∈ (Endp.specWakeTailE d'.bv σ').1
  rw [h7]; exact Set.mem_singleton _



end

end

end Fl4Proofs.P3
