/-
P3 (DESIGN.md §9), IPC: **`send_signal`'s wake-ups with an SC donation on
`JAtZ`** (toward `SignalRestJHyp`, ScSignalJ): the waiting notification's
head, or the idle notification's bound thread blocked receiving, given the
notification's SC (`maybe_donate_sc`: the thread without an SC, the SC bound
to no thread).

* `JAtZ.deadP_dfr`: the dead stay dead across a `DWFr` step (IpcSignalDonFr)
  with the footprint `CnW`: the woken thread `t` is not dead (it was
  blocked), and an SC whose thread changes is a notification's SC, bound back
  to it (`JAtZ.ntfn_link`), so not dead.
* `JAtZ.wake_postD`: `JAtZ.wake_postB` (ScSignalBoundJ) in the frame `DWFr`.
* `JAtZ.signal_waitDJ`, `JAtZ.signal_boundDJ`: the two wake-ups with or
  without a donation: FL4's side `send_signal_wait_irelD`,
  `send_signal_bound_irelD` (IpcSignalDon), the spec's `wake_specG`
  (IpcSignalDonSpec), then `wake_postD`; with the platform's `MIN_BUDGET`
  [P] (`hmb`, as IpcCapJ). The donated SC may be the current SC (unowned
  after its thread unbound it, a reschedule pending, then a TCB timer's
  notification signalled in `schedule`'s prelude): the woken thread then owns
  it (`CurOwnT`, `CurOwnW`'s owner), not postponed while time is consumed
  (`OffOK`: the head refill ready and sufficient).
-/
import Fl4Proofs.P3.ScSignalBoundJ
import Fl4Proofs.P3.IpcSignalDon
import Fl4Proofs.P3.IpcSignalDonSpec
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A notification's SC is not dead (bound back to the notification,
`JAtZ.ntfn_link`; a dead SC's notification word is `0`). -/
theorem JAtZ.ntfnSc_not_dead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} {y : Fl4Spec.SchedContext}
    {k : Nat} (hq : σ.kheap q.bv = some (.schedContext y k)) {o : Fl4Spec.ObjRef} {xo : Fl4Spec.Notification}
    (ho : σ.kheap o = some (.notification xo)) (hsc : xo.ntfnSc = some q.bv) : ¬ DeadP (L := L) H s q := by
  intro hd
  obtain ⟨n', hn', en⟩ := J.obj.ntfn o xo ho
  subst en
  obtain ⟨y', m', hky, hyn⟩ := J.ntfn_link hn' xo q.bv ho hsc
  rw [hq] at hky; cases hky
  obtain ⟨c', hc', ec⟩ := J.obj.sc q.bv y k hq
  have hcq : c' = q := P1.eq_of_bv ec
  subst hcq
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  obtain ⟨-, hH⟩ := hJ.sc c' y k (J.c0 c' hc') hq
  obtain ⟨-, -, d3, -⟩ := hd.2.2.2.2 _ hH
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, m, hkx, hR⟩ := hs.scs c' hc'
  rw [hq] at hkx; cases hkx
  have h1 := hR.ntfn
  rw [scW_ntfn] at h1
  rw [show L.mem s (scNtfnA c') = 0#u64 from d3, optRef_zero, hyn] at h1
  cases h1

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `DWFr` step** with the footprint `CnW`
(`deadP_cfr`; `t` was blocked, so not dead; an SC whose thread changes is a
notification's SC, so not dead). -/
theorem JAtZ.deadP_dfr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r t : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : DWFr r t σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state, (null) bound notification and SC kept
    obtain ⟨t', ht', e⟩ := J.obj.tcb q.bv x hx
    have htq : t' = q := P1.eq_of_bv e
    subst htq
    obtain ⟨-, -, d3, -, -⟩ := hd.1 (J.zH.1 t' ht')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t' ht'
    rw [hx] at hk'; cases hk'
    have hbn : x.tcbBoundNotification = none := by
      rw [hR.bound, show tBoundA t' = P1.boundA t' from rfl, d3, optRef_zero]
    obtain ⟨st', bn, fl, ar, sc, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, ?_, ?_⟩
    · show st' = x.tcbState
      rcases hs with ⟨⟨e, -⟩ | ⟨-, e, -⟩, -, -⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e] at h0; simp [tsCode] at h0
      · exact absurd e (ht t' hq)
    · show bn = x.tcbBoundNotification
      rcases hs with ⟨-, -, e | e⟩ | ⟨-, e, -⟩
      · exact e
      · rw [e, hbn]
      · exact absurd e (ht t' hq)
    · show sc = x.tcbSchedContext ∨ sc = none
      by_cases e : sc = x.tcbSchedContext
      · exact Or.inl e
      · exact absurd (F.tsc _ x _ hx hk3 e).1 (ht t' hq)
  · -- a dead endpoint: idle, so holding nobody
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | ⟨-, hm⟩
    · exact hy
    · exfalso
      obtain ⟨e', he', e⟩ := J.obj.ep q.bv x hx
      have heq : e' = q := P1.eq_of_bv e
      subst heq
      have d2 := hd.2.1 (J.zH.2.1 e' he')
      obtain ⟨x', hk', hO⟩ := J.xtop.ipc.toE.ep e' he'
      rw [hx] at hk'; cases hk'
      rw [epState_eq] at d2
      cases x with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hm
      | sendEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
      | recvEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
  · -- a dead notification: not waiting, unbound
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, d2, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, -, hobj, hbd, hsc'⟩ := F.ntfnF hx
    have hbn : x.ntfnBoundTcb = none := by
      rw [hR.bound, show nBoundA n' = P1.ntfnBtA n' from rfl, d2, optRef_zero]
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, (hobj hnw).imp id And.right, ?_, hsc'⟩
    rcases hbd with e | e
    · exact e
    · rw [e, hbn]
  · -- a dead reply: naming nobody
    obtain ⟨y, hy, -, hc⟩ := F.replyF hx
    refine ⟨y, hy, ?_⟩
    rcases hc with e | ⟨hxt, -⟩
    · exact e
    · exfalso
      obtain ⟨r', hr', e⟩ := J.obj.reply q.bv x hx
      have heq : r' = q := P1.eq_of_bv e
      subst heq
      have d4 := hd.2.2.2.1 (J.zH.2.2.1 r' hr')
      obtain ⟨x', hk', hx'⟩ := J.xtop.ipc.toE.reply r' hr'
      rw [hx] at hk'; cases hk'
      have d4' : L.mem s (Endp.rTcbA r') = 0#u64 := d4
      rw [hx', d4', optRef_zero] at hxt
      cases hxt
  · -- an SC: its thread kept (a changed one is a notification's SC, not dead), its notification kept or cut
    obtain ⟨rf, nt, tc, hk3, -, hn⟩ := F.scF hx
    refine ⟨_, hk3, ?_, hn⟩
    show tc = x.scTcb ∨ tc = none
    by_cases e : tc = x.scTcb
    · exact Or.inl e
    · obtain ⟨-, o, xo, ho, hsc⟩ := F.scb q.bv x n _ n hx hk3 e
      exact absurd hd (J.ntfnSc_not_dead hx ho hsc)

set_option maxHeartbeats 8000000 in
/-- **A wake with or without a donation keeps `JAtZ`** (`wake_postB` in the
frame `DWFr`). -/
theorem JAtZ.wake_postD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n t : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : DWFr n t σ σ') (I3 : Inv σ') (B3 : BlockedScActive σ') (hAI3 : ActIdle σ')
    (hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') (hrun3 : CurRunM σ')
    (hRR : ∀ d ∈ Z.R, ∀ xr, σ.kheap d.bv = some (.reply xr) → xr.replyTcb = some t →
      Detached Z.C Lst d ∧ L.mem s (rNextA d) = 0#u64 ∧ L.mem s (rPrevA d) = 0#u64)
    (ht : ∀ q ∈ D, q.bv ≠ t) (htT : ∃ u ∈ Z.T, u.bv = t) :
    ∃ V' : XVs, JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s' a σ' := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hIR hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s') Z.R Z.C σ' Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s') Z.R Z.C σ' Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨x, hx, -, hc⟩ := F.replyB hy
    obtain ⟨e1, e2⟩ := k4 d hd
    rcases hc with e | ⟨hxt, -⟩
    · obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨x, hx, e ▸ hyt⟩
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
    · obtain ⟨h1, h2, h3⟩ := hRR d hd x hx hxt
      exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_dfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep ht
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own htT J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

/-- A thread in a state other than `inactive` is not dead. -/
theorem JAtZ.not_dead_of_st (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (htT : t ∈ Z.T)
    {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hst : tsCode xt.tcbState ≠ 0) :
    ∀ q ∈ D, q.bv ≠ t.bv := by
  intro q hq eq
  have hqt : q = t := P1.eq_of_bv eq
  subst hqt
  have d1 := ((J.jcov.dead q hq).1 (J.zH.1 q htT)).1
  have hI := J.xtop.irelK J.ks J.buf
  have h3 := (hI.1.toN.at_tcb htT hkt).st
  rw [P1.stA_eq, ← tStA_eq] at d1
  rw [d1] at h3
  unfold sched.TS_INACTIVE at h3
  exact hst (by rw [← h3]; rfl)

set_option maxHeartbeats 8000000 in
/-- **A waiting notification signalled, donating or not, keeps `JAtZ`**
(module docstring). -/
theorem JAtZ.signal_waitDJ (hAT : P0.ArchTotal arI)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) {l : List Fl4Spec.ObjRef} (ho : x.ntfnObj = .waitingNtfn l)
    (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hbl := (J.sv.ntfnQ n.bv x hk).2
  refine WP.spec_mono (WP.spec_and (send_signal_wait_irelD J.ip hmb s a σ hI J.inv J.nsc hn hk ho hbl badge)
    (P1.notification.send_signal.tinvF hAT s a n badge J.blk hnH (hNt n hnH))) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, d, xd, σd, σ', hmq, hkd, hxs, hdon, hsend, hmw, hIR, hF, hFS⟩, hb⟩
  try simp only [WP.uncurry'_pair] at hb
  obtain ⟨hb, -, hfoot⟩ := hb
  have hfoot := hfoot (J.donCore hn)
  subst ea
  have hdn : d.bv ≠ n.bv := by intro e; rw [e, hk] at hkd; cases hkd
  set σ1 := updK σ n.bv (.notification (afterDequeue x d)) with hσ1
  have hk1 : σ1.kheap d.bv = some (.tcb xd) := by simp [hσ1, updK, hdn, hkd]
  have hkn1 : σ1.kheap n.bv = some (.notification (afterDequeue x d)) := by simp [hσ1, updK]
  have hkp1 : ∀ p, p ≠ n.bv → σ1.kheap p = σ.kheap p := fun p hp => by simp [hσ1, updK, hp]
  have hsub : (afterDequeue x d).ntfnObj.ntfnQueue.Sublist x.ntfnObj.ntfnQueue := by
    show (match Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x) with
      | [] => Fl4Spec.Ntfn.idleNtfn
      | _ => Fl4Spec.Ntfn.waitingNtfn (Fl4Spec.removeAll d.bv (Fl4Spec.ntfnQueueOf x))).ntfnQueue.Sublist
        (Fl4Spec.ntfnQueueOf x)
    split
    · exact List.nil_sublist _
    · unfold Fl4Spec.removeAll; apply List.filter_sublist
  have F1 : NFr false n.bv σ σ1 :=
    NFr.upd hk (Or.inr (Or.inr ⟨x, afterDequeue x d, rfl, rfl, rfl, hsub, (fun h => by cases h), Or.inl rfl,
      fun hw => absurd ho (hw l), Or.inl rfl⟩))
  have hI1 : Inv σ1 := J.inv.updNtfn hk (fun p hp => J.inv.ntfnSc n.bv x p hk hp)
  have hAI1 : ActIdle σ1 := ⟨fun u hu => F1.sched (J.act.1 u hu), F1.idleOK J.act.2⟩
  have hcur1 : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := Or.imp id F1.curInv J.cur
  have hrun1 : CurRunM σ1 := Or.imp id F1.curRunW J.curRun
  have hoff1 : OffOK σ1 := F1.off J.off
  have hsp1 : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → Fl4Spec.scActive y = true := by
    intro c y k hc
    have hcn : c ≠ n.bv := by rintro rfl; rw [hkn1] at hc; cases hc
    rw [hkp1 c hcn] at hc
    exact J.sv.scSpor c y k hc
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specG hI1 (wake_inv3 hI1 hk1 hxs badge.bv) (F1.bsa J.bsa) hAI1
    hcur1 hrun1 hk1 (by rw [hxs]; rfl) (CFr.ofNFr (wake_f3 hk1 hxs badge.bv)) hkn1 hoff1 hsp1 hdon hmw
  have FF : DWFr n.bv d.bv σ σ' := (DWFr.ofNFr F1).trans F2
  have hdT : d ∈ Z.T := by
    obtain ⟨t', ht', e⟩ := J.obj.tcb d.bv xd hkd
    rw [← P1.eq_of_bv e]; exact ht'
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) := hFS.1.mono fun b h => Or.inl h
  have hRR : ∀ q ∈ Z.R, ∀ xr, σ.kheap q.bv = some (.reply xr) → xr.replyTcb = some d.bv →
      Detached Z.C Lst q ∧ L.mem s (rNextA q) = 0#u64 ∧ L.mem s (rPrevA q) = 0#u64 := by
    intro q _ xr hq hxt
    exfalso
    obtain ⟨x', hk', hs'⟩ := J.sv.replyTcb q.bv xr d.bv hq hxt
    rw [hkd] at hk'; cases hk'
    rcases hs' with e | ⟨ep, dd, e⟩ <;> rw [hxs] at e <;> cases e
  have htD := J.not_dead_of_st hdT hkd (by rw [hxs]; simp [tsCode])
  obtain ⟨V', J'⟩ := J.wake_postD hIR hF hw hb hfoot FF I' B' AI' cur' run' hRR htD ⟨d, hdT, rfl⟩
  exact ⟨σ', V', Ac, Lst, D, hsend, FF.sk.dt, J'⟩

set_option maxHeartbeats 8000000 in
/-- **The idle notification's bound receiver woken, donating or not, keeps
`JAtZ`** (module docstring; `JAtZ.signal_boundJ` with `wake_specG`). -/
theorem JAtZ.signal_boundDJ (hAT : P0.ArchTotal arI) (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification}
    (hk : σ.kheap n.bv = some (.notification x)) (hidle : x.ntfnObj = .idleNtfn) {t : U64} {tcb : Fl4Spec.Tcb}
    (hb : x.ntfnBoundTcb = some t.bv) (hkt : σ.kheap t.bv = some (.tcb tcb))
    (hrb : Fl4Spec.receiveBlocked tcb.tcbState = true) (badge : U64) :
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hNt : ∀ m ∈ P1.Heap.ntfns H, H m = some .ntfn := fun _ h => h
  have hnH : n ∈ P1.Heap.ntfns H := J.zH.2.2.2 n hn
  have hx := J.xtop.ipc.toN.at_ntfn hn hk
  obtain ⟨hb0, hbt⟩ := Notif.optRef_some (hx.bound ▸ hb)
  have htU : L.mem s (nBoundA n) = t := P1.eq_of_bv hbt
  have htT : t ∈ Z.T := htU ▸ hx.bound_mem hb0
  obtain ⟨e, ro, d, hst⟩ : ∃ e ro d, tcb.tcbState = .blockedOnReceive e ro d := by
    cases h : tcb.tcbState <;> simp [h, Fl4Spec.receiveBlocked] at hrb
    exact ⟨_, _, _, rfl⟩
  have hCR : ∀ t', t' = t → CancelRecvHyp Z.E (L.mem s) σ t' tcb := fun t' et => et ▸
    cancelRecvHyp_of hI.1.toE J.sv J.obj J.inv htT hkt hrb
  have hCR0 := hCR t rfl
  obtain ⟨xe, hke, hqe⟩ := hCR0.ok.2.1 _ ro d hst
  have hro : ∀ rp, ro = some rp → ∃ xr, σ.kheap rp = some (.reply xr) ∧ xr.replyTcb = some t.bv := fun rp er => by
    subst er; exact hCR0.ok.2.2.1 _ rp d hst
  have hrbI : RbIn tcb.tcbState := Or.inl ⟨_, _, _, hst⟩
  have post1 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      CFr n.bv t.bv σ σ1 ∧ Inv σ1 ∧ ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by
    intro σ1 x1 hc hk1 hin hrib
    have hm : ((), σ1) ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hc]; exact Set.mem_singleton _
    obtain ⟨F1, -, -⟩ := cancelIpc_recv_cfr (r := n.bv) hkt hst hke hqe hro hm
    exact ⟨F1, cancel_recv_inv J.inv hkt hrbI hm hrib, hm⟩
  have hA3 : ∀ σ1 x1, Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ1)}, False) →
      σ1.kheap t.bv = some (.tcb x1) → x1.tcbState = .inactive → RelIfBound σ1 t.bv →
      Inv (wakeSt3 σ1 t.bv x1 badge.bv) ∧ NSC Z.N Z.C σ1 ∧ ∀ dd pp, t.bv ∉ σ1.readyQueues dd pp := by
    intro σ1 x1 hc hk1 hin hrib
    obtain ⟨F1, hI1, -⟩ := post1 σ1 x1 hc hk1 hin hrib
    exact ⟨wake_inv3B hI1 hk1 hin hrib badge.bv, F1.nsc J.nsc, (hI1.notQueued hk1 (by rw [hin]; rfl)).1⟩
  refine WP.spec_mono (WP.spec_and (send_signal_bound_irelD J.ip hmb s a σ hI hn hk hidle hb hkt hrb badge hCR hA3)
    (P1.notification.send_signal.tinvF hAT s a n badge J.blk hnH (hNt n hnH))) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, s1, σ1, σd, σ', x1, hc, hk1, hin, hrib, hX1, hF1, hW1, hdon, hsend, hmw, hIR, hF2, hFS⟩,
    hbk⟩
  try simp only [WP.uncurry'_pair] at hbk
  obtain ⟨hbk, -, hfoot⟩ := hbk
  have hfoot := hfoot (J.donCore hn)
  subst ea
  obtain ⟨F1, hI1, hm1⟩ := post1 σ1 x1 hc hk1 hin hrib
  obtain ⟨-, hk1', hact1⟩ := cancelIpc_recv_cfr (r := n.bv) hkt hst hke hqe hro hm1
  have hB1 := F1.bsa J.bsa
  have hAI1 : ActIdle σ1 := by
    refine ⟨fun u hu => ?_, F1.idleOK J.act.2⟩
    rcases hact1 with e1 | e1
    · exact F1.sched (J.act.1 u (by rw [← e1]; exact hu))
    · rw [e1] at hu; cases hu
  have hcn : σ.schedulerAction = .chooseNewThread → σ1.schedulerAction = .chooseNewThread := fun e0 => by
    rcases hact1 with e1 | e1
    · rw [e1, e0]
    · exact e1
  have hcur1 : σ1.schedulerAction = .chooseNewThread ∨ CurInv σ1 := J.cur.imp hcn F1.curInv
  have hrun1 : CurRunM σ1 := J.curRun.of_cn F1.curRunW hact1.symm
  obtain ⟨xn1, hkn1, -⟩ := F1.ntfnF hk
  have hoff1 : OffOK σ1 := F1.off J.off
  have hsp1 : ∀ c y k, σ1.kheap c = some (.schedContext y k) → y.scSporadic = true → Fl4Spec.scActive y = true := by
    intro c y k hc
    obtain ⟨y0, rf, nt, hy0, rfl, -⟩ := F1.scB hc
    exact J.sv.scSpor c y0 k hy0
  obtain ⟨I', B', F2, AI', cur', run'⟩ := wake_specG hI1 (wake_inv3B hI1 hk1 hin hrib badge.bv) hB1 hAI1 hcur1
    hrun1 hk1 (by rw [hin]; rfl) (wake_f3B hk1 hin badge.bv) hkn1 hoff1 hsp1 hdon hmw
  have FF : DWFr n.bv t.bv σ σ' := (DWFr.ofCFr F1).trans F2
  have hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ) :=
    (hW1.trans (hFS.1.mono fun b hb => FinW.back hW1.1 (SzKeepC.of F1.szKeep) hb)).mono
      fun b h => h.elim id Or.inl
  have hRR : ∀ q ∈ Z.R, ∀ xr, σ.kheap q.bv = some (.reply xr) → xr.replyTcb = some t.bv →
      Detached Z.C Lst q ∧ L.mem s (rNextA q) = 0#u64 ∧ L.mem s (rPrevA q) = 0#u64 :=
    fun q hq xr hx' hxt => recvReplyHyp_holds Z Ac Lst D s _ σ J q hq xr t.bv tcb hx' hxt hkt hrb
  have htD := J.not_dead_of_st htT hkt (by rw [hst]; simp [tsCode])
  obtain ⟨V', J'⟩ := J.wake_postD hIR (hF1.trans hF2) hw hbk hfoot FF I' B' AI' cur' run' hRR htD ⟨t, htT, rfl⟩
  exact ⟨σ', V', Ac, Lst, D, hsend, FF.sk.dt, J'⟩

end

end

end Fl4Proofs.P3
