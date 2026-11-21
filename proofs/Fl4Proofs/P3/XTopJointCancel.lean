/-
P3 (DESIGN.md §9), IPC: **`cancel_ipc` at `J` of a thread blocked sending on
an endpoint or waiting on a notification** (`JAtZ.cancelSendJ`,
`JAtZ.cancelNtfnJ`; `jCancel_send`, `jCancel_ntfn`: XTopJointSuspend's
`JCancelAt` for the send and notification states, `JAtZ.suspendJ`'s `hSd`,
`hNt`),
from `JAtZ` before to `JAtZ` after, with no named premise.

* FL4's side: `cancel_ipc_sendF` / `cancel_ipc_ntfnF` (IpcCancelF: the
  spec's outcome, `IRel` after, the footprint `CnW`), the slots kept by
  `IRel.iframe_of` (`CnW.oobj`); P1's `BlkOK` after (`ipc.cancel_ipc.blk`)
  and its footprint `KW` (`ipc.cancel_ipc.kw`).
* The spec's side: the frame `KFr t` (IpcCancelFr: `cancelIpc_send_kfr`,
  `cancelIpc_ntfn_kfr`), `Inv` by `cancel_kb_inv` with `t`'s `RelIfBound`
  carried from `Inv.rd` (`KFr.rib`); the blocked thread's queue from
  `SchedValid` (`sendQ`, `ntfnW`), its queue object in `E`/`N` by
  `ObjCover`.
* `JAtZ.deadP_kfr`: the dead stay dead (`deadP_cfr` for `KFr`: `t`, blocked,
  is not dead; a dead endpoint or notification holds nobody, so is kept).
* `JAtZ.kfrStep`: the assembly (ScSignalBoundJ's `wake_postB` for `KFr`: the
  replies are kept, so `RFree` and `CallRel` carry over directly).
-/
import Fl4Proofs.P3.ScSignalBoundJ
import Fl4Proofs.P3.IpcCancelF
import Fl4Proofs.P3.IpcCancelFr
import Fl4Proofs.P3.XTopJointSuspend
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

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across a `KFr` step** with the footprint `CnW`
(module docstring). -/
theorem JAtZ.deadP_kfr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : KFr t σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ⟨x, F.replyF hx, rfl⟩) (fun x n hx => ⟨x, F.scF hx, Or.inl rfl, Or.inl rfl⟩)
    (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK) F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: kept but for its fault (it is not `t`)
    obtain ⟨st', fl, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
    show st' = x.tcbState
    rcases hs with ⟨e, -⟩ | ⟨e, -⟩
    · exact e
    · exact absurd e (ht q hq)
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
  · -- a dead notification: not waiting, so holding nobody
    obtain ⟨n', hn', e⟩ := J.obj.ntfn q.bv x hx
    have hnq : n' = q := P1.eq_of_bv e
    subst hnq
    obtain ⟨d1, -, -⟩ := hd.2.2.1 (J.zH.2.2.2 n' hn')
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.toN.ntfn n' hn'
    rw [hx] at hk'; cases hk'
    obtain ⟨y, hy, hsc', hbd, hc⟩ := F.ntfnF hx
    have hnw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := by
      intro l e
      have hO := hR.obj
      rw [e] at hO
      exact d1 (by rw [epState_eq]; exact hO.1)
    refine ⟨y, hy, ?_, hbd, Or.inl hsc'⟩
    rcases hc with rfl | hm
    · exact Or.inl rfl
    · exfalso
      cases h : x.ntfnObj with
      | waitingNtfn l => exact hnw l h
      | idleNtfn => rw [h] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm
      | activeNtfn b => rw [h] at hm; simp [Fl4Spec.Ntfn.ntfnQueue] at hm

set_option maxHeartbeats 8000000 in
/-- **A `KFr` step keeps `JAtZ`** (module docstring). -/
theorem JAtZ.kfrStep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : KFr t σ σ') (I3 : Inv σ')
    (hact : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
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
    obtain ⟨e1, e2⟩ := k4 d hd
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨y, F.replyB hy, hyt⟩
    exact ⟨h1, by rw [e2]; exact h2, by rw [e1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hIR.2.2.1
  have hAI3 : ActIdle σ' := by
    refine ⟨fun u hu => ?_, F.idleOK J.act.2⟩
    rcases hact with e1 | e1
    · exact F.sched (J.act.1 u (by rw [← e1]; exact hu))
    · rw [e1] at hu; cases hu
  have hcn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread := fun e0 => by
    rcases hact with e1 | e1
    · rw [e1, e0]
    · exact e1
  have hcur3 : σ'.schedulerAction = .chooseNewThread ∨ CurInv σ' := J.cur.imp hcn F.curInv
  have hrun3 : CurRunM σ' := J.curRun.of_cn F.curRunW hact.symm
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_kfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep ht
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

/-- A blocked thread (state code not `Inactive`) is not dead. -/
theorem JAtZ.notDead (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (h0 : tsCode x.tcbState ≠ 0) :
    ∀ q ∈ D, q.bv ≠ t.bv := by
  intro q hq eq
  have hqt : q = t := P1.eq_of_bv eq
  subst hqt
  have d1 := ((J.jcov.dead q hq).1 (J.zH.1 q ht)).1
  have h3 := ((J.xtop.irelK J.ks J.buf).1.toN.at_tcb ht hk).st
  rw [P1.stA_eq, ← tStA_eq] at d1
  rw [d1] at h3
  unfold sched.TS_INACTIVE at h3
  exact h0 (by rw [← h3]; rfl)

/-- What every `cancel_ipc` at `J` reads of P1: `BlkOK` after and the
footprint `KW`. -/
theorem JAtZ.cancelP1 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    ipc.cancel_ipc st arI s a t ⦃ r => P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H)
      (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac r.1 ∧
      P1.WritesIn st s r.1 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
        (P1.EH H) s) ⦄ := by
  have htH : t ∈ P1.Heap.tcbs H := J.zH.1 t ht
  obtain ⟨⟨Q0, R0, h0⟩, -, ⟨hO, hR, -⟩, -, hSg⟩ := J.blk
  have hreply : L.mem s (P1.stA t) = sched.TS_BLOCKED_ON_REPLY → P1.ReplyT st (P1.Heap.replies H)
      (P1.Heap.scs H) s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t htH hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  refine WP.spec_mono (WP.spec_and (P1.ipc.cancel_ipc.blk s a t J.blk htH)
    (P1.ipc.cancel_ipc.kw s a t h0 htH hO hSg.sub hreply (fun h1 h2 => (hR.recv t htH h1 h2).1))) ?_
  rintro ⟨s1, a1⟩ ⟨h1, h2⟩
  try simp only [WP.uncurry'_pair] at h1 h2
  exact ⟨h1, h2⟩

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` at `J` of a thread blocked sending** (module docstring). -/
theorem JAtZ.cancelSendJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hst : ∃ e d, x.tcbState = .blockedOnSend e d) :
    ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  obtain ⟨e, d, hst⟩ := hst
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xe, hke, hqe⟩ := J.sv.sendQ _ _ _ _ hk hst
  have heE : L.mem s (tBlockA t) ∈ Z.E := by
    obtain ⟨e', he', ee⟩ := J.obj.ep e xe hke
    obtain ⟨y, hy, hyr⟩ := hI.1.tcb t ht
    rw [hk] at hy; cases hy
    have : L.mem s (tBlockA t) = e' := P1.eq_of_bv ((hyr.blkE e (by rw [hst]; rfl)).trans ee.symm)
    rw [this]; exact he'
  have htD := J.notDead ht hk (by rw [hst]; simp [tsCode])
  refine WP.spec_mono (WP.spec_and (cancel_ipc_sendF (ar := arI) J.ip s a σ hI ht hk hst ⟨xe, hke, hqe⟩ heE)
    (J.cancelP1 ht)) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, σ', hc, hIR, hW⟩, hbk, hfoot⟩
  simp only at ea hbk hfoot hIR hW
  subst ea
  have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hc]; exact Set.mem_singleton _
  obtain ⟨F, hk1, hact⟩ := cancelIpc_send_kfr hk hst hke hqe hm
  have I3 := cancel_kb_inv_in J.inv hk (by rw [hst]; rfl) hm hk1 rfl
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', J'⟩ := J.kfrStep hIR hF hW hbk hfoot F I3 hact htD
  exact ⟨rfl, σ', hc, V', Ac, Lst, J'⟩

set_option maxHeartbeats 8000000 in
/-- **`cancel_ipc` at `J` of a thread blocked on a notification** (module
docstring). -/
theorem JAtZ.cancelNtfnJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) (hst : ∃ n, x.tcbState = .blockedOnNotification n) :
    ipc.cancel_ipc st arI s a t ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  obtain ⟨n, hst⟩ := hst
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨xn, hkn, hqn⟩ := J.sv.ntfnW _ _ _ hk hst
  have hnN : L.mem s (tBlockA t) ∈ Z.N := by
    obtain ⟨n', hn', en⟩ := J.obj.ntfn n xn hkn
    obtain ⟨y, hy, hyr⟩ := hI.1.tcb t ht
    rw [hk] at hy; cases hy
    have : L.mem s (tBlockA t) = n' := P1.eq_of_bv ((hyr.blkN n hst).trans en.symm)
    rw [this]; exact hn'
  have htD := J.notDead ht hk (by rw [hst]; simp [tsCode])
  refine WP.spec_mono (WP.spec_and (cancel_ipc_ntfnF (ar := arI) J.ip s a σ hI ht hk hst ⟨xn, hkn, hqn⟩ hnN)
    (J.cancelP1 ht)) ?_
  rintro ⟨s', a'⟩ ⟨⟨ea, σ', hc, hIR, hW⟩, hbk, hfoot⟩
  simp only at ea hbk hfoot hIR hW
  subst ea
  have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) t.bv σ).1 := by rw [hc]; exact Set.mem_singleton _
  obtain ⟨F, -, hact⟩ := cancelIpc_ntfn_kfr hk hst hkn hqn hm
  have hrib := F.rib J.inv hk (Or.inr (Or.inl ⟨n, hst⟩))
  have I3 := cancel_kb_inv J.inv hk (by rw [hst]; rfl) hm hrib
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hW fun b hb => CnW.oobj hI.2.2.1 hb
  obtain ⟨V', J'⟩ := J.kfrStep hIR hF hW hbk hfoot F I3 hact htD
  exact ⟨rfl, σ', hc, V', Ac, Lst, J'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JCancelAt` for a thread blocked sending** (module docstring). -/
theorem jCancel_send {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} :
    JCancelAt (L := L) arI AR th fun ts => ∃ e d, ts = .blockedOnSend e d := by
  intro Z H Cs Ac Lst D s a σ _ J t ht x hk h
  exact J.cancelSendJ ht hk h

/-- **`JCancelAt` for a thread blocked on a notification** (module
docstring). -/
theorem jCancel_ntfn {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} :
    JCancelAt (L := L) arI AR th fun ts => ∃ n, ts = .blockedOnNotification n := by
  intro Z H Cs Ac Lst D s a σ _ J t ht x hk h
  exact J.cancelNtfnJ ht hk h

end

end

end Fl4Proofs.P3
