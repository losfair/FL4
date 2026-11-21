/-
P3 (DESIGN.md §9), IPC: **an `RSFr` step keeps `JAtZ`** (toward
XTopJointRecvIpcLink's `JRecvSendHyp`: `receive_ipc` from a waiting sender
at `J`, KENTRY-PLAN.md item 6 (d)).

* `JAtZ.deadP_rsfr`: the dead stay dead across IpcRecvSendFr's `RSFr t r`
  (XTopJointCancel's `deadP_kfr`: `t`, blocked, is not dead; a dead
  endpoint holds nobody; a dead TCB keeps its state; SCs change only their
  refills).
* `JAtZ.rsfrStep`: XTopJointCancel's `JAtZ.kfrStep` for `RSFr` (the replies
  and notifications are kept, so `RFree`, `CallRel` and `NSC` carry over
  directly).
-/
import Fl4Proofs.P3.IpcRecvSendFr
import Fl4Proofs.P3.XTopJointCancel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- The receive-from-sender step's object changes keep what the IPC-buffer
fields read (a TCB's state and registers only, an SC's refills, an endpoint). -/
theorem Sched.RSChg.objFrK {t r cur p : Fl4Spec.ObjRef} {o o' : Fl4Spec.KernelObject}
    (h : Sched.RSChg t r cur p o o') : IpcFrKeep.ObjFrK o o' := by
  rcases h with ⟨_, _, _, rfl, rfl, -⟩ | ⟨_, _, _, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, -, -⟩
  · exact IpcFrKeep.objFrK_tcb rfl rfl
  · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)
  · exact IpcFrKeep.objFrK_other (fun _ e => by cases e) (fun _ e => by cases e) (fun _ e => by cases e)

theorem Sched.RSFr.ipcFr {t r : Fl4Spec.ObjRef} {σ σ' : Fl4Spec.State Unit} (F : Sched.RSFr t r σ σ') :
    IpcFrKeep σ σ' :=
  IpcFrKeep.of_chg F.kh fun _ _ _ h => h.objFrK

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an `RSFr` step** with the footprint `CnW`
(module docstring). -/
theorem JAtZ.deadP_rsfr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t r : Fl4Spec.ObjRef} {s3 : S}
    {σ3 : Fl4Spec.State Unit} (F : RSFr t r σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3)
    (ht : ∀ q ∈ D, q.bv ≠ t) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ⟨x, F.ntfnF hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, F.replyF hx, rfl⟩)
    (fun x n hx => by obtain ⟨rf, h1, -⟩ := F.scF hx; exact ⟨_, h1, Or.inl rfl, Or.inl rfl⟩)
    (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK) F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: its state kept (it is not `t`)
    obtain ⟨st', ar, hk3, hs⟩ := F.tcbF hx
    refine ⟨_, hk3, ?_, rfl, Or.inl rfl⟩
    show st' = x.tcbState
    rcases hs.2 with e | ⟨e, -⟩
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

set_option maxHeartbeats 8000000 in
/-- **An `RSFr` step keeps `JAtZ`** (module docstring). -/
theorem JAtZ.rsfrStep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t r : Fl4Spec.ObjRef}
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hIR : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hF : IFrame (L := L) Z.th s s') (hw : P1.WritesIn st s s' (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H)
      (P1.EH H) s))
    (F : RSFr t r σ σ') (I3 : Inv σ')
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
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_rsfr F hS3 hIR.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep ht
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, F.bsa J.bsa, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) F.szKeep hF.1
    F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD⟩

end

end

end Fl4Proofs.P3
