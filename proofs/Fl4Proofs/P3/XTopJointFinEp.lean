/-
P3 (DESIGN.md §9), IPC: **`JAtZ` across a final endpoint cap's
finalisation** (toward `JStepHyps.del`, as XTopJointFin for notifications):
FL4's `cancel_all_ipc` against the spec's `finalise_cap` of the endpoint cap,
from `JAtZ` before to `JAtZ` after at the sets `Z.mv Z.G V'` (the slots kept,
the VSpace sets fresh).

* FL4's side: IpcCancelAllIpc's `cancel_all_ipc_irel` (`IRel` after, the
  slots kept, the footprint `CnStep`: `FinW`, the endpoints' two words, the
  replies' `TCB` words), its queued threads blocked on the endpoint
  (`ep_queue_blocked`).
* The spec's side: IpcFinEpInv's `inv_cancelAllIpc` (`Inv`,
  `BlockedScActive`, the frame `EFr` with `P = RecvAt σ`: a freed reply named
  a thread blocked receiving at the start).
* `JAtZ.deadP_efr`: the dead stay dead (a dead TCB is inactive, so blocked
  on nothing; a dead endpoint is idle; a dead reply names nothing).
* `JAtZ.finEpJ`: `JAtZ` after: `XTopAt` (`XTopAt.irel_same`), the kinds kept
  (`EFr.kback`), `JCs`, and `JRest`: the FL4 frame words from `CnW`
  (ScSignalBoundJ's `cnW_keeps`, `cnW_irq`, `cnW_utc`), `CallRel` from the
  call stacks, `reply_sc` and the reply links, `RFree` for a freed reply by
  `RecvReplyHyp` (`recvReplyHyp_holds`) (ScSignalBoundJ: a reply naming a thread blocked
  receiving is detached and unlinked, l4v `valid_replies`), core 0's debug
  word (P1's `KW`), P1's `BlkOK` (`fin_cap_ep.slots`).
-/
import Fl4Proofs.P3.IpcFinEpInv
import Fl4Proofs.P3.ScSignalBoundJ
import Fl4Proofs.P3.JProducers
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

/-- A thread blocked receiving at `σ`. -/
def RecvAt (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) : Prop :=
  ∃ xt, σ.kheap t = some (.tcb xt) ∧ Fl4Spec.receiveBlocked xt.tcbState = true

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **The dead stay dead across an `EFr` step** with the footprint `CnW`
(`deadP_cfr` for `EFr`). -/
theorem JAtZ.deadP_efr (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {e : Fl4Spec.ObjRef}
    {P : Fl4Spec.ObjRef → Prop} {s3 : S} {σ3 : Fl4Spec.State Unit} (F : EFr e P σ σ3)
    (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3) (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (CnW (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx h0 => ?_) (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    (fun x n hx => ?_) (fun hqC => k3 q hqC) (fun z hz hqC K hK8 hK => J.cnW_scOut hw hz hqC hK8 hK)
    F.sk.idle hAS hY3 (hYK.dk q.bv) hd
  · -- a dead TCB: inactive, so blocked on nothing; kept
    obtain ⟨st', hk3, hs⟩ := F.tcbF hx
    have hst : st' = x.tcbState := hs.st (fun hb => by
      rcases epBlocked_some hb with ⟨d, h⟩ | ⟨ro, d, h⟩ <;> rw [h] at h0 <;> simp [tsCode] at h0)
    subst hst
    exact ⟨_, hk3, rfl, rfl, Or.inl rfl⟩
  · -- a dead endpoint: idle, so kept
    obtain ⟨y, hy, hc⟩ := F.epF hx
    rcases hc with rfl | ⟨hne, -⟩
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
      | idleEP => exact hne rfl
      | sendEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
      | recvEP l => have := hO.1; rw [d2] at this; exact absurd this (by decide)
  · -- a dead notification: kept
    exact ⟨x, F.othF hx (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e), Or.inl rfl, rfl, Or.inl rfl⟩
  · -- a dead reply: naming nobody, so kept
    obtain ⟨y, hy, -, hc⟩ := F.replyF hx
    refine ⟨y, hy, ?_⟩
    rcases hc with e | ⟨⟨t, hxt, -⟩, -⟩
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
  · -- an SC: its thread and notification kept
    obtain ⟨rf, hk3, -⟩ := F.scF hx
    exact ⟨_, hk3, Or.inl rfl, Or.inl rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a final endpoint cap's finalisation** (module
docstring): at `Z.mv Z.G V'`, the dead set and P1's sets kept. From
`RecvReplyHyp` (`recvReplyHyp_holds`). -/
theorem JAtZ.finEpJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {e b : U64} {x1 x2 x3 x4 : Bool} (he : e ∈ Z.E) :
    objects.finalise_cap st arI s a (.Endpoint e b x1 x2 x3 x4) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧ ∃ σ' V',
        ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Endpoint e b x1 x2 x3 x4)) true σ).1 ∧
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D res.2.1 res.2.2 σ' ∧ KBack σ σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ∧ L.ksb res.2.1 = L.ksb s ⦄ := by
  have hpH : H e = some .ep := J.zH.2.1 e he
  have hI := J.xtop.irelK J.ks J.buf
  have hpre := J.epFinPre.2.2.1 e he
  have hfc : objects.finalise_cap st arI s a (.Endpoint e b x1 x2 x3 x4) true false =
      objects.finalise_cap_object st arI s a (.Endpoint e b x1 x2 x3 x4) true := by
    simp [objects.finalise_cap]
  have hp3 : objects.finalise_cap st arI s a (.Endpoint e b x1 x2 x3 x4) true false ⦃ res =>
      res.1 = (capability.Cap.Null, capability.Cap.Null) ∧ res.2.2 = a ∧ ∃ σ3,
        ((), σ3) ∈ (Fl4Spec.cancelAllIpc (Z := Unit) e.bv σ).1 ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c res.2.1 σ3 ∧
        IFrame (L := L) Z.th s res.2.1 ∧ Ipc.CnStep (st := st) Z.T Z.N Z.C Z.E Z.R Z.c s σ res.2.1 σ3 ⦄ := by
    rw [hfc]
    unfold objects.finalise_cap_object
    simp only [↓reduceIte]
    refine WP.spec_bind (cancel_all_ipc_irel J.ip s σ hI he hpre) ?_
    rintro s3 ⟨σ3, hm3, hI3, hF3, hC3⟩
    rw [WP.spec_ok]
    exact ⟨rfl, rfl, σ3, hm3, hI3, hF3, hC3⟩
  refine WP.spec_mono (WP.spec_and hp3
    (P1.fin_cap_ep.slots (ar := arI) s a e b x1 x2 x3 x4 true false J.blk hpH)) ?_
  rintro ⟨⟨rem, cl⟩, s3, a3⟩ ⟨⟨e1, e2, σ3, hm3, hI3, hF, hCS⟩, -, hblk, hfoot, -⟩
  simp only at e1 e2 hm3 hI3 hF hCS hblk hfoot ⊢
  -- the spec
  have hbl : ∀ x, σ.kheap e.bv = some (.endpoint x) → ∀ u ∈ x.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧
      Fl4Spec.epBlocked xu.tcbState = some e.bv ∧ (Fl4Spec.receiveBlocked xu.tcbState = true → RecvAt σ u) := by
    intro x hx u hu
    obtain ⟨xu, hku, hb⟩ := ep_queue_blocked J.ip hI he hx hu
    exact ⟨xu, hku, hb, fun hr => ⟨xu, hku, hr⟩⟩
  obtain ⟨I3, B3, F, hact⟩ := inv_cancelAllIpc (P := RecvAt σ) J.inv J.bsa hpre hbl hm3
  have hmem : ((absCap capability.Cap.Null, absCap capability.Cap.Null), σ3) ∈
      (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Endpoint e b x1 x2 x3 x4)) true σ).1 := by
    show _ ∈ (Fl4Spec.NonDet.liftM (fun _ => (Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap)) (Fl4Spec.NonDet.when true
      (Fl4Spec.cancelAllIpc e.bv)) σ).1
    unfold Fl4Spec.NonDet.liftM Fl4Spec.NonDet.when
    simp only [↓reduceIte]
    exact mem_bind_nd (x := ((), σ3)) hm3 (Set.mem_singleton _)
  have hck := finEp_nkc e.bv b.bv _ true σ _ hmem
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 (a' := a3) (by rw [e2]; exact hAR) hF.1 hck.cdt hck.orig hck.ks
    hF.2
  have hks : L.ksb s3 = L.ksb s := hF.2
  have hw := hCS.1
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.cnW_keeps hw
  have ck := F.callKeep
  have hCR' : CallRel (L.mem s3) Z.R Z.C σ3 Lst :=
    J.call.frame k3 k4 (fun q _ y n hy => ck.1 _ y n hy) (fun d _ x hx => ck.2.1 _ x hx)
  have hRP' := J.rp.frame hks ck.2.2
  have hRF' : RFree (L.mem s3) Z.R Z.C σ3 Lst := by
    intro d hd hfd
    obtain ⟨y, hy, hyt⟩ := hfd
    obtain ⟨x, hx, -, hc⟩ := F.replyB hy
    obtain ⟨r1, r2⟩ := k4 d hd
    rcases hc with e' | ⟨⟨t, hxt, xt, hkt, hrb⟩, -⟩
    · obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨x, hx, e' ▸ hyt⟩
      exact ⟨h1, by rw [r2]; exact h2, by rw [r1]; exact h3⟩
    · obtain ⟨h1, h2, h3⟩ := recvReplyHyp_holds Z Ac Lst D s a σ J d hd x t xt hx hxt hkt hrb
      exact ⟨h1, by rw [r2]; exact h2, by rw [r1]; exact h3⟩
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hI3.2.2.1
  -- the scheduler fields
  have hAI3 : ActIdle σ3 := by
    rcases hact with e' | e'
    · exact ⟨fun t ht => (by rw [e'] at ht; cases ht), F.idleOK J.act.2⟩
    · rw [e']; exact J.act
  have hcur3 : σ3.schedulerAction = .chooseNewThread ∨ CurInv σ3 := by
    rcases hact with e' | e'
    · exact Or.inl e'
    · rw [e']; exact J.cur
  have hrun3 : CurRunM σ3 := by
    rcases hact with e' | e'
    · exact Or.inl (act_cn_nr e')
    · rw [e']; exact J.curRun
  -- the dead stay dead
  have hdead : ∀ q ∈ D, DeadP (L := L) H s3 q := J.deadP_efr F hS3 hI3.1 hw k3 hAI3.1 (J.yld.frame k2 F.ykeep) F.ykeep
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s3 σ3 := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => F.szKeep q.bv y n hq) hks (J.cnW_irq hw)
      (J.idleW_keep hS3 F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS3 F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)) hDbg
    (D' := D)
  have hRR' := J.rrecv.frame k4 F.khrb
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac Lst D s3 σ3 :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 F.sk.idle F.sk.isc), hkern,
      J.cnW_utc hw hF.1 F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, I3, hcur3, F.own J.own, F.off J.off,
      hAI3, B3, F.isorted J.isorted, hrun3, hblk⟩
  have hC0 := JCs.same J hF.1 F.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s3 σ3 := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨e1, e2, σ3, Z.vs, hmem, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD, F.kback, hF.1, hks⟩

end

end

end Fl4Proofs.P3
