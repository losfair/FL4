/-
P3 (DESIGN.md §9), CSpace/IPC: **CNode CancelBadgedSends and the invalid
labels with `JAt` after** (discharging XTopJointStep's per-op premise
`JPostHyp` at the CNode cap's remaining labels).

* FL4's side: `cancel_badged_irelF`, IpcCancelBadged's `cancel_badged_irel`
  with the slots and the base kept (`IFrame`) and the footprint `CnStep`
  (as IpcCancelAllIpc's `cancel_all_ipc_irel`: the dequeue's `EWrite`, the
  restart's `restart_irelF`, the reschedule's scheduler words).
* The spec's side: `inv_cancelBadgedSends`, `cancel_badged_sends` keeps `Inv`
  and `BlockedScActive` in the frame `EFr e (fun _ => False)` of IpcFinEpInv
  (a thread blocked on the endpoint restarted or made inactive, the
  endpoint's queue shorter, an SC's refills; no reply changed), by
  `inv_badged_iter` (the dequeue, `Inv.updEp`; `rtinf_inv`).
* `JAtZ.cancelBadgedJ`: `JAtZ` across `cancel_badged_sends`, as
  XTopJointFinEp's `JAtZ.finEpJ` (no reply freed, so no `RecvReplyHyp`), P1's
  `BlkOK` by `cancel_badged_sends.blkF`.
* `decode_invocation_cnode_cancelJ`: the CancelBadgedSends label at `JAt`
  (the caller's restart by `stepClosed_jat` from `JStepHyps`, then
  `JAtZ.cancelBadgedJ`); `decode_invocation_cnode_illegalJ`: the invalid
  labels (an error, the state kept).
-/
import Fl4Proofs.P3.XTopJointDelR
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.BufFr
import Fl4Proofs.P3.BufFrA
open Aeneas Aeneas.Std Result

/-! ## FL4's side: `cancel_badged_sends` with its frame -/

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched Classical

noncomputable section

section LoopF
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

variable (st th cr N T C E R B c) in
/-- `BInv` with the slots and the base kept since `s0` and the footprint
`CnStep` since `(s0, σ0)`. -/
def BInvF (e b : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x : S × U64 × U64) : Prop :=
  ∃ σ' y, ∃ kept rest : List U64, IRel st th cr N T C E R B c x.1 σ' ∧ σ'.kheap e.bv = some (.endpoint y) ∧
    y.epQueue = (kept ++ rest).map UScalar.bv ∧ (∀ q, y ≠ .recvEP q) ∧ x.2.1 = rest.headD 0#u64 ∧
    rest.length ≤ x.2.2.val ∧
    (∀ z, z ∈ (Fl4Spec.NonDet.mapMx (rrb e b) (rest.map UScalar.bv) σ').1 →
      z ∈ (Fl4Spec.NonDet.mapMx (rrb e b) q0 σ0).1) ∧
    IFrame (L := L) th s0 x.1 ∧ CnStep (st := st) T N C E R c s0 σ0 x.1 σ' ∧
    (∀ u ∈ rest.map UScalar.bv, MemOKE σ' u) ∧ ScBack σ' ∧ ActReady σ'

set_option maxHeartbeats 8000000 in
/-- **The loop of `cancel_badged_sends`** on `IRel`, with its frame. -/
theorem badged_loopF (hP0 : IPlaced N T E R B)
    {e b : U64} (he : e ∈ E) (s0 : S) (σ0 : Fl4Spec.State Unit) (q0 : List Fl4Spec.ObjRef) (x0 : S × U64 × U64)
    (h0 : BInvF st th cr N T C E R B c e b s0 σ0 q0 x0) :
    endpoint.cancel_badged_sends_loop st x0.1 e b x0.2.1 x0.2.2 ⦃ s' => ∃ σf,
      ((), σf) ∈ (Fl4Spec.NonDet.mapMx (rrb e b) q0 σ0).1 ∧ IRel st th cr N T C E R B c s' σf ∧
      IFrame (L := L) th s0 s' ∧ CnStep (st := st) T N C E R c s0 σ0 s' σf ∧ ActReady σf ⦄ := by
  have hP := hP0.e
  have hH := ipcCore_top (st := st) (th := th) (cr := cr) (N := N) (C := C) (c := c) hP
  unfold endpoint.cancel_badged_sends_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 × U64 => x.2.2.val)
    (inv := BInvF st th cr N T C E R B c e b s0 σ0 q0) _ _ x0 ?_ h0
  rintro ⟨s, t, fuel⟩ ⟨σ', y, kept, rest, hX, hky, hq, hnr, ht, hlen, hinc, hss, hcs, hmm, hBk, hAr⟩
  simp only at hX hky hq hnr ht hlen hinc hss hcs hmm hBk hAr ⊢
  have hEP := hX.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, hB⟩ := hEP.queue
  have hxs' : xs = kept ++ rest := by
    rw [hq] at hxs
    exact (List.map_injective_iff.2 (fun a b h => eq_of_bv h) hxs).symm
  subst hxs'
  unfold endpoint.cancel_badged_sends_loop.body
  step with obj.Tcb.is_null.spec as ⟨bn, hbn⟩
  cases rest with
  | nil =>
    simp only [List.headD_nil] at ht
    subst ht
    simp only [hbn, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ', hinc _ rfl, hX, hss, hcs, hAr⟩
  | cons t0 rest' =>
    simp only [List.headD_cons] at ht
    subst t
    have ht0T : t0 ∈ T := hQ.mem t0 (by simp)
    have ht00 : t0 ≠ 0#u64 := hQ.ne0 hP.tcb t0 (by simp)
    simp only [hbn, ht00, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hf0 : fuel > 0#u64 := by
      simp only [List.length_cons] at hlen
      show (0#u64 : U64).val < fuel.val; simp; omega
    simp only [hf0, ↓reduceIte]
    step as ⟨fuel1, hfuel1⟩
    -- the successor
    have hseg := hQ.seg
    rw [Seg_mid] at hseg
    obtain ⟨-, -, hnext, -⟩ := hseg
    unfold tcbqueue.next_of
    step with tcbqueue.next.spec as ⟨nx, hnx⟩
    -- the thread's state
    obtain ⟨hbe, hcode⟩ := hB t0 (by simp)
    obtain ⟨xt, hkt, hTR⟩ := hX.1.tcb t0 ht0T
    have hTRE := hX.1.toE.at_tcb ht0T hkt
    have h4 : (L.mem s (tStA t0)).val = 4 := by
      cases y with
      | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hq
      | recvEP q => exact absurd rfl (hnr q)
      | sendEP q =>
        obtain ⟨-, ys, -, hys, hQ', hqo⟩ := hEP
        have := hQ'.unique hP.tcb hQ
        rw [this] at hqo
        exact (hqo t0 (by simp)).1
    obtain ⟨e', d, hst⟩ : ∃ e' d, xt.tcbState = .blockedOnSend e' d := by
      have := hTRE.st; rw [h4] at this
      cases h : xt.tcbState <;> rw [h] at this <;> simp [tsCode] at this
      exact ⟨_, _, rfl⟩
    have he' : e' = e.bv := by
      rw [← hTRE.blk e' (by simp [hst, Fl4Spec.epBlocked]), hbe]
    subst he'
    have hbdg : (L.mem s (tBadgeA t0)).bv = d.senderBadge := (hTRE.send _ d hst).1
    step with obj.Tcb.block_badge.spec as ⟨i, hi⟩
    subst hi
    by_cases hm : L.mem s (tBadgeA t0) = b
    · -- dequeued and restarted
      simp only [hm, ↓reduceIte]
      have hd : t0.bv ∈ y.epQueue := by rw [hq]; simp
      have hta := hP.tcb t0 ht0T
      refine WP.spec_bind (WP.spec_and (ep_dequeue_c hH hP0 hP s σ' hX.1.toE (IpcRel.toSRN hX.1 hX.2) he hky hd)
        (ep_dequeue_full hP s he t0 (kept ++ t0 :: rest') hQ (by simp))) ?_
      rintro s1 ⟨⟨hdq, hR1, hS1, hA1⟩, -, -, hQA, hw1, -, -⟩
      have hX1 := IpcRel.ofSRN hR1 hS1
      have hF1 : IFrame (L := L) th s s1 := IRel.iframe_of hX hw1 fun b hb => iwords_oobj (EWrite.iwords hb)
      have hCd : CnStep (st := st) T N C E R c s σ' s1 (updK σ' e.bv (.endpoint (epDeq y t0.bv))) := by
        refine ⟨⟨hw1.1, hw1.2.1, fun b hb hn => hQA b hb ⟨fun h => hn (Or.inr (Or.inl ⟨e, he, h⟩)), ?_⟩⟩,
          SzKeepC.of (SzKeep.updK hky (fun _ _ h => by cases h))⟩
        rintro ⟨w, hw, h | h⟩
        · exact hn (Or.inl (Or.inr ⟨w, hQ.mem w hw, 3496, by omega, by omega, by omega, by omega, by omega, h⟩))
        · exact hn (Or.inl (Or.inr ⟨w, hQ.mem w hw, 3504, by omega, by omega, by omega, by omega, by omega, h⟩))
      set σd := updK σ' e.bv (.endpoint (epDeq y t0.bv)) with hσd
      have hte : t0.bv ≠ e.bv := by intro h; rw [h, hky] at hkt; cases hkt
      have hktd : σd.kheap t0.bv = some (.tcb xt) := by simp [hσd, updK, hte, hkt]
      have hkyd : σd.kheap e.bv = some (.endpoint (epDeq y t0.bv)) := by simp [hσd, updK]
      have hb1 : L.mem s1 (tBlockA t0) = e := (hA1 _ (a_blk hta).1 ⟨t0, ht0T, (a_blk hta).2⟩).trans hbe
      obtain ⟨hdqq, hdnr⟩ := epDeq_send_queue hnr t0.bv
      have hnd : (kept ++ t0 :: rest').Nodup := hQ.nodup
      have hrm : Fl4Spec.removeAll t0.bv y.epQueue = (kept ++ rest').map UScalar.bv := by
        rw [hq, removeAll_map hnd]
        congr 1
        have hnk : t0 ∉ kept := fun h => by
          have := List.nodup_append.1 hnd
          exact this.2.2 _ h _ (by simp) rfl
        rw [List.erase_append_right _ hnk, List.erase_cons_head]
      have hnq : t0.bv ∉ (epDeq y t0.bv).epQueue := by
        rw [hdqq, hrm, List.mem_map]
        rintro ⟨z, hz, ez⟩
        have : z = t0 := eq_of_bv ez
        subst this
        have := List.nodup_append.1 hnd
        rcases List.mem_append.1 hz with h | h
        · exact this.2.2 _ h _ (by simp) rfl
        · exact (List.nodup_cons.1 this.2.1).1 h
      have hq1 := dequeued_not_queued hR1 he hb1 hkyd hnq
      -- the spec's facts at the dequeued state
      have hFd : SFr σ' σd := SFr.updOther hky (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      have hBd : ScBack σd := hFd.scBack hBk
      have hxsd : xt.tcbFault = none → ScOK σd xt := by
        obtain ⟨x', hk', hsc⟩ := MemOKE.updOther (o' := .endpoint (epDeq y t0.bv)) hky (fun _ h => by cases h)
          (fun _ _ h => by cases h) (hmm t0.bv (by simp))
        rw [hktd] at hk'; cases hk'; exact hsc
      refine WP.spec_bind (restart_irelF hP0 s1 σd hX1 ht0T hktd (by rw [hst]; simp [tsCode]) hq1 hxsd hBd
        (hFd.actReady hAr (Or.inl rfl))) ?_
      rintro s2 ⟨σ'', hres, hX2, hkeep, hF2, hC2, hB'', hA'', ht'', hkp''⟩
      have hnd' : t0 ∉ rest' := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
      rw [WP.spec_ok]
      refine ⟨⟨σ'', epDeq y t0.bv, kept, rest', hX2, hkeep _ _ hkyd, by rw [hdqq, hrm], hdnr,
        by rw [hnx, hnext], ?_, ?_, hss.trans (hF1.trans hF2), hcs.trans (hCd.trans hC2), fun u hu => ?_, hB'', hA''⟩,
        ?_⟩
      · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
      · refine fun z hz => hinc z (mapMx_cons_mem (l := rest'.map UScalar.bv) ?_ z hz)
        show ((), σ'') ∈ (Fl4Spec.removeAndRestartBadgedThread (Z := Unit) t0.bv e.bv b.bv σ').1
        unfold Fl4Spec.removeAndRestartBadgedThread
        rw [nd_bind_one (getThreadState_eq hkt), hst]
        have hb' : Fl4Spec.blockingIpcBadge (.blockedOnSend e.bv d) = b.bv := by
          rw [Fl4Spec.blockingIpcBadge, ← hbdg, hm]
        simp only [Fl4Spec.NonDet.when, hb', ↓reduceIte]
        exact ⟨((), σd), by rw [hdq]; rfl, hres⟩
      · obtain ⟨u0, hu0, rfl⟩ := List.mem_map.1 hu
        exact memOK_after hktd hBd (fun h => hnd' (eq_of_bv h ▸ hu0))
          (MemOKE.updOther (o' := .endpoint (epDeq y t0.bv)) hky (fun _ h => by cases h) (fun _ _ h => by cases h)
            (hmm _ (List.mem_map_of_mem (List.mem_cons_of_mem _ hu0)))) hkp'' ht''
      · rw [hfuel1]; scalar_tac
    · -- kept
      simp only [hm, ↓reduceIte, WP.spec_ok]
      refine ⟨⟨σ', y, kept ++ [t0], rest', hX, hky, by rw [hq]; simp, hnr, by rw [hnx, hnext], ?_, ?_, hss, hcs,
        fun u hu => hmm u (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hu), hBk, hAr⟩, ?_⟩
      · rw [hfuel1]; simp only [List.length_cons] at hlen; scalar_tac
      · refine fun z hz => hinc z (mapMx_cons_mem (l := rest'.map UScalar.bv) ?_ z hz)
        show ((), σ') ∈ (Fl4Spec.removeAndRestartBadgedThread (Z := Unit) t0.bv e.bv b.bv σ').1
        unfold Fl4Spec.removeAndRestartBadgedThread
        rw [nd_bind_one (getThreadState_eq hkt), hst]
        have hb' : Fl4Spec.blockingIpcBadge (.blockedOnSend e.bv d) ≠ b.bv := by
          rw [Fl4Spec.blockingIpcBadge, ← hbdg]; exact fun h => hm (eq_of_bv h)
        simp only [Fl4Spec.NonDet.when, hb', ↓reduceIte]
        rfl
      · rw [hfuel1]; scalar_tac

set_option maxHeartbeats 8000000 in
/-- **`cancel_badged_sends` on `IRel`**, the slots and the base kept, with
the footprint `CnStep`. -/
theorem cancel_badged_irelF (hP0 : IPlaced N T E R B)
    (s : S) (σ : Fl4Spec.State Unit) (hX : IRel st th cr N T C E R B c s σ) {e : U64} (he : e ∈ E) (b : U64)
    (hpre : EpQPre σ e.bv) :
    endpoint.cancel_badged_sends st s e b ⦃ s' => ∃ σ',
      ((), σ') ∈ (Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ).1 ∧ IRel st th cr N T C E R B c s' σ' ∧
      IFrame (L := L) th s s' ∧ CnStep (st := st) T N C E R c s σ s' σ' ⦄ := by
  have hP := hP0.e
  obtain ⟨y, hky, hEP⟩ := hX.1.toE.ep e he
  obtain ⟨hm0, hB0, hA0⟩ := hpre y hky
  unfold endpoint.cancel_badged_sends
  step with obj.Ep.state.spec as ⟨i, hi⟩
  rw [epState_eq] at hi
  have hsp : Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ = (match y with
        | .sendEP queue => (do Fl4Spec.NonDet.mapMx (fun t => Fl4Spec.removeAndRestartBadgedThread t e.bv b.bv) queue
                               Fl4Spec.rescheduleRequired)
        | _ => return ()) σ := by
    unfold Fl4Spec.cancelBadgedSends
    rw [nd_bind_one (getEndpoint_eq hky)]
    rfl
  cases y with
  | idleEP =>
    have h0 : i ≠ obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp]; rfl, hX, IFrame.refl _ _, CnStep.refl _ _⟩
  | recvEP q =>
    have h0 : i ≠ obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]; decide
    simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, by rw [hsp]; rfl, hX, IFrame.refl _ _, CnStep.refl _ _⟩
  | sendEP q =>
    have h0 : i = obj.EP_SEND := by rw [hi, hEP.1, ep_state_vals.2.1]
    simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨-, xs, -, hqx, hQ, -⟩ := hEP
    step with endpoint.get_queue.spec as ⟨qq, hqq⟩
    have hfuel : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
    have hI0 : BInvF st th cr N T C E R B c e b s σ q (s, qq.head, layout.WALK_FUEL) :=
      ⟨σ, .sendEP q, [], xs, hX, hky, by rw [hqx]; rfl, (fun q' e' => by cases e'),
        by rw [hqq, epQ_eq, hQ.head], by rw [hfuel]; exact len_le_max xs hQ.nodup (hQ.ne0 hP.tcb),
        fun z hz => by rw [hqx]; exact hz, IFrame.refl _ _, CnStep.refl _ _,
        fun u hu => hm0 u (by show u ∈ q; rw [hqx]; simpa using hu), hB0, hA0⟩
    refine WP.spec_bind (badged_loopF hP0 he s σ q _ hI0) ?_
    rintro s1 ⟨σf, hmf, hXf, hss1, hcs1, hAf⟩
    refine WP.spec_mono (WP.spec_and (resched_irel hP0 s1 σf hXf hAf)
      (reschedule_required_sfootI hXf.2.2.1)) ?_
    rintro s2 ⟨⟨σr, hrs, hkr, hX2⟩, hw2⟩
    refine ⟨σr, ?_, hX2, hss1.trans (IRel.iframe_of hXf hw2 fun b hb => sfootI_oobj hP.tcb hb),
      hcs1.trans ⟨hw2.mono fun b hb => Or.inl (SFootI.finW hP.tcb hb), SzKeepC.of (SzKeep.of_kheap hkr)⟩⟩
    rw [hsp]
    exact ⟨((), σf), hmf, by show ((), σr) ∈ (Fl4Spec.rescheduleRequired σf).1; rw [hrs]; rfl⟩

end LoopF

end

end Fl4Proofs.P3.Ipc

/-! ## The spec's side: the scheduler invariants in `EFr` -/

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec Classical

/-- The facts `cancel_badged_sends`'s loop carries: the queue still to visit
in the endpoint's, each of its threads blocked on the endpoint. -/
def BLoopInv (σ : State Unit) (e : ObjRef) (l : List ObjRef) : Prop :=
  Inv σ ∧ BlockedScActive σ ∧ (∃ x, σ.kheap e = some (.endpoint x) ∧ ∀ u ∈ l, u ∈ x.epQueue) ∧ l.Nodup ∧
    (∀ u ∈ l, ∃ xu, σ.kheap u = some (.tcb xu) ∧ epBlocked xu.tcbState = some e)

set_option maxHeartbeats 16000000 in
/-- **One thread of `cancel_badged_sends` keeps the loop's facts**, in `EFr`
(a thread with the badge dequeued and restarted, `rtinf_inv`; the others
kept). -/
theorem inv_badged_iter {P : ObjRef → Prop} {σ σ5 : State Unit} {e t : ObjRef} {b : Badge} {l : List ObjRef}
    (h : BLoopInv σ e (t :: l)) (hm : ((), σ5) ∈ (removeAndRestartBadgedThread (Z := Unit) t e b σ).1) :
    BLoopInv σ5 e l ∧ EFr e P σ σ5 := by
  obtain ⟨hI, hB, ⟨x, hk, hsub⟩, hnd, hbl⟩ := h
  have htl : t ∉ l := (List.nodup_cons.1 hnd).1
  obtain ⟨xt, hkt, hbe⟩ := hbl t (List.mem_cons_self ..)
  have het : e ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
  have hnr : runnable xt.tcbState = false := epBlocked_run hbe
  unfold removeAndRestartBadgedThread at hm
  rw [nd_bind_one (getThreadState_eq hkt)] at hm
  by_cases hbd : blockingIpcBadge xt.tcbState = b
  · simp only [NonDet.when, hbd, ↓reduceIte] at hm
    have hmem : t ∈ x.epQueue := hsub t (List.mem_cons_self ..)
    have hxne : x ≠ .idleEP := by rintro rfl; simp [Endpoint.epQueue] at hmem
    rw [nd_bind_one (tcbEpDequeue_eq hk hmem)] at hm
    set σ1 := updK σ e (.endpoint (epDeq x t)) with hσ1
    have hI1 : Inv σ1 := hI.updEp hk
    have hkp1 : ∀ p, p ≠ e → σ1.kheap p = σ.kheap p := fun p hp => by
      simp only [hσ1, updK, Function.update_of_ne hp]
    have hkt1 : σ1.kheap t = some (.tcb xt) := by rw [hkp1 t (Ne.symm het)]; exact hkt
    have hK1 : Ipc.SKeep σ σ1 := Ipc.SKeep.updK (fun _ h => by cases h) (fun _ _ h => by cases h)
    have hrib : xt.tcbFault = none → RelIfBound σ1 t := fun hf =>
      Ipc.RelIfBound.of_keep (hI.rd t xt hkt (inClassR_nf (epBlocked_inClass hbe) fun b e => by
        rw [hf] at e; cases e)) hK1
    have hsa : ∀ p y k, xt.tcbSchedContext = some p → σ1.kheap p = some (.schedContext y k) →
        scActive y = true := by
      intro p y k hp hky
      obtain ⟨y0, k0, hky0, hyt⟩ := hI.back t xt p hkt hp
      have hpe : p ≠ e := by rintro rfl; rw [hk] at hky0; cases hky0
      rw [hkp1 p hpe, hky0] at hky; cases hky
      exact hB.tcb p _ _ t xt hky0 hyt hkt (epBlocked_ipcQ hbe)
    obtain ⟨hI5, hS5, ⟨st5, hst5, hkt5⟩, hkp5, hsc5⟩ := rtinf_inv hI1 hkt1 hnr hrib hsa hm
    have hkeep : ∀ p, p ≠ t → p ≠ e → xt.tcbSchedContext ≠ some p → σ5.kheap p = σ.kheap p :=
      fun p h1 h2 h4 => by rw [hkp5 p h1 h4, hkp1 p h2]
    have hS1 : Sk σ σ1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hS : Sk σ σ5 := hS1.trans hS5
    have hec : xt.tcbSchedContext ≠ some e := fun hc => by
      obtain ⟨y, k, h1, -⟩ := hI.back t xt e hkt hc
      rw [hk] at h1; cases h1
    have F : EFr e P σ σ5 := by
      refine ⟨hS, fun p => ?_⟩
      by_cases hpt : p = t
      · subst hpt
        exact Or.inr ⟨.tcb xt, .tcb { xt with tcbState := st5 }, hkt, hkt5,
          Or.inl ⟨xt, st5, rfl, rfl, Or.inr ⟨hbe, hst5⟩⟩⟩
      by_cases hpe : p = e
      · refine Or.inr ⟨.endpoint x, .endpoint (epDeq x t), by rw [hpe]; exact hk, ?_,
          Or.inr (Or.inr (Or.inl ⟨x, epDeq x t, rfl, rfl, hpe, hxne,
            by rw [epDeq_queue']; unfold removeAll; exact List.filter_sublist⟩))⟩
        rw [hkp5 p hpt (by rw [hpe]; exact hec), hσ1, hpe]; simp [updK]
      by_cases hpc : xt.tcbSchedContext = some p
      · obtain ⟨y, k, hky, -⟩ := hI.back t xt p hkt hpc
        have hky1 : σ1.kheap p = some (.schedContext y k) := by rw [hkp1 p hpe]; exact hky
        obtain ⟨rf, hrf, hcur⟩ := hsc5 p y k hpc hky1
        exact Or.inr ⟨.schedContext y k, .schedContext { y with scRefills := rf } k, hky, hrf,
          Or.inr (Or.inl ⟨y, k, rf, rfl, rfl, fun h => hcur (h.trans hS1.csc.symm)⟩)⟩
      · exact Or.inl (hkeep p hpt hpe hpc)
    refine ⟨⟨hI5, F.bsa hB, ⟨epDeq x t, ?_, fun u hu => ?_⟩, (List.nodup_cons.1 hnd).2, fun u hu => ?_⟩, F⟩
    · rw [hkp5 e het hec, hσ1]; simp [updK]
    · have hut : u ≠ t := fun h => htl (h ▸ hu)
      rw [epDeq_queue']; unfold removeAll
      exact List.mem_filter.2 ⟨hsub u (List.mem_cons_of_mem _ hu), by simpa using Ne.symm hut⟩
    · obtain ⟨xu, hku, hbu⟩ := hbl u (List.mem_cons_of_mem _ hu)
      have hut : u ≠ t := fun h => htl (h ▸ hu)
      have hue : u ≠ e := by rintro rfl; rw [hk] at hku; cases hku
      have huc : xt.tcbSchedContext ≠ some u := fun hc => by
        obtain ⟨y, k, h1, -⟩ := hI.back t xt u hkt hc
        rw [hku] at h1; cases h1
      exact ⟨xu, by rw [hkeep u hut hue huc]; exact hku, hbu⟩
  · simp only [NonDet.when, hbd, ↓reduceIte] at hm
    have e5 : σ5 = σ := mem_singleton_snd hm
    subst e5
    exact ⟨⟨hI, hB, ⟨x, hk, fun u hu => hsub u (List.mem_cons_of_mem _ hu)⟩, (List.nodup_cons.1 hnd).2,
      fun u hu => hbl u (List.mem_cons_of_mem _ hu)⟩, EFr.refl _ _ _⟩

/-- **The loop of `cancel_badged_sends` keeps the loop's facts.** -/
theorem badged_loop_inv {P : ObjRef → Prop} {e : ObjRef} {b : Badge} :
    ∀ (l : List ObjRef) (σ σ' : State Unit), BLoopInv σ e l →
    ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartBadgedThread (Z := Unit) t e b) l σ).1 →
    BLoopInv σ' e [] ∧ EFr e P σ σ'
  | [], σ, σ', h, hm => by
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨h, EFr.refl _ _ _⟩
  | t :: l, σ, σ', h, hm => by
    obtain ⟨y, hy, hm⟩ := (show ((), σ') ∈ ((removeAndRestartBadgedThread (Z := Unit) t e b >>= fun _ =>
      NonDet.mapMx (fun t => removeAndRestartBadgedThread (Z := Unit) t e b) l) σ).1 from hm)
    obtain ⟨⟨⟩, σ5⟩ := y
    obtain ⟨h5, hF5⟩ := inv_badged_iter (P := P) h hy
    obtain ⟨h', hF'⟩ := badged_loop_inv l σ5 σ' h5 hm
    exact ⟨h', hF5.trans hF'⟩

set_option maxHeartbeats 4000000 in
/-- **`cancel_badged_sends` keeps `Inv` and `BlockedScActive`**, in the frame
`EFr` (any `P`: no reply changes), the action then `choose_new_thread` unless
nothing changed. -/
theorem inv_cancelBadgedSends {P : ObjRef → Prop} {σ σ' : State Unit} {e : ObjRef} {b : Badge} {x : Endpoint}
    (hI : Inv σ) (hB : BlockedScActive σ) (hk : σ.kheap e = some (.endpoint x)) (hnd : x.epQueue.Nodup)
    (hbl : ∀ u ∈ x.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧ epBlocked xu.tcbState = some e)
    (hm : ((), σ') ∈ (cancelBadgedSends (Z := Unit) e b σ).1) :
    Inv σ' ∧ BlockedScActive σ' ∧ EFr e P σ σ' ∧ (σ'.schedulerAction = .chooseNewThread ∨ σ' = σ) := by
  unfold cancelBadgedSends at hm
  rw [nd_bind_one (getEndpoint_eq hk)] at hm
  cases x with
  | sendEP q =>
    obtain ⟨z, hz, hm⟩ := hm
    obtain ⟨⟨⟩, σf⟩ := z
    have h0 : BLoopInv σ e q := ⟨hI, hB, ⟨.sendEP q, hk, fun u hu => hu⟩, hnd, hbl⟩
    obtain ⟨⟨hIf, hBf, -⟩, hFf⟩ := badged_loop_inv (P := P) q σ σf h0 hz
    obtain ⟨σr, hr, hq⟩ := rescheduleRequired_qchange hIf.actReady
    obtain ⟨σr', hr', hQ', ha'⟩ := resched_q hIf.actReady
    have hm' : ((), σ') ∈ (rescheduleRequired (Z := Unit) σf).1 := hm
    have e1 : σ' = σr := mem_singleton_snd (by rw [hr] at hm'; exact hm')
    have e' : σ' = σr' := mem_singleton_snd (by rw [hr'] at hm'; exact hm')
    subst e1
    refine ⟨hIf.qchange hq, ?_, hFf.trans (e' ▸ hQ'.efr), Or.inl (e' ▸ ha')⟩
    obtain ⟨hk', -⟩ := hq
    exact ⟨fun p y k t x hp hyt hx hqt => hBf.tcb p y k t x (hk' ▸ hp) hyt (hk' ▸ hx) hqt,
      fun p y k hp hr' => hBf.replies p y k (hk' ▸ hp) hr'⟩
  | idleEP =>
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB, EFr.refl _ _ _, Or.inr rfl⟩
  | recvEP q =>
    have : σ' = σ := mem_singleton_snd hm
    rw [this]; exact ⟨hI, hB, EFr.refl _ _ _, Or.inr rfl⟩

end Spec

end

end Fl4Proofs.P3.Sched

/-! ## `JAtZ` across `cancel_badged_sends` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across `cancel_badged_sends`** (module docstring): at
`Z.mv Z.G V'`, the dead set and P1's sets kept. -/
theorem JAtZ.cancelBadgedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {e : U64} (b : U64) (he : e ∈ Z.E)
    (hpre : EpQPre σ e.bv) :
    endpoint.cancel_badged_sends st s e b ⦃ s3 => ∃ σ3 V',
      ((), σ3) ∈ (Fl4Spec.cancelBadgedSends (Z := Unit) e.bv b.bv σ).1 ∧
      JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s3 a σ3 ∧ SlotsSame Z.th (L.mem s) (L.mem s3) ∧
      L.ksb s3 = L.ksb s ⦄ := by
  have hpH : H e = some .ep := J.zH.2.1 e he
  have hI := J.xtop.irelK J.ks J.buf
  refine WP.spec_mono (WP.spec_and (cancel_badged_irelF J.ip s σ hI he b hpre)
    (P1.endpoint.cancel_badged_sends.blkF s e b J.blk hpH)) ?_
  rintro s3 ⟨⟨σ3, hm3, hI3, hF, hCS⟩, hblk, hfoot0⟩
  have hfoot := hfoot0.mono (show ({e} : Set U64) ⊆ P1.EH H from fun x hx => by
    rw [Set.mem_singleton_iff.1 hx]; exact Or.inl hpH)
  -- the spec
  obtain ⟨y, hky, -⟩ := hI.1.toE.ep e he
  have hEP := hI.1.toE.at_ep he hky
  obtain ⟨xs, hQ, hxs, -⟩ := hEP.queue
  have hnd : y.epQueue.Nodup := by rw [hxs]; exact hQ.nodup.map (fun a b h => eq_of_bv h)
  have hbl : ∀ u ∈ y.epQueue, ∃ xu, σ.kheap u = some (.tcb xu) ∧ Fl4Spec.epBlocked xu.tcbState = some e.bv :=
    fun u hu => ep_queue_blocked J.ip hI he hky hu
  obtain ⟨I3, B3, F, hact⟩ := inv_cancelBadgedSends (P := fun _ => False) J.inv J.bsa hky hnd hbl hm3
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 (a' := a) hAR hF.1 F.sk.cdt F.sk.orig F.ksub hF.2
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
    rcases hc with e' | ⟨⟨t, -, hf⟩, -⟩
    · obtain ⟨h1, h2, h3⟩ := J.rfree d hd ⟨x, hx, e' ▸ hyt⟩
      exact ⟨h1, by rw [r2]; exact h2, by rw [r1]; exact h3⟩
    · exact hf.elim
  have hDbg := J.kw_dbg hfoot
  have hKd := J.kw_dbgKeep hfoot
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3 := hI3.2.2.1
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
  exact ⟨σ3, Z.vs, hm3, J.cs_frameI hks hX3 hw (fun b hb => Ipc.CnW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => J.cnW_nv hb) F.sk.arch (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
      (fun _ e => by cases e)) F.szKeep hF.1 F.kback F.ipcFr hC R hKd F.sk.orig (J.idleW_keep hS3 F.sk.idle F.sk.isc).1 J.zD, hF.1, hks⟩

end

end

end Fl4Proofs.P3

/-! ## The CNode cap's CancelBadgedSends and invalid labels at `JAt` -/

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **A CancelBadgedSends's outcome at `JAt`** (as `cn_cancel_topX`): the
caller's restart at `J` (`stepClosed_jat`, `JStepHyps`), alone for badge 0,
then `JAtZ.cancelBadgedJ`. -/
theorem cn_cancel_topJ (hAM : ARMask arI AR) (hJ : JStepHyps (L := L) arI AR Z.th) {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hC : CurRun σ)
    {ct : U64} (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.CnodeInvocation} {res : core.result.Result Unit error.Exc × S × A}
    (hq : CancelDec (L := L) Z.th ct σ m s (res.1, res.2.1) ∧ res.2.2 = ar) :
    TopPostDMX (L := L) (JAt (L := L) arI AR) σ blk call don
      (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeCNode m) s res := by
  obtain ⟨r, s', a'⟩ := res
  obtain ⟨hq, rfl⟩ := hq
  cases r with
  | Err e =>
    obtain ⟨rfl, e', h1, h2⟩ := hq
    exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err h1, Or.inl h2⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩
  | Ok u =>
    obtain ⟨inv, hrun, σ1, hst, p, b, rfl, ⟨sl, hsl, hcV⟩, s2, hs2, h0, h1⟩ := hq
    obtain ⟨htcb, x, hk⟩ := J.xtop.curTcb hcur
    have hrn : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
    have hσ1 : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
      have hst' := hst
      rw [hcur, Notif.setThreadState_eq .restart hk] at hst'
      have := congrArg (fun q => ((), σ1) ∈ q.1) hst'
      simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
      simpa using this.symm
    -- the caller's restart at `J`
    obtain ⟨Ac1, Lst1, J1⟩ := J.restartSJ hJ hcur hk htcb hrn hs2
    rw [← hσ1] at J1
    by_cases hb : b = 0#u64
    · subst hb
      have e := h0 rfl
      subst e
      have hrun0 : (Fl4Spec.invokeCnode (Z := Unit)
          (.cancelBadgedSendsCall (absCap (.Endpoint p 0#u64 true true true true)))).run σ1 =
          ({(.ok (), σ1)}, False) := by
        show (Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv (0#u64 : U64).bv (rightsOf true true true true)))).run σ1 = _
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when]
        have : ¬ ((0#u64 : U64).bv ≠ 0) := by simp
        simp only [this, ↓reduceIte]
        exact run_liftE rfl
      have hx : ((.ok (), σ1) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p 0#u64 true true true true)))).run σ1).1 := by rw [hrun0]; rfl
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ1),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J1.xtop.rel.1, J1.xtop.rel.2.1,
          J1.xtop.rel.2.2.1, J1.xtop.rel.2.2.2.1, J1.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D, J1⟩⟩
    · have hcb := h1 hb
      have he : p ∈ Z.E := hE p b sl hsl hcV
      have hpre : EpQPre σ1 p.bv := by rw [hσ1]; exact epQPre_restart hk (hQ _) hsw
      have h := J1.cancelBadgedJ b he hpre
      rw [hcb, WP.spec_ok] at h
      obtain ⟨σ3, V3, hm3, J3, -, -⟩ := h
      have hbv : b.bv ≠ 0 := by
        intro h; apply hb; apply UScalar.eq_of_val_eq
        have := congrArg BitVec.toNat h; simpa using this
      have hx : ((.ok (), σ3) : Except Unit Unit × Fl4Spec.State Unit) ∈
          ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
            (absCap (.Endpoint p b true true true true)))).run σ1).1 := by
        show _ ∈ ((Fl4Spec.invokeCnode (Z := Unit) (.cancelBadgedSendsCall
          (.endpointCap p.bv b.bv (rightsOf true true true true)))).run σ1).1
        unfold Fl4Spec.invokeCnode Fl4Spec.withoutPreemption
        simp only [Fl4Spec.NonDet.when, hbv, ne_eq, not_false_eq_true, ↓reduceIte]
        exact mem_liftE (x := ((), σ3)) hm3
      exact Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun), σ1, hst, (.ok [], σ3),
        mem_bindE_ok hx (Set.mem_singleton _), ⟨_, _, Or.inl ⟨rfl, rfl⟩, J3.xtop.rel.1, J3.xtop.rel.2.1,
          J3.xtop.rel.2.2.1, J3.xtop.rel.2.2.2.1, J3.xtop.rel.2.2.2.2.1⟩, ⟨_, H, Cs, Ac1, Lst1, D, J3⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The CNode CancelBadgedSends label at `JAt`** (as
`decode_invocation_cnode_cancelX`): `cnode_cancel_dec`, then `cn_cancel_topJ`. -/
theorem decode_invocation_cnode_cancelJ (hAM : ARMask arI AR) (hJ : JStepHyps (L := L) arI AR Z.th) (s : S)
    (ar : A) (σ : Fl4Spec.State Unit) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hC : CurRun σ)
    (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .cnodeCancelBadgedSends)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (p r gs g : U64) (hwf : CapWf (.CNode p r gs g)) (hcv : CapValid Z.th (.CNode p r gs g))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hact : OutsideObjects Z.th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hcur : σ.curThread = ct.bv) (hQ : ∀ e, EpQPre σ e)
    (hsw : ∀ u, σ.schedulerAction = .switchThread u → u ≠ ct.bv)
    (hE : ∀ (e b : U64) (sl : Fl4Spec.CslotPtr), AbsSlot Z.th sl →
      capV (L.mem s) (cslotAddr sl) = .Endpoint e b true true true true → e ∈ Z.E)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ fl4_abi.label.CNodeCancelBadgedSends length slot
      (.CNode p r gs g) blk call don fp buf extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨⟨hR, hV, hM, hCd, hI⟩, hFI⟩ := And.intro hX.rel.2.1 hX.rel.2.2.1
  have htcb := (hX.curTcb hcur).1
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_mono (cnode_cancel_dec arI Z.th s ar σ Z.G hR hV hX.rel.1 hM hCd slbl hlbl length buf ct hct
      args hlen hargs _ _ ⟨hwf, rfl⟩ hcv extra _ hI hFI hact hcur htcb)
      fun res h => cn_cancel_topJ arI hAM hJ J hC hcur hQ hsw hE h
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, ⟨Z, H, Cs, Ac, Lst, D, J⟩⟩

/-- **The CNode cap's invalid labels at `JAt`** (as
`decode_invocation_cnode_illegalX`): an error, the state kept. -/
theorem decode_invocation_cnode_illegalJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ)
    (lbl : U64) (hlo : lbl.val < 25 ∨ 32 < lbl.val) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = cnodeLabelOf lbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List Fl4Spec.Data)
    (p r gs g : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot (.CNode p r gs g) blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold cnodeLabelOf
    simp only [show lbl.val ≠ 25 by omega, show lbl.val ≠ 26 by omega, show lbl.val ≠ 27 by omega,
      show lbl.val ≠ 28 by omega, show lbl.val ≠ 29 by omega, show lbl.val ≠ 30 by omega,
      show lbl.val ≠ 31 by omega, show lbl.val ≠ 32 by omega, ↓reduceIte]
  have hdec := decode_illegal slbl args (absCap (.CNode p r gs g)) (excaps.map Prod.fst) σ (by rw [hg]; decide)
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  left
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold cnode.decode
    rcases hlo with h | h
    · have n1 : lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      rw [if_pos n1]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hJ0⟩
    · have n1 : ¬ lbl < fl4_abi.label.CNodeRevoke := by have := lbl_revoke_val; scalar_tac
      have n2 : lbl > fl4_abi.label.CNodeRotate := by have := lbl_rotate_val; scalar_tac
      rw [if_neg n1, if_pos n2]
      simp only [error.illegal, bind_ok]
      rw [WP.spec_ok]
      exact Or.inl ⟨_, rfl, rfl, ⟨.illegalOperation, run_liftME_err hdec, Or.inl trivial⟩, hJ0⟩
  · simp only [↓reduceIte]
    rw [WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, hJ0⟩

end

end

end Fl4Proofs.P3
