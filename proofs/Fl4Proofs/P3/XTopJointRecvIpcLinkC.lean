/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch22 (c3)): **the endpoint
receive with a reply linked to another thread at a `MidC` state.**

* `cancelLink_curInv`: the spec's `cancel_ipc` of a thread `i ≠ ct` blocked
  on a reply (`reply_remove_tcb`) or receiving with one keeps `CurInv`. The
  spec's `reply_remove_tcb` only trims the call stack of the SC the reply is
  at (`scReplies`) and unlinks the reply; it never moves an SC between
  threads (in l4v it is `reply_remove`, not `reply_remove_tcb`, that returns
  a donated SC). So: `IK i` (`ikm_cancelIpc`: every TCB's SC field, every
  SC's refill max, the release queue), the current thread and ct's TCB
  (`cancelOther_keep`), the current and idle SC (`rsf_replyRemoveTcb`); the
  receive cancel by `CFr.curInv`.
* `jRecvIpcLinkC`: XTopJointKEntry15M's `jRecvIpcLinkM` with `MidC` for
  `MidE` (`MidC` at the state after the cancel by `cancelLink_curInv`) and
  `jRecvIpcUC` for `jRecvIpcUM`.
-/
import Fl4Proofs.P3.XTopJointKEntry21M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

set_option maxHeartbeats 4000000 in
/-- **The spec's `cancel_ipc` of a linked thread other than ct keeps
`CurInv`** (module docstring). -/
theorem cancelLink_curInv {σ σ' : Fl4Spec.State Unit} (hsv : Sched.SchedValid σ) {i : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (hk : σ.kheap i = some (.tcb x)) {q : Fl4Spec.ObjRef}
    (hst : x.tcbState = .blockedOnReply q ∨ ∃ e d, x.tcbState = .blockedOnReceive e (some q) d)
    (hne : σ.curThread ≠ i) (hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i σ).1) (hC : CurInv σ) :
    CurInv σ' := by
  rcases hst with hst | ⟨e, d, hst⟩
  · have e2 : Fl4Spec.cancelIpc (Z := Unit) i σ =
        Fl4Spec.replyRemoveTcb i q (updK σ i (.tcb { x with tcbFault := none })) := by
      unfold Fl4Spec.cancelIpc
      rw [Notif.nd_bind_one (Notif.getThreadState_eq hk), Notif.nd_bind_one (Notif.threadSet_eq _ hk), hst]
    have hm' : ((), σ') ∈ (Fl4Spec.replyRemoveTcb (Z := Unit) i q
        (updK σ i (.tcb { x with tcbFault := none }))).1 := by rw [← e2]; exact hm
    have hsF : Vs.rsF σ' = Vs.rsF (updK σ i (.tcb { x with tcbFault := none })) :=
      Vs.rsf_replyRemoveTcb i q _ ((), σ') hm'
    simp only [Vs.rsF, Prod.mk.injEq, updK] at hsF
    obtain ⟨-, hcsc', -, -, hisc'⟩ := hsF
    have hIK : IK i σ σ' := Sched.ikm_cancelIpc (t := i) σ ((), σ') hm
    obtain ⟨hct', -, -, -, hkeep⟩ := cancelOther_keep hm hne
    obtain ⟨xt, hkt, hxs, hnb⟩ := hC.tcb
    obtain ⟨y, n, hy⟩ := hC.sc
    have hO := hIK.1 σ.curSc
    rw [hy] at hO
    cases ho : σ'.kheap σ.curSc with
    | none => rw [ho] at hO; simp [OIK] at hO
    | some o' =>
      rw [ho] at hO
      simp only [OIK] at hO
      obtain ⟨y', rfl, hik⟩ := hO.2.1 y n rfl
      refine ⟨⟨xt, by rw [hct']; exact hkeep _ _ hne hkt, by rw [hcsc']; exact hxs, hnb⟩,
        ⟨y', n, by rw [hcsc']; exact ho⟩, ?_, by rw [hct', hIK.2.2.1]; exact hC.notRel⟩
      intro hni y2 n2 hy2
      rw [hcsc', ho] at hy2
      cases hy2
      rw [hcsc', hisc'] at hni
      have ha := hC.active hni y n hy
      simp only [Fl4Spec.scActive] at ha ⊢
      rw [hik.2.1]; exact ha
  · obtain ⟨xe, hke, hq⟩ := hsv.recvQ i x e (some q) d hk hst
    exact (Sched.cancelIpc_recv_cfr (r := i) hk hst hke hq
      (fun rp h => hsv.recvReply i x e rp d hk (by rw [hst, h])) hm).1.curInv hC

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread at a
`MidC` state** (module docstring). -/
theorem jRecvIpcLinkC (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : MidC σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (q : U64) (g' : Bool) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) (hcr : CapRel (.Reply q g') rc')
    {xr : Fl4Spec.Reply} (hkr : σ.kheap q.bv = some (.reply xr))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : JHeld (L := L) Z.th s (.Reply q g')) (hi0 : L.mem s (rTcbA q) ≠ 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true (.Reply q g') ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hR := (J.xtop.irelK J.ks J.buf).1.toE
  obtain ⟨q0, hq, hqe⟩ := J.obj.reply _ xr hkr
  rw [Sched.bv_inj hqe] at hq
  have hrt : xr.replyTcb = some (L.mem s (rTcbA q)).bv := (hR.at_reply hq hkr).trans (Notif.optRef_ne hi0)
  obtain ⟨xi, hki, hsti⟩ := J.sv.replyTcb q.bv xr _ hkr hrt
  obtain ⟨i, hiT, hie⟩ := J.obj.tcb _ xi hki
  have hiq : L.mem s (rTcbA q) = i := (P1.eq_of_bv hie).symm
  rw [hiq] at hrt hki hi0
  have hict : i ≠ ct := by
    intro e
    subst e
    have hr := hni.run xi (by rw [hcur]; exact hki)
    rcases hsti with h | ⟨_, _, h⟩ <;> rw [h] at hr <;> simp [Fl4Spec.runnable] at hr
  have hne : σ.curThread ≠ i.bv := fun e => hict (P1.eq_of_bv (e.symm.trans hcur))
  refine receive_ipc_linked hiq hi0 hict ?_
  refine WP.spec_mono (J.cancelLinkJ hiT hki hsti) ?_
  rintro ⟨s1, a1⟩ ⟨hSS, h1, σ', he, hin, V, Ac', Lst', J'⟩
  dsimp only at h1 hSS J' ⊢
  subst h1
  have hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i.bv σ).1 := by rw [he]; exact Set.mem_singleton _
  obtain ⟨hct', hid', hact', hrq', hkeep⟩ := cancelOther_keep hm hne
  have hR' := (J'.xtop.irelK J'.ks J'.buf).1.toE
  obtain ⟨xr', hkr', hrl⟩ := hR'.reply q hq
  have hnone : xr'.replyTcb = none := cancelOther_reply J.sv J'.sv hm hkr hrt hin hkr'
  have h0' : L.mem s1 (rTcbA q) = 0#u64 := optRef_none (hrl.symm.trans hnone)
  refine ⟨h0', ?_⟩
  have hcr' : rc' = absCap (.Reply q g') := hcr.abs
  subst hcr'
  have hsp : Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true
      (absCap (.Reply q g')) σ =
      Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true
      (absCap (.Reply q g')) σ' :=
    receiveIpc_linked _ _ _ _ hkr hrt (fun e => hne (hcur.trans e.symm)) he hkr' hnone
  rw [hsp]
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he', h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he'
  obtain ⟨xe', hke', -⟩ := hR'.ep p he'
  have hrun' : CurRun σ' := fun x hx => by
    obtain ⟨x0, hk0, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct ht
    rw [hct', hcur, hkeep ct.bv x0 (fun e => hict (P1.eq_of_bv e.symm)) hk0] at hx
    have e : x0 = x := by cases hx; rfl
    subst e
    exact hni.run x0 (by rw [hcur]; exact hk0)
  have hC' : CurInv σ' := cancelLink_curInv J.sv hki hsti hne hm hni.2.2.2
  have hE' : MidC σ' := ⟨by rw [hct', hid']; exact hni.1, hrun', by rw [hact']; exact hni.2.2.1, hC'⟩
  exact jRecvIpcUC (Z := Z.mv Z.G V) hAT hmax htu J' ht (hct'.trans hcur) hE' hE'.nr
    (by rw [hct', hrq']; exact hnq) p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩)

end

end

end Fl4Proofs.P3
