/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch24 (d3)): **the endpoint
receive with a reply linked to another thread at a `MidN` state** (ct has no
SC, a reschedule pending), outside the two SC donations to ct.

As XTopJointRecvIpcLinkC's `jRecvIpcLinkC`: cancel the linked thread `i`
(`JAtZ.cancelLinkJ`), then the free-reply receive at the state after
(XTopJointRecvIpcN's `jRecvIpcUN`). `MidN` holds after by
`cancelOther_keep` (ct's TCB, the action, the idle thread). `jRecvIpcUN`
asks `¬ IpcActDon` / `¬ IpcPushDon` at the state AFTER the cancel; they are
carried back to the state before (`cancelLink_actDon`, `cancelLink_pushDon`):

* the spec's `cancel_ipc` of `i` blocked on a reply is `reply_remove_tcb`,
  which writes only TCBs, SCs and replies: every notification and endpoint is
  kept (`neV`, the notification / endpoint at `p`; `ne_replyRemoveTcb`, a
  projection frame `FK` built from `ne_setObject`);
* of `i` receiving (with the reply) it is in IpcSignalBoundSpec's frame `CFr`
  (`cancelIpc_recv_cfr`, here with `r := i`, a TCB, so no notification
  changes); the endpoint `i` waits on loses `i`; it was a receive queue
  (FL4's queue codes: `JAtZ.epQ_code`, l4v `valid_ep`), so it is no send
  queue after (its head would have been a receiver before, kept by
  `cancelOther_keep`, or `i`, inactive after);
* SCs keep their bound thread (`IK`, `ikm_cancelIpc`); the head sender
  of a send queue is not `i` (its queue code is a sender's), so keeps its TCB.
-/
import Fl4Proofs.P3.XTopJointKEntry23M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- The notification or endpoint an object is (`none` for any other). -/
def neO : Option KernelObject → Option KernelObject
  | some (.notification x) => some (.notification x)
  | some (.endpoint x) => some (.endpoint x)
  | _ => none

/-- The notification or endpoint at `p`. -/
def neV (p : ObjRef) (σ : State Unit) : Option KernelObject := neO (σ.kheap p)

theorem neO_some {o k : Option KernelObject} (h : neO o = k) (hk : k ≠ none) : o = k := by
  subst h
  rcases o with _ | k0
  · exact absurd rfl hk
  · cases k0 <;> first | rfl | exact absurd rfl hk

theorem neO_of_aType {k o : KernelObject} (hA : aType k = aType o) (ho : neO (some o) = none) :
    neO (some k) = none := by
  cases k with
  | notification y =>
    exfalso
    cases o with
    | notification z => exact absurd ho (by simp [neO])
    | cnode sz cs => simp only [aType] at hA; split at hA <;> cases hA
    | schedContext z n => simp only [aType] at hA; split at hA <;> cases hA
    | _ => cases hA
  | endpoint y =>
    exfalso
    cases o with
    | endpoint z => exact absurd ho (by simp [neO])
    | cnode sz cs => simp only [aType] at hA; split at hA <;> cases hA
    | schedContext z n => simp only [aType] at hA; split at hA <;> cases hA
    | _ => cases hA
  | _ => rfl

section
variable {p : ObjRef}

theorem ne_setObject (q : ObjRef) (o : KernelObject) (ho : neO (some o) = none) :
    FK (neV p) (setObject (Z := Unit) q o) := by
  intro σ x hx
  obtain ⟨⟨k, hk, hA⟩, e⟩ := MidRun.setObject_out hx
  rw [e]
  simp only [neV, Function.update_apply]
  split
  · next hc => subst hc; rw [hk, ho, neO_of_aType hA ho]
  · rfl

theorem ne_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    FK (neV p) (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo
  repeat' dk_step0

/-- **`reply_remove_tcb` keeps every notification and endpoint.** -/
theorem ne_replyRemoveTcb (t r : ObjRef) : FK (neV p) (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb replyUnlinkTcb getReply getReplyObjRef setReplyObjRef setThreadState setThreadStateAct setSchedulerAction threadSet
    getThreadState threadGet getSkObjRef getSimpleKo updateSkObjRef setSimpleKo getSchedContext
    updateSchedContext setSchedContext
  repeat' (first | exact ne_setObject _ _ rfl | exact ne_getSimpleKo _ _ | dk_step0)

end

/-- **The spec's `cancel_ipc` of a thread blocked on a reply keeps every
notification and endpoint.** -/
theorem cancelReply_ne {σ σ' : State Unit} {i : ObjRef} {x : Tcb} (hk : σ.kheap i = some (.tcb x))
    {q : ObjRef} (hst : x.tcbState = .blockedOnReply q) (hm : ((), σ') ∈ (cancelIpc (Z := Unit) i σ).1)
    (p : ObjRef) : neV p σ' = neV p σ := by
  have e2 : cancelIpc (Z := Unit) i σ =
      replyRemoveTcb i q (updK σ i (.tcb { x with tcbFault := none })) := by
    unfold cancelIpc
    rw [Notif.nd_bind_one (Notif.getThreadState_eq hk), Notif.nd_bind_one (Notif.threadSet_eq _ hk), hst]
  rw [e2] at hm
  refine (ne_replyRemoveTcb (p := p) i q _ _ hm).trans ?_
  simp only [neV, updK, Function.update_apply]
  split
  · next hc => subst hc; rw [hk]; rfl
  · rfl

/-- **The spec's `cancel_ipc` of a thread receiving keeps every
notification** (`CFr` with `r := i`). -/
theorem cfr_ntfn {σ σ' : State Unit} {i : ObjRef} {x : Tcb} (hk : σ.kheap i = some (.tcb x))
    (F : CFr i i σ σ') {n : ObjRef} {xn : Notification} (h : σ'.kheap n = some (.notification xn)) :
    σ.kheap n = some (.notification xn) := by
  rcases F.kh n with e | ⟨o, o', h1, h2, hc⟩
  · rw [← e]; exact h
  · rw [h2] at h
    cases h
    rcases hc with ⟨x0, st, bn, fl, ar, rfl, e', -⟩ | ⟨hn, -⟩ | ⟨x0, y0, rfl, e', -, -⟩ | ⟨x0, rfl, e', -⟩
    · cases e'
    · rcases hn with ⟨_, _, _, _, -, e', -⟩ | ⟨_, _, _, _, -, e', -⟩ | ⟨x0, y0, rfl, -, hp, -⟩
      · cases e'
      · cases e'
      · rw [hp, hk] at h1; cases h1
    · cases e'
    · cases e'

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **FL4's endpoint queue codes** (l4v `valid_ep`): a member of a send queue
is a TCB blocked sending, of a receive queue one blocked receiving
(`EpObjRel`'s `QueuedOn`, `TcbRelE.st`). -/
theorem JAtZ.epQ_code {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p : Fl4Spec.ObjRef} {x : Fl4Spec.Endpoint} (hk : σ.kheap p = some (.endpoint x)) {u : Fl4Spec.ObjRef}
    (hu : u ∈ x.epQueue) :
    ∃ xt, σ.kheap u = some (.tcb xt) ∧ (∀ l, x = .sendEP l → tsCode xt.tcbState = 4) ∧
      (∀ l, x = .recvEP l → tsCode xt.tcbState = 3) := by
  obtain ⟨e, he, rfl⟩ := J.obj.ep _ x hk
  have hR := (J.xtop.irelK J.ks J.buf).1.toE
  have hO := hR.at_ep he hk
  cases x with
  | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hu
  | sendEP l0 =>
    obtain ⟨-, xs, -, rfl, hQ, hB⟩ := hO
    simp only [Fl4Spec.Endpoint.epQueue, List.mem_map] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨xt, hkt, hrel⟩ := hR.tcb y (hQ.mem y hy)
    exact ⟨xt, hkt, ⟨fun _ _ => hrel.st.symm.trans (hB y hy).1, fun _ h => Fl4Spec.Endpoint.noConfusion h⟩⟩
  | recvEP l0 =>
    obtain ⟨-, xs, -, rfl, hQ, hB⟩ := hO
    simp only [Fl4Spec.Endpoint.epQueue, List.mem_map] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨xt, hkt, hrel⟩ := hR.tcb y (hQ.mem y hy)
    exact ⟨xt, hkt, ⟨fun _ h => Fl4Spec.Endpoint.noConfusion h, fun _ _ => hrel.st.symm.trans (hB y hy).1⟩⟩

variable {Z Z' : XSets} {H H' : P1.Heap} {Cs Cs' Ac Ac' : Set U64} {Lst Lst' : U64 → List U64} {D D' : Set U64}
  {s s' : S} {a a' : A} {σ σ' : Fl4Spec.State Unit}

/-- The linked thread's cancel: what the two transfers below share. -/
structure CancelLinkAt (σ σ' : Fl4Spec.State Unit) (i q : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) : Prop where
  hk : σ.kheap i = some (.tcb x)
  hst : x.tcbState = .blockedOnReply q ∨ ∃ e d, x.tcbState = .blockedOnReceive e (some q) d
  hne : σ.curThread ≠ i
  hm : ((), σ') ∈ (Fl4Spec.cancelIpc (Z := Unit) i σ).1
  hin : ∃ y, σ'.kheap i = some (.tcb y) ∧ y.tcbState = .inactive

theorem CancelLinkAt.code {i q : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (C : CancelLinkAt σ σ' i q x) :
    tsCode x.tcbState = 5 ∨ tsCode x.tcbState = 3 := by
  rcases C.hst with h | ⟨e, d, h⟩ <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **A send queue after the cancel was one before.** -/
theorem cancelLink_sendEP (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ') {i q : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (C : CancelLinkAt σ σ' i q x) {p sd : Fl4Spec.ObjRef} {l : List Fl4Spec.ObjRef}
    (h : σ'.kheap p = some (.endpoint (.sendEP (sd :: l)))) :
    σ.kheap p = some (.endpoint (.sendEP (sd :: l))) := by
  rcases C.hst with hst | ⟨e, d, hst⟩
  · have e1 := cancelReply_ne C.hk hst C.hm p
    unfold neV at e1
    rw [h] at e1
    exact neO_some e1.symm (by simp [neO])
  · obtain ⟨xe, hke, hq⟩ := J.sv.recvQ i x e (some q) d C.hk hst
    have F := (Sched.cancelIpc_recv_cfr (r := i) C.hk hst hke hq
      (fun rp h => J.sv.recvReply i x e rp d C.hk (by rw [hst, h])) C.hm).1
    obtain ⟨-, -, -, -, hkeep⟩ := cancelOther_keep C.hm C.hne
    rcases F.kh p with e1 | ⟨o, o', h1, h2, hc⟩
    · rw [← e1]; exact h
    · exfalso
      rw [h2] at h
      cases h
      rcases hc with ⟨_, _, _, _, _, -, e', -⟩ | ⟨hn, hnt⟩ | ⟨x0, y0, rfl, e', hsub, hmem⟩ | ⟨_, -, e', -⟩
      · cases e'
      · rcases hn with ⟨_, _, _, _, -, e', -⟩ | ⟨_, _, _, _, -, e', -⟩ | ⟨_, _, -, e', -⟩ <;> cases e'
      · cases e'
        have hsd : sd ∈ x0.epQueue := hsub.subset (by simp [Fl4Spec.Endpoint.epQueue])
        obtain ⟨xs', hks', hc4, -⟩ := J'.epQ_code h2 (u := sd) (by simp [Fl4Spec.Endpoint.epQueue])
        have c4 := hc4 _ rfl
        cases x0 with
        | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hmem
        | sendEP l0 =>
          obtain ⟨xi, hki, hci, -⟩ := J.epQ_code h1 hmem
          rw [C.hk] at hki; cases hki
          have := hci _ rfl
          rw [hst] at this; cases this
        | recvEP l0 =>
          obtain ⟨xd, hkd, -, hcd⟩ := J.epQ_code h1 hsd
          have c3 := hcd _ rfl
          by_cases hdi : sd = i
          · subst hdi
            obtain ⟨y, hy, hy0⟩ := C.hin
            rw [hks'] at hy; cases hy
            rw [hy0] at c4; cases c4
          · rw [hkeep sd xd hdi hkd] at hks'; cases hks'
            rw [c3] at c4; cases c4
      · cases e'

/-- **A notification after the cancel was the same before.** -/
theorem cancelLink_ntfn (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {i q : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (C : CancelLinkAt σ σ' i q x) {n : Fl4Spec.ObjRef} {xn : Fl4Spec.Notification}
    (h : σ'.kheap n = some (.notification xn)) : σ.kheap n = some (.notification xn) := by
  rcases C.hst with hst | ⟨e, d, hst⟩
  · have e1 := cancelReply_ne C.hk hst C.hm n
    unfold neV at e1
    rw [h] at e1
    exact neO_some e1.symm (by simp [neO])
  · obtain ⟨xe, hke, hq⟩ := J.sv.recvQ i x e (some q) d C.hk hst
    exact cfr_ntfn C.hk (Sched.cancelIpc_recv_cfr (r := i) C.hk hst hke hq
      (fun rp h => J.sv.recvReply i x e rp d C.hk (by rw [hst, h])) C.hm).1 h

/-- **`IpcActDon` after the cancel was so before** (module docstring). -/
theorem cancelLink_actDon (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {i q : Fl4Spec.ObjRef}
    {x : Fl4Spec.Tcb} (C : CancelLinkAt σ σ' i q x) (h : IpcActDon σ') : IpcActDon σ := by
  obtain ⟨xt, n, xn, hkt, hbn, hkn, hact, c, y, k, hc, hky, hyt⟩ := h
  obtain ⟨hct', -, -, -, hkeep⟩ := cancelOther_keep C.hm C.hne
  have hIK : IK i σ σ' := Sched.ikm_cancelIpc (t := i) σ ((), σ') C.hm
  -- ct's TCB
  rw [hct'] at hkt
  have hO := hIK.1 σ.curThread
  rw [hkt] at hO
  obtain ⟨xt0, hkt0⟩ : ∃ xt0, σ.kheap σ.curThread = some (.tcb xt0) := by
    cases ho : σ.kheap σ.curThread with
    | none => rw [ho] at hO; simp [OIK] at hO
    | some o =>
      rw [ho] at hO; simp only [OIK] at hO
      obtain ⟨x0, rfl⟩ := hO.2.2.2.1 xt rfl
      exact ⟨x0, rfl⟩
  have e0 := hkeep _ _ C.hne hkt0
  rw [hkt] at e0
  simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at e0
  subst e0
  -- the SC's bound thread
  have hS := hIK.1 c
  rw [hky] at hS
  obtain ⟨y0, hky0, hyt0⟩ : ∃ y0, σ.kheap c = some (.schedContext y0 k) ∧ y0.scTcb = none := by
    cases ho : σ.kheap c with
    | none => rw [ho] at hS; simp [OIK] at hS
    | some o =>
      rw [ho] at hS; simp only [OIK] at hS
      obtain ⟨x0, m0, rfl⟩ := hS.2.2.2.2.1 y k rfl
      obtain ⟨y2, e2, hik⟩ := hS.2.1 x0 m0 rfl
      cases e2
      exact ⟨x0, rfl, hik.2.2.2.1.symm.trans hyt⟩
  exact ⟨xt, n, xn, hkt0, hbn, cancelLink_ntfn J C hkn, hact, c, y0, k, hc, hky0, hyt0⟩

/-- **`IpcPushDon` after the cancel was so before** (module docstring). -/
theorem cancelLink_pushDon (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (J' : JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σ') {i q : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (C : CancelLinkAt σ σ' i q x) {p : Fl4Spec.ObjRef} {rc : capability.Cap} (h : IpcPushDon σ' p rc) :
    IpcPushDon σ p rc := by
  obtain ⟨sd, l, xs, hke, hks, hsc, hok⟩ := h
  have hke0 := cancelLink_sendEP J J' C hke
  obtain ⟨-, -, -, -, hkeep⟩ := cancelOther_keep C.hm C.hne
  obtain ⟨xd, hkd, hc4, -⟩ := J.epQ_code hke0 (u := sd) (by simp [Fl4Spec.Endpoint.epQueue])
  have hdi : sd ≠ i := by
    rintro rfl
    rw [C.hk] at hkd; cases hkd
    have := hc4 _ rfl
    rcases C.code with h | h <;> rw [h] at this <;> cases this
  rw [hkeep sd xd hdi hkd] at hks
  simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hks
  subst hks
  exact ⟨sd, l, xd, hke0, hkd, hsc, hok⟩

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread at a
`MidN` state outside the two donations** (module docstring). -/
theorem jRecvIpcLinkN (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (q : U64) (g' : Bool) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) (hcr : CapRel (.Reply q g') rc')
    {xr : Fl4Spec.Reply} (hkr : σ.kheap q.bv = some (.reply xr))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : JHeld (L := L) Z.th s (.Reply q g')) (hi0 : L.mem s (rTcbA q) ≠ 0#u64)
    (hAD : ¬ IpcActDon σ) (hPD : ¬ IpcPushDon σ p.bv (.Reply q g')) :
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
  have C : CancelLinkAt σ σ' i.bv q.bv xi := ⟨hki, hsti, hne, hm, hin⟩
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
  obtain ⟨x0, hk0, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct ht
  have hk0' : σ'.kheap ct.bv = some (.tcb x0) := hkeep ct.bv x0 (fun e => hict (P1.eq_of_bv e.symm)) hk0
  have hrun' : CurRun σ' := fun x hx => by
    rw [hct', hcur, hk0'] at hx
    simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
    subst hx
    exact hni.run x0 (by rw [hcur]; exact hk0)
  have hN' : MidN σ' := ⟨by rw [hct', hid']; exact hni.1, hrun', by rw [hact']; exact hni.2.2.1,
    fun x hx => by
      rw [hct', hcur, hk0'] at hx
      simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hx
      subst hx
      exact hni.2.2.2 x0 (by rw [hcur]; exact hk0)⟩
  exact jRecvIpcUN (Z := Z.mv Z.G V) hAT hmax htu J' ht (hct'.trans hcur) hN'
    (by rw [hct', hrq']; exact hnq) p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩) (fun h => hAD (cancelLink_actDon J C h))
    (fun h => hPD (cancelLink_pushDon J J' C h))

end

end

end Fl4Proofs.P3
