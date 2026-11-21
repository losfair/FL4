/-
P3 (DESIGN.md §9), receive at a mid state (KENTRY-PLAN sch29): **every
endpoint `receive_ipc` at a `chooseNewThread` mid state where ct has no SC**
(`MidN`), the reply-push donation (`IpcPushDon`) included.

* `jRecvIpcUD` (sch29gen/gen2.py, from XTopJointRecvIpcN's `jRecvIpcUN`):
  the head sender pushing a reply WITH an SC (call, or a fault other than a
  timeout: `PushOK`) is XTopJointRecvSendPDD's `JAtZ.recvSendPDJW` /
  `JAtZ.recvSendFPDJW` (`reply_push` donates the sender's SC to ct: FL4's
  `can_donate` true, ct's SC word 0; the SC released at the block by
  `Inv.rd` of the blocked-on-send sender or `Inv.scRef`; the current SC any,
  `CurOwnW` from `JAtZ.own`); the SC is in `Z.C` by `SchedSpec.scMem`.
* `jRecvIpcUDD`, `jRecvIpcLinkDD`: XTopJointRecvIpcActDonD's `jRecvIpcUDN` /
  `jRecvIpcLinkDN` without `¬ IpcPushDon`.
-/
import Fl4Proofs.P3.XTopJointRecvSendPDD
import Fl4Proofs.P3.XTopJointRecvIpcActDonD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` with a null or free reply at a `MidN` state without an
active bound notification** (module docstring): XTopJointRecvIpcN's `jRecvIpcUN` without `¬ IpcPushDon`. -/
theorem jRecvIpcUD (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64)
    (hAD : ¬ IpcActDon σ) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hD := ipcDoneM3_of J ht hpE hun
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  have hI := J.xtop.irelK J.ks J.buf
  have hS0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → x.tcbSchedContext = none := fun x hx =>
    hni.2.2.2 x (by rw [hcur]; exact hx)
  have hR0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → ct.bv ∉ σ.releaseQueue := fun x hx =>
    J.inv.notRel_of_noSc hx (hS0 x hx)
  have hU0 : ∀ x, σ.kheap ct.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = true := fun x hx =>
    hni.run x (by rw [hcur]; exact hx)
  have hnl : ¬ LendM ct σ := fun hL => by
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨n, xn, -, -, -, h1, h2⟩ := hL xt hkt
    exact h2 (h1.trans (hS0 xt hkt))
  suffices hRJ : endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ from
    WP.spec_mono hRJ fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  rcases hD with ((hca | hcb | ⟨hcn, hnr0⟩ | ⟨hun', hcs, hnr0⟩) | ⟨hun', hcp | hcT⟩) | hR
  · obtain ⟨⟨xt, n0, x, b0, hkt, hbn, hkn, hact⟩, hrr⟩ := hca
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hnd : x.ntfnSc = none ∨
        ∃ q y k, x.ntfnSc = some q ∧ σ.kheap q = some (.schedContext y k) ∧ y.scTcb ≠ none := by
      cases hq : x.ntfnSc with
      | none => exact Or.inl rfl
      | some q =>
        obtain ⟨y0, m0, hky, -⟩ := J.ntfn_link hn x q hkn hq
        exact Or.inr ⟨q, y0, m0, rfl, hky, fun h0 =>
          hAD ⟨xt, n.bv, x, by rw [hcur]; exact hkt, hbn, hkn, ⟨b0, hact⟩, q, y0, m0, hq, hky, h0⟩⟩
    exact J.recvIpcActJN hAT ht hcur hni hnq hkt hn hkn hbn hact hnd true hke b sd true g gr hra b.bv
      (rightsOf sd true g gr)
  · obtain ⟨-, hbn, hns, hrr⟩ := hcb
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hx := hI.1.toE.at_ep he hke
    have hst2 : stOf (L.mem s) p = 0#u64 ∨ stOf (L.mem s) p = 2#u64 := by
      cases xe with
      | idleEP => exact Or.inl hx.1
      | recvEP q => exact Or.inr hx.1
      | sendEP q => exact absurd rfl (hns _ hke q)
    have hbound : L.mem s (tBoundA ct) = 0#u64 :=
      optRef_none ((hI.1.toE.at_tcb ht hkt).bound.symm.trans (hbn xt hkt))
    exact J.recvIpcBlockJG ht hcur hni.1 hnq (hR0 xt hkt) hkt (hU0 xt hkt) (Or.inr ⟨hni.2.2.1, hS0 xt hkt⟩)
      he hke hcB hcov hra hcovR b sd true g gr b.bv (rightsOf sd true g gr)
      (fun h => receive_ipc_block_red hra hbound hst2 h)
      (receiveIpc_noSend b.bv (rightsOf sd true g gr) true (replyArg_spec J.ip.e hI.1.toE hra) hkt (hbn xt hkt) hke
        (hns xe hke))
  · obtain ⟨-, ⟨xt, n0, xn, hkt, hbn, hkn, hna⟩, hns, hrr⟩ := hcn
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ xn hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hcB : Endp.CanBlock true xe := by
      cases xe with
      | idleEP => trivial
      | recvEP q => rfl
      | sendEP q => exact absurd rfl (hns _ hke q)
    obtain ⟨hcov, hcovR⟩ := J.recvCov_of he hHd hHr hra
    exact J.recvIpcBlockNJG ht hcur hni.1 hnq (hR0 xt hkt) hkt (hU0 xt hkt) (Or.inr ⟨hni.2.2.1, hS0 xt hkt⟩)
      hn hbn hkn hna (hnr0 xt _ xn hkt hbn hkn) he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
        (true = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) := by
      rcases hbn xt hkt with hb0 | ⟨n0, xn, hbn0, hkn, hna⟩
      · exact Or.inl hb0
      · exact Or.inr ⟨n0, xn, hbn0, hkn, hna, fun _ => hnr0 xt n0 xn hkt hbn0 hkn⟩
    exact J.recvSendJ0X ht hkt (hU0 xt hkt) hbN hcur he hke' hks b sd true g gr hra hok b.bv
      (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcp
    obtain ⟨sdU, hsdT, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    by_cases hxs : xs.tcbSchedContext = none
    swap
    · -- sch29: the push donates the sender's SC to ct (XTopJointRecvSendPDD)
      obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
      obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
      have hrv0 : rv ≠ 0#u64 := by
        rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
        · exact absurd h1 hok.1
        · exact (J.rp.align rv hr).2.1
      obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
      have hbN := hbn xt hkt
      obtain ⟨Q0, R0, -, hsS⟩ := J.xtop.fin.1.1.1.lists
      obtain ⟨x', hk', -, -, hscw, -⟩ := hsS.tcb sdU hsdT
      rw [hks] at hk'; cases hk'
      have hpc0 : L.mem s (P1.scA sdU) ≠ 0#u64 := fun h0 => hxs (by rw [hscw, h0, optRef_zero])
      have hpC : L.mem s (P1.scA sdU) ∈ Z.C := hsS.scMem sdU hsdT hpc0
      have hxsp : xs.tcbSchedContext = some (L.mem s (P1.scA sdU)).bv := by rw [hscw]; exact Notif.optRef_ne hpc0
      obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
      · exact J.recvSendPDJW hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hfs hpC hxsp (hS0 xt hkt)
          hni.2.2.1 (hR0 xt hkt) b sd true g gr hra (hcovR hrv0) hcl hyes hrn b.bv (rightsOf sd true g gr)
          (J.recvPreN ht hkt hbN p b sd true g gr hra)
      · exact J.recvSendFPDJW hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hft
          (fun b0 e0 => hxs (hto b0 e0)) hpC hxsp (hS0 xt hkt) hni.2.2.1 (hR0 xt hkt) b sd true g gr hra
          (hcovR hrv0) hyes hrn b.bv (rightsOf sd true g gr) (J.recvPreN ht hkt hbN p b sd true g gr hra)
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hrv0 : rv ≠ 0#u64 := by
      rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
      · exact absurd h1 hok.1
      · exact (J.rp.align rv hr).2.1
    obtain ⟨-, hcovR⟩ := J.recvCov_of he hHd hHr hra
    have hbN := hbn xt hkt
    have hA : σ.schedulerAction = .resumeCurThread ∨ (σ.schedulerAction = .chooseNewThread ∧
        ct.bv ∉ σ.releaseQueue ∧ (xs.tcbSchedContext = none ∨ xt.tcbSchedContext ≠ none)) :=
      Or.inr ⟨hni.2.2.1, hR0 xt hkt, Or.inl hxs⟩
    obtain ⟨hrn, hyes, ⟨hfs, hcl⟩ | ⟨f, hft, hto⟩⟩ := hok
    · exact J.recvSendPJGC hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hfs hA
        b sd true g gr hra (hcovR hrv0) hcl hyes hrn b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
    · exact J.recvSendFPJGC hAT ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hft hto hA
        b sd true g gr hra (hcovR hrv0) hyes hrn b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcT
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun'
    have hbN := hbn xt hkt
    have hcovR := (J.recvCov_of he hHd hHr hra).2
    obtain ⟨⟨bb, hft⟩, hsn⟩ := hok
    by_cases hp : rc ≠ .Null ∧ ∀ e' dd, xs.tcbState = .blockedOnSend e' dd →
        dd.senderCanGrant = true ∨ dd.senderCanGrantReply = true
    · have hrv0 : rv ≠ 0#u64 := by
        rcases hra with ⟨h1, -, -⟩ | ⟨_, _, _, _, hr, -⟩
        · exact absurd h1 hp.1
        · exact (J.rp.align rv hr).2.1
      exact J.recvSendFPTJ hAT hmax htu ht hkt (hU0 xt hkt) hbN hcur hni.1 hnq he hke' hks hft hsn
        (Or.inr ⟨hni.2.2.1, hR0 xt hkt⟩) b sd true g gr hra (hcovR hrv0) hp.2 hp.1 b.bv (rightsOf sd true g gr)
        (J.recvPreN ht hkt hbN p b sd true g gr hra)
    · exact J.recvSendFTJ hAT hmax htu ht hkt (hU0 xt hkt) hbN hcur he hke' hks hft hsn b sd true g gr hra
        (noPush_of hp) b.bv (rightsOf sd true g gr) (J.recvPreN ht hkt hbN p b sd true g gr hra)
  · exfalso
    rcases hR with ⟨-, hL⟩ | ⟨-, ⟨-, hL⟩ | ⟨-, hL, -⟩ | ⟨hL, -⟩⟩
    · exact hnl hL
    · exact hnl hL
    · exact hnl hL
    · exact hnl hL

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` with a null or free reply at a `MidN` state** (module
docstring): XTopJointRecvIpcActDonD's `jRecvIpcUDN` without `¬ IpcPushDon`. -/
theorem jRecvIpcUDD (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidN σ)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (Endp.rTcbA q) = 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  by_cases hAD : IpcActDon σ
  · obtain ⟨xt, n0, x, hkt, hbn, hkn, ⟨b0, hact⟩, -⟩ := hAD
    rw [hcur] at hkt
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    obtain ⟨xe, hke⟩ := hpE
    exact WP.spec_mono (J.recvIpcActDJN hAT hmb ht hcur hni hnq hkt hn hkn hbn hact true hke b sd true g gr hra
        b.bv (rightsOf sd true g gr))
      fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ => ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · exact jRecvIpcUD hAT hmax htu J ht hcur hni hnq p b sd g gr rc rc' hpE hrc hHd hHr hun hAD

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread at a
`MidN` state** (module docstring): XTopJointRecvIpcActDonD's `jRecvIpcLinkDN`
without `¬ IpcPushDon`, by `jRecvIpcUDD`. -/
theorem jRecvIpcLinkDD (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : MidN σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (q : U64) (g' : Bool) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) (hcr : CapRel (.Reply q g') rc')
    {xr : Fl4Spec.Reply} (hkr : σ.kheap q.bv = some (.reply xr))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : JHeld (L := L) Z.th s (.Reply q g')) (hi0 : L.mem s (Endp.rTcbA q) ≠ 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true (.Reply q g') ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hR := (J.xtop.irelK J.ks J.buf).1.toE
  obtain ⟨q0, hq, hqe⟩ := J.obj.reply _ xr hkr
  rw [Sched.bv_inj hqe] at hq
  have hrt : xr.replyTcb = some (L.mem s (Endp.rTcbA q)).bv := (hR.at_reply hq hkr).trans (Notif.optRef_ne hi0)
  obtain ⟨xi, hki, hsti⟩ := J.sv.replyTcb q.bv xr _ hkr hrt
  obtain ⟨i, hiT, hie⟩ := J.obj.tcb _ xi hki
  have hiq : L.mem s (Endp.rTcbA q) = i := (P1.eq_of_bv hie).symm
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
  have h0' : L.mem s1 (Endp.rTcbA q) = 0#u64 := optRef_none (hrl.symm.trans hnone)
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
  exact jRecvIpcUDD (Z := Z.mv Z.G V) hAT hmax hmb htu J' ht (hct'.trans hcur) hN'
    (by rw [hct', hrq']; exact hnq) p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩)

end

end

end Fl4Proofs.P3
