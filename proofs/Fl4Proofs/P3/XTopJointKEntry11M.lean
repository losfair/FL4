/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch16): **`kernel_entryJ11M`:
`JMidLeavesHyp` narrowed by the endpoint receives proved under a pending
switch.** sch15's `JMidLeavesHyp` [W] asked `receive_ipc` at every non-resumed
mid state. At a switch mid state (`MidE`, action `switchThread u`, u ≠ ct)
the following cases of a null or free reply are proved here, ending in
`JAtZR`:

* `JAtZ.recvIpcActJM`: an active bound notification (`JAtZ.recvIpcActJ`
  from `MidE`: `CurInv` by `J.curInv hni.ncn`, `CanBlock` by
  `canBlockCurM`; post `JAtZ`, so `.toR`).
* the blocking wait without a bound notification (`JAtZ.recvIpcBlockJM`,
  XTopJointRecvIpcBlockM) and with a bound idle or waiting one whose SC is
  not the thread's (`JAtZ.recvIpcBlockNJGM`);
* a head sender in `RecvSendBasicCase` (no reply pushed, the sender not
  woken) without the bound SC return: `JAtZ.recvSendJ0X` reads no action.

`IpcDoneM` collects these cases, `jRecvIpcDoneM` proves them.
`JRecvLeavesRN2` is `JRecvLeavesRN` with the endpoint receive asked only
under `IpcOpen` (a pending reschedule, or not `IpcDoneM`: a linked reply,
the bound SC return, a sender pushing a reply or woken, a timeout-fault
sender); `JRecvLeavesRN2.toRN` recovers `JRecvLeavesRN` at a non-resumed
mid state with no switch to ct. `JMidLeavesHyp2` [W] is `JMidLeavesHyp`
concluding `JRecvLeavesRN2` (same l4v counterpart: receive_ipc_corres /
receive_signal_corres / handle_fault_corres inside handle_recv_corres under
scheduler_act_sane; each remaining case is a case of sch15's premise, true in
reachable states), `jMidLeavesHyp_of2`, `KDispHyps11M`, `.to10M`, NEW TOP
`kernel_entryJ11M` = `kernel_entryJ10M` with `KDispHyps11M`.
-/
import Fl4Proofs.P3.XTopJointRecvIpcBlockM
import Fl4Proofs.P3.XTopJointKEntry10M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 16000000 in
/-- **`receive_ipc` with an active bound notification at `J`** (module
docstring): the current thread at a mid state (`MidE`: resumed or a switch
to another thread pending), as `JAtZ.recvSigActiveJM`. -/
theorem JAtZ.recvIpcActJM (hAT : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (hcur : σ.curThread = t.bv)
    (hni : MidE σ) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    {xt : Fl4Spec.Tcb} (hkt0 : σ.kheap t.bv = some (.tcb xt))
    {n : U64} (hn : n ∈ Z.N) {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hbn : xt.tcbBoundNotification = some n.bv) {b0 : Fl4Spec.Badge} (hact : x.ntfnObj = .activeNtfn b0)
    (blk : Bool) {e : U64} {xe : Fl4Spec.Endpoint} (hke : σ.kheap e.bv = some (.endpoint xe))
    (cb : U64) (c1 c2 c3 c4 : Bool)
    {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64} (hrc : ReplyArg Z.R (L.mem s) rc rc' rv)
    (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st arI s a t (.Endpoint e cb c1 c2 c3 c4) blk rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) blk rc' σ).1,
        RJ (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  have hI := J.xtop.irelK J.ks J.buf
  have hC : CurInv σ := J.curInv hni.ncn
  have hkt := hkt0
  obtain ⟨xc, hkc, hscc, -⟩ := hC.tcb
  rw [hcur, hkt] at hkc; cases hkc
  obtain ⟨ys, ms, hks⟩ := hC.sc
  have hrn : Fl4Spec.runnable xt.tcbState = true := hni.run xt (by rw [hcur]; exact hkt)
  have hcb := J.canBlockCurM ht hcur hkt hrn hni.1 (by rw [← hcur]; exact hC.notRel) (hni.sa (x := xt) hcur) hnq
  -- the badge register
  have hx := hI.1.toN.at_ntfn hn hk
  have hst : stOf (L.mem s) n = obj.NTFN_ACTIVE := stOf_active (T := Z.T) (hact ▸ hx.obj) rfl
  have hb0 : (L.mem s (nBadgeA n)).bv = b0 := by
    have := hx.obj; rw [hact] at this; exact this.2.2
  have hXb := badge_wr_irel J.ip hI ht hkt (L.mem s (nBadgeA n))
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ ht hkt Fl4Spec.badge_register _ hXb
  rw [hb0] at J1
  have hnt : n.bv ≠ t.bv := by intro e; rw [e, hkt] at hk; cases hk
  have hk1 : (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))).kheap n.bv = some (.notification x) := by
    simp [updK, hnt, hk]
  -- the notification's state
  have hI1 := J1.xtop.irelK J1.ks J1.buf
  obtain ⟨hR2, hW2, hS2⟩ := set_idle_relI J1.ip hI1.1 hn hk1 hact
  have hSch2 := hI1.2.2.1.stable hW2 hS2
  obtain ⟨Q, R, hc, hs⟩ := hSch2.lists
  obtain ⟨xt2, hkt2, -, -, hsct2, -⟩ := hs.tcb t ht
  have hkt2' : (updK (updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register b0))) n.bv
      (.notification (Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x))).kheap t.bv =
      some (.tcb (setReg xt Fl4Spec.badge_register b0)) := by
    simp [updK, hnt.symm]
  rw [hkt2'] at hkt2; cases hkt2
  have hsw : optRef (L.mem (recvActS st s t n) (P1.scA t)) = some σ.curSc := hsct2.symm.trans hscc
  have h0 : L.mem (recvActS st s t n) (P1.scA t) ≠ 0#u64 := by
    intro e; rw [e, optRef_zero] at hsw; cases hsw
  have hcw : L.mem (recvActS st s t n) (P1.scA t) =
      Sched.nodeW st (recvActS st s t n) (L.cpu (recvActS st s t n)) layout.node.CUR_SC := by
    apply P1.eq_of_bv
    rw [Notif.optRef_ne h0] at hsw
    rw [Option.some.inj hsw]
    exact hs.curSc.trans (congrArg (fun q => (Sched.nodeW st (recvActS st s t n) q layout.node.CUR_SC).bv) hc.cur).symm
  have heq := spec_eq_ok (receive_signal_active_eq (arI := arI) (a := a) blk hst h0 hcw)
  -- P1's `BlkOK` after
  obtain ⟨⟨Q0, R0, h0'⟩, hB0, hX0, hS0, hSg0⟩ := J.blk
  have p1 := P1.notification.receive_signal.ipc hAT s a t n blk Q0 R0 h0' hB0 hX0 hS0 hSg0 hcb
    (J.zH.2.2.2 n hn) (J.zH.2.2.2 n hn) (by rw [epState_eq, hst, ntfn_consts.2.2]; decide)
  rw [heq, WP.spec_ok] at p1
  simp only [WP.uncurry'_pair] at p1
  -- the notification write at `J`
  have hxw : ∀ l, x.ntfnObj ≠ .waitingNtfn l := fun l h => by rw [hact] at h; cases h
  obtain ⟨σ', V', hsp', -, J2⟩ := J1.signal_badge_post hn hk1 hxw
    (y := Fl4Spec.ntfnObjUpdate (fun _ => .idleNtfn) x) (fun l h => by cases h) rfl rfl rfl
    ⟨_, rfl, hR2, hS2, hW2, NoBlock.ntfnUpd _ _ _⟩ p1
  obtain rfl := (congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (Prod.mk.inj hsp').1))
  -- the spec's outcome and FL4's
  have hct : σ.curSc ≠ t.bv := fun e => by rw [e, hkt] at hks; cases hks
  have hcn : σ.curSc ≠ n.bv := fun e => by rw [e, hk] at hks; cases hks
  have hxt := hI.1.toE.at_tcb ht hkt
  have hb1 : optRef (L.mem s (tBoundA t)) = some n.bv := hxt.bound.symm.trans hbn
  have hbz : L.mem s (tBoundA t) ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb1; cases hb1
  have hbound : L.mem s (tBoundA t) = n := by
    rw [Notif.optRef_ne hbz] at hb1; exact P1.eq_of_bv (Option.some.inj hb1)
  have ht0 : t ≠ 0#u64 := fun e => by
    obtain ⟨Q1, R1, hc1, -⟩ := J.xtop.fin.1.1.1.lists
    exact (hc1.tcbs t ht).ne0 (by rw [e]; rfl)
  have heqI := spec_eq_ok (receive_ipc_preA (ar := arI) s a t e cb c1 c2 c3 c4 blk rc rc' rv hrc hbound
    (by rw [← hbound]; exact hbz) hst (complete_signal_cur_eq (arI := arI) (a := a) ht0 hst h0 hcw))
  have hspecI := receiveIpc_active b rights blk (replyArg_spec J.ip.e hI.1.toE hrc) hkt hbn hke hk hact
  rw [hspecI, completeSignal_cur hkt hk hact hscc hks hct hcn hnt, heqI, WP.spec_ok]
  exact ⟨_, Set.mem_singleton _, J2.xtop.relTop, _, _, _, _, _, _, J2⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The current thread's bound notification (if any) does not lend it its
SC (no SC return before the receive). -/
def NoRetM (ct : U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ xt n xn, σ.kheap ct.bv = some (.tcb xt) → xt.tcbBoundNotification = some n →
    σ.kheap n = some (.notification xn) → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)

/-- **The endpoint receives proved at a switch mid state** (module
docstring). -/
def IpcDoneM (ct : U64) (s : S) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) : Prop :=
  RecvIpcActCase (L := L) ct s σ rc ∨ RecvIpcBlockCase (L := L) ct true s σ p rc ∨
    (RecvIpcBoundCase (L := L) ct true s σ p rc ∧ NoRetM ct σ) ∨
    ((rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) ∧
      RecvSendBasicCase ct true σ p rc ∧ NoRetM ct σ)

/-- The endpoint receives `JRecvLeavesRN2` still asks (module docstring). -/
def IpcOpen (ct : U64) (s : S) (σ : Fl4Spec.State Unit) (p : U64) (rc : capability.Cap) : Prop :=
  σ.schedulerAction = .chooseNewThread ∨ ¬ IpcDoneM (L := L) ct s σ p rc

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`IpcDoneM`'s receives at a switch mid state** (module docstring). -/
theorem jRecvIpcDoneM (hAT : P0.ArchTotal arI) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hD : IpcDoneM (L := L) ct s σ p rc) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ := by
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  rcases hD with hca | hcb | ⟨hcn, hnr0⟩ | ⟨hun, hcs, hnr0⟩
  · obtain ⟨⟨xt, n0, x, b0, hkt, hbn, hkn, hact⟩, hrr⟩ := hca
    obtain ⟨n, hn, rfl⟩ := J.obj.ntfn _ x hkn
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    exact WP.spec_mono (J.recvIpcActJM hAT ht hcur hni hnq hkt hn hkn hbn hact true hke b sd true g gr hra b.bv
      (rightsOf sd true g gr)) fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ =>
        ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩
  · obtain ⟨-, hbn, hns, hrr⟩ := hcb
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hrr
    have hI := J.xtop.irelK J.ks J.buf
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
    exact J.recvIpcBlockJM ht hcur hni hsw hnq hkt he hke hcB hcov hra hcovR b sd true g gr b.bv
      (rightsOf sd true g gr) (fun h => receive_ipc_block_red hra hbound hst2 h)
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
    exact J.recvIpcBlockNJGM ht hcur hni hsw hnq hkt hn hbn hkn hna (hnr0 xt _ xn hkt hbn hkn) he hke hcB hcov hra
      hcovR b sd true g gr b.bv (rightsOf sd true g gr)
  · obtain ⟨hbn, sd0, q, xs, hke', hks, hok⟩ := hcs
    obtain ⟨sdU, -, hsde⟩ := J.obj.tcb _ xs hks
    subst hsde
    have hI := J.xtop.irelK J.ks J.buf
    obtain ⟨xt, hkt, -⟩ := hI.1.tcb ct ht
    obtain ⟨rv, hra⟩ := J.replyArg_of hrc hun
    have hrun := hni.run xt (by rw [hcur]; exact hkt)
    have hbN : xt.tcbBoundNotification = none ∨ ∃ n xn, xt.tcbBoundNotification = some n ∧
        σ.kheap n = some (.notification xn) ∧ Fl4Spec.isActive xn = false ∧
        (true = true → ¬ (xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none)) := by
      rcases hbn xt hkt with hb0 | ⟨n0, xn, hbn0, hkn, hna⟩
      · exact Or.inl hb0
      · exact Or.inr ⟨n0, xn, hbn0, hkn, hna, fun _ => hnr0 xt n0 xn hkt hbn0 hkn⟩
    exact WP.spec_mono (J.recvSendJ0X ht hkt hrun hbN hcur he hke' hks b sd true g gr hra hok b.bv
      (rightsOf sd true g gr)) fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'⟩ =>
        ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'.toR⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN` with the endpoint receive narrowed to `IpcOpen`**
(module docstring). -/
structure JRecvLeavesRN2 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    IpcOpen (L := L) ct s σ p rc →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → SigOpen σ p →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, narrowed**
(module docstring): sch15's `JMidLeavesHyp` concluding `JRecvLeavesRN2`. -/
def JMidLeavesHyp2 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN2 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN` from `JRecvLeavesRN2`** at a non-resumed mid state
with no switch to ct: `jRecvIpcDoneM` outside `IpcOpen`. -/
theorem JRecvLeavesRN2.toRN (hAT : P0.ArchTotal arI) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN2 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN (L := L) arI AR Z.th ct s a σ where
  sig := h.sig
  flt := h.flt
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr => by
    by_cases ho : IpcOpen (L := L) ct s σ p rc
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd (Or.inl e) ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      exact jRecvIpcDoneM hAT J hctT hcur hE hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr
        (Classical.not_not.1 fun hd => ho (Or.inr hd))

/-- **`JMidLeavesHyp` from `JMidLeavesHyp2`** (module docstring). -/
theorem jMidLeavesHyp_of2 (hAT : P0.ArchTotal arI) {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp2 (L := L) arI AR cptr σ) : JMidLeavesHyp (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN hAT J hct hni1 hrun ha hsw hnq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with the mid receive leaves narrowed**
(module docstring). -/
structure KDispHyps11M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (n : I64) (c : Fl4Spec.Syscall) : Prop where
  inv : ∀ ct call bl don, sched.cur_thread st s = ok ct → InvSys n call bl don →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct call bl don false (L.mem s (regA ct layout.reg.CAP))
  recv : ∀ bl cr, RecvSys n bl cr → (∀ d p, σ.curThread ∉ σ.readyQueues d p) ∧
    (∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler)
  mid : ∀ ct rg sr cr, sched.cur_thread st s = ok ct → MidSysR n c rg sr cr →
    JEntryGlob (L := L) arI AR Z.th ∧ JEntryAt (L := L) arI AR Z H Cs s a σ ∧
    JPathAt (L := L) arI AR Z H Cs D s a σ ct false false true true (L.mem s (regA ct rg)) ∧
    MidRun.JMidPerfHypQ true (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidVfhHyp (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ ∧
    JMidLeavesHyp2 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

theorem KDispHyps11M.to10M (hAT : P0.ArchTotal arI) {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHyps11M (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps10M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidLeavesHyp_of2 hAT h6⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ10M`
with `KDispHyps11M` (mid: entry facts, `JMidPerfHypQ` [W], `JMidVfhHyp` [J],
`JMidLeavesHyp2` [W]) for `KDispHyps10M` (module docstring). -/
theorem kernel_entryJ11M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps11M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hPP : PPPlat arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hIP : IrqPlat arI AR)
    (hNS : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit), JHoleAt (L := L) arI AR s a σ → NativeScope σ)
    (hNSR : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A)
      (σ : Fl4Spec.State Unit), JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ → NativeScope σ)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) :
    syscall.handle_syscall_old st arI s a n ⦃ r => KPost (L := L) arI AR c σ r ⦄ :=
  kernel_entryJ10M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to10M hA)
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
