/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch17): **`kernel_entryJ15M`:
every endpoint receive at a switch mid state.** `JMidLeavesHyp5` [W]
(XTopJointKEntry14M) asked `receive_ipc` under `IpcOpen3`. At a switch mid
state (`MidE`, action `switchThread u`, u ≠ ct):

* `ipcDoneM3_of`: with a null or free reply every case is in `IpcDoneM3`
  (the case split of XTopJointRecvIpcLink's `jRecvIpcU_of` for a blocking
  receive: an active bound notification; no waiting sender with no, or a not
  active, bound notification, lending its SC or not; a head sender
  (`JAtZ.head_sendT`) in `SendOK` / `PushOK` / `TmoOK` (`sendOK_split`), the
  receiver lending its SC or not); `jRecvIpcUM` = `jRecvIpcDoneM3` of it;
* `jRecvIpcLinkM`: a reply linked to another thread: XTopJointRecvIpcLink's
  `jRecvIpcLink_of` (FL4's and the spec's `cancel_ipc` of that thread,
  `JAtZ.cancelLinkJ`) with `jRecvIpcUM` at the state after (`cancelOther_keep`:
  the action, the current thread, the ready queues and every other TCB kept,
  so `MidE` holds there).

`JRecvLeavesRN6` asks the endpoint receive only under a pending reschedule;
`.toRN5`; `JMidLeavesHyp6` [W] = `JMidLeavesHyp5` concluding `JRecvLeavesRN6`
(same l4v counterpart and truth argument as sch15/16), `jMidLeavesHyp_of6`,
`KDispHyps15M`, `.to14M`, NEW TOP `kernel_entryJ15M`.
-/
import Fl4Proofs.P3.XTopJointKEntry14M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **Every blocking receive with a null or free reply is in `IpcDoneM3`**
(module docstring). -/
theorem ipcDoneM3_of (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    {p : U64} (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x)) {rc : capability.Cap}
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) :
    IpcDoneM3 (L := L) ct s σ p rc := by
  obtain ⟨xe, hke⟩ := hpE
  obtain ⟨e, he, h⟩ := J.obj.ep _ xe hke
  rw [Sched.bv_inj h] at he
  obtain ⟨xt, hkt, -⟩ := (J.xtop.irelK J.ks J.buf).1.tcb ct ht
  -- the receiver's bound notification: none, active, or not active (lending its SC or not)
  have hB : xt.tcbBoundNotification = none ∨
      (∃ n x b0, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification x) ∧
        x.ntfnObj = .activeNtfn b0) ∨
      ∃ n xn, xt.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
        Fl4Spec.isActive xn = false := by
    rcases hb : xt.tcbBoundNotification with _ | n
    · exact Or.inl rfl
    · obtain ⟨xn, hkn⟩ := J.sv.tcbNtfn ct.bv xt n hkt hb
      cases hxo : xn.ntfnObj with
      | activeNtfn b0 => exact Or.inr (Or.inl ⟨n, xn, b0, rfl, hkn, hxo⟩)
      | idleNtfn => exact Or.inr (Or.inr ⟨n, xn, rfl, hkn, by simp [Fl4Spec.isActive, hxo]⟩)
      | waitingNtfn q => exact Or.inr (Or.inr ⟨n, xn, rfl, hkn, by simp [Fl4Spec.isActive, hxo]⟩)
  rcases hB with hb0 | ⟨n, x, b0, hbn, hkn, hact⟩ | ⟨n, xn, hbn, hkn, hna⟩
  · -- no bound notification
    have hnr : NoRetM ct σ := fun x' n' xn' hx' hb' _ => by
      rw [hkt] at hx'; cases hx'; rw [hb0] at hb'; cases hb'
    have hbA : ∀ x', σ.kheap ct.bv = some (.tcb x') → x'.tcbBoundNotification = none := fun x' hx' => by
      rw [hkt] at hx'; cases hx'; exact hb0
    by_cases hs : ∃ l, xe = .sendEP l
    · obtain ⟨l, rfl⟩ := hs
      obtain ⟨sd0, q, xs, e', dd, rfl, hks, hstd⟩ := J.head_sendT he hke
      rcases sendOK_split rc hstd with hok | hok | hok
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hun, ⟨fun x' hx' => Or.inl (hbA x' hx'),
          sd0, q, xs, hke, hks, hok⟩, hnr⟩))))
      · exact Or.inl (Or.inr ⟨hun, Or.inl ⟨fun x' hx' => Or.inl (hbA x' hx'), sd0, q, xs, hke, hks, hok⟩⟩)
      · exact Or.inl (Or.inr ⟨hun, Or.inr ⟨fun x' hx' => Or.inl (hbA x' hx'), sd0, q, xs, hke, hks, hok⟩⟩)
    · have hns : ∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q := fun x hx q e0 => by
        rw [hke] at hx; cases hx; exact hs ⟨q, e0⟩
      exact Or.inl (Or.inl (Or.inr (Or.inl ⟨rfl, hbA, hns, hun⟩)))
  · -- an active bound notification
    exact Or.inl (Or.inl (Or.inl ⟨⟨xt, n, x, b0, hkt, hbn, hkn, hact⟩, hun⟩))
  · -- a bound notification not active
    have hbN : ∀ x', σ.kheap ct.bv = some (.tcb x') → x'.tcbBoundNotification = none ∨
        ∃ n xn, x'.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
          Fl4Spec.isActive xn = false := fun x' hx' => by
      rw [hkt] at hx'; cases hx'; exact Or.inr ⟨n, xn, hbn, hkn, hna⟩
    by_cases hl : xn.ntfnSc = xt.tcbSchedContext ∧ xn.ntfnSc ≠ none
    · have hL : LendM ct σ := fun x' hx' => by
        rw [hkt] at hx'; cases hx'; exact ⟨n, xn, hbn, hkn, hna, hl⟩
      by_cases hs : ∃ l, xe = .sendEP l
      · obtain ⟨l, rfl⟩ := hs
        obtain ⟨sd0, q, xs, e', dd, rfl, hks, hstd⟩ := J.head_sendT he hke
        rcases sendOK_split rc hstd with hok | hok | hok
        · exact Or.inr (Or.inr ⟨hun, Or.inl ⟨⟨hbN, sd0, q, xs, hke, hks, hok⟩, hL⟩⟩)
        · exact Or.inr (Or.inr ⟨hun, Or.inr (Or.inl ⟨rfl, fun x' hx' => by
            rw [hkt] at hx'; cases hx'; exact ⟨n, xn, hbn, hkn, hna, hl⟩, sd0, q, xs, hke, hks, hok⟩)⟩)
        · exact Or.inr (Or.inr ⟨hun, Or.inr (Or.inr ⟨hL, sd0, q, xs, hke, hks, hok⟩)⟩)
      · have hns : ∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q := fun x hx q e0 => by
          rw [hke] at hx; cases hx; exact hs ⟨q, e0⟩
        exact Or.inr (Or.inl ⟨⟨rfl, ⟨xt, n, xn, hkt, hbn, hkn, hna⟩, hns, hun⟩, hL⟩)
    · have hnr : NoRetM ct σ := fun x' n' xn' hx' hb' hk' => by
        rw [hkt] at hx'; cases hx'; rw [hbn] at hb'; cases hb'; rw [hkn] at hk'; cases hk'; exact hl
      have hbN' : ∀ x', σ.kheap ct.bv = some (.tcb x') → x'.tcbBoundNotification = none ∨
          ∃ n xn, x'.tcbBoundNotification = some n ∧ σ.kheap n = some (.notification xn) ∧
            Fl4Spec.isActive xn = false ∧ (true = true → ¬ (xn.ntfnSc = x'.tcbSchedContext ∧ xn.ntfnSc ≠ none)) :=
        fun x' hx' => by
          rw [hkt] at hx'; cases hx'; exact Or.inr ⟨n, xn, hbn, hkn, hna, fun _ => hl⟩
      by_cases hs : ∃ l, xe = .sendEP l
      · obtain ⟨l, rfl⟩ := hs
        obtain ⟨sd0, q, xs, e', dd, rfl, hks, hstd⟩ := J.head_sendT he hke
        rcases sendOK_split rc hstd with hok | hok | hok
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨hun, ⟨hbN, sd0, q, xs, hke, hks, hok⟩, hnr⟩))))
        · exact Or.inl (Or.inr ⟨hun, Or.inl ⟨hbN', sd0, q, xs, hke, hks, hok⟩⟩)
        · exact Or.inl (Or.inr ⟨hun, Or.inr ⟨hbN', sd0, q, xs, hke, hks, hok⟩⟩)
      · have hns : ∀ x, σ.kheap p.bv = some (.endpoint x) → ∀ q, x ≠ .sendEP q := fun x hx q e0 => by
          rw [hke] at hx; cases hx; exact hs ⟨q, e0⟩
        exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨rfl, ⟨xt, n, xn, hkt, hbn, hkn, hna⟩, hns, hun⟩, hnr⟩))))

/-- **`receive_ipc` with a null or free reply at a switch mid state**
(module docstring). -/
theorem jRecvIpcUM (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (ht : ct ∈ Z.T) (hcur : σ.curThread = ct.bv) (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (p b : U64) (sd g gr : Bool) (rc : capability.Cap) (rc' : Fl4Spec.Cap)
    (hpE : ∃ x, σ.kheap p.bv = some (.endpoint x))
    (hrc : (rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x)))
    (hHd : JHeld (L := L) Z.th s (.Endpoint p b sd true g gr))
    (hHr : ∀ q g', rc = .Reply q g' → JHeld (L := L) Z.th s rc)
    (hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64) :
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄ :=
  jRecvIpcDoneM3 hAT hmax htu J ht hcur hni hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr (ipcDoneM3_of J ht hpE hun)

set_option maxHeartbeats 4000000 in
/-- **`receive_ipc` at `J` with a reply linked to another thread**
(module docstring): FL4's and the spec's `cancel_ipc` of that thread
(`JAtZ.cancelLinkJ`), then `jRecvIpcUM` at the state after, at a switch mid
state (sch17; the cancel keeps the action, the current thread and its TCB). -/
theorem jRecvIpcLinkM (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (ht : ct ∈ Z.T)
    (hcur : σ.curThread = ct.bv) (hni : MidE σ) (hsw : σ.schedulerAction ≠ .resumeCurThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
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
  have hE' : MidE σ' := ⟨by rw [hct', hid']; exact hni.1, hrun', by rw [hact', hct']; exact hni.2.2⟩
  exact jRecvIpcUM (Z := Z.mv Z.G V) hAT hmax htu J' ht (hct'.trans hcur) hE' (by rw [hact']; exact hsw)
    (by rw [hct', hrq']; exact hnq) p b sd g gr (.Reply q g') _ ⟨xe', hke'⟩
    (Or.inr ⟨hcr, q, g', rfl, xr', hkr'⟩) (jHeld_of_same hSS hHd) (fun _ _ _ => jHeld_of_same hSS hHr)
    (Or.inr ⟨q, g', rfl, h0'⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`JRecvLeavesRN5` with the endpoint receive asked only under a pending reschedule**
(module docstring). -/
structure JRecvLeavesRN6 (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (ct : U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  ipc : ∀ p b sd g gr rc rc', (∃ x, σ.kheap p.bv = some (.endpoint x)) →
    ((rc = .Null ∧ rc' = .nullCap) ∨
      (CapRel rc rc' ∧ ∃ q g', rc = .Reply q g' ∧ ∃ x, σ.kheap q.bv = some (.reply x))) →
    JHeld (L := L) th s (.Endpoint p b sd true g gr) → (∀ q g', rc = .Reply q g' → JHeld (L := L) th s rc) →
    σ.schedulerAction = .chooseNewThread →
    endpoint.receive_ipc st arI s a ct (.Endpoint p b sd true g gr) true rc ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveIpc (Z := Unit) ct.bv (absCap (.Endpoint p b sd true g gr)) true rc' σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  sig : ∀ p b w rd ac, CapRel (.Notification p b w rd) ac → (∃ x, σ.kheap p.bv = some (.notification x)) →
    JHeld (L := L) th s (.Notification p b w rd) → SigOpen σ p →
    notification.receive_signal st arI s a ct p true ⦃ r =>
      ∃ z ∈ (Fl4Spec.receiveSignal (Z := Unit) ct.bv ac true σ).1, RJR (L := L) arI AR r.1 r.2 z.2 ⦄
  flt : ∀ cptr lf lf', LookupFaultRel lf lf' → FltOpen σ →
    faults.handle_fault st arI s a ct (.Cap cptr true lf) ⦃ r =>
      ∃ z ∈ (Fl4Spec.handleFault (Z := Unit) ct.bv (.capFault (Fl4Spec.ofBl (Fl4Spec.toBl cptr.bv)) true lf') σ).1,
        RJR (L := L) arI AR r.1 r.2 z.2 ⦄

/-- **[W] The receive leaves at a non-resumed mid state, narrowed further**
(module docstring): `JMidLeavesHyp5` concluding `JRecvLeavesRN6`. -/
def JMidLeavesHyp6 (AR : A → Fl4Spec.Cr3 → Prop) (cptr : Fl4Spec.CapRef) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ y ∈ ((Fl4Spec.fl4HandleInvocationR (Z := Unit) true false false true true cptr).run σ).1, y.1 = .ok () →
    y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, y.2.curThread ∉ y.2.readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread y.2.curThread →
    (∀ x, y.2.kheap y.2.curThread = some (.tcb x) → Fl4Spec.validFaultHandler x.tcbFaultHandler) →
    ∀ (s1 : S) (a1 : A), RelTopM (L := L) s1 y.2 → CurRun y.2 → y.2.curThread ≠ y.2.idleThread →
    ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a1 y.2 → ∀ ct, sched.cur_thread st s1 = ok ct →
        JRecvLeavesRN6 (L := L) arI AR Z.th ct s1 a1 y.2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **`JRecvLeavesRN5` from `JRecvLeavesRN6`** at a non-resumed mid state
with no switch to ct: `jRecvIpcUM` / `jRecvIpcLinkM` unless a reschedule is pending. -/
theorem JRecvLeavesRN6.toRN5 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (hni1 : σ.curThread ≠ σ.idleThread) (hrun : CurRun σ) (hsw : σ.schedulerAction ≠ .resumeCurThread)
    (hsc : σ.schedulerAction ≠ .switchThread σ.curThread) (hnq : ∀ d p, σ.curThread ∉ σ.readyQueues d p)
    (h : JRecvLeavesRN6 (L := L) arI AR Z.th ct s a σ) : JRecvLeavesRN5 (L := L) arI AR Z.th ct s a σ where
  sig := h.sig
  flt := h.flt
  ipc := fun p b sd g gr rc rc' hpE hrc hHd hHr _ => by
    by_cases ho : σ.schedulerAction = .chooseNewThread
    · exact h.ipc p b sd g gr rc rc' hpE hrc hHd hHr ho
    · obtain ⟨hcur, -⟩ := J.curEq hct
      have hctT : ct ∈ Z.T := TopSR.cur_mem J.xtop.fin.1 hcur.symm
      have hE : MidE σ := by
        refine ⟨hni1, hrun, Or.inr ?_⟩
        cases e : σ.schedulerAction with
        | resumeCurThread => exact absurd e hsw
        | chooseNewThread => exact absurd e ho
        | switchThread u => exact ⟨u, rfl, fun hu => hsc (by rw [e, hu])⟩
      by_cases hun : rc = .Null ∨ ∃ q g', rc = .Reply q g' ∧ L.mem s (rTcbA q) = 0#u64
      · exact jRecvIpcUM hAT hmax htu J hctT hcur hE hsw hnq p b sd g gr rc rc' hpE hrc hHd hHr hun
      · rcases hrc with ⟨rfl, -⟩ | ⟨hcr, q, g', rfl, xr, hkr⟩
        · exact absurd (Or.inl rfl) hun
        · exact jRecvIpcLinkM hAT hmax htu J hctT hcur hE hsw hnq p b sd g gr q g' rc' hpE hcr hkr hHd
            (hHr q g' rfl) (fun h => hun (Or.inr ⟨q, g', rfl, h⟩))

/-- **`JMidLeavesHyp5` from `JMidLeavesHyp6`** (module docstring). -/
theorem jMidLeavesHyp_of6 (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {cptr : Fl4Spec.CapRef} {σ : Fl4Spec.State Unit}
    (hL : JMidLeavesHyp6 (L := L) arI AR cptr σ) : JMidLeavesHyp5 (L := L) arI AR cptr σ := by
  intro y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct
  exact (hL y hy hok ha hnq hsw hvf s1 a1 hR hrun hni1 Z H Cs Ac Lst D J ct hct).toRN5 hAT hmax (htu a1) J hct hni1
    hrun ha hsw hnq

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The dispatch premises with the mid receive leaves narrowed**
(module docstring). -/
structure KDispHyps15M (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs D : Set U64) (s : S) (a : A)
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
    JMidLeavesHyp6 (L := L) arI AR (Fl4Spec.toBl (L.mem s (regA ct rg)).bv) σ

variable {arI}

theorem KDispHyps15M.to14M (hAT : P0.ArchTotal arI) (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall}
    (h : KDispHyps15M (L := L) arI AR Z H Cs D s a σ n c) : KDispHyps14M (L := L) arI AR Z H Cs D s a σ n c where
  inv := h.inv
  recv := h.recv
  mid := fun ct rg sr cr hct hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.mid ct rg sr cr hct hm
    exact ⟨h1, h2, h3, h4, h5, jMidLeavesHyp_of6 hAT hmax htu h6⟩

set_option maxHeartbeats 16000000 in
/-- **The kernel entry for a native system call at `J`**, `kernel_entryJ14M`
with `KDispHyps15M` (mid: entry facts, `JMidPerfHypQ` [W], `JMidVfhHyp` [J],
`JMidLeavesHyp6` [W]) for `KDispHyps14M` (module docstring). -/
theorem kernel_entryJ15M [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hni : Entered σ) (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x))
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), JAtZ (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' σb →
        KDispHyps15M (L := L) arI AR Z' H' Cs' D' s' a' σb n c)
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
  kernel_entryJ14M s a σ J hni n c hn hflag hB
    (fun σb hBA Z' H' Cs' Ac' Lst' D' s' a' J' => (hK σb hBA Z' H' Cs' Ac' Lst' D' s' a' J').to14M hA hmax htu)
    hFin hARI hA hnd hPP hmrt hmb hIP hNS hNSR hT hmax htu

end

end

end Fl4Proofs.P3
